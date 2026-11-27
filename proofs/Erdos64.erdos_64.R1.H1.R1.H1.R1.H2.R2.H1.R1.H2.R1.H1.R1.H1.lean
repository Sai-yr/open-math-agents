import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H1_R1
import Mathlib

/-!
# Dyadic cycles in abelian covers of hexagonal grids

The two chords of a normalized pair of hexagons record its two voltages.
If both are nonzero, explicit vertex-simple walks on two or four sheets
give cycle lengths 16/32 for a length-two handle and 32/64 for a length-ten
handle. The four local matching lemmas of PR 5246 give a one-third lower
bound on the density of nonzero faces in the finite base, including when the
sheet group is infinite. Two orientations of triangular cells give equality
and periodicity if all dyadic cycles up to length 32 are absent.

The general theorem is DyadicHex.voltageFamily. It allows length 64 when
the order of the base is divisible by three. The final specialization meets
the four allowed lengths of the abelian voltage problem in PR 9593.
-/

open SimpleGraph Finset
namespace DyadicHex

private theorem cycleOfNext {X : Type*} (G : SimpleGraph X) {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) (f : Fin n ↪ X) (edges : ∀ i, G.Adj (f i) (f (i+1))) :
    cycleGraph n ⊑ G := by
  obtain ⟨t,rfl⟩ : ∃ t, n=t+2 := ⟨n-2,by omega⟩
  refine ⟨⟨⟨f,?_⟩,f.injective⟩⟩
  intro i j h
  rcases cycleGraph_adj.mp h with l|r
  · have e : i=j+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp l
    simpa only [e] using (edges j).symm
  · have e : j=i+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp r
    simpa only [e] using edges i

private def legal {n k : ℕ} (E : Finset (Fin n × Fin n)) (U W : Finset (Fin k × Fin k))
    (a b : Fin n × Fin k) :=
  ((a.1,b.1)∈E ∧ a.2=b.2) ∨ (a.1.val=5 ∧ b.1.val=0 ∧ (a.2,b.2)∈U) ∨
    (a.1.val=11 ∧ b.1.val=6 ∧ (a.2,b.2)∈W)

private instance {n k} (E : Finset (Fin n × Fin n)) (U W : Finset (Fin k × Fin k))
    (a b : Fin n × Fin k) : Decidable (legal E U W a b) := by unfold legal; infer_instance

private theorem liftWord {n k m : ℕ} [NeZero n] [NeZero m] (hn : 12 ≤ n) (hm : 3 ≤ m)
    {V X : Type*} [AddCommGroup V] (G : SimpleGraph X) (emb : Fin n × V ↪ X)
    (u v : V) (E : Finset (Fin n × Fin n))
    (tree : ∀ i j, (i,j)∈E → ∀ g, G.Adj (emb (i,g)) (emb (j,g)))
    (left : ∀ g, G.Adj (emb (5,g)) (emb (0,g+u)))
    (right : ∀ g, G.Adj (emb (11,g)) (emb (6,g+v)))
    (sh : Fin k ↪ V) (U W : Finset (Fin k × Fin k))
    (us : ∀ i j, (i,j)∈U → sh j=sh i+u) (vs : ∀ i j, (i,j)∈W → sh j=sh i+v)
    (p : Fin m → Fin n × Fin k) (distinct : Function.Injective p)
    (next : ∀ i, legal E U W (p i) (p (i+1)) ∨ legal E U W (p (i+1)) (p i)) :
    cycleGraph m ⊑ G := by
  let e := ((Function.Embedding.refl (Fin n)).prodMap sh).trans emb
  have forward (a b : Fin n × Fin k) (h : legal E U W a b) : G.Adj (e a) (e b) := by
    rcases a with ⟨i,s⟩; rcases b with ⟨j,t⟩
    rcases h with ⟨ht,h⟩|⟨hl,hr,h⟩|⟨hl,hr,h⟩
    · change s=t at h; subst t; exact tree i j ht _
    · have e₁ : i=5 := Fin.ext (by simpa [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : 5<n)] using hl)
      have e₂ : j=0 := Fin.ext (by simpa using hr)
      subst i; subst j; change G.Adj (emb (5,sh s)) (emb (0,sh t))
      rw [us s t h]; exact left _
    · have e₁ : i=11 := Fin.ext (by simpa [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : 11<n)] using hl)
      have e₂ : j=6 := Fin.ext (by simpa [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : 6<n)] using hr)
      subst i; subst j; change G.Adj (emb (11,sh s)) (emb (6,sh t))
      rw [vs s t h]; exact right _
  exact cycleOfNext G hm ⟨fun i => e (p i),e.injective.comp distinct⟩
    (fun i => (next i).elim (forward _ _) (fun h => (forward _ _ h).symm))

private def sheets {V : Type*} [AddCommGroup V] (u v : V)
    (hu : u ≠ 0) (hv : v ≠ 0) (hp : u ≠ v) (hn : u ≠ -v) : Fin 4 ↪ V :=
  ⟨![0,u,v,u+v],by
    have h0 : u+v≠0 := fun h => hn (eq_neg_of_add_eq_zero_left h)
    have h1 : u+v≠u := by simpa using hv
    have h2 : u+v≠v := by simpa using hu
    intro i j h
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact (hu h).elim
      | exact (hu h.symm).elim
      | exact (hv h).elim
      | exact (hv h.symm).elim
      | exact (hp h).elim
      | exact (hp h.symm).elim
      | exact (h0 h).elim
      | exact (h0 h.symm).elim
      | exact (h1 h).elim
      | exact (h1 h.symm).elim
      | exact (h2 h).elim
      | exact (h2 h.symm).elim⟩
private def twoSheets {V : Type*} [AddCommGroup V] (u : V) (hu : u≠0) : Fin 2 ↪ V :=
  ⟨![0,u],by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

/-- Spanning tree of two hexagons joined by a 2-edge handle. The two omitted edges are 5–0 and 11–6. -/
def tree2 : Finset (Fin 13 × Fin 13) := {(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,12),(12,6)}
theorem barbell2 {V X : Type*} [AddCommGroup V] (G : SimpleGraph X)
    (emb : Fin 13 × V ↪ X) (u v : V) (hu : u≠0) (hv : v≠0)
    (tree : ∀ i j, (i,j)∈tree2 → ∀ g, G.Adj (emb (i,g)) (emb (j,g)))
    (left : ∀ g, G.Adj (emb (5,g)) (emb (0,g+u)))
    (right : ∀ g, G.Adj (emb (11,g)) (emb (6,g+v))) :
    cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  by_cases hp : u=v
  · left
    let p : Fin 16 → Fin 13 × Fin 2 := ![(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(0,1),(12,1),(6,1),(11,0),(10,0),(9,0),(8,0),(7,0),(6,0),(12,0)]
    apply liftWord (by decide) (by decide) G emb u v (tree2) tree left right (twoSheets u hu) {(0,1)} {(0,1)} _ _ p
    · change ∀ i j, p i=p j → i=j; dsimp only [p]; decide +kernel
    · dsimp only [p,tree2]; decide +kernel
    · intro i j h; simp only [mem_singleton,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      simp_all [twoSheets,add_comm]
    · intro i j h; simp only [mem_singleton,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      simp_all [twoSheets,add_comm]
  by_cases hn : u= -v
  · left
    let p : Fin 16 → Fin 13 × Fin 2 := ![(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(0,1),(12,1),(6,1),(7,1),(8,1),(9,1),(10,1),(11,1),(6,0),(12,0)]
    apply liftWord (by decide) (by decide) G emb u v (tree2) tree left right (twoSheets u hu) {(0,1)} {(1,0)} _ _ p
    · change ∀ i j, p i=p j → i=j; dsimp only [p]; decide +kernel
    · dsimp only [p,tree2]; decide +kernel
    · intro i j h; simp only [mem_singleton,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      simp_all [twoSheets,add_comm]
    · intro i j h; simp only [mem_singleton,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      simp_all [twoSheets,add_comm]
  right
  let p : Fin 32 → Fin 13 × Fin 4 := ![(0,0), (1,0), (2,0), (3,0), (4,0), (5,0), (0,1), (12,1), (6,1),
      (7,1), (8,1), (9,1), (10,1), (11,1), (6,3), (12,3), (0,3), (5,2), (4,2), (3,2), (2,2), (1,2), (0,2),
      (12,2), (6,2), (11,0), (10,0), (9,0), (8,0), (7,0), (6,0), (12,0)]
  apply liftWord (by decide) (by decide) G emb u v (tree2) tree left right (sheets u v hu hv hp hn) {(0,1),(2,3)} {(0,2),(1,3)} _ _ p
  · change ∀ i j, p i=p j → i=j; dsimp only [p]; decide +kernel
  · dsimp only [p,tree2]; decide +kernel
  · intro i j h; simp only [mem_insert,mem_singleton,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · change u = 0+u; abel
    · change u+v = v+u; abel
  · intro i j h; simp only [mem_insert,mem_singleton,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · change v = 0+v; abel
    · change u+v = u+v; abel

/-- Spanning tree of two hexagons joined by a 10-edge handle. The two omitted edges are 5–0 and 11–6. -/
def tree10 : Finset (Fin 21 × Fin 21) := {(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,12),(12,13),(13,14),(14,15),(15,16),(16,17),(17,18),(18,19),(19,20),(20,6)}
theorem barbell10 {V X : Type*} [AddCommGroup V] (G : SimpleGraph X)
    (emb : Fin 21 × V ↪ X) (u v : V) (hu : u≠0) (hv : v≠0)
    (tree : ∀ i j, (i,j)∈tree10 → ∀ g, G.Adj (emb (i,g)) (emb (j,g)))
    (left : ∀ g, G.Adj (emb (5,g)) (emb (0,g+u)))
    (right : ∀ g, G.Adj (emb (11,g)) (emb (6,g+v))) :
    cycleGraph 32 ⊑ G ∨ cycleGraph 64 ⊑ G := by
  by_cases hp : u=v
  · left
    let p : Fin 32 → Fin 21 × Fin 2 := ![(0,0), (1,0), (2,0), (3,0), (4,0), (5,0), (0,1), (12,1), (13,1),
      (14,1), (15,1), (16,1), (17,1), (18,1), (19,1), (20,1), (6,1), (11,0), (10,0), (9,0), (8,0), (7,0),
      (6,0), (20,0), (19,0), (18,0), (17,0), (16,0), (15,0), (14,0), (13,0), (12,0)]
    apply liftWord (by decide) (by decide) G emb u v (tree10) tree left right (twoSheets u hu) {(0,1)} {(0,1)} _ _ p
    · change ∀ i j, p i=p j → i=j; dsimp only [p]; decide +kernel
    · dsimp only [p,tree10]; decide +kernel
    · intro i j h; simp only [mem_singleton,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      simp_all [twoSheets,add_comm]
    · intro i j h; simp only [mem_singleton,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      simp_all [twoSheets,add_comm]
  by_cases hn : u= -v
  · left
    let p : Fin 32 → Fin 21 × Fin 2 := ![(0,0), (1,0), (2,0), (3,0), (4,0), (5,0), (0,1), (12,1), (13,1),
      (14,1), (15,1), (16,1), (17,1), (18,1), (19,1), (20,1), (6,1), (7,1), (8,1), (9,1), (10,1), (11,1),
      (6,0), (20,0), (19,0), (18,0), (17,0), (16,0), (15,0), (14,0), (13,0), (12,0)]
    apply liftWord (by decide) (by decide) G emb u v (tree10) tree left right (twoSheets u hu) {(0,1)} {(1,0)} _ _ p
    · change ∀ i j, p i=p j → i=j; dsimp only [p]; decide +kernel
    · dsimp only [p,tree10]; decide +kernel
    · intro i j h; simp only [mem_singleton,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      simp_all [twoSheets,add_comm]
    · intro i j h; simp only [mem_singleton,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      simp_all [twoSheets,add_comm]
  right
  let p : Fin 64 → Fin 21 × Fin 4 := ![(0,0), (1,0), (2,0), (3,0), (4,0), (5,0), (0,1), (12,1), (13,1),
      (14,1), (15,1), (16,1), (17,1), (18,1), (19,1), (20,1), (6,1), (7,1), (8,1), (9,1), (10,1), (11,1),
      (6,3), (20,3), (19,3), (18,3), (17,3), (16,3), (15,3), (14,3), (13,3), (12,3), (0,3), (5,2), (4,2),
      (3,2), (2,2), (1,2), (0,2), (12,2), (13,2), (14,2), (15,2), (16,2), (17,2), (18,2), (19,2), (20,2),
      (6,2), (11,0), (10,0), (9,0), (8,0), (7,0), (6,0), (20,0), (19,0), (18,0), (17,0), (16,0), (15,0),
      (14,0), (13,0), (12,0)]
  apply liftWord (by decide) (by decide) G emb u v (tree10) tree left right (sheets u v hu hv hp hn) {(0,1),(2,3)} {(0,2),(1,3)} _ _ p
  · change ∀ i j, p i=p j → i=j; dsimp only [p]; decide +kernel
  · dsimp only [p,tree10]; decide +kernel
  · intro i j h; simp only [mem_insert,mem_singleton,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · change u = 0+u; abel
    · change u+v = v+u; abel
  · intro i j h; simp only [mem_insert,mem_singleton,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · change v = 0+v; abel
    · change u+v = u+v; abel

end DyadicHex
namespace DyadicHex
open SimpleGraph Finset
abbrev Tile := Fin 8 × Fin 4
abbrev Site := Bool × Tile
def coord (i j : ℕ) : Tile := (Fin.ofNat 8 i,Fin.ofNat 4 j)
def flux {V : Type*} [AddCommGroup V] (P Q : Tile → V) (i j : ℕ) :=
  P (coord i j) + Q (coord (i+1) j) - P (coord i (j+1)) - Q (coord i j)
structure TileEdges {V X : Type*} [AddCommGroup V] (G : SimpleGraph X)
    (F : Site × V ↪ X) (P Q : Tile → V) : Prop where
  zero : ∀ i g, G.Adj (F ((false,i),g)) (F ((true,i),g))
  a : ∀ i j : Tile, j.1.val=i.1.val+1 → j.2=i.2 →
    ∀ g, G.Adj (F ((false,i),g)) (F ((true,j),g+P i))
  b : ∀ i j : Tile, j.1=i.1 → j.2.val=i.2.val+1 →
    ∀ g, G.Adj (F ((false,i),g)) (F ((true,j),g+Q i))


private theorem stepZero {V X : Type*} [AddCommGroup V] {G : SimpleGraph X}
    {F : Site × V ↪ X} {P Q : Tile → V} (E : TileEdges G F P Q)
    (i : Tile) {g k : V} (h : k=g) :
    G.Adj (F ((false,i),g)) (F ((true,i),k)) := h.symm ▸ E.zero i g

private theorem stepA {V X : Type*} [AddCommGroup V] {G : SimpleGraph X}
    {F : Site × V ↪ X} {P Q : Tile → V} (E : TileEdges G F P Q)
    (i j : Tile) (dx : j.1.val=i.1.val+1) (dy : j.2=i.2) {g k : V} (h : k=g+P i) :
    G.Adj (F ((false,i),g)) (F ((true,j),k)) := h.symm ▸ E.a i j dx dy g

private theorem stepB {V X : Type*} [AddCommGroup V] {G : SimpleGraph X}
    {F : Site × V ↪ X} {P Q : Tile → V} (E : TileEdges G F P Q)
    (i j : Tile) (dx : j.1=i.1) (dy : j.2.val=i.2.val+1) {g k : V} (h : k=g+Q i) :
    G.Adj (F ((false,i),g)) (F ((true,j),k)) := h.symm ▸ E.b i j dx dy g

private def frame {V X : Type*} [AddCommGroup V] {n} (F : Site × V ↪ X)
    (sites : Fin n → Site) (hi : Function.Injective sites) (p : Fin n → V) :
    Fin n × V ↪ X := ⟨fun z => F (sites z.1,z.2+p z.1),by
      rintro ⟨i,g⟩ ⟨j,k⟩ h
      have eq := F.injective h
      have e : i=j := hi (congrArg Prod.fst eq)
      subst j
      have e' : g=k := add_right_cancel (congrArg Prod.snd eq)
      rw [e']⟩

/-- Faces at (0,0) and (2,0), with a two-edge handle. The offset at each site is the sum along its path in the spanning tree. -/
theorem patchEast {V X : Type*} [AddCommGroup V] (G : SimpleGraph X) (F : Site × V ↪ X)
    (P Q : Tile → V) (E : TileEdges G F P Q) (hu : flux P Q 0 0 ≠ 0) (hv : flux P Q 2 0 ≠ 0) :
    cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  let sites : Fin 13 → Site := ![(false,(coord 1 0)), (true,(coord 1 1)), (false,(coord 0 1)), (true,(coord 0 1)),
      (false,(coord 0 0)), (true,(coord 1 0)), (false,(coord 2 0)), (true,(coord 3 0)), (false,(coord 3 0)),
      (true,(coord 3 1)), (false,(coord 2 1)), (true,(coord 2 1)), (true,(coord 2 0))]
  have inj : Function.Injective sites := by change ∀ i j, sites i=sites j → i=j; dsimp only [sites]; decide +kernel
  let off : Fin 13 → V := ![(0), (0 + Q (coord 1 0)), (0 - P (coord 0 1) + Q (coord 1 0)), (0 - P (coord 0 1) + Q (coord 1 0)),
      (0 - P (coord 0 1) - Q (coord 0 0) + Q (coord 1 0)), (0 + P (coord 0 0) - P (coord 0 1) - Q (coord 0 0) + Q (coord 1 0)),
      (0 + P (coord 1 0)), (0 + P (coord 1 0) + P (coord 2 0)), (0 + P (coord 1 0) + P (coord 2 0)),
      (0 + P (coord 1 0) + P (coord 2 0) + Q (coord 3 0)), (0 + P (coord 1 0) + P (coord 2 0) - P (coord 2 1) + Q (coord 3 0)),
      (0 + P (coord 1 0) + P (coord 2 0) - P (coord 2 1) + Q (coord 3 0)), (0 + P (coord 1 0))]
  let e := frame F sites inj off
  have edge0 (g : V) : G.Adj (e (0,g)) (e (1,g)) := by
    apply stepB E (coord 1 0) (coord 1 1) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge1 (g : V) : G.Adj (e (1,g)) (e (2,g)) := by
    apply G.adj_symm
    apply stepA E (coord 0 1) (coord 1 1) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge2 (g : V) : G.Adj (e (2,g)) (e (3,g)) := by
    apply stepZero E (coord 0 1)
    dsimp [off,flux]
  have edge3 (g : V) : G.Adj (e (3,g)) (e (4,g)) := by
    apply G.adj_symm
    apply stepB E (coord 0 0) (coord 0 1) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge4 (g : V) : G.Adj (e (4,g)) (e (5,g)) := by
    apply stepA E (coord 0 0) (coord 1 0) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge5 (g : V) : G.Adj (e (6,g)) (e (7,g)) := by
    apply stepA E (coord 2 0) (coord 3 0) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge6 (g : V) : G.Adj (e (7,g)) (e (8,g)) := by
    apply G.adj_symm
    apply stepZero E (coord 3 0)
    dsimp [off,flux]
  have edge7 (g : V) : G.Adj (e (8,g)) (e (9,g)) := by
    apply stepB E (coord 3 0) (coord 3 1) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge8 (g : V) : G.Adj (e (9,g)) (e (10,g)) := by
    apply G.adj_symm
    apply stepA E (coord 2 1) (coord 3 1) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge9 (g : V) : G.Adj (e (10,g)) (e (11,g)) := by
    apply stepZero E (coord 2 1)
    dsimp [off,flux]
  have edge10 (g : V) : G.Adj (e (0,g)) (e (12,g)) := by
    apply stepA E (coord 1 0) (coord 2 0) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge11 (g : V) : G.Adj (e (12,g)) (e (6,g)) := by
    apply G.adj_symm
    apply stepZero E (coord 2 0)
    dsimp [off,flux]
  have edge12 (g : V) : G.Adj (e (5,g)) (e (0,g+flux P Q 0 0)) := by
    apply G.adj_symm
    apply stepZero E (coord 1 0)
    dsimp [off,flux]; abel
  have edge13 (g : V) : G.Adj (e (11,g)) (e (6,g+flux P Q 2 0)) := by
    apply G.adj_symm
    apply stepB E (coord 2 0) (coord 2 1) (by decide) (by decide)
    dsimp [off,flux]; abel
  apply barbell2 G e _ _ hu hv _ edge12 edge13
  intro i j hij
  simp only [tree2,mem_insert,mem_singleton,Prod.mk.injEq] at hij
  rcases hij with
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact edge0
  · exact edge1
  · exact edge2
  · exact edge3
  · exact edge4
  · exact edge5
  · exact edge6
  · exact edge7
  · exact edge8
  · exact edge9
  · exact edge10
  · exact edge11

/-- Faces at (0,0) and (0,2), with a two-edge handle. The offset at each site is the sum along its path in the spanning tree. -/
theorem patchNorth {V X : Type*} [AddCommGroup V] (G : SimpleGraph X) (F : Site × V ↪ X)
    (P Q : Tile → V) (E : TileEdges G F P Q) (hu : flux P Q 0 0 ≠ 0) (hv : flux P Q 0 2 ≠ 0) :
    cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  let sites : Fin 13 → Site := ![(false,(coord 0 1)), (true,(coord 0 1)), (false,(coord 0 0)), (true,(coord 1 0)),
      (false,(coord 1 0)), (true,(coord 1 1)), (false,(coord 0 2)), (true,(coord 1 2)), (false,(coord 1 2)),
      (true,(coord 1 3)), (false,(coord 0 3)), (true,(coord 0 3)), (true,(coord 0 2))]
  have inj : Function.Injective sites := by change ∀ i j, sites i=sites j → i=j; dsimp only [sites]; decide +kernel
  let off : Fin 13 → V := ![(0), (0), (0 - Q (coord 0 0)), (0 + P (coord 0 0) - Q (coord 0 0)), (0 + P (coord 0 0) - Q (coord 0 0)),
      (0 + P (coord 0 0) - Q (coord 0 0) + Q (coord 1 0)), (0 + Q (coord 0 1)), (0 + P (coord 0 2) + Q (coord 0 1)),
      (0 + P (coord 0 2) + Q (coord 0 1)), (0 + P (coord 0 2) + Q (coord 0 1) + Q (coord 1 2)), (0 + P (coord 0 2) - P (coord 0 3) + Q (coord 0 1) + Q (coord 1 2)),
      (0 + P (coord 0 2) - P (coord 0 3) + Q (coord 0 1) + Q (coord 1 2)), (0 + Q (coord 0 1))]
  let e := frame F sites inj off
  have edge0 (g : V) : G.Adj (e (0,g)) (e (1,g)) := by
    apply stepZero E (coord 0 1)
    dsimp [off,flux]
  have edge1 (g : V) : G.Adj (e (1,g)) (e (2,g)) := by
    apply G.adj_symm
    apply stepB E (coord 0 0) (coord 0 1) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge2 (g : V) : G.Adj (e (2,g)) (e (3,g)) := by
    apply stepA E (coord 0 0) (coord 1 0) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge3 (g : V) : G.Adj (e (3,g)) (e (4,g)) := by
    apply G.adj_symm
    apply stepZero E (coord 1 0)
    dsimp [off,flux]
  have edge4 (g : V) : G.Adj (e (4,g)) (e (5,g)) := by
    apply stepB E (coord 1 0) (coord 1 1) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge5 (g : V) : G.Adj (e (6,g)) (e (7,g)) := by
    apply stepA E (coord 0 2) (coord 1 2) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge6 (g : V) : G.Adj (e (7,g)) (e (8,g)) := by
    apply G.adj_symm
    apply stepZero E (coord 1 2)
    dsimp [off,flux]
  have edge7 (g : V) : G.Adj (e (8,g)) (e (9,g)) := by
    apply stepB E (coord 1 2) (coord 1 3) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge8 (g : V) : G.Adj (e (9,g)) (e (10,g)) := by
    apply G.adj_symm
    apply stepA E (coord 0 3) (coord 1 3) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge9 (g : V) : G.Adj (e (10,g)) (e (11,g)) := by
    apply stepZero E (coord 0 3)
    dsimp [off,flux]
  have edge10 (g : V) : G.Adj (e (0,g)) (e (12,g)) := by
    apply stepB E (coord 0 1) (coord 0 2) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge11 (g : V) : G.Adj (e (12,g)) (e (6,g)) := by
    apply G.adj_symm
    apply stepZero E (coord 0 2)
    dsimp [off,flux]
  have edge12 (g : V) : G.Adj (e (5,g)) (e (0,g+flux P Q 0 0)) := by
    apply G.adj_symm
    apply stepA E (coord 0 1) (coord 1 1) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge13 (g : V) : G.Adj (e (11,g)) (e (6,g+flux P Q 0 2)) := by
    apply G.adj_symm
    apply stepB E (coord 0 2) (coord 0 3) (by decide) (by decide)
    dsimp [off,flux]; abel
  apply barbell2 G e _ _ hu hv _ edge12 edge13
  intro i j hij
  simp only [tree2,mem_insert,mem_singleton,Prod.mk.injEq] at hij
  rcases hij with
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact edge0
  · exact edge1
  · exact edge2
  · exact edge3
  · exact edge4
  · exact edge5
  · exact edge6
  · exact edge7
  · exact edge8
  · exact edge9
  · exact edge10
  · exact edge11

/-- Faces at (0,2) and (2,0), with a two-edge handle. The offset at each site is the sum along its path in the spanning tree. -/
theorem patchDiagonal {V X : Type*} [AddCommGroup V] (G : SimpleGraph X) (F : Site × V ↪ X)
    (P Q : Tile → V) (E : TileEdges G F P Q) (hu : flux P Q 0 2 ≠ 0) (hv : flux P Q 2 0 ≠ 0) :
    cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  let sites : Fin 13 → Site := ![(true,(coord 1 2)), (false,(coord 1 2)), (true,(coord 1 3)), (false,(coord 0 3)),
      (true,(coord 0 3)), (false,(coord 0 2)), (true,(coord 2 1)), (false,(coord 2 0)), (true,(coord 3 0)),
      (false,(coord 3 0)), (true,(coord 3 1)), (false,(coord 2 1)), (false,(coord 1 1))]
  have inj : Function.Injective sites := by change ∀ i j, sites i=sites j → i=j; dsimp only [sites]; decide +kernel
  let off : Fin 13 → V := ![(0), (0), (0 + Q (coord 1 2)), (0 - P (coord 0 3) + Q (coord 1 2)), (0 - P (coord 0 3) + Q (coord 1 2)),
      (0 - P (coord 0 3) - Q (coord 0 2) + Q (coord 1 2)), (0 + P (coord 1 1) - Q (coord 1 1)), (0 + P (coord 1 1) - Q (coord 1 1) - Q (coord 2 0)),
      (0 + P (coord 1 1) + P (coord 2 0) - Q (coord 1 1) - Q (coord 2 0)), (0 + P (coord 1 1) + P (coord 2 0) - Q (coord 1 1) - Q (coord 2 0)),
      (0 + P (coord 1 1) + P (coord 2 0) - Q (coord 1 1) - Q (coord 2 0) + Q (coord 3 0)), (0 + P (coord 1 1) + P (coord 2 0) - P (coord 2 1) - Q (coord 1 1) - Q (coord 2 0) + Q (coord 3 0)),
      (0 - Q (coord 1 1))]
  let e := frame F sites inj off
  have edge0 (g : V) : G.Adj (e (0,g)) (e (1,g)) := by
    apply G.adj_symm
    apply stepZero E (coord 1 2)
    dsimp [off,flux]
  have edge1 (g : V) : G.Adj (e (1,g)) (e (2,g)) := by
    apply stepB E (coord 1 2) (coord 1 3) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge2 (g : V) : G.Adj (e (2,g)) (e (3,g)) := by
    apply G.adj_symm
    apply stepA E (coord 0 3) (coord 1 3) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge3 (g : V) : G.Adj (e (3,g)) (e (4,g)) := by
    apply stepZero E (coord 0 3)
    dsimp [off,flux]
  have edge4 (g : V) : G.Adj (e (4,g)) (e (5,g)) := by
    apply G.adj_symm
    apply stepB E (coord 0 2) (coord 0 3) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge5 (g : V) : G.Adj (e (6,g)) (e (7,g)) := by
    apply G.adj_symm
    apply stepB E (coord 2 0) (coord 2 1) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge6 (g : V) : G.Adj (e (7,g)) (e (8,g)) := by
    apply stepA E (coord 2 0) (coord 3 0) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge7 (g : V) : G.Adj (e (8,g)) (e (9,g)) := by
    apply G.adj_symm
    apply stepZero E (coord 3 0)
    dsimp [off,flux]
  have edge8 (g : V) : G.Adj (e (9,g)) (e (10,g)) := by
    apply stepB E (coord 3 0) (coord 3 1) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge9 (g : V) : G.Adj (e (10,g)) (e (11,g)) := by
    apply G.adj_symm
    apply stepA E (coord 2 1) (coord 3 1) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge10 (g : V) : G.Adj (e (0,g)) (e (12,g)) := by
    apply G.adj_symm
    apply stepB E (coord 1 1) (coord 1 2) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge11 (g : V) : G.Adj (e (12,g)) (e (6,g)) := by
    apply stepA E (coord 1 1) (coord 2 1) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge12 (g : V) : G.Adj (e (5,g)) (e (0,g+flux P Q 0 2)) := by
    apply stepA E (coord 0 2) (coord 1 2) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge13 (g : V) : G.Adj (e (11,g)) (e (6,g+flux P Q 2 0)) := by
    apply stepZero E (coord 2 1)
    dsimp [off,flux]; abel
  apply barbell2 G e _ _ hu hv _ edge12 edge13
  intro i j hij
  simp only [tree2,mem_insert,mem_singleton,Prod.mk.injEq] at hij
  rcases hij with
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact edge0
  · exact edge1
  · exact edge2
  · exact edge3
  · exact edge4
  · exact edge5
  · exact edge6
  · exact edge7
  · exact edge8
  · exact edge9
  · exact edge10
  · exact edge11

/-- Faces at (0,0) and (6,0), with a ten-edge handle. The offset at each site is the sum along its path in the spanning tree. -/
theorem patchFar {V X : Type*} [AddCommGroup V] (G : SimpleGraph X) (F : Site × V ↪ X)
    (P Q : Tile → V) (E : TileEdges G F P Q) (hu : flux P Q 0 0 ≠ 0) (hv : flux P Q 6 0 ≠ 0) :
    cycleGraph 32 ⊑ G ∨ cycleGraph 64 ⊑ G := by
  let sites : Fin 21 → Site := ![(false,(coord 1 0)), (true,(coord 1 1)), (false,(coord 0 1)), (true,(coord 0 1)),
      (false,(coord 0 0)), (true,(coord 1 0)), (false,(coord 6 0)), (true,(coord 7 0)), (false,(coord 7 0)),
      (true,(coord 7 1)), (false,(coord 6 1)), (true,(coord 6 1)), (true,(coord 2 0)), (false,(coord 2 0)),
      (true,(coord 3 0)), (false,(coord 3 0)), (true,(coord 4 0)), (false,(coord 4 0)), (true,(coord 5 0)),
      (false,(coord 5 0)), (true,(coord 6 0))]
  have inj : Function.Injective sites := by change ∀ i j, sites i=sites j → i=j; dsimp only [sites]; decide +kernel
  let off : Fin 21 → V := ![(0), (0 + Q (coord 1 0)), (0 - P (coord 0 1) + Q (coord 1 0)), (0 - P (coord 0 1) + Q (coord 1 0)),
      (0 - P (coord 0 1) - Q (coord 0 0) + Q (coord 1 0)), (0 + P (coord 0 0) - P (coord 0 1) - Q (coord 0 0) + Q (coord 1 0)),
      (0 + P (coord 1 0) + P (coord 2 0) + P (coord 3 0) + P (coord 4 0) + P (coord 5 0)), (0 + P (coord 1 0) + P (coord 2 0) + P (coord 3 0) + P (coord 4 0) + P (coord 5 0) + P (coord 6 0)),
      (0 + P (coord 1 0) + P (coord 2 0) + P (coord 3 0) + P (coord 4 0) + P (coord 5 0) + P (coord 6 0)),
      (0 + P (coord 1 0) + P (coord 2 0) + P (coord 3 0) + P (coord 4 0) + P (coord 5 0) + P (coord 6 0) + Q (coord 7 0)),
      (0 + P (coord 1 0) + P (coord 2 0) + P (coord 3 0) + P (coord 4 0) + P (coord 5 0) + P (coord 6 0) - P (coord 6 1) + Q (coord 7 0)),
      (0 + P (coord 1 0) + P (coord 2 0) + P (coord 3 0) + P (coord 4 0) + P (coord 5 0) + P (coord 6 0) - P (coord 6 1) + Q (coord 7 0)),
      (0 + P (coord 1 0)), (0 + P (coord 1 0)), (0 + P (coord 1 0) + P (coord 2 0)), (0 + P (coord 1 0) + P (coord 2 0)),
      (0 + P (coord 1 0) + P (coord 2 0) + P (coord 3 0)), (0 + P (coord 1 0) + P (coord 2 0) + P (coord 3 0)),
      (0 + P (coord 1 0) + P (coord 2 0) + P (coord 3 0) + P (coord 4 0)), (0 + P (coord 1 0) + P (coord 2 0) + P (coord 3 0) + P (coord 4 0)),
      (0 + P (coord 1 0) + P (coord 2 0) + P (coord 3 0) + P (coord 4 0) + P (coord 5 0))]
  let e := frame F sites inj off
  have edge0 (g : V) : G.Adj (e (0,g)) (e (1,g)) := by
    apply stepB E (coord 1 0) (coord 1 1) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge1 (g : V) : G.Adj (e (1,g)) (e (2,g)) := by
    apply G.adj_symm
    apply stepA E (coord 0 1) (coord 1 1) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge2 (g : V) : G.Adj (e (2,g)) (e (3,g)) := by
    apply stepZero E (coord 0 1)
    dsimp [off,flux]
  have edge3 (g : V) : G.Adj (e (3,g)) (e (4,g)) := by
    apply G.adj_symm
    apply stepB E (coord 0 0) (coord 0 1) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge4 (g : V) : G.Adj (e (4,g)) (e (5,g)) := by
    apply stepA E (coord 0 0) (coord 1 0) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge5 (g : V) : G.Adj (e (6,g)) (e (7,g)) := by
    apply stepA E (coord 6 0) (coord 7 0) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge6 (g : V) : G.Adj (e (7,g)) (e (8,g)) := by
    apply G.adj_symm
    apply stepZero E (coord 7 0)
    dsimp [off,flux]
  have edge7 (g : V) : G.Adj (e (8,g)) (e (9,g)) := by
    apply stepB E (coord 7 0) (coord 7 1) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge8 (g : V) : G.Adj (e (9,g)) (e (10,g)) := by
    apply G.adj_symm
    apply stepA E (coord 6 1) (coord 7 1) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge9 (g : V) : G.Adj (e (10,g)) (e (11,g)) := by
    apply stepZero E (coord 6 1)
    dsimp [off,flux]
  have edge10 (g : V) : G.Adj (e (0,g)) (e (12,g)) := by
    apply stepA E (coord 1 0) (coord 2 0) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge11 (g : V) : G.Adj (e (12,g)) (e (13,g)) := by
    apply G.adj_symm
    apply stepZero E (coord 2 0)
    dsimp [off,flux]
  have edge12 (g : V) : G.Adj (e (13,g)) (e (14,g)) := by
    apply stepA E (coord 2 0) (coord 3 0) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge13 (g : V) : G.Adj (e (14,g)) (e (15,g)) := by
    apply G.adj_symm
    apply stepZero E (coord 3 0)
    dsimp [off,flux]
  have edge14 (g : V) : G.Adj (e (15,g)) (e (16,g)) := by
    apply stepA E (coord 3 0) (coord 4 0) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge15 (g : V) : G.Adj (e (16,g)) (e (17,g)) := by
    apply G.adj_symm
    apply stepZero E (coord 4 0)
    dsimp [off,flux]
  have edge16 (g : V) : G.Adj (e (17,g)) (e (18,g)) := by
    apply stepA E (coord 4 0) (coord 5 0) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge17 (g : V) : G.Adj (e (18,g)) (e (19,g)) := by
    apply G.adj_symm
    apply stepZero E (coord 5 0)
    dsimp [off,flux]
  have edge18 (g : V) : G.Adj (e (19,g)) (e (20,g)) := by
    apply stepA E (coord 5 0) (coord 6 0) (by decide) (by decide)
    dsimp [off,flux]; abel
  have edge19 (g : V) : G.Adj (e (20,g)) (e (6,g)) := by
    apply G.adj_symm
    apply stepZero E (coord 6 0)
    dsimp [off,flux]
  have edge20 (g : V) : G.Adj (e (5,g)) (e (0,g+flux P Q 0 0)) := by
    apply G.adj_symm
    apply stepZero E (coord 1 0)
    dsimp [off,flux]; abel
  have edge21 (g : V) : G.Adj (e (11,g)) (e (6,g+flux P Q 6 0)) := by
    apply G.adj_symm
    apply stepB E (coord 6 0) (coord 6 1) (by decide) (by decide)
    dsimp [off,flux]; abel
  apply barbell10 G e _ _ hu hv _ edge20 edge21
  intro i j hij
  simp only [tree10,mem_insert,mem_singleton,Prod.mk.injEq] at hij
  rcases hij with
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact edge0
  · exact edge1
  · exact edge2
  · exact edge3
  · exact edge4
  · exact edge5
  · exact edge6
  · exact edge7
  · exact edge8
  · exact edge9
  · exact edge10
  · exact edge11
  · exact edge12
  · exact edge13
  · exact edge14
  · exact edge15
  · exact edge16
  · exact edge17
  · exact edge18
  · exact edge19
end DyadicHex

open Finset
namespace DyadicHex

/-- If the defect set has density at least one third, avoiding the three
two-step differences forces periodicity along the first axis. -/
theorem packing {B : Type*} [AddCommGroup B] [Fintype B] (D : Finset B) (u v : B)
    (dense : Fintype.card B ≤ 3*D.card)
    (exclude : ∀ x, ¬(x ∈ D ∧ x+u ∈ D) ∧ ¬(x ∈ D ∧ x+v ∈ D) ∧
      ¬(x+u ∈ D ∧ x+v ∈ D)) :
    Fintype.card B = 3*D.card ∧ ∃ x ∈ D, x+u+u+u ∈ D := by
  classical
  let f (x : B) : ℕ := if x ∈ D then 1 else 0
  have sumF (t : B) : ∑ x : B, f (x+t) = D.card := by
    calc
      _ = ∑ x : B, f x := (Equiv.sum_comp (Equiv.addRight t) f)
      _ = _ := by simp [f]
  have total (s t w : B) (one : ∀ x, f (x+s) + f (x+t) + f (x+w) ≤ 1) :
      ∀ x, f (x+s) + f (x+t) + f (x+w) = 1 := by
    intro x
    by_contra h
    have lt : ∑ j : B, (f (j+s)+f (j+t)+f (j+w)) < ∑ _j : B, 1 := by
      apply sum_lt_sum (fun i _ => one i)
      exact ⟨x,mem_univ _,lt_of_le_of_ne (one x) h⟩
    simp only [sum_add_distrib,sumF,sum_const,card_univ,smul_eq_mul,mul_one] at lt
    omega
  have upper (x : B) : f x + f (x+u) + f (x+v) ≤ 1 := by
    obtain ⟨a,b,c⟩ := exclude x
    unfold f
    split <;> split <;> split <;> simp_all
  have lower (x : B) : f (x+u+v) + f (x+u) + f (x+v) ≤ 1 := by
    have a := (exclude (x+u)).2.1
    have b := (exclude (x+v)).1
    have c := (exclude x).2.2
    rw [show x+v+u=x+u+v by abel] at b
    unfold f
    split <;> split <;> split <;> simp_all
  have T (x : B) : f x + f (x+u) + f (x+v) = 1 := by
    simpa using total 0 u v (by simpa using upper) x
  have R (x : B) : f (x+u+v) + f (x+u) + f (x+v) = 1 := by
    simpa [add_assoc] using total (u+v) u v (by simpa [add_assoc] using lower) x
  have diag (x : B) : f (x+u+v)=f x := by have := T x; have := R x; omega
  have row (x : B) : f (x+u)+f (x+u+u)+f x = 1 := by simpa [diag] using T (x+u)
  have nz : D.Nonempty := card_pos.mp (by have := Fintype.card_pos (α := B); omega)
  obtain ⟨x,hx⟩ := nz
  have hsum := Finset.sum_congr (s₁ := (univ : Finset B)) rfl (fun j _ => T j)
  have sumSame : ∑ x : B, f x = D.card := by simpa using sumF 0
  simp only [sum_add_distrib,sumSame,sumF,sum_const,card_univ,smul_eq_mul,mul_one] at hsum
  refine ⟨by omega,x,hx,?_⟩
  have := row x
  have := row (x+u)
  have hx' : f x=1 := by simp [f,hx]
  have hh : f (x+u+u+u)=1 := by omega
  simpa [f] using hh

end DyadicHex

namespace DyadicHex
open SimpleGraph Finset

def place {B : Type*} [AddCommGroup B] (a b x : B) (i : Tile) :=
  x + i.1.val • a + i.2.val • b

def defect {B V : Type*} [AddCommGroup B] [AddCommGroup V] (a b : B) (P Q : B → V) (x : B) :=
  P x + Q (x+a) - P (x+b) - Q x

private theorem denseBase {X B V : Type} [Fintype B] [AddCommGroup B] [AddCommGroup V]
    (G : SimpleGraph (Bool × X)) (p q : Equiv.Perm X) (e : B × V ≃ X)
    (a b : B) (P Q : B → V) (D : Finset B)
    (pEq : ∀ x g, p (e (x,g)) = e (x+a,g+P x))
    (qEq : ∀ x g, q (e (x,g)) = e (x+b,g+Q x))
    (comm : ∀ x g, p (q (e (x,g))) = q (p (e (x,g))) ↔ x ∉ D)
    (sep : ∀ x, p x≠x ∧ q x≠x ∧ p x≠q x)
    (adj₀ : ∀ z, G.Adj (false,z) (true,z))
    (adj₁ : ∀ z, G.Adj (false,z) (true,p z))
    (adj₂ : ∀ z, G.Adj (false,z) (true,q z))
    (absent : ¬(cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G)) :
    Fintype.card B ≤ 3*D.card := by
  classical
  apply OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.CommutationDensity.one_third
    D (Equiv.addRight a) (Equiv.addRight b)
  intro x hx
  let z := e (x,0)
  have invP : p.symm z = e (x-a,-P (x-a)) := by
    apply p.injective
    rw [p.apply_symm_apply,pEq]
    simp [z]
  have invQ : q.symm z = e (x-b,-Q (x-b)) := by
    apply q.injective
    rw [q.apply_symm_apply,qEq]
    simp [z]
  have c := (comm x 0).2 hx
  have l₁ (h : x-a ∉ D) : p (q (p.symm z)) = q (p (p.symm z)) := by
    rw [invP]; exact (comm _ _).2 h
  have r₁ (h : x+a ∉ D) : p (q (p z)) = q (p (p z)) := by
    dsimp only [z]; rw [pEq]; exact (comm _ _).2 h
  have l₂ (h : x-b ∉ D) : p (q (q.symm z)) = q (p (q.symm z)) := by
    rw [invQ]; exact (comm _ _).2 h
  have r₂ (h : x+b ∉ D) : p (q (q z)) = q (p (q z)) := by
    dsimp only [z]; rw [qEq]; exact (comm _ _).2 h
  have z₀ := OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.LocalCommutation.near0
    G p q sep adj₀ adj₁ adj₂ z c
  have z₁ := OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.LocalCommutation.near1
    G p q sep adj₀ adj₁ adj₂ z c
  have z₂ := OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.LocalCommutation.near2
    G p q sep adj₀ adj₁ adj₂ z c
  have z₃ := OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.LocalCommutation.near3
    G p q sep adj₀ adj₁ adj₂ z c
  have inv (t : B) : (Equiv.addRight t).symm x=x-t := by
    apply (Equiv.addRight t).injective
    rw [Equiv.apply_symm_apply]
    change x=x-t+t
    simp
  rw [inv,inv]
  change 2 ≤ (if x+a ∈ D then 1 else 0) + (if x-a ∈ D then 1 else 0) +
    (if x+b ∈ D then 1 else 0) + (if x-b ∈ D then 1 else 0)
  by_cases h₁ : x+a ∈ D <;> by_cases h₂ : x-a ∈ D <;>
    by_cases h₃ : x+b ∈ D <;> by_cases h₄ : x-b ∈ D <;> simp [*] <;>
      first | exact absent (z₀ (r₁ h₁) (l₂ h₄) (r₂ h₃)) | exact absent (z₁ (l₁ h₂) (l₂ h₄) (r₂ h₃)) |
        exact absent (z₂ (l₁ h₂) (r₁ h₁) (r₂ h₃)) | exact absent (z₃ (l₁ h₂) (r₁ h₁) (l₂ h₄))

theorem family {X B V : Type} [Fintype B]
    [AddCommGroup B] [AddCommGroup V] (p q : Equiv.Perm X) (e : B × V ≃ X)
    (a b : B) (P Q : B → V)
    (embed : Function.Injective (place a b 0))
    (pEq : ∀ x g, p (e (x,g)) = e (x+a,g+P x))
    (qEq : ∀ x g, q (e (x,g)) = e (x+b,g+Q x))
    (sep : ∀ x, p x≠x ∧ q x≠x ∧ p x≠q x)
    (G : SimpleGraph (Bool × X))
    (adj₀ : ∀ z, G.Adj (false,z) (true,z))
    (adj₁ : ∀ z, G.Adj (false,z) (true,p z))
    (adj₂ : ∀ z, G.Adj (false,z) (true,q z)) :
    ∃ k : ℕ, 2 ≤ k ∧ k ≤ 6 ∧ (k = 6 → 3 ∣ Fintype.card B) ∧ cycleGraph (2^k) ⊑ G := by
  classical
  by_contra neg
  have absent {k : ℕ} (lo : 2≤k) (hi : k≤5) (h : cycleGraph (2^k) ⊑ G) : False :=
    neg ⟨k,lo,by omega,by omega,h⟩
  have n4 : ¬ cycleGraph 4 ⊑ G := absent (k:=2) (by decide) (by decide)
  have n8 : ¬ cycleGraph 8 ⊑ G := absent (k:=3) (by decide) (by decide)
  have n16 : ¬ cycleGraph 16 ⊑ G := absent (k:=4) (by decide) (by decide)
  have n32 : ¬ cycleGraph 32 ⊑ G := absent (k:=5) (by decide) (by decide)
  let D := univ.filter (fun x => defect a b P Q x ≠ 0)
  have hdef (x : B) (g : V) : p (q (e (x,g))) = q (p (e (x,g))) ↔ defect a b P Q x = 0 := by
    rw [qEq,pEq,pEq,qEq,e.injective.eq_iff,Prod.mk.injEq]
    have eq : x+b+a=x+a+b := by abel
    simp only [eq,true_and,defect]
    constructor <;> intro h <;> abel_nf at * <;> grind
  have comm (x : B) (g : V) : p (q (e (x,g))) = q (p (e (x,g))) ↔ x ∉ D := by
    simpa [D] using hdef x g
  have dense := denseBase G p q e a b P Q D pEq qEq comm sep adj₀ adj₁ adj₂
    (fun h => h.elim n4 (fun z => z.elim n8 n16))
  have placeInj (x : B) : Function.Injective (place a b x) := by
    intro i j h
    apply embed
    simpa only [place,zero_add,add_assoc,add_right_inj] using h
  let F (x : B) : Site × V ↪ Bool × X :=
    ⟨fun z => (z.1.1,e (place a b x z.1.2,z.2)),by
      rintro ⟨⟨s,i⟩,g⟩ ⟨⟨t,j⟩,h⟩ eq
      change (s,e (place a b x i,g))=(t,e (place a b x j,h)) at eq
      obtain ⟨rfl,hh⟩ := Prod.mk.inj eq
      obtain ⟨hij,rfl⟩ := Prod.mk.inj (e.injective hh)
      rw [placeInj x hij]⟩
  have E (x : B) : TileEdges G (F x) (P ∘ place a b x) (Q ∘ place a b x) := by
    constructor
    · intro i g; exact adj₀ _
    · intro i j h₁ h₂ g
      have loc : place a b x j = place a b x i + a := by
        simp only [place,h₁,h₂,add_nsmul,one_nsmul]; abel
      change G.Adj (false,e (_,g)) (true,e (place a b x j,g+P _))
      rw [loc,← pEq]; exact adj₁ _
    · intro i j h₁ h₂ g
      have loc : place a b x j = place a b x i + b := by
        simp only [place,h₁,h₂,add_nsmul,one_nsmul]; abel
      change G.Adj (false,e (_,g)) (true,e (place a b x j,g+Q _))
      rw [loc,← qEq]; exact adj₂ _
  have val (x : B) (i j : ℕ) (hi : i+1 < 8) (hj : j+1 < 4) :
      flux (P ∘ place a b x) (Q ∘ place a b x) i j =
        defect a b P Q (x+i • a+j • b) := by
    have hi₀ : i<8 := by omega
    have hj₀ : j<4 := by omega
    simp only [flux,defect,Function.comp_apply,place,coord,Fin.val_ofNat,Nat.mod_eq_of_lt hi,
      Nat.mod_eq_of_lt hj,Nat.mod_eq_of_lt hi₀,Nat.mod_eq_of_lt hj₀,add_nsmul,one_nsmul]
    ac_rfl
  have nz (x : B) (i j : ℕ) (hi : i+1<8) (hj : j+1<4) (h : x+i • a+j • b ∈ D) :
      flux (P ∘ place a b x) (Q ∘ place a b x) i j ≠ 0 := by
    rw [val x i j hi hj]
    exact (mem_filter.mp h).2
  have exclude (x : B) : ¬(x∈D ∧ x+2 • a∈D) ∧ ¬(x∈D ∧ x+2 • b∈D) ∧
      ¬(x+2 • a∈D ∧ x+2 • b∈D) := by
    have skip := fun (h : cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G) => h.elim n16 n32
    refine ⟨?_,?_,?_⟩
    · rintro ⟨hl,hr⟩
      exact skip (patchEast G (F x) _ _ (E x)
        (nz x 0 0 (by decide) (by decide) (by simpa using hl))
        (nz x 2 0 (by decide) (by decide) (by simpa using hr)))
    · rintro ⟨hl,hr⟩
      exact skip (patchNorth G (F x) _ _ (E x)
        (nz x 0 0 (by decide) (by decide) (by simpa using hl))
        (nz x 0 2 (by decide) (by decide) (by simpa using hr)))
    · rintro ⟨hl,hr⟩
      exact skip (patchDiagonal G (F x) _ _ (E x)
        (nz x 0 2 (by decide) (by decide) (by simpa using hr))
        (nz x 2 0 (by decide) (by decide) (by simpa using hl)))
  obtain ⟨hcard,x,hx,h₆⟩ := packing D (2 • a) (2 • b) dense exclude
  have h₆' : x+6 • a+0 • b ∈ D := by
    rw [zero_smul,add_zero,show x+6 • a=x+2 • a+2 • a+2 • a by abel]
    exact h₆
  exact (patchFar G (F x) _ _ (E x)
    (nz x 0 0 (by decide) (by decide) (by simpa using hx))
    (nz x 6 0 (by decide) (by decide) h₆')).elim n32 (fun h => neg ⟨6,by decide,by decide,fun _ => ⟨D.card,hcard⟩,h⟩)

end DyadicHex

namespace DyadicHex
open SimpleGraph

private def voltageShift {B V : Type} [AddCommGroup B] [AddCommGroup V]
    (a : B) (P : B → V) : Equiv.Perm (B × V) where
  toFun z := (z.1+a,z.2+P z.1)
  invFun z := (z.1-a,z.2-P (z.1-a))
  left_inv := by rintro ⟨x,g⟩; simp
  right_inv := by rintro ⟨x,g⟩; simp

/-- A three-matching abelian lift over a finite abelian base admitting an embedded
8-by-4 hexagonal patch contains a dyadic cycle of length at most 64. The bound is 32
when three does not divide the number of base coordinates. -/
theorem voltageFamily {B V : Type} [AddCommGroup B] [Fintype B] [AddCommGroup V]
    (a b : B) (az : a ≠ 0) (bz : b ≠ 0) (ab : a ≠ b)
    (chart : Function.Injective (fun i : Fin 8 × Fin 4 => i.1.val • a+i.2.val • b))
    (w : B → Fin 3 → V) :
    let G := SimpleGraph.fromRel fun l r : Bool × B × V =>
      ∃ (i : B) (k : Fin 3) (g : V),
        l = (false,i,g) ∧ r = (true,i + (![0,a,b] : Fin 3 → B) k,g+w i k)
    ∃ k : ℕ, 2 ≤ k ∧ k ≤ 6 ∧ (k=6 → 3 ∣ Fintype.card B) ∧ cycleGraph (2^k) ⊑ G := by
  classical
  intro G
  let P (x : B) := w x 1 - w (x+a) 0
  let Q (x : B) := w x 2 - w (x+b) 0
  let p := voltageShift a P
  let q := voltageShift b Q
  let relabel : (Bool × B × V) ↪ (Bool × B × V) :=
    ⟨fun z => (z.1,z.2.1,z.2.2+(if z.1 then w z.2.1 0 else 0)),by
      rintro ⟨s,x,g⟩ ⟨t,y,h⟩ he
      obtain ⟨rfl,h'⟩ := Prod.mk.inj he
      obtain ⟨rfl,h''⟩ := Prod.mk.inj h'
      exact congrArg (fun k => (s,x,k)) (show g=h from add_right_cancel h'')⟩
  let H := G.comap relabel
  have adj (x : B) (i : Fin 3) (g : V) :
      G.Adj (false,x,g) (true,x+(![0,a,b] : Fin 3 → B) i,g+w x i) :=
    ⟨by simp,Or.inl ⟨x,i,g,rfl,rfl⟩⟩
  have adj₀ : ∀ z, H.Adj (false,z) (true,z) := by
    rintro ⟨x,g⟩
    change G.Adj (false,x,g+0) (true,x,g+w x 0)
    simpa using adj x 0 g
  have adj₁ : ∀ z, H.Adj (false,z) (true,p z) := by
    rintro ⟨x,g⟩
    change G.Adj (false,x,g+0) (true,x+a,g+P x+w (x+a) 0)
    simpa [P,add_assoc] using adj x 1 g
  have adj₂ : ∀ z, H.Adj (false,z) (true,q z) := by
    rintro ⟨x,g⟩
    change G.Adj (false,x,g+0) (true,x+b,g+Q x+w (x+b) 0)
    simpa [Q,add_assoc] using adj x 2 g
  have sep : ∀ z, p z ≠ z ∧ q z ≠ z ∧ p z ≠ q z := by
    rintro ⟨x,g⟩
    refine ⟨fun h => az ?_,fun h => bz ?_,fun h => ab ?_⟩
    · have eq : x+a=x := congrArg Prod.fst h
      simpa using eq
    · have eq : x+b=x := congrArg Prod.fst h
      simpa using eq
    · exact add_left_cancel (show x+a=x+b from congrArg Prod.fst h)
  obtain ⟨k,lo,hi,three,cyc⟩ := family p q (Equiv.refl _) a b P Q
    (by intro i j h; apply chart; simpa [place] using h) (fun _ _ => rfl) (fun _ _ => rfl) sep H adj₀ adj₁ adj₂
  exact ⟨k,lo,hi,three,cyc.trans (SimpleGraph.Embedding.comap relabel G).isContained⟩

end DyadicHex

theorem OMA.solution : OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H1_R1.H1 := by
  intro B _ _ a b az bz ab chart three V _ w G
  classical
  let _ := Fintype.ofFinite B
  obtain ⟨k,lo,hi,divides,cycle⟩ := DyadicHex.voltageFamily a b az bz ab chart w
  rw [Nat.card_eq_fintype_card] at three
  have noSix : k ≠ 6 := fun eq => three (divides eq)
  have small : k ≤ 5 := by omega
  interval_cases k
  · exact Or.inl cycle
  · exact Or.inr (Or.inl cycle)
  · exact Or.inr (Or.inr (Or.inl cycle))
  · exact Or.inr (Or.inr (Or.inr cycle))
