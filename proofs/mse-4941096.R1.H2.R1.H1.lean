import OMAReductions.R_mse_4941096_R1_H2_R1
import Mathlib.Tactic

/-!
A short arc has length at most three. Complete the orientation on all pairs
at distances one through three. On a stretch of short-only sources, the number
of forward crossings of successive cuts is nondecreasing. Its range is 0..6,
so one of seven consecutive eight-site blocks has constant cut count.

The finite lemma below verifies that eight such regular sites, with the
strict second-neighborhood bound at their two centers, force a one-way cut.
A bandwidth buffer on each side then extends the forbidden direction to
the whole graph, contradicting strong connectivity.
-/

open Finset OMA.S_mse_4941096

namespace WidthThree

/-- The forward orientations from a vertex to its next three successors. -/
structure Mask where
  a : Bool
  b : Bool
  c : Bool

def row (out : ℤ → Finset ℤ) (x : ℤ) : Mask :=
  ⟨decide (x+1 ∈ out x), decide (x+2 ∈ out x), decide (x+3 ∈ out x)⟩

def put (b : Bool) (i : ℤ) (s : Finset ℤ) : Finset ℤ := if b then insert i s else s

@[simp] theorem mem_put {n i : ℤ} {b : Bool} {s : Finset ℤ} :
    n ∈ put b i s ↔ (b = true ∧ n=i) ∨ n∈s := by cases b <;> simp [put]

theorem card_put (b : Bool) (i : ℤ) (s : Finset ℤ) (h : i ∉ s) :
    (put b i s).card = b.toNat + s.card := by
  cases b <;> simp [put,h,Nat.add_comm]

def neighborhood (v : ℤ) (a b c d e f : Bool) : Finset ℤ :=
  put a (v-3) (put b (v-2) (put c (v-1) (put d (v+1) (put e (v+2) (put f (v+3) ∅)))))

theorem card_neighborhood (x : ℤ) (a b c d e f : Bool) :
    (neighborhood x a b c d e f).card =
      a.toNat + b.toNat + c.toNat + d.toNat + e.toNat + f.toNat := by
  unfold neighborhood
  repeat rw [card_put _ _ _ (by simp +arith)]
  simp [Nat.add_assoc]

/-- Short pairs missing in the original graph are directed from right to left. -/
def completed (r : ℤ → Mask) (x : ℤ) :=
  neighborhood x (!(r (x-3)).c) (!(r (x-2)).b) (!(r (x-1)).a)
      (r x).a (r x).b (r x).c

/-- Number of rightward arcs crossing the cut just after x in the completion. -/
def flow (r : ℤ → Mask) (x : ℤ) :=
  (r x).a.toNat + (r x).b.toNat + (r x).c.toNat +
  (r (x-1)).b.toNat + (r (x-1)).c.toNat + (r (x-2)).c.toNat

theorem flow_balance (r : ℤ → Mask) (x : ℤ) :
    flow r x + 3 = flow r (x-1) + (completed r x).card := by
  have comp (b : Bool) : b.toNat + (!b).toNat = 1 := by cases b <;> rfl
  have := comp (r (x-3)).c
  have := comp (r (x-2)).b
  have := comp (r (x-1)).a
  simp only [flow, completed, card_neighborhood, show x-1-1=x-2 by omega,
    show x-1-2=x-3 by omega]
  omega

theorem actual_subset {out : ℤ → Finset ℤ}
    (irr : ∀ x, x ∉ out x) (anti : ∀ x y, y ∈ out x → x ∉ out y)
    (x : ℤ) (bound : ∀ y, y ∈ out x → x-3 ≤ y ∧ y ≤ x+3) :
    out x ⊆ completed (row out) x := by
  intro y hy
  have hs := bound y hy
  have hn : y ≠ x := fun h => irr x (h ▸ hy)
  have hr := anti x y hy
  have : y=x-3 ∨ y=x-2 ∨ y=x-1 ∨ y=x+1 ∨ y=x+2 ∨ y=x+3 := by omega
  rcases this with h|h|h|h|h|h <;> subst y <;>
    simp_all [completed, neighborhood, row]

end WidthThree

namespace WidthThree.Window
open Finset
abbrev Row := ℤ × Finset ℤ
def basis (i : ℤ) : Finset ℤ := {i-3,i-2,i-1,i+1,i+2,i+3}
/-- Check the center rows first so the second-neighborhood bound prunes early. -/
def order : List ℤ := [3,4,2,5,1,6,0,7]

def agree (x : ℤ) (s : Finset ℤ) (p : Row) : Bool :=
  if x ≤ p.1+3 ∧ p.1 ≤ x+3 then decide ((p.1 ∈ s) ↔ (x ∉ p.2)) else true

/-- Destinations at distance two witnessed by the rows already assigned. -/
def seenSecond (s : Finset ℤ) : List Row → Finset ℤ
  | [] => ∅
  | p :: tail => if p.1 ∈ s then p.2 ∪ seenSecond s tail else seenSecond s tail

def sizeOK (d : List Row) (p : Row) : Bool :=
  if p.1 = 3 ∨ p.1 = 4 then decide ((seenSecond p.2 d \ p.2).card ≤ 3) else true

def legal (i : ℤ) (s : Finset ℤ) (d : List Row) : Bool :=
  d.all (agree i s) && ((i,s)::d).all (sizeOK ((i,s)::d))

def closedCut (d : List Row) : Prop :=
  (∀ p ∈ d, p.1 ≤ 3 → ∀ j ∈ p.2, j ≤ 3) ∨
  (∀ p ∈ d, 3 < p.1 → ∀ j ∈ p.2, 3 < j)

instance (d : List Row) : Decidable (closedCut d) := by unfold closedCut; infer_instance

/-- Quantify over the three-element subsets of each row and test every surviving cut. -/
def check : List ℤ → List Row → Bool
  | [], d => decide (closedCut d)
  | i::rest, d => decide (∀ s ∈ (basis i).powersetCard 3, legal i s d = true →
                               check rest ((i,s)::d) = true)

set_option maxRecDepth 150000 in
set_option maxHeartbeats 0 in
theorem certificate : check order [] = true := by decide +kernel
end WidthThree.Window

namespace WidthThree.Window
open Finset OMA.S_mse_4941096

def sound (g : ℤ → Finset ℤ) (d : List Row) : Prop :=
  ∀ p ∈ d, p.1 ∈ order ∧ p.2 = g p.1

private theorem seen_subset {g : ℤ → Finset ℤ} {d : List Row} (h : sound g d)
    (s : Finset ℤ) : seenSecond s d ⊆ s.biUnion g := by
  induction d with
  | nil => simp [seenSecond]
  | cons p d ih =>
    have hp := (h p (by simp)).2
    have ht := ih (fun z hz => h z (by simp [hz]))
    intro j hj
    simp only [seenSecond] at hj
    split at hj
    next hx =>
      rcases mem_union.mp hj with hj|hj
      · exact mem_biUnion.mpr ⟨p.1,hx,hp ▸ hj⟩
      · exact ht hj
    next => exact ht hj

/-- Every real neighborhood assignment meeting these bounds survives the finite tests. -/
theorem local_cut (g : ℤ → Finset ℤ) (cert : check order [] = true)
    (sub : ∀ i ∈ order, g i ⊆ basis i)
    (deg : ∀ i ∈ order, (g i).card = 3)
    (pair : ∀ i ∈ order, ∀ j ∈ order, i ≠ j → i ≤ j+3 → j ≤ i+3 →
      (j ∈ g i ↔ i ∉ g j))
    (size : ∀ i, i = 3 ∨ i = 4 → (second g i).card ≤ 3) :
    (∀ i ∈ order, i ≤ 3 → ∀ j ∈ g i, j ≤ 3) ∨
    (∀ i ∈ order, 3 < i → ∀ j ∈ g i, 3 < j) := by
  have step {i : ℤ} (hi : i ∈ order) {d : List Row} (hd : sound g d)
      (fresh : ∀ p ∈ d, i ≠ p.1) : legal i (g i) d = true := by
    have hs : sound g ((i,g i)::d) := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨hi,rfl⟩
      · exact hd _ hp
    simp only [legal,Bool.and_eq_true,List.all_eq_true]
    constructor
    · intro p hp
      simp only [agree]; split
      next h =>
        rw [(hd p hp).2]
        exact decide_eq_true (pair i hi p.1 (hd p hp).1 (fresh p hp) h.1 h.2)
      next => rfl
    · intro p hp
      simp only [sizeOK]; split
      next center =>
        rw [(hs p hp).2]
        apply decide_eq_true
        exact (card_le_card (fun j hj => mem_sdiff.mpr ⟨seen_subset hs (g p.1) (mem_sdiff.mp hj).1,(mem_sdiff.mp hj).2⟩)).trans (size p.1 center)
      next => rfl
  let label := fun i : ℤ => (i,g i)
  have walk (is : List ℤ) (d : List Row) (valid : ∀ i ∈ is, i ∈ order)
      (hn : is.Nodup) (hd : sound g d) (fresh : ∀ i ∈ is, ∀ p ∈ d, i ≠ p.1)
      (h : check is d = true) : closedCut (is.reverse.map label ++ d) := by
    induction is generalizing d with
    | nil => exact of_decide_eq_true h
    | cons i is ih =>
      have hi := valid i (by simp)
      have hd' : sound g (label i::d) := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨hi,rfl⟩
        · exact hd p hp
      have h' := of_decide_eq_true h (g i) (mem_powersetCard.mpr ⟨sub i hi,deg i hi⟩)
        (step hi hd (fresh i (by simp)))
      have hz := ih (label i::d) (fun j hj => valid j (by simp [hj])) (List.nodup_cons.mp hn).2 hd' (by
        intro j hj p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · intro e; change j = i at e; subst j; exact (List.nodup_cons.mp hn).1 hj
        · exact fresh j (by simp [hj]) p hp) h'
      simpa [List.reverse_cons,List.append_assoc] using hz
  have h := walk order [] (by simp) (by decide) (by simp [sound]) (by simp) cert
  simp only [List.append_nil] at h
  have included (i : ℤ) (hi : i ∈ order) : label i ∈ order.reverse.map label :=
    List.mem_map.mpr ⟨i,List.mem_reverse.mpr hi,rfl⟩
  rcases h with h|h
  · exact Or.inl fun i hi => h _ (included i hi)
  · exact Or.inr fun i hi => h _ (included i hi)
end WidthThree.Window

namespace WidthThree
open Finset OMA.S_mse_4941096
private theorem pair_complete (r : ℤ → Mask) (i j : ℤ) (hne : i ≠ j)
    (lo : i ≤ j+3) (hi : j ≤ i+3) : j∈completed r i ↔ i∉completed r j := by
  have : j=i-3 ∨ j=i-2 ∨ j=i-1 ∨ j=i+1 ∨ j=i+2 ∨ j=i+3 := by omega
  rcases this with e|e|e|e|e|e <;> subst j <;> simp +arith [completed,neighborhood]

private def moved (out : ℤ → Finset ℤ) (z i : ℤ) :=
  (out (z+i)).image (fun x => x-z)

private theorem mem_moved {out : ℤ → Finset ℤ} {z i j : ℤ} :
    j ∈ moved out z i ↔ z+j ∈ out (z+i) := by
  constructor
  · intro h
    obtain ⟨k,hk,e⟩ := mem_image.mp h
    rwa [show z+j=k by omega]
  · intro h
    exact mem_image.mpr ⟨_,h,by omega⟩

private theorem moved_card (out : ℤ → Finset ℤ) (z i : ℤ) :
    (moved out z i).card = (out (z+i)).card :=
  card_image_of_injective _ (fun x y e => by omega)

private theorem moved_second_card (out : ℤ → Finset ℤ) (z i : ℤ) :
    (second (moved out z) i).card = (second out (z+i)).card := by
  have h : second (moved out z) i = (second out (z+i)).image (fun x => x-z) := by
    ext j
    simp only [second,mem_sdiff,mem_biUnion,mem_moved,mem_image]
    constructor
    · rintro ⟨⟨k,hk,hj⟩,hn⟩
      exact ⟨z+j,⟨⟨z+k,hk,hj⟩,hn⟩,by omega⟩
    · rintro ⟨a,⟨⟨k,hk,hj⟩,hn⟩,he⟩
      have ha : z+j=a := by omega
      rw [ha]
      exact ⟨⟨k-z,by simpa using hk,by simpa using hj⟩,hn⟩
  rw [h]
  exact card_image_of_injective _ (fun x y e => by omega)

private theorem closed_path {out : ℤ → Finset ℤ} {P : ℤ → Prop}
    (h : ∀ a, P a → ∀ b ∈ out a, P b) {v w : ℤ} (hv : P v)
    (path : Relation.ReflTransGen (fun i j => j ∈ out i) v w) : P w := by
  induction path with
  | refl => exact hv
  | tail _ hab ih => exact h _ ih _ hab

/-- For short crossings of the central cut, the eight-site lemma blocks all
paths across it in one direction. -/
theorem obstruct_patch (cert : Window.check Window.order [] = true)
    (out : ℤ → Finset ℤ) (hg : exampleGraph out) (z : ℤ)
    (regular : ∀ i : ℤ, 0 ≤ i → i ≤ 7 →
      out (z+i) = completed (row out) (z+i) ∧ (out (z+i)).card = 3)
    (crossing : ∀ x y, y ∈ out x →
      ((x ≤ z+3 ∧ z+3 < y) ∨ (y ≤ z+3 ∧ z+3 < x)) → x-3 ≤ y ∧ y ≤ x+3) : False := by
  obtain ⟨irr,anti,strong,_,equal⟩ := hg
  let g := moved out z
  have range_iff (i : ℤ) : i ∈ Window.order ↔ 0 ≤ i ∧ i ≤ 7 := by
    constructor
    · intro h; simp [Window.order] at h; omega
    · rintro ⟨a,b⟩; interval_cases i <;> decide
  have actual (i : ℤ) (hi : i ∈ Window.order) := regular i ((range_iff i).mp hi).1 ((range_iff i).mp hi).2
  have sub (i : ℤ) (hi : i∈Window.order) : g i ⊆ Window.basis i := by
    intro j hj
    have h := mem_moved.mp hj
    have hh : z+j ∈ completed (row out) (z+i) := (actual i hi).1 ▸ h
    simp [completed,neighborhood] at hh
    have hn : i ≠ j := by rintro rfl; exact irr _ h
    simp only [Window.basis,mem_insert,mem_singleton]
    omega
  have three (i : ℤ) (hi : i∈Window.order) : (g i).card = 3 :=
    (moved_card out z i).trans (actual i hi).2
  have size (i : ℤ) (center : i = 3 ∨ i = 4) : (second g i).card ≤ 3 := by
    have hi : i ∈ Window.order := (range_iff i).mpr (by omega)
    change (second (moved out z) i).card ≤ 3
    rw [moved_second_card,←equal,(actual i hi).2]
  have pair (i : ℤ) (hi : i∈Window.order) (j : ℤ) (hj : j∈Window.order)
      (hne : i ≠ j) (ha : i ≤ j+3) (hb : j ≤ i+3) : j ∈ g i ↔ i ∉ g j := by
    change j ∈ moved out z i ↔ ¬ i ∈ moved out z j
    rw [mem_moved,mem_moved,(actual i hi).1,(actual j hj).1]
    exact pair_complete _ _ _ (by omega) (by omega) (by omega)
  rcases Window.local_cut g cert sub three pair size with h|h
  · have closed (x : ℤ) (hx : x ≤ z+3) (y : ℤ) (hy : y ∈ out x) : y ≤ z+3 := by
      by_contra! hbad
      have hyb := crossing x y hy (by omega)
      have hi := (range_iff (x-z)).mpr (by omega)
      have hm : y-z ∈ g (x-z) := mem_moved.mpr (by simpa using hy)
      have := h (x-z) hi (by omega) _ hm
      omega
    have impossible := closed_path (P := fun x => x ≤ z+3) closed
      (show z+3 ≤ z+3 by omega) (strong (z+3) (z+4))
    omega
  · have closed (x : ℤ) (hx : z+3 < x) (y : ℤ) (hy : y ∈ out x) : z+3 < y := by
      by_contra! hbad
      have hyb := crossing x y hy (by omega)
      have hi := (range_iff (x-z)).mpr (by omega)
      have hm : y-z ∈ g (x-z) := mem_moved.mpr (by simpa using hy)
      have := h (x-z) hi (by omega) _ hm
      omega
    have impossible := closed_path (P := fun x => z+3 < x) closed
      (show z+3 < z+4 by omega) (strong (z+4) (z+3))
    omega


private theorem flow_le_six (r : ℤ → Mask) (x : ℤ) : flow r x ≤ 6 := by
  have one (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
  unfold flow
  have := one (r x).a; have := one (r x).b; have := one (r x).c
  have := one (r (x-1)).b; have := one (r (x-1)).c; have := one (r (x-2)).c
  omega

/-- A 56-site run of short outgoing arcs contains eight successive regular sites. -/
theorem regular_patch {out : ℤ → Finset ℤ}
    (irr : ∀ x, x ∉ out x) (anti : ∀ x y, y ∈ out x → x ∉ out y)
    (deg : ∀ x, 3 ≤ (out x).card) (a : ℤ)
    (short : ∀ x, a ≤ x → x < a+56 → ∀ y ∈ out x, x-3 ≤ y ∧ y ≤ x+3) :
    ∃ z : ℤ, a ≤ z ∧ z+7 < a+56 ∧ ∀ i : ℤ, 0 ≤ i → i ≤ 7 →
      out (z+i) = completed (row out) (z+i) ∧ (out (z+i)).card = 3 := by
  let f (n : ℕ) := flow (row out) (a-1+(n:ℤ))
  have step (n : ℕ) (hn : n < 56) : f n ≤ f (n+1) := by
    have h := flow_balance (row out) (a+n)
    have hs := actual_subset irr anti (a+n) (short _ (by omega) (by omega))
    have hle := card_le_card hs
    have hdeg := deg (a+n)
    change flow _ _ ≤ flow _ _
    rw [show a-1+(n:ℤ)=a+n-1 by omega,show a-1+((n+1:ℕ):ℤ)=a+n by omega]
    omega
  have cmp (m n : ℕ) (hmn : m ≤ n) (hn : n ≤ 56) : f m ≤ f n := by
    induction n with
    | zero =>
      have hm : m=0 := by omega
      rw [hm]
    | succ n ih =>
      by_cases hm : m ≤ n
      · exact (ih hm (by omega)).trans (step n (by omega))
      · have hm' : m=n+1 := by omega
        rw [hm']
  have block : ∃ k : Fin 7, f (8*k.val+8) ≤ f (8*k.val) := by
    by_contra! h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    have h4 := h 4; have h5 := h 5; have h6 := h 6
    norm_num at h0 h1 h2 h3 h4 h5 h6
    have hc : f 56 ≤ 6 := flow_le_six _ _
    omega
  obtain ⟨k,hk⟩ := block
  have hk7 := k.isLt
  let z : ℤ := a+8*(k.val:ℤ)
  refine ⟨z,by dsimp [z]; omega,by dsimp [z]; omega,?_⟩
  intro i hi hi7
  let n := 8*k.val+i.toNat
  have e₁ : a-1+(n:ℤ)=z+i-1 := by dsimp [z,n]; omega
  have e₂ : a-1+((n+1:ℕ):ℤ)=z+i := by dsimp [z,n]; omega
  have h₁ := cmp (8*k.val) n (by dsimp [n]; omega) (by dsimp [n]; omega)
  have h₂ := cmp (n+1) (8*k.val+8) (by dsimp [n]; omega) (by omega)
  have eqf : f (n+1) = f n := by have := step n (by dsimp [n]; omega); omega
  change flow _ _ = flow _ _ at eqf
  rw [e₁,e₂] at eqf
  have balance := flow_balance (row out) (z+i)
  have sub := actual_subset irr anti (z+i) (short _ (by dsimp [z]; omega) (by dsimp [z]; omega))
  have le := card_le_card sub
  have ge := deg (z+i)
  exact ⟨eq_of_subset_of_card_le sub (by omega),by omega⟩

/-- In any counterexample, every block of 2W+56 consecutive vertices has a vertex
emitting an arc of length at least four, where W is any global bandwidth bound. -/
theorem long_arcs_in_every_interval (cert : Window.check Window.order [] = true)
    (out : ℤ → Finset ℤ) (hg : exampleGraph out) (deg : ∀ x, 3 ≤ (out x).card)
    (W : ℕ) (bound : ∀ x y, y ∈ out x → x-(W:ℤ) ≤ y ∧ y ≤ x+W) (L : ℤ) :
    ∃ x, L ≤ x ∧ x < L+2*(W:ℤ)+56 ∧ ∃ y ∈ out x, x+4 ≤ y ∨ y+4 ≤ x := by
  by_contra! h
  have short (x : ℤ) (hl : L ≤ x) (hu : x < L+2*(W:ℤ)+56)
      (y : ℤ) (hy : y ∈ out x) : x-3 ≤ y ∧ y ≤ x+3 := by
    have := h x hl hu y hy
    omega
  obtain ⟨z,hz,hzz,hr⟩ := regular_patch hg.1 hg.2.1 deg (L+W)
    (fun x hx hx' y hy => short x (by omega) (by omega) y hy)
  apply obstruct_patch cert out hg z hr
  intro x y hy cross
  obtain ⟨lo,up⟩ := bound x y hy
  exact short x (by rcases cross with h|h <;> omega) (by rcases cross with h|h <;> omega) y hy
end WidthThree

theorem OMA.solution : OMA.R_mse_4941096_R1_H2_R1.H1 :=
  WidthThree.long_arcs_in_every_interval WidthThree.Window.certificate
