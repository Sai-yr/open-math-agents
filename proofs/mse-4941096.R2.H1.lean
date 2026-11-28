import OMAReductions.R_mse_4941096_R2

import Mathlib


/-!
# Strict second-neighborhood expansion on two integer orbits

Represent the closed first neighborhoods by four finite sets of integer
displacements. Small two-step neighborhoods force equal diagonal sets and
constrain every closed displacement to one sign. A height function then
contradicts strong connectivity.
-/

open Finset
open scoped Pointwise
namespace TwoOrbit

abbrev F := Finset ℤ

def Gap (A : F) (a b : ℤ) : Prop :=
  a ∈ A ∧ b ∈ A ∧ a < b ∧ ∀ x ∈ A, x ≤ a ∨ b ≤ x

theorem cd {A B : F} (ha : A.Nonempty) (hb : B.Nonempty) :
    A.card + B.card ≤ (A+B).card+1 := by
  have := cauchy_davenport_add_of_linearOrder_isCancelAdd ha hb
  omega

theorem prev {A : F} {a : ℤ} (ha : a ∈ A) (h : ∃ b ∈ A, b<a) :
    ∃ b, Gap A b a := by
  let S:=A.filter (· < a)
  obtain ⟨b,hb,lt⟩ := h
  have ne : S.Nonempty := ⟨b,mem_filter.mpr ⟨hb,lt⟩⟩
  have hm := mem_filter.mp (S.max'_mem ne)
  refine ⟨S.max' ne,hm.1,ha,hm.2,?_⟩
  intro z hz
  by_cases small : z<a
  · exact Or.inl (S.le_max' z (mem_filter.mpr ⟨hz,small⟩))
  · exact Or.inr (by omega)

theorem nextGap {A : F} {a : ℤ} (ha : a ∈ A) (h : ∃ b ∈ A, a<b) :
    ∃ b, Gap A a b := by
  let S:=A.filter (a < ·)
  obtain ⟨b,hb,lt⟩ := h
  have ne : S.Nonempty := ⟨b,mem_filter.mpr ⟨hb,lt⟩⟩
  have hm := mem_filter.mp (S.min'_mem ne)
  refine ⟨S.min' ne,ha,hm.1,hm.2,?_⟩
  intro z hz
  by_cases big : a<z
  · exact Or.inr (S.min'_le z (mem_filter.mpr ⟨hz,big⟩))
  · exact Or.inl (by omega)

private lemma partitionGap {A : F} {a b : ℤ} (h : Gap A a b) :
    (A.filter (·≤a)).card + (A.filter (b≤·)).card = A.card := by
  have dis : Disjoint (A.filter (·≤a)) (A.filter (b≤·)) := by
    apply disjoint_left.mpr
    intro z h1 h2
    have := (mem_filter.mp h1).2
    have := (mem_filter.mp h2).2
    have := h.2.2.1
    omega
  rw [← card_union_of_disjoint dis]
  congr 1
  ext z
  simp only [mem_union,mem_filter]
  exact ⟨fun t => t.elim And.left And.left,fun hz => (h.2.2.2 z hz).imp (And.intro hz) (And.intro hz)⟩

/-- Opposite corners of two consecutive gaps give different interior sums
unless the gaps have the same length. -/
theorem sameGap {A B : F} {a a' b b' : ℤ} (h : Gap A a a') (k : Gap B b b')
    (minimal : (A+B).card+1 = A.card+B.card) : a'-a = b'-b := by
  by_contra neq
  let L := A.filter (·≤a) + B.filter (·≤b)
  let U := A.filter (a'≤·) + B.filter (b'≤·)
  let M : F := {a+b',a'+b}
  have lab (z : ℤ) (hz : z∈L) : z≤a+b := by
    obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hz
    exact add_le_add (mem_filter.mp hx).2 (mem_filter.mp hy).2
  have uab (z : ℤ) (hz : z∈U) : a'+b'≤z := by
    obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hz
    exact add_le_add (mem_filter.mp hx).2 (mem_filter.mp hy).2
  have ha := h.2.2.1
  have hb := k.2.2.1
  have mab (z : ℤ) (hz : z∈M) : a+b<z ∧ z<a'+b' := by
    rcases mem_insert.mp hz with rfl|hz
    · omega
    · have := mem_singleton.mp hz; omega
  have dl : Disjoint L M := disjoint_left.mpr (fun z hz hm => (mab z hm).1.not_ge (lab z hz))
  have du : Disjoint (L∪M) U := by
    apply disjoint_left.mpr
    intro z hz hu
    have := uab z hu
    rcases mem_union.mp hz with hh|hh
    · have := lab z hh; omega
    · have := mab z hh; omega
  have sub : (L∪M)∪U ⊆ A+B := by
    apply union_subset
    · apply union_subset
      · exact add_subset_add (filter_subset ..) (filter_subset ..)
      · intro z hz
        rcases mem_insert.mp hz with rfl|hh
        · exact add_mem_add h.1 k.2.1
        · rw [mem_singleton.mp hh]; exact add_mem_add h.2.1 k.1
    · exact add_subset_add (filter_subset ..) (filter_subset ..)
  have cards := card_le_card sub
  rw [card_union_of_disjoint du,card_union_of_disjoint dl] at cards
  have cm : M.card=2 := card_pair (by omega)
  have cl := cd (A:=A.filter (·≤a)) (B:=B.filter (·≤b))
    ⟨a,mem_filter.mpr ⟨h.1,le_rfl⟩⟩ ⟨b,mem_filter.mpr ⟨k.1,le_rfl⟩⟩
  have cu := cd (A:=A.filter (a'≤·)) (B:=B.filter (b'≤·))
    ⟨a',mem_filter.mpr ⟨h.2.1,le_rfl⟩⟩ ⟨b',mem_filter.mpr ⟨k.2.1,le_rfl⟩⟩
  change _ ≤ L.card+1 at cl
  change _ ≤ U.card+1 at cu
  have := partitionGap h
  have := partitionGap k
  omega
end TwoOrbit

namespace TwoOrbit
open Finset
open scoped Pointwise

private theorem sameDiagonal {X Y T U : F} (xz : 0∈X) (yz : 0∈Y)
    (t : T.Nonempty) (u : U.Nonempty) (anti : 0∉T+U)
    (a : ((X+X)∪(T+U)).card+(T+(X∪Y)).card+1≤2*(X.card+T.card))
    (b : ((Y+Y)∪(T+U)).card+(U+(X∪Y)).card+1≤2*(Y.card+U.card)) : X=Y := by
  let L := (X+X)∪(T+U)
  let R := (Y+Y)∪(T+U)
  let D := (X+X)∪(Y+Y)
  have covers : D ⊆ L∪R := union_subset
    (fun _ h => mem_union_left _ (mem_union_left _ h))
    (fun _ h => mem_union_right _ (mem_union_left _ h))
  have both : insert 0 (T+U) ⊆ L∩R := by
    intro z hz
    rcases mem_insert.mp hz with rfl|hs
    · exact mem_inter.mpr ⟨mem_union_left _ (by simpa using add_mem_add xz xz),
        mem_union_left _ (by simpa using add_mem_add yz yz)⟩
    · exact mem_inter.mpr ⟨mem_union_right _ hs,mem_union_right _ hs⟩
  have sz := card_le_card both
  rw [card_insert_of_notMem anti] at sz
  have cov := card_le_card covers
  have total := card_union_add_card_inter L R
  have xy := card_union_add_card_inter X Y
  have nz : (X∪Y).Nonempty := ⟨0,mem_union_left _ xz⟩
  have c1 := cd t nz
  have c2 := cd u nz
  have c3 := cd t u
  change L.card+_+1≤_ at a
  change R.card+_+1≤_ at b
  have key : D.card≤2*(X∩Y).card := by omega
  have cx := cd (A:=X) (B:=X) ⟨0,xz⟩ ⟨0,xz⟩
  have cy := cd (A:=Y) (B:=Y) ⟨0,yz⟩ ⟨0,yz⟩
  have dx : (X+X).card≤D.card := card_le_card subset_union_left
  have dy : (Y+Y).card≤D.card := card_le_card subset_union_right
  have hx := eq_of_subset_of_card_le (inter_subset_left (s₂:=Y) (s₁:=X)) (by omega)
  have hy := eq_of_subset_of_card_le (inter_subset_right (s₂:=Y) (s₁:=X)) (by omega)
  exact hx.symm.trans hy

private theorem pickGap {A : F} (h : 1<A.card) : ∃ a b, Gap A a b := by
  obtain ⟨a,ha,b,hb,ne⟩ := one_lt_card.mp h
  rcases lt_or_gt_of_ne ne with hab | hab
  · obtain ⟨c,hc⟩ := nextGap ha ⟨b,hb,hab⟩; exact ⟨a,c,hc⟩
  · obtain ⟨c,hc⟩ := nextGap hb ⟨a,ha,hab⟩; exact ⟨b,c,hc⟩

private theorem unequalGaps {X K : F} (xz : 0∈X) (skew : ∀ d∈X, -d∈X → d=0)
    (hp : ∃ p∈X, 0<p) (hn : ∃ n∈X, n<0) (large : 1<K.card)
    (minim : (K+X).card+1 = K.card+X.card) : False := by
  obtain ⟨n,gn⟩ := prev xz hn
  obtain ⟨p,gp⟩ := nextGap xz hp
  obtain ⟨a,b,g⟩ := pickGap large
  have e₁ := sameGap g gn minim
  have e₂ := sameGap g gp minim
  have np : -n=p := by omega
  have := skew n gn.1 (np.symm ▸ gp.2.1)
  have := gn.2.2.1
  omega

private theorem stepAcross {X T U : F} {a b s h : ℤ} (gx : Gap X a b)
    (mt : (T+X).card+1=T.card+X.card) (mu : (U+X).card+1=U.card+X.card)
    (hs : s∈T+U) (hh : h∈T+U) (lt : h<s) : s-(b-a)∈T+U := by
  obtain ⟨i,hi,j,hj,rfl⟩ := mem_add.mp hs
  obtain ⟨k,hk,l,hl,rfl⟩ := mem_add.mp hh
  by_cases cmp : k < i
  · obtain ⟨i',g⟩ := prev hi ⟨k,hk,cmp⟩
    have := sameGap g gx mt
    convert add_mem_add g.1 hj using 1; omega
  · obtain ⟨j',g⟩ := prev hj ⟨l,hl,by omega⟩
    have := sameGap g gx mu
    convert add_mem_add hi g.1 using 1; omega

private theorem stepUp {X T U : F} {a b s h : ℤ} (gx : Gap X a b)
    (mt : (T+X).card+1=T.card+X.card) (mu : (U+X).card+1=U.card+X.card)
    (hs : s∈T+U) (hh : h∈T+U) (lt : s<h) : s+(b-a)∈T+U := by
  obtain ⟨i,hi,j,hj,rfl⟩ := mem_add.mp hs
  obtain ⟨k,hk,l,hl,rfl⟩ := mem_add.mp hh
  by_cases cmp : i<k
  · obtain ⟨i',g⟩ := nextGap hi ⟨k,hk,cmp⟩
    have := sameGap g gx mt
    convert add_mem_add g.2.1 hj using 1; omega
  · obtain ⟨j',g⟩ := nextGap hj ⟨l,hl,by omega⟩
    have := sameGap g gx mu
    convert add_mem_add hi g.2.1 using 1; omega

/-- All weights of closed walks in the two-state quotient have one sign. -/
theorem rigidity {X Y T U : F} (xz : 0∈X) (yz : 0∈Y)
    (t : T.Nonempty) (u : U.Nonempty) (anti : 0∉T+U)
    (skew : ∀ d∈X, -d∈X → d=0)
    (a : ((X+X)∪(T+U)).card+(T+(X∪Y)).card+1≤2*(X.card+T.card))
    (b : ((Y+Y)∪(T+U)).card+(U+(X∪Y)).card+1≤2*(Y.card+U.card)) :
    X=Y ∧ ((∀ z∈X∪(T+U), 0≤z) ∨ ∀ z∈X∪(T+U), z≤0) := by
  have eq := sameDiagonal xz yz t u anti a b
  subst Y
  refine ⟨rfl,?_⟩
  simp only [union_idempotent] at a b
  let D:=X+X
  let S:=T+U
  let V:=D∪S
  change V.card+_+1≤_ at a b
  have lo := cd (A:=X) (B:=X) ⟨0,xz⟩ ⟨0,xz⟩
  have ts := cd t u
  have tx := cd t (B:=X) ⟨0,xz⟩
  have ux := cd u (B:=X) ⟨0,xz⟩
  change _ ≤ D.card+1 at lo
  change _ ≤ S.card+1 at ts
  have subD : D ⊆ V := subset_union_left
  have subS : insert 0 S ⊆ V := by
    apply insert_subset
    · exact mem_union_left _ (by simpa [D] using add_mem_add xz xz)
    · exact subset_union_right
  have vd := card_le_card subD
  have vs := card_le_card subS
  change 0 ∉ S at anti
  rw [card_insert_of_notMem anti] at vs
  have embed (x : ℤ) (hx : x∈X) : x∈D := by simpa [D] using add_mem_add xz hx
  have lower := card_pos.mpr (show X.Nonempty from ⟨0,xz⟩)
  have ltT := card_pos.mpr t
  have ltU := card_pos.mpr u
  have duo : (∃ p ∈ X, 0<p) → (∃ n ∈ X, n<0) → False := by
    intro p n
    obtain ⟨v,hv,vp⟩ := p
    have xs : 1<X.card := one_lt_card.mpr ⟨0,xz,v,hv,by omega⟩
    have nex := unequalGaps xz skew ⟨v,hv,vp⟩ n xs
    change ¬(D.card+1=X.card+X.card) at nex
    have et : (T+X).card+1 = T.card+X.card := by omega
    have eu : (U+X).card+1 = U.card+X.card := by omega
    by_cases tl : 1<T.card
    · exact unequalGaps xz skew ⟨v,hv,vp⟩ n tl et
    by_cases ul : 1<U.card
    · exact unequalGaps xz skew ⟨v,hv,vp⟩ n ul eu
    omega
  by_contra! mixed
  obtain ⟨⟨n,hn,neg⟩,⟨p,hp,pos⟩⟩ := mixed
  have exceptional (z : ℤ) (hz : z∈S) (hd : z∉D) :
      ((T+X).card+1=T.card+X.card) ∧ ((U+X).card+1=U.card+X.card) ∧ V=insert 0 S := by
    have strict := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subD,fun eq => hd (eq.symm ▸ mem_union_right D hz)⟩)
    have eqs : V.card ≤ (insert 0 S).card := by rw [card_insert_of_notMem anti]; omega
    exact ⟨by omega,by omega,(eq_of_subset_of_card_le subS eqs).symm⟩
  by_cases px : ∃ v∈X, 0<v
  · have nonneg (z : ℤ) (hz : z∈X) : 0≤z := by by_contra! h; exact duo px ⟨z,hz,h⟩
    have ns : n∈S := (mem_union.mp hn).resolve_left (fun h => (nonneg n h).not_gt neg)
    have nd : n∉D := by
      intro h; obtain ⟨i,hi,j,hj,rfl⟩ := mem_add.mp h
      have := nonneg i hi; have := nonneg j hj; omega
    obtain ⟨mt,mu,fill⟩ := exceptional n ns nd
    obtain ⟨v,g⟩ := nextGap xz px
    have vp := g.2.2.1
    have ins : v∈V := subD (embed v g.2.1)
    rw [fill] at ins
    have vs' : v∈S := (mem_insert.mp ins).resolve_left (by omega)
    have zz := stepAcross g mt mu vs' ns (by omega)
    exact anti (by simpa using zz)
  · by_cases nx : ∃ v∈X, v<0
    · have nonpos (z : ℤ) (hz : z∈X) : z≤0 := by by_contra! h; exact px ⟨z,hz,h⟩
      have ps : p∈S := (mem_union.mp hp).resolve_left (fun h => (nonpos p h).not_gt pos)
      have pd : p∉D := by
        intro h; obtain ⟨i,hi,j,hj,rfl⟩ := mem_add.mp h
        have := nonpos i hi; have := nonpos j hj; omega
      obtain ⟨mt,mu,fill⟩ := exceptional p ps pd
      obtain ⟨v,g⟩ := prev xz nx
      have vn := g.2.2.1
      have ins : v∈V := subD (embed v g.1)
      rw [fill] at ins
      have vs' : v∈S := (mem_insert.mp ins).resolve_left (by omega)
      have zz := stepUp g mt mu vs' ps (by omega)
      exact anti (by simpa using zz)
    · have single : X={0} := eq_singleton_iff_unique_mem.mpr ⟨xz,fun z hz => by
        by_contra h
        rcases lt_or_gt_of_ne h with lt|gt
        · exact nx ⟨z,hz,lt⟩
        · exact px ⟨z,hz,gt⟩⟩
      have xs : X.card=1 := by simp [single]
      have ns : n∈S := (mem_union.mp hn).resolve_left (by simp [single,show n≠0 by omega])
      have ps : p∈S := (mem_union.mp hp).resolve_left (by simp [single,show p≠0 by omega])
      have lots : 1<S.card := one_lt_card.mpr ⟨n,ns,p,ps,by omega⟩
      omega
end TwoOrbit

namespace TwoOrbit
open Finset OMA.S_mse_4941096
open scoped Pointwise

private abbrev closed (out : ℤ → F) (v : ℤ) := insert v (out v)

lemma closedCard {out : ℤ → F} (irr : ∀ v, v∉out v)
    (asym : ∀ v w, w∈out v → v∉out w) (equal : ∀ v, (second out v).card≤(out v).card)
    (v : ℤ) : ((closed out v).biUnion (closed out)).card+1≤2*(closed out v).card := by
  classical
  have ne : v∉second out v := by
    intro h
    obtain ⟨w,hw,back⟩ := mem_biUnion.mp (mem_sdiff.mp h).1
    exact asym v w hw back
  have eq : (closed out v).biUnion (closed out)=insert v ((out v)∪(second out v)) := by
    ext z
    simp only [closed,mem_biUnion,mem_insert,mem_union,second,mem_sdiff]
    grind
  have dis : Disjoint (out v) (second out v) := disjoint_left.mpr (fun _ h hs => (mem_sdiff.mp hs).2 h)
  rw [eq,card_insert_of_notMem (by simpa only [mem_union,not_or] using And.intro (irr v) ne),
    card_union_of_disjoint dis,card_insert_of_notMem (irr v)]
  have := equal v
  omega

private lemma countRows (f : (Bool × ℤ) ≃ ℤ) (C L R : F)
    (cl : ∀ d, f (false,d)∈C ↔ d∈L) (cr : ∀ d, f (true,d)∈C ↔ d∈R) :
    C.card=L.card+R.card := by
  let l (d : ℤ) := f (false,d)
  let r (d : ℤ) := f (true,d)
  have eq : C=L.image l ∪ R.image r := by
    ext z
    obtain ⟨⟨i,d⟩,rfl⟩ := f.surjective z
    cases i <;> simp [l,r,cl,cr]
  have dis : Disjoint (L.image l) (R.image r) := by
    apply disjoint_left.mpr
    rintro z hl hr
    obtain ⟨d,_,rfl⟩ := mem_image.mp hl
    obtain ⟨e,_,he⟩ := mem_image.mp hr
    have := f.injective he
    exact Bool.noConfusion (congrArg Prod.fst this)
  rw [eq,card_union_of_disjoint dis,card_image_of_injective _ (show Function.Injective l from
    fun x y h => congrArg Prod.snd (f.injective h)),card_image_of_injective _ (show Function.Injective r from
    fun x y h => congrArg Prod.snd (f.injective h))]

private lemma reachClosed {out : ℤ → F} {P : ℤ → Prop} (step : ∀ v, P v → ∀ w∈out v, P w)
    {v w : ℤ} (s : P v) (walk : Relation.ReflTransGen (fun i j => j∈out i) v w) : P w := by
  induction walk with
  | refl => exact s
  | tail _ h ih => exact step _ ih _ h

private lemma otherRow {out : ℤ → F} (f : (Bool × ℤ) ≃ ℤ) (B : Bool → Bool → F)
    (row : ∀ (i j : Bool) (n d : ℤ), f (j,n+d)∈closed out (f (i,n)) ↔ d∈B i j)
    (strong : ∀ v w, Relation.ReflTransGen (fun i j => j∈out i) v w) (i : Bool) :
    (B i (!i)).Nonempty := by
  by_contra missing
  let P (v : ℤ) := (f.symm v).1=i
  have preserved : ∀ v, P v → ∀ w∈out v, P w := by
    intro v hv w hw
    obtain ⟨⟨j,n⟩,rfl⟩ := f.surjective v
    obtain ⟨⟨k,l⟩,rfl⟩ := f.surjective w
    have ji : j=i := by simpa [P] using hv
    subst j
    change (f.symm (f (k,l))).1=i
    rw [Equiv.symm_apply_apply]
    by_contra ne
    have ki : k=(!i) := by cases k <;> cases i <;> simp_all
    have e := (row i k n (l-n)).mp (by simpa using (show f (_,l) ∈ insert (f (i,n)) (out (f (i,n))) from mem_insert_of_mem hw))
    exact missing ⟨l-n,ki ▸ e⟩
  have impossible := reachClosed preserved (v:=f (i,0)) (by simp [P]) (strong _ (f (!i,0)))
  cases i <;> simp [P] at impossible

private lemma againstSign {out : ℤ → F} (f : (Bool × ℤ) ≃ ℤ) (B : Bool → Bool → F)
    (row : ∀ (i j : Bool) (n d : ℤ), f (j,n+d)∈closed out (f (i,n)) ↔ d∈B i j)
    (strong : ∀ v w, Relation.ReflTransGen (fun i j => j∈out i) v w)
    (diagonal : B false false=B true true) (s m : ℤ) (unit : s=1 ∨ s= -1)
    (hm : m∈B false true) (small : ∀ d∈B false true, 0 ≤ s *(d-m))
    (signs : ∀ d∈(B false false)∪(B false true+B true false), 0 ≤ s *d) : False := by
  let score (v : ℤ) : ℤ := s * ((f.symm v).2 - if (f.symm v).1 then m else 0)
  have sc (i : Bool) (n : ℤ) : score (f (i,n))=s*(n-if i then m else 0) := by simp [score]
  have advance (v w : ℤ) (hw : w∈out v) : score v ≤ score w := by
    obtain ⟨⟨i,n⟩,rfl⟩ := f.surjective v
    obtain ⟨⟨j,l⟩,rfl⟩ := f.surjective w
    have e := (row i j n (l-n)).mp (by simpa using (show f (_,l) ∈ insert (f (i,n)) (out (f (i,n))) from mem_insert_of_mem hw))
    rw [sc,sc]
    cases i <;> cases j <;> simp only [Bool.false_eq_true,↓reduceIte,sub_zero]
    · have := signs (l-n) (mem_union_left _ e); nlinarith
    · have := small (l-n) e; nlinarith
    · have := signs (m+(l-n)) (mem_union_right _ (add_mem_add hm e)); nlinarith
    · have := signs (l-n) (mem_union_left _ (diagonal.symm ▸ e)); nlinarith
  have zero : score (f (false,0))=0 := by simp [sc]
  have : 0 ≤ score (f (false,-s)) := reachClosed (P:=fun v => 0 ≤ score v)
    (fun v hv w hw => le_trans hv (advance v w hw)) (by rw [zero]) (strong _ _)
  rw [sc] at this
  rcases unit with rfl|rfl <;> norm_num at this

/-- A strongly connected oriented graph admitting a translation with two
infinite orbits has a vertex with strictly more second than first neighbors.
Only finite out-neighborhoods enter the proof. -/
theorem strictExpansion (out : ℤ → F) (f : (Bool × ℤ) ≃ ℤ) (B : Bool → Bool → F)
    (row : ∀ (i j : Bool) (n d : ℤ), f (j,n+d)∈insert (f (i,n)) (out (f (i,n))) ↔ d∈B i j)
    (irr : ∀ v, v∉out v) (asym : ∀ v w, w∈out v → v∉out w)
    (strong : ∀ v w, Relation.ReflTransGen (fun i j => j∈out i) v w) :
    ∃ v, (out v).card<(second out v).card := by
  classical
  by_contra! equal
  have diag (i : Bool) : 0∈B i i := (row i i 0 0).mp (by simp)
  have single (i j : Bool) (d : ℤ) : f (j,d)∈closed out (f (i,0)) ↔ d∈B i j := by
    simpa only [zero_add] using row i j 0 d
  have double (i j : Bool) (d : ℤ) : f (j,d)∈(closed out (f (i,0))).biUnion (closed out) ↔
      d∈(B i false+B false j)∪(B i true+B true j) := by
    constructor
    · intro h
      obtain ⟨w,hw,hz⟩ := mem_biUnion.mp h
      obtain ⟨⟨k,a⟩,rfl⟩ := f.surjective w
      have c := (single i k a).mp hw
      have e := (row k j a (d-a)).mp (by simpa using hz)
      have mem : d∈B i k+B k j := by simpa using add_mem_add c e
      cases k
      · exact mem_union_left _ mem
      · exact mem_union_right _ mem
    · intro h
      have lift (k : Bool) (hk : d∈B i k+B k j) : f (j,d)∈(closed out (f (i,0))).biUnion (closed out) := by
        obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hk
        exact mem_biUnion.mpr ⟨f (k,a),(single i k a).mpr ha,(row k j a b).mpr hb⟩
      exact (mem_union.mp h).elim (lift false) (lift true)
  have counts (i : Bool) :
      ((B i false+B false false)∪(B i true+B true false)).card+
      ((B i false+B false true)∪(B i true+B true true)).card+1≤2*((B i false).card+(B i true).card) := by
    rw [← countRows f _ _ _ (double i false) (double i true),
      ← countRows f _ _ _ (single i false) (single i true)]
    exact closedCard irr asym equal _
  have strict {v w : ℤ} (h : w ∈ closed out v) (neq : w≠v) : w∈out v :=
    (mem_insert.mp h).resolve_left neq
  have opposed : 0∉B false true+B true false := by
    intro h
    obtain ⟨a,ha,b,hb,eq⟩ := mem_add.mp h
    have h₁ := strict ((single false true a).mpr ha) (by simp)
    have h₂ := (row true false a b).mpr hb
    rw [eq] at h₂
    exact asym _ _ h₁ (strict h₂ (by simp))
  have skew (d : ℤ) (hd : d∈B false false) (hn : -d∈B false false) : d=0 := by
    by_contra h
    have h₁ := strict ((single false false d).mpr hd) (by simpa using h)
    have h₂ := (row false false d (-d)).mpr hn
    rw [add_neg_cancel] at h₂
    exact asym _ _ h₁ (strict h₂ (by simpa using Ne.symm h))
  have t := otherRow f B row strong false
  have u := otherRow f B row strong true
  change (B false true).Nonempty at t
  change (B true false).Nonempty at u
  have A := counts false
  rw [add_comm (B false false) (B false true),← add_union] at A
  have C := counts true
  rw [add_comm (B true true) (B true false),← add_union,
    add_comm (B true false) (B false true),union_comm (B false true+B true false),
    add_comm (B true false+(B false false∪B true true)).card,add_comm (B true false).card] at C
  obtain ⟨e,plus|minus⟩ := rigidity (diag false) (diag true) t u opposed skew A C
  · exact againstSign f B row strong e 1 ((B false true).min' t) (Or.inl rfl)
      ((B false true).min'_mem t) (fun d hd => by have := (B false true).min'_le d hd; omega)
      (by simpa using plus)
  · exact againstSign f B row strong e (-1) ((B false true).max' t) (Or.inr rfl)
      ((B false true).max'_mem t) (fun d hd => by have := (B false true).le_max' d hd; omega)
      (by simpa using minus)
theorem noTwoOrbits : OMA.R_mse_4941096_R2.H1 := by
  intro out ⟨f,B,row⟩ ⟨irr,asym,strong,_,eq⟩
  obtain ⟨v,hv⟩ := strictExpansion out f B row irr asym strong
  exact hv.ne (eq v)
end TwoOrbit

open Finset
open scoped Pointwise
namespace TwoOrbit

/-- Small doubling and a unique zero sum orient a critical integer
progression away from zero. -/
theorem orientedProgression {A : F} {k : ℕ} (pos : 0<k) (n : A.card=k+1) (zero : 0∈A)
    (skew : ∀ x∈A, -x∈A → x=0) (minimal : (A+A).card+1=A.card+A.card) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x, x∈A ↔ ∃ i : ℕ, i≤k ∧ (i : ℤ)*d=x := by
  classical
  let f := A.orderEmbOfFin n
  have mem (i : Fin (k+1)) : f i∈A := A.orderEmbOfFin_mem n i
  have all (x : ℤ) : x∈A ↔ ∃ i, f i=x := by
    change x ∈ (A : Set ℤ) ↔ _; rw [← A.range_orderEmbOfFin n]; rfl
  let val (i : ℕ) (h : i≤k) := f ⟨i,by omega⟩
  have gap (i : ℕ) (hi : i<k) : Gap A (val i hi.le) (val (i+1) hi) := by
    refine ⟨mem _,mem _,f.strictMono (by exact_mod_cast (show i < i+1 by omega)),?_⟩
    intro x hx
    obtain ⟨j,rfl⟩ := (all _).mp hx
    rcases le_or_gt j.val i with h|h
    · exact Or.inl (f.monotone (by exact_mod_cast h))
    · exact Or.inr (f.monotone (by exact_mod_cast h))
  let g := val 1 pos - val 0 (by omega)
  have gp : 0<g := sub_pos.mpr (gap 0 pos).2.2.1
  have formula (i : ℕ) (hi : i≤k) : val i hi=val 0 (by omega)+(i:ℤ)*g := by
    induction i with
    | zero => simp
    | succ i ih =>
      have eq := sameGap (gap i (by omega)) (gap 0 pos) minimal
      change val (i+1) hi-val i (by omega)=g at eq
      rw [Nat.cast_succ,add_mul,one_mul,← add_assoc,← ih (by omega)]
      omega
  obtain ⟨j,hj⟩ := (all _).mp zero
  have rep : val j.val (by omega)=0 := hj
  have endpoint : j.val=0 ∨ j.val=k := by
    by_contra! interior
    have lo := formula (j.val-1) (by omega)
    have hi := formula (j.val+1) (by omega)
    have atj := formula j.val (by omega)
    rw [Int.ofNat_sub (by omega : 1≤j.val),Nat.cast_one] at lo
    rw [Nat.cast_succ] at hi
    have ml := mem (⟨j.val-1,by omega⟩ : Fin (k+1))
    have mh := mem (⟨j.val+1,by omega⟩ : Fin (k+1))
    change val (j.val-1) (by omega) ∈ A at ml
    change val (j.val+1) (by omega) ∈ A at mh
    have hneg : -(val (j.val-1) (by omega))=val (j.val+1) (by omega) := by nlinarith
    have hs := skew _ ml (hneg.symm ▸ mh)
    nlinarith
  rcases endpoint with e|e
  · have base : val 0 (by omega)=0 := by simpa only [e] using rep
    refine ⟨g,by omega,?_⟩
    intro x
    constructor
    · intro hx
      obtain ⟨i,rfl⟩ := (all _).mp hx
      exact ⟨i,by omega,by simpa only [base,zero_add] using (formula i (by omega)).symm⟩
    · rintro ⟨i,hi,rfl⟩
      exact (all _).mpr ⟨⟨i,by omega⟩,by simpa only [base,zero_add] using formula i hi⟩
  · have top : val k (by omega)=0 := by simpa only [e] using rep
    have atTop := formula k le_rfl
    refine ⟨-g,by omega,?_⟩
    intro x
    constructor
    · intro hx
      obtain ⟨i,rfl⟩ := (all _).mp hx
      refine ⟨k-i,by omega,?_⟩
      have eq := formula i.val (by omega)
      change _ = val i.val (by omega) 
      rw [Int.ofNat_sub (by omega : i.val≤k)]
      nlinarith
    · rintro ⟨i,hi,rfl⟩
      refine (all _).mpr ⟨⟨k-i,by omega⟩,?_⟩
      have eq := formula (k-i) (by omega)
      change val (k-i) (by omega)=_
      rw [Int.ofNat_sub hi] at eq
      nlinarith
end TwoOrbit

namespace TwoOrbit
open Finset OMA.S_mse_4941096
open scoped Pointwise

/-- At a minimum-degree vertex some successor changes the displacement set.
Uniformity is only assumed at the center and its immediate successors. -/
theorem displacementChange (forbidden : OMA.R_mse_4941096_R2.H2)
    {out : ℤ → F} (graph : exampleGraph out) (c : ℤ)
    (minimum : ∀ v, (out c).card≤(out v).card) :
    ∃ v∈out c, ∃ d : ℤ, ¬(v+d∈out v ↔ c+d∈out c) := by
  classical
  by_contra! uniform
  obtain ⟨irr,asym,strong,bound,eq⟩ := graph
  have nonempty : (out c).Nonempty := by
    by_contra ne
    have no (a : ℤ) (path : Relation.ReflTransGen (fun i j => j∈out i) c a) : c=a := by
      induction path with
      | refl => rfl
      | tail _ e ih => subst_vars; exact (ne ⟨_,e⟩).elim
    have := no _ (strong c (c+1)); omega
  let k := (out c).card
  have kp : 0<k := card_pos.mpr nonempty
  let A := (insert c (out c)).image (fun z => z-c)
  have ma (d : ℤ) : d∈A ↔ c+d∈insert c (out c) := by
    constructor
    · intro hd; obtain ⟨z,hz,e⟩ := mem_image.mp hd
      rwa [show c+d=z by omega]
    · intro hd; exact mem_image.mpr ⟨c+d,hd,by omega⟩
  have az : 0∈A := (ma _).mpr (by simp)
  have mk : A.card=k+1 := by
    dsimp [A,k]; rw [card_image_of_injective _ (by intro x y h; dsimp at h; omega),card_insert_of_notMem (irr c)]
  have localRow (v : ℤ) (hv : v∈insert c (out c)) (d : ℤ) :
      v+d∈insert v (out v) ↔ d∈A := by
    rw [ma,mem_insert,mem_insert]
    rcases mem_insert.mp hv with rfl|h
    · rfl
    · have e := uniform v h d
      constructor <;> rintro (he|he)
      · exact Or.inl (by omega)
      · exact Or.inr (e.mp he)
      · exact Or.inl (by omega)
      · exact Or.inr (e.mpr he)
  have sk (x : ℤ) (hx : x∈A) (hn : -x∈A) : x=0 := by
    by_contra ne
    have e := (ma x).mp hx
    have edge := (mem_insert.mp e).resolve_left (by omega)
    have back := (localRow (c+x) e (-x)).mpr hn
    rw [show c+x+ -x=c by omega] at back
    exact asym _ _ edge ((mem_insert.mp back).resolve_left (by omega))
  let C2 := (insert c (out c)).biUnion (fun z => insert z (out z))
  have images : C2=(A+A).image (fun d => c+d) := by
    ext z
    constructor
    · intro hz
      obtain ⟨w,hw,hz⟩ := mem_biUnion.mp hz
      have x := (ma (w-c)).mpr (by simpa using hw)
      have y := (localRow w hw (z-w)).mp (by simpa using hz)
      exact mem_image.mpr ⟨(w-c)+(z-w),add_mem_add x y,by omega⟩
    · intro hz
      obtain ⟨d,hd,rfl⟩ := mem_image.mp hz
      obtain ⟨i,hi,j,hj,rfl⟩ := mem_add.mp hd
      have cc := (ma i).mp hi
      exact mem_biUnion.mpr ⟨c+i,cc,by simpa [add_assoc] using (localRow _ cc j).mpr hj⟩
  have count := closedCard irr asym (fun z => (eq z).ge) c
  change C2.card+1≤2*(insert c (out c)).card at count
  rw [images,card_image_of_injective _ (by intro i j h; dsimp at h; omega),card_insert_of_notMem (irr c)] at count
  have low := cd (A:=A) (B:=A) ⟨0,az⟩ ⟨0,az⟩
  change _≤2*(k+1) at count
  obtain ⟨d,nd,deltas⟩ := orientedProgression kp mk az sk (by omega)
  let v (i : ℕ) := c+(i:ℤ)*d
  apply forbidden out ⟨irr,asym,strong,bound,eq⟩ k kp minimum
  refine ⟨v,?_,?_⟩
  · intro i _ j _ e
    change c+(i:ℤ)*d=c+(j:ℤ)*d at e
    have eqn := mul_right_cancel₀ nd (add_left_cancel e)
    exact_mod_cast eqn
  · intro i hi z
    have vi : v i∈insert c (out c) := (ma ((i:ℤ)*d)).mp ((deltas _).mpr ⟨i,hi.le,rfl⟩)
    constructor
    · intro hz
      have cl : v i+(z-v i)∈insert (v i) (out (v i)) := by simpa using mem_insert_of_mem (b:=v i) hz
      obtain ⟨j,le,e⟩ := (deltas _).mp ((localRow _ vi _).mp cl)
      have neq : z≠v i := fun h => irr _ (h ▸ hz)
      have jp : 0<j := by
        by_contra! bad
        have ej : j=0 := by omega
        rw [ej,Nat.cast_zero,zero_mul] at e
        omega
      refine ⟨i+j,by omega,by omega,?_⟩
      dsimp [v] at e ⊢; rw [add_mul]; omega
    · rintro ⟨j,hj,le,rfl⟩
      have jd : (j-i:ℕ)≤k := by omega
      have diff : v i+((j-i:ℕ):ℤ)*d=v j := by
        dsimp [v]; rw [Int.ofNat_sub hj.le]; ring
      have there := (localRow _ vi _).mpr ((deltas _).mpr ⟨j-i,jd,rfl⟩)
      rw [diff] at there
      apply (mem_insert.mp there).resolve_left
      intro e
      have eqn := mul_right_cancel₀ nd (add_left_cancel e)
      have : j=i := by exact_mod_cast eqn
      omega
end TwoOrbit

theorem OMA.solution : OMA.R_mse_4941096_R2.H1 := TwoOrbit.noTwoOrbits
