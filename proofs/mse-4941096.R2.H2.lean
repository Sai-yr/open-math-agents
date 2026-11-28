import OMAReductions.R_mse_4941096_R2
import Mathlib
/-!
# A finite minimum-outdegree configuration that forces a closed infinite path

Once k consecutive rows form the kth power of a path, their last neighbor
must continue the ordered pattern. Iteration yields a sequence whose
successor is uniquely determined by its vertex. Strong connectivity would
then force a finite cycle to cover the entire graph.
-/
namespace MinimumWindows
open Finset OMA.S_mse_4941096

/-- The first k rows of a directed kth power of a path, with all outgoing
edges specified. Only the values of v at the first 2k positions matter. -/
structure Window (out : ℤ → Finset ℤ) (k : ℕ) where
  v : ℕ → ℤ
  inj : ∀ i < 2*k, ∀ j < 2*k, v i=v j → i=j
  row : ∀ i<k, ∀ z, z∈out (v i) ↔ ∃ j, i<j ∧ j≤ i+k ∧ v j=z

private theorem extend {out : ℤ → Finset ℤ} {k : ℕ} (pos : 0<k)
    (minimum : ∀ z, k≤(out z).card) (irr : ∀ v, v∉out v)
    (asym : ∀ v w, w∈out v → v∉out w) (equal : ∀ v, (second out v).card≤(out v).card)
    (c : Window out k) : ∃ d : Window out k, ∀ j, j+1<2*k → d.v j=c.v (j+1) := by
  classical
  have row0 (z : ℤ) : z∈out (c.v 0) ↔ ∃ j, 0<j ∧ j≤k ∧ c.v j=z := by simpa using c.row 0 pos z
  have zeroSet : out (c.v 0)=(Ioc 0 k).image c.v := by
    ext z; simp only [row0,mem_image,mem_Ioc]; grind
  have cz : (out (c.v 0)).card=k := by
    rw [zeroSet,card_image_of_injOn]
    · simp
    · intro i hi j hj h
      have := mem_Ioc.mp hi; have := mem_Ioc.mp hj
      exact c.inj i (by omega) j (by omega) h
  have edge (i : ℕ) (hi : i<k) : c.v k ∈ out (c.v i) :=
    (c.row i hi _).mpr ⟨k,hi,by omega,rfl⟩
  have last : out (c.v k) ⊆ second out (c.v 0) := by
    intro z hz
    refine mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨c.v k,edge 0 pos,hz⟩,?_⟩
    intro h
    obtain ⟨j,hj,le,rfl⟩ := (row0 z).mp h
    rcases eq_or_lt_of_le le with rfl|lt
    · exact irr _ hz
    · exact asym _ _ (edge j lt) hz
  have exactLast : out (c.v k)=second out (c.v 0) := eq_of_subset_of_card_le last (by
    have := equal (c.v 0); have := minimum (c.v k); omega)
  let tailSet := (Ioo k (2*k)).image c.v
  have isTail (z : ℤ) : z∈tailSet ↔ ∃ j, k<j ∧ j<2*k ∧ c.v j=z := by
    simp only [tailSet,mem_image,mem_Ioo]; grind
  have within : tailSet ⊆ out (c.v k) := by
    intro z hz
    obtain ⟨j,hj,hi,rfl⟩ := (isTail z).mp hz
    rw [exactLast]
    refine mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨c.v (k-1),
      (row0 _).mpr ⟨k-1,by omega,by omega,rfl⟩,
      (c.row (k-1) (by omega) _).mpr ⟨j,by omega,by omega,rfl⟩⟩,?_⟩
    intro hz
    obtain ⟨l,_,hl,e⟩ := (row0 _).mp hz
    have := c.inj l (by omega) j hi e
    omega
  have ct : tailSet.card=k-1 := by
    dsimp [tailSet]
    rw [card_image_of_injOn]
    · rw [Nat.card_Ioo]; omega
    · intro i hi j hj e
      exact c.inj i (mem_Ioo.mp hi).2 j (mem_Ioo.mp hj).2 e
  have ck : (out (c.v k)).card=k := by
    have le := equal (c.v 0); rw [← exactLast,cz] at le; exact le.antisymm (minimum _)
  obtain ⟨w,hw,hnew⟩ := exists_mem_notMem_of_card_lt_card (show tailSet.card<(out (c.v k)).card by omega)
  have all : insert w tailSet=out (c.v k) := eq_of_subset_of_card_le (insert_subset hw within) (by
    rw [card_insert_of_notMem hnew]; omega)
  have fresh (i : ℕ) (hi : i<2*k) : c.v i≠w := by
    rintro rfl
    rcases lt_trichotomy i k with lt|rfl|gt
    · exact asym _ _ (edge i lt) hw
    · exact irr _ hw
    · exact hnew ((isTail _).mpr ⟨i,gt,hi,rfl⟩)
  let f (i : ℕ) := if i+1=2*k then w else c.v (i+1)
  have old (i : ℕ) (h : i+1<2*k) : f i=c.v (i+1) := if_neg (by omega)
  have new : f (2*k-1)=w := if_pos (by omega)
  refine ⟨⟨f,?_,?_⟩,old⟩
  · intro i hi j hj e
    by_cases ix : i+1=2*k
    · rw [show f i=w from if_pos ix] at e
      by_cases jx : j+1=2*k
      · omega
      · rw [old j (by omega)] at e
        exact (fresh (j+1) (by omega) e.symm).elim
    · rw [old i (by omega)] at e
      by_cases jx : j+1=2*k
      · rw [show f j=w from if_pos jx] at e
        exact (fresh (i+1) (by omega) e).elim
      · rw [old j (by omega)] at e
        have := c.inj (i+1) (by omega) (j+1) (by omega) e
        omega
  · intro i hi z
    rw [old i (by omega)]
    by_cases lastRow : i+1=k
    · rw [lastRow,← all,mem_insert,isTail]
      constructor
      · rintro (rfl|⟨j,hj,hj',rfl⟩)
        · exact ⟨2*k-1,by omega,by omega,new⟩
        · exact ⟨j-1,by omega,by omega,by rw [old _ (by omega),show j-1+1=j by omega]⟩
      · rintro ⟨j,hj,le,rfl⟩
        by_cases fin : j+1=2*k
        · exact Or.inl (if_pos fin)
        · exact Or.inr ⟨j+1,by omega,by omega,(old _ (by omega)).symm⟩
    · rw [c.row (i+1) (by omega)]
      constructor
      · rintro ⟨j,hj,le,rfl⟩
        exact ⟨j-1,by omega,by omega,by rw [old _ (by omega),show j-1+1=j by omega]⟩
      · rintro ⟨j,hj,le,rfl⟩
        exact ⟨j+1,by omega,by omega,(old _ (by omega)).symm⟩

theorem obstruction {out : ℤ → Finset ℤ} {k : ℕ} (pos : 0<k) (minimum : ∀ z, k≤(out z).card)
    (start : Window out k) (irr : ∀ v, v∉out v) (asym : ∀ v w, w∈out v → v∉out w)
    (equal : ∀ v, (second out v).card≤(out v).card)
    (strong : ∀ v w, Relation.ReflTransGen (fun i j => j∈out i) v w) : False := by
  classical
  choose next agreement using extend pos minimum irr asym equal
  let C (n : ℕ) := next^[n] start
  have evolve (n : ℕ) : C (n+1)=next (C n) := Function.iterate_succ_apply' ..
  let s (n : ℕ) := (C n).v 0
  have link (i j : ℕ) (hj : j<2*k) : s (i+j)=(C i).v j := by
    induction j generalizing i with
    | zero => rfl
    | succ j ih =>
      rw [show i+(j+1)=(i+1)+j by omega,ih _ (by omega),evolve]
      exact agreement _ j hj
  have row (i : ℕ) (z : ℤ) : z∈out (s i) ↔ ∃ j, 0<j ∧ j≤k ∧ s (i+j)=z := by
    change z∈out ((C i).v 0) ↔ _
    rw [(C i).row 0 pos]
    simp only [zero_add]
    constructor <;> rintro ⟨j,hj,le,e⟩
    · exact ⟨j,hj,le,(link i j (by omega)).trans e⟩
    · exact ⟨j,hj,le,(link i j (by omega)).symm.trans e⟩
  have localStep (i j : ℕ) (e : s i=s j) (ne : s (i+1)≠s (j+1)) :
      s (j+1)∈out (s (i+1)) := by
    have h := (row j _).mpr ⟨1,by omega,by omega,rfl⟩
    rw [← e] at h
    obtain ⟨l,hl,le,he⟩ := (row i _).mp h
    have nl : l≠1 := fun eq => ne (eq ▸ he)
    exact (row (i+1) _).mpr ⟨l-1,by omega,by omega,by rw [show i+1+(l-1)=i+l by omega,he]⟩
  have unique (i j : ℕ) (e : s i=s j) : s (i+1)=s (j+1) := by
    by_contra ne
    exact asym _ _ (localStep i j e ne) (localStep j i e.symm (Ne.symm ne))
  have tailCover (t : ℕ) (z : ℤ) : ∃ j≥t, s j=z := by
    have reach := strong (s t) z
    induction reach with
    | refl => exact ⟨t,le_rfl,rfl⟩
    | tail _ edge ih =>
      obtain ⟨j,le,rfl⟩ := ih
      obtain ⟨d,_,_,hd⟩ := (row j _).mp edge
      exact ⟨j+d,by omega,hd⟩
  obtain ⟨p,hp,hrep⟩ := tailCover 1 (s 0)
  have periodic (n : ℕ) : s (p+n)=s n := by
    induction n with
    | zero => simpa using hrep
    | succ n ih => exact unique (p+n) n ih
  let finite := (range p).image s
  have contained (n : ℕ) : s n∈finite := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases small : n<p
      · exact mem_image.mpr ⟨n,mem_range.mpr small,rfl⟩
      · have he := periodic (n-p)
        rw [show p+(n-p)=n by omega] at he
        rw [he]
        exact ih (n-p) (by omega)
  obtain ⟨z,hz⟩ := finite.exists_notMem
  obtain ⟨j,_,rfl⟩ := tailCover 0 z
  exact hz (contained j)
end MinimumWindows

theorem OMA.solution : OMA.R_mse_4941096_R2.H2 := by
  intro out graph k pos minimum ⟨v,inj,row⟩
  obtain ⟨irr,asym,strong,_,equal⟩ := graph
  exact MinimumWindows.obstruction pos minimum ⟨v,inj,row⟩ irr asym
    (fun z => (equal z).ge) strong
