import OMAStatements.S_oeis_a189391
/-!
# Cuts-resistance and the least apex of an addition triangle

Interpret a binary word as a walk with steps of size one. Removing one
bit from each run reduces the range of every nonempty walk by one.
The distribution of its upper extreme equals the distribution obtained
by folding the endpoint about −1/2. The folded endpoints order the
triangle's binomial weights in the opposite direction.
-/
namespace A189391Proof
open OMA.S_oeis_a189391 Finset

private def peak : List Bool→ℕ
  | []=>0
  | true::w=>peak w+1
  | false::w=>peak w-1

private def inv (w : List Bool) := w.map Bool.not

private theorem keep_len (w : List Bool) (b : Bool) : (keepRepeats b w).length≤w.length := by
  induction w generalizing b with
  | nil => simp [keepRepeats]
  | cons a w ih =>
    have H := ih a
    unfold keepRepeats; split <;> simp_all
    omega

private theorem keep_inv (w : List Bool) (b : Bool) :
    inv (keepRepeats b w)=keepRepeats (!b) (inv w) := by
  induction w generalizing b with
  | nil => simp [keepRepeats,inv]
  | cons a w ih =>
    cases a <;> cases b <;> simp [inv,keepRepeats] at ih ⊢ <;> tauto

private theorem rab_inv (w : List Bool) : inv (raboter w)=raboter (inv w) := by
  cases w with
  | nil => rfl
  | cons b w => exact keep_inv w b

/-- Deleting each run's initial bit lowers the upper extremum exactly when
the initial step goes upwards; the other extremum follows by complementing. -/
private theorem peaked (w : List Bool) :
    peak (keepRepeats true w)=peak w ∧
    peak (keepRepeats false w)=peak w-1 := by
  induction w with
  | nil => simp [peak,keepRepeats]
  | cons b w ih =>
    cases b <;> simp [peak,keepRepeats,ih.1,ih.2]

private def span (w : List Bool) := peak w+peak (inv w)

private theorem span_step (b : Bool) (w : List Bool) :
    span (b::w)=1+span (raboter (b::w)) := by
  unfold span
  rw [rab_inv]
  cases b <;> simp only [inv,List.map_cons,Bool.not_true,Bool.not_false] <;>
    simp only [peak,raboter,(peaked _).1,(peaked _).2] <;> omega

private theorem exact_steps (n : ℕ) (w : List Bool) (hn : w.length≤n) : steps n w=span w := by
  induction n generalizing w with
  | zero =>
    have hw : w=[] := List.length_eq_zero_iff.mp (by omega)
    subst w; rfl
  | succ n ih =>
    cases w with
    | nil => rfl
    | cons b w =>
      rw [steps,span_step,ih]
      have h := keep_len w b
      change (keepRepeats b w).length≤n
      simp only [List.length_cons] at hn; omega

private theorem total_add (n : ℕ) (f g : List Bool→ℕ) :
    wordSum n (fun w=>f w+g w)=wordSum n f+wordSum n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [wordSum]
    rw [←ih]
    congr 1; funext w; omega

private theorem total_inv (n : ℕ) (f : List Bool→ℕ) :
    wordSum n (fun w=>f (inv w))=wordSum n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [wordSum]
    rw [←ih (fun w=>f (true::w)+f (false::w))]
    congr 1; funext w; simp [inv,add_comm]

private theorem total_resistance (n : ℕ) : wordSum n resistance=2*wordSum n peak := by
  have eq : resistance=span := funext (fun w=>exact_steps w.length w le_rfl)
  rw [eq]
  unfold span
  rw [total_add,total_inv,two_mul]


private def folded (x : ℤ) : ℕ := if 0 ≤ x then x.toNat else (-x-1).toNat

private def endpoint : List Bool → ℤ
  | [] => 0
  | true::w => endpoint w + 1
  | false::w => endpoint w - 1

private def ones : List Bool → ℕ
  | [] => 0
  | true::w => ones w + 1
  | false::w => ones w

private theorem folded_step (g : ℕ → ℕ) (x : ℤ) :
    g (folded x + 1) + g (folded x - 1) =
      g (folded (x + 1)) + g (folded (x - 1)) := by
  by_cases h : 0 ≤ x
  · have u : folded (x+1) = folded x + 1 := by unfold folded; split_ifs <;> omega
    have d : folded (x-1) = folded x - 1 := by unfold folded; split_ifs <;> omega
    rw [u,d]
  · have u : folded (x+1) = folded x - 1 := by unfold folded; split_ifs <;> omega
    have d : folded (x-1) = folded x + 1 := by unfold folded; split_ifs <;> omega
    rw [u,d,add_comm]

private theorem folded_distribution (n : ℕ) (g : ℕ → ℕ) :
    wordSum n (fun w => g (peak w)) =
      wordSum n (fun w => g (folded (endpoint w))) := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    simp only [wordSum,peak,endpoint]
    exact (ih (fun k => g (k+1)+g (k-1))).trans
      (congrArg (wordSum n) (funext (fun w => folded_step g (endpoint w))))

private theorem word_congr (n : ℕ) (f g : List Bool → ℕ) (h : ∀ w, w.length=n → f w=g w) :
    wordSum n f=wordSum n g := by
  induction n generalizing f g with
  | zero => exact h [] rfl
  | succ n ih =>
    apply ih
    intro w hw
    rw [h (true::w) (by simp [hw]), h (false::w) (by simp [hw])]

private theorem endpoint_ones (w : List Bool) : endpoint w=2*(ones w:ℤ)-w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;> simp [endpoint,ones,ih] <;> omega

private def rank (n i : ℕ) := if n≤2*i then 2*i-n else n-2*i-1

private theorem folded_rank (n i : ℕ) : folded (2*(i:ℤ)-n)=rank n i := by
  unfold folded rank; split_ifs <;> omega

private theorem apex_words (n : ℕ) (f : ℕ → ℕ) : wordSum n (fun w=>f (ones w)) = apex n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [wordSum,ones,apex]
    rw [← ih]
    congr 1; funext w; exact add_comm _ _

private theorem total_rank (n : ℕ) : wordSum n resistance=2*apex n (rank n) := by
  rw [total_resistance]
  congr 1
  calc
    wordSum n peak = wordSum n (fun w=>folded (endpoint w)) := folded_distribution n id
    _ = wordSum n (fun w=>rank n (ones w)) := by
      apply word_congr; intro w hw; rw [endpoint_ones,hw,folded_rank]
    _ = apex n (rank n) := apex_words n _


private theorem rank_bound (n i : ℕ) (hi : i ≤ n) : rank n i ≤ n := by
  unfold rank; split_ifs <;> omega

private def rankMap (n : ℕ) (i : Fin (n+1)) : Fin (n+1) :=
  ⟨rank n i, Nat.lt_succ_of_le (rank_bound n i (Nat.le_of_lt_succ i.isLt))⟩

private theorem rank_injective (n : ℕ) : Function.Injective (rankMap n) := by
  intro i j h
  have hval := congrArg Fin.val h
  change rank n i.val=rank n j.val at hval
  apply Fin.ext
  unfold rank at hval
  split_ifs at hval <;> omega

private noncomputable def rankPerm (n : ℕ) : Equiv.Perm (Fin (n+1)) :=
  Equiv.ofBijective (rankMap n) (Finite.injective_iff_bijective.mp (rank_injective n))

private theorem half_choose (n : ℕ) {a b : ℕ} (hab : a≤b) (hb : b≤n/2) :
    n.choose a ≤ n.choose b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

private theorem choose_min (n i : ℕ) (h : i≤n) : n.choose (min i (n-i))=n.choose i := by
  by_cases hi : i≤n-i
  · rw [min_eq_left hi]
  · rw [min_eq_right (by omega), Nat.choose_symm h]

private theorem opposite (n : ℕ) : Antivary (fun i : Fin (n+1) => n.choose i.val)
    (fun i => (rankPerm n i).val) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  change rank n i.val < rank n j.val at hij
  change n.choose j.val ≤ n.choose i.val
  rw [←choose_min n j (by omega), ←choose_min n i (by omega)]
  apply half_choose
  · unfold rank at hij
    simp only [min_def]
    split_ifs at * <;> omega
  · omega

private theorem apex_binomial (n : ℕ) (f : ℕ → ℕ) :
    apex n f = ∑ i ∈ range (n+1), n.choose i * f i := by
  induction n generalizing f with
  | zero => simp [apex]
  | succ n ih =>
    rw [apex,ih]
    simp only [Nat.mul_add, sum_add_distrib]
    rw [sum_range_succ' (fun i=>n.choose i * f i),
      sum_range_succ' (fun i=>(n+1).choose i * f i)]
    simp only [Nat.choose_zero_right, one_mul,Nat.choose_succ_succ,add_mul,sum_add_distrib]
    rw [sum_range_succ (fun i=>n.choose (i+1)*f (i+1))]
    simp [add_comm,add_left_comm]

private theorem apex_fin (n : ℕ) (f : ℕ → ℕ) :
    apex n f = ∑ i : Fin (n+1), n.choose i.val * f i.val := by
  rw [apex_binomial,Fin.sum_univ_eq_sum_range (fun i=>n.choose i * f i)]

private theorem score_eq (n : ℕ) (σ : Equiv.Perm (Fin (n+1))) :
    score n σ = ∑ i : Fin (n+1), n.choose i.val * (σ i).val := by
  rw [score,apex_fin]
  exact sum_congr rfl (fun i _=>by simp only [dif_pos i.isLt])

private theorem min_score (n : ℕ) (σ : Equiv.Perm (Fin (n+1))) :
    apex n (rank n) ≤ score n σ := by
  rw [score_eq,apex_fin]
  have h := (opposite n).sum_smul_le_sum_smul_comp_perm (σ := σ.trans (rankPerm n).symm)
  change (∑ i : Fin (n+1), n.choose i.val * (rankPerm n i).val) ≤ _
  simpa [nsmul_eq_mul,Equiv.trans_apply] using h

private theorem attained_minimum (n : ℕ) : IsLeast (Set.range (fun σ : Equiv.Perm (Fin (n+1))=>2*score n σ))
    (wordSum n resistance) := by
  rw [total_rank]
  constructor
  · refine ⟨rankPerm n,?_⟩
    change 2 * score n (rankPerm n)=2*apex n (rank n)
    rw [score_eq,apex_fin]
    rfl
  · rintro _ ⟨σ,rfl⟩
    exact Nat.mul_le_mul_left 2 (min_score n σ)


end A189391Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a189391.main :=
  A189391Proof.attained_minimum
