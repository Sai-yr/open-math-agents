import OMAStatements.S_oeis_a132297

namespace OMA.S_oeis_a132297

-- k counts switches. For odd k the direction of the first switch
-- distinguishes the two possibilities, represented by v=0 or v=1.
private def form (k z o v : ℕ) : Profile := ⟨z,(k+1)/2-v,k/2+v,o⟩
private def shape (s : Bool) (k z o : ℕ) : Profile :=
  form k z o (if s then k%2 else 0)

private theorem switches (k z o v : ℕ) (hv : v ≤ k%2) :
    (form k z o v).zo+(form k z o v).oz = k := by
  change (k+1)/2-v+(k/2+v)=k
  omega

private theorem classify (w : List Bool) (s : Bool) :
    ∃ k z o, k+z+o = w.length ∧ walk s w=shape s k z o ∧
      (k=0 → if s then z=0 else o=0) := by
  induction w generalizing s with
  | nil => exact ⟨0,0,0,rfl,by cases s <;> rfl,by cases s <;> simp⟩
  | cons b w ih =>
    cases s <;> cases b
    · obtain ⟨k,z,o,hL,hw,h₀⟩ := ih false
      exact ⟨k,z+1,o,by simp; omega,by simp [walk,hw,shape,form],h₀⟩
    · obtain ⟨k,z,o,hL,hw,_⟩ := ih true
      refine ⟨k+1,z,o,by simp; omega,?_,by simp⟩
      simp [walk,hw,shape,form]
      omega
    · obtain ⟨k,z,o,hL,hw,h₀⟩ := ih true
      exact ⟨k,z,o+1,by simp; omega,by simp [walk,hw,shape,form],h₀⟩
    · obtain ⟨k,z,o,hL,hw,_⟩ := ih false
      refine ⟨k+1,z,o,by simp; omega,?_,by simp⟩
      simp [walk,hw,shape,form]
      omega

private theorem stay_zero (w : List Bool) (z : ℕ) :
    walk false (List.replicate z false ++ w) =
    {(walk false w) with zz := (walk false w).zz+z} := by
  induction z with
  | zero => simp
  | succ z ih => simp [List.replicate_succ,walk,ih,Nat.add_assoc]

private theorem stay_one (w : List Bool) (o : ℕ) :
    walk true (List.replicate o false ++ w) =
    {(walk true w) with oo := (walk true w).oo+o} := by
  induction o with
  | zero => simp
  | succ o ih => simp [List.replicate_succ,walk,ih,Nat.add_assoc]

private theorem all_switch (s : Bool) (k : ℕ) :
    walk s (List.replicate k true) = shape s k 0 0 := by
  induction k generalizing s with
  | zero => cases s <;> rfl
  | succ k ih =>
    cases s <;> simp [List.replicate_succ,walk,ih,shape,form] <;> omega

private theorem mem_profiles {m : ℕ} {p : Profile} : p ∈ profiles m ↔
    ∃ s w, w.length=m ∧ walk s w=p := by
  constructor
  · intro hp
    obtain ⟨⟨s,f⟩,_,rfl⟩ := Finset.mem_image.mp hp
    exact ⟨s,List.ofFn f,by simp,rfl⟩
  · rintro ⟨s,w,rfl,rfl⟩
    exact Finset.mem_image.mpr ⟨(s,w.get),Finset.mem_univ _,by simp [List.ofFn_get]⟩

-- Put all stays at the first visit to their symbol, then finish by switching.
private theorem positive_switches (s : Bool) (k z o : ℕ) :
    shape s (k+1) z o ∈ profiles (k+1+z+o) := by
  apply mem_profiles.mpr
  cases s
  · refine ⟨false, List.replicate z false ++ true :: (List.replicate o false ++ List.replicate k true),
      by simp; omega, ?_⟩
    rw [stay_zero,walk,stay_one, all_switch]
    simp [shape,form]
    omega
  · refine ⟨true, List.replicate o false ++ true :: (List.replicate z false ++ List.replicate k true),
      by simp; omega, ?_⟩
    rw [stay_one,walk,stay_zero, all_switch]
    simp [shape,form]
    omega

private abbrev Param (m : ℕ) := Bool ⊕ (Σ t : Fin m, Fin (m-t.val) × Fin (1+(t.val+1)%2))
private def encode (m : ℕ) : Param m → Profile
  | .inl false => ⟨m,0,0,0⟩
  | .inl true => ⟨0,0,0,m⟩
  | .inr ⟨t,z,v⟩ => form (t.val+1) z.val (m-(t.val+1)-z.val) v.val

private theorem in_image {m : ℕ} (p : Profile) : p ∈ profiles m ↔ ∃ u, encode m u=p := by
  constructor
  · intro hp
    obtain ⟨s,w,hL,rfl⟩ := mem_profiles.mp hp
    obtain ⟨k,z,o,h,hw,h₀⟩ := classify w s
    rw [hw]
    cases k with
    | zero =>
      specialize h₀ rfl
      cases s
      · refine ⟨.inl false, ?_⟩
        simp at h₀
        subst o
        have : z=m := by omega
        subst z
        rfl
      · refine ⟨.inl true, ?_⟩
        simp at h₀
        subst z
        have : o=m := by omega
        subst o
        rfl
    | succ k =>
      let v : ℕ := if s then (k+1)%2 else 0
      have hv : v<1+(k+1)%2 := by cases s <;> simp [v]
      refine ⟨.inr ⟨⟨k,by omega⟩,⟨z,by change z < m-k; omega⟩,⟨v,hv⟩⟩, ?_⟩
      change form (k+1) z (m-(k+1)-z) v = _
      rw [show m-(k+1)-z=o by omega]
      rfl
  · rintro ⟨u,rfl⟩
    rcases u with s | ⟨t,z,v⟩
    · cases s
      · apply mem_profiles.mpr
        exact ⟨false,List.replicate m false,by simp,by simpa [walk,encode] using stay_zero [] m⟩
      · apply mem_profiles.mpr
        exact ⟨true,List.replicate m false,by simp,by simpa [walk,encode] using stay_one [] m⟩
    · let o := m-(t.val+1)-z.val
      have hm : t.val+1+z.val+o=m := by dsimp only [o]; omega
      have hv := v.isLt
      by_cases h₀ : v.val=0
      · have hh := positive_switches false t.val z.val o
        rw [hm] at hh
        simpa [encode,shape,h₀,o] using hh
      · have hh := positive_switches true t.val z.val o
        rw [hm] at hh
        have h₁ : v.val = (t.val+1)%2 := by omega
        simpa [encode,shape,h₁,o] using hh

private theorem encode_inj {m : ℕ} (hm : 0 < m) : Function.Injective (encode m) := by
  intro a b hab
  have hk := congrArg (fun p : Profile => p.zo+p.oz) hab
  have hz := congrArg Profile.zz hab
  have hv := congrArg Profile.oz hab
  rcases a with s | ⟨t,z,v⟩ <;> rcases b with s' | ⟨t',z',v'⟩
  · cases s <;> cases s'
    · rfl
    · have : m=0 := hz; omega
    · have : 0=m := hz; omega
    · rfl
  · have hc := switches (t'.val+1) z'.val (m-(t'.val+1)-z'.val) v'.val (by omega)
    cases s <;> simp [encode] at hk
    all_goals omega
  · have hc := switches (t.val+1) z.val (m-(t.val+1)-z.val) v.val (by omega)
    cases s' <;> simp [encode] at hk
    all_goals omega
  · have h₁ := switches (t.val+1) z.val (m-(t.val+1)-z.val) v.val (by omega)
    have h₂ := switches (t'.val+1) z'.val (m-(t'.val+1)-z'.val) v'.val (by omega)
    simp only [encode] at hk
    have ht : t=t' := Fin.ext (by omega)
    subst t'
    have hz' : z=z' := Fin.ext hz
    subst z'
    have hv' : v=v' := Fin.ext (by change t.val.succ/2+v.val=t.val.succ/2+v'.val at hv; omega)
    subst v'
    rfl

private def multiplicity (j : ℕ) := 1+(j+1)%2
private def F (m : ℕ) := 2+∑ j ∈ Finset.range m, (m-j)*multiplicity j
private def W (m : ℕ) := ∑ j ∈ Finset.range m, multiplicity j

private theorem counted (m : ℕ) (hm : 0 < m) : term (m+1) = F m := by
  have heq : profiles m = Finset.univ.image (encode m) := by
    ext p
    simpa [in_image] using (in_image p : p ∈ profiles m ↔ ∃ u, encode m u=p)
  rw [term,if_pos (by omega),Nat.add_sub_cancel,heq,Finset.card_image_of_injective _ (encode_inj hm),
    Finset.card_univ]
  simp only [Param, Fintype.card_sum,Fintype.card_bool,Fintype.card_sigma,Fintype.card_prod,
    Fintype.card_fin, F, multiplicity]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => (m-j)*(1+(j+1)%2)) m

private theorem W_step (m : ℕ) : W (m+1) = W m + multiplicity m :=
  Finset.sum_range_succ _ _

private theorem F_step (m : ℕ) : F (m+1) = F m + W (m+1) := by
  have h :
      (∑ j ∈ Finset.range m, (m+1-j)*multiplicity j) =
      (∑ j ∈ Finset.range m, (m-j)*multiplicity j) + W m := by
    rw [W, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [show m+1-j = (m-j)+1 by omega, Nat.add_mul,Nat.one_mul]
  unfold F
  rw [Finset.sum_range_succ,h,W_step]
  simp
  omega

private theorem parity_W (h : ℕ) : W (2*h)=3*h ∧ W (2*h+1)=3*h+2 := by
  induction h with
  | zero => decide
  | succ h ih =>
    rw [show 2*(h+1) = (2*h+1)+1 by omega]
    rw [W_step (2*h+1+1),W_step (2*h+1),ih.2]
    simp [multiplicity]
    omega

private theorem parity_F (h : ℕ) :
    F (2*h)=3*h^2+2*h+2 ∧ F (2*h+1)=3*h^2+5*h+4 := by
  induction h with
  | zero => decide
  | succ h ih =>
    have h₁ := (parity_W (h+1)).1
    have h₂ := (parity_W (h+1)).2
    rw [show 2*(h+1) = (2*h+1)+1 by omega] at h₁ h₂ ⊢
    rw [F_step (2*h+1+1),F_step (2*h+1),ih.2,h₁,h₂]
    constructor <;> ring

private theorem closed (n : ℕ) (hn : 2 ≤ n) :
    8*(term n : ℤ) = 15+(-1)^n-4*(n:ℤ)+6*(n:ℤ)^2 := by
  obtain ⟨m,hm⟩ : ∃ m, n=m+1 := ⟨n-1,by omega⟩
  subst n
  rw [counted m (by omega)]
  obtain ⟨h,hh | hh⟩ := m.even_or_odd'
  · subst m
    rw [(parity_F h).1, pow_succ (-1:ℤ) (2*h), pow_mul (-1:ℤ) 2 h]
    norm_num
    ring
  · subst m
    rw [(parity_F h).2, pow_succ (-1:ℤ) (2*h+1), pow_succ (-1:ℤ) (2*h), pow_mul (-1:ℤ) 2 h]
    norm_num
    ring

private theorem recur (k : ℕ) :
    term (k+6)+2*term (k+3) = 2*term (k+5)+term (k+2) := by
  have h₆ := closed (k+6) (by omega)
  have h₅ := closed (k+5) (by omega)
  have h₃ := closed (k+3) (by omega)
  have h₂ := closed (k+2) (by omega)
  apply Int.ofNat_inj.mp
  push_cast at *
  simp only [pow_add] at h₆ h₅ h₃ h₂
  norm_num at h₆ h₅ h₃ h₂
  nlinarith only [h₆,h₅,h₃,h₂]

open PowerSeries in
private theorem generating :
    (1-2*X+2*X^3-X^4)*series = 4*X^2-X^3-2*X^4+2*X^5 := by
  have coefficient (n : ℕ) : coeff n series = (term n : ℚ) := by simp [series]
  have shift (n j : ℕ) :
      coeff n ((X : PowerSeries ℚ)^j * series) =
        if j ≤ n then (term (n-j) : ℚ) else 0 := by
    rw [coeff_X_pow_mul']
    simp only [series,coeff_mk]
  ext n
  have hpoly : (1-2*X+2*X^3-X^4)*series =
      series-(X^1*series+X^1*series)+(X^3*series+X^3*series)-X^4*series := by ring
  rw [hpoly]
  have hrhs : (4*X^2-X^3-2*X^4+2*X^5 : PowerSeries ℚ) =
      (X^2+X^2+X^2+X^2)-X^3-(X^4+X^4)+(X^5+X^5) := by ring
  rw [hrhs]
  simp only [map_sub,map_add,shift,coeff_X_pow,coefficient]
  by_cases hn : n < 6
  · interval_cases n <;> decide +kernel
  · obtain ⟨k,hk⟩ : ∃ k, n=k+6 := ⟨n-6,by omega⟩
    subst n
    have hc : (term (k+6) : ℚ)+2*term (k+3) = 2*term (k+5)+term (k+2) := by exact_mod_cast recur k
    simp only [if_pos (by omega : 1 ≤ k+6),if_pos (by omega : 3 ≤ k+6),
      if_pos (by omega : 4 ≤ k+6),if_neg (by omega : k+6 ≠ 2),if_neg (by omega : k+6 ≠ 3),
      if_neg (by omega : k+6 ≠ 4),if_neg (by omega : k+6 ≠ 5)]
    simp only [show k+6-1=k+5 by omega,show k+6-3=k+3 by omega,show k+6-4=k+2 by omega]
    linarith

end OMA.S_oeis_a132297

open OMA.S_oeis_a132297 in
theorem OMA.solution : type_of% @OMA.S_oeis_a132297.main := ⟨closed,recur,generating⟩
