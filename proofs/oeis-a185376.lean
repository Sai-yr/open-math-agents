import OMAStatements.S_oeis_a185376

/-!
# Counting binary necklaces with a palindromic cut

A rotation by k of a palindromic cut is again palindromic exactly when 2k
is a period. If the word has odd least period then only one distinct
palindromic cut occurs in its rotation class. Otherwise there are two,
separated by half of the least period. The singleton classes are counted
by restricting the repeated word to the odd part of the length.
-/
namespace A185376Proof
open OMA.S_oeis_a185376 Finset

/- The first half determines the palindrome. -/

private def rem (L : ℕ) (i : ℤ) := (i%(L:ℤ)).toNat
private def idx (L : ℕ) (i : ℤ) := min (rem L i) (L-1-rem L i)

private theorem rem_lt {L : ℕ} (hL : 0<L) (i : ℤ) : rem L i<L := by
  have hp : (0:ℤ)<L := by exact_mod_cast hL
  have := Int.emod_lt_of_pos i hp
  dsimp [rem]; omega

private theorem rem_cast {L : ℕ} (hL : 0<L) (i : ℤ) : (rem L i:ℤ)=i%(L:ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast hL.ne')

private theorem refl_rem {L : ℕ} (hL : 0<L) (i : ℤ) :
    rem L (-1-i)=L-1-rem L i := by
  have he := Int.emod_add_mul_ediv i (L:ℤ)
  have hp : (0:ℤ)<L := by exact_mod_cast hL
  have lo := Int.emod_nonneg i hp.ne'
  have hi := Int.emod_lt_of_pos i hp
  have h : -1-i= ((L:ℤ)-1-i%L)+(-1-i/L)*L := by nlinarith [he]
  have r := rem_cast hL i
  unfold rem
  rw [h,Int.add_mul_emod_self_right,Int.emod_eq_of_lt (by omega) (by omega)]
  omega

private theorem idx_lt {L : ℕ} (hL : 0<L) (i : ℤ) : idx L i < (L+1)/2 := by
  have h := rem_lt hL i
  dsimp [idx]; omega

private theorem repr {L : ℕ} (hL : 0<L) (w : PalWord L) (i : ℤ) :
    w.val i=w.val (idx L i) := by
  have H : w.val i=w.val (rem L i) := by
    rw [rem_cast hL]
    have h := w.property.1.int_mul (i/(L:ℤ)) (i%(L:ℤ))
    change w.val (i%(L:ℤ)+(i/(L:ℤ))*L)=_ at h
    rw [Int.emod_add_ediv_mul] at h
    exact h
  rw [H]; unfold idx
  by_cases hb : rem L i≤L-1-rem L i
  · rw [min_eq_left hb]
  · rw [min_eq_right (by omega)]
    have H := w.property.1 (-1-(rem L i:ℤ))
    rw [w.property.2] at H
    apply H.symm.trans
    apply congrArg w.val
    have hh := rem_lt hL i
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),Nat.cast_one]
    ring

private def wordEquiv {L : ℕ} (hL : 0<L) : PalWord L ≃ (Fin ((L+1)/2) → Bool) where
  toFun w := fun j=>w.val (j.val:ℤ)
  invFun g := ⟨fun i=>g ⟨idx L i,idx_lt hL i⟩,by
    constructor
    · intro i
      apply congrArg g; apply Fin.ext
      simp [idx,rem]
    · intro i
      apply congrArg g; apply Fin.ext
      have h := refl_rem hL i
      have hh := rem_lt hL i
      dsimp [idx]; rw [h]; omega⟩
  left_inv := by
    intro w; apply Subtype.ext; funext i; exact (repr hL w i).symm
  right_inv := by
    intro g; funext j
    apply congrArg g; apply Fin.ext
    have hh := j.isLt
    have hp : (0:ℤ)<L := by exact_mod_cast hL
    have e : rem L (j.val:ℤ)=j.val := by
      have hj0 : (0:ℤ)≤j.val := by positivity
      have hj1 : (j.val:ℤ)<L := by exact_mod_cast (show j.val<L by omega)
      simp only [rem,Int.emod_eq_of_lt hj0 hj1,Int.toNat_natCast]
    dsimp [idx]; rw [e]; omega

private theorem card_words {L : ℕ} (hL : 0<L) : Nat.card (PalWord L)=2^((L+1)/2) := by
  rw [Nat.card_congr (wordEquiv hL),Nat.card_fun]
  simp

/- Integer periods and the action of a rotation on the reflection. -/

private theorem period_generator {L : ℕ} (hL : 0<L) (w : PalWord L) :
    ∃ p : ℕ, 0<p ∧ ∀ k : ℤ,Function.Periodic w.val k ↔ (p:ℤ)∣k := by
  classical
  let H : ∃ p : ℕ,0<p ∧ Function.Periodic w.val (p:ℤ) := ⟨L,hL,w.property.1⟩
  let p := Nat.find H
  have ⟨hp,hper⟩ := Nat.find_spec H
  change 0<p at hp
  change Function.Periodic w.val (p:ℤ) at hper
  refine ⟨p,hp,fun k=>⟨?_,?_⟩⟩
  · intro hk
    have hp' : (0:ℤ)<p := by exact_mod_cast hp
    have h₁ := Int.emod_nonneg k hp'.ne'
    have h₂ := Int.emod_lt_of_pos k hp'
    have hr : Function.Periodic w.val (k%(p:ℤ)) := by
      have h := hk.sub_period (hper.int_mul (k/(p:ℤ)))
      change Function.Periodic w.val (k-k/(p:ℤ)*p) at h
      have e := Int.emod_add_ediv_mul k (p:ℤ)
      rwa [show k-k/(p:ℤ)*p=k%(p:ℤ) by omega] at h
    apply Int.dvd_of_emod_eq_zero
    by_contra hne
    have hlt : (k%(p:ℤ)).toNat<p := by omega
    exact Nat.find_min H hlt ⟨by omega,by simpa [Int.toNat_of_nonneg h₁] using hr⟩
  · rintro ⟨z,rfl⟩
    simpa only [Int.cast_id,mul_comm] using hper.int_mul z

private theorem pal_shift {L : ℕ} (w : PalWord L) (k : ℤ) :
    (∀ i, w.val (-1-i+k)=w.val (i+k)) ↔ Function.Periodic w.val (2*k) := by
  constructor
  · intro h i
    have hh := h (-1-i-k)
    rw [show -1-(-1-i-k)+k=i+2*k by ring,
      show -1-i-k+k=-1-i by ring,w.property.2] at hh
    exact hh
  · intro h i
    have e := w.property.2 (i-k)
    rw [show -1-(i-k)=-1-i+k by ring] at e
    exact e.trans (by simpa [show i-k+2*k=i+k by ring] using (h (i-k)).symm)

private def turn {L : ℕ} (w : PalWord L) (k : ℤ) (h : Function.Periodic w.val (2*k)) :
    PalWord L := ⟨fun i=>w.val (i+k), by
      constructor
      · intro i; simpa only [add_right_comm i (L:ℤ) k] using w.property.1 (i+k)
      · exact (pal_shift w k).mpr h⟩

private theorem shift_eq {L : ℕ} (w v : PalWord L) {k : ℤ}
    (hv : ∀ i,v.val i=w.val (i+k)) {j : ℤ} (h : Function.Periodic w.val (k-j)) :
    ∀ i,v.val i=w.val (i+j) := by
  intro i; rw [hv]
  simpa only [show i+j+(k-j)=i+k by ring] using h (i+j)

private theorem periods_same {L : ℕ} (w v : PalWord L) {k : ℤ}
    (hv : ∀ i,v.val i=w.val (i+k)) (m : ℤ) :
    Function.Periodic v.val m ↔ Function.Periodic w.val m := by
  constructor
  · intro h i
    have hh := h (i-k)
    simpa only [hv,show i-k+m+k=i+m by ring,show i-k+k=i by ring] using hh
  · intro h i
    simp only [hv,add_right_comm i m k,h (i+k)]

private theorem shifted_period {L : ℕ} (w v : PalWord L) {k : ℤ}
    (hv : ∀ i,v.val i=w.val (i+k)) : Function.Periodic w.val (2*k) :=
  (pal_shift w k).mp (fun i=>by simpa only [hv] using v.property.2 i)

/- The palindromic representatives of a single rotation class. -/

private def cls {L : ℕ} (w : PalWord L) : Necklace L := Quotient.mk (rotation L) w

private theorem same {L : ℕ} (w v : PalWord L) :
    cls v=cls w ↔ ∃ k : ℤ,∀ i,v.val i=w.val (i+k) :=
  ⟨fun h=>Quotient.exact h.symm,fun h=>(Quotient.sound h).symm⟩

private noncomputable def fiber {L : ℕ} [Fintype (PalWord L)] (c : Necklace L) : Finset (PalWord L) := by
  classical exact Finset.univ.filter (fun v=>cls v=c)

private theorem mem_fiber {L : ℕ} [Fintype (PalWord L)] (c : Necklace L) (w : PalWord L) :
    w∈fiber c ↔ cls w=c := by classical simp [fiber]

private theorem odd_class {L p : ℕ} [Fintype (PalWord L)] (w : PalWord L)
    (hper : ∀ k : ℤ, Function.Periodic w.val k ↔ (p:ℤ)∣k) (hp : Odd p) :
    fiber (cls w)={w} := by
  classical
  ext v; rw [mem_fiber,mem_singleton]
  constructor
  · intro h
    obtain ⟨k,hk⟩ := (same w v).mp h
    have h₂ := Int.natCast_dvd.mp ((hper _).mp (shifted_period w v hk))
    rw [Int.natAbs_mul] at h₂
    have h₁ : (p:ℤ)∣k := Int.natCast_dvd.mpr ((Nat.coprime_two_right.mpr hp).dvd_of_dvd_mul_left h₂)
    apply Subtype.ext; funext i
    exact (hk i).trans (((hper _).mpr h₁) i)
  · rintro rfl; rfl

private theorem even_class {L a : ℕ} [Fintype (PalWord L)] (ha : 0<a) (w : PalWord L)
    (hper : ∀ k : ℤ, Function.Periodic w.val k ↔ ((2*a:ℕ):ℤ)∣k) :
    (fiber (cls w)).card=2 := by
  classical
  have hp : Function.Periodic w.val (2*(a:ℤ)) := (hper _).mpr (by simp)
  let u := turn w (a:ℤ) hp
  have hu : u≠w := by
    intro h
    have hs : Function.Periodic w.val (a:ℤ) := fun i=>congrArg (fun v : PalWord L=>v.val i) h
    have hdvd := Int.natCast_dvd_natCast.mp ((hper _).mp hs)
    have := Nat.le_of_dvd ha hdvd
    omega
  have eq : fiber (cls w)={u,w} := by
    ext v; rw [mem_fiber,mem_insert,mem_singleton]
    constructor
    · intro he
      obtain ⟨k,hk⟩ := (same w v).mp he
      obtain ⟨z,hz⟩ := (hper _).mp (shifted_period w v hk)
      push_cast at hz
      have hkz : k=(a:ℤ)*z := by linarith
      rcases Int.even_or_odd z with ⟨t,ht⟩|⟨t,ht⟩
      · right
        have hs : Function.Periodic w.val k := (hper _).mpr ⟨t,by push_cast; rw [hkz,ht]; ring⟩
        apply Subtype.ext; funext i
        exact (hk i).trans (hs i)
      · left
        have hs : Function.Periodic w.val (k-a) := (hper _).mpr ⟨t,by push_cast; rw [hkz,ht]; ring⟩
        apply Subtype.ext; funext i
        exact shift_eq w v hk hs i
    · rintro (rfl|rfl)
      · exact (same w u).mpr ⟨a,fun _=>rfl⟩
      · rfl
  rw [eq,card_insert_of_notMem (by simpa using hu),card_singleton]

/- Count the singleton classes using the odd part of the length. -/

private noncomputable def small {L : ℕ} [Fintype (PalWord L)] (m : ℕ) : Finset (PalWord L) := by
  classical exact univ.filter (fun w : PalWord L=>Function.Periodic w.val (m:ℤ))

private theorem mem_small {L : ℕ} [Fintype (PalWord L)] (m : ℕ) (w : PalWord L) :
    w∈small m ↔ Function.Periodic w.val (m:ℤ) := by classical exact mem_filter.trans (and_iff_right (mem_univ w))

private def smallEquiv {L m : ℕ} [Fintype (PalWord L)] (hm : m∣L) :
    ↥(small (L:=L) m) ≃ PalWord m where
  toFun w := ⟨w.val.val,(mem_small _ _).mp w.property,w.val.property.2⟩
  invFun v := by
    have h : Function.Periodic v.val (L:ℤ) := by
      obtain ⟨j,hj⟩ := hm
      rw [hj,Nat.cast_mul,mul_comm]; exact v.property.1.nat_mul j
    exact ⟨⟨v.val,h,v.property.2⟩,(mem_small _ _).mpr v.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem count {L m e : ℕ} (hL : 0<L) (hm : Odd m) (hLm : L=2^e*m) :
    2*Nat.card (Necklace L)=Nat.card (PalWord L)+Nat.card (PalWord m) := by
  classical
  let _ : Finite (PalWord L) := (wordEquiv hL).finite_iff.mpr inferInstance
  let _ : Fintype (PalWord L) := Fintype.ofFinite _
  let _ : Finite (Necklace L) := by unfold Necklace; infer_instance
  let _ : Fintype (Necklace L) := Fintype.ofFinite _
  let S := small (L:=L) m
  have sc : S.card=Nat.card (PalWord m) := by
    have H := Nat.card_congr (smallEquiv (L:=L) (m:=m) (hLm ▸ dvd_mul_left m (2^e)))
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using H
  have hcount (c : Necklace L) : (fiber c).card+
      (S.filter (fun v=>cls v=c)).card=2 := by
    induction c using Quotient.inductionOn with
    | _ w =>
      change (fiber (cls w)).card+(S.filter (fun v=>cls v=cls w)).card=2
      obtain ⟨p,hp,H⟩ := period_generator hL w
      have hpL := Int.natCast_dvd_natCast.mp ((H _).mp w.property.1)
      rw [hLm] at hpL
      have hh : Function.Periodic w.val (m:ℤ) ↔ Odd p := by
        rw [H,Int.natCast_dvd_natCast]
        constructor
        · rintro ⟨a,ha⟩
          rw [ha] at hm
          exact (Nat.odd_mul.mp hm).1
        · intro h
          exact ((Nat.coprime_two_right.mpr h).pow_right e).dvd_of_dvd_mul_left hpL
      by_cases hodd : Odd p
      · have hr := odd_class w H hodd
        have hg : S.filter (fun v=>cls v=cls w)={w} := by
          ext v
          rw [mem_filter,mem_singleton]
          constructor
          · rintro ⟨_,hv⟩
            have h := (mem_fiber _ _).mpr hv
            simpa [hr] using h
          · rintro rfl; exact ⟨(mem_small _ _).mpr (hh.mpr hodd),rfl⟩
        rw [hr,hg,card_singleton]
      · have hd : 2∣p := by rw [Nat.odd_iff] at hodd; omega
        obtain ⟨a,rfl⟩ := hd
        have hc := even_class (by omega : 0<a) w H
        have hg : S.filter (fun v=>cls v=cls w)=∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro v hv
          obtain ⟨hs,he⟩ := mem_filter.mp hv
          obtain ⟨k,hk⟩ := (same w v).mp he
          exact hodd (hh.mp ((periods_same w v hk _).mp ((mem_small _ _).mp hs)))
        rw [hc,hg,card_empty,add_zero]
  have hr := card_eq_sum_card_fiberwise (s:=(univ : Finset (PalWord L)))
    (t:=(univ : Finset (Necklace L))) (f:=cls) (fun _ _=>mem_univ _)
  have hs := card_eq_sum_card_fiberwise (s:=S)
    (t:=(univ : Finset (Necklace L))) (f:=cls) (fun _ _=>mem_univ _)
  change univ.card=∑ c ∈ univ,(fiber c).card at hr
  calc 2*Nat.card (Necklace L) = ∑ _c ∈ (univ : Finset (Necklace L)),2 := by simp [Nat.card_eq_fintype_card,mul_comm]
       _ = ∑ c ∈ univ,((fiber c).card+(S.filter (fun v=>cls v=c)).card) :=
         sum_congr rfl (fun c _=>(hcount c).symm)
       _ = _ := by rw [sum_add_distrib,←hr,←hs,sc,card_univ,Nat.card_eq_fintype_card (α:=PalWord L)]

end A185376Proof

open OMA.S_oeis_a185376 A185376Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a185376.main := by
  intro n hn
  let e := n.factorization 2
  let m := n/2^e
  have he : 2^e*m=n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hm : Odd m := by
    have hh := Nat.not_dvd_ordCompl Nat.prime_two hn.ne'
    change ¬2∣m at hh
    rw [Nat.odd_iff]; omega
  have hpos : 0< m := by obtain ⟨a,ha⟩ := hm; omega
  have H := count (L:=2*n) (m:=m) (e:=e+1) (by omega) hm (by rw [pow_succ',mul_assoc,he])
  rw [card_words (by omega : 0<2*n),card_words hpos] at H
  obtain ⟨a,ha⟩ := hm
  have hn' : n=2^(e+1)*a+2^e := by rw [←he,ha,pow_succ]; ring
  have hp : 0<2^e := by positivity
  have ep : (n-2^e)/2^(e+1)=a := by
    rw [show n-2^e=2^(e+1)*a by omega,Nat.mul_div_cancel_left _ (by positivity)]
  change _=2^(n-1)+2^((n-2^e)/2^(e+1))
  rw [ep]
  rw [show (2*n+1)/2=n by omega,show (m+1)/2=a+1 by omega,pow_succ (2:ℕ) a] at H
  have hpow : (2:ℕ)^n=2^(n-1)*2 := by
    conv_lhs => rw [show n=(n-1)+1 by omega,pow_succ]
  rw [hpow] at H
  omega

