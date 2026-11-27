import OMAStatements.S_oeis_a384539

open OMA.S_oeis_a384539

/-! Write the two middle pieces as X and Y. The adjacent cuts have
quotients j and l, and Y/X = p/s. The three division equations yield
a nonzero integral determinant, uniformly bounding the number of digits. -/

private lemma cut {n : ℕ} (hn : term n) (i x y : ℕ) (hi : i < Nat.log 10 n)
    (he : n = 10^(i+1)*x+y) (hy : y < 10^(i+1)) : x ∣ y ∨ y ∣ x := by
  have h := hn.2.2 i (List.mem_range.mpr hi)
  rw [he, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hy, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hy] at h
  exact h

private lemma small_dvd {x y : ℕ} (hp : 0 < x) (hlt : x < y)
    (h : x ∣ y ∨ y ∣ x) : x ∣ y :=
  h.resolve_right (fun h' => (Nat.not_le_of_gt hlt) (Nat.le_of_dvd hp h'))

private lemma bound_scale (T X b c p s j l : ℕ)
    (hb : 0 < b) (hs : 0 < s)
    (hB : 10*s < l*p) (hjl : 100 < j*l)
    (h1 : (s*j)*X = 10*p*X + b*s*(100*T+j))
    (h2 : (l*p)*X = 10*s*X + c*s*(l*T+1))
    (hbl : b < 10) (hpl : p < 10) (hjl' : j < 1000) (hll : l < 10000) :
    T < 10^9 := by
  zify at *
  let A : ℤ := (s:ℤ)*j-10*p
  let B : ℤ := (l:ℤ)*p-10*s
  have hB' : 0 < B := by dsimp [B]; linarith
  have e1 : A*X = b*s*(100*T+j) := by dsimp [A]; linarith
  have e2 : B*X = c*s*(l*T+1) := by dsimp [B]; linarith
  have e3 : (b:ℤ)*B*(100*T+j) = c*A*(l*T+1) := by
    apply mul_right_cancel₀ (ne_of_gt hs)
    linear_combination B * -e1 + A * e2
  let D : ℤ := c*l*A-100*b*B
  have det : D*(l*T+1) = b*B*(j*l-100) := by
    dsimp [D]
    linear_combination - (l:ℤ)*e3
  have rpos : 0 < (b:ℤ)*B*(j*l-100) :=
    mul_pos (mul_pos hb hB') (by linarith)
  have hF : 0 < (l:ℤ)*T+1 := by positivity
  have dpos : 0 < D := pos_of_mul_pos_left (det.symm ▸ rpos) hF.le
  have coarse : (l:ℤ)*T+1 ≤ b*B*(j*l-100) := by
    rw [← det]; nlinarith only [mul_nonneg (show 0 ≤ D-1 by omega) hF.le]
  have hL : 0 < (l:ℤ) := by by_contra! h; nlinarith [show 0 ≤ (l:ℤ) by positivity]
  have ht : (T:ℤ) < b*B*j := by
    by_contra! h
    nlinarith only [coarse, mul_le_mul_of_nonneg_left h hL.le, mul_pos hb hB']
  have hBp : B ≤ 100000 := by
    dsimp [B]
    have H := mul_le_mul_of_nonneg_left (show (p:ℤ) ≤ 10 by omega) (show 0 ≤ (l:ℤ) by positivity)
    linarith
  have hprod : (b:ℤ)*B*j ≤ 10*100000*1000 := by
    exact mul_le_mul (mul_le_mul (by omega) hBp hB'.le (by decide)) (by omega)
      (by positivity) (by decide)
  norm_num at *
  omega

/-- Three exact quotients specify a candidate. The two guards cut out
nonintegral reconstructions before testing the original definition. -/
private def candidate (T b p s j : ℕ) : ℕ :=
  let a := s*j - 10*p
  let z := b*(10*s*T+p)
  if a = 0 ∨ z%a ≠ 0 then 0 else
    let x := 10*(z/a)+b
    if p*x%s ≠ 0 then 0 else
      let y := p*x/s
      if T ≤ y ∧ y < 10*T ∧ T ≤ x ∧ x < 100*T then 10*T*x+y else 0

private def ratios (p s j : ℕ) : Prop :=
  (s=1 ∧ p<10 ∧ j<1000) ∨ (p=1 ∧ ((s<10 ∧ j<1000) ∨ (s<100 ∧ j<100)))

private def covered (n : ℕ) : Prop :=
  ∃ t b p s j : ℕ, t<8 ∧ b<10 ∧ ratios p s j ∧
    (s*j-10*p) ∣ 2520*(10*s*(10^(t+1))+p) ∧
    n = candidate (10^(t+1)) b p s j

private lemma reconstruct {t T P X Y Q b c p s j l : ℕ}
    (hT : T=10^(t+1))
    (hb : 0<b) (hb' : b<10) (hc : 0<c) (hs : 0<s)
    (hp' : p<10) (hj' : j<1000) (hl' : l<10000)
    (hR : ratios p s j) (hX : X=10*P+b) (hY : Y=c*T+Q)
    (hQ : Q<T)
    (hXlo : T≤X) (hXhi : X<100*T) (hYlo : T≤Y) (hYhi : Y<10*T)
    (hmid : s*Y=p*X) (hleft : j*P=10*b*T+Y) (hright : l*Q=10*X+c) :
    covered (10*T*X+Y) := by
  have hTpos : 0<T := hT ▸ by positivity
  have eqP : (s*j)*P = 10*p*P+b*(10*s*T+p) := by
    linear_combination s*hleft+hmid+p*hX
  have eq1 : (s*j)*X = 10*p*X+b*s*(100*T+j) := by
    linear_combination 10*eqP+s*j*hX-10*p*hX
  have eq2 : (l*p)*X = 10*s*X+c*s*(l*T+1) := by
    linear_combination s*hright+s*l*hY-l*hmid
  have hA : 10*p<s*j := by
    by_contra! h
    have := Nat.mul_le_mul_right P h
    have : 0<b*(10*s*T+p) := by positivity
    omega
  have hB : 10*s<l*p := by
    by_contra! h
    have := Nat.mul_le_mul_right X h
    have : 0<c*s*(l*T+1) := by positivity
    omega
  have hjl : 100<j*l := by
    have hV : Q < j*P := by omega
    have hL : 0<l := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hB
    have := Nat.mul_lt_mul_of_pos_left hV hL
    have e : l*(j*P) = (j*l)*P := by ring
    by_contra! h
    have := Nat.mul_le_mul_right P h
    linarith
  have size := bound_scale T X b c p s j l hb hs hB hjl eq1 eq2 hb' hp' hj' hl'
  have ht : t<8 := by
    by_contra! h
    have := Nat.pow_le_pow_right (n := 10) (by decide) (show 9≤t+1 by omega)
    omega
  have za : b*(10*s*T+p) = (s*j-10*p)*P := by
    rw [Nat.sub_mul]; omega
  have ha : 0<s*j-10*p := by omega
  have nine : ∀ v ∈ List.range 10, v ≠ 0 → v ∣ 2520 := by decide
  have hd := nine b (List.mem_range.mpr hb') (by omega)
  have hd' : (s*j-10*p) ∣ 2520*(10*s*T+p) :=
    dvd_trans (show (s*j-10*p) ∣ b*(10*s*T+p) from ⟨P,za⟩) (Nat.mul_dvd_mul_right hd _)
  refine ⟨t,b,p,s,j,ht,hb',hR,hT ▸ hd',?_⟩
  simp [candidate, ← hT, za, Nat.ne_of_gt ha, Nat.mul_div_cancel_left P ha,
    ← hX, ← hmid, Nat.mul_div_cancel_left Y hs, hYlo, hYhi, hXlo, hXhi]

private lemma multiplier_lt {a x M U : ℕ} (h : a*x < M*U) (hx : U≤x) : a<M := by
  by_contra! hg
  exact (Nat.not_le_of_gt h) (Nat.mul_le_mul hg hx)

private lemma three_cuts {n t U P X Y Q b c : ℕ} (hU : U=10^t) (_hUpos : 0<U)
    (hn : n=100*U*X+Y) (hX : X=10*P+b) (hY : Y=c*(10*U)+Q)
    (hb : 0<b) (hb' : b<10) (hc : 0<c) (hc' : c<10)
    (hQlo : U≤Q) (hQhi : Q<10*U) (hXlo : 10*U≤X) (hXhi : X<1000*U)
    (hYlo : 10*U≤Y) (hYhi : Y<100*U)
    (dc : X ∣ Y ∨ Y ∣ X) (dl : P ∣ 100*b*U+Y ∨ 100*b*U+Y ∣ P)
    (dr : Q ∣ 10*X+c ∨ 10*X+c ∣ Q) : covered n := by
  have hPlo : U≤P := by omega
  have hPhi : P<100*U := by omega
  have vlow : 100*U≤100*b*U := by
    nlinarith only [Nat.mul_le_mul_right U (show 100≤100*b by omega)]
  have vhi : 100*b*U+Y<1000*U := by
    nlinarith only [Nat.mul_le_mul_right U (show 100*b≤900 by omega),hYhi]
  obtain ⟨j, hj⟩ := small_dvd (by omega) (by omega) dl
  obtain ⟨l, hl⟩ := small_dvd (by omega) (by omega) dr
  have hj0 : j*P=100*b*U+Y := by rw [hj, Nat.mul_comm]
  have hl0 : l*Q=10*X+c := by rw [hl, Nat.mul_comm]
  have hj' : j<1000 := multiplier_lt (hj0 ▸ vhi) hPlo
  have hl' : l<10000 := by
    apply multiplier_lt (U:=U) _ hQlo
    rw [hl0]; omega
  have hT : 10*U=10^(t+1) := by rw [hU, pow_succ, Nat.mul_comm]
  have hn' : n=10*(10*U)*X+Y := by rw [hn]; ring
  rw [hn']
  have hleft : j*P=10*b*(10*U)+Y := by rw [hj0]; ring
  have hXhi' : X<100*(10*U) := by omega
  have hYhi' : Y<10*(10*U) := by omega
  rcases dc with ⟨k,hk⟩ | ⟨k,hk⟩
  · have hk' : k<10 := by
      apply multiplier_lt (U:=10*U) _ hXlo
      simpa [hk, Nat.mul_comm X k] using hYhi'
    exact reconstruct hT hb hb' hc (by decide : 0<1) hk' hj' hl'
      (Or.inl ⟨rfl,hk',hj'⟩) hX hY hQhi hXlo hXhi' hYlo hYhi'
      (by simpa [Nat.mul_comm X k] using hk) hleft hl0
  · have hk' : k<100 := by
      apply multiplier_lt (U:=10*U) _ hYlo
      simpa [hk,Nat.mul_comm Y k] using hXhi'
    have hkpos : 0<k := by by_contra! hk0; simp [Nat.eq_zero_of_le_zero hk0] at hk; omega
    have hr : ratios 1 k j := by
      refine Or.inr ⟨rfl,?_⟩
      by_cases small : k<10
      · exact Or.inl ⟨small,hj'⟩
      · have big : 10*(10*U)≤X := by rw [hk, Nat.mul_comm Y k]; exact Nat.mul_le_mul (by omega) hYlo
        have hP : 10*U≤P := by omega
        refine Or.inr ⟨hk', multiplier_lt (U:=10*U) ?_ hP⟩
        rw [hj0]; omega
    exact reconstruct hT hb hb' hc hkpos (by decide : 1<10) hj' hl' hr
      hX hY hQhi hXlo hXhi' hYlo hYhi' (by simpa [Nat.mul_comm k Y] using hk.symm) hleft hl0

private lemma cover_large {n : ℕ} (good : term n) (hbig : 1000≤n) : covered n := by
  let g := Nat.log 10 n
  let t := (g-3)/2
  let U := 10^t
  have ng : n<10^(g+1) := Nat.lt_pow_succ_log_self (by decide) n
  have gn : 10^g≤n := Nat.pow_log_le_self _ (by omega)
  have hg : 3≤g := by
    by_contra! h
    have := Nat.pow_le_pow_right (n:=10) (by decide) (show g+1≤3 by omega)
    omega
  have gtlo : t+t+3≤g := by dsimp [t]; omega
  have gthi : g+1≤t+t+5 := by dsimp [t]; omega
  have u : 0<U := by dsimp [U]; positivity
  have lo : 1000*U*U≤n := by
    calc
      _ = 10^(t+t+3) := by simp [U,pow_add]; ring
      _ ≤ 10^g := Nat.pow_le_pow_right (by decide) gtlo
      _ ≤ n := gn
  have hi : n<100000*U*U := by
    calc
      _ < 10^(g+1) := ng
      _ ≤ 10^(t+t+5) := Nat.pow_le_pow_right (by decide) gthi
      _ = _ := by simp [U,pow_add]; ring
  let W := n/(10*U)
  let Q := n%(10*U)
  let X := W/10
  let c := W%10
  let b := X%10
  let P := X/10
  let Y := c*(10*U)+Q
  have dec0 : n=(10*U)*W+Q := (Nat.mod_add_div n (10*U)).symm.trans (Nat.add_comm _ _)
  have dec1 : W=10*X+c := (Nat.mod_add_div W 10).symm.trans (Nat.add_comm _ _)
  have dec2 : X=10*P+b := (Nat.mod_add_div X 10).symm.trans (Nat.add_comm _ _)
  have nq : Q<10*U := Nat.mod_lt _ (by positivity)
  have cb : c<10 := Nat.mod_lt _ (by decide)
  have bb : b<10 := Nat.mod_lt _ (by decide)
  have pow1 : 10^(t+1)=10*U := by rw [pow_succ,Nat.mul_comm]
  have pow2 : 10^(t+2)=100*U := by rw [pow_succ,pow1]; omega
  have pow3 : 10^(t+3)=1000*U := by rw [pow_succ,pow2]; omega
  have whole : n=100*U*X+Y := by rw [dec0,dec1]; dsimp only [Y]; ring
  have cbpos : 0<c := by
    have := good.2.1 (t+1) (List.mem_range.mpr (show t+1<g+1 by omega))
    change 0<n/ (10*U)%10
    rw [pow1] at this
    omega
  have bbpos : 0<b := by
    have h := good.2.1 (t+2) (List.mem_range.mpr (show t+2<g+1 by omega))
    change 0<n/(10*U)/10%10
    rw [Nat.div_div_eq_div_mul,show 10*U*10=100*U by ring,← pow2]
    omega
  have qlo : U≤Q := by
    have d := good.2.1 t (List.mem_range.mpr (show t<g+1 by omega))
    have hh : Q/U=n/U%10 := by
      change n%(10*U)/U=_
      rw [Nat.mul_comm 10 U, Nat.mod_mul_right_div_self]
    by_contra! h
    rw [Nat.div_eq_of_lt h] at hh
    exact d hh.symm
  have Ylo : 10*U≤Y := by
    have := Nat.mul_le_mul_right (10*U) (show 1≤c by omega)
    dsimp only [Y]; omega
  have Yhi : Y<100*U := by
    have := Nat.mul_le_mul_right (10*U) (show c≤9 by omega)
    dsimp only [Y]; omega
  have Xlo : 10*U≤X := by
    by_contra! h
    have := Nat.mul_le_mul_left (100*U) (show X+1≤10*U by omega)
    nlinarith only [this, whole, lo, Yhi]
  have Xhi : X<1000*U := by
    by_contra! h
    have := Nat.mul_le_mul_left (100*U) h
    nlinarith only [this, whole, hi, Nat.zero_le Y]
  apply three_cuts (t:=t) rfl u whole dec2 (by rfl) bbpos bb cbpos cb qlo nq Xlo Xhi Ylo Yhi
  · apply cut good (t+1) _ _ (show t+1<g by omega)
    · simpa [pow2] using whole
    · simpa [pow2] using Yhi
  · apply cut good (t+2) _ _ (show t+2<g by omega)
    · rw [pow3,whole,dec2]; ring
    · rw [pow3]
      change 100*b*U+Y<1000*U
      have := Nat.mul_le_mul_right U (show 100*b≤900 by omega)
      nlinarith only [this,Yhi]
  · apply Or.symm
    apply cut good t _ _ (show t<g by omega)
    · rw [pow1, ← dec1]; exact dec0
    · simpa [pow1] using nq

private def row (T p s cap : ℕ) : Bool :=
  let z := 2520*(10*s*T+p)
  (List.range cap).all fun j =>
    if z%(s*j-10*p)=0 then
      (List.range 10).all fun b =>
        let n := candidate T b p s j
        if n=0 then true else decide (term n → n ∈ entries)
    else true

private def rowsAt (t : ℕ) : Bool :=
  let T := 10^(t+1)
  (List.range 10).all (fun p => row T p 1 1000) &&
    (List.range 100).all (fun s => row T 1 s (if s<10 then 1000 else 100))

private lemma row_sound {n T p s cap j b : ℕ} (good : term n)
    (hj : j<cap) (hb : b<10) (hd : s*j-10*p ∣ 2520*(10*s*T+p))
    (he : n=candidate T b p s j) (h : row T p s cap=true) : n ∈ entries := by
  have h1 := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  simp only [Nat.mod_eq_zero_of_dvd hd, if_true] at h1
  have h2 := List.all_eq_true.mp h1 b (List.mem_range.mpr hb)
  have hn := good.1
  simpa [← he, show n≠0 by omega, good] using h2

private lemma checked_implies {n : ℕ} (checks : ∀ t<8, rowsAt t=true)
    (good : term n) (h : covered n) : n ∈ entries := by
  obtain ⟨t,b,p,s,j,ht,hb,hr,hd,he⟩ := h
  have rs := checks t ht
  simp only [rowsAt, Bool.and_eq_true, List.all_eq_true, List.mem_range] at rs
  obtain ⟨r1,r2⟩ := rs
  rcases hr with ⟨rfl,hp,hj⟩ | ⟨rfl,hs⟩
  · exact row_sound good hj hb hd he (r1 p hp)
  · obtain ⟨hs',hj⟩ : s<100 ∧ j<(if s<10 then 1000 else 100) := by
      split <;> omega
    exact row_sound good hj hb hd he (r2 s hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem all_checked : ∀ t<8, rowsAt t=true := by
  intro t ht
  interval_cases t <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem OMA.solution : type_of% @OMA.S_oeis_a384539.main := by
  refine ⟨fun n => ⟨fun hn => ?_, fun hm => ?_⟩, by decide +kernel, by decide⟩
  · by_cases h : n<1000
    · have small : ∀ x ∈ List.range 1000, term x → x ∈ entries := by decide +kernel
      exact small n (List.mem_range.mpr h) hn
    · exact checked_implies all_checked hn (cover_large hn (by omega))
  · have listed : ∀ x ∈ entries, term x := by decide +kernel
    exact listed n hm
