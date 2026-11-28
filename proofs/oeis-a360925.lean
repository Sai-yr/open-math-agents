import OMAStatements.S_oeis_a360925

/-!
# Shortest landing times from arbitrary nonnegative initial speed

An n-move braking phase must contribute at least n(n−1)/2 to the altitude
before the speed can first reach zero. A further s moves ending at rest
can make up at most floor(s²/4), even when the intermediate speed after
the first n moves is still positive. Every integer descent up to this
bound is attainable from rest. A trajectory attaining the required
descent after immediate braking therefore achieves the minimum.
-/

namespace A360925Proof
open OMA.S_oeis_a360925

private theorem single (u w : ℤ) (hlo : u-1≤w) (hhi : w≤u+1) : Flight 1 u w w := by
  simpa only [Int.zero_add] using Flight.move w (Flight.rest u) hlo hhi

private theorem append {t s : ℕ} {u v w x y : ℤ} (h1 : Flight t u v x) (h2 : Flight s v w y) :
    Flight (t+s) u w (x+y) := by
  induction h2 with
  | rest => simpa using h1
  | move w h lo hi ih =>
    simpa only [←Nat.add_assoc,←Int.add_assoc] using Flight.move w (ih h1) lo hi

private theorem shift {t : ℕ} {u v x : ℤ} (h : Flight t u v x) (k : ℤ) :
    Flight t (u+k) (v+k) (x+(t:ℤ)*k) := by
  induction h with
  | rest u => simpa using Flight.rest (u+k)
  | @move t u v d w h lo hi ih =>
    have hh := Flight.move (w+k) ih (by omega) (by omega)
    convert hh using 1
    push_cast
    ring

private theorem split_at (t s : ℕ) {u w d : ℤ} (h : Flight (t+s) u w d) :
    ∃ v x y : ℤ, Flight t u v x ∧ Flight s v w y ∧ d=x+y := by
  induction s generalizing w d with
  | zero => exact ⟨w,d,0,h,Flight.rest w,by simp⟩
  | succ s ih =>
    cases h with
    | @move _ _ z d' w h lo hi =>
      obtain ⟨v,x,y,h1,h2,e⟩:=ih h
      exact ⟨v,x,y+w,h1,Flight.move w h2 lo hi,by omega⟩

private theorem start_bound {t : ℕ} {u v d : ℤ} (h : Flight t u v d) :
    u-t≤v ∧ 2*(t:ℤ)*u-(t:ℤ)*(t+1)≤2*d := by
  induction h with
  | rest => simp
  | @move t u v d w h lo hi ih =>
    obtain ⟨a,b⟩:=ih
    push_cast
    exact ⟨by omega,by nlinarith⟩

private theorem end_bound {t : ℕ} {u v d : ℤ} (h : Flight t u v d) :
    2*(t:ℤ)*v-(t:ℤ)*(t-1)≤2*d := by
  induction h with
  | rest => simp
  | @move t u v d w h lo hi ih =>
    push_cast
    nlinarith [mul_nonneg (Int.natCast_nonneg t) (show 0≤v+1-w by omega)]

private def cap (s : ℕ) := (s/2)*((s+1)/2)
private def tri (n : ℕ) := n*(n-1)/2

private theorem cap_step (s : ℕ) : cap (s+2)=cap s+(s+1) := by
  have d : s=2*(s/2)+s%2 := by omega
  have a : (s+2)/2=s/2+1 := by omega
  have b : (s+2+1)/2=(s+1)/2+1 := by omega
  have c : s/2+(s+1)/2=s := by omega
  simp only [cap,a,b]
  nlinarith

private theorem cap_ge (s : ℕ) : s≤cap (s+1) := by
  induction s using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more s ih _ =>
    rw [show s+2+1=(s+1)+2 by omega,cap_step]
    omega

private theorem tri_succ (n : ℕ) : tri (n+1)=tri n+n := by
  cases n with
  | zero => decide
  | succ n =>
    simp only [tri,Nat.add_sub_cancel]
    have h : (n+1+1)*(n+1)=(n+1)*n+2*(n+1) := by ring
    rw [h]; omega

private theorem double_tri (n : ℕ) : (2:ℤ)*(tri n:ℤ)=(n:ℤ)*(n-1) := by
  induction n with
  | zero => decide
  | succ n ih => rw [tri_succ]; push_cast; nlinarith

private theorem brake (n : ℕ) : Flight n (n:ℤ) 0 (tri n) := by
  induction n with
  | zero => exact Flight.rest 0
  | succ n ih =>
    have st := single ((n:ℤ)+1) n (by omega) (by omega)
    have hh := append st ih
    rw [tri_succ]; push_cast; simpa [Nat.add_comm,Int.add_comm] using hh

end A360925Proof

namespace A360925Proof
open OMA.S_oeis_a360925

private theorem rest_capacity {s : ℕ} {u d : ℤ} (hu : 0≤u) (p : Flight s u 0 d) :
    -(cap s:ℤ) ≤ d := by
  let r:=s/2
  let c:=(s+1)/2
  have total : r+c=s := by dsimp [r,c]; omega
  have p' : Flight (r+c) u 0 d := total ▸ p
  obtain ⟨v,x,y,hx,hy,eq⟩:=split_at r c p'
  have a := (start_bound hx).2
  have b := end_bound hy
  have gap : c=r ∨ c=r+1 := by dsimp [r,c]; omega
  change -((r*c:ℕ):ℤ) ≤ d
  push_cast
  have nn := mul_nonneg (Int.natCast_nonneg r) hu
  rcases gap with e|e
  · have e' : (c:ℤ)=r := by exact_mod_cast e
    nlinarith
  · have e' : (c:ℤ)=r+1 := by exact_mod_cast e
    rw [e'] at b ⊢
    nlinarith

private theorem rest_reach (s : ℕ) : ∀ h : ℕ, h≤cap s → Flight s 0 0 (-(h:ℤ)) := by
  induction s using Nat.twoStepInduction with
  | zero =>
    intro h hh
    rw [show cap 0=0 by decide] at hh
    have : h=0 := by omega
    subst h; exact Flight.rest 0
  | one =>
    intro h hh
    rw [show cap 1=0 by decide] at hh
    have : h=0 := by omega
    subst h; exact single 0 0 (by decide) (by decide)
  | more s h0 h1 =>
    intro h hh
    by_cases low : h≤cap (s+1)
    · simpa using Flight.move 0 (h1 h low) (by decide) (by decide)
    have floor := cap_ge s
    have le : s+1≤h := by omega
    rw [cap_step] at hh
    have base := h0 (h-(s+1)) (by omega)
    have shifted := shift base (-1)
    simp only [Int.zero_add,mul_neg,mul_one] at shifted
    have down := single 0 (-1) (by decide) (by decide)
    have both := append down shifted
    have all := Flight.move 0 both (by decide) (by decide)
    rw [Nat.cast_sub le,Nat.cast_add,Nat.cast_one] at all
    convert all using 1 <;> omega

private theorem feasible {n t : ℕ} (h : Flight t (n:ℤ) 0 0) :
    n≤t ∧ tri n ≤ cap (t-n) := by
  have b := (start_bound h).1
  have le : n≤t := by omega
  refine ⟨le,?_⟩
  obtain ⟨v,x,y,st,fin,eq⟩:=split_at n (t-n) (show Flight (n+(t-n)) (n:ℤ) 0 0 by
    rwa [show n+(t-n)=t by omega])
  obtain ⟨vp,dp⟩:=start_bound st
  have bound := rest_capacity (show 0≤v by omega) fin
  have tr := double_tri n
  zify; nlinarith

private theorem fly (n s : ℕ) (hs : tri n ≤ cap s) : Flight (n+s) (n:ℤ) 0 0 := by
  simpa using append (brake n) (rest_reach s (tri n) hs)

end A360925Proof

namespace A360925Proof
open OMA.S_oeis_a360925

private def need (h : ℕ) := if h=0 then 0 else (4*h-3).sqrt+1

private theorem cap_sq (s : ℕ) : 4*cap s ≤ s^2 ∧ s^2≤4*cap s+1 := by
  let r:=s/2
  have choice : s=2*r ∨ s=2*r+1 := by dsimp [r]; omega
  rcases choice with e|e
  · have h : (s+1)/2=r := by omega
    change 4*(r*((s+1)/2)) ≤ s^2 ∧ s^2 ≤ 4*(r*((s+1)/2))+1
    rw [h,e]; constructor <;> nlinarith
  · have h : (s+1)/2=r+1 := by omega
    change 4*(r*((s+1)/2)) ≤ s^2 ∧ s^2 ≤ 4*(r*((s+1)/2))+1
    rw [h,e]; constructor <;> nlinarith

private theorem need_iff (h s : ℕ) : need h ≤ s ↔ h≤cap s := by
  by_cases hz : h=0
  · simp [need,hz]
  · rw [need,if_neg hz,Nat.succ_le_iff,Nat.sqrt_lt']
    have := cap_sq s
    omega

private theorem attains (n : ℕ) : Flight (n+need (tri n)) (n:ℤ) 0 0 :=
  fly n _ ((need_iff ..).mp le_rfl)

private theorem time_exact (n : ℕ) : time n = n+need (tri n) := by
  classical
  have ex : ∃ t : ℕ, Flight t (n:ℤ) 0 0 := ⟨_,attains n⟩
  rw [time,dif_pos ex]
  apply Nat.le_antisymm (Nat.find_min' ex (attains n))
  obtain ⟨hn,hb⟩:=feasible (Nat.find_spec ex)
  have := (need_iff ..).mpr hb
  omega

private theorem cap_next (s : ℕ) : cap (s+1)=cap s+(s+1)/2 := by
  have h : (s+1+1)/2=s/2+1 := by omega
  simp only [cap,h]; ring

private theorem increments (n : ℕ) (hn : 1≤n) :
    need (tri n)+1 ≤ need (tri (n+1)) ∧ need (tri (n+1)) ≤ need (tri n)+2 := by
  let q := need (tri n)
  have reaches : tri n≤cap q := (need_iff ..).mp le_rfl
  have tr : 2*tri n=n*(n-1) := by
    have h := double_tri n
    have en : ((n-1:ℕ):ℤ)=(n:ℤ)-1 := by rw [Nat.cast_sub hn]; norm_num
    exact_mod_cast (show (2:ℤ)*(tri n:ℤ)=(n:ℤ)*((n-1:ℕ):ℤ) by rw [en]; exact h)
  have qsmall : q≤2*n := by
    apply (need_iff ..).mpr
    have hcap : cap (2*n)=n*n := by unfold cap; rw [show 2*n/2=n by omega,show (2*n+1)/2=n by omega]
    rw [hcap]
    have := Nat.mul_le_mul_left n (Nat.sub_le n 1)
    omega
  have qlarge : n≤q+1 := by
    by_contra! hl
    have q0 := (cap_sq q).1
    have q1 := Nat.mul_le_mul (show q≤n by omega) (show q≤n-1 by omega)
    have pos : 0<n*(n-1) := Nat.mul_pos (by omega) (by omega)
    rw [sq] at q0
    omega
  change q+1 ≤ need (tri (n+1)) ∧ need (tri (n+1)) ≤ q+2
  rw [tri_succ]
  constructor
  · by_contra! hs
    have eq : tri n+n ≤cap q := (need_iff ..).mp (show need (tri n+n)≤q by omega)
    cases e : q with
    | zero => rw [e,show cap 0=0 by decide] at eq; omega
    | succ k =>
      have past : ¬tri n≤cap k := fun h=>by have := (need_iff ..).mpr h; change q≤k at this; omega
      rw [e,cap_next] at eq
      omega
  · apply (need_iff ..).mpr
    rw [cap_step]; omega

private theorem solved :
    (∀ n : ℕ, ∃ t : ℕ, Flight t (n:ℤ) 0 0) ∧ time 0 = 0 ∧ time 1 = 1 ∧
    (∀ n : ℕ, 2 ≤ n → time n = n+1+Nat.sqrt (2*n^2-2*n-3)) ∧
    (∀ n : ℕ, 1 ≤ n → time (n+1)-time n = 2 ∨ time (n+1)-time n = 3) := by
  refine ⟨fun n=>⟨_,attains n⟩,by rw [time_exact]; decide,by rw [time_exact]; decide,?_,?_⟩
  · intro n hn
    have ht : 0<tri n := by
      obtain ⟨m,rfl⟩ : ∃ m,n=m+2 := ⟨n-2,by omega⟩
      rw [tri_succ]; omega
    have eq : 4*tri n + 2*n=2*n^2 := by
      have h := double_tri n
      zify; nlinarith
    rw [time_exact,need,if_neg ht.ne',show 2*n^2-2*n-3=4*tri n-3 by omega]
    omega
  · intro n hn; rw [time_exact,time_exact]
    have := increments n hn; omega

end A360925Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a360925.main :=
  A360925Proof.solved
