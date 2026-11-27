import OMAStatements.S_mo_315485

namespace ChainPartition
open OMA.S_mo_315485

abbrev Chain (l : List ℕ) := l.Pairwise (fun a b => a < b ∧ a ∣ b)
def scale (d : ℕ) (l : List ℕ) := l.map (d * ·)

theorem sum_scale (d : ℕ) (l : List ℕ) : (scale d l).sum = d*l.sum := by
  induction l with
  | nil => simp [scale]
  | cons a l ih => simpa [scale,mul_add] using congrArg (d*a + ·) ih

theorem scale_chain {d : ℕ} (dp : 0 < d) {l : List ℕ} : Chain (scale d l) ↔ Chain l := by
  simp [Chain,scale,List.pairwise_map,Nat.mul_lt_mul_left dp,Nat.mul_dvd_mul_iff_left dp]

theorem cons_scale {d : ℕ} (dp : 0 < d) {l : List ℕ} :
    Chain (d :: scale d l) ↔ (∀ b ∈ l, 2 ≤ b) ∧ Chain l := by
  rw [Chain,List.pairwise_cons]
  change _ ∧ Chain (scale d l) ↔ _
  rw [scale_chain dp]
  apply and_congr_left
  intro _
  constructor
  · intro h b hb
    have lt := (h (d*b) (List.mem_map_of_mem hb)).1
    have hh : d*1 < d*b := by simpa using lt
    have := (Nat.mul_lt_mul_left dp).mp hh
    omega
  · intro h z hz
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hz
    exact ⟨by simpa using (Nat.mul_lt_mul_left dp).mpr (show 1 < b from h b hb),dvd_mul_right ..⟩

theorem enum_iff {lo : ℕ} (hp : 0 < lo) (k n : ℕ) (l : List ℕ) :
    l ∈ partitions lo k n ↔
      l.sum=n ∧ l.length=k ∧ (∀ b ∈ l, lo ≤ b) ∧ Chain l := by
  induction k generalizing n lo l with
  | zero =>
    cases l <;> by_cases h : n=0 <;> simp_all [partitions,Chain]
    omega
  | succ k ih =>
    constructor
    · intro h
      obtain ⟨d,hd,himage⟩ := Finset.mem_biUnion.mp h
      obtain ⟨tail,ht,rfl⟩ := Finset.mem_image.mp himage
      obtain ⟨hdiv,hl⟩ := Finset.mem_filter.mp hd
      obtain ⟨dv,nn⟩ := Nat.mem_divisors.mp hdiv
      have dp := hp.trans_le hl
      obtain ⟨hs,hk,hlow,chain⟩ := (ih (by decide : 0 < 2) _ _).mp ht
      have nd : 0 < n/d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero nn) dv) dp
      have rel : d*(1+tail.sum)=n := by rw [hs,show 1+(n/d-1)=n/d by omega,Nat.mul_div_cancel' dv]
      refine ⟨?_,by simpa using hk,?_,(cons_scale dp).mpr ⟨hlow,chain⟩⟩
      · change d + (scale d tail).sum=n
        rw [sum_scale,←rel]; ring
      · intro b hb
        rcases List.mem_cons.mp hb with rfl|hb
        · exact hl
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
        exact hl.trans (Nat.le_mul_of_pos_right d (by have := hlow a ha; omega))
    · rintro ⟨hs,hk,low,chain⟩
      cases l with
      | nil => simp at hk
      | cons d l =>
        have hl := low d (by simp)
        have dp := hp.trans_le hl
        obtain ⟨all,rem⟩ := List.pairwise_cons.mp chain
        let tail := l.map (· / d)
        have lift : scale d tail=l := by
          simp only [scale,tail,List.map_map]
          conv_rhs => rw [←List.map_id l]
          exact List.map_congr_left fun b hb => Nat.mul_div_cancel' (all b hb).2
        have split := (cons_scale dp).mp (lift ▸ chain : Chain (d :: scale d tail))
        have sum : n=d*(1+tail.sum) := by
          rw [←hs,List.sum_cons,←lift,sum_scale]; ring
        have pos : 0 < n := by rw [sum]; positivity
        have quo : n/d-1=tail.sum := by rw [sum,Nat.mul_div_cancel_left _ dp]; omega
        have member : tail ∈ partitions 2 k (n/d-1) := (ih (by decide : 0 < 2) _ _).mpr
          ⟨quo.symm,by simpa [tail] using hk,split.1,split.2⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨d,Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨⟨_,sum⟩,pos.ne'⟩,hl⟩,?_⟩
        exact Finset.mem_image.mpr ⟨tail,member,congrArg (d :: ·) lift⟩

theorem enum_card {lo : ℕ} (hp : 0 < lo) (k n : ℕ) :
    (partitions lo k n).card=count lo k n := by
  induction k generalizing n lo with
  | zero => by_cases h : n=0 <;> simp [partitions,count,h]
  | succ k ih =>
    rw [partitions,count,Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro d hd
      have dp := hp.trans_le (Finset.mem_filter.mp hd).2
      rw [Finset.card_image_of_injective,ih (by decide : 0 < 2)]
      intro u v eq
      apply (List.map_injective_iff (f:=fun x : ℕ => d*x)).mpr (fun _ _ z => Nat.eq_of_mul_eq_mul_left dp z)
      exact (List.cons.inj eq).2
    · intro d hd e he ne
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      obtain ⟨_,_,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨_,_,h⟩ := Finset.mem_image.mp hz'
      exact ne (List.cons.inj h).1.symm

end ChainPartition


namespace ChainPartition
open OMA.S_mo_315485

private theorem scaled {d n k : ℕ} {l : List ℕ} (dp : 0 < d) (h : IsPartition n k l) :
    IsPartition (d*n) k (scale d l) := by
  obtain ⟨hs,hk,pos,pair⟩ := h
  refine ⟨by rw [sum_scale,hs],by simpa [scale] using hk,?_,(scale_chain dp).mpr pair⟩
  intro x hx
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  exact Nat.mul_pos dp (pos a ha)

private theorem extend {d n k : ℕ} {l : List ℕ} (dp : 2 ≤ d) (h : IsPartition n k l) :
    IsPartition (1+d*n) (k+1) (1 :: scale d l) := by
  obtain ⟨a,b,pc,c⟩ := scaled (by omega : 0 < d) h
  refine ⟨by simpa using a,by simpa using b,?_,List.pairwise_cons.mpr ⟨?_,c⟩⟩
  · intro z hz
    rcases List.mem_cons.mp hz with rfl|hz
    · decide
    · exact pc _ hz
  · intro z hz
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    exact ⟨by have := Nat.le_mul_of_pos_right d (h.2.2.1 a ha); omega,one_dvd _⟩

private def powers : ℕ → List ℕ
  | 0 => []
  | k+1 => 1 :: scale 2 (powers k)

private theorem powers_valid (k : ℕ) : IsPartition (2^k-1) k (powers k) := by
  induction k with
  | zero => simp [IsPartition,powers]
  | succ k ih =>
    have h := extend (by decide : 2 ≤ 2) ih
    have pos : 0 < 2^k := by positivity
    rwa [show 1+2*(2^k-1)=2^(k+1)-1 by rw [pow_succ]; omega] at h

/-- A fixed power of two has a partition of each prescribed positive length. -/
private theorem seed (k : ℕ) :
    ∃ l, IsPartition (2^(2*(k+1))) (k+2) l := by
  let a := 2^(k+1)
  have ap : 0 < a := by dsimp [a]; positivity
  have h := extend (show 2 ≤ a+1 by omega) (powers_valid (k+1))
  have identity : 1+(a+1)*(2^(k+1)-1) = 2^(2*(k+1)) := by
    rw [two_mul,show (2:ℕ)^(k+1+(k+1))=a*a from pow_add ..]
    change 1+(a+1)*(a-1)=a*a
    have := Nat.sub_add_cancel (show 1 ≤ a by omega)
    nlinarith [congrArg (fun n : ℕ => a*n) this]
  exact ⟨_,identity ▸ h⟩

private theorem cutoff_pos (k : ℕ) : 0 < cutoff k := by
  cases k <;> simp [cutoff]

theorem eventual (n k : ℕ) (big : cutoff k ≤ n) : ∃ l, IsPartition n (k+1) l := by
  induction k generalizing n with
  | zero =>
    exact ⟨[n],by simpa [IsPartition] using (cutoff_pos 0).trans_le big⟩
  | succ k ih =>
    let M := 2^(2*(k+1))
    have Mp : 0 < M := by dsimp [M]; positivity
    change M*(2*cutoff k+1) ≤ n at big
    have np : 0 < n := (Nat.mul_pos Mp (Nat.succ_pos _)).trans_le big
    obtain ⟨e,t,⟨b,hb⟩,eq⟩ := Nat.exists_eq_two_pow_mul_odd np.ne'
    by_cases ex : 2*(k+1) ≤ e
    · obtain ⟨l,h⟩ := seed k
      have dv : M ∣ n := (pow_dvd_pow 2 ex).trans ⟨t,eq⟩
      obtain ⟨z,hz⟩ := dv
      have zp : 0 < z := by by_contra! h; simp [show z=0 by omega] at hz; omega
      exact ⟨_,(show z*M=n by rw [hz,mul_comm]) ▸ scaled zp h⟩
    · have upper : 2^e ≤ M := pow_le_pow_right₀ (by decide : 1 ≤ 2) (by omega)
      have nt : n ≤ M*t := eq ▸ Nat.mul_le_mul_right t upper
      have tlarge := Nat.le_of_mul_le_mul_left (big.trans nt) Mp
      obtain ⟨l,h⟩ := ih b (by omega)
      have oddpart : IsPartition t (k+2) (1::scale 2 l) := by
        have exp : 1+2*b=t := by omega
        exact exp ▸ extend (by decide : 2 ≤ 2) h
      exact ⟨_,eq.symm ▸ scaled (show 0 < 2^e by positivity) oddpart⟩

/-- Distinct normalized partitions can be scaled to every common multiple of
their sums; their distinct first parts remember which sum was selected. -/
theorem many (k b : ℕ) : ∃ M : ℕ, 0 < M ∧
    ∀ n : ℕ, 0 < n → M ∣ n → b ≤ count 1 (k+2) n := by
  let T := 2^(k+1)-1
  have Tpos : 0 < T := by
    dsimp [T]; rw [pow_succ]
    have : 0 < 2^k := by positivity
    omega
  let S (i : ℕ) := 1+(i+2)*T
  let M := (S b).factorial
  refine ⟨M,Nat.factorial_pos _,?_⟩
  intro n np mn
  have dvd (i : ℕ) (hi : i < b) : S i ∣ n := by
    apply Dvd.dvd.trans _ mn
    apply Nat.dvd_factorial (by dsimp [S]; omega)
    dsimp [S]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right T (by omega)) 1
  let part (i : ℕ) := scale (n/S i) (1::scale (i+2) (powers (k+1)))
  have pos (i : ℕ) (hi : i < b) : 0 < n/S i :=
    Nat.div_pos (Nat.le_of_dvd np (dvd i hi)) (by dsimp [S]; omega)
  have present (i : ℕ) (hi : i < b) : part i ∈ partitions 1 (k+2) n := by
    have base : IsPartition (S i) (k+2) (1::scale (i+2) (powers (k+1))) :=
      extend (by omega) (powers_valid (k+1))
    have h := scaled (pos i hi) base
    rw [Nat.div_mul_cancel (dvd i hi)] at h
    exact (enum_iff (by decide : 0 < 1) _ _ _).mpr ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩
  have inj {i j : ℕ} (hi : i < b) (hj : j < b) (eq : part i=part j) : i=j := by
    have first : n/S i=n/S j := by simpa [part,scale] using congrArg List.head? eq
    have eq2 := (Nat.div_mul_cancel (dvd i hi)).trans (Nat.div_mul_cancel (dvd j hj)).symm
    rw [←first] at eq2
    have se := Nat.eq_of_mul_eq_mul_left (pos i hi) eq2
    have ms : (i+2)*T=(j+2)*T := Nat.add_left_cancel se
    have := Nat.eq_of_mul_eq_mul_right Tpos ms
    omega
  have bound := Finset.card_le_card_of_injOn (s:=Finset.range b) (t:=partitions 1 (k+2) n)
    part (fun i hi => present i (Finset.mem_range.mp hi))
      (fun i hi j hj => inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj))
  simpa only [Finset.card_range,enum_card (by decide : 0 < 1)] using bound

private def staircase (a : ℕ) : ℕ → List ℕ
  | 0 => []
  | k+1 => a :: staircase (2*a) k

/-- A strict divisor is at most half the next part. The minimum sum at
each length is attained by just one chain, including the empty chain. -/
private theorem minimum_aux {a : ℕ} (l : List ℕ) (chain : Chain l)
    (low : ∀ z ∈ l, a ≤ z) :
    a*(2^l.length-1) ≤ l.sum ∧
    (l.sum=a*(2^l.length-1) → l=staircase a l.length) := by
  induction l generalizing a with
  | nil => simp [staircase]
  | cons d l ih =>
    obtain ⟨hd,ht⟩ := List.pairwise_cons.mp chain
    have ad := low d (by simp)
    have twice (z : ℕ) (hz : z ∈ l) : 2*d ≤ z := by
      obtain ⟨lt,m,hm⟩ := hd z hz
      have two : 2 ≤ m := by
        by_contra! h
        rcases (show m=0 ∨ m=1 by omega) with rfl|rfl <;> simp at hm <;> omega
      calc 2*d ≤ m*d := Nat.mul_le_mul_right d two
           _ = z := by rw [hm,mul_comm]
    obtain ⟨lower,unique⟩ := ih ht twice
    let T := 2^l.length-1
    have formula : 2^(l.length+1)-1=1+2*T := by
      dsimp [T]; rw [pow_succ]; have : 0 < 2^l.length := by positivity
      omega
    simp only [List.length_cons,List.sum_cons,formula]
    change (a*(1+2*T) ≤ d+l.sum) ∧ _
    have bound : d*(1+2*T) ≤ d+l.sum := by
      change 2*d*T ≤ l.sum at lower
      nlinarith only [lower]
    have al := Nat.mul_le_mul_right (1+2*T) ad
    refine ⟨al.trans bound,?_⟩
    intro eq
    have first : a=d := Nat.eq_of_mul_eq_mul_right (by omega : 0 < 1+2*T)
      (le_antisymm al (eq ▸ bound))
    subst d
    have ts : l.sum=2*a*(2^l.length-1) := by
      change a+l.sum=a*(1+2*T) at eq
      change l.sum=2*a*T
      nlinarith only [eq]
    exact congrArg (a :: ·) (unique ts)

theorem sharp_minimum (k : ℕ) :
    (∀ n l, IsPartition n k l → 2^k-1 ≤ n) ∧
    ∃! l, IsPartition (2^k-1) k l := by
  have geom := powers_valid k
  have exact_form {l : List ℕ} (h : IsPartition (2^k-1) k l) :
      l=staircase 1 k := by
    obtain ⟨s,len,positive,cc⟩ := h
    have eq := (minimum_aux (a:=1) l cc positive).2 (by simpa [len] using s)
    simpa [len] using eq
  refine ⟨?_,⟨powers k,geom,fun l h => (exact_form h).trans (exact_form geom).symm⟩⟩
  rintro n l ⟨s,len,positive,cc⟩
  simpa [len,s] using (minimum_aux (a:=1) l cc positive).1

end ChainPartition

theorem OMA.solution : type_of% @OMA.S_mo_315485.main := by
  refine ⟨?_,fun n k => ChainPartition.enum_card (by decide) k n,
    ChainPartition.eventual,ChainPartition.many,ChainPartition.sharp_minimum⟩
  intro n k l
  exact ChainPartition.enum_iff (by decide) k n l
