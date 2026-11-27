import OMAReductions.R_mo_264127_R1

open OMA.S_mo_264127

private def K {V : Type} (P : V→Prop) (a b : V) := a≠b ∧ P a ∧ P b

private lemma one {V : Type} {R : V→V→Prop} (irr : ∀ a, ¬R a a) {P : V→Prop}
    {x y : V} (px : P x) (py : P y) (w : Fin 1→V×V) (hw : hit R x y 1 w) :
    hit (K P) x y 1 w := by
  rcases hw with h|⟨a,e,b⟩
  · exact Or.inl h
  · change (w 0).2=y at b
    exact Or.inr ⟨a,⟨fun eq => irr _ (eq ▸ e),a ▸ px,b ▸ py⟩,b⟩

private lemma two {V : Type} {R : V→V→Prop} (irr : ∀ a, ¬R a a) {P : V→Prop}
    {x y : V} (px : P x) (py : P y) (mid : ∀ z, R x z → R z y → P z)
    (w : Fin 2→V×V) (hw : hit R x y 2 w) : hit (K P) x y 2 w := by
  rcases hw with h|⟨a,e,b⟩
  · exact Or.inl (one irr px py _ h)
  · have pb : P (w 0).2 := by
      rcases b with h|⟨u,rs,v⟩
      · change (w 0).2=y at h
        exact h ▸ py
      · change ((Fin.tail w) 0).2=y at v
        exact mid _ (a ▸ e) (u ▸ v ▸ rs)
    exact Or.inr ⟨a,⟨fun eq => irr _ (eq ▸ e),a ▸ px,pb⟩,one irr pb py _ b⟩

private lemma three {V : Type} {R : V→V→Prop} (irr : ∀ a, ¬R a a) {P : V→Prop}
    {x y : V} (px : P x) (py : P y) (left : ∀ z, R x z → P z)
    (right : ∀ z, R z y → P z) (w : Fin 3→V×V) (hw : hit R x y 3 w) :
    hit (K P) x y 3 w := by
  rcases hw with h|⟨a,e,b⟩
  · exact Or.inl (two irr px py (fun z l _ => left z l) _ h)
  · have pb := left _ (a ▸ e)
    exact Or.inr ⟨a,⟨fun eq => irr _ (eq ▸ e),a ▸ px,pb⟩,
      two irr pb py (fun z _ r => right z r) _ b⟩

private lemma equal_hits {V : Type} {R : V→V→Prop} (irr : ∀ a, ¬R a a) {P : V→Prop}
    (closed : ∀ x, P x → ∀ y, R x y → P y)
    (complete : ∀ x, P x → ∀ y, P y → x≠y → R x y) {x y : V}
    (px : P x) (k : ℕ) (w : Fin k → V×V) : hit R x y k w ↔ hit (K P) x y k w := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [hit, ih px]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨a,e,b⟩
      have pa := a ▸ px
      have pb := closed _ pa _ e
      exact ⟨a,⟨fun eq => irr _ (eq ▸ e),pa,pb⟩,(ih pb _).mp b⟩
    · rintro ⟨a,e,b⟩
      exact ⟨a,complete _ e.2.1 _ e.2.2 e.1,(ih e.2.2 _).mpr b⟩

private lemma cs_le {V : Type} [Fintype V] {R C : V→V→Prop} {i j : V} {k : ℕ}
    (sub : ∀ w, hit R i j k w → hit C i j k w) : successes R i j k≤successes C i j k := by
  classical
  unfold successes
  apply Finset.card_le_card
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,sub w (Finset.mem_filter.mp hw).2⟩

private lemma cs_lt {V : Type} [Fintype V] {R C : V→V→Prop} {i j : V} {k : ℕ}
    (sub : ∀ w, hit R i j k w → hit C i j k w)
    (w : Fin k→V×V) (w1 : hit C i j k w) (w0 : ¬hit R i j k w) :
    successes R i j k<successes C i j k := by
  classical
  unfold successes
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset ?_).mpr
  · exact ⟨w,by simp [w1],by simp [w0]⟩
  · intro v hv; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,sub v (Finset.mem_filter.mp hv).2⟩

private lemma cs_upper {V : Type} [Fintype V] (R : V→V→Prop) (i j : V) (k : ℕ) :
    successes R i j k ≤ (Fintype.card V ^ 2)^k := by
  classical
  unfold successes
  simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_prod,Fintype.card_fin,pow_two] using
    (Finset.card_filter_le (s:=Finset.univ) (p:=fun w=>hit R i j k w))

private lemma missing_two {V : Type} {R : V→V→Prop} {P : V→Prop} {i u j : V}
    (pi : P i) (pu : P u) (pj : P j) (ij : i≠j) (iu : i≠u) (uj : u≠j)
    (bad : ¬ R u j) : ∃ w : Fin 2→V×V, hit (K P) i j 2 w ∧ ¬hit R i j 2 w := by
  refine ⟨![(i,u),(u,j)],?_⟩
  simp [hit,Fin.tail,K, *]

private lemma missing_three {V : Type} {R : V→V→Prop} {P : V→Prop} {i u v j : V}
    (pi : P i) (pu : P u) (pv : P v) (pj : P j) (ij : i≠j) (iu : i≠u)
    (iv : i≠v) (uj : u≠j) (vj : v≠j) (uv : u≠v) (bad : ¬ R u v) :
    ∃ w : Fin 3→V×V, hit (K P) i j 3 w ∧ ¬hit R i j 3 w := by
  refine ⟨![(i,u),(u,v),(v,j)],?_⟩
  simp [hit,Fin.tail,K, *]

private lemma classification {V : Type} [Fintype V] {R : V→V→Prop} (i j : V)
    (irr : ∀ x, ¬R x x) (sym : ∀ {x y}, R x y → R y x) (adj : R i j)
    (P : V→Prop) (pin : ∀ x, P x ↔ x=i ∨ R i x)
    (sat : ∀ x, P x → (∀ y, P y → x≠y → R x y) → ∀ y, R x y → P y) :
    (∀ k, successes R i j k=successes (K P) i j k) ∨
    ∃ m : ℕ, m≤3 ∧ (∀ k<m, successes R i j k≤successes (K P) i j k) ∧
      successes R i j m<successes (K P) i j m := by
  classical
  have pi := (pin i).mpr (Or.inl rfl)
  have pj := (pin j).mpr (Or.inr adj)
  have ij : i≠j := fun e => irr _ (e ▸ adj)
  have left (z) (hz : R i z) := (pin z).mpr (Or.inr hz)
  have at2 := two irr pi pj (fun z a _ => left z a)
  have init (k : ℕ) (hk : k≤2) : successes R i j k≤successes (K P) i j k := by
    interval_cases k
    · exact cs_le (fun _ h => h)
    · exact cs_le (one irr pi pj)
    · exact cs_le at2
  by_cases jfull : ∀ y, P y → j≠y → R j y
  · have right (z) (hz : R z j) := sat j pj jfull z (sym hz)
    by_cases all : ∀ x, P x → ∀ y, P y → x≠y → R x y
    · left; intro k
      exact le_antisymm (cs_le (fun w => (equal_hits irr (fun x h => sat x h (all x h)) all pi k w).mp))
        (cs_le (fun w => (equal_hits irr (fun x h => sat x h (all x h)) all pi k w).mpr))
    · push Not at all
      obtain ⟨u,pu,v,pv,uv,bad⟩ := all
      have iu : i≠u := by rintro rfl; exact ((pin v).mp pv).elim (fun h => uv h.symm) bad
      have iv : i≠v := by rintro rfl; exact ((pin u).mp pu).elim uv (fun h => bad (sym h))
      have uj : u≠j := by rintro rfl; exact bad (jfull _ pv uv)
      have vj : v≠j := by rintro rfl; exact bad (sym (jfull _ pu uv.symm))
      obtain ⟨w,hw,miss⟩ := missing_three pi pu pv pj ij iu iv uj vj uv bad
      exact Or.inr ⟨3,le_rfl,fun k hk=>init k (by omega),cs_lt (three irr pi pj left right) w hw miss⟩
  · push Not at jfull
    obtain ⟨u,pu,ju,bad⟩ := jfull
    have iu : i≠u := by rintro rfl; exact bad (sym adj)
    obtain ⟨w,hw,miss⟩ := missing_two pi pu pj ij iu ju.symm (fun h => bad (sym h))
    exact Or.inr ⟨2,by decide,fun k hk=>init k (by omega),cs_lt at2 w hw miss⟩

private lemma saturation {V : Type} (G : SimpleGraph V) [G.LocallyFinite]
    {d : ℕ} (reg : G.IsRegularOfDegree d) (S : Finset V) (i : S)
    (inside : ∀ v, G.Adj i.val v → v∈S) :
    let P : S→Prop := fun u => u=i ∨ G.Adj i.val u.val
    ∀ x, P x → (∀ y, P y → x≠y → G.Adj x.val y.val) → ∀ y, G.Adj x.val y.val → P y := by
  classical
  let B := insert i.val (G.neighborFinset i.val)
  have spec (x : S) : x.val∈B ↔ x=i ∨ G.Adj i.val x.val := by
    change x.val ∈ insert i.val (G.neighborFinset i.val) ↔ _
    rw [Finset.mem_insert,G.mem_neighborFinset]
    exact or_congr Subtype.val_inj Iff.rfl
  have sub : B⊆S := by
    intro v hv
    rcases Finset.mem_insert.mp hv with h|h
    · exact h ▸ i.property
    · exact inside _ ((G.mem_neighborFinset ..).mp h)
  intro P x px all y edge
  have hB : B.card=d+1 := by
    dsimp only [B]
    rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self _),G.card_neighborFinset_eq_degree,reg]
  have inc : B.erase x.val ⊆ G.neighborFinset x.val := by
    intro b hb
    obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hb
    exact (G.mem_neighborFinset ..).mpr (all ⟨b,sub mem⟩ ((spec _).mp mem) (fun e => ne (congrArg Subtype.val e).symm))
  have eq := Finset.eq_of_subset_of_card_le inc (by
    rw [G.card_neighborFinset_eq_degree,reg,Finset.card_erase_of_mem ((spec _).mpr px),hB]; omega)
  apply (spec _).mp
  exact Finset.mem_of_mem_erase (eq ▸ (G.mem_neighborFinset ..).mpr edge)

private lemma short_series {a b : ℕ→ℕ} {M t : ℝ} (hM : 0≤M) (ht : 0≤t)
    (ha : ∀ k, (a k:ℝ)≤M^k) (hb : ∀ k, (b k:ℝ)≤M^k)
    {m : ℕ} (hm : m≤3) (before : ∀ k<m, a k≤b k) (gap : a m<b m)
    (hsmall : 24*(M+1)^4*t≤1) :
    (∑' k : ℕ, (a k:ℝ)*t^k/(k.factorial:ℝ)) ≤
      ∑' k : ℕ, (b k:ℝ)*t^k/(k.factorial:ℝ) := by
  let A := fun k : ℕ => (a k:ℝ)*t^k/(k.factorial:ℝ)
  let B := fun k : ℕ => (b k:ℝ)*t^k/(k.factorial:ℝ)
  let r := M*t
  have r0 : 0≤r := mul_nonneg hM ht
  have base : 1≤M+1 := by linarith
  have p4 : (M+1)^1≤(M+1)^4 := pow_le_pow_right₀ base (by decide)
  have rsmall : r≤1/2 := by
    dsimp only [r]
    nlinarith only [hsmall,mul_le_mul_of_nonneg_right p4 ht,ht]
  have r1 : r<1 := by linarith
  have series := summable_geometric_of_lt_one r0 r1
  have bound (f : ℕ→ℕ) (h : ∀ k, (f k:ℝ)≤M^k) (k : ℕ) :
      (f k:ℝ)*t^k/(k.factorial:ℝ)≤r^k := by
    calc
      _ ≤ (f k:ℝ)*t^k := div_le_self (by positivity) (by exact_mod_cast Nat.factorial_pos k)
      _ ≤ M^k*t^k := mul_le_mul_of_nonneg_right (h k) (pow_nonneg ht k)
      _ = _ := (mul_pow M t k).symm
  have sumA : Summable A := series.of_nonneg_of_le (fun k => by dsimp [A]; positivity) (bound a ha)
  have sumB : Summable B := series.of_nonneg_of_le (fun k => by dsimp [B]; positivity) (bound b hb)
  have smallPower : M^(m+1)≤(M+1)^4 := by
    calc
      _ ≤ (M+1)^(m+1) := by gcongr; linarith
      _ ≤ (M+1)^4 := pow_le_pow_right₀ base (by omega)
  have fac : (m.factorial:ℝ)≤6 := by exact_mod_cast Nat.factorial_le hm
  have key : 2*M^(m+1)*t*(m.factorial:ℝ)≤1 := by
    have h1 := mul_le_mul_of_nonneg_right smallPower ht
    have h2 := mul_le_mul_of_nonneg_left fac (show 0≤M^(m+1)*t by positivity)
    nlinarith only [h1,h2,hsmall,show 0≤(M+1)^4*t by positivity]
  have tail : (∑' k : ℕ, A (k+(m+1))) ≤ t^m/(m.factorial:ℝ) := by
    calc
      _ ≤ ∑' k : ℕ, r^k*r^(m+1) := by
        apply Summable.tsum_le_tsum _ (sumA.comp_injective (add_left_injective (m+1))) (series.mul_right _)
        intro k
        simpa only [Function.comp_apply,A,←pow_add] using bound a ha (k+(m+1))
      _ = (1-r)⁻¹*r^(m+1) := by rw [tsum_mul_right,tsum_geometric_of_lt_one r0 r1]
      _ ≤ 2*r^(m+1) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg r0 _)
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      _ ≤ _ := by
        apply (le_div_iff₀ (by positivity)).mpr
        dsimp only [r]; rw [mul_pow,pow_succ t m]
        nlinarith only [mul_le_mul_of_nonneg_right key (pow_nonneg ht m)]
  have heads : ∑ k ∈ Finset.range m, A k ≤ ∑ k ∈ Finset.range m, B k := by
    apply Finset.sum_le_sum
    intro k hk
    have h : (a k:ℝ)≤b k := by exact_mod_cast before k (Finset.mem_range.mp hk)
    dsimp [A,B]; gcongr
  have win : A m+t^m/(m.factorial:ℝ) ≤ B m := by
    have h : (a m:ℝ)+1≤b m := by exact_mod_cast gap
    dsimp only [A,B]; rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_right h (pow_nonneg ht m)]
  have posTail : 0 ≤ ∑' k : ℕ, B (k+(m+1)) := tsum_nonneg (fun k => by dsimp [B]; positivity)
  change (∑' k, A k)≤∑' k, B k
  rw [← sumA.sum_add_tsum_nat_add (m+1),← sumB.sum_add_tsum_nat_add (m+1),
    Finset.sum_range_succ,Finset.sum_range_succ]
  linarith

theorem OMA.solution : OMA.R_mo_264127_R1.H1 := by
  classical
  intro V G lf d reg S i j edge inside t ht small
  let R : S→S→Prop := fun x y => G.Adj x.val y.val
  let P : S→Prop := fun x => x=i ∨ R i x
  obtain eq|⟨m,hm,before,gap⟩ := classification i j (R:=R) (fun x=>G.loopless.irrefl x.val)
    (fun e=>G.adj_symm e) edge P (fun _ => Iff.rfl) (saturation G reg S i inside)
  · change prob R i j t ≤ prob (K P) i j t
    simp only [prob,eq,le_refl]
  · change prob R i j t ≤ prob (K P) i j t
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply short_series (M:=(S.card:ℝ)^2) (by positivity) ht _ _ hm before gap small
    · intro k; exact_mod_cast (by simpa only [Fintype.card_coe] using cs_upper R i j k)
    · intro k; exact_mod_cast (by simpa only [Fintype.card_coe] using cs_upper (K P) i j k)
