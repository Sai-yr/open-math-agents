import OMAReductions.R_Erdos242_erdos_242_R1_H1_R1_H1_R1_H1_R1

/-!
For x=(p+11)/4, two divisor residues d,e can give a three-term expansion
via d+e=0 or pd+e=0 modulo 11. Starting with 3 and a factor of nonsquare
residue, the five lists in `small` exhaust the noncolliding states of the
first test. The second test resolves two states. All finite transition and
witness checks use the Lean kernel.
-/

namespace ElevenDivisors

abbrev R := ZMod 11

def residues : List R → List R
  | [] => [1]
  | a :: s => residues s ++ (residues s).map (a * ·)

def step (a : R) (s : List R) : List R := if a = 1 then s else a::s

def small : List (List R) := [[2,3],[3,6],[2,2,3],[2,3,6],[3,6,6]]

def nonsquares : List R := [2,6,7,8,10]

def hit (p : R) (s : List R) : Prop :=
  ∃ d ∈ residues s, ∃ e ∈ residues s, d+e=0 ∨ p*d+e=0

def carried (a : R) (s v : List R) : Prop :=
  (step a s).Perm v ∧ v.prod = a*s.prod ∧ ∀ r ∈ residues v, r ∈ residues (a::s)

private theorem finite_step (w : List R) (hw : w ∈ small) (a : R) (ha : a ≠ 0) :
    hit 1 (a::w) ∨ ∃ v ∈ small, carried a w v := by
  have check : ∀ w ∈ small, ∀ a : R, a ≠ 0 →
      ((∃ d ∈ residues (a::w), ∃ e ∈ residues (a::w), d+e=0 ∨ 1*d+e=0) ∨
        ∃ v ∈ small, (step a w).Perm v ∧ v.prod = a*w.prod ∧
          ∀ r ∈ residues v, r ∈ residues (a::w)) := by decide +kernel
  exact check w hw a ha

private theorem seed_step (a : R) (ha : a ∈ nonsquares) :
    hit 1 [a,3] ∨ ∃ v ∈ small, carried a [3] v := by
  have check : ∀ a ∈ nonsquares,
      ((∃ d ∈ residues [a,3], ∃ e ∈ residues [a,3], d+e=0 ∨ 1*d+e=0) ∨
        ∃ v ∈ small, (step a [3]).Perm v ∧ v.prod = a*([3] : List R).prod ∧
          ∀ r ∈ residues v, r ∈ residues [a,3]) := by decide +kernel
  exact check a ha

theorem finish_states (s : List R) (hs : s ∈ small) :
    (s.Perm [2,3] ∨ s.Perm [3,6] ∨ s.Perm [2,3,6]) ∨ hit (4*s.prod) s := by
  have check : ∀ s ∈ small, (s.Perm [2,3] ∨ s.Perm [3,6] ∨ s.Perm [2,3,6]) ∨
    (∃ d ∈ residues s, ∃ e ∈ residues s, d+e=0 ∨ 4*s.prod*d+e=0) := by decide +kernel
  exact check s hs

def labels (l : List ℕ) : List R := (l.map (fun (n : ℕ) => (n : R))).filter (· != 1)

def realized (s : List R) (x : ℕ) : Prop := ∀ r ∈ residues s, ∃ d : ℕ, d ∣ x ∧ (d : R) = r

def collision (p : R) (x : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ x ∧ ∃ e : ℕ, e ∣ x ∧ ((d : R)+e=0 ∨ p*d+e=0)

private theorem propagate {q x : ℕ} {w : List R} (h : realized w x) :
    realized ((q : R)::w) (q*x) := by
  intro r hr
  rcases List.mem_append.mp hr with hold|hnew
  · obtain ⟨d,hd,he⟩ := h r hold
    exact ⟨d,hd.trans (dvd_mul_left _ _),he⟩
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hnew
    obtain ⟨d,hd,he⟩ := h b hb
    exact ⟨q*d,Nat.mul_dvd_mul_left _ hd,by push_cast; rw [he]⟩

def good (p : R) (l : List ℕ) : Prop :=
  collision p l.prod ∨ ∃ w ∈ small, (labels l).Perm w ∧ w.prod=(l.prod : R) ∧ realized w l.prod

theorem realize_hit {p : R} {l : List R} {x : ℕ} (h : hit p l) (rep : realized l x) : collision p x := by
  obtain ⟨d,hd,e,he,H⟩ := h
  obtain ⟨d',hd',rfl⟩ := rep d hd
  obtain ⟨e',he',rfl⟩ := rep e he
  exact ⟨d',hd',e',he',H⟩

private theorem seed_hit {s : List R} {x : ℕ} (p : R) (h : hit 1 s) (hr : realized s x) :
    collision p x := by
  obtain ⟨d,hd,e,he,h⟩ := realize_hit h hr
  exact ⟨d,hd,e,he,Or.inl (by simpa using h)⟩

private theorem safe_prepend (p : R) (q : ℕ) (l : List ℕ) (w : List R)
    (perm : (labels l).Perm w) (eq : w.prod=(l.prod : R)) (rep : realized w l.prod)
    (branch : hit 1 ((q:R)::w) ∨ ∃ v ∈ small, carried q w v) : good p (q::l) := by
  have more := propagate (q:=q) rep
  rcases branch with h|⟨v,hv,hperm,hprod,hrep⟩
  · exact Or.inl (seed_hit p h more)
  · right
    refine ⟨v,hv,?_,by simp [hprod,eq],fun r hr => more r (hrep r hr)⟩
    apply List.Perm.trans _ hperm
    by_cases h : (q : R)=1
    · simpa [labels,step,h] using perm
    · simpa [labels,step,h] using perm.cons (q : R)

private theorem grow (p : R) (l b : List ℕ) (start : good p b) (unit : ((l++b).prod : R) ≠ 0) :
    good p (l++b) := by
  induction l with
  | nil => simpa using start
  | cons q l ih =>
    simp only [List.cons_append,List.prod_cons,Nat.cast_mul] at unit ⊢
    have nq : (q : R) ≠ 0 := fun eq => unit (by rw [eq]; simp)
    have nl : ((l++b).prod : R) ≠ 0 := fun eq => unit (by rw [eq]; simp)
    rcases ih nl with ⟨d,hd,e,he,H⟩|⟨w,hw,perm,eq,rep⟩
    · exact Or.inl ⟨d,hd.trans (dvd_mul_left ..),e,he.trans (dvd_mul_left ..),H⟩
    · exact safe_prepend p q _ w perm eq rep (finite_step w hw q nq)

theorem seeded (p : R) (l : List ℕ) (q : ℕ) (qn : (q : R) ∈ nonsquares)
    (unit : ((l++[q,3]).prod : R) ≠ 0) : good p (l++[q,3]) := by
  apply grow p l [q,3] _ unit
  apply safe_prepend p q [3] [3] (by decide) (by decide) _ (seed_step _ qn)
  intro r hr
  simp [residues] at hr
  rcases hr with rfl|rfl
  · exact ⟨1,by decide,by decide⟩
  · exact ⟨3,by decide,by decide⟩

end ElevenDivisors

namespace ElevenDivisors

def expansion (p : ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4/p : ℚ) = 1/x+1/y+1/z

private theorem order_tail {p x y z : ℕ} (hx : 0 < x) (hy : x < y) (hz : x < z) (h : y ≠ z)
    (eqn : (4/p : ℚ) = 1/x + 1/y + 1/z) : expansion p := by
  rcases lt_or_gt_of_ne h with hlt|hgt
  · exact ⟨x,y,z,hx,hy,hlt,eqn⟩
  · exact ⟨x,z,y,hx,hz,hgt,by rw [eqn]; ring⟩

private theorem frac {d u x t : ℕ} (hu : 0 < u) (hx : 0 < x) (ht : 0 < t)
    (du : d*u=x) : (1 : ℚ) / (t*u : ℕ) = (d : ℚ)/(t*x : ℕ) := by
  have eqn : (d:ℚ)*u=x := by exact_mod_cast du
  push_cast
  field_simp
  nlinarith

theorem from_collision {p x d e : ℕ} (hp : 11 < p) (rel : p+11=4*x)
    (unit : (x : ZMod 11) ≠ 0) (hd : d ∣ x) (he : e ∣ x)
    (hit : (d : ZMod 11)+e=0 ∨ (p : ZMod 11)*d+e=0) : expansion p := by
  have hx : 0<x := by omega
  have xp : x < p := by omega
  have dp := Nat.pos_of_dvd_of_pos hd hx
  have ep := Nat.pos_of_dvd_of_pos he hx
  have ele := Nat.le_of_dvd hx he
  obtain ⟨u,du⟩ := hd
  obtain ⟨v,ev⟩ := he
  have up : 0<u := by by_contra! false; simp [(by omega : u=0)] at du; omega
  have vp : 0<v := by by_contra! false; simp [(by omega : v=0)] at ev; omega
  have rQ : (p:ℚ)+11=4*x := by exact_mod_cast rel
  have p0 : 0 < p := by omega
  rcases hit with h|h
  · have cast0 : ((d+e : ℕ) : ZMod 11) = 0 := by push_cast; exact h
    obtain ⟨t,dt⟩ := (ZMod.natCast_eq_zero_iff _ _).mp cast0
    have tp : 0<t := by omega
    have tQ : (d:ℚ)+e=11*t := by exact_mod_cast dt
    have ne : d ≠ e := by
      rintro rfl
      have nz : (d : ZMod 11) ≠ 0 := fun a => unit (by simp [du,a])
      have test : ∀ a : ZMod 11, a+a=0 → a=0 := by decide
      exact nz (test _ h)
    have uv : u ≠ v := by rintro rfl; exact ne (Nat.eq_of_mul_eq_mul_right up (du.symm.trans ev))
    have yb : x < p*t*u := by nlinarith [Nat.le_mul_of_pos_right p tp, Nat.le_mul_of_pos_right (p*t) up]
    have zb : x < p*t*v := by nlinarith [Nat.le_mul_of_pos_right p tp, Nat.le_mul_of_pos_right (p*t) vp]
    apply order_tail hx yb zb (fun eq => uv (Nat.eq_of_mul_eq_mul_left (by positivity) eq))
    rw [frac up hx (Nat.mul_pos p0 tp) du.symm, frac vp hx (Nat.mul_pos p0 tp) ev.symm]
    push_cast
    field_simp
    nlinarith [congrArg (fun a : ℚ => a*t) rQ]
  · have cast0 : ((p*d+e : ℕ) : ZMod 11)=0 := by push_cast; exact h
    obtain ⟨t,dt⟩ := (ZMod.natCast_eq_zero_iff _ _).mp cast0
    have tp : 0<t := by nlinarith
    have tQ : (p:ℚ)*d+e=11*t := by exact_mod_cast dt
    have dlt : d < t := by nlinarith [Nat.mul_lt_mul_of_pos_right hp dp]
    have xy : x < t*u := du ▸ Nat.mul_lt_mul_of_pos_right dlt up
    have epd : e < p*d := ele.trans_lt (xp.trans_le (Nat.le_mul_of_pos_right p dp))
    have upv : u < p*v := by
      apply (Nat.mul_lt_mul_left dp).mp
      nlinarith [Nat.mul_lt_mul_of_pos_right epd vp]
    have yz : t*u < p*t*v := by
      simpa [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using Nat.mul_lt_mul_of_pos_left upv tp
    refine ⟨x,t*u,p*t*v,hx,xy,yz,?_⟩
    rw [frac up hx tp du.symm,frac vp hx (Nat.mul_pos p0 tp) ev.symm]
    push_cast
    field_simp
    nlinarith [congrArg (fun a : ℚ => a*t) rQ]

end ElevenDivisors

namespace ElevenDivisors

theorem covered : OMA.R_Erdos242_erdos_242_R1_H1_R1_H1_R1_H1_R1.H1 := by
  intro p hp h12 nonzero r nr excluded
  let x := (p+11)/4
  let l := x.primeFactorsList
  have relation : p+11=4*x := by dsimp [x]; omega
  have positive : 0 < x := by omega
  have factors : l.prod = x := Nat.prod_primeFactorsList positive.ne'
  have prodrel : (4 : R)*x=p := by
    have h := congrArg (fun n : ℕ => (n : R)) relation
    simp only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_mul] at h
    simpa only [show (11 : R)=0 by decide,add_zero] using h.symm
  have unit : (x : R) ≠ 0 := by
    intro z
    rw [z,mul_zero] at prodrel
    exact nonzero (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp prodrel.symm))
  have h3 : 3 ∈ l := (Nat.mem_primeFactorsList positive.ne').mpr ⟨Nat.prime_three,by omega⟩
  obtain ⟨a,ha,hn⟩ := nr
  have occurs : a ∈ l.map (fun n : ℕ => (n : R)) := (List.mem_filter.mp ha).1
  obtain ⟨q,hq,eq⟩ := List.mem_map.mp occurs
  have qn : (q : R) ∈ nonsquares := eq ▸ hn
  have nq : q ≠ 3 := by
    rintro rfl
    exact (by decide : (3 : R) ∉ nonsquares) qn
  let rest := (l.erase q).erase 3
  have eh : 3 ∈ l.erase q := (List.mem_erase_of_ne nq.symm).mpr h3
  have reordered : l.Perm (rest++[q,3]) := by
    apply (List.perm_cons_erase hq).trans
    apply (List.Perm.cons q (List.perm_cons_erase eh)).trans
    exact (List.perm_append_comm (l₁:=[q,3]) (l₂:=rest))
  have prod : (rest++[q,3]).prod = x := reordered.prod_eq.symm.trans factors
  have lbl : r.Perm (labels (rest++[q,3])) :=
    (reordered.map (fun n : ℕ => (n : R))).filter (· != 1)
  rcases seeded p rest q qn (by rwa [prod]) with col|⟨s,hs,per,pr,rep⟩
  · rw [prod] at col
    obtain ⟨d,hd,e,he,hit⟩ := col
    exact from_collision hp relation unit hd he hit
  · rw [prod] at pr rep
    rcases finish_states s hs with ex|hit
    · apply False.elim ∘ excluded
      rcases ex with h|h|h
      · exact Or.inl (lbl.trans (per.trans h))
      · exact Or.inr (Or.inl (lbl.trans (per.trans h)))
      · exact Or.inr (Or.inr (lbl.trans (per.trans h)))
    · rw [pr,prodrel] at hit
      obtain ⟨d,hd,e,he,H⟩ := realize_hit hit rep
      exact from_collision hp relation unit hd he H

end ElevenDivisors

theorem OMA.solution : OMA.R_Erdos242_erdos_242_R1_H1_R1_H1_R1_H1_R1.H1 :=
  ElevenDivisors.covered
