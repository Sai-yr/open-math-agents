import OMAStatements.S_oeis_a084013

/-!
# A fixed-length construction of palindromic multiples

For m coprime to the base, two of the first m+1 repunit remainders agree.
Cancel the common power of the base to obtain a divisible repunit using
at most m digits. Superposing two such strings of ones accommodates any
length at least m, with overlaps giving digits two.

For a remaining power c of two or five, build a short palindromic block
divisible by c, repeat it to absorb the coprime cofactor, and mirror it
across a central string of zeros. Finally restore the terminal zeros of
multipliers divisible by ten.
-/

namespace A084013Proof
open OMA.S_oeis_a084013 Finset

private def val (w : List ℕ) := Nat.ofDigits 10 w

private structure Pal (w : List ℕ) : Prop where
  mirror : w.reverse = w
  bounded : ∀ d ∈ w, d < 10
  first : w.head! ≠ 0

private theorem not_nil {w : List ℕ} (h : Pal w) : w ≠ [] := by
  rintro rfl; exact h.first rfl

private theorem canonical {w : List ℕ} (h : Pal w) : Nat.digits 10 (val w) = w := by
  apply Nat.digits_ofDigits 10 (by decide) _ h.bounded
  intro hn
  have last : w.getLast hn = w.head! := by
    calc
      _ = w.reverse.getLast (by simpa only [h.mirror] using hn) := by simp only [h.mirror]
      _ = w.head hn := List.getLast_reverse _
      _ = w.head! := by cases w with
        | nil => exact False.elim (hn rfl)
        | cons _ _ => rfl
  exact last ▸ h.first

private def has (n L : ℕ) := ∃ w : List ℕ, Pal w ∧ w.length=L ∧ n∣val w

private def rep (b n : ℕ) := ∑ i ∈ range n,b^i

private theorem rep_add (b i h : ℕ) : rep b (i+h)=rep b i+b^i*rep b h := by
  simp [rep,sum_range_add,pow_add,mul_sum]

private theorem rep_step (b h : ℕ) : rep b (h+1)=1+b*rep b h := by
  simpa [rep,Nat.add_comm 1 h] using rep_add b 1 h

private theorem short_rep {b m : ℕ} (hm : 0< m) (hc : m.Coprime b) :
    ∃ h : ℕ, 0<h ∧ h ≤ m ∧ m∣rep b h := by
  let f := fun j=>rep b j%m
  have maps : Set.MapsTo f (range (m+1)) (range m) := fun j _=>mem_range.mpr (Nat.mod_lt _ hm)
  obtain ⟨u,hu,v,hv,ne,eq⟩:=exists_ne_map_eq_of_card_lt_of_maps_to
    (show (range m).card < (range (m+1)).card by simp) maps
  have he : ∃ i j : ℕ, i < j ∧ j ≤ m ∧ rep b j ≡ rep b i [MOD m] := by
    rcases lt_or_gt_of_ne ne with h|h
    · exact ⟨u,v,h,by have := mem_range.mp hv; omega,eq.symm⟩
    · exact ⟨v,u,h,by have := mem_range.mp hu; omega,eq⟩
  obtain ⟨i,j,hij,hjm,hh⟩:=he
  refine ⟨j-i,by omega,by omega,?_⟩
  have hx := rep_add b i (j-i)
  rw [show i+(j-i)=j by omega] at hx
  rw [hx,Nat.add_comm,Nat.add_modEq_right_iff] at hh
  exact (hc.pow_right i).dvd_of_dvd_mul_left hh

private def copies (w : List ℕ) (h : ℕ) := (List.replicate h w).flatten

private theorem copies_succ (w : List ℕ) (h : ℕ) : copies w (h+1)=w++copies w h := by
  simp [copies,List.replicate_succ]

private theorem copies_len (w : List ℕ) (h : ℕ) : (copies w h).length=w.length*h := by
  induction h with
  | zero => simp [copies]
  | succ h ih => rw [copies_succ,List.length_append,ih,Nat.mul_succ]; omega

private theorem copies_val (w : List ℕ) (h : ℕ) : val (copies w h)=val w * rep (10^w.length) h := by
  induction h with
  | zero => simp [copies,val,rep]
  | succ h ih =>
    rw [copies_succ,show val (w++copies w h) = val w+10^w.length*val (copies w h) by
      exact Nat.ofDigits_append,ih,rep_step]
    ring

private theorem copies_pal {w : List ℕ} (hw : Pal w) {h : ℕ} (hh : 0<h) : Pal (copies w h) := by
  refine ⟨by simp [copies,List.reverse_flatten,hw.mirror],?_,?_⟩
  · intro d hd
    obtain ⟨v,hv,hd⟩ := List.mem_flatten.mp hd
    exact hw.bounded d (by simpa only [List.eq_of_mem_replicate hv] using hd)
  · obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hh.ne'
    rw [copies_succ,List.head!_append _ (not_nil hw)]
    exact hw.first

private theorem padded {n L : ℕ} {w : List ℕ} (hw : Pal w) (hd : n∣val w) (hl : 2*w.length ≤ L) :
    has n L := by
  let g:=L-2*w.length
  let z:=List.replicate g 0
  let P:=w++z++w
  have hp : Pal P := by
    refine ⟨by simp [P,z,List.reverse_append,hw.mirror,List.append_assoc],?_,?_⟩
    · intro d h
      simp only [P,List.mem_append] at h
      rcases h with (h|h)|h
      · exact hw.bounded _ h
      · have := List.eq_of_mem_replicate h; omega
      · exact hw.bounded _ h
    · rw [show P=w++(z++w) by simp [P],List.head!_append _ (not_nil hw)]
      exact hw.first
  refine ⟨P,hp,by simp [P,z,g]; omega,?_⟩
  have hval : val P=val w+10^(w.length+g)*val w := by
    simp [P,z,val,Nat.ofDigits_append,Nat.ofDigits_replicate_zero,pow_add,Nat.mul_assoc]
  rw [hval]; exact dvd_add hd (dvd_mul_of_dvd_right hd _)

end A084013Proof

namespace A084013Proof
open OMA.S_oeis_a084013

private theorem run_val (n d : ℕ) : val (List.replicate n d) = d*rep 10 n := by
  induction n with
  | zero => simp [val,rep]
  | succ n ih =>
    rw [List.replicate_succ,rep_step]
    change d+10*val (List.replicate n d)=_
    rw [ih]; ring

private theorem run_pal {n d : ℕ} (hn : 0<n) (hd : 0<d) (hb : d<10) :
    Pal (List.replicate n d) := by
  refine ⟨by simp,fun j hj=>by simpa only [List.eq_of_mem_replicate hj] using hb,?_⟩
  obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp [List.replicate_succ,hd.ne']

private theorem coprime_length {n L : ℕ} (hn : 0<n) (hL : n≤L) (hc : n.Coprime 10) : has n L := by
  obtain ⟨h,hpos,hm,hd⟩:=short_rep hn hc
  by_cases hgap : 2*h≤L
  · apply padded (w:=List.replicate h 1) (run_pal hpos (by decide) (by decide))
    · simpa only [run_val,one_mul] using hd
    · simpa using hgap
  let g:=L-h
  let u:=h-g
  have hg : g+u=h := by dsimp [g,u]; omega
  have hu : 0<u := by dsimp [g,u]; omega
  let outside:=List.replicate g 1
  let middle:=List.replicate u 2
  let w:=outside++middle++outside
  have hw : Pal w := by
    refine ⟨by simp [w,outside,middle,List.reverse_append,List.append_assoc],?_,?_⟩
    · intro d hd
      simp only [w,List.mem_append] at hd
      rcases hd with (h|h)|h <;> have := List.eq_of_mem_replicate h <;> omega
    · by_cases gz : g=0
      · simp only [w,outside,gz,List.replicate_zero,List.nil_append,List.append_nil]
        exact (run_pal hu (by decide) (by decide)).first
      · have ho := run_pal (Nat.pos_of_ne_zero gz) (by decide : 0<1) (by decide)
        rw [show w=outside++(middle++outside) by simp [w],List.head!_append _ (not_nil ho)]
        exact ho.first
  refine ⟨w,hw,by simp [w,outside,middle]; dsimp [g,u]; omega,?_⟩
  have e1 := rep_add 10 g u
  have e2 := rep_add 10 u g
  rw [hg] at e1; rw [Nat.add_comm u g,hg] at e2
  have valw : val w = rep 10 h + 10^g*rep 10 h := by
    change Nat.ofDigits 10 ((outside++middle)++outside)=_
    simp only [Nat.ofDigits_append,List.length_append,outside,middle,List.length_replicate]
    change (val (List.replicate g 1)+10^g*val (List.replicate u 2))+
      10^(g+u)*val (List.replicate g 1)=_
    simp only [run_val,one_mul,pow_add]
    linear_combination -e1 - 10^g*e2
  rw [valw]; exact dvd_add hd (dvd_mul_of_dvd_right hd _)

end A084013Proof

namespace A084013Proof
open OMA.S_oeis_a084013

private def short (c : ℕ) := ∃ w : List ℕ, Pal w ∧ c∣val w ∧ 2*w.length ≤ c

private theorem digit_block {c : ℕ} (hc : 2≤c) (hb : c<10) : short c := by
  refine ⟨[c],⟨by simp,by simpa using hb,by simpa using (show c≠0 by omega)⟩,?_,by simpa using hc⟩
  simp [val]

private theorem mirror_block {p e : ℕ} (h0 : 0<p) (hp10 : p<10) (hp : p∣10)
    (he : 0<e) (hbound : 4*e ≤ p^e) (h10 : ¬10∣p^e) : short (p^e) := by
  let c:=p^e
  let ds:=Nat.digits 10 c
  have cpos : 0<c := by dsimp [c]; positivity
  have dsne : ds≠[] := Nat.digits_ne_nil_iff_ne_zero.mpr cpos.ne'
  have dshead : ds.head!≠0 := by
    change (Nat.digits 10 c).head!≠0
    rw [Nat.head!_digits (by decide)]
    exact fun h=>h10 (Nat.dvd_of_mod_eq_zero h)
  have dlen : ds.length ≤ e := (Nat.digits_length_le_iff (by decide) c).mpr
    (Nat.pow_lt_pow_left hp10 he.ne')
  let low:=ds++List.replicate (e-ds.length) 0
  have llen : low.length=e := by simp [low]; omega
  have lne : low≠[] := by intro h; rw [h] at llen; simp at llen; omega
  have lhead : low.head!≠0 := by dsimp only [low]; rw [List.head!_append _ dsne]; exact dshead
  have lb (x : ℕ) (hx : x∈low) : x<10 := by
    rcases List.mem_append.mp hx with hx|hx
    · exact Nat.digits_lt_base (by decide) hx
    · have := List.eq_of_mem_replicate hx; omega
  let w:=low++low.reverse
  have hw : Pal w := by
    refine ⟨by simp [w,List.reverse_append],?_,?_⟩
    · intro d hd; rcases List.mem_append.mp hd with h|h
      · exact lb d h
      · exact lb d (List.mem_reverse.mp h)
    · dsimp only [w]; rw [List.head!_append _ lne]; exact lhead
  have eq : val low=c := by simp [low,val,ds,Nat.ofDigits_append_replicate_zero,Nat.ofDigits_digits]
  refine ⟨w,hw,?_,by simp [w,llen]; omega⟩
  rw [show val w=val low+10^low.length*val low.reverse by exact Nat.ofDigits_append]
  change c∣val low+10^low.length*val low.reverse
  rw [eq,llen]
  exact dvd_add dvd_rfl (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hp e) _)

private theorem four_pow {e : ℕ} (he : 4≤e) : 4*e ≤ 2^e := by
  induction e,he using Nat.le_induction with
  | base => decide
  | succ e he ih => rw [pow_succ]; omega

private theorem five_pow {e : ℕ} (he : 1≤e) : 4*e ≤ 5^e := by
  induction e,he using Nat.le_induction with
  | base => decide
  | succ e he ih => rw [pow_succ]; omega

private theorem short_factor {p e : ℕ} (hp : p=2 ∨ p=5) (he : 0<e) (h10 : ¬10 ∣ p^e) : short (p^e) := by
  rcases hp with rfl|rfl
  · by_cases h4 : 4≤e
    · exact mirror_block (by decide) (by decide) (by decide) he (four_pow h4) h10
    · interval_cases e <;> first | omega | apply digit_block <;> decide
  · exact mirror_block (by decide) (by decide) (by decide) he (five_pow he) h10

private theorem join_factors {c m L : ℕ} (hm : 0< m) (hL : c*m ≤ L) (small : short c) (cop : m.Coprime 10) :
    has (c*m) L := by
  obtain ⟨w,hw,hc,le⟩:=small
  obtain ⟨h,hp,hb,hd⟩:=short_rep hm (cop.pow_right w.length)
  apply padded (w:=copies w h) (copies_pal hw hp)
  · rw [copies_val]; exact Nat.mul_dvd_mul hc hd
  · rw [copies_len,←Nat.mul_assoc]
    exact (Nat.mul_le_mul le hb).trans hL

end A084013Proof

namespace A084013Proof
open OMA.S_oeis_a084013

private theorem ten_coprime {m : ℕ} (h2 : ¬2∣m) (h5 : ¬5∣m) : m.Coprime 10 := by
  rw [show 10=2*5 by decide,Nat.coprime_mul_iff_right]
  exact ⟨(Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm,
    ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h5).symm⟩

private theorem nondecimal {n L : ℕ} (hn : 0<n) (hL : n≤L) (hlast : ¬10∣n) : has n L := by
  have factor (p : ℕ) (hp : p=2 ∨ p=5) (hd : p∣n)
      (other : ∀ m, m∣n → ¬p∣m → m.Coprime 10) : has n L := by
    have pp : p≠1 := by omega
    obtain ⟨e,m,hm,eq⟩:=Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p pp
    have he : 0<e := by
      by_contra! hz
      have e0 : e=0 := by omega
      simp only [e0,pow_zero,one_mul] at eq
      exact hm (eq ▸ hd)
    have mp : 0 < m := by
      by_contra! hz
      have zm : m=0 := by omega
      rw [zm,Nat.mul_zero] at eq
      omega
    have dm : m∣n := eq ▸ dvd_mul_left _ _
    have dc : p^e∣n := eq ▸ dvd_mul_right _ _
    rw [eq] at hL ⊢
    exact join_factors mp hL (short_factor hp he (fun h=>hlast (h.trans dc))) (other m dm hm)
  by_cases h2 : 2∣n
  · have h5 : ¬5∣n := fun hd=>hlast ((by decide : Nat.Coprime 2 5).mul_dvd_of_dvd_of_dvd h2 hd)
    exact factor 2 (Or.inl rfl) h2 (fun m hm hnm=>ten_coprime hnm (fun h=>h5 (h.trans hm)))
  by_cases h5 : 5∣n
  · exact factor 5 (Or.inr rfl) h5 (fun m hm hnm=>ten_coprime (fun h=>h2 (h.trans hm)) hnm)
  exact coprime_length hn hL (ten_coprime h2 h5)

private theorem room (a m : ℕ) (hm : 0< m) : a+m ≤ 10^a*m := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h : 0<10^a*m := by positivity
    rw [pow_succ]
    nlinarith

private theorem drop_zeros {w : List ℕ} (hw : Pal w) (a : ℕ) :
    (List.replicate a 0 ++ w).dropWhile (· == 0) = w := by
  rw [List.dropWhile_append_of_pos (by intro d hd; simp [List.eq_of_mem_replicate hd])]
  cases w with
  | nil => rfl
  | cons d l =>
    have hd := hw.first
    change d≠0 at hd
    simp only [List.dropWhile_cons,show (d==0)=false from beq_eq_false_iff_ne.mpr hd,Bool.false_eq_true,if_false]

private theorem witness : ∀ n : ℕ, 0<n → ∃ x, qualifies n x := by
  intro n hn
  obtain ⟨a,m,hm,eq⟩:=Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 10 (by decide)
  have mp : 0 < m := by
    by_contra! hz
    have zm : m=0 := by omega
    rw [zm,Nat.mul_zero] at eq
    omega
  have le : a+m≤n := by rw [eq]; exact room _ _ mp
  obtain ⟨w,hw,len,div⟩:=nondecimal (L:=n-a) mp (by omega) hm
  have hd := canonical hw
  have wp : 0<val w := Nat.pos_of_ne_zero (Nat.digits_ne_nil_iff_ne_zero.mp (hd ▸ not_nil hw))
  refine ⟨10^a*val w,by positivity,?_,?_,?_⟩
  · rw [eq]; exact Nat.mul_dvd_mul_left _ div
  · rw [Nat.digits_base_pow_mul (by decide) wp,hd,List.length_append,List.length_replicate,len]
    omega
  · rw [Nat.digits_base_pow_mul (by decide) wp,hd]
    split_ifs with nd
    · simpa only [drop_zeros hw] using hw.mirror
    · have az : a=0 := by
        by_contra hp
        have had : 10∣10^a := dvd_pow_self 10 hp
        exact nd (eq ▸ dvd_mul_of_dvd_left had m)
      simpa [az] using hw.mirror

private theorem solved : ∀ n : ℕ, 0 < n → a n ≠ 0 := by
  intro n hn
  classical
  have h := witness n hn
  rw [a,dif_pos h]
  exact (Nat.find_spec h).1.ne'

end A084013Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a084013.main :=
  A084013Proof.solved
