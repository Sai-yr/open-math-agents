import OMAStatements.S_mo_279044

/-!
# Weighted comparison of left and right resolvents

For positive semidefinite blocks Cᵢ and their positive definite sum G, the
kernel Re tr(G⁻¹ Cᵢ G⁻¹ Cⱼ) is symmetric and nonnegative. Its row sums
give the block contributions Re tr(G⁻¹ Cᵢ). Exponential scaling of the
blocks therefore increases every comonotone weighted sum of their
contributions. Applying this to the rows of the graph of R B and then
passing to the limit at singular B gives the result for all dimensions.
-/

namespace Resolvent
open Matrix Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
abbrev Mat (n : Type*) := Matrix n n ℂ
def tr (X : Mat n) : ℝ := X.trace.re
omit [DecidableEq n] in
lemma tr_swap (A B : Mat n) : tr (A*B)=tr (B*A) := congrArg Complex.re (trace_mul_comm ..)
omit [DecidableEq n] in
lemma tr_smul (a : ℝ) (A : Mat n) : tr (a • A)=a * tr A := by simp [tr,Matrix.trace_smul,Complex.real_smul]
omit [DecidableEq n] in
lemma tr_sum {ι : Type*} [Fintype ι] (A : ι → Mat n) : tr (∑ i, A i)=∑ i, tr (A i) := by simp [tr,Matrix.trace_sum]
lemma tr_pos {A B : Mat n} (ha : A.PosSemidef) (hb : B.PosSemidef) : 0 ≤ tr (A*B) := by
  obtain ⟨C,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha.nonneg
  have e : tr (star C*C*B)=tr (C*B*Cᴴ) := by rw [mul_assoc,tr_swap]; rfl
  rw [e]; exact (RCLike.nonneg_iff.mp (hb.mul_mul_conjTranspose_same C).trace_nonneg).1
lemma inv_left {A : Mat n} (u : IsUnit A) : A⁻¹*A=1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp u)
lemma inv_right {A : Mat n} (u : IsUnit A) : A*A⁻¹=1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp u)
lemma inv_deriv {g : ℝ → Mat n} {v : Mat n} {t : ℝ} (hg : HasDerivAt g v t) (hu : IsUnit (g t)) :
    HasDerivAt (fun y => (g y)⁻¹) (-(g t)⁻¹*v*(g t)⁻¹) t := by
  have e : HasFDerivAt Ring.inverse (-(ContinuousLinearMap.mulLeftRight ℝ (Mat n) (g t)⁻¹ (g t)⁻¹)) (g t) := by
    obtain ⟨u,eu⟩ := hu
    rw [←eu,Matrix.nonsing_inv_eq_ringInverse,Ring.inverse_unit]
    exact hasFDerivAt_ringInverse _
  simpa [Matrix.nonsing_inv_eq_ringInverse,Function.comp_def,ContinuousLinearMap.mulLeftRight_apply] using e.comp_hasDerivAt t hg
lemma tr_deriv {g : ℝ → Mat n} {v : Mat n} {t : ℝ} (hg : HasDerivAt g v t) :
    HasDerivAt (fun y => tr (g y)) (tr v) t := by
  let L := Complex.reCLM.comp (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap n ℝ ℂ))
  exact L.hasFDerivAt.comp_hasDerivAt t hg
variable {ι : Type*} [Fintype ι]
def kernel (Z : Mat n) (C : ι → Mat n) (i j : ι) := tr ((Z*C i)*(Z*C j))
omit [Fintype ι] [DecidableEq n] in
lemma ksym (Z : Mat n) (C : ι → Mat n) (i j : ι) : kernel Z C i j=kernel Z C j i := tr_swap .. 
omit [Fintype ι] in
lemma kpos {Z : Mat n} (hz : Z.IsHermitian) {C : ι → Mat n} (hc : ∀ i, (C i).PosSemidef)
    (i j : ι) : 0 ≤ kernel Z C i j := by
  have a := (hc i).mul_mul_conjTranspose_same Z
  rw [hz.eq] at a
  simpa [kernel,mul_assoc] using tr_pos a (hc j)
lemma krow (G : Mat n) (C : ι → Mat n) (hs : ∑ i, C i=G) (hu : IsUnit G) (i : ι) :
    ∑ j, kernel G⁻¹ C i j=tr (G⁻¹*C i) := by
  simp only [kernel,←tr_sum,←Matrix.mul_sum,hs,inv_left hu, mul_one]
lemma dissipation (G : Mat n) (C : ι → Mat n) (hs : ∑ i, C i=G) (hp : G.PosDef)
    (hc : ∀ i, (C i).PosSemidef) (w h : ι → ℝ)
    (hwh : ∀ i j, 0 ≤ (w i-w j)*(h i-h j)) :
    0 ≤ ∑ i, w i * (h i * tr (G⁻¹*C i) - ∑ j, h j * kernel G⁻¹ C j i) := by
  let K := kernel G⁻¹ C
  have p : 0 ≤ ∑ i, ∑ j, (w i-w j)*(h i-h j)*K i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hwh i j) (kpos hp.inv.isHermitian hc i j)
  let f := fun i j => w i*(h i-h j)*K i j
  have ea (i j : ι) : (w i-w j)*(h i-h j)*K i j = f i j+f j i := by
    dsimp [f,K]; rw [ksym _ _ j i]; ring
  simp_rw [ea,Finset.sum_add_distrib] at p
  rw [Finset.sum_comm (f:=fun i j => f j i)] at p
  have term (i : ι) : w i*(h i*tr (G⁻¹*C i)-∑ j, h j*kernel G⁻¹ C j i)=∑ j, f i j := by
    rw [←krow G C hs hp.isUnit i, Finset.mul_sum, ←Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    dsimp [f,K]; rw [ksym _ _ j i]; ring
  simp_rw [term]
  linarith

end
end Resolvent

namespace Resolvent
open Matrix Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
noncomputable section
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
def block (S : ι → Mat n) (h : ι → ℝ) (t : ℝ) (i : ι) := Real.exp (t*h i) • S i
def gram (S : ι → Mat n) (h : ι → ℝ) (t : ℝ) := ∑ i, block S h t i
def score (S : ι → Mat n) (w h : ι → ℝ) (t : ℝ) :=
  ∑ i, w i * tr ((gram S h t)⁻¹ * block S h t i)
omit [Fintype ι] in
lemma block_deriv (S : ι → Mat n) (h : ι → ℝ) (t : ℝ) (i : ι) :
  HasDerivAt (fun y => block S h y i) (h i • block S h t i) t := by
  simpa [block,smul_smul,mul_comm] using (((hasDerivAt_id t).mul_const (h i)).exp.smul_const (S i))
lemma gram_deriv (S : ι → Mat n) (h : ι → ℝ) (t : ℝ) :
  HasDerivAt (gram S h) (∑ i, h i • block S h t i) t :=
  HasDerivAt.fun_sum fun i _ => block_deriv S h t i
omit [DecidableEq n] in
lemma tr_add' (A B : Mat n) : tr (A+B)=tr A+tr B := by simp [tr]
omit [DecidableEq n] in
lemma tr_neg' (A : Mat n) : tr (-A)= -tr A := by simp [tr]
lemma score_monotone (S : ι → Mat n) (w h : ι → ℝ) (hs : ∀ i, (S i).PosSemidef)
    (hg : ∀ t, (gram S h t).PosDef) (order : ∀ i j, 0 ≤ (w i-w j)*(h i-h j)) :
    Monotone (score S w h) := by
  let slope := fun t => ∑ i, w i*(h i*tr ((gram S h t)⁻¹*block S h t i) -
    ∑ j, h j * kernel (gram S h t)⁻¹ (block S h t) j i)
  have derivation (t : ℝ) : HasDerivAt (score S w h) (slope t) t := by
    apply HasDerivAt.fun_sum; intro i _
    apply HasDerivAt.const_mul (w i)
    have dz := inv_deriv (gram_deriv S h t) (hg t).isUnit
    convert tr_deriv (dz.mul (block_deriv S h t i)) using 1
    all_goals try rfl
    simp only [kernel]
    simp only [neg_mul, Matrix.mul_sum, Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,
      tr_add',tr_neg',tr_sum,tr_smul,sub_eq_add_neg, mul_assoc]
    abel
  apply monotone_of_deriv_nonneg (fun t => (derivation t).differentiableAt)
  intro t
  rw [(derivation t).deriv]
  exact dissipation _ _ rfl (hg t) (fun i => (hs i).smul (Real.exp_pos _).le) w h order

lemma score_trace (S : ι → Mat n) (w h : ι → ℝ) (t : ℝ) :
  score S w h t = tr ((gram S h t)⁻¹ * ∑ i, w i • block S h t i) := by
  simp [score,Matrix.mul_sum,tr_sum,tr_smul]
end
end Resolvent

namespace Resolvent
open Matrix Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
def rd (b : n → ℝ) : Mat n := diagonal (fun i => (b i : ℂ))
omit [Fintype n] in
lemma rd_one : rd (fun _ : n => 1)=1 := by simp [rd]
lemma rd_mul (b c : n → ℝ) : rd b*rd c=rd (fun i => b i*c i) := by simp [rd,diagonal_mul_diagonal]
omit [Fintype n] in
lemma rd_star (b : n → ℝ) : (rd b)ᴴ=rd b := by simp [rd,diagonal_conjTranspose]
omit [Fintype n] in
lemma rd_pos {b : n → ℝ} (hb : ∀ i, 0 < b i) : (rd b).PosDef :=
  posDef_diagonal_iff.mpr fun i => by exact_mod_cast hb i
def compressed (X A : Mat n) := A + Xᴴ*A*X
def mass (X : Mat n) := 1+Xᴴ*X
lemma mass_pos (X : Mat n) : (mass X).PosDef := PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self _)
lemma comp_one (X : Mat n) : compressed X 1=mass X := by simp [compressed,mass]
lemma mass_push (X : Mat n) : mass Xᴴ * X = X * mass X := by simp [mass,add_mul,mul_add,mul_assoc]
lemma woodbury (X : Mat n) : X*(mass X)⁻¹*Xᴴ=1-(mass Xᴴ)⁻¹ := by
  let M := mass X
  let L := mass Xᴴ
  have m := inv_right (mass_pos X).isUnit
  have u := inv_left (mass_pos Xᴴ).isUnit
  have b : L*(X*M⁻¹*Xᴴ) = L-1 := by
    change mass Xᴴ*(X*(mass X)⁻¹*Xᴴ)=_
    rw [←mul_assoc,←mul_assoc,mass_push X, mul_assoc X (mass X),m,mul_one]
    simp [L,mass]
  calc X*(mass X)⁻¹*Xᴴ = (L⁻¹*L)*(X*M⁻¹*Xᴴ) := by rw [show L⁻¹*L=1 from u,one_mul]
       _ = L⁻¹*(L-1) := by rw [mul_assoc,b]
       _ = 1-L⁻¹ := by rw [mul_sub, show L⁻¹*L=1 from u,mul_one]
lemma graph_score (X W : Mat n) :
    tr ((mass X)⁻¹ * compressed X W) =
      tr W + tr (W*(mass X)⁻¹) - tr (W*(mass Xᴴ)⁻¹) := by
  have cyc : tr ((mass X)⁻¹*(Xᴴ*W*X))=tr (W*(X*(mass X)⁻¹*Xᴴ)) := by
    rw [tr_swap]; simp only [mul_assoc]; rw [tr_swap Xᴴ]; simp only [mul_assoc]
  simp only [compressed,mul_add,tr,Matrix.trace_add,Complex.add_re] at *
  rw [cyc,woodbury,mul_sub,mul_one,Matrix.trace_sub,Complex.sub_re,Matrix.trace_mul_comm (mass X)⁻¹]
  ring
lemma gauge (B X Y W : Mat n) (hb : Bᴴ=B)
    (inter : B*X=Y*B) :
    compressed X (B*W*B)=B*compressed Y W*B := by
  have it := congrArg Matrix.conjTranspose inter
  simp only [conjTranspose_mul,hb] at it
  unfold compressed
  rw [mul_add,add_mul]
  congr 1
  calc Xᴴ*(B*W*B)*X = (Xᴴ*B)*W*(B*X) := by simp [mul_assoc]
       _ = _ := by rw [it,inter]; simp [mul_assoc]
lemma gauge_score (B G T : Mat n) (bu : IsUnit B) :
    tr ((B*G*B)⁻¹*(B*T*B))=tr (G⁻¹*T) := by
  have c := inv_left bu
  simp only [Matrix.mul_inv_rev]
  calc tr (B⁻¹*(G⁻¹*B⁻¹)*(B*T*B)) = tr (B⁻¹*(G⁻¹*T)*B) := by
         congr 1; simp only [mul_assoc]; rw [←mul_assoc B⁻¹ B,c,one_mul]
       _ = _ := by rw [tr_swap _ B,←mul_assoc,inv_right bu,one_mul]
end
end Resolvent

namespace Resolvent
open Matrix Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
def atom (i : n) := rd (fun j => if i=j then 1 else 0)
omit [Fintype n] in
lemma atom_psd (i : n) : (atom i).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr; intro j
  by_cases e : i=j <;> simp [e]
lemma sum_atoms (a : n → ℝ) : ∑ i, a i • atom i=rd a := by
  ext j k
  simp only [Matrix.sum_apply,Matrix.smul_apply,atom,rd,diagonal_apply,Complex.real_smul]
  by_cases e : j=k
  · subst k; simp [apply_ite Complex.ofReal, mul_ite]
  · simp [e]
def slice (X : Mat n) (i : n) := compressed X (atom i)
lemma sum_slices (X : Mat n) (a : n → ℝ) : ∑ i, a i • slice X i=compressed X (rd a) := by
  unfold slice compressed
  have one (i : n) : a i • (Xᴴ*atom i*X) = Xᴴ*(a i • atom i)*X := by
    simp only [Matrix.mul_smul,Matrix.smul_mul]
  simp only [smul_add,Finset.sum_add_distrib,one,←Matrix.sum_mul,←Matrix.mul_sum,sum_atoms]
lemma slice_psd (X : Mat n) (i : n) : (slice X i).PosSemidef :=
  (atom_psd i).add ((atom_psd i).conjTranspose_mul_mul_same X)
lemma gram_slice (X : Mat n) (h : n → ℝ) (t : ℝ) :
  gram (slice X) h t = compressed X (rd (fun i => Real.exp (t*h i))) := sum_slices ..
lemma gram_pos (X : Mat n) (h : n → ℝ) (t : ℝ) : (gram (slice X) h t).PosDef := by
  rw [gram_slice]
  have p := rd_pos (fun i : n => Real.exp_pos (t*h i))
  exact p.add_posSemidef (p.posSemidef.conjTranspose_mul_mul_same X)
lemma score_slice (X : Mat n) (w h : n → ℝ) (t : ℝ) :
  score (slice X) w h t =
    tr ((compressed X (rd fun i => Real.exp (t*h i)))⁻¹ *
        compressed X (rd fun i => w i*Real.exp (t*h i))) := by
  rw [score_trace,gram_slice]; simp only [block,smul_smul,sum_slices]
end
end Resolvent

namespace Resolvent
open Matrix Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- A diagonal similarity carrying X to its adjoint orders all comonotone
weighted left and right resolvent traces. -/
lemma positive_diag (b w : n → ℝ) (hb : ∀ i, 0 < b i)
    (hw : ∀ i j, b i ≤ b j → w i ≤ w j) (R : Mat n) (hr : R.IsHermitian) :
    tr (rd w * (mass (R*rd b))⁻¹) ≤ tr (rd w * (mass (rd b*R))⁻¹) := by
  let B := rd b
  let W := rd w
  let X := R*B
  let Y := B*R
  let h := fun i => Real.log (b i ^ 2)
  have conjx : Xᴴ=Y := by simp [X,Y,B,conjTranspose_mul,rd_star,hr.eq]
  have conjy : Yᴴ=X := by rw [←conjx,conjTranspose_conjTranspose]
  have inter : B*X=Y*B := (mul_assoc ..).symm
  have bu : IsUnit B := (rd_pos hb).isUnit
  have ord (i j : n) : 0 ≤ (w i-w j)*(h i-h j) := by
    have inc (i j : n) (le : b i ≤ b j) : h i ≤ h j :=
      Real.log_le_log (sq_pos_of_pos (hb i)) (pow_le_pow_left₀ (hb i).le le _)
    rcases le_total (b i) (b j) with le|le
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hw _ _ le)) (sub_nonpos.mpr (inc _ _ le))
    · exact mul_nonneg (sub_nonneg.mpr (hw _ _ le)) (sub_nonneg.mpr (inc _ _ le))
  have slope := score_monotone (slice X) w h (slice_psd X) (gram_pos X h) ord (show (0:ℝ)≤1 by norm_num)
  rw [score_slice,score_slice] at slope
  have unitexp (i : n) : Real.exp (h i)=b i^2 := Real.exp_log (sq_pos_of_pos (hb i))
  simp only [zero_mul,Real.exp_zero,mul_one,rd_one,comp_one,one_mul,unitexp] at slope
  have ds : rd (fun i => b i^2)=B*1*B := by simp [B,rd_mul,pow_two]
  have dw : rd (fun i => w i*b i^2)=B*W*B := by
    simp only [B,W,rd_mul]; congr 1; funext i; ring
  rw [ds,dw,gauge B X Y 1 (rd_star b) inter,comp_one,gauge B X Y W (rd_star b) inter,
    gauge_score _ _ _ bu] at slope
  change tr ((mass X)⁻¹*compressed X W) ≤ tr ((mass Y)⁻¹*compressed Y W) at slope
  rw [graph_score,graph_score,conjx,conjy] at slope
  change tr (W*(mass X)⁻¹) ≤ tr (W*(mass Y)⁻¹)
  linarith

end
end Resolvent

namespace Resolvent
open Matrix Filter Topology
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
lemma continuous_objective (W : Mat n) :
    Continuous (fun X : Mat n => tr (W*(mass X)⁻¹)) := by
  have cg : Continuous (mass (n:=n)) := continuous_const.add (continuous_id.matrix_conjTranspose.mul continuous_id)
  let L := Complex.reCLM.comp (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap n ℝ ℂ))
  apply continuous_iff_continuousAt.mpr
  intro X
  have inv : ContinuousAt (fun A : Mat n => A⁻¹) (mass X) := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse] using (differentiableAt_inverse (𝕜:=ℝ) (mass_pos X).isUnit).continuousAt
  exact L.continuous.continuousAt.comp (continuousAt_const.mul (inv.comp cg.continuousAt))
omit [Fintype n] in
lemma shifted (b : n → ℝ) (t : ℝ) : rd (fun i => b i+t)=rd b + t • (1 : Mat n) := by
  ext i j
  by_cases e : i=j
  · subst j; simp [rd,Complex.real_smul]
  · simp [rd,e]
lemma semidefinite_diag (b w : n → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hw : ∀ i j, b i ≤ b j → w i ≤ w j) (R : Mat n) (hr : R.IsHermitian) :
    tr (rd w * (mass (R*rd b))⁻¹) ≤ tr (rd w * (mass (rd b*R))⁻¹) := by
  let D := fun t : ℝ => rd b + t • (1 : Mat n)
  have d : Continuous D := continuous_const.add (continuous_id.smul continuous_const)
  have d0 : D 0=rd b := by simp [D]
  have left := (continuous_objective (rd w)).comp ((continuous_const (y:=R)).mul d)
  have right := (continuous_objective (rd w)).comp (d.mul (continuous_const (y:=R)))
  have lim₁ := left.continuousAt (x:=0) |>.tendsto.mono_left (nhdsWithin_le_nhds (s:=Set.Ioi 0))
  have lim₂ := right.continuousAt (x:=0) |>.tendsto.mono_left (nhdsWithin_le_nhds (s:=Set.Ioi 0))
  have ev : ∀ᶠ t in 𝓝[>] (0:ℝ), tr (rd w*(mass (R*D t))⁻¹) ≤ tr (rd w*(mass (D t*R))⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have tp : 0<t := ht
    rw [show D t=rd (fun i => b i+t) from (shifted b t).symm]
    exact positive_diag _ w (fun i => add_pos_of_nonneg_of_pos (hb i) tp)
      (fun i j p => hw i j (by linarith)) R hr
  simpa [Function.comp_def,d0] using le_of_tendsto_of_tendsto lim₁ lim₂ ev
end
end Resolvent

namespace Resolvent
open Matrix Unitary
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [DecidableEq n] in
lemma weighted_trace_real {A B : Mat n} (ha : A.IsHermitian) (hb : B.IsHermitian) :
    (A*B).trace.im=0 := by
  apply Complex.conj_eq_iff_im.mp
  change star (A*B).trace=(A*B).trace
  rw [←Matrix.trace_conjTranspose,conjTranspose_mul,ha.eq,hb.eq,Matrix.trace_mul_comm]
lemma tr_conj (U : unitary (Mat n)) (A : Mat n) :
  tr (conjStarAlgAut ℂ _ U A)=tr A := by
  simp only [conjStarAlgAut_apply,tr,Matrix.trace_mul_cycle,Unitary.coe_star_mul_self,one_mul]
lemma conjugate_score (U : unitary (Mat n)) (X W : Mat n) :
    tr (conjStarAlgAut ℂ _ U W * (mass (conjStarAlgAut ℂ _ U X))⁻¹)=tr (W*(mass X)⁻¹) := by
  let Φ := conjStarAlgAut ℂ (Mat n) U
  have m : mass (Φ X)=Φ (mass X) := by
    unfold mass
    change 1 + star (Φ X)*Φ X = Φ (1+star X*X)
    rw [map_add,map_mul,map_one,map_star]
  have inv : (Φ (mass X))⁻¹=Φ ((mass X)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [←map_mul,inv_left (mass_pos X).isUnit,map_one]
  change tr (Φ W*(mass (Φ X))⁻¹)=_
  rw [m,inv,←map_mul,tr_conj]
/-- The stronger comparison holds for any scalar weight preserving the
ordering of the eigenvalues, including discontinuous threshold weights. -/
theorem isotone_weight (B R : Mat n) (hB : B.PosSemidef) (hR : R.IsHermitian)
    (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Ici 0)) :
    tr (hB.isHermitian.cfc f * (1+B*R^2*B)⁻¹) ≤
    tr (hB.isHermitian.cfc f * (1+R*B^2*R)⁻¹) := by
  let b := hB.isHermitian.eigenvalues
  let U := hB.isHermitian.eigenvectorUnitary
  let Φ := conjStarAlgAut ℂ (Mat n) U
  let T := Φ.symm R
  let w := fun i => f (b i)
  have be : B=Φ (rd b) := hB.isHermitian.spectral_theorem
  have we : hB.isHermitian.cfc f=Φ (rd w) := rfl
  have re : Φ T=R := Φ.apply_symm_apply R
  have th : T.IsHermitian := by
    change star (Φ.symm R)=Φ.symm R
    rw [←map_star, show star R=R from hR.eq]
  have base := semidefinite_diag b w (hB.eigenvalues_nonneg)
    (fun i j h => hf (hB.eigenvalues_nonneg i) (hB.eigenvalues_nonneg j) h) T th
  have one : mass (R*B)=1+B*R^2*B := by simp [mass,conjTranspose_mul,hR.eq,hB.1.eq,pow_two,mul_assoc]
  have two : mass (B*R)=1+R*B^2*R := by simp [mass,conjTranspose_mul,hR.eq,hB.1.eq,pow_two,mul_assoc]
  rw [←one,←two,we]
  have l : Φ (T*rd b)=R*B := by rw [map_mul,re,←be]
  have r : Φ (rd b*T)=B*R := by rw [map_mul,re,←be]
  rw [←l,←r,conjugate_score,conjugate_score]
  exact base
end
end Resolvent

theorem OMA.solution : type_of% @OMA.S_mo_279044.main := by
  intro n B R hB hR s hs
  exact Resolvent.isotone_weight B R hB hR _ (fun _ hx _ _ h => Real.rpow_le_rpow hx h hs)
