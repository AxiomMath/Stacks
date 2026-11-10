module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SmoothLift.BaseChange

/-!
# The Čech argument: local lifts can be corrected to agree on overlaps

Let `B_k`, `k ∈ K`, be a finite family of flat framed `A'`-algebras which is jointly faithfully
flat, and let `z_k` be lifts over `B_k`.  Then the lifts can be corrected by tangent vectors so
that they agree over every `B_k ⊗_{A'} B_l`.

## Main definitions

* `AlgebraicGeometry.Space.SmoothLift.cech0`, `AlgebraicGeometry.Space.SmoothLift.cech1`: the
  Čech differentials in degrees zero and one, with values in the tangent vectors.
* `AlgebraicGeometry.Space.SmoothLift.cocyc`: the difference of the two restrictions of the lifts
  to a double overlap.

## Main results

* `AlgebraicGeometry.Space.SmoothLift.Framing.gBaseChange_bijective`: the tangent vectors over a
  flat base change `R ⊗ R'` are the base change of those over `R`.
* `AlgebraicGeometry.Space.SmoothLift.cech1_cocyc`: the differences of the lifts form a cocycle.
* `AlgebraicGeometry.Space.SmoothLift.cech_exact`: every Čech `1`-cocycle is a coboundary.
* `AlgebraicGeometry.Space.SmoothLift.exists_compatible_lifts`: the lifts can be corrected to
  agree on the double overlaps.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space.SmoothLift

open Stacks.SmoothLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : Base B S hS}
  {𝔓 : Problem D}

/-! ### Base change of the group of tangent vectors -/

section GBaseChange

variable {F : Frame 𝔓} {R : Alg D} (Fr : Framing F R) (R' : Alg D)

/-- The identification of the tangent vectors with the coordinate derivations, over `A'`. -/
noncomputable def Framing.gEquivA : Fr.G ≃ₗ[D.A] Fr.Der :=
  Fr.gEquiv.restrictScalars D.A

/-- **The base change map of tangent vectors**, `g ⊗ b ↦ (1 ⊗ b) · g|_{R ⊗ R'}`. -/
noncomputable def Framing.gBaseChange : Fr.G ⊗[D.A] R'.R →ₗ[D.A] (Fr.tens R').G :=
  (Fr.tens R').gEquivA.symm.toLinearMap ∘ₗ Fr.baseChange R' ∘ₗ
    Fr.gEquivA.toLinearMap.rTensor R'.R

theorem Framing.gBaseChange_tmul (g : Fr.G) (b : R'.R) :
    Fr.gBaseChange R' (g ⊗ₜ b) =
      (Ideal.Quotient.mk (sqIdeal D.C (Alg.tensor R R').R) (incl₂ R' b) :
        Q D.C (Alg.tensor R R').R) • (Fr.tens R').ofT ((Fr.toT g).pull (incl₁ R')) := by
  apply (Fr.tens R').tangentEquiv.injective
  change (Fr.tens R').tangentEquiv ((Fr.tens R').gEquivA.symm (Fr.baseChange R'
    (Fr.gEquivA g ⊗ₜ b))) = _
  rw [show (Fr.tens R').tangentEquiv ((Fr.tens R').gEquivA.symm _) = _ from
    LinearEquiv.apply_symm_apply (Fr.tens R').gEquiv _, Fr.baseChange_tmul]
  change _ = (Fr.tens R').tangentEquiv ((Fr.tens R').toT (_ • _))
  rw [(Fr.tens R').smul_eq, (Fr.tens R').tangentEquiv_smul, (Fr.tens R').toT_ofT,
    Fr.tangentEquiv_pull]
  rfl

/-- Along a flat algebra `R'`, the base change map of tangent vectors is bijective. -/
theorem Framing.gBaseChange_bijective [Module.Flat D.A R'.R] :
    Function.Bijective (Fr.gBaseChange R') :=
  (Fr.tens R').gEquivA.symm.bijective.comp
    ((Fr.baseChange_bijective R').comp (LinearEquiv.rTensor R'.R Fr.gEquivA).bijective)

end GBaseChange

/-! ### Pullback of tangent vectors as a linear map -/

section PullLin

variable {F F' : Frame 𝔓} {R R' : Alg D} (Fr : Framing F R) (Fr' : Framing F' R')
  (h : R.R →ₐ[D.A] R'.R) (z : 𝔓.Lifts R)

/-- Pullback of tangent vectors along an algebra map, as a linear map over `A'`; its
additivity uses the lift `z`. -/
noncomputable def pullLin : Fr.G →ₗ[D.A] Fr'.G where
  toFun t := Fr'.ofT ((Fr.toT t).pull h)
  map_add' := Fr.pull_add Fr' h z
  map_smul' c t := by
    change Fr'.ofT ((Fr.toT (algebraMap D.A (Q D.C R.R) c • t)).pull h) =
      algebraMap D.A (Q D.C R'.R) c • Fr'.ofT ((Fr.toT t).pull h)
    rw [Fr.pull_smul Fr' h, qMap_algebraMap]

theorem pullLin_apply (t : Fr.G) : pullLin Fr Fr' h z t = Fr'.ofT ((Fr.toT t).pull h) := rfl

theorem toT_pullLin (t : Fr.G) : Fr'.toT (pullLin Fr Fr' h z t) = (Fr.toT t).pull h := rfl

theorem pullLin_pullLin {F'' : Frame 𝔓} {R'' : Alg D} (Fr'' : Framing F'' R'')
    (h' : R'.R →ₐ[D.A] R''.R) (z' : 𝔓.Lifts R') (t : Fr.G) :
    pullLin Fr' Fr'' h' z' (pullLin Fr Fr' h z t) = Fr''.ofT ((Fr.toT t).pull (h'.comp h)) :=
  congrArg Fr''.ofT (Problem.Tangents.pull_comp h h' (Fr.toT t))

theorem pullLin_smul (q : Q D.C R.R) (t : Fr.G) :
    pullLin Fr Fr' h z (q • t) = qMap D.C h q • pullLin Fr Fr' h z t :=
  Fr.pull_smul Fr' h q t

end PullLin

/-! ### A faithfully flat product of algebras -/

/-- If a finite product of `A`-algebras `C k` is faithfully flat over `A`, an element `n` lies in
the range of a linear map `δ` as soon as each `n ⊗ 1` lies in the range of `δ ⊗ C k`. -/
theorem Module.FaithfullyFlat.mem_range_of_forall_mem_range {A M N : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] {K : Type*} [Finite K]
    (C : K → Type*) [∀ k, CommRing (C k)] [∀ k, Algebra A (C k)]
    [Module.FaithfullyFlat A (∀ k, C k)] (δ : M →ₗ[A] N) (n : N)
    (h : ∀ k, n ⊗ₜ[A] (1 : C k) ∈ LinearMap.range (δ.rTensor (C k))) :
    n ∈ LinearMap.range δ := by
  classical
  have := Fintype.ofFinite K
  choose ε hε using h
  refine Module.FaithfullyFlat.mem_range_of_tmul_one_mem_range (B' := ∀ k, C k) δ n
    ⟨(TensorProduct.piRight A A M C).symm ε, ?_⟩
  apply (TensorProduct.piRight A A N C).injective
  funext k
  have hnat : ∀ x : M ⊗[A] (∀ k, C k), TensorProduct.piRight A A N C (δ.rTensor _ x) k =
      δ.rTensor (C k) (TensorProduct.piRight A A M C x k) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul m f => rfl
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  rw [hnat, LinearEquiv.apply_symm_apply, hε]
  rfl

/-! ### The Čech complex of a finite family of framed algebras -/

section Family

variable {K : Type u} (Bk : K → Alg D)

/-- The double overlaps `B_k ⊗ B_l`. -/
noncomputable abbrev R2 (k l : K) : Alg D := Alg.tensor (Bk k) (Bk l)

/-- The triple overlaps `(B_k ⊗ B_l) ⊗ B_m`. -/
noncomputable abbrev R3 (k l m : K) : Alg D := Alg.tensor (R2 Bk k l) (Bk m)

/-- The first face `B_k → B_k ⊗ B_l`. -/
noncomputable abbrev f1 (k l : K) : (Bk k).R →ₐ[D.A] (R2 Bk k l).R := incl₁ (Bk l)

/-- The second face `B_l → B_k ⊗ B_l`. -/
noncomputable abbrev f2 (k l : K) : (Bk l).R →ₐ[D.A] (R2 Bk k l).R := incl₂ (R := Bk k) (Bk l)

/-- The face `B_k ⊗ B_l → B_k ⊗ B_l ⊗ B_m`. -/
noncomputable abbrev f12 (k l m : K) : (R2 Bk k l).R →ₐ[D.A] (R3 Bk k l m).R := incl₁ (Bk m)

/-- The face `B_k ⊗ B_m → B_k ⊗ B_l ⊗ B_m`. -/
noncomputable abbrev f13 (k l m : K) : (R2 Bk k m).R →ₐ[D.A] (R3 Bk k l m).R :=
  Alg.tensorMap (f1 Bk k l) (Bk m)

/-- The face `B_l ⊗ B_m → B_k ⊗ B_l ⊗ B_m`. -/
noncomputable abbrev f23 (k l m : K) : (R2 Bk l m).R →ₐ[D.A] (R3 Bk k l m).R :=
  Alg.tensorMap (f2 Bk k l) (Bk m)

theorem f12_f1 (k l m : K) : (f12 Bk k l m).comp (f1 Bk k l) = (f13 Bk k l m).comp (f1 Bk k m) :=
  AlgHom.ext fun _ => rfl

theorem f12_f2 (k l m : K) : (f12 Bk k l m).comp (f2 Bk k l) = (f23 Bk k l m).comp (f1 Bk l m) :=
  AlgHom.ext fun _ => rfl

theorem f13_f2 (k l m : K) : (f13 Bk k l m).comp (f2 Bk k m) = (f23 Bk k l m).comp (f2 Bk l m) := by
  apply AlgHom.ext
  intro b
  change Alg.tmul (f1 Bk k l 1) b = Alg.tmul (f2 Bk k l 1) b
  rw [map_one, map_one]

theorem f13_incl₂ (k l m : K) (b : (Bk m).R) :
    f13 Bk k l m (incl₂ (R := Bk k) (Bk m) b) = incl₂ (R := R2 Bk k l) (Bk m) b := by
  change Alg.tmul (f1 Bk k l 1) b = Alg.tmul 1 b
  rw [map_one]

theorem f23_incl₂ (k l m : K) (b : (Bk m).R) :
    f23 Bk k l m (incl₂ (R := Bk l) (Bk m) b) = incl₂ (R := R2 Bk k l) (Bk m) b := by
  change Alg.tmul (f2 Bk k l 1) b = Alg.tmul 1 b
  rw [map_one]

variable {Fk : K → Frame 𝔓} (Fr : ∀ k, Framing (Fk k) (Bk k)) (z : ∀ k, 𝔓.Lifts (Bk k))

/-- The framing of a double overlap by its first factor. -/
noncomputable abbrev Fr2 (k l : K) : Framing (Fk k) (R2 Bk k l) := (Fr k).tens (Bk l)

/-- The framing of a triple overlap by its first factor. -/
noncomputable abbrev Fr3 (k l m : K) : Framing (Fk k) (R3 Bk k l m) := (Fr2 Bk Fr k l).tens (Bk m)

/-- The lift `z_k` restricted to `B_k ⊗ B_l`. -/
noncomputable abbrev z2 (k l : K) : 𝔓.Lifts (R2 Bk k l) := (z k).pull (f1 Bk k l)

/-- **The Čech differential in degree zero.** -/
noncomputable def cech0 : (∀ k, (Fr k).G) →ₗ[D.A] (∀ k l, (Fr2 Bk Fr k l).G) :=
  LinearMap.pi fun k => LinearMap.pi fun l =>
    pullLin (Fr l) (Fr2 Bk Fr k l) (f2 Bk k l) (z l) ∘ₗ LinearMap.proj l -
      pullLin (Fr k) (Fr2 Bk Fr k l) (f1 Bk k l) (z k) ∘ₗ LinearMap.proj k

theorem cech0_apply (y : ∀ k, (Fr k).G) (k l : K) :
    cech0 Bk Fr z y k l = pullLin (Fr l) (Fr2 Bk Fr k l) (f2 Bk k l) (z l) (y l) -
      pullLin (Fr k) (Fr2 Bk Fr k l) (f1 Bk k l) (z k) (y k) := rfl

/-- **The Čech differential in degree one**, as a function. -/
noncomputable def cech1 (x : ∀ k l, (Fr2 Bk Fr k l).G) (k l m : K) : (Fr3 Bk Fr k l m).G :=
  pullLin (Fr2 Bk Fr l m) (Fr3 Bk Fr k l m) (f23 Bk k l m) (z2 Bk z l m) (x l m) -
    pullLin (Fr2 Bk Fr k m) (Fr3 Bk Fr k l m) (f13 Bk k l m) (z2 Bk z k m) (x k m) +
      pullLin (Fr2 Bk Fr k l) (Fr3 Bk Fr k l m) (f12 Bk k l m) (z2 Bk z k l) (x k l)

/-! ### The cocycle of a family of lifts -/

/-- The difference of the two restrictions of the lifts to a double overlap. -/
noncomputable def cocyc (k l : K) : (Fr2 Bk Fr k l).G :=
  (Fr2 Bk Fr k l).ofT (Classical.choose ((Fr2 Bk Fr k l).exists_act (z2 Bk z k l)
    ((z l).pull (f2 Bk k l))))

theorem act_cocyc (k l : K) :
    act ((Fr2 Bk Fr k l).toT (cocyc Bk Fr z k l)) (z2 Bk z k l) = (z l).pull (f2 Bk k l) :=
  Classical.choose_spec ((Fr2 Bk Fr k l).exists_act (z2 Bk z k l) ((z l).pull (f2 Bk k l)))

theorem act_pull_cocyc {k l : K} {R' : Alg D} (h : (R2 Bk k l).R →ₐ[D.A] R'.R) :
    act (((Fr2 Bk Fr k l).toT (cocyc Bk Fr z k l)).pull h) ((z k).pull (h.comp (f1 Bk k l))) =
      (z l).pull (h.comp (f2 Bk k l)) := by
  rw [← Problem.Lifts.pull_comp, act_pull, act_cocyc, Problem.Lifts.pull_comp]

/-- **The cocycle condition.** -/
theorem cech1_cocyc : cech1 Bk Fr z (cocyc Bk Fr z) = 0 := by
  funext k l m
  let Φ := Fr3 Bk Fr k l m
  let w : 𝔓.Lifts (R3 Bk k l m) := (z k).pull ((f12 Bk k l m).comp (f1 Bk k l))
  have h12 := act_pull_cocyc Bk Fr z (f12 Bk k l m)
  have h23 := act_pull_cocyc Bk Fr z (f23 Bk k l m)
  have h13 := act_pull_cocyc Bk Fr z (f13 Bk k l m)
  rw [f12_f2] at h12
  rw [← f12_f1, f13_f2] at h13
  have key : pullLin (Fr2 Bk Fr l m) Φ (f23 Bk k l m) (z2 Bk z l m) (cocyc Bk Fr z l m) +
      pullLin (Fr2 Bk Fr k l) Φ (f12 Bk k l m) (z2 Bk z k l) (cocyc Bk Fr z k l) =
      pullLin (Fr2 Bk Fr k m) Φ (f13 Bk k l m) (z2 Bk z k m) (cocyc Bk Fr z k m) := by
    apply Φ.toT_injective_act w
    rw [Φ.act_add]
    exact (congrArg _ h12).trans (h23.trans h13.symm)
  change _ - _ + _ = (0 : Φ.G)
  rw [← key]
  abel

end Family

/-! ### Finite products and tensor products -/

theorem piLeft_apply_eq {A N : Type*} [CommRing A] [AddCommGroup N] [Module A N] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    (x : (∀ i, M i) ⊗[A] N) (i : ι) :
    TensorProduct.piLeft A N M x i = (LinearMap.proj i).rTensor N x := by
  induction x using TensorProduct.inductionOn with
  | tmul f n => rfl
  | add x y hx hy => rw [map_add, Pi.add_apply, hx, hy, map_add]

/-- A family of maps out of the factors of a tensor product with a finite product is jointly
bijective as soon as each is bijective. -/
theorem pi_rTensor_bijective {A N : Type*} [CommRing A] [AddCommGroup N] [Module A N] {ι : Type*}
    [Finite ι] (M M' : ι → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module A (M i)] [∀ i, AddCommGroup (M' i)] [∀ i, Module A (M' i)]
    (g : ∀ i, M i ⊗[A] N →ₗ[A] M' i) (hg : ∀ i, Function.Bijective (g i)) :
    Function.Bijective (LinearMap.pi fun i => g i ∘ₗ (LinearMap.proj i).rTensor N) := by
  classical
  have := Fintype.ofFinite ι
  have : (LinearMap.pi fun i => g i ∘ₗ (LinearMap.proj i).rTensor N : _ → _) =
      (fun y i => g i (y i)) ∘ TensorProduct.piLeft A N M := by
    funext x i
    simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, piLeft_apply_eq]
  rw [this]
  refine Function.Bijective.comp ⟨fun y y' h => funext fun i => (hg i).1 (congrFun h i),
    fun y => ⟨fun i => ((hg i).2 (y i)).choose, funext fun i => ((hg i).2 (y i)).choose_spec⟩⟩
    (TensorProduct.piLeft A N M).bijective

/-! ### Exactness of the Čech complex in degree one -/

section Exact

variable {K : Type u} (Bk : K → Alg D) {Fk : K → Frame 𝔓}
  (Fr : ∀ k, Framing (Fk k) (Bk k)) (z : ∀ k, 𝔓.Lifts (Bk k))

/-- The base change of the degree-zero cochains along `B_m`. -/
noncomputable def cechI1 (m : K) :
    (∀ k, (Fr k).G) ⊗[D.A] (Bk m).R →ₗ[D.A] (∀ k, (Fr2 Bk Fr k m).G) :=
  LinearMap.pi fun k => (Fr k).gBaseChange (Bk m) ∘ₗ (LinearMap.proj k).rTensor _

/-- The base change of the degree-one cochains along `B_m`. -/
noncomputable def cechI2 (m : K) :
    (∀ k l, (Fr2 Bk Fr k l).G) ⊗[D.A] (Bk m).R →ₗ[D.A] (∀ k l, (Fr3 Bk Fr k l m).G) :=
  LinearMap.pi fun k => (LinearMap.pi fun l => (Fr2 Bk Fr k l).gBaseChange (Bk m) ∘ₗ
    (LinearMap.proj l).rTensor _) ∘ₗ (LinearMap.proj k).rTensor _

/-- The Čech differential of the base-changed complex, the last factor being kept. -/
noncomputable def cechD0 (m : K) : (∀ k, (Fr2 Bk Fr k m).G) →ₗ[D.A] (∀ k l, (Fr3 Bk Fr k l m).G) :=
  LinearMap.pi fun k => LinearMap.pi fun l =>
    pullLin (Fr2 Bk Fr l m) (Fr3 Bk Fr k l m) (f23 Bk k l m) (z2 Bk z l m) ∘ₗ LinearMap.proj l -
      pullLin (Fr2 Bk Fr k m) (Fr3 Bk Fr k l m) (f13 Bk k l m) (z2 Bk z k m) ∘ₗ LinearMap.proj k

theorem cechI1_tmul (m : K) (y : ∀ k, (Fr k).G) (b : (Bk m).R) (k : K) :
    cechI1 Bk Fr m (y ⊗ₜ b) k = (Fr k).gBaseChange (Bk m) (y k ⊗ₜ b) := rfl

theorem cechI2_tmul (m : K) (x : ∀ k l, (Fr2 Bk Fr k l).G) (b : (Bk m).R) (k l : K) :
    cechI2 Bk Fr m (x ⊗ₜ b) k l = (Fr2 Bk Fr k l).gBaseChange (Bk m) (x k l ⊗ₜ b) := rfl

theorem cechD0_apply (m : K) (e : ∀ k, (Fr2 Bk Fr k m).G) (k l : K) :
    cechD0 Bk Fr z m e k l =
      pullLin (Fr2 Bk Fr l m) (Fr3 Bk Fr k l m) (f23 Bk k l m) (z2 Bk z l m) (e l) -
        pullLin (Fr2 Bk Fr k m) (Fr3 Bk Fr k l m) (f13 Bk k l m) (z2 Bk z k m) (e k) := rfl

theorem cechI1_bijective [Finite K] [∀ m, Module.Flat D.A (Bk m).R] (m : K) :
    Function.Bijective (cechI1 Bk Fr m) :=
  pi_rTensor_bijective _ _ _ fun k => (Fr k).gBaseChange_bijective (Bk m)

theorem cechI2_bijective [Finite K] [∀ m, Module.Flat D.A (Bk m).R] (m : K) :
    Function.Bijective (cechI2 Bk Fr m) :=
  pi_rTensor_bijective _ _ _ fun k =>
    pi_rTensor_bijective _ _ _ fun l => (Fr2 Bk Fr k l).gBaseChange_bijective (Bk m)

theorem cech_comm_tmul (m : K) (y : ∀ k, (Fr k).G) (b : (Bk m).R) (k l : K) :
    (Fr2 Bk Fr k l).gBaseChange (Bk m) (cech0 Bk Fr z y k l ⊗ₜ b) =
      pullLin (Fr2 Bk Fr l m) (Fr3 Bk Fr k l m) (f23 Bk k l m) (z2 Bk z l m)
          ((Fr l).gBaseChange (Bk m) (y l ⊗ₜ b)) -
        pullLin (Fr2 Bk Fr k m) (Fr3 Bk Fr k l m) (f13 Bk k l m) (z2 Bk z k m)
          ((Fr k).gBaseChange (Bk m) (y k ⊗ₜ b)) := by
  rw [Framing.gBaseChange_tmul, Framing.gBaseChange_tmul, Framing.gBaseChange_tmul,
    ← pullLin_apply (Fr2 Bk Fr k l) (Fr3 Bk Fr k l m) (f12 Bk k l m) (z2 Bk z k l),
    ← pullLin_apply (Fr l) (Fr2 Bk Fr l m) (f1 Bk l m) (z l),
    ← pullLin_apply (Fr k) (Fr2 Bk Fr k m) (f1 Bk k m) (z k),
    pullLin_smul, pullLin_smul, cech0_apply, map_sub, pullLin_pullLin, pullLin_pullLin,
    pullLin_pullLin, pullLin_pullLin, qMap_mk, qMap_mk, f23_incl₂, f13_incl₂, f12_f2,
    f12_f1, smul_sub]

theorem cech_comm (m : K) (w : (∀ k, (Fr k).G) ⊗[D.A] (Bk m).R) :
    cechI2 Bk Fr m ((cech0 Bk Fr z).rTensor _ w) = cechD0 Bk Fr z m (cechI1 Bk Fr m w) := by
  induction w using TensorProduct.inductionOn with
  | tmul y b =>
    funext k l
    rw [LinearMap.rTensor_tmul, cechI2_tmul, cechD0_apply, cechI1_tmul, cechI1_tmul]
    exact cech_comm_tmul Bk Fr z m y b k l
  | add w w' hw hw' => rw [map_add, map_add, hw, hw', map_add, map_add]

theorem neg_sub_neg_eq_of_sub_add {G : Type*} [AddCommGroup G] {a b c : G} (h : a - b + c = 0) :
    -a - -b = c := by
  rw [neg_sub_neg, eq_neg_of_add_eq_zero_right h, neg_sub]

theorem cech1_apply (x : ∀ k l, (Fr2 Bk Fr k l).G) (k l m : K) :
    cech1 Bk Fr z x k l m =
      pullLin (Fr2 Bk Fr l m) (Fr3 Bk Fr k l m) (f23 Bk k l m) (z2 Bk z l m) (x l m) -
        pullLin (Fr2 Bk Fr k m) (Fr3 Bk Fr k l m) (f13 Bk k l m) (z2 Bk z k m) (x k m) +
          pullLin (Fr2 Bk Fr k l) (Fr3 Bk Fr k l m) (f12 Bk k l m) (z2 Bk z k l) (x k l) := rfl

/-- For a family of flat algebras, the base change of a Čech `1`-cocycle along each `B_m` is a
coboundary. -/
theorem cech_tmul_mem_range [Finite K] [∀ m, Module.Flat D.A (Bk m).R]
    (x : ∀ k l, (Fr2 Bk Fr k l).G) (hx : cech1 Bk Fr z x = 0) (m : K) :
    x ⊗ₜ[D.A] (1 : (Bk m).R) ∈ LinearMap.range ((cech0 Bk Fr z).rTensor (Bk m).R) := by
  obtain ⟨w, hw⟩ := (cechI1_bijective Bk Fr m).2 (fun k => -(x k m))
  refine ⟨w, (cechI2_bijective Bk Fr m).1 ?_⟩
  rw [cech_comm, hw]
  funext k l
  rw [cechD0_apply, cechI2_tmul, Framing.gBaseChange_tmul, map_one, map_one, one_smul,
    ← pullLin_apply (Fr2 Bk Fr k l) (Fr3 Bk Fr k l m) (f12 Bk k l m) (z2 Bk z k l), map_neg,
    map_neg]
  have h := congrFun (congrFun (congrFun hx k) l) m
  rw [cech1_apply] at h
  exact neg_sub_neg_eq_of_sub_add h

/-- **Exactness of the Čech complex in degree one**: every cocycle is a coboundary. -/
theorem cech_exact [Finite K] [∀ m, Module.Flat D.A (Bk m).R]
    [Module.FaithfullyFlat D.A (∀ m, (Bk m).R)] (x : ∀ k l, (Fr2 Bk Fr k l).G)
    (hx : cech1 Bk Fr z x = 0) : ∃ y, cech0 Bk Fr z y = x :=
  Module.FaithfullyFlat.mem_range_of_forall_mem_range (fun m => (Bk m).R) (cech0 Bk Fr z) x
    (cech_tmul_mem_range Bk Fr z x hx)

include Fr z in
/-- **Local lifts can be corrected to agree on the double overlaps.** -/
theorem exists_compatible_lifts [Finite K] [∀ m, Module.Flat D.A (Bk m).R]
    [Module.FaithfullyFlat D.A (∀ m, (Bk m).R)] :
    ∃ z' : ∀ k, 𝔓.Lifts (Bk k), ∀ k l, (z' k).pull (f1 Bk k l) = (z' l).pull (f2 Bk k l) := by
  obtain ⟨y, hy⟩ := cech_exact Bk Fr z (cocyc Bk Fr z) (cech1_cocyc Bk Fr z)
  refine ⟨fun k => act ((Fr k).toT (-(y k))) (z k), fun k l => ?_⟩
  have hc : cocyc Bk Fr z k l =
      pullLin (Fr l) (Fr2 Bk Fr k l) (f2 Bk k l) (z l) (y l) -
        pullLin (Fr k) (Fr2 Bk Fr k l) (f1 Bk k l) (z k) (y k) := by
    rw [← hy]; rfl
  rw [← act_pull, ← act_pull, ← act_cocyc Bk Fr z k l]
  change act ((Fr2 Bk Fr k l).toT (pullLin (Fr k) (Fr2 Bk Fr k l) (f1 Bk k l) (z k) (-(y k))))
      (z2 Bk z k l) =
    act ((Fr2 Bk Fr k l).toT (pullLin (Fr l) (Fr2 Bk Fr k l) (f2 Bk k l) (z l) (-(y l))))
      (act ((Fr2 Bk Fr k l).toT (cocyc Bk Fr z k l)) (z2 Bk z k l))
  rw [← (Fr2 Bk Fr k l).act_add, hc, map_neg, map_neg]
  congr 2
  abel

end Exact

end AlgebraicGeometry.Space.SmoothLift
