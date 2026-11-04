module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.TwistComparison
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.TwistRestriction
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePushforwardCartesian
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.PullbackBaseAlgebra

/-!
# Flat base change of the vanishing ideal of a closed subscheme of a relative Proj

Work in Situation 01NN: a scheme `T`, a quasi-coherent graded `𝒪_T`-algebra `𝒜`,
`p : Proj_T(𝒜) ⟶ T` and a closed immersion `i : Z ⟶ Proj_T(𝒜)`.  A homogeneous section `a` of
`𝒜_n` is an *equation* for `Z` when the section of `𝒪(n)` it names restricts to zero on `Z`; these
are the sections of Tag 0801's graded ideal (`mem_twistKerGradedIdeal_iff`).  This file proves that
the equations commute with flat base change of affine bases: along a flat morphism `g : T' ⟶ T` of
affine schemes, the equations for `Z ×_T T' ⊆ Proj_{T'}(g^*𝒜)` are the `Γ(T', 𝒪)`-combinations of
the base changes of the equations for `Z`.  This is the step "`ℐ` is quasi-coherent" of the proof
of Stacks 085L, read on charts, and it rests on flat base change of global sections
(Stacks 02KH in degree zero).

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistEquationSection`: the restriction to `Z`
  of the section of `𝒪(n)` named by a global section of `𝒜_n`; it vanishes exactly on the global
  sections of Tag 0801's graded ideal (`twistEquationSection_eq_zero_iff`).
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistEquationTransport`: along the base
  change `pc : Proj_{T'}(𝒜₁) ⟶ Proj_T(𝒜)` of Stacks 084B (3) and a square `z ≫ i = i₁ ≫ pc`, the
  comparison `z^*(i^*𝒪(n)) ≅ i₁^*𝒪₁(n)`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistEquationTransport_pullbackSection`: the
  comparison carries `z^*` of the equation section of `a` to the equation section of its
  restriction.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistEquationSection_eq_zero_of_restrict`:
  equations restrict to equations, along any base change.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.mem_span_of_twistEquationSection_eq_zero`:
  **flat base change of the equations** over affine bases.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistEquationSection_eq_zero_of_cover`:
  **being an equation descends** along a jointly surjective family of flat base changes of affine
  bases.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.ker_le_span_image_of_flat` and
  `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.eq_zero_of_forall_one_tmul_eq_zero`: the
  commutative algebra behind the last two.

## Implementation notes

The comparison of pulled-back sections is proved once at free variables
(`sectionTransportIso_pullbackSection`) and instantiated at the twists: written directly for the
twists of Tag 01NR, the composite has two spellings of the same module (`pbAlgS` and
`Scheme.Modules.pullback`) which `rw` cannot match and whose definitional comparison exceeds the
recursion budget.

## References

* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra GluedTwistAlgebra.twistDataOfGradedAlgebra)
open AlgebraicGeometry.Scheme.Modules (pullbackSection)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

section Algebra

variable {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']
  {M N M' Q : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R' M'] [AddCommGroup Q] [Module R' Q]

/-- **The kernel of a map commutes with flat base change, read through an injection.**  Let
`R ⟶ R'` be flat, `φ : M ⟶ N` an `R`-linear map, `r : M ⟶ M'` an additive map into an
`R'`-module, semilinear along `R ⟶ R'`, whose image spans it, and `φ' : M' ⟶ Q` an `R'`-linear
map such that `φ' ∘ r` is `m ↦ β(1 ⊗ φ m)` for an injective `R'`-linear `β : R' ⊗_R N ⟶ Q`.  Then
the kernel of `φ'` is spanned over `R'` by the image under `r` of the kernel of `φ`. -/
theorem ker_le_span_image_of_flat [Module.Flat R R'] (φ : M →ₗ[R] N) (r : M → M')
    (hr_add : ∀ m m', r (m + m') = r m + r m')
    (hr_smul : ∀ (c : R) (m : M), r (c • m) = algebraMap R R' c • r m)
    (φ' : M' →ₗ[R'] Q) (β : R' ⊗[R] N →ₗ[R'] Q) (hβ : Function.Injective β)
    (hspan : ∀ x : M', x ∈ Submodule.span R' (Set.range r))
    (hcomp : ∀ m, φ' (r m) = β ((1 : R') ⊗ₜ[R] φ m)) :
    LinearMap.ker φ' ≤ Submodule.span R' (r '' (LinearMap.ker φ : Set M)) := by
  let : Module R M' := Module.compHom M' (algebraMap R R')
  have : IsScalarTower R R' M' :=
    ⟨fun c b m => by
      show (c • b) • m = algebraMap R R' c • b • m
      rw [Algebra.smul_def, mul_smul]⟩
  let rL : M →ₗ[R] M' := { toFun := r, map_add' := hr_add, map_smul' := hr_smul }
  intro x hx
  let θ : R' ⊗[R] M →ₗ[R'] M' := rL.liftBaseChange R'
  have hθ : ∀ (b : R') (m : M), θ (b ⊗ₜ[R] m) = b • r m := fun _ _ => rfl
  -- every element of `M'` is in the range of `θ`
  have hrange : Submodule.span R' (Set.range r) ≤ LinearMap.range θ := by
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact ⟨(1 : R') ⊗ₜ[R] m, by rw [hθ, one_smul]⟩
  obtain ⟨t, rfl⟩ := hrange (hspan x)
  -- the square `φ' ∘ θ = β ∘ (R' ⊗ φ)`
  have hsq : ∀ s : R' ⊗[R] M, φ' (θ s) = β (φ.baseChange R' s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      rw [hθ, map_smul, hcomp, LinearMap.baseChange_tmul, ← map_smul, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one]
    | add s s' hs hs' => rw [map_add, map_add, hs, hs', map_add, map_add]
  have h0 : φ.baseChange R' t = 0 := hβ (by rw [← hsq, map_zero]; exact hx)
  -- flatness: `t` comes from `R' ⊗ ker φ`
  have hex : Function.Exact ((LinearMap.ker φ).subtype.lTensor R') (φ.lTensor R') :=
    Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_ker_map φ)
  have h0' : φ.lTensor R' t = 0 := by
    rwa [← LinearMap.baseChange_eq_ltensor]
  obtain ⟨s, rfl⟩ := (hex t).1 h0'
  clear h0 h0' hx
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b k =>
    rw [LinearMap.lTensor_tmul, hθ]
    exact Submodule.smul_mem _ b (Submodule.subset_span ⟨k, k.2, rfl⟩)
  | add s s' hs hs' =>
    rw [map_add, map_add]
    exact add_mem hs hs'

end Algebra

section Descent

/-- **An element killed by a jointly surjective family of flat base changes is zero.**  Let
`R ⟶ R'_j` be flat ring maps whose spectra jointly cover `Spec R`, and `n` an element of an
`R`-module with `1 ⊗ n = 0` in every `R'_j ⊗_R N`.  Then `n = 0`: the cyclic submodule `R n` is
`R/I` for `I` the annihilator, its base changes `R'_j/IR'_j` embed into `R'_j ⊗ N` by flatness and
vanish, so `I` lies in no prime of any `R'_j`, hence in no prime of `R`. -/
theorem eq_zero_of_forall_one_tmul_eq_zero {R : Type*} [CommRing R] {ι : Type*}
    (R' : ι → Type*) [∀ j, CommRing (R' j)] [∀ j, Algebra R (R' j)] [∀ j, Module.Flat R (R' j)]
    (hsurj : ∀ p : Ideal R, p.IsPrime → ∃ j, ∃ q : Ideal (R' j), q.IsPrime ∧
      q.comap (algebraMap R (R' j)) = p)
    {N : Type*} [AddCommGroup N] [Module R N] (n : N)
    (h : ∀ j, (1 : R' j) ⊗ₜ[R] n = 0) : n = 0 := by
  classical
  by_contra hn
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R N n)
  have hI : I ≠ ⊤ := by
    intro hI
    have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    exact hn (by simpa [I] using h1)
  obtain ⟨p, hpmax, hIp⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨j, q, hqp, hq⟩ := hsurj p hpmax.isPrime
  -- the map `R/I ⟶ N`, `c ↦ c • n`, is injective
  let κ : (R ⧸ I) →ₗ[R] N := (Submodule.subtype _).comp
    (LinearMap.toSpanSingleton R N n).quotKerEquivRange.toLinearMap
  have hκ : Function.Injective κ := by
    simp only [κ, LinearMap.coe_comp, LinearEquiv.coe_coe]
    exact Subtype.val_injective.comp (LinearEquiv.injective _)
  have hκ1 : κ (Submodule.Quotient.mk 1) = n := by
    show (LinearMap.toSpanSingleton R N n) 1 = n
    simp
  have hinj : Function.Injective (κ.lTensor (R' j)) :=
    Module.Flat.lTensor_preserves_injective_linearMap κ hκ
  have hzero : (1 : R' j) ⊗ₜ[R] (Submodule.Quotient.mk 1 : R ⧸ I) = 0 :=
    hinj (by rw [LinearMap.lTensor_tmul, hκ1, map_zero]; exact h j)
  -- so `1 ∈ I R'_j`
  have hmem : (1 : R' j) ∈ I.map (algebraMap R (R' j)) := by
    have := congrArg (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (R' j) I).symm hzero
    change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (R' j) I).symm
      ((1 : R' j) ⊗ₜ[R] (Ideal.Quotient.mk I 1)) = _ at this
    rw [map_zero, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul] at this
    have h1 := (Submodule.Quotient.mk_eq_zero _).1 this
    rwa [one_smul] at h1
  have hle : I.map (algebraMap R (R' j)) ≤ q := by
    rwa [Ideal.map_le_iff_le_comap, hq]
  exact hqp.ne_top ((Ideal.eq_top_iff_one _).2 (hle hmem))

end Descent

/-! ### The equation section of a homogeneous section -/

section Equation

variable {T : Scheme.{u}} (A : SheafGradedAlgebra T) {Z : Scheme.{u}}
  (i : Z ⟶ (relativeProj A).scheme)

/-- **The restriction to `Z` of the section of `𝒪(n)` named by a global section of `𝒜_n`**: Tag
01NR's `ψ`, followed by the pullback along `i`, over the whole of `Z`.  A section is an equation
for `Z` exactly when this vanishes (`twistEquationSection_eq_zero_iff`). -/
def twistEquationSection (n : ℕ) (a : (A.piece (n : ℤ)).val.obj (op ⊤)) :
    ((Scheme.Modules.pullback i).obj ((Tag07ZGTwist.twistAlgebra A).piece (n : ℤ))).val.obj
      (op ⊤) :=
  pullbackSection i ((Tag07ZGTwist.twistAlgebra A).piece (n : ℤ))
    ((relativeProj A).toBase ⁻¹ᵁ ⊤) ⊤ (fun _ _ => trivial)
    (((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ n).val.app (op ⊤) a)

/-- **A global section is an equation for `Z` exactly when its equation section vanishes.** -/
theorem twistEquationSection_eq_zero_iff [IsClosedImmersion i]
    [QuasiCompact (relativeProj A).toBase] (n : ℕ) (a : (A.piece (n : ℤ)).val.obj (op ⊤)) :
    twistEquationSection A i n a = 0 ↔
      a ∈ ((twistKerGradedIdeal A (GluedTwistAlgebra.twistDataOfGradedAlgebra A) i).piece
        (n : ℤ)).toSubmodule.obj (op ⊤) :=
  (mem_twistKerGradedIdeal_iff A _ i n ⊤ a).symm

end Equation

/-! ### Transport of pulled-back sections along a commutative square, at free variables -/

section GenericTransport

variable {T T' P P₁ Z Z₁ : Scheme.{u}} (g : T' ⟶ T) (p : P ⟶ T) (p₁ : P₁ ⟶ T') (pc : P₁ ⟶ P)
  (hpcT : pc ≫ p = p₁ ≫ g) {O : P.Modules} {O₁ : P₁.Modules}
  (i : Z ⟶ P) (i₁ : Z₁ ⟶ P₁) (z : Z₁ ⟶ Z) (hz : z ≫ i = i₁ ≫ pc)

/-- **The comparison `z^*(i^*O) ≅ i₁^*O₁` along a square `z ≫ i = i₁ ≫ pc`**, for an isomorphism
`tw : pc^*O ≅ O₁`: the composition comparisons, followed by `i₁^*tw`. -/
def sectionTransportIso (tw : (Scheme.Modules.pullback pc).obj O ≅ O₁) :
    (Scheme.Modules.pullback z).obj ((Scheme.Modules.pullback i).obj O) ≅
      (Scheme.Modules.pullback i₁).obj O₁ :=
  (Scheme.Modules.pullbackComp z i).app _ ≪≫ (Scheme.Modules.pullbackCongr hz).app _ ≪≫
    ((Scheme.Modules.pullbackComp i₁ pc).app _).symm ≪≫ (Scheme.Modules.pullback i₁).mapIso tw

/-- **The comparison carries `z^*` of a pulled-back homogeneous section to the pulled-back
homogeneous section of the base change.**  If `tw` carries the base change of `ψ` to `ψ₁` after
`Φk`, and `Φk(x) = g^*a`, then the comparison sends `z^*(i^*ψ(a))` to `i₁^*ψ₁(x)`. -/
theorem sectionTransportIso_pullbackSection (tw : (Scheme.Modules.pullback pc).obj O ≅ O₁)
    {M : T.Modules} {M₁ : T'.Modules} (ψ : M ⟶ (Scheme.Modules.pushforward p).obj O)
    (ψ₁ : M₁ ⟶ (Scheme.Modules.pushforward p₁).obj O₁) (Φk : M₁ ⟶ (Scheme.Modules.pullback g).obj M)
    (hψ : Φk ≫ basePsi p p₁ g pc hpcT ψ ≫ (Scheme.Modules.pushforward p₁).map tw.hom = ψ₁)
    (a : M.val.obj (op ⊤)) (x : M₁.val.obj (op ⊤))
    (hx : Φk.val.app (op ⊤) x = pullbackSection g M ⊤ ⊤ (fun _ _ => trivial) a) :
    (sectionTransportIso pc i i₁ z hz tw).hom.val.app (op ⊤)
        (pullbackSection z ((Scheme.Modules.pullback i).obj O) ⊤ ⊤ (fun _ _ => trivial)
          (pullbackSection i O (p ⁻¹ᵁ ⊤) ⊤ (fun _ _ => trivial) (ψ.val.app (op ⊤) a))) =
      pullbackSection i₁ O₁ (p₁ ⁻¹ᵁ ⊤) ⊤ (fun _ _ => trivial) (ψ₁.val.app (op ⊤) x) := by
  have h1 := Scheme.Modules.pullbackSection_comp z i O (p ⁻¹ᵁ ⊤) ⊤ ⊤
    (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (ψ.val.app (op ⊤) a)
  have h2 := Scheme.Modules.pullbackSection_congr hz O (p ⁻¹ᵁ ⊤) ⊤
    (fun _ _ => trivial) (fun _ _ => trivial) (ψ.val.app (op ⊤) a)
  have h3 := Scheme.Modules.pullbackSection_comp i₁ pc O (p ⁻¹ᵁ ⊤) (p₁ ⁻¹ᵁ ⊤) ⊤
    (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (ψ.val.app (op ⊤) a)
  have h3' : ((Scheme.Modules.pullbackComp i₁ pc).inv.app O).val.app (op ⊤)
      (pullbackSection (i₁ ≫ pc) O (p ⁻¹ᵁ ⊤) ⊤ (fun _ _ => trivial) (ψ.val.app (op ⊤) a)) =
      pullbackSection i₁ ((Scheme.Modules.pullback pc).obj O) (p₁ ⁻¹ᵁ ⊤) ⊤
        (fun _ _ => trivial) (pullbackSection pc O (p ⁻¹ᵁ ⊤) (p₁ ⁻¹ᵁ ⊤) (fun _ _ => trivial)
          (ψ.val.app (op ⊤) a)) := by
    rw [← h3]
    exact Stacks.SheafOfModules.inv_val_app_hom_val_app
      ((Scheme.Modules.pullbackComp i₁ pc).app O) _ _
  have h4 := Scheme.Modules.pullbackSection_naturality i₁ tw.hom (p₁ ⁻¹ᵁ ⊤) ⊤
    (fun _ _ => trivial)
    (pullbackSection pc O (p ⁻¹ᵁ ⊤) (p₁ ⁻¹ᵁ ⊤) (fun _ _ => trivial) (ψ.val.app (op ⊤) a))
  have h5 := basePsi_pullbackSection p p₁ g pc hpcT ψ ⊤ ⊤ (fun _ _ => trivial)
    (fun _ _ => trivial) a
  have hkey : tw.hom.val.app (op (p₁ ⁻¹ᵁ ⊤))
      (pullbackSection pc O (p ⁻¹ᵁ ⊤) (p₁ ⁻¹ᵁ ⊤) (fun _ _ => trivial) (ψ.val.app (op ⊤) a)) =
      ψ₁.val.app (op ⊤) x := by
    rw [← h5, ← hx, ← hψ]
    rfl
  show ((Scheme.Modules.pullback i₁).map tw.hom).val.app (op ⊤)
    (((Scheme.Modules.pullbackComp i₁ pc).inv.app O).val.app (op ⊤)
      (((Scheme.Modules.pullbackCongr hz).hom.app O).val.app (op ⊤)
        (((Scheme.Modules.pullbackComp z i).hom.app O).val.app (op ⊤) _))) = _
  rw [h1, h2, h3', h4, hkey]

end GenericTransport

/-! ### Transport of equation sections along a base change -/

section Transport

variable {T T' : Scheme.{u}} (g : T' ⟶ T) (A : SheafGradedAlgebra T) {A₁ : SheafGradedAlgebra T'}
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A₁)
    (situationAlgebra (A.pullback g)))
  (hΦ : ∀ n : ℤ, IsIso (Φ.app n))
  (pc : (relativeProj A₁).scheme ⟶ (relativeProj A).scheme)
  (hpc : pc = (relativeProjCongr Φ hΦ).hom ≫ baseChangeHom A g)
  {Z Z₁ : Scheme.{u}} (i : Z ⟶ (relativeProj A).scheme) (i₁ : Z₁ ⟶ (relativeProj A₁).scheme)
  (z : Z₁ ⟶ Z) (hz : z ≫ i = i₁ ≫ pc)

/-- **The comparison `z^*(i^*𝒪(n)) ≅ i₁^*𝒪₁(n)`** of the restricted twists on `Z₁`: the
composition comparisons along `z ≫ i = i₁ ≫ pc`, followed by `i₁^*` of the comparison of twists
of Stacks 084B (3) (`congrBaseChangeTwistIso`). -/
def twistEquationTransport (n : ℤ) :
    (Scheme.Modules.pullback z).obj
        ((Scheme.Modules.pullback i).obj ((Tag07ZGTwist.twistAlgebra A).piece n)) ≅
      (Scheme.Modules.pullback i₁).obj ((Tag07ZGTwist.twistAlgebra A₁).piece n) :=
  sectionTransportIso pc i i₁ z hz (O := (Tag07ZGTwist.twistAlgebra A).piece n)
    (ProjRepresentsF1.gradedAlgebraIsoApp (congrBaseChangeTwistIso A g Φ hΦ pc hpc) n)

/-- **The comparison carries the base change of an equation section to the equation section of
the base change.**  If `x` is a global section of `𝒜₁_n` with `Φ(x) = g^*a`, then the
comparison sends `z^*` of the equation section of `a` to the equation section of `x`. -/
theorem twistEquationTransport_pullbackSection (n : ℕ) (a : (A.piece (n : ℤ)).val.obj (op ⊤))
    (x : (A₁.piece (n : ℤ)).val.obj (op ⊤))
    (hx : (Φ.app (n : ℤ)).val.app (op ⊤) x =
      pullbackSection g (A.piece (n : ℤ)) ⊤ ⊤ (fun _ _ => trivial) a) :
    (twistEquationTransport g A Φ hΦ pc hpc i i₁ z hz (n : ℤ)).hom.val.app (op ⊤)
        (pullbackSection z _ ⊤ ⊤ (fun _ _ => trivial) (twistEquationSection A i n a)) =
      twistEquationSection A₁ i₁ n x := by
  have hpcT : pc ≫ (relativeProj A).toBase = (relativeProj A₁).toBase ≫ g := by
    rw [hpc, Category.assoc, baseChangeHom_comp_toBase, ← Category.assoc,
      relativeProjCongr_hom_comp_toBase]
  exact sectionTransportIso_pullbackSection g (relativeProj A).toBase (relativeProj A₁).toBase pc
    hpcT i i₁ z hz (O := (Tag07ZGTwist.twistAlgebra A).piece n)
    (O₁ := (Tag07ZGTwist.twistAlgebra A₁).piece n)
    (ProjRepresentsF1.gradedAlgebraIsoApp (congrBaseChangeTwistIso A g Φ hΦ pc hpc) n)
    ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ n)
    ((GluedTwistAlgebra.twistDataOfGradedAlgebra A₁).ψ n) (Φ.app (n : ℤ))
    ((Category.assoc _ _ _).symm.trans
      (congrBaseChangePsi_comp_congrBaseChangeTwistIso A g Φ hΦ pc hpc hpcT n)) a x hx

end Transport

section FlatBaseChange

open Stacks.AlgebraicGeometry.FlatBaseChangeCohomology (baseModule_eq_instModule
  baseModule_id_eq_instModule appLE_top_eq_app appLE_top_id)
open Stacks.AlgebraicGeometry.SectionsBaseChange (baseAlgebra baseModule le_preimage_top
  pullbackSectionsHom pullbackSectionsHom_apply)

variable {T T' : Scheme.{u}} (g : T' ⟶ T) (A : SheafGradedAlgebra T) {A₁ : SheafGradedAlgebra T'}
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A₁)
    (situationAlgebra (A.pullback g)))
  (hΦ : ∀ n : ℤ, IsIso (Φ.app n))
  (pc : (relativeProj A₁).scheme ⟶ (relativeProj A).scheme)
  (hpc : pc = (relativeProjCongr Φ hΦ).hom ≫ baseChangeHom A g)
  {Z Z₁ : Scheme.{u}} (i : Z ⟶ (relativeProj A).scheme) (i₁ : Z₁ ⟶ (relativeProj A₁).scheme)
  (z : Z₁ ⟶ Z)

include hpc in
/-- The square of Stacks 084B (3): `Proj_{T'}(𝒜₁) = T' ×_T Proj_T(𝒜)` through `pc`. -/
theorem isPullback_comparison :
    IsPullback pc (relativeProj A₁).toBase (relativeProj A).toBase g := by
  have h₁ : IsPullback (relativeProjCongr Φ hΦ).hom (relativeProj A₁).toBase
      (relativeProj (A.pullback g)).toBase (𝟙 T') :=
    IsPullback.of_horiz_isIso ⟨by rw [relativeProjCongr_hom_comp_toBase, Category.comp_id]⟩
  have h := h₁.paste_horiz (isPullback_baseChangeHom A g)
  rwa [Category.id_comp, ← hpc] at h

/-- Pulling global sections back along `g` is semilinear along `Γ(T) ⟶ Γ(T')`. -/
theorem pullbackSectionsHom_top_smul (F : T.Modules) (c : Γ(T, ⊤)) (a : Γ(F, ⊤)) :
    pullbackSectionsHom g F ⊤ ⊤ (le_preimage_top g ⊤) (c • a) =
      (g.appLE ⊤ ⊤ (le_preimage_top g ⊤)).hom c •
        pullbackSectionsHom g F ⊤ ⊤ (le_preimage_top g ⊤) a := by
  have h : Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections g F ⊤ (c • a) =
      (g.appLE ⊤ (g ⁻¹ᵁ ⊤) le_rfl).hom c •
        Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections g F ⊤ a := by
    rw [Scheme.Hom.appLE_preimage_self]
    exact Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections_smul g F ⊤ c a
  rwa [Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackSectionsHom_top,
    Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackSectionsHom_top]

/-- An isomorphism of modules is injective on global sections. -/
theorem injective_app_top_of_isIso {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) [IsIso f] :
    Function.Injective (Scheme.Modules.Hom.app f ⊤) := by
  intro z₁ z₂ h
  have key : ∀ z, Scheme.Modules.Hom.app (inv f) ⊤ (Scheme.Modules.Hom.app f ⊤ z) = z :=
    fun z => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, IsIso.hom_inv_id,
      Scheme.Modules.Hom.id_app]
    rfl
  rw [← key z₁, h, key]

include hpc in
/-- **The comparison of the two degreewise maps along a flat base change of affine bases**:
there is an injective `Γ(T')`-linear map `β : Γ(T') ⊗_{Γ(T)} Γ(Z, i^*𝒪(n)) ⟶ Γ(Z₁, i₁^*𝒪₁(n))`
carrying `1 ⊗ (equation section of a)` to the equation section of every `x` with `Φ(x) = g^*a`.
It is Stacks 02KH in degree zero for `Z ⟶ T` followed by the comparison of twists of
Stacks 084B (3). -/
theorem exists_injective_twistEquation_baseChange [IsAffine T] [IsAffine T'] [Flat g]
    [QuasiCompact (relativeProj A).toBase] [IsClosedImmersion i]
    (hsq : IsPullback z i₁ i pc) (n : ℕ) :
    letI : Algebra Γ(T, ⊤) Γ(T', ⊤) := baseAlgebra g
    ∃ β : Γ(T', ⊤) ⊗[Γ(T, ⊤)]
        Γ(twistTarget A (GluedTwistAlgebra.twistDataOfGradedAlgebra A) i n, ⊤) →ₗ[Γ(T', ⊤)]
        Γ(twistTarget A₁ (GluedTwistAlgebra.twistDataOfGradedAlgebra A₁) i₁ n, ⊤),
      Function.Injective β ∧ ∀ (a : Γ(A.piece (n : ℤ), ⊤)) (x : Γ(A₁.piece (n : ℤ), ⊤)),
        Scheme.Modules.sectionsLinearMap (M := A₁.piece (n : ℤ))
          (N := (Scheme.Modules.pullback g).obj (A.piece (n : ℤ))) (Φ.app (n : ℤ)) ⊤ x =
          pullbackSectionsHom g (A.piece (n : ℤ)) ⊤ ⊤ (le_preimage_top g ⊤) a →
        Scheme.Modules.sectionsLinearMap
            (twistRestrictMapNat A₁ (GluedTwistAlgebra.twistDataOfGradedAlgebra A₁) i₁ n) ⊤ x =
          β ((1 : Γ(T', ⊤)) ⊗ₜ[Γ(T, ⊤)] Scheme.Modules.sectionsLinearMap
            (twistRestrictMapNat A (GluedTwistAlgebra.twistDataOfGradedAlgebra A) i n) ⊤ a) := by
  let : Algebra Γ(T, ⊤) Γ(T', ⊤) := baseAlgebra g
  classical
  have : Module.Flat Γ(T, ⊤) Γ(T', ⊤) :=
    Flat.flat_appLE g (isAffineOpen_top T) (isAffineOpen_top T') (le_preimage_top g ⊤)
  have H : IsPullback z (i₁ ≫ (relativeProj A₁).toBase) (i ≫ (relativeProj A).toBase) g :=
    hsq.paste_vert (isPullback_comparison g A Φ hΦ pc hpc)
  have : IsSeparated (relativeProj A).toBase :=
    Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_toBase A (relativeProj A)
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (i ≫ (relativeProj A).toBase)
  have : QuasiSeparatedSpace Z :=
    quasiSeparatedSpace_of_quasiSeparated (i ≫ (relativeProj A).toBase)
  have : ((Scheme.Modules.pullback i).obj
      ((Tag07ZGTwist.twistAlgebra A).piece (n : ℤ))).IsQuasicoherent :=
    Stacks.Conormal.gradedPullback_isQuasicoherent i
      (GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra
      (fun m => (GluedTwistAlgebra.twistDataOfGradedAlgebra A).isQuasicoherent m) (n : ℤ)
  -- Stacks 02KH in degree zero for `Z ⟶ T`
  let : Module Γ(T, ⊤) Γ((Scheme.Modules.pullback i).obj
      ((Tag07ZGTwist.twistAlgebra A).piece (n : ℤ)), ⊤) :=
    (inferInstance : Module Γ(T, ⊤)
      Γ(twistTarget A (GluedTwistAlgebra.twistDataOfGradedAlgebra A) i n, ⊤))
  obtain ⟨e, he⟩ := AlgebraicGeometry.SmallEtale.exists_linearEquiv_sections_baseChange_of_eq H
    ((Scheme.Modules.pullback i).obj ((Tag07ZGTwist.twistAlgebra A).piece (n : ℤ))) rfl
    (mod := inferInstance)
    ((show (inferInstance : Module Γ(T, ⊤) Γ((Scheme.Modules.pullback i).obj
        ((Tag07ZGTwist.twistAlgebra A).piece (n : ℤ)), ⊤)) =
      inferInstanceAs (Module ↑Γ(T, (⊤ : T.Opens))
        ↑Γ((Scheme.Modules.pushforward (i ≫ (relativeProj A).toBase)).obj
          ((Scheme.Modules.pullback i).obj ((Tag07ZGTwist.twistAlgebra A).piece (n : ℤ))),
          (⊤ : T.Opens))) from rfl).trans
      (baseModule_eq_instModule (i ≫ (relativeProj A).toBase)
        ((Scheme.Modules.pullback i).obj ((Tag07ZGTwist.twistAlgebra A).piece (n : ℤ)))).symm)
  -- the two degreewise maps, as linear maps on global sections
  let φL := Scheme.Modules.sectionsLinearMap
    (twistRestrictMapNat A (GluedTwistAlgebra.twistDataOfGradedAlgebra A) i n) ⊤
  let φ₁L := Scheme.Modules.sectionsLinearMap
    (twistRestrictMapNat A₁ (GluedTwistAlgebra.twistDataOfGradedAlgebra A₁) i₁ n) ⊤
  have hz : z ≫ i = i₁ ≫ pc := hsq.w
  -- the comparison of the restricted twists, as a linear map
  let Θ := (twistEquationTransport g A Φ hΦ pc hpc i i₁ z hz (n : ℤ)).hom
  let : Module Γ(T', ⊤) Γ((Scheme.Modules.pullback z).obj
      ((Scheme.Modules.pullback i).obj ((Tag07ZGTwist.twistAlgebra A).piece (n : ℤ))), ⊤) :=
    baseModule (i₁ ≫ (relativeProj A₁).toBase) _ ⊤
  have hring : ∀ b : Γ(T', ⊤),
      ((i₁ ≫ (relativeProj A₁).toBase).appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom b =
        (i₁.app ((relativeProj A₁).toBase ⁻¹ᵁ ⊤)).hom (((relativeProj A₁).toBase.app ⊤).hom b) :=
    fun b => congrArg (fun t => t.hom b) (appLE_top_eq_app (i₁ ≫ (relativeProj A₁).toBase))
  let ΘL : Γ((Scheme.Modules.pullback z).obj
      ((Scheme.Modules.pullback i).obj ((Tag07ZGTwist.twistAlgebra A).piece (n : ℤ))), ⊤)
        →ₗ[Γ(T', ⊤)]
      Γ(twistTarget A₁ (GluedTwistAlgebra.twistDataOfGradedAlgebra A₁) i₁ n, ⊤) :=
    { toFun := fun y => Scheme.Modules.Hom.app Θ ⊤ y
      map_add' := fun y y' => map_add _ y y'
      map_smul' := fun b y => by
        show Scheme.Modules.Hom.app Θ ⊤
            (((i₁ ≫ (relativeProj A₁).toBase).appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom b • y) =
          (show Γ(Z₁, ⊤) from (i₁.app ((relativeProj A₁).toBase ⁻¹ᵁ ⊤)).hom
            (((relativeProj A₁).toBase.app ⊤).hom b)) • Scheme.Modules.Hom.app Θ ⊤ y
        rw [Scheme.Modules.Hom.app_smul, hring] }
  have hΘinj : Function.Injective ΘL := by
    have : IsIso Θ := inferInstance
    exact injective_app_top_of_isIso Θ
  refine ⟨ΘL ∘ₗ e.toLinearMap, hΘinj.comp e.injective, fun a x hx => ?_⟩
  have ht := twistEquationTransport_pullbackSection g A Φ hΦ pc hpc i i₁ z hz n a x hx
  show φ₁L x = ΘL (e ((1 : Γ(T', ⊤)) ⊗ₜ[Γ(T, ⊤)] φL a))
  exact (((twistRestrictMapNat_app A₁ _ i₁ n ⊤ x).trans ht.symm).trans
    (congrArg (fun w => ΘL (pullbackSectionsHom z _ ⊤ ⊤ (le_preimage_top z ⊤) w))
      (twistRestrictMapNat_app A _ i n ⊤ a).symm)).trans
    (congrArg ΘL ((he 1 (φL a)).trans (one_smul _ _))).symm

include hpc in
/-- **Flat base change of the equations of a closed subscheme of a relative Proj.**  Let
`g : T' ⟶ T` be a flat morphism of affine schemes, `Φ : 𝒜₁ ≅ g^*𝒜` and
`pc : Proj_{T'}(𝒜₁) ⟶ Proj_T(𝒜)` the base-change morphism of Stacks 084B (3), `i : Z ⟶ Proj_T(𝒜)`
a closed immersion with `Proj_T(𝒜) ⟶ T` quasi-compact, and `Z₁ = Z ×_{Proj_T(𝒜)} Proj_{T'}(𝒜₁)`.
For `r : Γ(𝒜_n) ⟶ Γ(𝒜₁_n)` the restriction (`Φ ∘ r = g^*`), every global equation for `Z₁` in
degree `n` is a `Γ(T')`-combination of restrictions of global equations for `Z`.

This is Stacks 02KH in degree zero for `Z ⟶ T` (`exists_linearEquiv_sections_baseChange`),
transported along the comparison of twists of Stacks 084B (3)
(`twistEquationTransport_pullbackSection`), and the flatness of `Γ(T) ⟶ Γ(T')`
(`ker_le_span_image_of_flat`). -/
theorem mem_span_of_twistEquationSection_eq_zero [IsAffine T] [IsAffine T'] [Flat g]
    [QuasiCompact (relativeProj A).toBase] [IsClosedImmersion i]
    (hsq : IsPullback z i₁ i pc) (n : ℕ)
    (r : Γ(A.piece (n : ℤ), ⊤) → Γ(A₁.piece (n : ℤ), ⊤))
    (hr : ∀ a, Scheme.Modules.sectionsLinearMap (M := A₁.piece (n : ℤ))
      (N := (Scheme.Modules.pullback g).obj (A.piece (n : ℤ))) (Φ.app (n : ℤ)) ⊤ (r a) =
      pullbackSectionsHom g (A.piece (n : ℤ)) ⊤ ⊤ (le_preimage_top g ⊤) a)
    (x : Γ(A₁.piece (n : ℤ), ⊤)) (hx : twistEquationSection A₁ i₁ n x = 0) :
    x ∈ Submodule.span Γ(T', ⊤) (r '' {a | twistEquationSection A i n a = 0}) := by
  classical
  let : Algebra Γ(T, ⊤) Γ(T', ⊤) := baseAlgebra g
  have : Module.Flat Γ(T, ⊤) Γ(T', ⊤) :=
    Flat.flat_appLE g (isAffineOpen_top T) (isAffineOpen_top T') (le_preimage_top g ⊤)
  obtain ⟨β, hβ, hβc⟩ := exists_injective_twistEquation_baseChange g A Φ hΦ pc hpc i i₁ z hsq n
  let φL := Scheme.Modules.sectionsLinearMap
    (twistRestrictMapNat A (GluedTwistAlgebra.twistDataOfGradedAlgebra A) i n) ⊤
  let φ₁L := Scheme.Modules.sectionsLinearMap
    (twistRestrictMapNat A₁ (GluedTwistAlgebra.twistDataOfGradedAlgebra A₁) i₁ n) ⊤
  -- the restriction map is additive and semilinear
  let ΦL := Scheme.Modules.sectionsLinearMap (M := A₁.piece (n : ℤ))
    (N := (Scheme.Modules.pullback g).obj (A.piece (n : ℤ))) (Φ.app (n : ℤ)) ⊤
  have hΦinj : Function.Injective ΦL := by
    exact @injective_app_top_of_isIso _ _ _ (Φ.app (n : ℤ)) (hΦ (n : ℤ))
  have r_add : ∀ a a', r (a + a') = r a + r a' := fun a a' => hΦinj <|
    (hr _).trans ((map_add _ a a').trans ((congrArg₂ (· + ·) (hr a).symm (hr a').symm).trans
      (map_add ΦL _ _).symm))
  have r_smul : ∀ (c : Γ(T, ⊤)) (a : Γ(A.piece (n : ℤ), ⊤)),
      r (c • a) = algebraMap Γ(T, ⊤) Γ(T', ⊤) c • r a := fun c a => hΦinj <|
    (hr _).trans ((pullbackSectionsHom_top_smul g (A.piece (n : ℤ)) c a).trans
      ((congrArg (fun y => (g.appLE ⊤ ⊤ (le_preimage_top g ⊤)).hom c • y) (hr a).symm).trans
        (ΦL.map_smul _ (r a)).symm))
  -- the global sections of `𝒜₁_n` are spanned by the restrictions
  have : (A.piece (n : ℤ)).IsQuasicoherent := A.isQuasicoherent (n : ℤ)
  obtain ⟨e₀, he₀⟩ := AlgebraicGeometry.SmallEtale.exists_linearEquiv_sections_baseChange_of_eq
    (IsPullback.of_id_snd (f := g)) (A.piece (n : ℤ)) rfl (mod := inferInstance)
    (baseModule_id_eq_instModule (A.piece (n : ℤ))).symm
  have hspan : ∀ y : Γ(A₁.piece (n : ℤ), ⊤), y ∈ Submodule.span Γ(T', ⊤) (Set.range r) := by
    intro y
    let S := (Submodule.span Γ(T', ⊤) (Set.range r)).map ΦL
    have hS : ∀ t, e₀ t ∈ S := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero =>
        rw [map_zero]
        exact zero_mem S
      | tmul b a =>
        rw [he₀]
        convert S.smul_mem b (Submodule.mem_map_of_mem (Submodule.subset_span ⟨a, rfl⟩)) using 1
        rw [hr a]
        exact congrArg (fun t : Γ(T', ⊤) ⟶ Γ(T', ⊤) => t.hom b •
          pullbackSectionsHom g (A.piece (n : ℤ)) ⊤ ⊤ (le_preimage_top g ⊤) a) (appLE_top_id T')
      | add t t' ht ht' =>
        rw [map_add]
        exact add_mem ht ht'
    obtain ⟨t, ht⟩ := e₀.surjective (ΦL y)
    obtain ⟨y', hy', hy'eq⟩ := hS t
    exact hΦinj (hy'eq.trans ht) ▸ hy'
  have hker := ker_le_span_image_of_flat φL r r_add r_smul φ₁L β hβ hspan
    (fun a => hβc a (r a) (hr a))
  have hxk : x ∈ LinearMap.ker φ₁L := (twistRestrictMapNat_app A₁ _ i₁ n ⊤ x).trans hx
  refine Submodule.span_mono ?_ (hker hxk)
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a, (twistRestrictMapNat_app A _ i n ⊤ a).symm.trans ha, rfl⟩

include hpc in
/-- **Equations restrict to equations** along the base change of Stacks 084B (3): if `a` is an
equation for `Z` and `Φ(x) = g^*a`, then `x` is an equation for `Z₁`.  No flatness is needed. -/
theorem twistEquationSection_eq_zero_of_restrict (hz : z ≫ i = i₁ ≫ pc) (n : ℕ)
    (a : Γ(A.piece (n : ℤ), ⊤)) (x : Γ(A₁.piece (n : ℤ), ⊤))
    (hx : Scheme.Modules.sectionsLinearMap (M := A₁.piece (n : ℤ))
      (N := (Scheme.Modules.pullback g).obj (A.piece (n : ℤ))) (Φ.app (n : ℤ)) ⊤ x =
      pullbackSectionsHom g (A.piece (n : ℤ)) ⊤ ⊤ (le_preimage_top g ⊤) a)
    (ha : twistEquationSection A i n a = 0) : twistEquationSection A₁ i₁ n x = 0 := by
  rw [← twistEquationTransport_pullbackSection g A Φ hΦ pc hpc i i₁ z hz n a x hx, ha]
  exact (congrArg _ (map_zero (pullbackSectionsHom z _ ⊤ ⊤ (le_preimage_top z ⊤)))).trans
    (map_zero _)

/-- **Joint surjectivity of a family of morphisms into an affine scheme, read on primes**: every
prime of `Γ(T)` is the contraction of a prime of some `Γ(T_j)`. -/
theorem exists_isPrime_comap_appLE {ι : Type*} [IsAffine T] {Tj : ι → Scheme.{u}}
    (gj : ∀ j, Tj j ⟶ T) (hsurj : ∀ t : T, ∃ j, ∃ t' : Tj j, (gj j).base t' = t)
    (p : Ideal Γ(T, ⊤)) (hp : p.IsPrime) :
    ∃ j, ∃ q : Ideal Γ(Tj j, ⊤), q.IsPrime ∧
      q.comap ((gj j).appLE ⊤ ⊤ (le_preimage_top (gj j) ⊤)).hom = p := by
  let pt : Spec Γ(T, ⊤) := (⟨p, hp⟩ : PrimeSpectrum Γ(T, ⊤))
  obtain ⟨j, t', ht'⟩ := hsurj ((inv T.toSpecΓ).base pt)
  let q : PrimeSpectrum Γ(Tj j, ⊤) := (Tj j).toSpecΓ.base t'
  refine ⟨j, q.asIdeal, q.isPrime, ?_⟩
  have hnat := congrArg (fun f => f.base t') (Scheme.toSpecΓ_naturality (gj j))
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hnat
  rw [ht'] at hnat
  have hpt : T.toSpecΓ.base ((inv T.toSpecΓ).base pt) = pt := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  rw [hpt] at hnat
  rw [appLE_top_eq_app (gj j)]
  exact (congrArg PrimeSpectrum.asIdeal hnat).symm

/-- **Being an equation descends along a jointly surjective family of flat base changes of
affine bases.**  If, for every member `g_j : T_j ⟶ T` of such a family, the restriction of `a`
is an equation for the base change `Z_j` of `Z`, then `a` is an equation for `Z`: the images of
`1 ⊗ (equation section of a)` in the base changes of `Γ(Z, i^*𝒪(n))` vanish
(`exists_injective_twistEquation_baseChange`), so it vanishes
(`eq_zero_of_forall_one_tmul_eq_zero`). -/
theorem twistEquationSection_eq_zero_of_cover [IsAffine T]
    [QuasiCompact (relativeProj A).toBase] [IsClosedImmersion i] {ι : Type*}
    {Tj : ι → Scheme.{u}} [∀ j, IsAffine (Tj j)] (gj : ∀ j, Tj j ⟶ T) [∀ j, Flat (gj j)]
    (hsurj : ∀ t : T, ∃ j, ∃ t' : Tj j, (gj j).base t' = t)
    {Aj : ∀ j, SheafGradedAlgebra (Tj j)}
    (Φj : ∀ j, SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra (Aj j))
      (situationAlgebra (A.pullback (gj j))))
    (hΦj : ∀ j, ∀ n : ℤ, IsIso ((Φj j).app n))
    (pcj : ∀ j, (relativeProj (Aj j)).scheme ⟶ (relativeProj A).scheme)
    (hpcj : ∀ j, pcj j = (relativeProjCongr (Φj j) (hΦj j)).hom ≫ baseChangeHom A (gj j))
    {Zj : ι → Scheme.{u}} (ij : ∀ j, Zj j ⟶ (relativeProj (Aj j)).scheme) (zj : ∀ j, Zj j ⟶ Z)
    (hsqj : ∀ j, IsPullback (zj j) (ij j) i (pcj j)) (n : ℕ) (a : Γ(A.piece (n : ℤ), ⊤))
    (xj : ∀ j, Γ((Aj j).piece (n : ℤ), ⊤))
    (hxj : ∀ j, Scheme.Modules.sectionsLinearMap (M := (Aj j).piece (n : ℤ))
      (N := (Scheme.Modules.pullback (gj j)).obj (A.piece (n : ℤ))) ((Φj j).app (n : ℤ)) ⊤
        (xj j) = pullbackSectionsHom (gj j) (A.piece (n : ℤ)) ⊤ ⊤ (le_preimage_top (gj j) ⊤) a)
    (h0 : ∀ j, twistEquationSection (Aj j) (ij j) n (xj j) = 0) :
    twistEquationSection A i n a = 0 := by
  let : ∀ j, Algebra Γ(T, ⊤) Γ(Tj j, ⊤) := fun j => baseAlgebra (gj j)
  have : ∀ j, Module.Flat Γ(T, ⊤) Γ(Tj j, ⊤) := fun j =>
    Flat.flat_appLE (gj j) (isAffineOpen_top T) (isAffineOpen_top (Tj j))
      (le_preimage_top (gj j) ⊤)
  refine (twistRestrictMapNat_app A _ i n ⊤ a).symm.trans ?_
  refine eq_zero_of_forall_one_tmul_eq_zero (fun j => Γ(Tj j, ⊤))
    (fun p hp => exists_isPrime_comap_appLE gj hsurj p hp)
    (Scheme.Modules.sectionsLinearMap
      (twistRestrictMapNat A (GluedTwistAlgebra.twistDataOfGradedAlgebra A) i n) ⊤ a) fun j => ?_
  obtain ⟨β, hβ, hβc⟩ := exists_injective_twistEquation_baseChange (gj j) A (Φj j) (hΦj j)
    (pcj j) (hpcj j) i (ij j) (zj j) (hsqj j) n
  refine hβ ((hβc a (xj j) (hxj j)).symm.trans ?_)
  exact ((twistRestrictMapNat_app (Aj j) _ (ij j) n ⊤ (xj j)).trans (h0 j)).trans
    (map_zero β).symm

end FlatBaseChange

end Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

end

