module

public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.DirectImageInDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.ProductOfStructureSheavesResolution
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTrace
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingCriterion
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SideCondition

/-!
# The trace map for the affine line is not an isomorphism without the coherator

Let `R` be a ring, `Y = Spec R`, `X = 𝐀¹_R = Spec R[x]` and `f : X ⟶ Y` the structure morphism.
Take `L = 𝒪_X` and `K = 𝒪_Y` in the sheafy trace map of [Stacks, Tag 0B6H],

`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`.

[Stacks, Tag 0GEU] says that the left hand side lies in `D_QCoh(𝒪_Y)`, while the right hand side is
isomorphic to `∏_{n ≥ 0} 𝒪_Y`, which is not quasi-coherent; so the statement of
[Stacks, Tag 0A9Q] fails without the coherator `DQ_Y`.

## Main results

* `Stacks.Duality.AffineLine.derivedPushforward_derivedSheafHom_mem` — the left hand side: for
  every `M` in `D_QCoh(𝒪_X)`, in particular for `M = a(K)`, `Rf_*R𝓗om_{𝒪_X}(𝒪_X, M)` lies in
  `D_QCoh(𝒪_Y)`.
* `Stacks.Duality.AffineLine.derivedSheafHomIso` — the right hand side:
  `R𝓗om_{𝒪_Y}(Rf_*𝒪_X, 𝒪_Y) ≅ ∏_{n ≥ 0} 𝒪_Y`, the product placed in degree zero.
* `Stacks.Duality.AffineLine.not_mem_derivedSheafHom` and
  `Stacks.Duality.AffineLine.isEmpty_iso` — when `∏_{n ≥ 0} 𝒪_Y` is not quasi-coherent, the right
  hand side is not in `D_QCoh(𝒪_Y)`, so it is not isomorphic to the left hand side, and
  `Stacks.Duality.AffineLine.not_isIso_sheafyTrace` — the trace map is not an isomorphism.
* `Stacks.Duality.AffineLine.uncoheratedTrace_example` — **[Stacks, Tag 0GEU]**, in corrected
  form.

## The statement of the source is false for some rings

Tag 0GEU writes `Y = Spec(R)` for an unspecified ring `R`, and asserts that `∏_{n ≥ 0} 𝒪_Y` is not
quasi-coherent. That is false for a field `k`: `Spec k` is a point and the product is
quasi-coherent (`Stacks.Duality.isQuasicoherent_piStructureSheaf_of_isField`). The two other
assertions of the example — the left hand side is in `D_QCoh`, the right hand side is `∏ 𝒪_Y` —
hold for every `R`. What holds about the third is
`Stacks.Duality.isQuasicoherent_piStructureSheaf_iff`: the product is quasi-coherent exactly when
every `t ∈ R` satisfies an equation `t^j = t^{j+1} b`. So the example works precisely for the
rings with an element `t` admitting no such equation, for instance `R = ℤ` with `t = 2`, and for
those the trace map is not an isomorphism.

## Implementation notes

*The derived categories.* Everything is read at `CategoryTheory.HasDerivedCategory.standard`, the
model at which `Stacks.SheafOfModules.derivedSheafHom` and `Stacks.Duality.sheafyTrace` are
stated.

*The left hand side.* It is stated for an arbitrary `M` in `D_QCoh(𝒪_X)` rather than for
`a(𝒪_Y)`; `a(𝒪_Y)` is such an object for whatever right adjoint `a` is used, so this is the
assertion of the source for every choice of `a`. It holds because `R𝓗om(𝒪_X, M) = M` and `Rf_*`
preserves `D_QCoh` along the affine morphism `f`.

*The right hand side.* `Rf_*𝒪_X = f_*𝒪_X` because `f` is affine, and `f_*𝒪_X` is the sheaf
associated to the `R`-module `R[x]`, which is free on the monomials, so `f_*𝒪_X = ⊕_{n ≥ 0} 𝒪_Y`.
Choosing an injective resolution `𝒪_Y → J`, `R𝓗om(⊕_n 𝒪_Y, 𝒪_Y)` is the internal Hom complex
`𝓗om^•(⊕_n 𝒪_Y, J) = ∏_n J` (`AlgebraicGeometry.RingedSite.isLimitFanHomFree`), and `∏_n J` is
a resolution of `∏_n 𝒪_Y` by Serre vanishing on the affine opens
(`Stacks.Duality.ProductResolution.quasiIso_piLiftSingle_cochainComplex`).

## References

* [Stacks Project, Tag 0GEU](https://stacks.math.columbia.edu/tag/0GEU)
* [Stacks Project, Tag 0A9Q](https://stacks.math.columbia.edu/tag/0A9Q)
* [Stacks Project, Tag 0B6H](https://stacks.math.columbia.edu/tag/0B6H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Duality.AffineLine

variable (R : CommRingCat.{u})

/-- The polynomial ring `R[x]`. -/
abbrev polynomialRing : CommRingCat.{u} := CommRingCat.of (Polynomial R)

/-- The affine line `𝐀¹_R = Spec R[x]`. -/
abbrev affineLine : Scheme.{u} := Spec (polynomialRing R)

/-- The structure morphism `𝐀¹_R ⟶ Spec R`. -/
abbrev structureMorphism : affineLine R ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial R)))

/-- `R[x]`, as an `R`-module by restriction of scalars, is free on the monomials: it is the
direct sum of countably many copies of `R`. -/
def polynomialLinearEquiv :
    (ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap R (Polynomial R))).hom).obj
        (ModuleCat.of (polynomialRing R) (polynomialRing R)) ≃ₗ[R]
      DirectSum (ULift.{u} ℕ) (fun _ ↦ (ModuleCat.of R R : ModuleCat.{u} R)) :=
  { ((Polynomial.basisMonomials R).repr.trans
      ((Finsupp.domLCongr Equiv.ulift.symm).trans
        (finsuppLEquivDirectSum R R (ULift.{u} ℕ)))).toAddEquiv with
    map_smul' := fun r p ↦ by
      change ((Polynomial.basisMonomials R).repr.trans
          ((Finsupp.domLCongr Equiv.ulift.symm).trans
            (finsuppLEquivDirectSum R R (ULift.{u} ℕ))))
          (algebraMap R (Polynomial R) r * (show Polynomial R from p)) =
        r • ((Polynomial.basisMonomials R).repr.trans
          ((Finsupp.domLCongr Equiv.ulift.symm).trans
            (finsuppLEquivDirectSum R R (ULift.{u} ℕ)))) (show Polynomial R from p)
      rw [← Algebra.smul_def, map_smul] }

/-- `R[x]`, as an `R`-module, is the coproduct of countably many copies of `R`. -/
def polynomialModuleIso :
    (ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap R (Polynomial R))).hom).obj
        (ModuleCat.of (polynomialRing R) (polynomialRing R)) ≅
      ∐ (fun _ : ULift.{u} ℕ ↦ (ModuleCat.of R R : ModuleCat.{u} R)) :=
  (polynomialLinearEquiv R).toModuleIso ≪≫
    (ModuleCat.coprodIsoDirectSum (fun _ : ULift.{u} ℕ ↦ (ModuleCat.of R R : ModuleCat.{u} R))).symm

/-- **`f_*𝒪_{𝐀¹_R} = ⊕_{n ≥ 0} 𝒪_{Spec R}`.** The direct image of the structure sheaf of the affine
line is the sheaf associated to `R[x] = ⊕_n R`, and the associated sheaf functor, a left adjoint,
preserves the direct sum. -/
def pushforwardStructureSheafIso :
    (pushforwardSheafOfModules (structureMorphism R)).obj
        (SheafOfModules.unit (affineLine R).ringCatSheaf) ≅
      SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} ℕ) :=
  have : PreservesColimitsOfSize.{u, u} (tilde.functor R) :=
    (tilde.adjunction (R := R)).leftAdjoint_preservesColimits
  Scheme.Modules.pushforwardUnitTildeIso (CommRingCat.ofHom (algebraMap R (Polynomial R))) ≪≫
    (tilde.functor R).mapIso (polynomialModuleIso R) ≪≫
    PreservesCoproduct.iso (tilde.functor R)
      (fun _ : ULift.{u} ℕ ↦ (ModuleCat.of R R : ModuleCat.{u} R))

/-- `𝒪_X` in degree zero, as an object of `D(𝒪_X)`. -/
abbrev structureSheafDerived (X : Scheme.{u}) : DerivedCategory X.Modules :=
  (DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)

/-- `𝒪_X` in degree zero lies in `D_QCoh(𝒪_X)`. -/
theorem structureSheafDerived_mem (X : Scheme.{u}) :
    DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      (structureSheafDerived X) :=
  Stacks.Duality.DerivedPushforward.derivedCategoryB_singleFunctor_obj _
    (inferInstance : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsQuasicoherent)

/-- **`Rf_*𝒪_{𝐀¹_R} = (⊕_{n ≥ 0} 𝒪_{Spec R})[0]`.** The structure morphism is affine, so the
derived direct image of the structure sheaf is its direct image. -/
def derivedPushforwardStructureSheafIso :
    (derivedPushforward (structureMorphism R)).obj (structureSheafDerived (affineLine R)) ≅
      DerivedCategory.Q.obj ((HomologicalComplex.single
        (SheafOfModules.{u} (Spec R).ringCatSheaf) (ComplexShape.up ℤ) 0).obj
          (SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} ℕ))) :=
  (Stacks.AlgebraicGeometry.DerivedAffinePushforward.derivedPushforwardStructureSheafIso
      (structureMorphism R)).symm ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (pushforwardStructureSheafIso R) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app _

/-- **The internal Hom complex out of `(⊕_{n ≥ 0} 𝒪)[0]` is the product `∏_{n ≥ 0}` of copies of
the target**, the `n`-th projection being restriction to the `n`-th summand followed by
evaluation at the unit section. This is `AlgebraicGeometry.RingedSite.isLimitFanHomFree`, with
the index set `ℕ` in place of its lift to the universe of the modules. -/
def sheafHomComplexFreeIso (I : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.SheafOfModules.ringedSite (Spec R).sheaf).O)) ℤ) :
    (RingedSite.sheafHomComplex (Stacks.SheafOfModules.ringedSite (Spec R).sheaf)
        (RingedSite.freeComplex _ (ULift.{u} ℕ)) I).obj ≅ ∏ᶜ (fun _ : ℕ ↦ I) :=
  IsLimit.conePointUniqueUpToIso
      (RingedSite.isLimitFanCompIso (RingedSite.isLimitFanHomFree _ (ULift.{u} ℕ) I)
        fun _ ↦ RingedSite.structureSheafHomIso _ I)
      (productIsProduct fun _ : ULift.{u} ℕ ↦ I) ≪≫
    (Pi.reindex Equiv.ulift.symm (fun _ : ULift.{u} ℕ ↦ I)).symm

/-- **[Stacks, Tag 0GEU], the right hand side.**
`R𝓗om_{𝒪_Y}(Rf_*𝒪_X, 𝒪_Y) ≅ ∏_{n ≥ 0} 𝒪_Y` for `Y = Spec R`, `X = 𝐀¹_R` and `f` the structure
morphism, the product placed in degree zero. -/
def derivedSheafHomIso :
    ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
        (op ((derivedPushforward (structureMorphism R)).obj
          (structureSheafDerived (affineLine R))))).obj (structureSheafDerived (Spec R)) ≅
      (DerivedCategory.singleFunctor (Spec R).Modules 0).obj
        (∏ᶜ (fun _ : ℕ ↦ SheafOfModules.unit (Spec R).ringCatSheaf)) :=
  let Xs := Stacks.SheafOfModules.ringedSite (Spec R).sheaf
  let R0 := injectiveResolution (SheafOfModules.unit (Spec R).ringCatSheaf)
  have : QuasiIso (ProductResolution.piLiftSingle
      (fun _ : ℕ ↦ SheafOfModules.unit (Spec R).ringCatSheaf) (fun _ ↦ ProductResolution.J R0)
      (fun _ ↦ R0.ι')) :=
    ProductResolution.quasiIso_piLiftSingle_cochainComplex R0 ℕ
  have hι : IsIso (DerivedCategory.Q.map R0.ι') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  ((RingedSite.derivedSheafHomBifunctor Xs).mapIso
      (derivedPushforwardStructureSheafIso R).symm.op).app _ ≪≫
    ((RingedSite.derivedSheafHomBifunctor Xs).obj _).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _ ≪≫
        @asIso _ _ _ _ (DerivedCategory.Q.map R0.ι') hι) ≪≫
    @RingedSite.derivedSheafHomComparison Xs
      (inferInstance : HasDerivedCategory (SheafOfModules.{u} (Spec R).ringCatSheaf))
      (RingedSite.freeComplex Xs (ULift.{u} ℕ)) (ProductResolution.J R0)
      (CochainComplex.isKInjective_of_injective (ProductResolution.J R0) 0) ≪≫
    DerivedCategory.Q.mapIso (sheafHomComplexFreeIso R (ProductResolution.J R0)) ≪≫
    (asIso (DerivedCategory.Q.map (ProductResolution.piLiftSingle
      (fun _ : ℕ ↦ SheafOfModules.unit (Spec R).ringCatSheaf) (fun _ ↦ ProductResolution.J R0)
      (fun _ ↦ R0.ι')))).symm ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm

/-- The left hand side of the uncoherated trace map for `X = 𝐀¹_R`, `L = 𝒪_X`, at an object `M`
of `D_QCoh(𝒪_X)` in place of `a(K)`: `Rf_*R𝓗om_{𝒪_X}(𝒪_X, M)`. -/
abbrev traceSource (M : DerivedCategory (affineLine R).Modules) :
    DerivedCategory (Spec R).Modules :=
  (derivedPushforward (structureMorphism R)).obj
    (((Stacks.SheafOfModules.derivedSheafHom (affineLine R).sheaf).obj
      (op (structureSheafDerived (affineLine R)))).obj M)

/-- The right hand side of the uncoherated trace map for `X = 𝐀¹_R`, `L = 𝒪_X` and
`K = 𝒪_{Spec R}`: `R𝓗om_{𝒪_Y}(Rf_*𝒪_X, 𝒪_Y)`. -/
abbrev traceTarget : DerivedCategory (Spec R).Modules :=
  ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
    (op ((derivedPushforward (structureMorphism R)).obj
      (structureSheafDerived (affineLine R))))).obj (structureSheafDerived (Spec R))

/-- Quasi-coherence of all cohomology sheaves transfers along an isomorphism in the derived
category. -/
private theorem derivedCategoryB_of_iso {Y : Scheme.{u}} {K L : DerivedCategory Y.Modules}
    (e : K ≅ L) (h : DerivedCategoryB.derivedCategoryB (A := Y.Modules)
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf) K) :
    DerivedCategoryB.derivedCategoryB (A := Y.Modules)
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf) L := fun i ↦
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso e) (h i)

/-- **[Stacks, Tag 0GEU], the left hand side.** For every `M` in `D_QCoh(𝒪_X)` — in particular
for `M = a(𝒪_Y)`, whatever the right adjoint `a` — the object `Rf_*R𝓗om_{𝒪_X}(𝒪_X, M)` lies in
`D_QCoh(𝒪_Y)`: `R𝓗om_{𝒪_X}(𝒪_X, M) = M`, and `Rf_*` preserves quasi-coherence of cohomology
along the affine morphism `f`. -/
theorem traceSource_mem (M : quasiCoherentDerivedCategory (affineLine R)) :
    DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)
      (traceSource R M.obj) :=
  derivedCategoryB_of_iso ((derivedPushforward (structureMorphism R)).mapIso
    (RingedSite.derivedStructureSheafHomIso
      (Stacks.SheafOfModules.ringedSite (affineLine R).sheaf) M.obj)).symm
    fun i ↦ AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom.{u + 1}
      (structureMorphism R) M.obj M.2 i

/-- **The right hand side is not in `D_QCoh` when the product is not quasi-coherent.** Its zeroth
cohomology sheaf is `∏_{n ≥ 0} 𝒪_Y`. -/
theorem traceTarget_not_mem
    (h : ¬ (∏ᶜ (fun _ : ℕ ↦ SheafOfModules.unit (Spec R).ringCatSheaf)).IsQuasicoherent) :
    ¬ DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)
      (traceTarget R) := by
  intro hm
  have e : (DerivedCategory.homologyFunctor (Spec R).Modules 0).obj (traceTarget R) ≅
      (∏ᶜ (fun _ : ℕ ↦ SheafOfModules.unit (Spec R).ringCatSheaf) : (Spec R).Modules) :=
    (DerivedCategory.homologyFunctor (Spec R).Modules 0).mapIso (derivedSheafHomIso R) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (Spec R).Modules 0).app _
  exact h ((SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e (hm 0))

/-- **No isomorphism between the two sides.** When `∏_{n ≥ 0} 𝒪_Y` is not quasi-coherent, for no
`M` in `D_QCoh(𝒪_X)` is `Rf_*R𝓗om_{𝒪_X}(𝒪_X, M)` isomorphic to `R𝓗om_{𝒪_Y}(Rf_*𝒪_X, 𝒪_Y)`. -/
theorem isEmpty_iso
    (h : ¬ (∏ᶜ (fun _ : ℕ ↦ SheafOfModules.unit (Spec R).ringCatSheaf)).IsQuasicoherent)
    (M : quasiCoherentDerivedCategory (affineLine R)) :
    IsEmpty (traceSource R M.obj ≅ traceTarget R) :=
  ⟨fun e ↦ traceTarget_not_mem R h (derivedCategoryB_of_iso e (traceSource_mem R M))⟩

/-- Derived direct image along the structure morphism of the affine line preserves quasi-coherence
of cohomology, `f` being affine. -/
theorem hpush (K : quasiCoherentDerivedCategory (affineLine R)) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj
      ((derivedPushforward (structureMorphism R)).obj K.obj)).IsQuasicoherent :=
  AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom.{u + 1}
    (structureMorphism R) K.obj K.2 i

open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi Stacks.DerivedTensor.RingedSite in
/-- **The uncoherated trace map of the affine line is not an isomorphism.** When
`∏_{n ≥ 0} 𝒪_Y` is not quasi-coherent, for every right adjoint `a` of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` the map
`Rf_*R𝓗om_{𝒪_X}(𝒪_X, a(𝒪_Y)) ⟶ R𝓗om_{𝒪_Y}(Rf_*𝒪_X, 𝒪_Y)` of [Stacks, Tag 0B6H] is not an
isomorphism, so the statement of [Stacks, Tag 0A9Q] is false without the coherator. -/
theorem not_isIso_sheafyTrace
    (h : ¬ (∏ᶜ (fun _ : ℕ ↦ SheafOfModules.unit (Spec R).ringCatSheaf)).IsQuasicoherent)
    (DX : TensorHomAdjunction (derivedTensorProductFunctor (affineLine R).sheaf)
      (Stacks.SheafOfModules.derivedSheafHom (affineLine R).sheaf))
    (DY : TensorHomAdjunction (derivedTensorProductFunctor (Spec R).sheaf)
      (Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf))
    {a : quasiCoherentDerivedCategory (Spec R) ⥤ quasiCoherentDerivedCategory (affineLine R)}
    (adj : quasiCoherentDerivedPushforward (structureMorphism R) (hpush R) ⊣ a) :
    ¬ IsIso (sheafyTrace (structureMorphism R) DX DY (hpush R) adj
      ⟨structureSheafDerived (affineLine R), structureSheafDerived_mem (affineLine R)⟩
      ⟨structureSheafDerived (Spec R), structureSheafDerived_mem (Spec R)⟩) := fun hI ↦
  (isEmpty_iso R h
    (a.obj ⟨structureSheafDerived (Spec R), structureSheafDerived_mem (Spec R)⟩)).false
    (@asIso _ _ _ _ _ hI)

/-- **[Stacks, Tag 0GEU].** Let `Y = Spec R`, `X = 𝐀¹_R` and `f : X ⟶ Y` the structure morphism,
and take `L = 𝒪_X`, `K = 𝒪_Y` in the trace map `Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`.

1. The left hand side is in `D_QCoh(𝒪_Y)`: this holds for `Rf_*R𝓗om_{𝒪_X}(𝒪_X, M)` for every
   `M` in `D_QCoh(𝒪_X)`, so for `M = a(K)` whatever the right adjoint `a`.
2. The right hand side is isomorphic to `∏_{n ≥ 0} 𝒪_Y` placed in degree zero.
3. `∏_{n ≥ 0} 𝒪_Y` is quasi-coherent exactly when every `t ∈ R` satisfies an equation
   `t^j = t^{j+1} b`.
4. So when some `t ∈ R` satisfies no such equation, the right hand side is not in `D_QCoh(𝒪_Y)`,
   it is not isomorphic to the left hand side, and the trace map is not an isomorphism
   (`Stacks.Duality.AffineLine.not_isIso_sheafyTrace`).

The source asserts in (3) that the product is not quasi-coherent for an arbitrary `R`. That is
false for a field (`Stacks.Duality.isQuasicoherent_piStructureSheaf_of_isField`), and (3) is the
corrected form: the product fails to be quasi-coherent precisely for the rings with an element
`t` admitting no equation `t^j = t^{j+1} b`, such as `ℤ` (`uncoheratedTrace_example_int`). -/
@[stacks 0GEU "the full example in corrected form: the left side is in D_QCoh, the right side \
is the product of copies of the structure sheaf, which is quasi-coherent exactly when every t \
satisfies t^j = t^(j+1) b (false over Z, true over a field), and then no isomorphism exists"]
theorem uncoheratedTrace_example :
    (∀ M : quasiCoherentDerivedCategory (affineLine R),
      DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)
        (traceSource R M.obj)) ∧
    Nonempty (traceTarget R ≅ (DerivedCategory.singleFunctor (Spec R).Modules 0).obj
      (∏ᶜ (fun _ : ℕ ↦ SheafOfModules.unit (Spec R).ringCatSheaf))) ∧
    ((∏ᶜ (fun _ : ℕ ↦ SheafOfModules.unit (Spec R).ringCatSheaf)).IsQuasicoherent ↔
      ∀ t : R, ∃ (j : ℕ) (b : R), t ^ j = t ^ (j + 1) * b) ∧
    ((∃ t : R, ∀ (j : ℕ) (b : R), t ^ j ≠ t ^ (j + 1) * b) →
      ¬ DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf) (traceTarget R) ∧
      ∀ M : quasiCoherentDerivedCategory (affineLine R),
        IsEmpty (traceSource R M.obj ≅ traceTarget R)) := by
  refine ⟨traceSource_mem R, ⟨derivedSheafHomIso R⟩, isQuasicoherent_piStructureSheaf_iff R,
    fun ⟨t, ht⟩ ↦ ?_⟩
  have h : ¬ (∏ᶜ (fun _ : ℕ ↦ SheafOfModules.unit (Spec R).ringCatSheaf)).IsQuasicoherent :=
    fun hqc ↦ by
      obtain ⟨j, b, hjb⟩ := (isQuasicoherent_piStructureSheaf_iff R).1 hqc t
      exact ht j b hjb
  exact ⟨traceTarget_not_mem R h, isEmpty_iso R h⟩

/-- **[Stacks, Tag 0GEU] over `ℤ`.** For `Y = Spec ℤ` and `X = 𝐀¹_ℤ` the right hand side of the
trace map is `∏_{n ≥ 0} 𝒪_Y`, which is not quasi-coherent, while the left hand side is in
`D_QCoh(𝒪_Y)`; so the two are not isomorphic. -/
theorem uncoheratedTrace_example_int :
    ¬ (∏ᶜ (fun _ : ℕ ↦
        SheafOfModules.unit (Spec (CommRingCat.of ℤ)).ringCatSheaf)).IsQuasicoherent ∧
      ∀ M : quasiCoherentDerivedCategory (affineLine (CommRingCat.of ℤ)),
        IsEmpty (traceSource (CommRingCat.of ℤ) M.obj ≅ traceTarget (CommRingCat.of ℤ)) :=
  ⟨not_isQuasicoherent_piStructureSheaf_int,
    isEmpty_iso (CommRingCat.of ℤ) not_isQuasicoherent_piStructureSheaf_int⟩

end Stacks.Duality.AffineLine

end
