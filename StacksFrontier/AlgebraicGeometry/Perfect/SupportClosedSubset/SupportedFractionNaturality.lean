module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DeterminantChangeOfEquations

/-!
# The class map into local cohomology is functorial in the module and depends only on the wedge

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global functions with common zero locus the
closed subset `Z ⊆ X`, and let `ℱ` be a quasi-coherent `𝒪_X`-module.  Stacks 0G7Q gives the class
map `c_{f₁,…,f_c}`, and Stacks 0G7M identifies its target with `i_*ℋ^c_Z(ℱ)`; the composite of
those with the canonical epimorphism `ℱ ↠ i_*i^*ℱ` is a morphism

`ℱ ⟶ i_*ℋ^c_Z(ℱ)`

read on the coefficient module itself.  This file proves two properties of it:

* it is **functorial in `ℱ`** — the square commutes for every morphism of quasi-coherent
  `𝒪_X`-modules, the target being the functor `ℱ ↦ i_*ℋ^c_Z(ℱ)`;
* it is **canonical** — it does not depend on the chosen equations, only on the wedge
  `[f₁] ∧ ⋯ ∧ [f_c]` of their conormal classes.

## Main definitions

* `supportCohomologySheafFunctor`: `ℱ ↦ i_*ℋ^p_T(ℱ)`, as a functor of the coefficient module.
* `supportedFractionSource`: the class map of Stacks 0G7Q, read on `ℱ` and in `i_*ℋ^c_T(ℱ)`.
* `equationsQuotientFunctor`: `ℱ ↦ i_*i^*ℱ`, the cokernel of `(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ`, as a
  functor of the coefficient module.
* `fractionClassTrans`: **Stacks 0G7Q** — the canonical map `c_{f₁, …, f_c}` together with its
  functoriality in `ℱ`, as a natural transformation of those two functors.
* `ConormalDeterminantData`: a module `line` on `X` with a global section `wedge f` for every
  family of `c` equations with zero locus `Z`, the transformation law
  `wedge (a · f) = det(a) · wedge f`, and the statement that `wedge f` generates `line` over the
  closed subscheme; the motivating example is `i_*⋀^c 𝒞_{Z/X}` with `[f₁] ∧ ⋯ ∧ [f_c]`.

## Main results

* `supportedFractionSource_natural`: **the functoriality in `ℱ`** of the class map read in
  `i_*ℋ^c_T(ℱ)`.  This is the naturality square that `SupportedFractionMap` leaves unassembled:
  the fraction morphism is natural there, but the induced square between the two cokernels, and
  its compatibility with the comparison of Stacks 0G7L, are not.
* `cokernelπ_comp_fractionClassTrans_app`: the natural transformation of Stacks 0G7Q on the class
  of a local section `s` is the class of the fraction `s / (f₁ ⋯ f_c)`.
* `supportedFractionSource_eq_of_wedge_eq`: **the canonicity** — two families of `c` equations
  with the same zero locus and the same wedge give the same morphism `ℱ ⟶ i_*ℋ^c_Z(ℱ)`.
* `Q_map_extendMap_cplxMap_comp_cechToDerivedSupport` and
  `homologyMap_cplxMap_comp_cechHomologyToSupport`: the comparison of Stacks 0G7L, and the
  degree-`p` cohomology sheaf map it induces, are natural in the coefficient module.  This is
  the closing clause of Stacks 0G7L and, like the rest of that remark, needs no quasi-coherence:
  it is stated for a morphism of arbitrary `𝒪_X`-modules.
* `supportedFractionSource_eq_det_smul`: Stacks 0G7S, read on `supportedFractionSource`.

## Implementation notes

The target `i_*ℋ^p_T(ℱ)` is `supportCohomologySheaf` of `DeterminantChangeOfEquations`, namely the
degree-`p` cohomology of `i_* R𝓗_T(ℱ[0])`; `supportCohomologySheafFunctor` is the composite of the
three functors it is built from, so it agrees with `supportCohomologySheaf` on objects by
definition and supplies the map on morphisms.  This spelling of the local cohomology sheaf is the
one Stacks 0G7Q and Stacks 0G7S are stated at; it is not identified in this project with
`localCohomologySheafFunctor` or with `localCohomologySheafOfComplex`.

Naturality of the comparison of Stacks 0G7L in the coefficient module is proved exactly as its
compatibility with the subfamily projections is proved in `DeterminantChangeOfEquations`: the
counit of Stacks 0G72 is invertible at the extended alternating Čech complex, and after the counit
the comparison becomes `i_* R𝓗_T` applied to the augmentation, which is natural by
`Augmentation.augmentation_natural`.  It is then carried down to the cohomology sheaves by the two
identifications `HomologicalComplex.extendHomologyIso` and `derivedQHomologyIso`, both of which are
natural.  On the source side the class map is read through `cechCocycleClass`, whose behaviour
under a morphism of complexes is `cocycleClass_comp_homologyMap`, so the naturality square reduces
to `fractionHom_naturality`.

In the canonicity statement the section `[f₁] ∧ ⋯ ∧ [f_c]` and its determinant law are the
fields of the datum `ConormalDeterminantData`; the statement is that the morphism into local
cohomology, which is built from the equations alone, depends on them only through that section.
Its mathematical content is Stacks 0G7S.  The twisted map of Stacks 0G7T, with source
`(⋀^c 𝒞_{Z/X})^∨ ⊗ i^*ℱ`, is `Stacks.Perfect.ConormalClass.conormalTwistClass`.

## References

* [Stacks Project, Tag 0G7T](https://stacks.math.columbia.edu/tag/0G7T)
* [Stacks Project, Tag 0G7S](https://stacks.math.columbia.edu/tag/0G7S)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.CechDerivedSupport
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.ExtendedAlternatingCech.Augmentation
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.SupportedFraction

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-! ### The local cohomology sheaf as a functor of the coefficient module -/

/-- **`i_*ℋ^p_T`, as a functor of the coefficient module.**  The coefficient module placed in
degree `0`, its derived sections with support on `T` pushed forward to `X`, and the degree-`p`
cohomology sheaf of the result.  On objects this is `supportCohomologySheaf`. -/
public def supportCohomologySheafFunctor {T : Set X} (hT : IsClosed T) (p : ℤ) :
    X.Modules ⥤ X.Modules :=
  DerivedCategory.singleFunctor X.Modules 0 ⋙ supportPush hT ⋙
    DerivedCategory.homologyFunctor X.Modules p

/-- The functor of the coefficient module evaluates to the cohomology sheaf `i_*ℋ^p_T(ℱ)`. -/
public theorem supportCohomologySheafFunctor_obj {T : Set X} (hT : IsClosed T) (p : ℤ)
    (F : X.Modules) :
    (supportCohomologySheafFunctor hT p).obj F = supportCohomologySheaf hT F p := rfl

/-- **`i_*ℋ^p_T(φ)`, the map of cohomology sheaves induced by a morphism of coefficient
modules**, with its type spelled by `supportCohomologySheaf`.  It is the map of
`supportCohomologySheafFunctor` on `φ`, by `supportCohomologySheafFunctor_map`; the two spellings
`X.Modules` and `SheafOfModules (structureSheafRing X.toRingedSpace)` of the ambient category
agree only up to unfolding, so this form, whose stated type uses only the first, is the one the
proofs below are carried out at. -/
public def supportCohomologySheafMap {T : Set X} (hT : IsClosed T) {F G : X.Modules} (φ : F ⟶ G)
    (p : ℤ) : supportCohomologySheaf hT F p ⟶ supportCohomologySheaf hT G p :=
  (DerivedCategory.homologyFunctor X.Modules p).map
    ((supportPush hT).map ((DerivedCategory.singleFunctor X.Modules 0).map φ))

/-- On a morphism the functor is the degree-`p` cohomology of `i_* R𝓗_T` applied to it. -/
public theorem supportCohomologySheafFunctor_map {T : Set X} (hT : IsClosed T) (p : ℤ)
    {F G : X.Modules} (φ : F ⟶ G) :
    (supportCohomologySheafFunctor hT p).map φ = supportCohomologySheafMap hT φ p := rfl

/-! ### The comparison of Stacks 0G7L is natural in the coefficient module -/

/-- The augmentation of Stacks 0G7L is natural in the coefficient module, with the induced map of
extended alternating Čech complexes spelled `cplxMap`. -/
public theorem Q_map_extendMap_cplxMap_comp_augmentation {m : ℕ} (e : Fin m → Γ(X, ⊤))
    {F G : X.Modules} (φ : F ⟶ G) :
    DerivedCategory.Q.map (HomologicalComplex.extendMap (cplxMap e φ)
          ComplexShape.embeddingUpNat) ≫ augmentation e G =
      augmentation e F ≫ (DerivedCategory.singleFunctor X.Modules 0).map φ :=
  augmentation_natural e φ

/-- **The edge `i_* R𝓗_T(ℱ) ⟶ ℱ` of the diagram of Stacks 0G7L is natural in the coefficient
module.**  It is the counit of Stacks 0G72 evaluated at `ℱ[0]`, hence a component of a natural
transformation, so its naturality square is `NatTrans.naturality`; it is stated here because the
remark asserts its diagram functorial in `ℱ`, and that assertion is the naturality of all three
edges. -/
@[stacks 0G7L "functoriality in the 𝒪_X-module ℱ, the edge i_*RℋT(ℱ) ⟶ ℱ of the diagram"]
public theorem derivedSupportedSectionsToId_single_naturality {T : Set X} (hT : IsClosed T)
    {F G : X.Modules} (φ : F ⟶ G) :
    (supportPush hT).map ((DerivedCategory.singleFunctor X.Modules 0).map φ) ≫
        (supportPushCounit hT).app ((DerivedCategory.singleFunctor X.Modules 0).obj G) =
      (supportPushCounit hT).app ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
        (DerivedCategory.singleFunctor X.Modules 0).map φ :=
  (supportPushCounit hT).naturality ((DerivedCategory.singleFunctor X.Modules 0).map φ)

/-- **The canonical comparison `𝓕^• ⟶ i_* R𝓗_T(ℱ)` of Stacks 0G7L is natural in the coefficient
module.**  Both sides become, after the invertible counit of Stacks 0G72, the functor
`i_* R𝓗_T` applied to a naturality square for the augmentation.

This is the second of the three edges of the remark's diagram; with
`Q_map_extendMap_cplxMap_comp_augmentation` for the edge `𝓕^• ⟶ ℱ` and
`derivedSupportedSectionsToId_single_naturality` for the edge `i_* R𝓗_T(ℱ) ⟶ ℱ` it is the
remark's closing clause, that the diagram is "functorial in the `𝒪_X`-module `ℱ`".

As in the source, `φ` is a morphism of arbitrary `𝒪_X`-modules: quasi-coherence is nowhere used,
the counit being invertible at the extended alternating Čech complex of any module by
Stacks 0G7K. -/
@[stacks 0G7L "functoriality in the 𝒪_X-module ℱ, the edge 𝓕^• ⟶ i_*RℋT(ℱ) of the diagram"]
public theorem Q_map_extendMap_cplxMap_comp_cechToDerivedSupport {m : ℕ} (e : Fin m → Γ(X, ⊤))
    {F G : X.Modules} (φ : F ⟶ G) {T : Set X}
    (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T) :
    DerivedCategory.Q.map (HomologicalComplex.extendMap (cplxMap e φ)
          ComplexShape.embeddingUpNat) ≫ cechToDerivedSupport e G hT hTe =
      cechToDerivedSupport e F hT hTe ≫
        (supportPush hT).map ((DerivedCategory.singleFunctor X.Modules 0).map φ) := by
  refine ((@asIso _ _ _ _ _
    (isIso_derivedSupportedSectionsToId_cech e F hT hTe)).cancel_iso_hom_left _ _).mp ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun ψ => ψ ≫ cechToDerivedSupport e G hT hTe)
    ((supportPushCounit hT).naturality (DerivedCategory.Q.map
      (HomologicalComplex.extendMap (cplxMap e φ) ComplexShape.embeddingUpNat))).symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun ψ => (supportPush hT).map (DerivedCategory.Q.map
      (HomologicalComplex.extendMap (cplxMap e φ) ComplexShape.embeddingUpNat)) ≫ ψ)
    (derivedSupportedSectionsToId_comp_cechToDerivedSupport e G hT hTe)) ?_
  refine Eq.trans ((supportPush hT).map_comp _ _).symm ?_
  refine Eq.trans (congrArg (supportPush hT).map
    (Q_map_extendMap_cplxMap_comp_augmentation e φ)) ?_
  refine Eq.trans ((supportPush hT).map_comp _ _) ?_
  refine Eq.trans (congrArg (fun ψ => ψ ≫ (supportPush hT).map
      ((DerivedCategory.singleFunctor X.Modules 0).map φ))
    (derivedSupportedSectionsToId_comp_cechToDerivedSupport e F hT hTe).symm) ?_
  exact Category.assoc _ _ _

/-- The comparison of Stacks 0G7L, with its target spelled by `supportPushSingle`, is natural in
the coefficient module. -/
public theorem Q_map_extendMap_cplxMap_comp_cechToSupport {m : ℕ} (e : Fin m → Γ(X, ⊤))
    {F G : X.Modules} (φ : F ⟶ G) {T : Set X}
    (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T) :
    DerivedCategory.Q.map (HomologicalComplex.extendMap (cplxMap e φ)
          ComplexShape.embeddingUpNat) ≫ cechToSupport e G hT hTe =
      cechToSupport e F hT hTe ≫
        (supportPush hT).map ((DerivedCategory.singleFunctor X.Modules 0).map φ) :=
  Q_map_extendMap_cplxMap_comp_cechToDerivedSupport e φ hT hTe

/-- The degree-`p` cohomology of the comparison of Stacks 0G7L, read on the extended complexes, is
natural in the coefficient module. -/
public theorem homologyMap_extendMap_cplxMap_comp_extendHomologyToSupport {m : ℕ}
    (e : Fin m → Γ(X, ⊤)) {F G : X.Modules} (φ : F ⟶ G)
    {T : Set X} (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T) (p : ℕ) :
    HomologicalComplex.homologyMap (HomologicalComplex.extendMap (cplxMap e φ)
          ComplexShape.embeddingUpNat) (p : ℤ) ≫ extendHomologyToSupport e G hT hTe p =
      extendHomologyToSupport e F hT hTe p ≫ supportCohomologySheafMap hT φ (p : ℤ) := by
  have hnat : HomologicalComplex.homologyMap (HomologicalComplex.extendMap (cplxMap e φ)
          ComplexShape.embeddingUpNat) (p : ℤ) ≫
        (derivedQHomologyIso ((cplx e G).extend ComplexShape.embeddingUpNat) (p : ℤ)).inv =
      (derivedQHomologyIso ((cplx e F).extend ComplexShape.embeddingUpNat) (p : ℤ)).inv ≫
        (DerivedCategory.homologyFunctor X.Modules (p : ℤ)).map
          (DerivedCategory.Q.map (HomologicalComplex.extendMap (cplxMap e φ)
            ComplexShape.embeddingUpNat)) := by
    rw [Iso.comp_inv_eq, Category.assoc, derivedQHomologyIso_hom_naturality, Iso.inv_hom_id_assoc]
  rw [extendHomologyToSupport, extendHomologyToSupport, ← Category.assoc, hnat, Category.assoc,
    ← Functor.map_comp, Q_map_extendMap_cplxMap_comp_cechToSupport]
  exact Eq.trans (congrArg (fun ψ => (derivedQHomologyIso ((cplx e F).extend
        ComplexShape.embeddingUpNat) (p : ℤ)).inv ≫ ψ)
      ((DerivedCategory.homologyFunctor X.Modules (p : ℤ)).map_comp _ _))
    (Category.assoc _ _ _).symm

/-- **The degree-`p` cohomology of the extended alternating Čech complex mapped to `i_*ℋ^p_T(ℱ)`
is natural in the coefficient module.** -/
public theorem homologyMap_cplxMap_comp_cechHomologyToSupport {m : ℕ} (e : Fin m → Γ(X, ⊤))
    {F G : X.Modules} (φ : F ⟶ G) {T : Set X}
    (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T) (p : ℕ) :
    HomologicalComplex.homologyMap (cplxMap e φ) p ≫ cechHomologyToSupport e G hT hTe p =
      cechHomologyToSupport e F hT hTe p ≫ supportCohomologySheafMap hT φ (p : ℤ) := by
  have hnat : HomologicalComplex.homologyMap (cplxMap e φ) p ≫
        (HomologicalComplex.extendHomologyIso (cplx e G) ComplexShape.embeddingUpNat
          (embeddingUpNat_f p)).inv =
      (HomologicalComplex.extendHomologyIso (cplx e F) ComplexShape.embeddingUpNat
          (embeddingUpNat_f p)).inv ≫
        HomologicalComplex.homologyMap (HomologicalComplex.extendMap (cplxMap e φ)
          ComplexShape.embeddingUpNat) (p : ℤ) := by
    rw [Iso.comp_inv_eq, Category.assoc,
      HomologicalComplex.extendHomologyIso_hom_naturality, Iso.inv_hom_id_assoc]
  rw [cechHomologyToSupport, cechHomologyToSupport, ← Category.assoc, hnat, Category.assoc,
    homologyMap_extendMap_cplxMap_comp_extendHomologyToSupport]
  exact (Category.assoc _ _ _).symm

/-- A morphism of coefficient modules carries the class of a top-degree Čech cochain to the class
of its image. -/
public theorem cechCocycleClass_top_comp_homologyMap_cplxMap {d : ℕ}
    (f : Fin (d + 1) → Γ(X, ⊤)) {F G : X.Modules} (φ : F ⟶ G) {M : X.Modules}
    (u : M ⟶ prodTerm f F d) :
    cechCocycleClass f F d u (comp_difSucc_top f F u) ≫
        HomologicalComplex.homologyMap (cplxMap f φ) (d + 1) =
      cechCocycleClass f G d (u ≫ prodMap f φ d) (comp_difSucc_top f G (u ≫ prodMap f φ d)) :=
  cocycleClass_comp_homologyMap (cplxMap f φ) (CochainComplex.next ℕ (d + 1)) u
    (comp_cplx_d_succ f F d u (comp_difSucc_top f F u))

/-! ### The class map read on the coefficient module -/

/-- **The class map `c_{f₁,…,f_c}` of Stacks 0G7Q, read on the coefficient module and in
`i_*ℋ^c_T(ℱ)`.**  It is the canonical epimorphism `ℱ ↠ i_*i^*ℱ` presenting the source as the
cokernel of `(f₁, …, f_c)`, followed by the class map of Stacks 0G7Q and by the identification
`cokernelLastDifToSupport` of its target with `i_*ℋ^c_T(ℱ)`.

Reading the class map this way is what Stacks 0G7S does: the two presentations of `i_*i^*ℱ`
belonging to two families of equations have no chosen isomorphism between them, but both receive
`ℱ` by an epimorphism, so an equation of morphisms out of `ℱ` is equivalent to an equation of
class maps and needs no such choice.

No factor of the composite uses the quasi-coherence of `ℱ`, and `General.supportedFractionSource`
is the same composite without that hypothesis. -/
public def supportedFractionSource {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤)) (F : X.Modules)
    [F.IsQuasicoherent] {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    F ⟶ supportCohomologySheaf hT F ((d + 1 : ℕ) : ℤ) :=
  cokernel.π (equationsMultiplication f F) ≫ supportedFractionClass f F ≫
    cokernelLastDifToSupport f F hT hTf

/-- The class map read on the coefficient module is the degree-`c` cohomology class of the fraction
`s / (f₁ ⋯ f_c)`, carried into `i_*ℋ^c_T(ℱ)` by the comparison of Stacks 0G7L. -/
public theorem supportedFractionSource_eq {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤)) (F : X.Modules)
    [F.IsQuasicoherent] {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    supportedFractionSource f F hT hTf =
      cechCocycleClass f F d (fractionHom f F d) (comp_difSucc_top f F (fractionHom f F d)) ≫
        cechHomologyToSupport f F hT hTf (d + 1) :=
  (cokernelπ_comp_supportedFractionClass_comp f F hT hTf).trans
    (comp_cokernelπ_comp_cokernelLastDifToSupport f F hT hTf (fractionHom f F d))

/-- **The class map kills a multiple of an equation.**  Multiplying a local section of `ℱ` by one
of the equations makes its class in `i_*ℋ^c_T(ℱ)` vanish.

This is the `supportedFractionSource` analogue of
`AlgebraicGeometry.Scheme.Hom.smulHom_comp_formFractionClass`, but the proof does not transport:
there the vanishing is an appeal to Stacks 0G7Q through
`Stacks.Perfect.FractionClass.smulHom_comp_classMap`, because that spelling's class map is built
on `Stacks.Perfect.FractionClass.equationsMap`.  Here it is immediate, because
`supportedFractionSource` begins with the projection onto the cokernel of
`equationsMultiplication`, and `equationsMultiplication` *is* the coproduct of the very maps
`globalSmul (f j)` being killed: multiplication by `f j` is the `j`-th coprojection followed by
it, so composing with the projection to its cokernel is zero by `cokernel.condition`.  Neither
the quasi-coherence of `ℱ` nor anything about `T` is used beyond typing the statement. -/
public theorem globalSmul_comp_supportedFractionSource {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤))
    (F : X.Modules) [F.IsQuasicoherent] {T : Set X} (hT : IsClosed T)
    (hTf : equationsClosedSet f ⊆ T) (j : Fin (d + 1)) :
    globalSmul (f j) F ≫ supportedFractionSource f F hT hTf = 0 := by
  have hι : Sigma.ι (fun _ : Fin (d + 1) => F) j ≫ equationsMultiplication f F =
      globalSmul (f j) F := Sigma.ι_comp_desc _ _
  have h0 : globalSmul (f j) F ≫ cokernel.π (equationsMultiplication f F) = 0 := by
    rw [← hι, Category.assoc, cokernel.condition, comp_zero]
  rw [supportedFractionSource, ← Category.assoc, h0, zero_comp]

/-! ### Functoriality in the module -/

/-- Naturality of a class map in the coefficient module, given its description as the class of the
cocycle `fractionHom f F d` at each module. -/
private theorem comp_eq_comp_supportCohomologySheafMap {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤))
    {F G : X.Modules} (φ : F ⟶ G) {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T)
    {sF : F ⟶ supportCohomologySheaf hT F ((d + 1 : ℕ) : ℤ)}
    {sG : G ⟶ supportCohomologySheaf hT G ((d + 1 : ℕ) : ℤ)}
    (hF : sF = cechCocycleClass f F d (fractionHom f F d)
      (comp_difSucc_top f F (fractionHom f F d)) ≫ cechHomologyToSupport f F hT hTf (d + 1))
    (hG : sG = cechCocycleClass f G d (fractionHom f G d)
      (comp_difSucc_top f G (fractionHom f G d)) ≫ cechHomologyToSupport f G hT hTf (d + 1)) :
    φ ≫ sG = sF ≫ supportCohomologySheafMap hT φ ((d + 1 : ℕ) : ℤ) := by
  rw [hG, hF, ← Category.assoc, comp_cechCocycleClass, Category.assoc,
    ← homologyMap_cplxMap_comp_cechHomologyToSupport f φ hT hTf (d + 1), ← Category.assoc,
    cechCocycleClass_top_comp_homologyMap_cplxMap]
  exact congrArg (fun ψ => ψ ≫ cechHomologyToSupport f G hT hTf (d + 1))
    (cechCocycleClass_congr f G d _ _ (fractionHom_naturality f φ d).symm)

/-- **The class map into `i_*ℋ^c_T(ℱ)` is functorial in the quasi-coherent module `ℱ`.**  For
every morphism `φ : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules,

`φ ≫ c_𝒢 = c_ℱ ≫ i_*ℋ^c_T(φ)`

where the right-hand factor is the functor `supportCohomologySheafFunctor` on `φ`.

`SupportedFractionMap` proves the fraction morphism natural but leaves this square unassembled;
the two steps it needs are the naturality of the comparison of Stacks 0G7L in the coefficient
module (`homologyMap_cplxMap_comp_cechHomologyToSupport`) and the behaviour of a Čech cohomology
class under the induced map of complexes (`cechCocycleClass_top_comp_homologyMap_cplxMap`), after
which both sides are the class of the single cocycle `fractionHom f F d ≫ prodMap f φ d`.

Neither step uses the quasi-coherence of the two modules, and
`General.supportedFractionSource_natural` is the same square without those hypotheses; it is the
functoriality in an arbitrary `𝒪_X`-module that Stacks 0G7Q asserts, and `fractionClassTrans` is
that functoriality as a natural transformation. -/
public theorem supportedFractionSource_natural {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤))
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) {T : Set X}
    (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    φ ≫ supportedFractionSource f G hT hTf =
      supportedFractionSource f F hT hTf ≫
        (supportCohomologySheafFunctor hT ((d + 1 : ℕ) : ℤ)).map φ := by
  exact comp_eq_comp_supportCohomologySheafMap f φ hT hTf (supportedFractionSource_eq f F hT hTf)
    (supportedFractionSource_eq f G hT hTf)

/-! ### The class map and its functoriality, for an arbitrary coefficient module

Stacks 0G7Q asserts its class map, and its functoriality, for an arbitrary `𝒪_X`-module `ℱ`;
quasi-coherence enters the remark only where an identification has to be *invertible*, which is
Stacks 0G7M.  The class map read on the coefficient module and its naturality square are
therefore repeated here without that hypothesis, on the identifications of
`Stacks.Perfect.SupportedFraction.General` of `DeterminantChangeOfEquations.lean`.  That is what
lets `fractionClassTrans` below be a natural transformation of functors defined on all of
`X.Modules`; the declarations above keep the hypothesis, as the consumers of Stacks 0G7S and of
Stacks 0G7T do.
-/

/-- **The class map `c_{f₁,…,f_c}` of Stacks 0G7Q, read on an arbitrary coefficient module and in
`i_*ℋ^c_T(ℱ)`.**  The same composite as `supportedFractionSource`: the canonical epimorphism
`ℱ ↠ i_*i^*ℱ`, the class map of Stacks 0G7Q and the identification
`General.cokernelLastDifToSupport` of its target, none of which uses quasi-coherence. -/
public def General.supportedFractionSource {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤)) (F : X.Modules)
    {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    F ⟶ supportCohomologySheaf hT F ((d + 1 : ℕ) : ℤ) :=
  cokernel.π (equationsMultiplication f F) ≫ supportedFractionClass f F ≫
    General.cokernelLastDifToSupport f F hT hTf

/-- The class map read on an arbitrary coefficient module is the degree-`c` cohomology class of
the fraction `s / (f₁ ⋯ f_c)`, carried into `i_*ℋ^c_T(ℱ)` by the comparison of Stacks 0G7L. -/
public theorem General.supportedFractionSource_eq {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤))
    (F : X.Modules) {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    General.supportedFractionSource f F hT hTf =
      cechCocycleClass f F d (fractionHom f F d) (comp_difSucc_top f F (fractionHom f F d)) ≫
        cechHomologyToSupport f F hT hTf (d + 1) :=
  (General.cokernelπ_comp_supportedFractionClass_comp f F hT hTf).trans
    (General.comp_cokernelπ_comp_cokernelLastDifToSupport f F hT hTf (fractionHom f F d))

/-- **The class map into `i_*ℋ^c_T(ℱ)` is functorial in the `𝒪_X`-module `ℱ`.**  This is
`supportedFractionSource_natural` with no quasi-coherence hypothesis on either module: the
naturality of the comparison of Stacks 0G7L in the coefficient module and the behaviour of a Čech
cohomology class under the induced map of complexes hold for every morphism of `𝒪_X`-modules, and
after them both sides are the class of the single cocycle `fractionHom f F d ≫ prodMap f φ d`.

This is the functoriality Stacks 0G7Q asserts; `fractionClassTrans` is it as a natural
transformation. -/
public theorem General.supportedFractionSource_natural {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤))
    {F G : X.Modules} (φ : F ⟶ G) {T : Set X}
    (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    φ ≫ General.supportedFractionSource f G hT hTf =
      General.supportedFractionSource f F hT hTf ≫
        (supportCohomologySheafFunctor hT ((d + 1 : ℕ) : ℤ)).map φ := by
  exact comp_eq_comp_supportCohomologySheafMap f φ hT hTf
    (General.supportedFractionSource_eq f F hT hTf)
    (General.supportedFractionSource_eq f G hT hTf)

/-! ### Stacks 0G7Q as a natural transformation of functors of the module -/

/-- **`i_*i^*ℱ`, as a functor of the coefficient module.**  On objects it is the cokernel of
`(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ`, which is `i_*i^*ℱ` for the closed immersion `i : Z ⟶ X` cut out by
the equations — the presentation Stacks 0G7Q uses — and on a morphism `φ : ℱ ⟶ 𝒢` it is the
induced map of cokernels, namely `i_*i^*φ`.  It is characterised by
`cokernelπ_comp_equationsQuotientFunctor_map`.

That the induced map exists is `equationsMultiplication_comp` applied to the two facts the
projection of `globalSmul_comp_supportedFractionSource` above also rests on: multiplication by a
global function is `𝒪_X`-linear, hence commutes with `φ`, and multiplication by one equation is
the corresponding coprojection followed by `equationsMultiplication`, hence is killed by the
projection to its cokernel. -/
public def equationsQuotientFunctor {c : ℕ} (f : Fin c → Γ(X, ⊤)) : X.Modules ⥤ X.Modules where
  obj F := cokernel (equationsMultiplication f F)
  map {F G} φ := cokernel.desc (equationsMultiplication f F)
    (φ ≫ cokernel.π (equationsMultiplication f G))
    (equationsMultiplication_comp f F _ fun i => by
      have hnat : globalSmul (f i) F ≫ φ = φ ≫ globalSmul (f i) G := by
        ext V z
        simp [globalSmul_app]
      have hι : Sigma.ι (fun _ : Fin c => G) i ≫ equationsMultiplication f G =
          globalSmul (f i) G := Sigma.ι_comp_desc _ _
      have h0 : globalSmul (f i) G ≫ cokernel.π (equationsMultiplication f G) = 0 := by
        rw [← hι, Category.assoc, cokernel.condition, comp_zero]
      rw [← Category.assoc, hnat, Category.assoc, h0, comp_zero])
  map_id F := by
    refine (cancel_epi (cokernel.π (equationsMultiplication f F))).mp ?_
    rw [cokernel.π_desc, Category.id_comp, Category.comp_id]
  map_comp {F G H} φ ψ := by
    refine (cancel_epi (cokernel.π (equationsMultiplication f F))).mp ?_
    rw [cokernel.π_desc, ← Category.assoc, cokernel.π_desc, Category.assoc, Category.assoc,
      cokernel.π_desc]

/-- The functor `ℱ ↦ i_*i^*ℱ` on a morphism is characterised by its composite with the canonical
epimorphism `ℱ ↠ i_*i^*ℱ`. -/
public theorem cokernelπ_comp_equationsQuotientFunctor_map {c : ℕ} (f : Fin c → Γ(X, ⊤))
    {F G : X.Modules} (φ : F ⟶ G) :
    cokernel.π (equationsMultiplication f F) ≫ (equationsQuotientFunctor f).map φ =
      φ ≫ cokernel.π (equationsMultiplication f G) :=
  cokernel.π_desc _ _ _

/-- **Stacks Project, Tag 0G7Q.**  With `X` a scheme, `f₁, …, f_c ∈ Γ(X, 𝒪_X)` global functions
and `Z ⊆ X` the closed subscheme they cut out, there is a canonical map

`c_{f₁, …, f_c} : i^*ℱ ⟶ ℋ^c_Z(ℱ)`

of `𝒪_X|_Z`-modules, functorial in the `𝒪_X`-module `ℱ`.  Here it is that functoriality: a
natural transformation between the two functors of `ℱ`, from `ℱ ↦ i_*i^*ℱ`
(`equationsQuotientFunctor`, the cokernel of `(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ`, which is how the remark
presents the source) to `ℱ ↦ i_*ℋ^c_Z(ℱ)` (`supportCohomologySheafFunctor`).  Both functors are
direct images along the inclusion of `Z`, which is fully faithful, so the transformation is the
map of `𝒪_X|_Z`-modules of the statement — this is the last step of the remark's construction and
the form in which Stacks 0G7T states the analogous twisted map
(`Stacks.Perfect.ConormalClass.conormalTwistClass`).

Its component at `ℱ` is the map `supportedFractionClass` of the remark, between the two
presentations, followed by the canonical identification `General.cokernelLastDifToSupport` of its
target with `i_*ℋ^c_Z(ℱ)`; on the class of a local section `s` of `ℱ` it is the class of the
fraction `s / (f₁ ⋯ f_c)`, by `cokernelπ_comp_fractionClassTrans_app`.  As in Remark 0G7I, which
fixes the setting of this remark, `ℱ` is an arbitrary `𝒪_X`-module and the morphisms of the
naturality square are arbitrary morphisms of `𝒪_X`-modules: quasi-coherence is used neither by
the map nor by its functoriality, which is why the two factors and the naturality square are
taken from the namespace `General` above, and the source adds it only in Stacks 0G7S and
Stacks 0G7U.

The target is the spelling of `i_*ℋ^c_Z(ℱ)` in which Stacks 0G7Q and Stacks 0G7S are stated here,
with the direct image taken before the cohomology sheaf.  The other spelling, with the cohomology
sheaf taken on `Z` first — the one `Stacks.Perfect.FractionClass.fractionClass` lands in — is
identified with this one, naturally in `ℱ` and with no hypothesis on `ℱ`, by
`Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso`. -/
@[stacks 0G7Q "the canonical map c_{f₁,…,f_c} : i^*ℱ ⟶ ℋ^c_Z(ℱ) together with its functoriality \
in the 𝒪_X-module ℱ, as a natural transformation between the two functors of ℱ: from ℱ ↦ i_*i^*ℱ, \
the cokernel of (f₁,…,f_c) as the remark presents it, to ℱ ↦ i_*ℋ^c_Z(ℱ); read on X along the \
fully faithful i_*, as the remark's last step and as Stacks 0G7T does for the twisted map"]
public def fractionClassTrans {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤)) :
    equationsQuotientFunctor f ⟶
      supportCohomologySheafFunctor (isClosed_equationsClosedSet f) ((d + 1 : ℕ) : ℤ) where
  app F := supportedFractionClass f F ≫
    General.cokernelLastDifToSupport f F (isClosed_equationsClosedSet f) subset_rfl
  naturality F G φ := by
    refine (cancel_epi (cokernel.π (equationsMultiplication f F))).mp ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun ψ => ψ ≫ (supportedFractionClass f G ≫
        General.cokernelLastDifToSupport f G (isClosed_equationsClosedSet f) subset_rfl))
      (cokernelπ_comp_equationsQuotientFunctor_map f φ)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (General.supportedFractionSource_natural f φ
      (isClosed_equationsClosedSet f) subset_rfl) ?_
    exact Category.assoc _ _ _

/-- **The natural transformation of Stacks 0G7Q sends the class of a local section `s` of `ℱ` to
the class of the fraction `s / (f₁ ⋯ f_c)`**, read in `i_*ℋ^c_Z(ℱ)` through the canonical
identification of that module with the cokernel of the last Čech differential. -/
public theorem cokernelπ_comp_fractionClassTrans_app {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤))
    (F : X.Modules) :
    cokernel.π (equationsMultiplication f F) ≫ (fractionClassTrans f).app F =
      fractionHom f F d ≫ cokernel.π (lastDif f F) ≫
        General.cokernelLastDifToSupport f F (isClosed_equationsClosedSet f) subset_rfl :=
  General.cokernelπ_comp_supportedFractionClass_comp f F (isClosed_equationsClosedSet f)
    subset_rfl

/-! ### Canonicity -/

/-- Stacks 0G7S, read on the class map of the coefficient module: changing the equations by a
matrix multiplies the morphism `ℱ ⟶ i_*ℋ^c_Z(ℱ)` by the determinant of the matrix. -/
public theorem supportedFractionSource_eq_det_smul {d : ℕ} (f g : Fin (d + 1) → Γ(X, ⊤))
    (a : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent]
    (hg : ∀ j, g j = ∑ i, a j i * f i)
    (hZ : equationsClosedSet g = equationsClosedSet f) :
    supportedFractionSource f F (isClosed_equationsClosedSet f) subset_rfl =
      globalSmul a.det F ≫
        supportedFractionSource g F (isClosed_equationsClosedSet f) hZ.le :=
  (supportedFractionClass_eq_det_smul f g a F hg hZ).2.2

/-- **A determinant datum for the families of `c` equations cutting out `Z`.**  A module `line`
on `X` with a global section `wedge f` for every family of `c` equations cutting out `Z`, such
that changing the equations by a matrix multiplies the section by the determinant of the matrix,
and such that the section generates the line over the closed subscheme.  The motivating example
is `line = i_*⋀^c 𝒞_{Z/X}` with `wedge f` the wedge of the conormal classes.

The second property is stated as the implication it is used through rather than as invertibility
of `line`.  Both `⋀^c 𝒞_{Z/X}` and `i^*ℱ` are modules on the closed subscheme, so a global
function acting as the identity on a generator of the first restricts to `1` there and therefore
acts as the identity on the second; it is that consequence which the field records.  Asking
instead for `r = 1` in `Γ(X, 𝒪_X)` would be false for the determinant line, which is annihilated
by the ideal of `Z`. -/
public structure ConormalDeterminantData (X : Scheme.{u}) (Z : Set X) (c : ℕ) where
  /-- The determinant line. -/
  line : X.Modules
  /-- The section attached to a family of `c` equations cutting out `Z`. -/
  wedge (f : Fin c → Γ(X, ⊤)) (hf : equationsClosedSet f = Z) : Γ(line, ⊤)
  /-- Changing the equations by a matrix multiplies the wedge by the determinant of the matrix. -/
  wedge_det (f g : Fin c → Γ(X, ⊤)) (hf : equationsClosedSet f = Z)
      (hg : equationsClosedSet g = Z) (a : Matrix (Fin c) (Fin c) Γ(X, ⊤))
      (ha : ∀ j, g j = ∑ i, a j i * f i) : wedge g hg = a.det • wedge f hf
  /-- A global function acting as the identity on the wedge acts as the identity on `i_*i^*ℱ`. -/
  wedge_cancel (f : Fin c → Γ(X, ⊤)) (hf : equationsClosedSet f = Z) (r : Γ(X, ⊤))
      (hr : r • wedge f hf = wedge f hf) (F : X.Modules) :
    globalSmul r F ≫ cokernel.π (equationsMultiplication f F) =
      cokernel.π (equationsMultiplication f F)

/-- **The morphism `ℱ ⟶ i_*ℋ^c_Z(ℱ)` is canonical: it depends on the equations only through the
wedge `[f₁] ∧ ⋯ ∧ [f_c]` of their conormal classes.**  If two families of `c` equations cut out
the same closed subset `Z`, are related by a matrix, and have the same wedge, then the two
morphisms `ℱ ⟶ i_*ℋ^c_Z(ℱ)` they define coincide.

The mathematical content is Stacks 0G7S, which says that the two morphisms differ exactly by
multiplication by the determinant of the matrix relating the two families.  The wedge having the
same value for both families makes that determinant act as the identity on the wedge, hence on
`i_*i^*ℱ`, which is where the two morphisms are read. -/
public theorem supportedFractionSource_eq_of_wedge_eq {d : ℕ} {Z : Set X}
    (D : ConormalDeterminantData X Z (d + 1)) (f g : Fin (d + 1) → Γ(X, ⊤))
    (hf : equationsClosedSet f = Z) (hg : equationsClosedSet g = Z)
    (a : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(X, ⊤)) (ha : ∀ j, g j = ∑ i, a j i * f i)
    (F : X.Modules) [F.IsQuasicoherent] (hw : D.wedge g hg = D.wedge f hf) :
    supportedFractionSource f F (isClosed_equationsClosedSet f) subset_rfl =
      supportedFractionSource g F (isClosed_equationsClosedSet f) (hg.trans hf.symm).le := by
  have hfix : a.det • D.wedge g hg = D.wedge g hg := by
    rw [hw]
    exact (D.wedge_det f g hf hg a ha).symm.trans hw
  rw [supportedFractionSource_eq_det_smul f g a F ha (hg.trans hf.symm), supportedFractionSource,
    ← Category.assoc, D.wedge_cancel g hg a.det hfix F]

end Stacks.Perfect.SupportedFraction

end
