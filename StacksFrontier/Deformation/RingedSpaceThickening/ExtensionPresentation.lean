module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalIdealRestriction
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentExactSequence
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentPresentationQuasiIso
import StacksCore.Tactic.StacksAttribute

/-!
# The presentation attached to a square-zero extension

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces, `𝒢` an `𝒪_X`-module and
`0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` an extension of `f⁻¹𝒪_S`-algebras with `𝒢` an ideal of square
zero. Taking for `ℰ` the sheaf of sets underlying `𝒪_{X'}` and for `α' : ℰ ⟶ 𝒪_{X'}` the
identity gives a commutative diagram over `𝒪_{X'} ⟶ 𝒪_X` in which `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X` is
surjective; writing `𝒥` for its kernel, `𝖭𝖫(α) = (𝒥/𝒥² ⟶ Ω_{f⁻¹𝒪_S[ℰ]/f⁻¹𝒪_S} ⊗ 𝒪_X)` is
`𝖭𝖫_{X/S}` in `D(𝒪_X)`, and `α'` induces a map `𝒥/𝒥² ⟶ 𝒢`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension`: an extension
  `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras with `𝒢` an ideal of square zero.
* `AlgebraSquareZeroExtension.generators`, `generatorsMap` and `lift`: the sheaf of sets `ℰ`,
  the map `α : ℰ ⟶ 𝒪_X`, and the map `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'}` determined by `α'`.
* `AlgebraSquareZeroExtension.presentation`: the presentation `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X`.
* `AlgebraicGeometry.RingedSpaceThickening.generatorsPresentation` and
  `PresentedSquareZeroExtension`: the presentation of a prescribed family of generators, and an
  extension carrying a lift `α' : ℰ ⟶ 𝒪_{X'}` of such a family.
* `AlgebraSquareZeroExtension.toPresented`: an extension, presented by the family underlying
  its own structure sheaf, with `α'` the identity.
* `AlgebraSquareZeroExtension.conormalToIdeal`: the induced map `𝒥/𝒥² ⟶ 𝒢`.
* `AlgebraSquareZeroExtension.naiveCotangentIso`: the isomorphism `𝖭𝖫(α) ≅ 𝖭𝖫_{X/S}` in
  `D(𝒪_X)`.

## Main results

* `AlgebraSquareZeroExtension.lift_comp_reduction`: the map determined by `α'` followed by the
  reduction `𝒪_{X'} ⟶ 𝒪_X` is the presentation attached to `α`.
* `generatorsPresentation_isLocallySurjective`: the presentation of a surjective prescribed
  family of generators is surjective.
* `AlgebraSquareZeroExtension.presentation_isLocallySurjective`: the presentation
  `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X` is surjective.
* `AlgebraSquareZeroExtension.idealRestriction_app`: on a local relation `h` of the
  presentation the map `𝒥 ⟶ 𝒢` is `h ↦ α'(h)`, read in the square-zero ideal and carried to
  `𝒢`.

## References

* [Stacks Project, Tag 0GQ0](https://stacks.math.columbia.edu/tag/0GQ0)
* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sites.Conormal (IdealRestriction conormalDesc
  conormalSheaf kernelIdeal kernelIdeal_le_comap hom_of_comp_eq)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf
  freeAlgebraSheafCoefficientMap canonicalPresentation freeAlgebraSheaf_hom_ext
  freeAlgebraSheafCoefficientMap_comp_desc freeAlgebraSheafVariable_comp_desc
  canonicalPresentation_eq_desc freeAlgebraSheafDesc freeAlgebraSheafVariable)
open Stacks.SheafOfModules (inverseImageMiddleRing ringedSpaceStructureMap)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S : RingedSpace.{u, u}}

/-- `f⁻¹𝒪_S`, the inverse image of the structure sheaf of the base, as a sheaf on the site of
opens of `X`. -/
abbrev inverseImageBaseRing (f : X ⟶ S) :
    Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u} :=
  inverseImageMiddleRing f

/-- `f⁻¹𝒪_S ⟶ 𝒪_X`, the structure morphism of `f`, over the site of opens of `X`. -/
abbrev structureRingMap (f : X ⟶ S) : inverseImageBaseRing f ⟶ X.sheaf :=
  ringedSpaceStructureMap f

/-- An extension `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras in which `𝒢` is an ideal of
square zero.
The reduction is surjective and the identification of its kernel with `𝒢` is a natural family
of maps on sections, linear over `𝒪_{X'}` acting through the reduction. -/
structure AlgebraSquareZeroExtension (f : X ⟶ S)
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology X.carrier) X.sheaf)) where
  /-- The extended structure sheaf `𝒪_{X'}`. -/
  sheaf : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}
  /-- The `f⁻¹𝒪_S`-algebra structure `f⁻¹𝒪_S ⟶ 𝒪_{X'}`. -/
  base : inverseImageBaseRing f ⟶ sheaf
  /-- The reduction `𝒪_{X'} ⟶ 𝒪_X`. -/
  reduction : sheaf ⟶ X.sheaf
  /-- The reduction is a morphism of `f⁻¹𝒪_S`-algebras. -/
  base_comp_reduction : base ≫ reduction = structureRingMap f
  /-- The reduction is surjective. -/
  reduction_surjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) reduction.hom
  /-- The identification of the square-zero ideal `Ker(𝒪_{X'} ⟶ 𝒪_X)` with `𝒢`. -/
  ideal : IdealRestriction.{u, u, u, u} reduction G

/-- The presentation `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X` of a prescribed family of generators `α : ℰ ⟶ 𝒪_X`. -/
abbrev generatorsPresentation (f : X ⟶ S) (E : Functor (Opens X.carrier)ᵒᵖ (Type u))
    (α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) :
    freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E ⟶
      X.sheaf :=
  Stacks.SheafOfModules.presentation (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing f) X.sheaf (structureRingMap f) E α

/-- If every section of `𝒪_X` is locally of the form `α(x)`, then `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X` is
surjective. -/
instance generatorsPresentation_isLocallySurjective (f : X ⟶ S)
    (E : Functor (Opens X.carrier)ᵒᵖ (Type u))
    (α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) α] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (generatorsPresentation f E α).hom :=
  Stacks.Sites.FreeAlgebra.freeAlgebraSheafDesc_isLocallySurjective
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf E
    (structureRingMap f) α

/-- A square-zero extension `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras together with a
lift `α' : ℰ ⟶ 𝒪_{X'}` of a prescribed family of generators `α : ℰ ⟶ 𝒪_X`. The
identification of the square-zero ideal `Ker(𝒪_{X'} ⟶ 𝒪_X)` with `𝒢` is a natural family of
maps on sections, linear over `𝒪_{X'}` acting through the reduction. -/
structure PresentedSquareZeroExtension (f : X ⟶ S)
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology X.carrier) X.sheaf))
    (E : Functor (Opens X.carrier)ᵒᵖ (Type u))
    (α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) where
  /-- The extended structure sheaf `𝒪_{X'}`. -/
  sheaf : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}
  /-- The `f⁻¹𝒪_S`-algebra structure `f⁻¹𝒪_S ⟶ 𝒪_{X'}`. -/
  base : inverseImageBaseRing f ⟶ sheaf
  /-- The reduction `𝒪_{X'} ⟶ 𝒪_X`. -/
  reduction : sheaf ⟶ X.sheaf
  /-- The reduction is a morphism of `f⁻¹𝒪_S`-algebras. -/
  base_comp_reduction : base ≫ reduction = structureRingMap f
  /-- The lift `α' : ℰ ⟶ 𝒪_{X'}` of the prescribed family of generators. -/
  liftGen : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) sheaf
  /-- The lift is a lift: followed by the reduction it is `α`. -/
  liftGen_comp :
    liftGen ≫ Functor.whiskerRight
        ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map reduction)
        (forget CommRingCat.{u}) = α
  /-- The identification of the square-zero ideal `Ker(𝒪_{X'} ⟶ 𝒪_X)` with `𝒢`. -/
  ideal : IdealRestriction.{u, u, u, u} reduction G

namespace PresentedSquareZeroExtension

variable {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  {E : Functor (Opens X.carrier)ᵒᵖ (Type u)}
  {α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf}
  (P : PresentedSquareZeroExtension f G E α)

/-- The map `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'}` determined by the lift `α'`. -/
abbrev lift :
    freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E ⟶
      P.sheaf :=
  freeAlgebraSheafDesc (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
    P.sheaf E P.base P.liftGen

/-- The map determined by `α'` followed by the reduction `𝒪_{X'} ⟶ 𝒪_X` is the presentation
attached to `α`. -/
theorem lift_comp_reduction : P.lift ≫ P.reduction = generatorsPresentation f E α :=
  freeAlgebraSheaf_hom_ext (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
    X.sheaf E
    (((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ P.reduction)
          (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X.carrier)
            (inverseImageBaseRing f) P.sheaf E P.base P.liftGen))).trans
      (P.base_comp_reduction.trans
        (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X.carrier)
          (inverseImageBaseRing f) X.sheaf E (structureRingMap f) α).symm))
    ((congrArg
          (fun t ↦ freeAlgebraSheafVariable (Opens.grothendieckTopology X.carrier)
              (inverseImageBaseRing f) E ≫ Functor.whiskerRight t (forget CommRingCat.{u}))
          ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map_comp
            P.lift P.reduction)).trans
      ((congrArg
            (freeAlgebraSheafVariable (Opens.grothendieckTopology X.carrier)
                (inverseImageBaseRing f) E ≫ ·)
            (Functor.whiskerRight_comp _ _ _)).trans
        (((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ Functor.whiskerRight
                ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map
                  P.reduction) (forget CommRingCat.{u}))
              (freeAlgebraSheafVariable_comp_desc (Opens.grothendieckTopology X.carrier)
                (inverseImageBaseRing f) P.sheaf E P.base P.liftGen))).trans
          (P.liftGen_comp.trans
            (freeAlgebraSheafVariable_comp_desc (Opens.grothendieckTopology X.carrier)
              (inverseImageBaseRing f) X.sheaf E (structureRingMap f) α).symm))))

/-- A local relation of the presentation is carried by `α'` into the square-zero ideal. -/
theorem lift_mem_kernelIdeal (U : (Opens X.carrier)ᵒᵖ)
    (h : kernelIdeal (generatorsPresentation f E α).hom U) :
    (P.lift.hom.app U).hom h.1 ∈ kernelIdeal P.reduction.hom U :=
  kernelIdeal_le_comap (generatorsPresentation f E α).hom P.reduction.hom P.lift.hom
    (hom_of_comp_eq P.lift_comp_reduction) U h.2

/-- The map `𝒥(U) ⟶ 𝒢(U)` on sections determined by `α'`: apply `α'`, then read the result in
the square-zero ideal. -/
def idealRestriction : IdealRestriction.{u, u, u, u} (generatorsPresentation f E α) G where
  app U :=
    { toFun := fun h ↦ P.ideal.app U ⟨(P.lift.hom.app U).hom h.1, P.lift_mem_kernelIdeal U h⟩
      map_zero' :=
        Eq.trans (congrArg (P.ideal.app U) (Subtype.ext (map_zero (P.lift.hom.app U).hom)))
          (map_zero (P.ideal.app U))
      map_add' := fun h h' ↦
        Eq.trans (congrArg (P.ideal.app U) (Subtype.ext (map_add (P.lift.hom.app U).hom _ _)))
          (map_add (P.ideal.app U) _ _) }
  app_smul U r h :=
    Eq.trans (congrArg (P.ideal.app U) (Subtype.ext (map_mul (P.lift.hom.app U).hom r h.1)))
      (Eq.trans (P.ideal.app_smul U ((P.lift.hom.app U).hom r) _)
        (congrArg (· • P.ideal.app U
            ⟨(P.lift.hom.app U).hom h.1, P.lift_mem_kernelIdeal U h⟩)
          (congrArg (fun t : _ ⟶ X.sheaf ↦ (t.hom.app U).hom r) P.lift_comp_reduction)))
  app_map {U V} i h := by
    refine Eq.trans ?_
      (P.ideal.app_map i ⟨(P.lift.hom.app U).hom h.1, P.lift_mem_kernelIdeal U h⟩)
    refine congrArg (P.ideal.app V) (Subtype.ext ?_)
    exact NatTrans.naturality_apply P.lift.hom i h.1

/-- On a local relation `h` of the presentation the restriction datum is `α'(h)`, read in the
square-zero ideal and carried to `𝒢`. -/
theorem idealRestriction_app (U : (Opens X.carrier)ᵒᵖ)
    (h : kernelIdeal (generatorsPresentation f E α).hom U) :
    P.idealRestriction.app U h =
      P.ideal.app U ⟨(P.lift.hom.app U).hom h.1, P.lift_mem_kernelIdeal U h⟩ :=
  rfl

section Conormal

variable [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
  (generatorsPresentation f E α).hom]

/-- The map `𝒥/𝒥² ⟶ 𝒢` determined by `α'`. -/
abbrev conormalToIdeal :
    conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
      (freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E)
      X.sheaf (generatorsPresentation f E α) ⟶ G :=
  conormalDesc.{u, u, u, u} (generatorsPresentation f E α) G P.idealRestriction

end Conormal

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (f) (E) (α) [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
  (generatorsPresentation f E α).hom]

/-- `𝖭𝖫(α)`, the naive cotangent complex of the prescribed presentation. -/
abbrev presentationComplex :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology X.carrier) X.sheaf)) ℤ :=
  Stacks.SheafOfModules.presentationNaiveCotangentComplex.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
    (structureRingMap f) E α

/-- `𝖭𝖫_{X/S}`, the naive cotangent complex of `𝒪_X` over `f⁻¹𝒪_S`. -/
abbrev relativeComplex :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology X.carrier) X.sheaf)) ℤ :=
  Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)

/-- `𝖭𝖫(α)` as an object of `D(𝒪_X)`. -/
abbrev presentationObj :=
  (DerivedCategory.Q (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf))).obj (presentationComplex f E α)

/-- `𝖭𝖫_{X/S}` as an object of `D(𝒪_X)`. -/
abbrev relativeObj :=
  (DerivedCategory.Q (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf))).obj (relativeComplex f)

/-- The canonical comparison map `𝖭𝖫(α) ⟶ 𝖭𝖫_{X/S}` of the presentation becomes an isomorphism in
`D(𝒪_X)`. -/
instance isIso_Q_map_comparison :
    IsIso (DerivedCategory.Q.map
      (Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u}
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
        (structureRingMap f) E α)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (Stacks.SheafOfModules.quasiIso_naiveCotangentComplexComparison
      (inverseImageBaseRing f) X.sheaf (structureRingMap f) E α)

/-- The identification `𝖭𝖫(α) ≅ 𝖭𝖫_{X/S}` in `D(𝒪_X)` given by the canonical comparison map. -/
def naiveCotangentIso : presentationObj f E α ≅ relativeObj f :=
  asIso (DerivedCategory.Q.map
    (Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u}
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
      (structureRingMap f) E α))

variable {f} {E} {α}

end Derived

end PresentedSquareZeroExtension

namespace AlgebraSquareZeroExtension

attribute [instance] reduction_surjective

variable {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  (P : AlgebraSquareZeroExtension f G)

/-- The sheaf of sets `ℰ` of the source: the one underlying `𝒪_{X'}`. -/
abbrev generators : Functor (Opens X.carrier)ᵒᵖ (Type u) :=
  underlyingPresheaf (Opens.grothendieckTopology X.carrier) P.sheaf

/-- The map `α : ℰ ⟶ 𝒪_X` of the source: the reduction, read on underlying sets. -/
abbrev generatorsMap :
    P.generators ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf :=
  Functor.whiskerRight P.reduction.hom (forget CommRingCat.{u})

/-- The map `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'}` determined by `α' : ℰ ⟶ 𝒪_{X'}`, which is the identity. -/
abbrev lift :
    freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
      P.generators ⟶ P.sheaf :=
  canonicalPresentation (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
    P.sheaf P.base

/-- The presentation `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X` attached to `α`. -/
abbrev presentation :
    freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
      P.generators ⟶ X.sheaf :=
  Stacks.SheafOfModules.presentation (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing f) X.sheaf (structureRingMap f) P.generators P.generatorsMap

/-- An extension `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0`, presented by the family of generators underlying
its own structure sheaf, with `α'` the identity. -/
def toPresented (P : AlgebraSquareZeroExtension f G) :
    PresentedSquareZeroExtension f G P.generators P.generatorsMap where
  sheaf := P.sheaf
  base := P.base
  reduction := P.reduction
  base_comp_reduction := P.base_comp_reduction
  liftGen := 𝟙 _
  liftGen_comp := Category.id_comp _
  ideal := P.ideal

/-- The map determined by `α'` followed by the reduction `𝒪_{X'} ⟶ 𝒪_X` is the presentation
attached to `α`. -/
@[stacks 0GQ0 "the commutative diagram over 𝒪_{X'} ⟶ 𝒪_X for the choice of sheaf of sets ℰ \
that the source gives, namely the one underlying 𝒪_{X'} with α' the identity"]
theorem lift_comp_reduction : P.lift ≫ P.reduction = P.presentation :=
  P.toPresented.lift_comp_reduction

/-- The presentation `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X` is surjective. -/
@[stacks 0GQ0 "surjectivity of f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X, which is what makes 𝖭𝖫(α) defined"]
instance presentation_isLocallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) P.presentation.hom := by
  rw [← P.lift_comp_reduction]
  change Presheaf.IsLocallySurjective _ (P.lift.hom ≫ P.reduction.hom)
  infer_instance

/-- A local relation of the presentation is carried by `α'` into the square-zero ideal. -/
theorem lift_mem_kernelIdeal (U : (Opens X.carrier)ᵒᵖ)
    (h : kernelIdeal P.presentation.hom U) :
    (P.lift.hom.app U).hom h.1 ∈ kernelIdeal P.reduction.hom U :=
  P.toPresented.lift_mem_kernelIdeal U h

/-- The map `𝒥(U) ⟶ 𝒢(U)` on sections determined by `α'`: apply `α'`, then read the result in
the square-zero ideal. -/
def idealRestriction : IdealRestriction.{u, u, u, u} P.presentation G :=
  P.toPresented.idealRestriction

/-- The map `𝒥/𝒥² ⟶ 𝒢` determined by `α'`. -/
@[stacks 0GQ0 "the map 𝒥/𝒥² ⟶ 𝒢 determined by α'; not the resulting element of \
Ext¹_{𝒪_X}(𝖭𝖫(α), 𝒢), whose agreement with the class of 𝒪_{X'} under the bijection of 0GPZ \
is not proved here"]
abbrev conormalToIdeal :
    conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
      (freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
        P.generators) X.sheaf P.presentation ⟶ G :=
  P.toPresented.conormalToIdeal

/-- On a local relation `h` of the presentation the restriction datum is `α'(h)`, read in the
square-zero ideal and carried to `𝒢`. -/
theorem idealRestriction_app (U : (Opens X.carrier)ᵒᵖ)
    (h : kernelIdeal P.presentation.hom U) :
    P.idealRestriction.app U h =
      P.ideal.app U ⟨(P.lift.hom.app U).hom h.1, P.lift_mem_kernelIdeal U h⟩ :=
  P.toPresented.idealRestriction_app U h

/-! ### The identification with the naive cotangent complex -/

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- `𝖭𝖫(α)`, the naive cotangent complex of the presentation attached to the extension. -/
abbrev naiveCotangentComplex :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology X.carrier) X.sheaf)) ℤ :=
  PresentedSquareZeroExtension.presentationComplex f P.generators P.generatorsMap

/-- The identification `𝖭𝖫(α) ≅ 𝖭𝖫_{X/S}` in `D(𝒪_X)` given by the canonical comparison map. -/
@[stacks 0GQ0 "the identification 𝖭𝖫_{X/S} ≅ 𝖭𝖫(α) in D(𝒪_X) for the chosen ℰ, by 08TL"]
def naiveCotangentIso :
    DerivedCategory.Q.obj P.naiveCotangentComplex ≅
      DerivedCategory.Q.obj (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u}
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
        (structureRingMap f)) :=
  PresentedSquareZeroExtension.naiveCotangentIso f P.generators P.generatorsMap

end Derived

end AlgebraSquareZeroExtension

end AlgebraicGeometry.RingedSpaceThickening

end
