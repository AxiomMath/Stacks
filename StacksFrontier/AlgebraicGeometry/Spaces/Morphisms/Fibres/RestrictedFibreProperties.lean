module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricComponentCount
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReduced
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria

/-!
# Properties of a morphism inherited by its fibres over sections

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` and let `v` be a section of `Y` over
an object `T ⟶ S` of the big fppf site. The restriction of `f` to the big fppf site of `T`, and
the fibre `restrictedFibre f v` of `f` over `v`, an algebraic space over `T`, inherit from `f`
being proper, flat, locally of finite presentation, quasi-compact and quasi-separated: viewed
again over `S`, the restriction of `f` is a base change of `f`, and these properties are stable
under base change and do not depend on the base scheme.

## Main results

* `AlgebraicGeometry.Space.isProper_relocalizeRestrict_map`,
  `AlgebraicGeometry.Space.isFlat_relocalizeRestrict_map`,
  `AlgebraicGeometry.Space.isFinitePresentation_relocalizeRestrict_map`: the restriction of `f`
  to the big fppf site of `T` is proper, flat, of finite presentation when `f` is.
* `AlgebraicGeometry.Space.isProper_restrictedFibre`,
  `AlgebraicGeometry.Space.isFlat_restrictedFibre`,
  `AlgebraicGeometry.Space.isFinitePresentation_restrictedFibre`: the same for the structure
  morphism of the fibre over a section.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on a big fppf site over a scheme, given directly: instance search
for them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_restrictedFibreProperties
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_restrictedFibreProperties
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_restrictedFibreProperties B S hS).has_limit _

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
  {T : Scheme.{u}} (hT : B.Contains T) (g : B.obj hT ⟶ B.obj hS)

/-! ### The restriction of a morphism -/

section Restrict

/-- Viewed again over `S`, the restriction of `f` along `g` is the base change of `f` along the
counit of the restriction of `Y`. -/
theorem isPullback_relocalize_relocalizeRestrict_map :
    IsPullback (OverShriek.relocalizeRestrictCounit g X)
      ((OverShriek.relocalizePresheafFunctor g).map ((OverShriek.relocalizeRestrict g).map f))
      f (OverShriek.relocalizeRestrictCounit g Y) :=
  OverShriek.isPullback_map_relocalizeRestrictCounit g f

variable (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)

/-- A property of morphisms holding on every étale chart, and stable under base change, is
inherited by the restriction of a morphism to a smaller base. -/
private theorem holdsOnEveryEtaleChart_relocalizeRestrict_map
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (P : MorphismProperty Scheme.{u})
    (hP : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => HoldsOnEveryEtaleChart B S hS P f.hom))
    (hf : HoldsOnEveryEtaleChart B S hS P f) :
    HoldsOnEveryEtaleChart B T hT P ((OverShriek.relocalizeRestrict g).map f) := by
  have hXT := isAlgebraicSpace_relocalizeRestrict B T S hT hS g X hX
  have hYT := isAlgebraicSpace_relocalizeRestrict B T S hT hS g Y hY
  refine (holdsOnEveryEtaleChart_relocalizeMap_iff B T S hT hS g _ _).mp ?_
  exact hP.of_isPullback
    (isPullback_homMk B S hS hX
      (isAlgebraicSpace_relocalize B (B.obj hT) (B.obj hS) g _ hYT) hY
      (isAlgebraicSpace_relocalize B (B.obj hT) (B.obj hS) g _ hXT)
      (isPullback_relocalize_relocalizeRestrict_map B S hS f hT g)) hf

include hX hY in
/-- **Restriction to a smaller base preserves properness.** -/
theorem isProper_relocalizeRestrict_map (hf : IsProper B S hS f) :
    IsProper B T hT ((OverShriek.relocalizeRestrict g).map f) := by
  have hXT := isAlgebraicSpace_relocalizeRestrict B T S hT hS g X hX
  have hYT := isAlgebraicSpace_relocalizeRestrict B T S hT hS g Y hY
  refine (isProper_relocalize_iff B T hT S hS g hXT hYT _).mp ?_
  exact isProper_of_isPullback B S hS
    (isAlgebraicSpace_relocalize B (B.obj hT) (B.obj hS) g _ hXT) hX
    (isAlgebraicSpace_relocalize B (B.obj hT) (B.obj hS) g _ hYT) hY
    (isPullback_relocalize_relocalizeRestrict_map B S hS f hT g) hf

include hX hY in
/-- **Restriction to a smaller base preserves flatness.** -/
theorem isFlat_relocalizeRestrict_map (hf : IsFlat B S hS f) :
    IsFlat B T hT ((OverShriek.relocalizeRestrict g).map f) :=
  holdsOnEveryEtaleChart_relocalizeRestrict_map B S hS f hT g hX hY _
    (isFlat_isStableUnderBaseChange B S hS) hf

include hX hY in
/-- **Restriction to a smaller base preserves local finite presentation.** -/
theorem isLocallyOfFinitePresentation_relocalizeRestrict_map
    (hf : IsLocallyOfFinitePresentation B S hS f) :
    IsLocallyOfFinitePresentation B T hT ((OverShriek.relocalizeRestrict g).map f) :=
  holdsOnEveryEtaleChart_relocalizeRestrict_map B S hS f hT g hX hY _
    (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS) hf

/-- **Restriction to a smaller base preserves quasi-compactness.** -/
theorem isQuasiCompact_relocalizeRestrict_map (hf : IsQuasiCompact B S hS f) :
    IsQuasiCompact B T hT ((OverShriek.relocalizeRestrict g).map f) :=
  (isQuasiCompact_relocalize_iff B T hT S hS g _).mp
    (isQuasiCompact_of_isPullback B S hS
      (isPullback_relocalize_relocalizeRestrict_map B S hS f hT g) hf)

/-- **Restriction to a smaller base preserves quasi-separatedness.** -/
theorem isQuasiSeparated_relocalizeRestrict_map (hf : IsQuasiSeparated B S hS f) :
    IsQuasiSeparated B T hT ((OverShriek.relocalizeRestrict g).map f) :=
  (isQuasiSeparated_relocalize_iff B T hT S hS g _).mp
    (isQuasiSeparated_of_isPullback B S hS
      (isPullback_relocalize_relocalizeRestrict_map B S hS f hT g) hf)

include hX hY in
/-- **Restriction to a smaller base preserves finite presentation.** -/
theorem isFinitePresentation_relocalizeRestrict_map (hf : IsFinitePresentation B S hS f) :
    IsFinitePresentation B T hT ((OverShriek.relocalizeRestrict g).map f) :=
  ⟨isLocallyOfFinitePresentation_relocalizeRestrict_map B S hS f hT g hX hY hf.1,
    isQuasiCompact_relocalizeRestrict_map B S hS f hT g hf.2.1,
    isQuasiSeparated_relocalizeRestrict_map B S hS f hT g hf.2.2⟩

end Restrict

/-! ### The fibre over a section -/

section Fibre

variable (v : Y.obj (op (Over.mk g)))

/-- The structure morphism of the fibre over a section is the second projection of the fibre
product defining it, the section being a morphism out of the terminal presheaf over `T`. -/
theorem from_restrictedFibre_eq :
    (isTerminal_yoneda_obj_base B T hT).from (restrictedFibre B S hS f hT g v) =
      pullback.snd ((OverShriek.relocalizeRestrict g).map f)
        (restrictedSection B S hS Y hT g v) :=
  (isTerminal_yoneda_obj_base B T hT).hom_ext _ _

/-- The fibre over a section is the base change of the restriction of `f` along the section. -/
theorem isPullback_restrictedFibre :
    IsPullback (pullback.fst ((OverShriek.relocalizeRestrict g).map f)
        (restrictedSection B S hS Y hT g v))
      ((isTerminal_yoneda_obj_base B T hT).from (restrictedFibre B S hS f hT g v))
      ((OverShriek.relocalizeRestrict g).map f) (restrictedSection B S hS Y hT g v) := by
  rw [from_restrictedFibre_eq]
  exact IsPullback.of_hasPullback _ _

variable (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)

/-- A property of morphisms of algebraic spaces stable under base change passes from the
restriction of `f` to the structure morphism of its fibre over a section. -/
private theorem restrictedFibre_of_relocalizeRestrict_map
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (Q : ∀ ⦃F G : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u⦄, (F ⟶ G) → Prop)
    (hQ : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B T hT⦄ (f : F ⟶ G) => Q f.hom))
    (hf : Q ((OverShriek.relocalizeRestrict g).map f)) :
    Q ((isTerminal_yoneda_obj_base B T hT).from (restrictedFibre B S hS f hT g v)) :=
  hQ.of_isPullback
    (isPullback_homMk B T hT (isAlgebraicSpace_relocalizeRestrict B T S hT hS g X hX)
      (isAlgebraicSpace_yoneda B T hT _) (isAlgebraicSpace_relocalizeRestrict B T S hT hS g Y hY)
      (isAlgebraicSpace_restrictedFibre B S hS f hX hY hT g v)
      (isPullback_restrictedFibre B S hS f hT g v)) hf

include hX hY in
/-- **The fibre of a proper morphism over a section is proper over the base of the section.** -/
theorem isProper_restrictedFibre (hf : IsProper B S hS f) :
    IsProper B T hT
      ((isTerminal_yoneda_obj_base B T hT).from (restrictedFibre B S hS f hT g v)) :=
  isProper_of_isPullback B T hT (isAlgebraicSpace_restrictedFibre B S hS f hX hY hT g v)
    (isAlgebraicSpace_relocalizeRestrict B T S hT hS g X hX)
    (isAlgebraicSpace_yoneda B T hT _) (isAlgebraicSpace_relocalizeRestrict B T S hT hS g Y hY)
    (isPullback_restrictedFibre B S hS f hT g v)
    (isProper_relocalizeRestrict_map B S hS f hT g hX hY hf)

include hX hY in
/-- **The fibre of a flat morphism over a section is flat over the base of the section.** -/
theorem isFlat_restrictedFibre (hf : IsFlat B S hS f) :
    IsFlat B T hT
      ((isTerminal_yoneda_obj_base B T hT).from (restrictedFibre B S hS f hT g v)) :=
  restrictedFibre_of_relocalizeRestrict_map B S hS f hT g v hX hY (@IsFlat B T hT)
    (isFlat_isStableUnderBaseChange B T hT) (isFlat_relocalizeRestrict_map B S hS f hT g hX hY hf)

include hX hY in
/-- **The fibre of a morphism of finite presentation over a section is of finite presentation
over the base of the section.** -/
theorem isFinitePresentation_restrictedFibre (hf : IsFinitePresentation B S hS f) :
    IsFinitePresentation B T hT
      ((isTerminal_yoneda_obj_base B T hT).from (restrictedFibre B S hS f hT g v)) := by
  have hr := isFinitePresentation_relocalizeRestrict_map B S hS f hT g hX hY hf
  refine ⟨restrictedFibre_of_relocalizeRestrict_map B S hS f hT g v hX hY
    (@IsLocallyOfFinitePresentation B T hT)
    (isLocallyOfFinitePresentation_isStableUnderBaseChange B T hT) hr.1,
    isQuasiCompact_of_isPullback B T hT (isPullback_restrictedFibre B S hS f hT g v) hr.2.1,
    isQuasiSeparated_of_isPullback B T hT (isPullback_restrictedFibre B S hS f hT g v) hr.2.2⟩

end Fibre

end AlgebraicGeometry.Space

end
