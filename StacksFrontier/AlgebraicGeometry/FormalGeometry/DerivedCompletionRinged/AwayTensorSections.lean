module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayTensorBridge
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingIdeal
public import StacksFrontier.RingTheory.LocalizationAwayTensor

/-!
# The tensor identity for the presheaves of sectionwise localizations, on sections

Let `(𝒞, 𝒪)` be a ringed site and let `f`, `g` be global sections of `𝒪`. Over every object `U`
of the site,

`𝒪(U)[1/f|_U] ⊗_{𝒪(U)} 𝒪(U)[1/g|_U] = 𝒪(U)[1/(f g)|_U]`,

which is `IsLocalization.Away.tensorProductAlgEquiv` read on the presheaves
`AlgebraicGeometry.RingedSite.awayModulePresheaf` of sectionwise localizations. This is the
component of the identification `𝒪_f ⊗_𝒪 𝒪_g = 𝒪_{f g}` of sheaves of `𝒪`-modules that
[Stacks, Tag 0996(3)] needs; the naturality in `U` that turns these components into a morphism
of presheaves of modules is not proved here.

## Main definitions

* `AlgebraicGeometry.RingedSite.awayTensorSectionIso`: **the identification above**, as an
  isomorphism of modules of sections over an object of the site.

## Main results

* `AlgebraicGeometry.RingedSite.isLocalizationAway_away` and
  `AlgebraicGeometry.RingedSite.isLocalizationAway_away_mul`: the two localization facts the
  components need, at the algebra structure the components must use.

## Implementation notes

The algebra structure is `((toAwayPresheaf f).app U).hom.toAlgebra`, the one induced by the
canonical map, and that is not a matter of convenience: it is *definitionally* the module
structure that `awayModulePresheaf` carries, since that presheaf is a restriction of scalars
along exactly this map. Using the `Algebra` instance that search finds instead would give a
structure equal to it only propositionally — `isLocalizationAway_awayPresheaf` proves the two
equal by `Algebra.algebra_ext` — and the components would then not typecheck against the
modules of sections they are supposed to compare.

`isLocalizationAway_awayPresheaf` is stated as an explicit theorem with the algebra instance
written out, rather than as an instance, and `isLocalizationAway_away` here has to be invoked by
hand for the same reason: `Stacks.MultiplicativeSubpresheaf.localizationPresheaf` is a `def`
whose `obj U := CommRingCat.of (Localization (S.obj U))`, and instance search does not unfold a
`def`. So `IsLocalization.Away (globalSectionVal f U) ((awayPresheaf f).obj U)` does *not*
synthesize, even though `IsLocalization ((awayMultiplicativeSubpresheaf f).obj U) _` does: the
`Away` spelling needs `Submonoid.powers (globalSectionVal f U)`, which is the value of that
hidden field. This is the `def`-is-a-wall phenomenon in its instance-search register — the terms
are definitionally equal and cross freely, it is only synthesis that stops.

## References

* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.SheafOfModules

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  (f g : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

omit [HasWeakSheafify X.J CommRingCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify X.J AddCommGrpCat] in
/-- The sectionwise localization at a global section is a localization of the ring of sections,
for the algebra structure induced by the canonical map — which is also the module structure that
`awayModulePresheaf` carries. -/
theorem isLocalizationAway_away (U : X.Cᵒᵖ) :
    letI := ((toAwayPresheaf f).app U).hom.toAlgebra
    IsLocalization.Away (globalSectionVal f U) ((awayPresheaf f).obj U) :=
  isLocalizationAway_awayPresheaf f U

omit [HasWeakSheafify X.J CommRingCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify X.J AddCommGrpCat] in
/-- The sectionwise localization at a product of two global sections is a localization away from
the product of their values. -/
theorem isLocalizationAway_away_mul (U : X.Cᵒᵖ) :
    letI := ((toAwayPresheaf (mulGlobalSection X f g)).app U).hom.toAlgebra
    IsLocalization.Away (globalSectionVal f U * globalSectionVal g U)
      ((awayPresheaf (mulGlobalSection X f g)).obj U) := by
  let := ((toAwayPresheaf (mulGlobalSection X f g)).app U).hom.toAlgebra
  rw [← globalSectionVal_mulGlobalSection]
  exact isLocalizationAway_awayPresheaf (mulGlobalSection X f g) U

/-- **The tensor identity on sections over an object of the site**:
`𝒪(U)[1/f] ⊗_{𝒪(U)} 𝒪(U)[1/g] = 𝒪(U)[1/(f g)]`. -/
def awayTensorSectionIso (U : X.Cᵒᵖ) :
    (MonoidalCategoryStruct.tensorObj (awayModulePresheafAlt X f)
        (awayModulePresheafAlt X g)).obj U ≅
      (awayModulePresheafAlt X (mulGlobalSection X f g)).obj U :=
  letI := ((toAwayPresheaf f).app U).hom.toAlgebra
  letI := ((toAwayPresheaf g).app U).hom.toAlgebra
  letI := ((toAwayPresheaf (mulGlobalSection X f g)).app U).hom.toAlgebra
  letI := isLocalizationAway_away X f U
  letI := isLocalizationAway_away X g U
  letI := isLocalizationAway_away_mul X f g U
  (IsLocalization.Away.tensorProductAlgEquiv (globalSectionVal f U) (globalSectionVal g U)
    ((awayPresheaf f).obj U) ((awayPresheaf g).obj U)
    ((awayPresheaf (mulGlobalSection X f g)).obj U)).toLinearEquiv.toModuleIso

end AlgebraicGeometry.RingedSite

end
