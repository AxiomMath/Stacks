module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleRelocalize
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeSubcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.RetractOfAPerfectObject

/-!
# Direct images and perfectness over a smaller base scheme

Let `h : W ⟶ S` be a morphism of a big fppf site. An algebraic space `X` over `W` is viewed over
`S` through the lower-shriek extension `Λ_h` of Stacks 03I5, part (2), and the two have
equivalent derived categories (`AlgebraicGeometry.Space.smallerBaseDerivedEquivalence`,
Stacks 04SG). This file records the properties of morphisms that do not depend on the base,
states as propositions the two comparisons, of derived direct images and of perfect objects, that
the passage of Stacks 0DKX from a base `S` to `Spec ℤ` uses, and deduces from them that
perfectness of a derived direct image descends from the larger base. For representable morphisms
the comparison of direct images is `AlgebraicGeometry.Space.smallerBasePushforwardIso`.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeSpaceDerivedEquivalence`: `D(𝒪_{Λ_h X}) ≌ D(𝒪_X)`.
* `AlgebraicGeometry.Space.SmallerBaseDerivedPushforwardComparison`: the proposition that the
  change of base commutes with `Rf_*`, for arbitrary morphisms.
* `AlgebraicGeometry.Space.SmallerBasePerfectComparison`: the proposition that the change of base
  preserves and reflects perfectness.

## Main results

* `AlgebraicGeometry.Space.isProper_relocalizeSpaceMap_iff`,
  `AlgebraicGeometry.Space.isFlat_relocalizeSpaceMap_iff` and
  `AlgebraicGeometry.Space.isFinitePresentation_relocalizeSpaceMap_iff`: properness, flatness and
  finite presentation do not depend on the base.
* `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_of_relocalize`: perfectness of a
  derived direct image descends from the larger base, given the two comparisons.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0DKX](https://stacks.math.columbia.edu/tag/0DKX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {W S : Scheme.{u}} {hW : B.Contains W} {hS : B.Contains S}
  (h : B.obj hW ⟶ B.obj hS)

/-! ### Spaces and morphisms over the larger base -/

variable {B h}

/-- **Properness does not depend on the base** (Stacks 03ZM). -/
theorem isProper_relocalizeSpaceMap_iff {X Y : AlgebraicSpaces B W hW} (f : X ⟶ Y) :
    IsProper B S hS (relocalizeSpaceMap h f).hom ↔ IsProper B W hW f.hom :=
  isProper_relocalize_iff B W hW S hS h X.2 Y.2 f.hom

/-- **Flatness does not depend on the base**, being an étale-chart condition. -/
theorem isFlat_relocalizeSpaceMap_iff {X Y : AlgebraicSpaces B W hW} (f : X ⟶ Y) :
    IsFlat B S hS (relocalizeSpaceMap h f).hom ↔ IsFlat B W hW f.hom :=
  holdsOnEveryEtaleChart_relocalizeMap_iff B W S hW hS h _ f.hom

/-- **Finite presentation does not depend on the base**: local finite presentation is an
étale-chart condition, and quasi-compactness and quasi-separatedness do not depend on the base. -/
theorem isFinitePresentation_relocalizeSpaceMap_iff {X Y : AlgebraicSpaces B W hW} (f : X ⟶ Y) :
    IsFinitePresentation B S hS (relocalizeSpaceMap h f).hom ↔
      IsFinitePresentation B W hW f.hom :=
  and_congr (holdsOnEveryEtaleChart_relocalizeMap_iff B W S hW hS h _ f.hom)
    (and_congr (isQuasiCompact_relocalize_iff B W hW S hS h f.hom)
      (isQuasiSeparated_relocalize_iff B W hW S hS h f.hom))

/-! ### The derived categories over the two bases -/

section Derived

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable (B h)

/-- The derived categories of an algebraic space over `W` and of its extension over `S` are
equivalent: `AlgebraicGeometry.Space.smallerBaseDerivedEquivalence` at the identity of the
extension. -/
abbrev relocalizeSpaceDerivedEquivalence (X : AlgebraicSpaces B W hW) :
    DerivedCategory (Modules.{u, u} B S hS (relocalizeSpace B hW hS h X).1
        (relocalizeSpace B hW hS h X).2) ≌
      DerivedCategory (Modules.{u, u} B W hW X.1 X.2) :=
  smallerBaseDerivedEquivalence B h (Z := X) (Y := relocalizeSpace B hW hS h X) (Iso.refl _)

/-- **The derived direct image commutes with the change of base** (Stacks 04SG for `Rf_*`), as a
proposition: for morphisms `f : Z₁ ⟶ Z₂` over `W` and `g : Y₁ ⟶ Y₂` over `S`
matched by `εᵢ : Λ_h Zᵢ ≅ Yᵢ`, the change of base
`AlgebraicGeometry.Space.smallerBaseDerivedEquivalence` intertwines the derived direct images:
`Rg_* ⋙ (−)' ≅ (−)' ⋙ Rf_*`. No representability is asked of `f` or `g`.

This is the derived form of `AlgebraicGeometry.Space.smallerBasePushforwardIso`, which is stated
for representable morphisms, through the chart formula of the direct image. For an arbitrary
morphism the direct image is the spaces-étale direct image conjugated by the comparison
equivalences of Stacks 03G1 (`AlgebraicGeometry.Space.smallEtaleDirectImage`), so the comparison
comes from the change of base on the spaces-étale sites and its compatibility with the structure
maps `f^♯`; on derived categories it follows from the uniqueness of right derived functors, the
change of base being exact. -/
def SmallerBaseDerivedPushforwardComparison : Prop :=
  ∀ {Z₁ Z₂ : AlgebraicSpaces B W hW} {Y₁ Y₂ : AlgebraicSpaces B S hS}
    (ε₁ : (OverShriek.relocalizePresheafFunctor h).obj Z₁.1 ≅ Y₁.1)
    (ε₂ : (OverShriek.relocalizePresheafFunctor h).obj Z₂.1 ≅ Y₂.1)
    {f : Z₁ ⟶ Z₂} {g : Y₁ ⟶ Y₂},
    ε₁.hom ≫ g.hom = (OverShriek.relocalizePresheafFunctor h).map f.hom ≫ ε₂.hom →
    Nonempty (derivedModulePushforward B S hS g ⋙ (smallerBaseDerivedEquivalence B h ε₂).functor ≅
      (smallerBaseDerivedEquivalence B h ε₁).functor ⋙ derivedModulePushforward B W hW f)

/-- **Perfectness over the smaller base** (Stacks 08G5 read through Stacks 04SG), as a
proposition: an object of `D(𝒪_Y)` is perfect exactly when the corresponding object
of `D(𝒪_Z)` is. This is the perfect counterpart of
`AlgebraicGeometry.Space.isPseudoCoherent_smallerBaseDerivedEquivalence_iff`: reindexing along an
equivalence of ringed sites which carries the structure sheaf to the structure sheaf preserves
and reflects strictly perfect local models. -/
def SmallerBasePerfectComparison : Prop :=
  ∀ {Z : AlgebraicSpaces B W hW} {Y : AlgebraicSpaces B S hS}
    (ε : (OverShriek.relocalizePresheafFunctor h).obj Z.1 ≅ Y.1)
    (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)),
    (smallEtaleRingedSite B W hW Z.1 Z.2).IsPerfect
        ((smallerBaseDerivedEquivalence B h ε).functor.obj K) ↔
      (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect K

variable {B h}

/-- **Perfectness of a derived direct image descends from the larger base**, from the two
comparisons above: if `R(Λ_h f)_*` of the object of `D(𝒪_{Λ_h X})` corresponding to `E` is
perfect, then `Rf_*E` is perfect. -/
theorem isPerfect_derivedModulePushforward_of_relocalize
    (hpush : SmallerBaseDerivedPushforwardComparison B h) (hperf : SmallerBasePerfectComparison B h)
    {X Y : AlgebraicSpaces B W hW} (f : X ⟶ Y) (E : DerivedCategory (Modules.{u, u} B W hW X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS (relocalizeSpace B hW hS h Y).1
        (relocalizeSpace B hW hS h Y).2).IsPerfect
      ((derivedModulePushforward B S hS (relocalizeSpaceMap h f)).obj
        ((relocalizeSpaceDerivedEquivalence B h X).inverse.obj E))) :
    (smallEtaleRingedSite B W hW Y.1 Y.2).IsPerfect
      ((derivedModulePushforward B W hW f).obj E) := by
  obtain ⟨φ⟩ := hpush (Iso.refl _) (Iso.refl _) (f := f) (g := relocalizeSpaceMap h f) (by simp)
  have h₁ := (hperf (Z := Y) (Y := relocalizeSpace B hW hS h Y) (Iso.refl _) _).2 hE
  exact RingedSite.isPerfect_of_iso _ h₁ (φ.app _ ≪≫ (derivedModulePushforward B W hW f).mapIso
    ((relocalizeSpaceDerivedEquivalence B h X).counitIso.app E))

end Derived

end AlgebraicGeometry.Space

end
