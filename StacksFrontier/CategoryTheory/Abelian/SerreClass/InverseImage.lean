module

public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# The isomorphisms modulo a Serre class, under an exact functor

Let `F : C ⥤ D` be an exact functor between abelian categories and let `Q` be a Serre class in
`D`.  Then the inverse image `Q.inverseImage F` is a Serre class in `C`, and its class of
isomorphisms-modulo-Serre is the inverse image of that of `Q`:

`(Q.inverseImage F).isoModSerre = Q.isoModSerre.inverseImage F`.

## Main results

* `CategoryTheory.ObjectProperty.isoModSerre_eq_inverseImage_of_iff`: the displayed equality,
  stated with the correspondence of the two Serre classes given *pointwise* as
  `∀ A, P A ↔ Q (F.obj A)`.
* `CategoryTheory.ObjectProperty.respectsIso_isoModSerre`: the isomorphisms modulo a Serre class
  respect isomorphisms.
* `CategoryTheory.ObjectProperty.localizerMorphismOfIff`: the localizer morphism attached to such
  a correspondence, and
  `CategoryTheory.ObjectProperty.isLocalizedEquivalence_localizerMorphismOfIff`: it is a localized
  equivalence as soon as `F` is an equivalence.
-/

@[expose] public section

open CategoryTheory.Limits

universe v v' u u'

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]

/-- **The isomorphisms modulo a Serre class are carried to the isomorphisms modulo its inverse
image by an exact functor.**  Here `P A ↔ Q (F.obj A)` for every object `A` of `C`. -/
theorem isoModSerre_eq_inverseImage_of_iff {P : ObjectProperty C} {Q : ObjectProperty D}
    [P.IsSerreClass] [Q.IsSerreClass] (F : C ⥤ D) [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (h : ∀ A : C, P A ↔ Q (F.obj A)) :
    P.isoModSerre = Q.isoModSerre.inverseImage F := by
  ext A B f
  change (P (kernel f) ∧ P (cokernel f)) ↔ (Q (kernel (F.map f)) ∧ Q (cokernel (F.map f)))
  rw [h (kernel f), h (cokernel f), Q.prop_iff_of_iso (PreservesKernel.iso F f),
    Q.prop_iff_of_iso (PreservesCokernel.iso F f)]

/-- **The localizer morphism attached to a correspondence of Serre classes.**  An exact functor
`F : C ⥤ D` carrying a Serre class `P` of `C` to a Serre class `Q` of `D`, in the sense that
`P A ↔ Q (F.obj A)` for every `A`, is a morphism of localizers from the isomorphisms modulo `P` to
the isomorphisms modulo `Q`. -/
def localizerMorphismOfIff {P : ObjectProperty C} {Q : ObjectProperty D} [P.IsSerreClass]
    [Q.IsSerreClass] (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (h : ∀ A : C, P A ↔ Q (F.obj A)) : LocalizerMorphism P.isoModSerre Q.isoModSerre :=
  LocalizerMorphism.ofEq (isoModSerre_eq_inverseImage_of_iff F h)

/-- The functor of `localizerMorphismOfIff F h` is `F`. -/
@[simp] theorem localizerMorphismOfIff_functor {P : ObjectProperty C} {Q : ObjectProperty D}
    [P.IsSerreClass] [Q.IsSerreClass] (F : C ⥤ D) [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (h : ∀ A : C, P A ↔ Q (F.obj A)) :
    (localizerMorphismOfIff F h).functor = F :=
  rfl

/-- The localizer morphism of a correspondence of Serre classes is induced. -/
instance isInduced_localizerMorphismOfIff {P : ObjectProperty C} {Q : ObjectProperty D}
    [P.IsSerreClass] [Q.IsSerreClass] (F : C ⥤ D) [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (h : ∀ A : C, P A ↔ Q (F.obj A)) :
    (localizerMorphismOfIff F h).IsInduced :=
  ⟨(isoModSerre_eq_inverseImage_of_iff F h).symm⟩

/-- **An equivalence matching two Serre classes induces an equivalence of the Serre quotients.**
If `F` is an equivalence with `P A ↔ Q (F.obj A)` for every `A`, then `localizerMorphismOfIff F h`
is a localized equivalence. -/
theorem isLocalizedEquivalence_localizerMorphismOfIff {P : ObjectProperty C}
    {Q : ObjectProperty D} [P.IsSerreClass] [Q.IsSerreClass] (F : C ⥤ D) [F.IsEquivalence]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (h : ∀ A : C, P A ↔ Q (F.obj A)) :
    (localizerMorphismOfIff F h).IsLocalizedEquivalence :=
  have : Q.isoModSerre.RespectsIso := MorphismProperty.respectsIso_of_isStableUnderComposition
      Q.isomorphisms_le_isoModSerre
  have : (localizerMorphismOfIff F h).functor.IsEquivalence := inferInstanceAs F.IsEquivalence
  LocalizerMorphism.isLocalizedEquivalence_of_isInduced _

end CategoryTheory.ObjectProperty

end
