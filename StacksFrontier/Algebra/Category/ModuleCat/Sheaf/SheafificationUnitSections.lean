module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricConstruction
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.SheafifyRestrict

/-!
# When the sheafification unit is bijective on the sections over one object

The unit of the sheafification of a presheaf of modules is always *locally* surjective, and that
is the form in which this development uses it: a section of the sheafification lifts along the
unit on a covering sieve (`Stacks.exists_lift_of_liftSieve`). Several arguments need more — that
a section over one specific object of the site is the unit image of an honest section of the
presheaf there, with no passage to a cover. That is not a formal consequence of local
surjectivity, and this file supplies the transfers which make it provable in practice.

All three turn on a single observation. If `u : M ⟶ N` is a locally bijective comparison from a
presheaf of modules into (the underlying presheaf of) a sheaf of modules, then sheafification
inverts `u`, so `Stacks.PresheafOfModules.sheafificationIsoOfIsLocallyBijective` identifies the
sheafification of `M` with `N`; and under that identification the unit *is* `u`. Surjectivity of
the unit over an object and surjectivity of `u` over that object therefore say the same thing,
and either can be read off the other.

## Main results

* `Stacks.PresheafOfModules.sheafificationIsoOfIsLocallyBijective_hom_sheafifyUnit`: **the
  identification of the sheafification carries the unit image of a local section to its
  comparison image.** This is what pins the identification down on sections, and the other three
  results are read off it.
* `Stacks.PresheafOfModules.surjective_sheafifyUnit_app_of_surjective` and
  `surjective_app_of_surjective_sheafifyUnit_app`: **a locally bijective comparison into a sheaf
  is surjective over an object exactly when the unit is.**
* `Stacks.PresheafOfModules.surjective_sheafifyUnit_app_of_isLocallyBijective`: **surjectivity of
  the unit over an object transfers along a locally bijective morphism of presheaves**, in either
  direction of that morphism, because sheafification inverts it.
* `Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff`: **the unit is bijective over an
  object exactly when the comparison is**, and
  `bijective_sheafifyUnit_app_of_isLocallyBijective`: bijectivity transfers along a locally
  bijective morphism whose component over the object is surjective. These are the form in which a
  sheafified homogeneous piece is identified with its sectionwise value over one open: over an
  open where the unit is bijective, and only there, the sections of the sheafification *are* the
  sections of the presheaf.

## Implementation notes

**Local bijectivity is passed as an explicit argument everywhere**, never as an instance. This
follows `Stacks.PresheafOfModules.sheafificationIsoOfIsLocallyBijective`, whose implementation
notes record the measurement: instance search for the local bijectivity of a sheafification unit
fails at these instances even when the sheaf of rings is pinned, because the ring comparison is
given as `𝟙 R.obj` and solving `?R.obj ≟ R.obj` asks the elaborator to invert a projection. The
instances exist and are found when the goal is stated on its own; they are not found when the goal
carries the unsolved `?R`. Naming them is the same device as the one recorded in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SymmetricAlgebraConstruction/Scheme.lean`.

**No new identification of the sheafification is introduced.**
`sheafificationIsoOfIsLocallyBijective` is already `sheafification α` applied to the comparison
followed by the counit, and `Stacks.PresheafOfModules.sheafifyCounitIso` is already the counit as
an isomorphism, so the first result below is `sheafifyCounitIso_map_comp_apply` at this instance
and nothing has to be rebuilt.

## References

* [Stacks Project, Tag 00WY](https://stacks.math.columbia.edu/tag/00WY)

## Not done here

**No tag is claimed.** Tag 00WY is the compatibility of sheafification with pushforward along a
continuous and cocontinuous functor; nothing here asserts it. Nothing here says when the
hypothesis of surjectivity over a given object holds — that is a statement about the site and the
presheaf, proved for the symmetric powers of a quasi-coherent module over an affine open in
`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/GeneratedInDegreeOne.lean`. Nothing here is
said about the *multiplication*: the identification below is of modules of sections, and that it
respects a graded-algebra structure is `Stacks.GradedAlgebra.sheafify_mul_unit`, which lives with
the graded algebra and not here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite PresheafOfModules

namespace Stacks.PresheafOfModules

universe v u t a

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]

/-- **The identification of a sheafification by a locally bijective comparison, read on the
unit.** `Stacks.PresheafOfModules.sheafificationIsoOfIsLocallyBijective` carries the unit image of
a local section of `M` to the image of that section under the comparison `u`.

This pins the identification down on sections: it is `sheafification α` applied to `u` followed by
the counit, so this is `Stacks.PresheafOfModules.sheafifyCounitIso_map_comp_apply` here. -/
theorem sheafificationIsoOfIsLocallyBijective_hom_sheafifyUnit
    {M : _root_.PresheafOfModules.{a} R₀} (N : SheafOfModules.{a} R)
    (u : M ⟶ (SheafOfModules.forget R ⋙ restrictScalars α).obj N)
    (hinj : _root_.PresheafOfModules.IsLocallyInjective J u)
    (hsurj : _root_.PresheafOfModules.IsLocallySurjective J u)
    (X : Cᵒᵖ) (s : M.obj X) :
    (sheafificationIsoOfIsLocallyBijective α N u hinj hsurj).hom.val.app X
        (Hom.app (sheafifyUnit α M) X s) = Hom.app u X s :=
  sheafifyCounitIso_map_comp_apply α N u X s

/-- **A locally bijective comparison into a sheaf which is surjective on the sections over an
object makes the sheafification unit surjective there.** -/
theorem surjective_sheafifyUnit_app_of_surjective
    {M : _root_.PresheafOfModules.{a} R₀} (N : SheafOfModules.{a} R)
    (u : M ⟶ (SheafOfModules.forget R ⋙ restrictScalars α).obj N)
    (hinj : _root_.PresheafOfModules.IsLocallyInjective J u)
    (hsurj : _root_.PresheafOfModules.IsLocallySurjective J u)
    (X : Cᵒᵖ) (hu : Function.Surjective (Hom.app u X)) :
    Function.Surjective (Hom.app (sheafifyUnit α M) X) := by
  set e := sheafificationIsoOfIsLocallyBijective α N u hinj hsurj with he
  intro y
  obtain ⟨s, hs⟩ := hu (e.hom.val.app X y)
  exact ⟨s, (Function.LeftInverse.injective (SheafOfModules.iso_inv_hom_app_apply e X))
    ((sheafificationIsoOfIsLocallyBijective_hom_sheafifyUnit α N u hinj hsurj X s).trans hs)⟩

/-- **Conversely, a surjective sheafification unit over an object makes every locally bijective
comparison into a sheaf surjective there.** -/
theorem surjective_app_of_surjective_sheafifyUnit_app
    {M : _root_.PresheafOfModules.{a} R₀} (N : SheafOfModules.{a} R)
    (u : M ⟶ (SheafOfModules.forget R ⋙ restrictScalars α).obj N)
    (hinj : _root_.PresheafOfModules.IsLocallyInjective J u)
    (hsurj : _root_.PresheafOfModules.IsLocallySurjective J u)
    (X : Cᵒᵖ) (h : Function.Surjective (Hom.app (sheafifyUnit α M) X)) :
    Function.Surjective (Hom.app u X) := by
  set e := sheafificationIsoOfIsLocallyBijective α N u hinj hsurj with he
  intro y
  obtain ⟨z, rfl⟩ := SheafOfModules.iso_hom_app_surjective e X y
  obtain ⟨s, rfl⟩ := h z
  exact ⟨s, (sheafificationIsoOfIsLocallyBijective_hom_sheafifyUnit α N u hinj hsurj X s).symm⟩

/-- **Surjectivity of the sheafification unit over an object transfers along a locally bijective
morphism of presheaves**, because sheafification inverts such a morphism. -/
theorem surjective_sheafifyUnit_app_of_isLocallyBijective
    {M M' : _root_.PresheafOfModules.{a} R₀} (w : M ⟶ M')
    (hinj : _root_.PresheafOfModules.IsLocallyInjective J w)
    (hsurj : _root_.PresheafOfModules.IsLocallySurjective J w)
    (X : Cᵒᵖ) (h : Function.Surjective (Hom.app (sheafifyUnit α M) X)) :
    Function.Surjective (Hom.app (sheafifyUnit α M') X) := by
  have _hi := hinj
  have _hs := hsurj
  have _hiso := isIso_sheafification_map_of_isLocallyBijective α w
  set e : (_root_.PresheafOfModules.sheafification.{a} α).obj M ≅
      (_root_.PresheafOfModules.sheafification.{a} α).obj M' :=
    asIso ((_root_.PresheafOfModules.sheafification.{a} α).map w) with he
  intro y
  obtain ⟨z, rfl⟩ := SheafOfModules.iso_hom_app_surjective e X y
  obtain ⟨s, rfl⟩ := h z
  exact ⟨Hom.app w X s, (unit_naturality_apply w X s).symm⟩

/-- **A locally bijective comparison into a sheaf which is injective on the sections over an
object makes the sheafification unit injective there.** -/
theorem injective_sheafifyUnit_app_of_injective
    {M : _root_.PresheafOfModules.{a} R₀} (N : SheafOfModules.{a} R)
    (u : M ⟶ (SheafOfModules.forget R ⋙ restrictScalars α).obj N)
    (hinj : _root_.PresheafOfModules.IsLocallyInjective J u)
    (hsurj : _root_.PresheafOfModules.IsLocallySurjective J u)
    (X : Cᵒᵖ) (hu : Function.Injective (Hom.app u X)) :
    Function.Injective (Hom.app (sheafifyUnit α M) X) := fun a b hab =>
  hu ((sheafificationIsoOfIsLocallyBijective_hom_sheafifyUnit α N u hinj hsurj X a).symm.trans
    ((congrArg
        (fun z => (sheafificationIsoOfIsLocallyBijective α N u hinj hsurj).hom.val.app X z)
        hab).trans
      (sheafificationIsoOfIsLocallyBijective_hom_sheafifyUnit α N u hinj hsurj X b)))

/-- **Conversely, an injective sheafification unit over an object makes every locally bijective
comparison into a sheaf injective there.** -/
theorem injective_app_of_injective_sheafifyUnit_app
    {M : _root_.PresheafOfModules.{a} R₀} (N : SheafOfModules.{a} R)
    (u : M ⟶ (SheafOfModules.forget R ⋙ restrictScalars α).obj N)
    (hinj : _root_.PresheafOfModules.IsLocallyInjective J u)
    (hsurj : _root_.PresheafOfModules.IsLocallySurjective J u)
    (X : Cᵒᵖ) (h : Function.Injective (Hom.app (sheafifyUnit α M) X)) :
    Function.Injective (Hom.app u X) := by
  set e := sheafificationIsoOfIsLocallyBijective α N u hinj hsurj with he
  intro a b hab
  exact h ((Function.LeftInverse.injective (SheafOfModules.iso_inv_hom_app_apply e X))
    ((sheafificationIsoOfIsLocallyBijective_hom_sheafifyUnit α N u hinj hsurj X a).trans
      (hab.trans
        (sheafificationIsoOfIsLocallyBijective_hom_sheafifyUnit α N u hinj hsurj X b).symm)))

/-- **The sheafification unit is bijective on the sections over an object exactly when a locally
bijective comparison into a sheaf is.**

Over such an object the sections of the sheafification *are* the sections of the presheaf. This is
the general form of the chart-level identification of a sheafified homogeneous piece with its
sectionwise value; for the symmetric powers of a quasi-coherent module it holds over every affine
open, and in general it does not hold over every open. -/
theorem bijective_sheafifyUnit_app_iff
    {M : _root_.PresheafOfModules.{a} R₀} (N : SheafOfModules.{a} R)
    (u : M ⟶ (SheafOfModules.forget R ⋙ restrictScalars α).obj N)
    (hinj : _root_.PresheafOfModules.IsLocallyInjective J u)
    (hsurj : _root_.PresheafOfModules.IsLocallySurjective J u)
    (X : Cᵒᵖ) :
    Function.Bijective (Hom.app (sheafifyUnit α M) X) ↔ Function.Bijective (Hom.app u X) :=
  ⟨fun h => ⟨injective_app_of_injective_sheafifyUnit_app α N u hinj hsurj X h.1,
      surjective_app_of_surjective_sheafifyUnit_app α N u hinj hsurj X h.2⟩,
    fun h => ⟨injective_sheafifyUnit_app_of_injective α N u hinj hsurj X h.1,
      surjective_sheafifyUnit_app_of_surjective α N u hinj hsurj X h.2⟩⟩

/-- **Bijectivity of the sheafification unit over an object transfers along a locally bijective
morphism of presheaves** whose own component over that object is surjective. -/
theorem bijective_sheafifyUnit_app_of_isLocallyBijective
    {M M' : _root_.PresheafOfModules.{a} R₀} (w : M ⟶ M')
    (hinj : _root_.PresheafOfModules.IsLocallyInjective J w)
    (hsurj : _root_.PresheafOfModules.IsLocallySurjective J w)
    (X : Cᵒᵖ) (h : Function.Bijective (Hom.app (sheafifyUnit α M) X))
    (hw : Function.Surjective (Hom.app w X)) :
    Function.Bijective (Hom.app (sheafifyUnit α M') X) := by
  have _hi := hinj
  have _hs := hsurj
  have _hiso := isIso_sheafification_map_of_isLocallyBijective α w
  set e : (_root_.PresheafOfModules.sheafification.{a} α).obj M ≅
      (_root_.PresheafOfModules.sheafification.{a} α).obj M' :=
    asIso ((_root_.PresheafOfModules.sheafification.{a} α).map w) with he
  refine ⟨?_, surjective_sheafifyUnit_app_of_isLocallyBijective α w hinj hsurj X h.2⟩
  intro a b hab
  obtain ⟨a₀, rfl⟩ := hw a
  obtain ⟨b₀, rfl⟩ := hw b
  refine congrArg (Hom.app w X) (h.1 ?_)
  exact (Function.LeftInverse.injective (SheafOfModules.iso_inv_hom_app_apply e X))
    ((unit_naturality_apply w X a₀).trans (hab.trans (unit_naturality_apply w X b₀).symm))

end Stacks.PresheafOfModules

end
