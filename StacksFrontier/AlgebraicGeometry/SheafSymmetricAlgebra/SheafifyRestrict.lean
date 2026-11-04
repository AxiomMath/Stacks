module

public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Scheme
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Restriction to an open commutes with sheafification, for presheaves of modules

Let `X` be a scheme, `U` an open of `X` and `P` a presheaf of `𝒪_X`-modules. This file identifies
the restriction to `U` of the sheafification of `P` with the sheafification of the restriction of
`P`, as sheaves of `𝒪_U`-modules:

`(P^#)|_U ≅ (P|_U)^#`.

Restriction is `AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι`, whose sections over `V` are
`Γ(P, U.ι ''ᵁ V)`; its presheaf-level form is
`Stacks.AlgebraicGeometry.SheafifyRestrict.presheafRestrict`.

The comparison is specialized to the degree-`n` piece of
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra`, the sheafified sectionwise symmetric algebra
of a module `E` on an arbitrary scheme, and used to reduce its quasi-coherence condition
`Stacks.SymGraded.IsQuasicoherentPieces` to a statement about an affine base. Since the degree-one
piece is isomorphic to `E`, quasi-coherence of all the pieces implies quasi-coherence of `E`.

## Main definitions

* `Stacks.PresheafOfModules.sheafificationIsoOfIsLocallyBijective`: a locally bijective
  comparison into a sheaf of modules identifies the sheafification with that sheaf.
* `Stacks.AlgebraicGeometry.SheafifyRestrict.presheafRestrict`: restriction of a presheaf of
  modules to an open subscheme.
* `Stacks.AlgebraicGeometry.SheafifyRestrict.restrictSheafificationIso`: the comparison
  `(P|_U)^# ≅ (P^#)|_U`.
* `Stacks.AlgebraicGeometry.SheafifyRestrict.restrictPieceIso`: the same for the degree-`n`
  piece of the sheafified sectionwise symmetric algebra.

## Main results

* `Stacks.PresheafOfModules.isIso_sheafification_map_of_isLocallyBijective`: sheafification
  inverts a locally bijective morphism of presheaves of modules.
* `Stacks.AlgebraicGeometry.SheafifyRestrict.isLocallySurjective_presheafRestrict_map` and
  `isLocallyInjective_presheafRestrict_map`: restriction to an open preserves local surjectivity
  and local injectivity.
* `Stacks.AlgebraicGeometry.SheafifyRestrict.restrictFunctor_obj_val` and
  `presheafRestrict_obj_eq`: the sheaf-level restriction is the presheaf-level one, and its
  sections over `V` are the sections of the original over `U.ι ''ᵁ V`.
* `Stacks.AlgebraicGeometry.SheafifyRestrict.isQuasicoherentPieces_of_restrict_sheafification`:
  `Stacks.SymGraded.IsQuasicoherentPieces` holds as soon as, for every affine open `V` of `X`, the
  sheafification of the restriction to `V` of the sectionwise degree-`n` symmetric power is
  quasi-coherent.

## References

* [Stacks Project, Tag 00WY](https://stacks.math.columbia.edu/tag/00WY)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Stacks.PresheafOfModules

universe v u t a

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]

/-- **Sheafification inverts a locally bijective morphism** of presheaves of modules. -/
theorem isIso_sheafification_map_of_isLocallyBijective
    {P Q : _root_.PresheafOfModules.{a} R₀} (u : P ⟶ Q)
    [_root_.PresheafOfModules.IsLocallyInjective J u]
    [_root_.PresheafOfModules.IsLocallySurjective J u] :
    IsIso ((_root_.PresheafOfModules.sheafification.{a} α).map u) := by
  have h : (MorphismProperty.isomorphisms _).inverseImage
      (_root_.PresheafOfModules.sheafification.{a} α) u := by
    rw [← _root_.PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms α]
    exact J.W_of_isLocallyBijective _
  exact h

/-- **A locally bijective comparison into a sheaf of modules identifies the sheafification.**
Given a sheaf of modules `N` and a locally bijective `u : P ⟶ N`, the sheafification of `P` is
`N`. -/
def sheafificationIsoOfIsLocallyBijective {P : _root_.PresheafOfModules.{a} R₀}
    (N : SheafOfModules.{a} R)
    (u : P ⟶ (SheafOfModules.forget R ⋙ _root_.PresheafOfModules.restrictScalars α).obj N)
    (hinj : _root_.PresheafOfModules.IsLocallyInjective J u)
    (hsurj : _root_.PresheafOfModules.IsLocallySurjective J u) :
    (_root_.PresheafOfModules.sheafification.{a} α).obj P ≅ N :=
  haveI := hinj
  haveI := hsurj
  haveI := isIso_sheafification_map_of_isLocallyBijective α u
  asIso ((_root_.PresheafOfModules.sheafification.{a} α).map u) ≪≫
    (asIso ((_root_.PresheafOfModules.sheafificationAdjunction.{a} α).counit)).app N

end Stacks.PresheafOfModules

namespace Stacks.AlgebraicGeometry.SheafifyRestrict

universe u

variable {X : Scheme.{u}} (U : X.Opens)

/-! ### Restriction of a presheaf of modules to an open subscheme -/

/-- The comparison of structure presheaves along the inclusion of an open subscheme. It is the
identity, by `AlgebraicGeometry.Scheme.Opens.ι_appIso`. -/
def opensComparison : (U : Scheme.{u}).presheaf ⟶ U.ι.opensFunctor.op ⋙ X.presheaf where
  app V := (U.ι.appIso V.unop).inv

/-- The comparison of structure *sheaves* along the inclusion of an open subscheme. -/
def ringComparison : (U : Scheme.{u}).ringCatSheaf ⟶
    (U.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (U : Scheme.{u})) (Opens.grothendieckTopology X)).obj
      X.ringCatSheaf :=
  ⟨Functor.whiskerRight (opensComparison U) (forget₂ CommRingCat RingCat)⟩

/-- **Restriction of a presheaf of modules to an open subscheme.** -/
def presheafRestrict :
    _root_.PresheafOfModules.{u} X.ringCatSheaf.obj ⥤
      _root_.PresheafOfModules.{u} (U : Scheme.{u}).ringCatSheaf.obj :=
  _root_.PresheafOfModules.pushforward (ringComparison U).hom

/-- **The restriction of a sheaf of modules is the restriction of its underlying presheaf**, on
the nose. -/
theorem restrictFunctor_obj_val (M : X.Modules) :
    ((Scheme.Modules.restrictFunctor U.ι).obj M).val = (presheafRestrict U).obj M.val := rfl

/-- **The sections of a restricted presheaf of modules** over `V` are the sections of the given
presheaf over the image of `V`, on the nose. -/
theorem presheafRestrict_obj_eq (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj)
    (V : (U : Scheme.{u}).Opens) :
    (((presheafRestrict U).obj P).obj (op V) : Type u) =
      (P.obj (op (U.ι ''ᵁ V)) : Type u) := rfl

/-! ### Restriction preserves local bijectivity -/

variable {P Q : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj} (v : P ⟶ Q)

/-- **Restriction to an open preserves local surjectivity.** -/
instance isLocallySurjective_presheafRestrict_map
    [_root_.PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) v] :
    _root_.PresheafOfModules.IsLocallySurjective
      (Opens.grothendieckTopology (U : Scheme.{u})) ((presheafRestrict U).map v) :=
  Presheaf.isLocallySurjective_whisker _ (Opens.grothendieckTopology X) U.ι.opensFunctor
    ((_root_.PresheafOfModules.toPresheaf _).map v)

/-- **Restriction to an open preserves local injectivity.** -/
instance isLocallyInjective_presheafRestrict_map
    [_root_.PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) v] :
    _root_.PresheafOfModules.IsLocallyInjective
      (Opens.grothendieckTopology (U : Scheme.{u})) ((presheafRestrict U).map v) :=
  Presheaf.isLocallyInjective_whisker _ (Opens.grothendieckTopology X) U.ι.opensFunctor
    ((_root_.PresheafOfModules.toPresheaf _).map v)

/-- The sheafification unit of a presheaf of modules on a scheme is locally surjective. -/
instance isLocallySurjective_sheafifyUnit
    (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :
    _root_.PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      (_root_.PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) P) :=
  inferInstanceAs (Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf))

/-- The sheafification unit of a presheaf of modules on a scheme is locally injective. -/
instance isLocallyInjective_sheafifyUnit
    (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :
    _root_.PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
      (_root_.PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) P) :=
  inferInstanceAs (Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf))

/-! ### The comparison -/

/-- **Restriction to an open commutes with sheafification, for presheaves of modules**: the
sheafification of the restriction of `P` to `U` is the restriction to `U` of the sheafification
of `P`. -/
def restrictSheafificationIso (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :
    (_root_.PresheafOfModules.sheafification (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)).obj
        ((presheafRestrict U).obj P) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj
        ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) :=
  Stacks.PresheafOfModules.sheafificationIsoOfIsLocallyBijective
    (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)
    ((Scheme.Modules.restrictFunctor U.ι).obj
      ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P))
    ((presheafRestrict U).map
      (_root_.PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) P))
    (isLocallyInjective_presheafRestrict_map U
      (_root_.PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) P))
    (isLocallySurjective_presheafRestrict_map U
      (_root_.PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) P))

/-! ### The homogeneous pieces of the sheafified sectionwise symmetric algebra -/

/-- **The degree-`n` piece of `Sym(E)`, restricted to an open**, is the sheafification of the
restriction to that open of the presheaf of sectionwise degree-`n` symmetric powers. -/
def restrictPieceIso (E : X.Modules) (n : ℤ) :
    (_root_.PresheafOfModules.sheafification (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)).obj
        ((presheafRestrict U).obj (Stacks.SymGraded.siteGradedPiece E.val n)) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj
        ((Scheme.Modules.symmetricAlgebra X E).piece n : X.Modules) :=
  restrictSheafificationIso U (Stacks.SymGraded.siteGradedPiece E.val n)

/-- **`Stacks.SymGraded.IsQuasicoherentPieces` on an arbitrary scheme is reduced to an affine
base.** It suffices that for every affine open `V` of `X` and every degree `n`, the
sheafification of the restriction to `V` of the presheaf of sectionwise degree-`n` symmetric
powers of `E` is quasi-coherent. -/
theorem isQuasicoherentPieces_of_restrict_sheafification (E : X.Modules)
    (h : ∀ (n : ℤ) (V : X.affineOpens),
      ((_root_.PresheafOfModules.sheafification
            (𝟙 ((V : X.Opens) : Scheme.{u}).ringCatSheaf.obj)).obj
          ((presheafRestrict (V : X.Opens)).obj (Stacks.SymGraded.siteGradedPiece E.val n)) :
        ((V : X.Opens) : Scheme.{u}).Modules).IsQuasicoherent) :
    Stacks.SymGraded.IsQuasicoherentPieces E :=
  Stacks.SymGraded.isQuasicoherentPieces_of_restrict_affineOpens E fun n V =>
    (SheafOfModules.isQuasicoherent ((V : X.Opens) : Scheme.{u}).ringCatSheaf).prop_of_iso
      (restrictPieceIso (V : X.Opens) E n) (h n V)

end Stacks.AlgebraicGeometry.SheafifyRestrict

end
