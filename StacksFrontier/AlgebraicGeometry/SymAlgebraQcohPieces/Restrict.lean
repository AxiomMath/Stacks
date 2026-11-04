module

public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.SheafifyRestrict
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange

/-!
# Restriction along an open immersion commutes with sheafification

`StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.SheafifyRestrict` identifies the
restriction to an open *subscheme* of the sheafification of a presheaf of modules with the
sheafification of its restriction. **This file is that statement for an arbitrary open
immersion of schemes**, which is what a reduction to an affine base needs: the affine model of
an affine open `V` of `X` is `Spec Γ(X, V)`, and the morphism exhibiting it is
`AlgebraicGeometry.IsAffineOpen.fromSpec`, not the inclusion of an open.

It also records the transport of quasi-coherence between the two, from `fromSpec` to the
inclusion `V.ι`.

## Main definitions

* `Stacks.AlgebraicGeometry.ImmersionRestrict.presheafRestrict`: **restriction of a presheaf of
  modules along an open immersion**, the presheaf-level form of
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor`.
* `Stacks.AlgebraicGeometry.ImmersionRestrict.restrictSheafificationIso`: **the comparison**
  `(P|_f)^# ≅ (P^#)|_f`.

## Main results

* `Stacks.AlgebraicGeometry.ImmersionRestrict.restrictFunctor_obj_val`: the sheaf-level
  restriction of Mathlib is the presheaf-level one here, on the nose.
* `Stacks.AlgebraicGeometry.ImmersionRestrict.isQuasicoherent_restrict_ι_of_fromSpec`:
  **quasi-coherence of the restriction to `Spec Γ(X, V)` gives it for the restriction to `V`**,
  for `V` an affine open. The two differ by the isomorphism `V ≅ Spec Γ(X, V)`.

## Implementation notes

Everything here is the corresponding declaration of
`Stacks.AlgebraicGeometry.SheafifyRestrict` with the inclusion `U.ι` of an open subscheme
replaced by an arbitrary open immersion `f`. That generalization costs nothing: Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` is *defined* for an arbitrary open immersion
by the comparison `U ↦ (f.appIso U).inv` of structure presheaves, so
`restrictFunctor_obj_val` below is still `rfl`, and the cocontinuity of `f.opensFunctor` that
carries local surjectivity and local injectivity across is an instance for an arbitrary open
immersion of schemes. The specialization to `U.ι` was not a simplification, only a choice.

## References

* [Stacks Project, Tag 00WY](https://stacks.math.columbia.edu/tag/00WY)

## Not done here

**No tag is claimed.** Tag 00WY is sheafification against pushforward along a continuous and
cocontinuous functor for presheaves valued in an arbitrary category, recorded elsewhere as
`Stacks.nonempty_pushforwardContinuousSheafificationCompatibility`; nothing here asserts it.

Nothing is said about the restriction of the *multiplication* of a graded algebra, nor about
the comparison for a morphism that is not an open immersion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Stacks.AlgebraicGeometry.ImmersionRestrict

universe u

variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

/-! ### Restriction of a presheaf of modules along an open immersion -/

/-- The comparison of structure presheaves along an open immersion, in the shape
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` uses, so that the two restrictions agree on
the nose. -/
def opensComparison : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf where
  app W := (f.appIso W.unop).inv

/-- The comparison of structure *sheaves* along an open immersion. -/
def ringComparison : Y.ringCatSheaf ⟶
    (f.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj X.ringCatSheaf :=
  ⟨Functor.whiskerRight (opensComparison f) (forget₂ CommRingCat RingCat)⟩

/-- **Restriction of a presheaf of modules along an open immersion.** -/
def presheafRestrict :
    PresheafOfModules.{u} X.ringCatSheaf.obj ⥤ PresheafOfModules.{u} Y.ringCatSheaf.obj :=
  PresheafOfModules.pushforward (ringComparison f).hom

/-- **The restriction of a sheaf of modules is the restriction of its underlying presheaf**, on
the nose. -/
theorem restrictFunctor_obj_val (M : X.Modules) :
    ((Scheme.Modules.restrictFunctor f).obj M).val = (presheafRestrict f).obj M.val := rfl

/-- **The sections of a restricted presheaf of modules** over `W` are the sections of the given
presheaf over the image of `W`, on the nose. -/
theorem presheafRestrict_obj_eq (P : PresheafOfModules.{u} X.ringCatSheaf.obj) (W : Y.Opens) :
    (((presheafRestrict f).obj P).obj (op W) : Type u) = (P.obj (op (f ''ᵁ W)) : Type u) := rfl

/-! ### Restriction preserves local bijectivity -/

variable {P Q : PresheafOfModules.{u} X.ringCatSheaf.obj} (v : P ⟶ Q)

/-- **Restriction along an open immersion preserves local surjectivity**: an open immersion is
cocontinuous, so a covering sieve of an open of the source is obtained from one of its image. -/
instance isLocallySurjective_presheafRestrict_map
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) v] :
    PresheafOfModules.IsLocallySurjective
      (Opens.grothendieckTopology Y) ((presheafRestrict f).map v) :=
  Presheaf.isLocallySurjective_whisker _ (Opens.grothendieckTopology X) f.opensFunctor
    ((PresheafOfModules.toPresheaf _).map v)

/-- **Restriction along an open immersion preserves local injectivity.** -/
instance isLocallyInjective_presheafRestrict_map
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) v] :
    PresheafOfModules.IsLocallyInjective
      (Opens.grothendieckTopology Y) ((presheafRestrict f).map v) :=
  Presheaf.isLocallyInjective_whisker _ (Opens.grothendieckTopology X) f.opensFunctor
    ((PresheafOfModules.toPresheaf _).map v)

/-! ### The comparison -/

/-- **Restriction along an open immersion commutes with sheafification, for presheaves of
modules**: the sheafification of the restriction of `P` along `f` is the restriction along `f`
of the sheafification of `P`. -/
def restrictSheafificationIso (P : PresheafOfModules.{u} X.ringCatSheaf.obj) :
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj ((presheafRestrict f).obj P) ≅
      (Scheme.Modules.restrictFunctor f).obj
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) :=
  Stacks.PresheafOfModules.sheafificationIsoOfIsLocallyBijective (𝟙 Y.ringCatSheaf.obj)
    ((Scheme.Modules.restrictFunctor f).obj
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P))
    ((presheafRestrict f).map (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) P))
    (isLocallyInjective_presheafRestrict_map f
      (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) P))
    (isLocallySurjective_presheafRestrict_map f
      (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) P))

/-! ### Transport of quasi-coherence from the affine model to the open -/

/-- **Quasi-coherence of the restriction to `Spec Γ(X, V)` gives it for the restriction to the
affine open `V`.** The two restrictions differ by the isomorphism
`AlgebraicGeometry.IsAffineOpen.isoSpec`. -/
theorem isQuasicoherent_restrict_ι_of_fromSpec {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) (M : X.Modules) (h : (M.restrict hV.fromSpec).IsQuasicoherent) :
    (M.restrict V.ι).IsQuasicoherent := by
  have := h
  have h2 : ((M.restrict hV.fromSpec).restrict hV.isoSpec.hom).IsQuasicoherent := inferInstance
  have iso : (M.restrict hV.fromSpec).restrict hV.isoSpec.hom ≅ M.restrict V.ι :=
    ((Scheme.Modules.restrictFunctorComp hV.isoSpec.hom hV.fromSpec).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hV.isoSpec_hom_fromSpec).app M
  exact (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso iso h2

end Stacks.AlgebraicGeometry.ImmersionRestrict

end
