module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.AlgebraicGeometry.QcohLimits.RestrictScalars

/-!
# The quasi-inverse of direct image along an affine morphism

Let `f : X ⟶ S` be a morphism of schemes and let `A = f_* 𝒪_X` be the direct image of the
structure sheaf, a sheaf of rings on `S`.  The direct image of `𝒪_X`-modules, regarded as a
functor to `A`-modules, is
`Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardModules f.base X.ringCatSheaf`,
and for `f` affine it carries quasi-coherent modules to quasi-coherent modules by
`Stacks.AlgebraicGeometry.QcohLimits.affinePushforward_isQuasicoherent`.  Stacks Tag 01SB
asserts that the resulting functor between the categories of quasi-coherent modules is an
equivalence, with quasi-inverse `𝒢 ↦ f^*𝒢 ⊗_{f^*f_*𝒪_X} 𝒪_X`.

This file constructs that quasi-inverse and reduces the assertion of Tag 01SB to three
statements about it, all of which are still open.  The quasi-inverse is *not* built by hand:
`SheafOfModules.pullback` already produces the left adjoint of a direct image along a
continuous functor between sites, and at the identity of `A` its value is exactly
`f^*𝒢 ⊗_{f^*f_*𝒪_X} 𝒪_X`, since both are left adjoint to the direct image over `A`.

## Main definitions

* `Stacks.AlgebraicGeometry.AffineQcohEquivalence.idPushforwardRing` is the identity of
  `f_* 𝒪_X`, given the type which exhibits it as a morphism of sheaves of rings from `f_* 𝒪_X`
  to the direct image of `𝒪_X` along `TopologicalSpace.Opens.map f.base`.
* `Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackModules` is the quasi-inverse
  `𝒢 ↦ f^*𝒢 ⊗_{f^*f_*𝒪_X} 𝒪_X` of Tag 01SB, i.e. the left adjoint of the direct image over
  `f_* 𝒪_X`.
* `Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackPushforwardAdjunction` is the
  adjunction between that functor and the direct image over `f_* 𝒪_X`.
* `Stacks.AlgebraicGeometry.AffineQcohEquivalence.affineQuasicoherentPushforward` is the direct
  image over `f_* 𝒪_X`, restricted from quasi-coherent `𝒪_X`-modules to quasi-coherent
  `f_* 𝒪_X`-modules.  This is the functor whose invertibility is the first assertion of Tag
  01SB.

## Main results

* `Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackModulesObjFreeIso`: the quasi-inverse
  carries a free `f_* 𝒪_X`-module to the free `𝒪_X`-module on the same index type.
* `Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_pullbackModules_of_presentation`:
  the quasi-inverse carries an `f_* 𝒪_X`-module having a presentation over all of `S` to a
  quasi-coherent `𝒪_X`-module.
* `Stacks.AlgebraicGeometry.AffineQcohEquivalence.isEquivalence_affineQuasicoherentPushforward`:
  the reduction of the first assertion of Tag 01SB to three statements, namely that the
  quasi-inverse preserves quasi-coherence and that the unit and the counit of the adjunction are
  invertible at quasi-coherent modules.

## Implementation notes

The existence of the left adjoint is not available to instance search: Mathlib produces it from
`PresheafOfModules.pullbackObjIsDefined_eq_top` and
`SheafOfModules.PullbackConstruction.adjunction`, and both require recognising the codomain of
the identity of `f_* 𝒪_X` as a direct image, which needs a non-reducible definition unfolded.
The two instances here therefore supply the relevant terms explicitly rather than by instance
search; `idPushforwardRing` exists so that the continuous functor between the sites is visible
in the type.

`pullbackModulesObjFreeIso` is Mathlib's `SheafOfModules.pullbackObjFreeIso`, which needs the
functor `TopologicalSpace.Opens.map f.base` between the sites to be final.  That holds for the
inverse image of opens along any continuous map and is recorded as `final_opensMap`: the
structured arrow category at an open `U` consists of the opens `V` of the target with
`U ≤ f ⁻¹ᵁ V`, which is cofiltered because inverse images preserve intersections, and Mathlib
already knows this as `CategoryTheory.RepresentablyFlat`.

**`hL` needs no locality comparison and no mate**: unlike the other two hypotheses, it follows
globally from Tag 01CE as
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_pullbackModules`
(`StacksFrontier/AlgebraicGeometry/AffineQcohEquivalence/QuasicoherentPullback.lean`). Use
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isEquivalence_affineQuasicoherentPushforward`
(`QuasicoherentPullback.lean:284`), which is the same reduction with `hL` discharged, leaving
**two** hypotheses.

What the remaining two hypotheses, `hunit` and `hcounit`, still need is a
comparison of the quasi-inverse with restriction to an open of `S`: each of them is local on
`S`, and over an affine open `V` of `S` with affine inverse image the module in question does
have a presentation, so
`isQuasicoherent_pullbackModules_of_presentation` and the corresponding computations of sections
would apply.  The comparison itself is the mate, in the sense of
`Stacks.CategoryTheory.mateEquiv_symm_congr_left`, of the canonical isomorphism between the two
composites of direct images along the two equal composite functors
`Over V ⥤ Over (f ⁻¹ᵁ V) ⥤ Opens X` and `Over V ⥤ Opens S ⥤ Opens X`; that mate is not
invertible for formal reasons and its invertibility is what remains unproved.

A lower bound on the content of `hunit`, which is not mere plumbing: `isQuasicoherent_extendScalars`
makes `E F` quasi-coherent over `A` for every quasi-coherent `F`, so `hunit` applies at `G = E F`
and, after restricting scalars, yields `F ⊗_{𝒪_S} f_*𝒪_X ≅ f_*(f^* F)`. That is **Tag 0FZE, the
affine projection formula, at `G = 𝒪_X`**, which `Duality/AffineProjectionFormula.lean` records as
open. So `hunit` cannot be cheaper than that case of 0FZE. The entanglement runs both ways:
that file cites this very theorem as blocking 0FZE, and it is this
`hunit`/`hcounit` half that it means, not `hL`.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 0H88](https://stacks.math.columbia.edu/tag/0H88)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.AlgebraicGeometry.AffineQcohEquivalence

open Stacks.AlgebraicGeometry.AffineQcohPushforward

/-! ### Finality of the inverse image of opens -/

/-- The inverse image of opens along a continuous map is a final functor: the opens of the
target containing the image of a given open form a cofiltered category. -/
instance final_opensMap {Y Z : TopCat.{u}} (g : Y ⟶ Z) : (Opens.map g).Final :=
  ⟨fun _ ↦ IsCofiltered.isConnected _⟩

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### The left adjoint of the direct image over `f_* 𝒪_X` -/

/-- The identity of `f_* 𝒪_X`, regarded as a morphism of sheaves of rings from `f_* 𝒪_X` to the
direct image of `𝒪_X` along `TopologicalSpace.Opens.map f.base`.  Spelling the codomain this way
makes the continuous functor between the two sites visible in the type, which is what the
construction of the left adjoint of the direct image needs. -/
def idPushforwardRing : pushforwardRing f.base X.ringCatSheaf ⟶
    ((Opens.map f.base).sheafPushforwardContinuous RingCat.{u} _ _).obj X.ringCatSheaf :=
  𝟙 _

/-- The direct image along `idPushforwardRing f` is the direct image over `f_* 𝒪_X`. -/
theorem pushforward_idPushforwardRing :
    SheafOfModules.pushforward.{u} (idPushforwardRing f) =
      pushforwardModules.{u} f.base X.ringCatSheaf :=
  rfl

/-- The direct image of presheaves of modules along `idPushforwardRing f` is a right adjoint. -/
instance isRightAdjoint_presheafPushforward :
    (PresheafOfModules.pushforward.{u} (idPushforwardRing f).hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top (idPushforwardRing f).hom)

/-- The direct image of sheaves of modules along `idPushforwardRing f` is a right adjoint. -/
instance isRightAdjoint_pushforwardModules :
    (SheafOfModules.pushforward.{u} (idPushforwardRing f)).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u} (idPushforwardRing f)).isRightAdjoint

/-- The quasi-inverse `𝒢 ↦ f^*𝒢 ⊗_{f^*f_*𝒪_X} 𝒪_X` of Stacks Tag 01SB, namely the left adjoint
of the direct image of `𝒪_X`-modules regarded as a functor to `f_* 𝒪_X`-modules. -/
def pullbackModules : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf) ⥤
    SheafOfModules.{u} X.ringCatSheaf :=
  SheafOfModules.pullback.{u} (idPushforwardRing f)

/-- The quasi-inverse of Stacks Tag 01SB is left adjoint to the direct image of `𝒪_X`-modules
over `f_* 𝒪_X`. -/
def pullbackPushforwardAdjunction :
    pullbackModules f ⊣ pushforwardModules.{u} f.base X.ringCatSheaf :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} (idPushforwardRing f)

/-- The quasi-inverse of Stacks Tag 01SB preserves colimits. -/
instance preservesColimitsOfSize_pullbackModules :
    PreservesColimitsOfSize.{u, u} (pullbackModules f) :=
  (pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits

/-! ### Free modules and quasi-coherence -/

/-- The quasi-inverse of Stacks Tag 01SB carries the free `f_* 𝒪_X`-module on a type to the free
`𝒪_X`-module on the same type. -/
def pullbackModulesObjFreeIso (I : Type u) :
    (pullbackModules f).obj (SheafOfModules.free I) ≅ SheafOfModules.free I :=
  SheafOfModules.pullbackObjFreeIso.{u} (idPushforwardRing f) I

/-- A free module on a scheme is quasi-coherent, being a coproduct of copies of the structure
sheaf. -/
theorem isQuasicoherent_free (I : Type u) :
    (SheafOfModules.free.{u} (R := X.ringCatSheaf) I).IsQuasicoherent :=
  QuasicoherentColimits.isQuasicoherent_of_isColimit
    (fun _ ↦ AffineQcohPushforward.isQuasicoherent_unit X)
    (SheafOfModules.isColimitFreeCofan I)

/-- The quasi-inverse of Stacks Tag 01SB carries a free `f_* 𝒪_X`-module to a quasi-coherent
`𝒪_X`-module. -/
theorem isQuasicoherent_pullbackModules_free (I : Type u) :
    ((pullbackModules f).obj (SheafOfModules.free.{u} I)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (pullbackModulesObjFreeIso f I).symm (isQuasicoherent_free I)

/-- The quasi-inverse of Stacks Tag 01SB carries an `f_* 𝒪_X`-module which has a presentation
over all of `S` to a quasi-coherent `𝒪_X`-module: the quasi-inverse preserves the cokernel
exhibiting the presentation, and carries both free modules in it to quasi-coherent modules. -/
theorem isQuasicoherent_pullbackModules_of_presentation
    (G : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) (P : G.Presentation) :
    ((pullbackModules f).obj G).IsQuasicoherent :=
  QuasicoherentColimits.isQuasicoherent_of_isColimit
    (fun k ↦ by cases k <;> exact isQuasicoherent_pullbackModules_free f _)
    (isColimitOfPreserves (pullbackModules f) P.isColimit)

/-! ### The restricted direct image, and the reduction of Stacks Tag 01SB -/

/-- Direct image along an affine morphism, restricted from quasi-coherent `𝒪_X`-modules to
quasi-coherent `f_* 𝒪_X`-modules.  The first assertion of Stacks Tag 01SB is that this functor
is an equivalence of categories. -/
def affineQuasicoherentPushforward [IsAffineHom f] :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent
        (pushforwardRing f.base X.ringCatSheaf)).FullSubcategory :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ pushforwardModules.{u} f.base X.ringCatSheaf)
    (fun M ↦ QcohLimits.affinePushforward_isQuasicoherent f M.obj M.property)

variable (hL : ∀ G : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf),
  G.IsQuasicoherent → ((pullbackModules f).obj G).IsQuasicoherent)

/-- If the quasi-inverse of Stacks Tag 01SB preserves quasi-coherence, it restricts to a functor
from quasi-coherent `f_* 𝒪_X`-modules to quasi-coherent `𝒪_X`-modules. -/
def quasicoherentPullback :
    (SheafOfModules.isQuasicoherent
        (pushforwardRing f.base X.ringCatSheaf)).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ pullbackModules f) fun G ↦ hL G.obj G.property

/-- The unit of the adjunction, at quasi-coherent modules, as an isomorphism of functors between
the full subcategories of quasi-coherent modules. -/
def quasicoherentUnitIso [IsAffineHom f]
    (h : ∀ G : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf),
      G.IsQuasicoherent → IsIso ((pullbackPushforwardAdjunction f).unit.app G)) :
    𝟭 _ ≅ quasicoherentPullback f hL ⋙ affineQuasicoherentPushforward f :=
  NatIso.ofComponents
    (fun G ↦ ObjectProperty.isoMk _ (@asIso _ _ _ _ _ (h G.obj G.property)))
    fun φ ↦ ObjectProperty.hom_ext _ ((pullbackPushforwardAdjunction f).unit.naturality φ.hom)

/-- The counit of the adjunction, at quasi-coherent modules, as an isomorphism of functors
between the full subcategories of quasi-coherent modules. -/
def quasicoherentCounitIso [IsAffineHom f]
    (h : ∀ M : SheafOfModules.{u} X.ringCatSheaf, M.IsQuasicoherent →
      IsIso ((pullbackPushforwardAdjunction f).counit.app M)) :
    affineQuasicoherentPushforward f ⋙ quasicoherentPullback f hL ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ (@asIso _ _ _ _ _ (h M.obj M.property)))
    fun φ ↦ ObjectProperty.hom_ext _ ((pullbackPushforwardAdjunction f).counit.naturality φ.hom)

include hL in
/-- **Reduction of the first assertion of Stacks Tag 01SB.** For an affine morphism, the direct
image restricted to quasi-coherent modules is an equivalence of categories as soon as its left
adjoint preserves quasi-coherence and the unit and counit of the adjunction are invertible at
quasi-coherent modules. -/
theorem isEquivalence_affineQuasicoherentPushforward [IsAffineHom f]
    (hunit : ∀ G : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf),
      G.IsQuasicoherent → IsIso ((pullbackPushforwardAdjunction f).unit.app G))
    (hcounit : ∀ M : SheafOfModules.{u} X.ringCatSheaf, M.IsQuasicoherent →
      IsIso ((pullbackPushforwardAdjunction f).counit.app M)) :
    (affineQuasicoherentPushforward f).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (affineQuasicoherentPushforward f) (quasicoherentPullback f hL)
    (quasicoherentCounitIso f hL hcounit).symm
    (quasicoherentUnitIso f hL hunit).symm).isEquivalence_functor

end Stacks.AlgebraicGeometry.AffineQcohEquivalence

end

end
