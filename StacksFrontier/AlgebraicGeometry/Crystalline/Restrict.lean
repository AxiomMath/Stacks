module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Basic

/-!
# Restriction of a divided power scheme to an open subscheme

Let `(X, I, γ)` be a divided power scheme and let `V` be an open subset of `X`.  The sections of
`𝒪_X` over an open of the open subscheme `V` are the sections of `𝒪_X` over its image in `X`, so
the ideal sheaf `I` and its divided power structure restrict to `V` objectwise, and the resulting
data make `V` a divided power scheme with a canonical morphism to `(X, I, γ)` whose underlying
morphism of schemes is the open immersion.  A divided power thickening of schemes restricts in the
same way along an open of its ambient scheme.

## Main definitions

* `AlgebraicGeometry.Scheme.Opens.restrictSubmodule` — the restriction of an ideal subsheaf of the
  structure sheaf to an open subscheme.
* `Crystalline.DividedPowerStructure.restrictOpen` — the restriction of a divided power structure.
* `Crystalline.DividedPowerScheme.restrict` — the restriction of a divided power scheme.
* `Crystalline.DividedPowerScheme.restrictι` — the canonical morphism `X.restrict V ⟶ X`.
* `Crystalline.DividedPowerScheme.restrictLE` — the morphism `X.restrict V ⟶ X.restrict V'` for
  `V ≤ V'`.
* `Crystalline.SchemeThickening.restrict` — the restriction of a divided power thickening along an
  open of its ambient scheme.

## Main results

* `AlgebraicGeometry.Scheme.Opens.isQuasicoherent_restrictSubmodule` — the restriction of a
  quasi-coherent ideal subsheaf is quasi-coherent.
* `Crystalline.DividedPowerScheme.isIso_restrictι_top` — restricting to the whole space gives an
  isomorphism of underlying schemes.
* `Stacks.Thickenings.IsThickening.morphismRestrict` — a thickening restricts to a thickening over
  any open of the ambient scheme.

## Implementation notes

The structure sheaf of the open subscheme `V` is, by construction, the composition of `𝒪_X` with
the open-image functor, so the restricted ideal subsheaf can be defined objectwise by
`W ↦ I(V.ι ''ᵁ W)`; the locality of its membership condition comes from the locality of `I` and
the fact that the open-image functor preserves covers.  Quasi-coherence is transported from
Mathlib's `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor`: the restriction
functor on sheaves of modules is the pushforward along the morphism of sheaves of rings built from
`AlgebraicGeometry.Scheme.Hom.appIso`, which for an open immersion `V.ι` is the identity, and
pushing forward along the identity is the objectwise restriction used here.

## References

* [Stacks Project, Tag 07I3](https://stacks.math.columbia.edu/tag/07I3)
* [Stacks Project, Tag 07I4](https://stacks.math.columbia.edu/tag/07I4)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry
open Stacks.Thickenings

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Opens

variable {X : Scheme.{u}} (V : X.Opens)
  (N : (SheafOfModules.unit X.ringCatSheaf).Submodule)

/-- **The restriction of an ideal subsheaf of `𝒪_X` to an open subscheme `V`.**  Its sections over
an open `W` of `V` are the sections of the given subsheaf over the image of `W` in `X`. -/
def restrictSubmodule : (SheafOfModules.unit V.toScheme.ringCatSheaf).Submodule where
  obj W := N.obj (op (V.ι ''ᵁ W.unop))
  map {_ _} f _ hx := N.map_mem (V.ι.opensFunctor.map f.unop).op hx
  isSheaf := by
    intro W s hs
    refine N.isSheaf (X := op (V.ι ''ᵁ W.unop)) s fun x hx ↦ ?_
    obtain ⟨W', f, hmem, hxW'⟩ := hs ⟨x, V.ι_image_le _ hx⟩ (V.mem_ι_image_iff.mp hx)
    exact ⟨V.ι ''ᵁ W', V.ι.opensFunctor.map f, hmem, V.mem_ι_image_iff.mpr hxW'⟩

/-- The sections of `V.restrictSubmodule N` over an open `W` of `V` are the sections of `N` over
the image of `W` in `X`. -/
@[simp]
theorem restrictSubmodule_obj (W : V.toScheme.Opensᵒᵖ) :
    (V.restrictSubmodule N).obj W = N.obj (op (V.ι ''ᵁ W.unop)) :=
  rfl

/-- **The identification of `𝒪_V` with the pushforward of `𝒪_X` along an open immersion.**  On
sections over an open `W` of `V` both sides are the sections of `𝒪_X` over the image of `W`, and
the morphism is the identity. -/
def restrictRingHom : V.toScheme.ringCatSheaf ⟶
    (V.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology V.toScheme) (Opens.grothendieckTopology X)).obj
      X.ringCatSheaf :=
  ⟨𝟙 _⟩

/-- The comparison morphism of presheaves of commutative rings underlying Mathlib's restriction
functor on sheaves of modules, given on sections by the inverse of
`AlgebraicGeometry.Scheme.Hom.appIso`. -/
def restrictPresheafHom : V.toScheme.presheaf ⟶ V.ι.opensFunctor.op ⋙ X.presheaf where
  app U := (V.ι.appIso U.unop).inv

/-- The morphism of sheaves of rings along which Mathlib's restriction functor on sheaves of
modules over `V` is a pushforward. -/
def restrictRingHom' : V.toScheme.ringCatSheaf ⟶
    (V.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology V.toScheme) (Opens.grothendieckTopology X)).obj
      X.ringCatSheaf :=
  ⟨Functor.whiskerRight V.restrictPresheafHom (forget₂ CommRingCat RingCat)⟩

/-- **The two comparison morphisms agree.**  On an open immersion of the form `V.ι` the morphism
on sections is the identity. -/
theorem restrictRingHom'_eq : V.restrictRingHom' = V.restrictRingHom := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ ?_))
  have h : (V.ι.appIso U.unop).inv = 𝟙 Γ(V.toScheme, U.unop) := by
    rw [Scheme.Opens.ι_appIso]; rfl
  show (forget₂ CommRingCat RingCat).map ((V.ι.appIso U.unop).inv) = _
  exact (congrArg (fun g ↦ (forget₂ CommRingCat RingCat).map g) h).trans
    ((forget₂ CommRingCat RingCat).map_id _)

/-- **The restriction of a quasi-coherent ideal subsheaf of `𝒪_X` to an open subscheme is
quasi-coherent.**  It is the pushforward of the given subsheaf along the identification of `𝒪_V`
with the pushforward of `𝒪_X`, hence isomorphic to its Mathlib restriction. -/
theorem isQuasicoherent_restrictSubmodule [N.toSheafOfModules.IsQuasicoherent] :
    (V.restrictSubmodule N).toSheafOfModules.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso
    ((SheafOfModules.pushforwardCongr V.restrictRingHom'_eq).app N.toSheafOfModules)
    (Scheme.Modules.isQuasicoherent_restrictFunctor.{u} V.ι N.toSheafOfModules)

end AlgebraicGeometry.Scheme.Opens

namespace Crystalline

open AlgebraicGeometry

/-- **The restriction of a divided power structure on an ideal subsheaf of `𝒪_X` to an open
subscheme.**  Over an open `W` of `V` it is the given divided power structure on the sections over
the image of `W` in `X`. -/
def DividedPowerStructure.restrictOpen {X : Scheme.{u}} (V : X.Opens)
    {N : (SheafOfModules.unit X.ringCatSheaf).Submodule}
    (gamma : DividedPowerStructure.{u, u, u} X.sheaf N) :
    DividedPowerStructure.{u, u, u} V.toScheme.sheaf (V.restrictSubmodule N) where
  dividedPowers W := gamma.dividedPowers (op (V.ι ''ᵁ W.unop))
  naturality f := gamma.naturality (V.ι.opensFunctor.map f.unop).op

/-- Over an open `W` of `V`, the restricted divided power structure is the divided power structure
`gamma` on the sections over the image of `W` in `X`. -/
@[simp]
theorem DividedPowerStructure.restrictOpen_dividedPowers {X : Scheme.{u}} (V : X.Opens)
    {N : (SheafOfModules.unit X.ringCatSheaf).Submodule}
    (gamma : DividedPowerStructure.{u, u, u} X.sheaf N) (W : V.toScheme.Opensᵒᵖ) :
    (gamma.restrictOpen V).dividedPowers W = gamma.dividedPowers (op (V.ι ''ᵁ W.unop)) :=
  rfl

namespace DividedPowerScheme

variable (X : DividedPowerScheme.{u}) (V : X.scheme.Opens)

/-- **The restriction of a divided power scheme to an open subscheme.**  Its underlying scheme is
the open subscheme `V`, and its ideal sheaf and divided power structure are the restrictions of
those of `X`. -/
def restrict : DividedPowerScheme.{u} where
  scheme := V.toScheme
  ideal := V.restrictSubmodule X.ideal
  isQuasicoherent := V.isQuasicoherent_restrictSubmodule X.ideal
  dividedPowers := X.dividedPowers.restrictOpen V

/-- The underlying scheme of `X.restrict V` is the open subscheme `V`. -/
@[simp]
theorem restrict_scheme : (X.restrict V).scheme = V.toScheme := rfl

/-- The ideal sheaf of `X.restrict V` is the restriction of the ideal sheaf of `X` to `V`. -/
@[simp]
theorem restrict_ideal : (X.restrict V).ideal = V.restrictSubmodule X.ideal := rfl

/-- The divided power structure of `X.restrict V` is the restriction of that of `X` to `V`. -/
@[simp]
theorem restrict_dividedPowers : (X.restrict V).dividedPowers =
    X.dividedPowers.restrictOpen V := rfl

/-- **The canonical morphism from the restriction of a divided power scheme to an open subscheme.**
Its underlying morphism of schemes is the open immersion of `V`, and the compatibility with the
divided powers is the compatibility of the divided power structure of `X` with restriction. -/
def restrictι : X.restrict V ⟶ X where
  hom := V.ι
  compatible U := X.dividedPowers.naturality
    (homOfLE (x := V.ι ''ᵁ V.ι ⁻¹ᵁ U) (Set.image_preimage_subset _ _)).op

/-- The underlying morphism of schemes of `X.restrictι V` is the open immersion `V.ι`. -/
@[simp]
theorem restrictι_hom : (X.restrictι V).hom = V.ι := rfl

/-- The morphism from a restriction is an open immersion on underlying schemes. -/
instance : IsOpenImmersion (X.restrictι V).hom :=
  inferInstanceAs (IsOpenImmersion V.ι)

/-- **Restricting to the whole space does not change the underlying scheme.** -/
instance isIso_restrictι_top : IsIso (X.restrictι ⊤).hom :=
  inferInstanceAs (IsIso X.scheme.topIso.hom)

variable {V}

/-- The map on sections of the inclusion of a smaller open subscheme is a morphism of divided
power rings, being a restriction map of the structure sheaf of `X`. -/
theorem isDPMorphism_homOfLE_app {V' : X.scheme.Opens} (h : V ≤ V') (U : V'.toScheme.Opens) :
    DividedPowers.IsDPMorphism
      (X.dividedPowers.dividedPowers (op (V'.ι ''ᵁ U)))
      (X.dividedPowers.dividedPowers (op (V.ι ''ᵁ (X.scheme.homOfLE h ⁻¹ᵁ U))))
      ((X.scheme.homOfLE h).app U).hom := by
  rw [Scheme.homOfLE_app]
  exact X.dividedPowers.naturality _

/-- **The inclusion of a smaller open subscheme as a morphism of divided power schemes.** -/
def restrictLE {V' : X.scheme.Opens} (h : V ≤ V') : X.restrict V ⟶ X.restrict V' where
  hom := X.scheme.homOfLE h
  compatible U := X.isDPMorphism_homOfLE_app h U

/-- The underlying morphism of schemes of `X.restrictLE h` is the inclusion `X.scheme.homOfLE h` of
open subschemes. -/
@[simp]
theorem restrictLE_hom {V' : X.scheme.Opens} (h : V ≤ V') :
    (X.restrictLE h).hom = X.scheme.homOfLE h :=
  rfl

/-- Restriction to a smaller open subscheme is compatible with the morphisms to `X`. -/
@[reassoc (attr := simp)]
theorem restrictLE_restrictι {V' : X.scheme.Opens} (h : V ≤ V') :
    X.restrictLE h ≫ X.restrictι V' = X.restrictι V :=
  Hom.ext (by simp)

end DividedPowerScheme

/-- **A thickening restricts to a thickening over any open of the ambient scheme.**  Being a
closed immersion is local at the target, and the restriction of a surjection to the preimage of an
open is surjective. -/
theorem Stacks.Thickenings.IsThickening.morphismRestrict {Y Z : Scheme.{u}} {i : Y ⟶ Z}
    (hi : IsThickening i) (U : Z.Opens) : IsThickening (i ∣_ U) := by
  have := hi.1
  refine ⟨inferInstance, ?_⟩
  rw [morphismRestrict_base]
  exact hi.2.restrictPreimage _

namespace SchemeThickening

variable (D : SchemeThickening.{u}) (V : D.target.scheme.Opens)

/-- **The restriction of a divided power thickening of schemes along an open of its ambient
scheme.**  The ambient divided power scheme is restricted to `V`, the thickened scheme to the
preimage of `V`, and the immersion is the restriction of the immersion. -/
def restrict : SchemeThickening.{u} where
  source := (D.immersion ⁻¹ᵁ V).toScheme
  target := D.target.restrict V
  immersion := D.immersion ∣_ V
  isThickening := Stacks.Thickenings.IsThickening.morphismRestrict D.isThickening V
  ideal_eq_ker W := by
    have hW : IsAffineOpen (X := V.toScheme) W.1 := W.2
    exact (D.ideal_eq_ker ⟨V.ι ''ᵁ W.1, hW.image_of_isOpenImmersion V.ι⟩).trans
      (Scheme.ker_morphismRestrict_ideal D.immersion V W).symm

/-- The thickened scheme of `D.restrict V` is the preimage of `V` under the immersion of `D`. -/
@[simp]
theorem restrict_source : (D.restrict V).source = (D.immersion ⁻¹ᵁ V).toScheme := rfl

/-- The ambient divided power scheme of `D.restrict V` is the restriction of that of `D` to
`V`. -/
@[simp]
theorem restrict_target : (D.restrict V).target = D.target.restrict V := rfl

/-- The immersion of `D.restrict V` is the restriction `D.immersion ∣_ V` of the immersion of
`D`. -/
@[simp]
theorem restrict_immersion : (D.restrict V).immersion = D.immersion ∣_ V := rfl

end SchemeThickening

end Crystalline

end

end
