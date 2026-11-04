module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Limits
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.SectionsDividedPowerRing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalCoverDoubleComplex

/-!
# The trivial thickenings of the affine opens of `X`

Fix a global crystalline situation `(p, (S, I, γ), X)`.  An affine open `V` of `X` gives the
trivial divided power thickening `(V, V, 0)` of [Stacks, Tag 07I8], the image of the open immersion
`V ⟶ X` under `Crystalline.GlobalCrystallineSituation.free`; its structure map to `X` is an open
immersion and its ambient scheme `V` is affine, so it is an object of the full subcategory
`AffineCris S` of `Cris(X/S)`.  This file packages that construction as a functor on the affine
opens of `X`, and records that a nonempty finite family of affine opens of a scheme with affine
diagonal (for instance a separated one) has a product among the affine opens, namely its
intersection.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.AffineOpens` — the affine opens of a scheme, as a full
  subcategory of its opens.
* `Crystalline.GlobalCrystallineSituation.trivialThickeningFunctor` — `V ↦ (V, V, 0)`, from the
  affine opens of `X` to `AffineCris S`.
* `Crystalline.GlobalCrystallineSituation.AffineOpens.isLimitInfFan` — the intersection of a family
  of opens is their product among the opens.

## Main results

* `Crystalline.GlobalCrystallineSituation.AffineOpens.hasProduct` — on a scheme with affine
  diagonal, a nonempty finite family of affine opens has a product in `AffineOpens X`.
* `Crystalline.GlobalCrystallineSituation.AffineOpens.piObj_obj` — its underlying open is the
  intersection of the members.

## References

* [Stacks Project, Tag 07I8](https://stacks.math.columbia.edu/tag/07I8)
* [Stacks Project, Tag 01KP](https://stacks.math.columbia.edu/tag/01KP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation

/-- **The affine opens of a scheme**, as the full subcategory of its opens on the affine ones. -/
abbrev AffineOpens (X : Scheme.{u}) : Type u :=
  ObjectProperty.FullSubcategory (fun V : X.Opens ↦ IsAffineOpen V)

namespace AffineOpens

variable {X : Scheme.{u}}

/-- The inclusion of the affine opens into the opens. -/
abbrev ι (X : Scheme.{u}) : AffineOpens X ⥤ X.Opens :=
  ObjectProperty.ι _

/-- An affine open of `X` is affine. -/
instance isAffine_obj (V : AffineOpens X) : IsAffine (V.obj : Scheme.{u}) :=
  V.property

/-- **The intersection of a family of opens is their product** among the opens of `X`. -/
def isLimitInfFan {J : Type*} (G : J → X.Opens) :
    IsLimit (Fan.mk (⨅ j, G j) fun j ↦ homOfLE (iInf_le G j)) :=
  Fan.IsLimit.mk _ (fun s ↦ homOfLE (le_iInf fun j ↦ leOfHom (s.proj j)))
    (fun _ _ ↦ rfl) (fun _ _ _ ↦ rfl)

variable [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- **A nonempty finite family of affine opens has a product among the affine opens**, on a
scheme with affine diagonal: the intersection, which is affine. -/
theorem hasProduct {J : Type*} [Finite J] [Nonempty J] (G : J → AffineOpens X) :
    HasProduct G :=
  Stacks.CechSite.FinalCover.hasProduct_fullSubcategory_of_isLimit G
    (isLimitInfFan fun j ↦ (G j).obj) (IsAffineOpen.iInf fun j ↦ (G j).property)

attribute [local instance] hasProduct

/-- The products of the tuples of members of a family of affine opens, the shape asked for by the
Čech complex `Stacks.CechSite.FinalCover.complexFunctor`. -/
instance hasProduct_tuple {ι : Type*} (U : ι → AffineOpens X) (n : ℕ) (x : Fin (n + 1) → ι) :
    HasProduct fun a ↦ U (x a) :=
  hasProduct _

/-- The intersection of a nonempty finite family of affine opens, as an affine open. -/
def inf {J : Type*} [Finite J] [Nonempty J] (G : J → AffineOpens X) : AffineOpens X :=
  ⟨⨅ j, (G j).obj, IsAffineOpen.iInf fun j ↦ (G j).property⟩

/-- **The underlying open of the product of a nonempty finite family of affine opens is the
intersection of its members.** -/
theorem piObj_obj {J : Type*} [Finite J] [Nonempty J] (G : J → AffineOpens X) :
    (∏ᶜ G).obj = ⨅ j, (G j).obj :=
  le_antisymm (le_iInf fun j ↦ leOfHom (Pi.π G j).hom)
    (leOfHom (Pi.lift (f := G) (P := inf G)
      fun j ↦ ObjectProperty.homMk (homOfLE (iInf_le (fun j ↦ (G j).obj) j))).hom)

end AffineOpens

variable (S : GlobalCrystallineSituation.{u})

/-- The trivial thickening `(V, V, 0)` of an affine open `V` of `X` is an object of `Cris(X/S)`:
its structure map to `X` is the open immersion `V ⟶ X`. -/
def trivialCrisObject (V : AffineOpens S.X) : CrystallineThickening S :=
  ⟨(free S).obj (Over.mk V.obj.ι), (inferInstance : IsOpenImmersion V.obj.ι)⟩

/-- **The trivial thickening `(V, V, 0)` of [Stacks, Tag 07I8], as a functor from the affine opens
of `X` to the objects of `Cris(X/S)` with affine ambient scheme**: an affine open `V` goes to the
image of the open immersion `V ⟶ X` under `free`, and an inclusion `V ⊆ V'` to the image of the
open immersion `V ⟶ V'` over `X`. -/
def trivialThickeningFunctor : AffineOpens S.X ⥤ AffineCris S :=
  ObjectProperty.lift _
    (ObjectProperty.lift _ (AffineOpens.ι S.X ⋙ S.X.restrictFunctor ⋙ free S)
      fun V ↦ (inferInstance : IsOpenImmersion V.obj.ι))
    fun V ↦ (inferInstance : IsAffine (V.obj : Scheme.{u}))

/-- The trivial thickening of an affine open, in `Cris(X/S)`. -/
theorem trivialThickeningFunctor_obj_obj (V : AffineOpens S.X) :
    ((trivialThickeningFunctor S).obj V).obj = trivialCrisObject S V :=
  rfl

/-- The trivial thickening of an affine open, in `CRIS(X/S)`. -/
theorem trivialThickeningFunctor_obj_obj_obj (V : AffineOpens S.X) :
    ((trivialThickeningFunctor S).obj V).obj.obj = (free S).obj (Over.mk V.obj.ι) :=
  rfl

/-- The trivial thickening of an inclusion of affine opens, in `CRIS(X/S)`. -/
theorem trivialThickeningFunctor_map_hom_hom {V V' : AffineOpens S.X} (f : V ⟶ V') :
    ((trivialThickeningFunctor S).map f).hom.hom =
      (free S).map (S.X.restrictFunctor.map f.hom) :=
  rfl

/-- The ambient scheme of the trivial thickening of an affine open `V` is `V`. -/
theorem trivialThickeningFunctor_target (V : AffineOpens S.X) :
    ((trivialThickeningFunctor S).obj V).obj.obj.thickening.target.scheme = V.obj :=
  rfl

end Crystalline.GlobalCrystallineSituation
