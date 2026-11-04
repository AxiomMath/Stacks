module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Limits
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Basic

/-!
# The small crystalline site over the small Zariski site

An object `(U, T, δ)` of the small crystalline site `Cris(X/S)` has `U ⟶ X` an open immersion, so
`U` is an object of the small Zariski site `X_Zar` of `X`; forgetting the divided power thickening
is a functor `Cris(X/S) ⥤ X_Zar`.  It has a left adjoint, which sends an open `U` of `X` to the
divided power thickening `(U, U, ∅)` of `U` by itself, the ambient scheme carrying the zero
divided power ideal.

Both functors are restrictions of their big site counterparts: `Cris(X/S)` is the full subcategory
of `CRIS(X/S)` on the thickenings whose map to `X` is an open immersion, `X_Zar` is the full
subcategory of `Sch/X` on the objects whose structure morphism is an open immersion, and the
restrictions commute with the two inclusions.  The adjunction is therefore the restriction of the
adjunction between `Sch/X` and `CRIS(X/S)` of [Stacks, Tag 07I8]: a morphism
`(U, U, ∅) ⟶ (V, T, δ)` is determined by its map `U ⟶ V`, because the immersion of `(U, U, ∅)` is
the identity, and the divided power map `U ⟶ T` it forces is one because the divided power ideal
of `U` is zero.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.ZariskiOpen` — the small Zariski site `X_Zar` of the
  scheme `X` of a global crystalline situation.
* `Crystalline.GlobalCrystallineSituation.smallForget` — the forgetful functor
  `Cris(X/S) ⥤ X_Zar`, `(U, T, δ) ↦ U`, [Stacks, Tag 07IH].
* `Crystalline.GlobalCrystallineSituation.smallFree` — the functor `X_Zar ⥤ Cris(X/S)`,
  `U ↦ (U, U, ∅)`, [Stacks, Tag 07II].

## Main results

* `Crystalline.GlobalCrystallineSituation.smallFreeForgetAdjunction` — the functor
  `U ↦ (U, U, ∅)` is left adjoint to the forgetful functor, [Stacks, Tag 07II].

## Implementation notes

`X_Zar` is `MorphismProperty.Over @IsOpenImmersion ⊤ X`, the objects of `Sch/X` whose structure
morphism is an open immersion with all `X`-morphisms between them, which is the definition of
[Stacks, Tag 020T] part (2).  The variant `AlgebraicGeometry.SmallZariski` is relative to a chosen
big Zariski site `B`, with every object required to satisfy `B.Contains`; the thickened scheme of
an object of `CRIS(X/S)` is an arbitrary scheme, so the forgetful functor `Cris(X/S) ⥤ X_Zar` is
stated for the form without that choice.  This matches
`Crystalline.GlobalCrystallineSituation.forget` of [Stacks, Tag 07I7], which models `(Sch/X)_Zar`
as `Over X`.

## References

* [Stacks Project, Tag 07IH](https://stacks.math.columbia.edu/tag/07IH)
* [Stacks Project, Tag 07II](https://stacks.math.columbia.edu/tag/07II)
* [Stacks Project, Tag 07I8](https://stacks.math.columbia.edu/tag/07I8)
* [Stacks Project, Tag 020T](https://stacks.math.columbia.edu/tag/020T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation

/-- The small Zariski site `X_Zar` of the scheme `X` of a global crystalline situation: the
objects of `Sch/X` whose structure morphism is an open immersion, with all `X`-morphisms between
them. -/
abbrev ZariskiOpen (S : GlobalCrystallineSituation.{u}) :=
  MorphismProperty.Over @AlgebraicGeometry.IsOpenImmersion ⊤ S.X

namespace ZariskiOpen

/-- The inclusion of the small Zariski site of `X` into the category of schemes over `X`. -/
abbrev ι (S : GlobalCrystallineSituation.{u}) : ZariskiOpen S ⥤ Over S.X :=
  MorphismProperty.Over.forget _ _ _

/-- The inclusion `X_Zar ⥤ Sch/X` is fully faithful, the small Zariski site being a full
subcategory of the category of schemes over `X`: a morphism of `X_Zar` is a morphism of `Sch/X`
and nothing more. -/
def fullyFaithfulι (S : GlobalCrystallineSituation.{u}) : (ι S).FullyFaithful where
  preimage f := MorphismProperty.Over.Hom.mk f trivial

end ZariskiOpen

/-- The forgetful functor `Cris(X/S) ⥤ X_Zar`, `(U, T, δ) ↦ U`, from the small crystalline site
to the small Zariski site: it keeps the scheme `U` with its open immersion into `X`. -/
@[stacks 07IH]
def smallForget (S : GlobalCrystallineSituation.{u}) :
    CrystallineThickening S ⥤ ZariskiOpen S where
  obj A := MorphismProperty.Over.mk ⊤ A.obj.toX A.property
  map f := MorphismProperty.Over.homMk f.hom.sourceHom f.hom.toX_naturality
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The scheme underlying `smallForget S` applied to `(U, T, δ)` is `U`. -/
@[simp]
theorem smallForget_obj_left (S : GlobalCrystallineSituation.{u}) (A : CrystallineThickening S) :
    ((smallForget S).obj A).left = A.obj.thickening.source := rfl

/-- The structure morphism of `smallForget S` applied to `A` is the open immersion of `A` into
`X`. -/
@[simp]
theorem smallForget_obj_hom (S : GlobalCrystallineSituation.{u}) (A : CrystallineThickening S) :
    ((smallForget S).obj A).hom = A.obj.toX := rfl

/-- The morphism of schemes underlying `smallForget S` applied to `f` is the map of `f` on the
thickened schemes. -/
@[simp]
theorem smallForget_map_left (S : GlobalCrystallineSituation.{u})
    {A B : CrystallineThickening S} (f : A ⟶ B) :
    ((smallForget S).map f).left = f.hom.sourceHom := rfl

/-- The functor `X_Zar ⥤ Cris(X/S)` sending an open `U ⟶ X` to the object `(U, U, ∅)` of the
small crystalline site: the scheme `U` thickened by itself, the ambient scheme carrying the zero
divided power ideal. -/
@[stacks 07II "the functor"]
def smallFree (S : GlobalCrystallineSituation.{u}) :
    ZariskiOpen S ⥤ CrystallineThickening S :=
  (Thickening.IsCrystalline (S := S)).lift (ZariskiOpen.ι S ⋙ free S) fun U ↦ U.prop

/-- The thickened scheme of `smallFree S` applied to `U` is `U`. -/
@[simp]
theorem smallFree_obj_source (S : GlobalCrystallineSituation.{u}) (U : ZariskiOpen S) :
    ((smallFree S).obj U).obj.thickening.source = U.left := rfl

/-- The ambient scheme of `smallFree S` applied to `U` is `U` with the zero divided power ideal. -/
@[simp]
theorem smallFree_obj_target (S : GlobalCrystallineSituation.{u}) (U : ZariskiOpen S) :
    ((smallFree S).obj U).obj.thickening.target = trivialDividedPowerScheme U.left := rfl

/-- The closed immersion of `smallFree S` applied to `U` is the identity of `U`. -/
@[simp]
theorem smallFree_obj_immersion (S : GlobalCrystallineSituation.{u}) (U : ZariskiOpen S) :
    ((smallFree S).obj U).obj.thickening.immersion = 𝟙 U.left := rfl

/-- The morphism to `X` of `smallFree S` applied to `U` is the structure morphism of `U`. -/
@[simp]
theorem smallFree_obj_toX (S : GlobalCrystallineSituation.{u}) (U : ZariskiOpen S) :
    ((smallFree S).obj U).obj.toX = U.hom := rfl

/-- The map on thickened schemes of `smallFree S` applied to `f : U ⟶ V` is `f`. -/
@[simp]
theorem smallFree_map_sourceHom (S : GlobalCrystallineSituation.{u}) {U V : ZariskiOpen S}
    (f : U ⟶ V) : ((smallFree S).map f).hom.sourceHom = f.left := rfl

/-- The map on ambient schemes of `smallFree S` applied to `f : U ⟶ V` is `f`. -/
@[simp]
theorem smallFree_map_targetHom_hom (S : GlobalCrystallineSituation.{u}) {U V : ZariskiOpen S}
    (f : U ⟶ V) : ((smallFree S).map f).hom.targetHom.hom = f.left := rfl

/-- The functor `smallFree`, `U ↦ (U, U, ∅)`, is left adjoint to the forgetful functor
`smallForget`: a morphism `(U, U, ∅) ⟶ (V, T, δ)` of the small crystalline site is exactly a
morphism `U ⟶ V` of the small Zariski site. -/
@[stacks 07II "left adjoint"]
def smallFreeForgetAdjunction (S : GlobalCrystallineSituation.{u}) :
    smallFree S ⊣ smallForget S :=
  Adjunction.restrictFullyFaithful (freeForgetAdjunction S) (ZariskiOpen.fullyFaithfulι S)
    (CrystallineThickening.fullyFaithfulι S) (Iso.refl _) (Iso.refl _)

end Crystalline.GlobalCrystallineSituation

end
