module

public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Sections
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.Sections
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Basic
public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.Groupoids.FittingIdealSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksFrontier.AlgebraicGeometry.OpensSheafificationInstances

/-!
# The twisted square: sections of an invertible module on a scheme covered by two closed subschemes

Let `X` be a scheme and `I₁`, `I₂` two quasi-coherent ideal sheaves with `I₁ ⊓ I₂ = ⊥`, so that
the scheme-theoretic union of the two closed subschemes they cut out is all of `X`.
`StacksDraft.AlgebraicGeometry.F3b.AffineClosedUnion.Sections` proves that the sections of the
*structure sheaf* over any open then form a fibre product. This file carries that statement
across the twist by an invertible sheaf of modules `L`: the square

```
Γ(L, V) --------------> Γ(i₁^*L, i₁⁻¹V)
   |                         |
   v                         v
Γ(i₂^*L, i₂⁻¹V) -----> Γ((i₁⊔i₂)^*L, (i₁⊔i₂)⁻¹V)
```

is cartesian as well, which is the form the proof of
[Stacks, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX) consumes — there `L` is a tensor
power `L^{⊗ m}` of an ample invertible sheaf and the statement is applied to a section vanishing
on the intersection.

## The route, and which of its five ingredients cost anything

The square above is the image of the *untwisted* square under the functor `- ⊗_{𝒪_X} L`, and all
four of its corners are then identified by the projection formula. Explicitly:

1. the untwisted square of structure sheaves is a pullback **in `X.Modules`** — this is
   `Stacks.AffineClosedUnion.isPullback_unitToPushforwardStructureSheaf_of_inf_eq_bot`, which
   reduces to sections over every open by
   `CategoryTheory.IsPullback.of_forall_isPullback_app` together with the fact that
   `AlgebraicGeometry.Scheme.Modules.toPresheaf` is faithful and preserves limits, and then to
   the ring square of `Sections.lean` because the two forgetful functors to `Type` carry the two
   squares to the *same* square of functions;
2. tensoring on the right by an invertible module is an equivalence
   (`Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence`), hence preserves
   pullbacks;
3. the corner `𝒪_X ⊗ L` is `L` by the left unit constraint
   (`Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor`);
4. the corners `i_*𝒪_Z ⊗ L` are `i_*(i^*L)` by the projection formula at a closed immersion
   (`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso`) followed by the same
   unit constraint on `Z`;
5. `Γ(i_*M, V) = Γ(M, i⁻¹V)` is definitional
   (`AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj`).

The only input that is not formal is (1).

## Implementation notes

**Three spellings of the category of modules on a scheme meet here, and all three crossings are
`rfl`.** `AlgebraicGeometry.Scheme.Modules X`, then
`SheafOfModules (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)`
— the spelling the projection formula is stated at — and
`SheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.toRingedSpace.presheaf
  _)` — the spelling the tensor
product and its invertible-module theory are stated at — are definitionally the same category;
`Stacks.RingedSpace.pushforwardFunctor f.toLRSHom.toShHom` and
`AlgebraicGeometry.Scheme.Modules.pushforward f` are definitionally the same functor, likewise for
the pullbacks, and `(Stacks.RingedSpace.tensorSheaf X.toRingedSpace).obj (A, L)` is definitionally
`(Stacks.SheafOfModules.Invertible.tensorRightFunctor _ _ L).obj A`. No bridging declaration is
needed and none is written: `twistPushforwardIso` applies the projection-formula
isomorphism directly at the `Scheme.Modules` spelling.

What does *not* cross for free is **instance search**, as elsewhere in this development: the
equivalence `(twistFunctor X L).IsEquivalence` exists but is not found, because unfolding the
abbreviation presents the structure presheaf in a different normal form from the one the
hypothesis is keyed at. The cure is the usual one — a local instance with a declared return
type, `isEquivalence_twistFunctor`, after which `IsPullback.map` finds everything it needs.

**The legs of the twisted square are canonical by construction, and `twistedUnit` is identified
with the unit of `i^* ⊣ i_*` in the sibling file
`StacksDraft.AlgebraicGeometry.F3b.AffineClosedUnion.TwistedUnit`**, where
`Stacks.AffineClosedUnion.twistedUnit_eq_unit` proves
`twistedUnit i L = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L` and
`twistedUnit_app_apply` reads its sections as `Stacks.RingedSpace.pullbackUnit`. The route is to
transpose under the adjunction, which reduces the claim to one coherence of the pullback tensor
comparison with the left unit constraints; `simp` on the definitional unfolding makes no progress
on it. **`twistedRestrict` is still not so identified**: the corresponding statement would say
that it is `i_*` of the unit of `g^* ⊣ g_*` conjugated by `Scheme.Modules.pushforwardComp`, and
proving it needs the projection formula at `i` as an *inverse*, which the computation for
`twistedUnit` never does. Consumers that need the restriction legs to be literally restriction of
sections should read that as the remaining open obligation.

## Main definitions

* `Stacks.AffineClosedUnion.unitToPushforwardStructureSheaf`: the comparison `𝒪_X ⟶ f_*𝒪_Y` of
  sheaves of `𝒪_X`-modules, whose sections over an open are literally
  `AlgebraicGeometry.Scheme.Hom.app`.
* `Stacks.AffineClosedUnion.pushforwardStructureSheafRestrict`: the restriction
  `f_*𝒪_Y ⟶ (g ≫ f)_*𝒪_W`, whose sections over an open are literally
  `AlgebraicGeometry.Scheme.Hom.appLE`.
* `Stacks.AffineClosedUnion.twistPushforwardIso`: the projection formula `i_*𝒪_Z ⊗ L ≅ i_*(i^*L)`
  at a closed immersion.
* `Stacks.AffineClosedUnion.twistedUnit` and `Stacks.AffineClosedUnion.twistedRestrict`: the two
  kinds of leg of the twisted square.

## Main results

* `Stacks.AffineClosedUnion.isPullback_app_of_inf_eq_bot`: the cartesian square of sections of
  the structure sheaf over an **arbitrary** open, in `CommRingCat`. The
  `Stacks.AffineClosedUnion.isPullback_appTop_of_inf_eq_bot` is the case `V = ⊤`, and
  `control_isPullback_appTop_of_isPullback_app` below derives it, so no generality is lost.
* `Stacks.AffineClosedUnion.isPullback_unitToPushforwardStructureSheaf_of_inf_eq_bot`: the
  untwisted square as a pullback in `X.Modules`.
* `Stacks.AffineClosedUnion.isPullback_twistedUnit_of_inf_eq_bot`: **the twisted square**, as a
  pullback in `X.Modules`.
* `Stacks.AffineClosedUnion.existsUnique_twisted_app_eq_of_inf_eq_bot` and
  `Stacks.AffineClosedUnion.existsUnique_twisted_app_eq_zero_of_inf_eq_bot`: the twisted square
  on elements, over an arbitrary open, the second being the vanishing form [Stacks, Tag 09NX]
  consumes.

No `@[stacks]` attribute is attached to anything in this file. The twisted square is not the
statement of any tag: [Stacks, Tag 09NW] is the ring-level remark, formalized elsewhere, and
[Stacks, Tag 09NX] is the ampleness criterion, whose own declaration is not proved here.

## References

* [Stacks Project, Tag 09NW](https://stacks.math.columbia.edu/tag/09NW)
* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace Stacks.AffineClosedUnion

-- Seated from `OpensSheafificationInstances`, not restated: sheafification for the site of
-- opens of a scheme, and its weak equivalences.
attribute [local instance]
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

noncomputable section

/-! ### The two kinds of leg, before the twist -/

/-- The comparison `𝒪_X ⟶ f_*𝒪_Y` of sheaves of `𝒪_X`-modules attached to a morphism of schemes.
Over an open `U` it is `AlgebraicGeometry.Scheme.Hom.app`, by definition. -/
abbrev unitToPushforwardStructureSheaf {Y X : Scheme.{u}} (f : Y ⟶ X) :
    Stacks.AlgebraicGeometry.PicardBaseChange.unitModule X ⟶
      Stacks.Morphisms.pushforwardStructureSheaf f :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

/-- Over an open `U`, `unitToPushforwardStructureSheaf f` sends a section `a` to `f.app U a`. -/
@[simp]
lemma unitToPushforwardStructureSheaf_app_apply {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    (a : Γ(X, U)) : (unitToPushforwardStructureSheaf f).app U a = (f.app U).hom a := rfl

/-- The restriction `f_*𝒪_Z ⟶ k_*𝒪_W` along a factorisation `k = g ≫ f`. Over an open `U` it is
`AlgebraicGeometry.Scheme.Hom.appLE` for `g`, by definition. -/
def pushforwardStructureSheafRestrict {W Z X : Scheme.{u}} (g : W ⟶ Z) (i : Z ⟶ X)
    {k : W ⟶ X} (hk : g ≫ i = k) :
    Stacks.Morphisms.pushforwardStructureSheaf i ⟶
      Stacks.Morphisms.pushforwardStructureSheaf k :=
  (Scheme.Modules.pushforward i).map (unitToPushforwardStructureSheaf g) ≫
    (Scheme.Modules.pushforwardComp g i).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr hk).hom.app _

/-- Over an open `U`, `pushforwardStructureSheafRestrict g i hk` sends a section `a` of `𝒪_Z` over
`i⁻¹ U` to its image under `g.appLE`. -/
@[simp]
lemma pushforwardStructureSheafRestrict_app_apply {W Z X : Scheme.{u}} (g : W ⟶ Z) (i : Z ⟶ X)
    {k : W ⟶ X} (hk : g ≫ i = k) (U : X.Opens) (a : Γ(Z, i ⁻¹ᵁ U)) :
    (pushforwardStructureSheafRestrict g i hk).app U a =
      (g.appLE (i ⁻¹ᵁ U) (k ⁻¹ᵁ U) (le_of_eq (by rw [← hk]; rfl))).hom a := rfl

/-! ### The untwisted square -/

section Untwisted

variable {X : Scheme.{u}} (I₁ I₂ : X.IdealSheafData)

/-- **The cartesian square of sections of the structure sheaf over an arbitrary open.** The
statement `Stacks.AffineClosedUnion.isPullback_appTop_of_inf_eq_bot` is the case `V = ⊤`; the
general case is read off the element-level statements of `Sections.lean` through
`CategoryTheory.Limits.Types.isPullback_iff`, the forgetful functor from `CommRingCat` being
faithful and reflecting limits. -/
theorem isPullback_app_of_inf_eq_bot (h : I₁ ⊓ I₂ = ⊥) (V : X.Opens) :
    IsPullback (I₁.subschemeι.app V) (I₂.subschemeι.app V)
      (interRestrictLeft I₁ I₂ V) (interRestrictRight I₁ I₂ V) :=
  IsPullback.of_map_of_faithful (forget CommRingCat) ((Types.isPullback_iff _ _ _ _).2
    ⟨by rw [← Functor.map_comp, ← Functor.map_comp, app_interRestrictLeft, app_interRestrictRight],
      fun _ _ hxy => app_ext_of_inf_eq_bot I₁ I₂ h V hxy.1 hxy.2,
      exists_app_eq_of_inf_eq_bot I₁ I₂ h V⟩)

/-- **The untwisted square as a pullback in `X.Modules`.** A sheaf of modules on a scheme is a
limit precisely when its sections over every open are, and over every open the square is the ring
square of `Stacks.AffineClosedUnion.isPullback_app_of_inf_eq_bot`: the two forgetful functors to
`Type` carry the square of abelian groups and the square of rings to the same square of
functions. -/
theorem isPullback_unitToPushforwardStructureSheaf_of_inf_eq_bot (h : I₁ ⊓ I₂ = ⊥) :
    IsPullback (unitToPushforwardStructureSheaf I₁.subschemeι)
      (unitToPushforwardStructureSheaf I₂.subschemeι)
      (pushforwardStructureSheafRestrict (inclusion (le_sup_left : I₁ ≤ I₁ ⊔ I₂))
        I₁.subschemeι (inclusion_subschemeι _))
      (pushforwardStructureSheafRestrict (inclusion (le_sup_right : I₂ ≤ I₁ ⊔ I₂))
        I₂.subschemeι (inclusion_subschemeι _)) :=
  IsPullback.of_map_of_faithful (Scheme.Modules.toPresheaf X)
    (IsPullback.of_forall_isPullback_app fun U => IsPullback.of_map_of_faithful
      (forget AddCommGrpCat)
      ((isPullback_app_of_inf_eq_bot I₁ I₂ h U.unop).map (forget CommRingCat)))

end Untwisted

/-! ### The twist -/

section Twist

/-- Tensoring on the right by `L`, as an endofunctor of `X.Modules`. -/
abbrev twistFunctor (X : Scheme.{u}) (L : X.Modules) : X.Modules ⥤ X.Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨X.toRingedSpace.presheaf,
    Presheaf.isSheaf_of_isSheaf_comp _ X.toRingedSpace.presheaf (forget₂ CommRingCat RingCat)
      (structureSheafRing X.toRingedSpace).property⟩).flip.obj L

variable {X : Scheme.{u}}

/-- Tensoring by an invertible module is an equivalence. The declared return type is what makes
instance search see this: unfolding `twistFunctor` presents the structure presheaf in a normal
form the hypothesis is not keyed at, so the bare instance is not found. -/
local instance isEquivalence_twistFunctor (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] :
    (twistFunctor X L).IsEquivalence :=
  Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence
    X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property L

/-- `𝒪_X ⊗ L ≅ L`, the left unit constraint of the sheaf tensor product. -/
def twistUnitIso (L : X.Modules) :
    (twistFunctor X L).obj (Stacks.AlgebraicGeometry.PicardBaseChange.unitModule X) ≅ L :=
  Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor _ _ L

/-- **The projection formula at a closed immersion, at the `Scheme.Modules` spelling.**
`i_*𝒪_Z ⊗_{𝒪_X} L ≅ i_*(i^*L)`: the
`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso`, whose statement is
definitionally of this shape, followed by the left unit constraint on `Z`. -/
def twistPushforwardIso {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (L : X.Modules) :
    (twistFunctor X L).obj (Stacks.Morphisms.pushforwardStructureSheaf i) ≅
      (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L) :=
  Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso i _ L ≪≫
    (Scheme.Modules.pushforward i).mapIso
      (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor _ _ _)

/-- The twist of the comparison `𝒪_X ⟶ i_*𝒪_Z`: the canonical map `L ⟶ i_*(i^*L)`. -/
def twistedUnit {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (L : X.Modules) :
    L ⟶ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L) :=
  (twistUnitIso L).inv ≫ (twistFunctor X L).map (unitToPushforwardStructureSheaf i) ≫
    (twistPushforwardIso i L).hom

/-- The twist of the restriction `i_*𝒪_Z ⟶ k_*𝒪_W`: the canonical map
`i_*(i^*L) ⟶ k_*(k^*L)` attached to a factorisation `k = g ≫ i` through two closed
immersions. -/
def twistedRestrict {W Z : Scheme.{u}} (g : W ⟶ Z) (i : Z ⟶ X) {k : W ⟶ X}
    (hk : g ≫ i = k) [IsClosedImmersion i] [IsClosedImmersion k] (L : X.Modules) :
    (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L) ⟶
      (Scheme.Modules.pushforward k).obj ((Scheme.Modules.pullback k).obj L) :=
  (twistPushforwardIso i L).inv ≫
    (twistFunctor X L).map (pushforwardStructureSheafRestrict g i hk) ≫
    (twistPushforwardIso k L).hom

variable (I₁ I₂ : X.IdealSheafData)

/-- **The twisted square.** For an invertible sheaf of modules `L` on `X` and two quasi-coherent
ideal sheaves meeting in zero, `L` is the fibre product of `i₁_*(i₁^*L)` and `i₂_*(i₂^*L)` over
`k_*(k^*L)`, `k` being the inclusion of the scheme-theoretic intersection. Tensoring by `L` is an
equivalence, so it carries the untwisted square to a pullback; the four corners are then
identified by the unit constraint and the projection formula. -/
theorem isPullback_twistedUnit_of_inf_eq_bot (h : I₁ ⊓ I₂ = ⊥) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] :
    IsPullback (twistedUnit I₁.subschemeι L) (twistedUnit I₂.subschemeι L)
      (twistedRestrict (inclusion (le_sup_left : I₁ ≤ I₁ ⊔ I₂)) I₁.subschemeι
        (inclusion_subschemeι _) L)
      (twistedRestrict (inclusion (le_sup_right : I₂ ≤ I₁ ⊔ I₂)) I₂.subschemeι
        (inclusion_subschemeι _) L) := by
  refine ((isPullback_unitToPushforwardStructureSheaf_of_inf_eq_bot I₁ I₂ h).map
      (twistFunctor X L)).of_iso' (twistUnitIso L).symm
      (twistPushforwardIso I₁.subschemeι L).symm (twistPushforwardIso I₂.subschemeι L).symm
      (twistPushforwardIso (I₁ ⊔ I₂).subschemeι L).symm ?_ ?_ ?_ ?_ <;>
    simp [twistedUnit, twistedRestrict]

/-- **The twisted square on elements, over an arbitrary open.** A pair of sections of the two
pulled-back modules agreeing on the scheme-theoretic intersection comes from a unique section of
`L`. -/
theorem existsUnique_twisted_app_eq_of_inf_eq_bot (h : I₁ ⊓ I₂ = ⊥) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] (V : X.Opens)
    (a : Γ((Scheme.Modules.pullback I₁.subschemeι).obj L, I₁.subschemeι ⁻¹ᵁ V))
    (b : Γ((Scheme.Modules.pullback I₂.subschemeι).obj L, I₂.subschemeι ⁻¹ᵁ V))
    (hab : (twistedRestrict (inclusion (le_sup_left : I₁ ≤ I₁ ⊔ I₂)) I₁.subschemeι
          (inclusion_subschemeι _) L).app V a =
        (twistedRestrict (inclusion (le_sup_right : I₂ ≤ I₁ ⊔ I₂)) I₂.subschemeι
          (inclusion_subschemeι _) L).app V b) :
    ∃! c : Γ(L, V), (twistedUnit I₁.subschemeι L).app V c = a ∧
      (twistedUnit I₂.subschemeι L).app V c = b := by
  have H := (((isPullback_twistedUnit_of_inf_eq_bot I₁ I₂ h L).map
    (Scheme.Modules.toPresheaf X)).app (Opposite.op V)).map (forget AddCommGrpCat)
  obtain ⟨c, hc₁, hc₂⟩ := Types.exists_of_isPullback H a b hab
  exact ⟨c, ⟨hc₁, hc₂⟩, fun d hd =>
    Types.ext_of_isPullback H (hd.1.trans hc₁.symm) (hd.2.trans hc₂.symm)⟩

/-- **The form [Stacks, Tag 09NX] consumes, twisted.** A section of `i₂^*L` over the preimage of
`V` which vanishes on the scheme-theoretic intersection is the image of a unique section of `L`
over `V` vanishing on the first closed subscheme. -/
theorem existsUnique_twisted_app_eq_zero_of_inf_eq_bot (h : I₁ ⊓ I₂ = ⊥) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] (V : X.Opens)
    (b : Γ((Scheme.Modules.pullback I₂.subschemeι).obj L, I₂.subschemeι ⁻¹ᵁ V))
    (hb : (twistedRestrict (inclusion (le_sup_right : I₂ ≤ I₁ ⊔ I₂)) I₂.subschemeι
      (inclusion_subschemeι _) L).app V b = 0) :
    ∃! c : Γ(L, V), (twistedUnit I₁.subschemeι L).app V c = 0 ∧
      (twistedUnit I₂.subschemeι L).app V c = b :=
  existsUnique_twisted_app_eq_of_inf_eq_bot I₁ I₂ h L V 0 b ((map_zero _).trans hb.symm)

end Twist

end

end Stacks.AffineClosedUnion

end
