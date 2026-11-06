module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatFamilyFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts

/-!
# Two of the three geometric inputs of Stacks 0D1I, from the size-free Stacks 07SK

`StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpaceDescent` reduces **Stacks 0D1I** to three
geometric conditions on an affine cofiltered limit of the big fppf site, and
`StacksFrontier.AlgebraicGeometry.Quot.ProperFlatFamilyFullness` replaces the third of them by a
fullness condition read on arbitrary morphisms. This file discharges two of those conditions
outright, from the size-free form of **Stacks 07SK** proved in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent`:

* `AlgebraicGeometry.ProperFlatMorphismEqualityDescendsAlongAffineLimit` from
  `AlgebraicGeometry.Space.eventually_eq_of_baseChange_eq_affineBase` (faithfulness);
* `AlgebraicGeometry.ProperFlatMorphismDescendsAlongAffineLimit` from
  `AlgebraicGeometry.Space.exists_morphism_after_baseChange_affineBase` (fullness).

## Main results

* `AlgebraicGeometry.properFlatMorphismEqualityDescendsAlongAffineLimit`
* `AlgebraicGeometry.properFlatMorphismDescendsAlongAffineLimit`
* `AlgebraicGeometry.properFlatFamilyIsomorphismDescendsAlongAffineLimit`: the third geometric
  input of Stacks 0D1I, which is now unconditional, being
  `AlgebraicGeometry.properFlatFamilyIsomorphismDescendsAlongAffineLimit_of_fullness` fed with
  the two conditions above.

## Implementation notes

The two conditions are phrased with the *chosen* fibre products `pullback (yoneda.map φ) f`, with
`AlgebraicGeometry.coneBaseRestrict` and `AlgebraicGeometry.pullbackBaseRestrict` for the
restriction maps, whereas Stacks 07SK is phrased with `CategoryTheory.Over.pullback`, whose value
at `f` is the opposite fibre product `pullback f (yoneda.map φ)`, and whose conclusion in the
fullness case comes with comparison isomorphisms rather than with the restriction maps. So the
work here is to instantiate 07SK and transport its conclusion across those comparisons. The
transport is isolated in two groups of private lemmas:

* `AlgebraicGeometry.snd_comp_eq_iff_fst_comp_eq` and
  `AlgebraicGeometry.overPullback_map_homMk_eq_iff` turn an equality of `Over.pullback`-base changes
  into an equality of composites with the chosen second projection, in both directions. This is
  all the faithfulness half needs.
* `AlgebraicGeometry.overPullbackHom` turns a morphism of the chosen fibre products lying over
  the base into a morphism of `Over.pullback`-base changes, and `AlgebraicGeometry.chosenHom`
  turns one back. `AlgebraicGeometry.symmetry_restrict_eq` identifies the restriction map
  `AlgebraicGeometry.coneBaseRestrict` with the first projection of the iterated fibre product
  read through the comparison isomorphism `α` returned by 07SK, and
  `AlgebraicGeometry.comp_overPullbackHom_eq` turns the compatibility equation 07SK returns into
  the one the condition demands.

Of the finite-presentation, flatness and properness hypotheses the two conditions carry, the 07SK
statements ask only for `AlgebraicGeometry.Space.IsFinitePresentation` of the structure morphism,
together with algebraicity of the source. Flatness and properness are not used — they are carried
by the conditions because the fibred category of Stacks 0D1E consists of flat proper families, and
the descent statements of Stacks 07XL are read in that fibred category.

## Index universes

The two conditions quantify over an index category `I : Type v` with `Category.{w} I`, while the
size-free Stacks 07SK is proved for `I : Type u` with `Category.{u} I`. The conditions are
therefore established here at `v = w = u`, i.e. at a *small* index category. That is this
library's canonical form of a Stacks 07XL condition -- a directed set is small -- recorded in the
"Index universes" note of `StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStackInSetoids`
and used by Stacks 0D43, `AlgebraicGeometry.isLimitPreservingPolarizedUnconditional`,
which is registered at a small index category. It is not a weakening of the mathematical content.

## References

* [Stacks Project, Tag 0D1I](https://stacks.math.columbia.edu/tag/0D1I)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- Fibre products of presheaves on the big fppf site over `S`, resolved in one instance step
(the search through `HasLimitsOfShape WalkingCospan` on presheaf categories times out). -/
local instance (priority := high) hasPullback_presheaf_ProperFlatMorphismDescent
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasPullback f g := HasLimitsOfShape.has_limit _

section Transport

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {W X Y Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The two chosen fibre products of a pair of morphisms cancel the same morphisms.** The
fibre product `W ×_Z X` used by the descent conditions and the fibre product `X ×_Z W` produced
by `CategoryTheory.Over.pullback` differ by the symmetry isomorphism, so a composite with the
second projection of the one agrees with another exactly when the corresponding composite with
the first projection of the other does. -/
private theorem snd_comp_eq_iff_fst_comp_eq (p : W ⟶ Z) (f : X ⟶ Z) {a a' : X ⟶ T} :
    pullback.snd p f ≫ a = pullback.snd p f ≫ a' ↔
      pullback.fst f p ≫ a = pullback.fst f p ≫ a' := by
  rw [← pullbackSymmetry_hom_comp_fst p f, Category.assoc, Category.assoc]
  exact Iso.cancel_iso_hom_left _ _ _

/-- **Equality of two base changes in the `Over.pullback` form, read on the chosen fibre
products.** Two vertical morphisms `a, a' : X ⟶ Y` over `Z` have equal base changes along
`p : W ⟶ Z` in the sense of `CategoryTheory.Over.pullback` exactly when their composites with the
second projection of the chosen fibre product `W ×_Z X` agree. -/
private theorem overPullback_map_homMk_eq_iff (f : X ⟶ Z) (g : Y ⟶ Z) (p : W ⟶ Z) {a a' : X ⟶ Y}
    (ha : a ≫ g = f) (ha' : a' ≫ g = f) :
    (Over.pullback p).map (Over.homMk a ha : Over.mk f ⟶ Over.mk g) =
        (Over.pullback p).map (Over.homMk a' ha' : Over.mk f ⟶ Over.mk g) ↔
      pullback.snd p f ≫ a = pullback.snd p f ≫ a' := by
  rw [snd_comp_eq_iff_fst_comp_eq]
  constructor
  · intro h
    simpa [pullback.lift_fst] using congrArg (fun φ => φ.left ≫ pullback.fst g p) h
  · intro h
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · simpa [pullback.lift_fst] using h
    · simp [pullback.lift_snd]

/-- The two symmetry isomorphisms of a pair of fibre products compose to the identity. -/
private theorem pullbackSymmetry_hom_comp_hom (a : X ⟶ Z) (b : Y ⟶ Z) :
    (pullbackSymmetry a b).hom ≫ (pullbackSymmetry b a).hom = 𝟙 (pullback a b) :=
  pullback.hom_ext (by simp) (by simp)

/-- The underlying morphisms of the two directions of an isomorphism of a slice category compose
to the identity. -/
private theorem inv_left_comp_hom_left {Bb : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Pp Qq : Over Bb}
    (α : Pp ≅ Qq) : α.inv.left ≫ α.hom.left = 𝟙 Qq.left := by
  rw [← Over.comp_left, α.inv_hom_id, Over.id_left]

/-- **A morphism of the chosen fibre products lying over the base, read as a morphism of the base
changes in the `Over.pullback` form.** This is the shape in which the fullness half of Stacks 07SK
takes its input. -/
private def overPullbackHom (f : X ⟶ Z) (g : Y ⟶ Z) (p : W ⟶ Z)
    (u : pullback p f ⟶ pullback p g) (hu : u ≫ pullback.fst p g = pullback.fst p f) :
    (Over.pullback p).obj (Over.mk f) ⟶ (Over.pullback p).obj (Over.mk g) :=
  Over.homMk ((pullbackSymmetry f p).hom ≫ u ≫ (pullbackSymmetry p g).hom) (by
    simp only [Over.pullback_obj_hom, Over.mk_hom, Category.assoc,
      pullbackSymmetry_hom_comp_snd, hu, pullbackSymmetry_hom_comp_fst])

@[simp]
private theorem overPullbackHom_left (f : X ⟶ Z) (g : Y ⟶ Z) (p : W ⟶ Z)
    (u : pullback p f ⟶ pullback p g) (hu : u ≫ pullback.fst p g = pullback.fst p f) :
    (overPullbackHom f g p u hu).left =
      (pullbackSymmetry f p).hom ≫ u ≫ (pullbackSymmetry p g).hom :=
  rfl

/-- **A morphism of the base changes in the `Over.pullback` form, read as a morphism of the chosen
fibre products.** This is the shape in which the two descent conditions ask for their output. -/
private def chosenHom (f : X ⟶ Z) (g : Y ⟶ Z) (p : W ⟶ Z)
    (G : (Over.pullback p).obj (Over.mk f) ⟶ (Over.pullback p).obj (Over.mk g)) :
    pullback p f ⟶ pullback p g :=
  (pullbackSymmetry p f).hom ≫ G.left ≫ (pullbackSymmetry g p).hom

/-- `AlgebraicGeometry.chosenHom` lies over the first factor `W`. -/
private theorem chosenHom_comp_fst (f : X ⟶ Z) (g : Y ⟶ Z) (p : W ⟶ Z)
    (G : (Over.pullback p).obj (Over.mk f) ⟶ (Over.pullback p).obj (Over.mk g)) :
    chosenHom f g p G ≫ pullback.fst p g = pullback.fst p f := by
  have hw : G.left ≫ pullback.snd g p = pullback.snd f p := by
    simpa using Over.w G
  simp only [chosenHom, Category.assoc, pullbackSymmetry_hom_comp_fst, hw,
    pullbackSymmetry_hom_comp_snd]

/-- The second projection of `AlgebraicGeometry.chosenHom`, through the symmetry isomorphism. -/
private theorem chosenHom_comp_snd (f : X ⟶ Z) (g : Y ⟶ Z) (p : W ⟶ Z)
    (G : (Over.pullback p).obj (Over.mk f) ⟶ (Over.pullback p).obj (Over.mk g)) :
    chosenHom f g p G ≫ pullback.snd p g =
      (pullbackSymmetry p f).hom ≫ G.left ≫ pullback.fst g p := by
  simp only [chosenHom, Category.assoc, pullbackSymmetry_hom_comp_snd]

/-- **The restriction map to a later base, read through the comparison isomorphism returned by
the fullness half of Stacks 07SK.** The restriction map `ρ` of the descent conditions -- the one
of `AlgebraicGeometry.coneBaseRestrict`, characterised here by its two components `hρfst` and
`hρsnd` -- becomes, after the symmetry isomorphism that passes to the `Over.pullback` form, the
first projection of the iterated fibre product read through `α`. Only the compatibility `hα` of
`α` with the first projections and the fact that `α` lies over the base are used. -/
private theorem symmetry_restrict_eq {P Vi Vj : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Vi)
    (pi : P ⟶ Vi) (pj : P ⟶ Vj) (q : Vj ⟶ Vi) (ρ : pullback pi f ⟶ pullback q f)
    (hρfst : ρ ≫ pullback.fst q f = pullback.fst pi f ≫ pj)
    (hρsnd : ρ ≫ pullback.snd q f = pullback.snd pi f)
    (α : (Over.pullback pj).obj ((Over.pullback q).obj (Over.mk f)) ≅
      (Over.pullback pi).obj (Over.mk f))
    (hα : α.hom.left ≫ pullback.fst f pi =
      pullback.fst (pullback.snd f q) pj ≫ pullback.fst f q) :
    ρ ≫ (pullbackSymmetry q f).hom =
      (pullbackSymmetry pi f).hom ≫ α.inv.left ≫ pullback.fst (pullback.snd f q) pj := by
  have hwinv : α.inv.left ≫ pullback.snd (pullback.snd f q) pj = pullback.snd f pi := by
    simpa using Over.w α.inv
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, hρsnd, Category.assoc, Category.assoc,
      ← hα, ← Category.assoc α.inv.left, inv_left_comp_hom_left, Category.id_comp,
      pullbackSymmetry_hom_comp_fst]
  · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, hρfst, Category.assoc, Category.assoc,
      pullback.condition, ← Category.assoc α.inv.left, hwinv,
      pullbackSymmetry_hom_comp_snd_assoc]

/-- **The compatibility equation returned by the fullness half of Stacks 07SK, read on the chosen
fibre products.** The composite of the morphism `G` at the later stage with the comparison
isomorphism `α` recovers the morphism `u` over the vertex, once both are read on the chosen fibre
products. -/
private theorem comp_overPullbackHom_eq {P Vi Vj : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Vi)
    (g : Y ⟶ Vi) (pi : P ⟶ Vi) (pj : P ⟶ Vj) (q : Vj ⟶ Vi)
    (u : pullback pi f ⟶ pullback pi g) (hu : u ≫ pullback.fst pi g = pullback.fst pi f)
    (G : (Over.pullback q).obj (Over.mk f) ⟶ (Over.pullback q).obj (Over.mk g))
    (α : (Over.pullback pj).obj ((Over.pullback q).obj (Over.mk f)) ≅
      (Over.pullback pi).obj (Over.mk f))
    (β : (Over.pullback pj).obj ((Over.pullback q).obj (Over.mk g)) ≅
      (Over.pullback pi).obj (Over.mk g))
    (hβ : β.hom.left ≫ pullback.fst g pi =
      pullback.fst (pullback.snd g q) pj ≫ pullback.fst g q)
    (hcomm : α.hom ≫ overPullbackHom f g pi u hu = (Over.pullback pj).map G ≫ β.hom) :
    (pullbackSymmetry pi f).hom ≫ α.inv.left ≫
        pullback.fst (pullback.snd f q) pj ≫ G.left ≫ pullback.fst g q =
      u ≫ pullback.snd pi g := by
  have h1 : pullback.fst (pullback.snd f q) pj ≫ G.left ≫ pullback.fst g q =
      ((Over.pullback pj).map G).left ≫ β.hom.left ≫ pullback.fst g pi := by
    rw [hβ, ← Category.assoc, ← Category.assoc]
    congr 1
    simp [pullback.lift_fst]
  have hcommleft : ((Over.pullback pj).map G).left ≫ β.hom.left ≫ pullback.fst g pi =
      α.hom.left ≫ (overPullbackHom f g pi u hu).left ≫ pullback.fst g pi := by
    rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, hcomm]
  rw [h1, hcommleft, ← Category.assoc α.inv.left, inv_left_comp_hom_left, Category.id_comp,
    overPullbackHom_left]
  simp only [Category.assoc, pullbackSymmetry_hom_comp_fst]
  rw [← Category.assoc, pullbackSymmetry_hom_comp_hom, Category.id_comp]

end Transport

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent of equalities of morphisms of finitely presented, flat and proper families along an
affine cofiltered limit, at a small index category.** This is the first of the two geometric
inputs of **Stacks 0D1I** discharged here, and it follows from the faithfulness half of the
size-free **Stacks 07SK**,
`AlgebraicGeometry.Space.eventually_eq_of_baseChange_eq_affineBase`: a vertical morphism of
families over a stage is a morphism of the slice category over the Yoneda image of the stage, and
`AlgebraicGeometry.overPullback_map_homMk_eq_iff` says that two such have equal base changes in the
sense of `CategoryTheory.Over.pullback` exactly when their composites with the second projection
of the chosen fibre product agree, which is the form the condition is stated in.

Flatness and properness of the two families are not used; only algebraicity and finite
presentation enter.

The condition is established at `v = w = u`, i.e. at a small index category: that is this
library's canonical form of a Stacks 07XL condition, as for the Stacks 0D43
`AlgebraicGeometry.isLimitPreservingPolarizedUnconditional`. See the "Index universes" section of
the module docstring. -/
theorem properFlatMorphismEqualityDescendsAlongAffineLimit :
    ProperFlatMorphismEqualityDescendsAlongAffineLimit.{u, u, u} B S hS := by
  intro I _ _ D c hc i X Y hX hY f g hfp _ _ hgp _ _ a a' ha ha' hvertex
  obtain ⟨k, s, hks⟩ := Space.eventually_eq_of_baseChange_eq_affineBase B S hS
    B.contains_terminal D c hc i (Over.mk f) (Over.mk g) hX hY hfp hgp
    (Over.homMk a ha) (Over.homMk a' ha')
    ((overPullback_map_homMk_eq_iff f g _ ha ha').mpr hvertex)
  exact ⟨k, s, (overPullback_map_homMk_eq_iff f g _ ha ha').mp hks⟩

/-- **Descent of morphisms of finitely presented, flat and proper families along an affine
cofiltered limit, at a small index category.** This is the second of the two geometric inputs of
**Stacks 0D1I** discharged here, and it follows from the fullness half of the size-free
**Stacks 07SK**, `AlgebraicGeometry.Space.exists_morphism_after_baseChange_affineBase`.

The morphism `u` over the vertex is fed to 07SK through
`AlgebraicGeometry.overPullbackHom`, and the morphism 07SK returns at a later stage is read back
through `AlgebraicGeometry.chosenHom`. The compatibility with
`AlgebraicGeometry.coneBaseRestrict` that the condition demands is checked on the two projections
of the chosen fibre product: the first projection is automatic from the two conditions that `u`
and the returned morphism lie over the base, and the second is
`AlgebraicGeometry.comp_overPullbackHom_eq` after the restriction map has been identified, by
`AlgebraicGeometry.symmetry_restrict_eq`, with the first projection of the iterated fibre product
read through the comparison isomorphism `α`.

Flatness and properness of the two families are not used; only algebraicity and finite
presentation enter.

The condition is established at `v = w = u`, i.e. at a small index category: that is this
library's canonical form of a Stacks 07XL condition, as for the Stacks 0D43
`AlgebraicGeometry.isLimitPreservingPolarizedUnconditional`. See the "Index universes" section of
the module docstring. -/
theorem properFlatMorphismDescendsAlongAffineLimit :
    ProperFlatMorphismDescendsAlongAffineLimit.{u, u, u} B S hS := by
  intro I _ _ D c hc i X Y hX hY f g hfp _ _ hgp _ _ u hufst
  obtain ⟨j, e, G, α, β, hα, hβ, hcomm⟩ := Space.exists_morphism_after_baseChange_affineBase
    B S hS B.contains_terminal D c hc i (Over.mk f) (Over.mk g) hX hY hfp hgp
    (overPullbackHom f g
      (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) u hufst)
  simp only [Over.pullback_obj_hom, Over.mk_hom] at hα hβ
  have hres := symmetry_restrict_eq f
    (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)))
    (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app j)))
    (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map e)))
    (coneBaseRestrict c e f) (coneBaseRestrict_fst c e f) (coneBaseRestrict_snd c e f) α hα
  refine ⟨j, e,
    chosenHom f g (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map e))) G,
    chosenHom_comp_fst f g _ G, ?_⟩
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, chosenHom_comp_fst, coneBaseRestrict_fst, Category.assoc,
      coneBaseRestrict_fst, ← Category.assoc, hufst]
  · rw [Category.assoc, Category.assoc, coneBaseRestrict_snd, chosenHom_comp_snd,
      ← Category.assoc, hres]
    simp only [Category.assoc]
    exact comp_overPullbackHom_eq f g _ _ _ u hufst G α β hβ hcomm

/-- **Descent of isomorphisms of finitely presented, flat and proper families along an affine
cofiltered limit, at a small index category.** This is the third geometric input of
**Stacks 0D1I**, and it is now unconditional: it is
`AlgebraicGeometry.properFlatFamilyIsomorphismDescendsAlongAffineLimit_of_fullness` fed with the
two conditions discharged above. -/
theorem properFlatFamilyIsomorphismDescendsAlongAffineLimit :
    ProperFlatFamilyIsomorphismDescendsAlongAffineLimit.{u, u, u} B S hS :=
  properFlatFamilyIsomorphismDescendsAlongAffineLimit_of_fullness B S hS
    (properFlatMorphismDescendsAlongAffineLimit B S hS)
    (properFlatMorphismEqualityDescendsAlongAffineLimit B S hS)

end AlgebraicGeometry

end
