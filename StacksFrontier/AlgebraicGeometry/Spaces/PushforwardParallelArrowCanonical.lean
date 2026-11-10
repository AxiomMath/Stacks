module

public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardSectionsEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardPresentationArrows

/-!
# The canonical and the geometric parallel arrow of Stacks 03M8 agree

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `τ : U ⟶ X` and `ρ : R ⟶ X` be étale, let `θ : R ⟶ U` be étale with `θ ≫ τ = ρ`,
and put `a = τ ≫ f` and `b = ρ ≫ f`.  Stacks 03M8 asserts the exactness of

`0 → f_*G → a_*(G|_U) → b_*(G|_R)`,

and this repository carries two readings of the second arrow:

* the **canonical** one, `AlgebraicGeometry.Space.chartDirectImageParallelArrow`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardPresentationArrows.lean`): the direct
  image along `f` of the unit of
  `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at `θ`, conjugated by the
  composition comparisons `AlgebraicGeometry.Space.smallEtaleDirectImageCompIso` of Stacks 03G2,
  part (3); and
* the **geometric** one, `AlgebraicGeometry.Space.directImageEtaleRestrictionParallel`
  (`StacksFrontier/AlgebraicGeometry/Spaces/PushforwardSectionsEtaleRestriction.lean`): restriction
  of the sections of the extension of `G` to the spaces-étale site along the comparison
  `AlgebraicGeometry.Space.postcompBaseChangeCompOverMapNat` of the two postcomposed base
  changes, which
  `AlgebraicGeometry.Space.directImageEtaleRestrictionParallel_sectionsIso` identifies with the
  arrow `prod.map θ (𝟙)` of the fork of
  `AlgebraicGeometry.Space.isLimitForkDirectImage`.

Both arrows live in the single hom-type

`a_*(G|_U) ⟶ b_*(G|_R)`

of sheaves of sets on the small étale site of `Y` at the universe of the structure rings, so the
assertion that they agree is a plain equation; it is **not** definitional, and `rfl` fails on it.
This file proves it.

## Main results

* `AlgebraicGeometry.Space.directImageEtaleRestrictionParallel_eq_chartDirectImageParallelArrow`:
  the geometric parallel arrow of Stacks 03M8 **is** the canonical one.
* `AlgebraicGeometry.Space.chartDirectImageParallelArrow_comparison`: the canonical arrow is the
  image under the comparison functor of Stacks 03G1 for `Y` of an explicit arrow
  `AlgebraicGeometry.Space.chartParallelSpacesArrow` of the spaces-étale site.  This is the
  descent of the small étale spelling to the spaces-étale one, and it is where the unit of
  `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` and the two composition
  comparisons are unwound.
* `AlgebraicGeometry.Space.coreParallelArrow_eq`: after the extension comparisons are moved to
  the two ends, what is left of the canonical arrow is restriction of sections along
  `AlgebraicGeometry.Space.postcompBaseChangeCompOverMapNat` — the geometric arrow.
* `AlgebraicGeometry.Space.postcompBaseChange_counit_comp`: the geometric core.  The counit of
  the adjunction of sites at the base change along `τ`, preceded by the comparison
  `AlgebraicGeometry.Space.spacesBaseChange_comp` of the base change along `θ ≫ τ` with the
  base change along `θ` of the base change along `τ`, is
  `AlgebraicGeometry.Space.postcompBaseChangeOverMap`: both sides are morphisms into a cartesian
  square over `τ`, and their two projections agree by
  `AlgebraicGeometry.Space.spacesBaseChange_comp_projection` and by `CategoryTheory.Over.w`.

## Implementation notes

The proof is in two halves, joined at
`AlgebraicGeometry.Space.chartParallelSpacesArrow`.

**The descent.**  `AlgebraicGeometry.Space.smallEtaleDirectImage` is the spaces-étale direct
image conjugated by the comparison equivalences of Stacks 03G1, so every factor of the canonical
arrow is the image under the comparison functor of a spaces-étale arrow — for the two
composition comparisons this is
`AlgebraicGeometry.Space.smallEtaleDirectImageCompIso_hom_app`, and for the unit it is
`AlgebraicGeometry.Space.comparison_map_factorizationUnitArrow`, which reads the unit at the
*extension* of `G|_U` through
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comparison`.  The inverse of the
comparison equivalence is then eliminated once and for all: a morphism of the form
`𝒞⁻¹(m)` is pinned by the arrow it is the transpose of, which is the content of the three
private lemmas on an equivalence of categories at the head of the file.  The unit intervenes
through `AlgebraicGeometry.Space.extensionRestriction_factorization`, which identifies the
spaces-étale arrow `(G^{ext})|_R` of the factorization with
`AlgebraicGeometry.Space.spacesEtaleExtensionRestrictionIso` at `τ` followed by its inverse at
`ρ`; the proof is
`AlgebraicGeometry.Space.smallEtaleSetRestrictionConjMate_counit` twice.

**The naturality.**  With the canonical arrow written on the spaces-étale side, the two
extension comparisons are moved to the two ends by the naturality of the unit of
`AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction` and of the three instances of
`AlgebraicGeometry.Space.spacesBaseChange_pushforward_compTypeU`, and what is left is compared
with the geometric arrow on sections, where it is the geometric core above.

Two spellings of the same object are unavoidable here: restriction along the comparison functor
of `U` of a sheaf restricted along spaces-étale postcomposition with `h` is restriction along
small étale postcomposition with `h` of the restriction along the comparison functor of `V`
(`AlgebraicGeometry.Space.spacesEtaleSetRestriction_comp_comparisonRestriction`, an `Eq.refl`),
and the two sides of that identity meet in every statement below that mentions both the unit and
the extension.  The identity is *semireducible*, so a `rewrite` whose motive crosses it produces
a term that is not type-correct at `implicit` transparency and the tactic fails; every such step
in this file is therefore taken in term mode with `congrArg`, whose function is given
explicitly, or — in `AlgebraicGeometry.Space.coreParallelArrow_eq`, where the goal has to be
read as a composite of four restriction maps — by one `show` in the reduced spelling.  The same
`show` is what keeps that proof inside the elaboration budget: the same chain driven by
unification against the unreduced goal reports `(deterministic) timeout at 'whnf'`.

No compiler limit is raised and no linter is disabled anywhere in this file, and the
registration of the tag on `AlgebraicGeometry.Space.isLimitForkDirectImage` is untouched:
this file proves one clause of Stacks 03M8 and claims none of it.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The small étale constructions as images of spaces-étale ones -/

section Spelling

variable {U V W : AlgebraicSpaces B S hS}

/-- The small étale direct image on morphisms is the spaces-étale direct image conjugated by
the comparison equivalences of Stacks 03G1: that is what
`AlgebraicGeometry.Space.smallEtaleDirectImage` is, so this holds by `Eq.refl`.  It is stated
because every step of the descent below rewrites with it. -/
theorem smallEtaleDirectImage_map_eq (h : U ⟶ V)
    {P Q : Sheaf (SmallEtale.topology B S hS U.1) (Type u)} (z : P ⟶ Q) :
    (smallEtaleDirectImage B S hS h).map z =
      (smallEtaleComparisonRestriction B S hS V).map
        ((spacesSetBaseChange B S hS h).map
          ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.map z)) := rfl

/-- **The unit of étale restriction of sheaves of sets, in its four factors.**  The adjunction
is the spaces-étale one conjugated by the comparison equivalences of Stacks 03G1 by two
instances of `CategoryTheory.Adjunction.comp`, so its unit is the inverse counit of the
comparison equivalence at `V`, the spaces-étale unit, the direct image of the comparison unit at
`U`, and the direct image of the restriction of the counit at `V` — in that order, and by
`Eq.refl`. -/
theorem smallEtaleSetRestrictionAdjunction_unit_app_eq (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) (P : Sheaf (SmallEtale.topology B S hS V.1) (Type u)) :
    (smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app P =
      (smallEtaleComparisonRestriction B S hS V).asEquivalence.counitIso.inv.app P ≫
        (smallEtaleComparisonRestriction B S hS V).asEquivalence.functor.map
          ((spacesEtalePostcompSheafAdjunction B S hS (Type u) h hh).unit.app
            ((smallEtaleComparisonRestriction B S hS V).asEquivalence.inverse.obj P)) ≫
        (smallEtaleComparisonRestriction B S hS V).asEquivalence.functor.map
          ((spacesSetBaseChange B S hS h).map
            ((smallEtaleComparisonRestriction B S hS U).asEquivalence.unitIso.hom.app
              ((spacesEtaleSetRestriction B S hS h hh).obj
                ((smallEtaleComparisonRestriction B S hS V).asEquivalence.inverse.obj P)))) ≫
        (smallEtaleComparisonRestriction B S hS V).asEquivalence.functor.map
          ((spacesSetBaseChange B S hS h).map
            ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.map
              ((smallEtaleSetRestriction B S hS h hh).map
                ((smallEtaleComparisonRestriction B S hS V).asEquivalence.counitIso.hom.app
                  P)))) :=
  rfl

/-- **The composition comparison of small étale direct images is the image of the cartesian
composition.**  `AlgebraicGeometry.Space.smallEtaleDirectImageCompIso` is
`CategoryTheory.MorphismOfTopoi.transport_comp_pushforward` followed by the whiskered
`AlgebraicGeometry.Space.spacesBaseChange_pushforward_compTypeU`, and the first of those is the
inverse unit of the comparison equivalence at the intermediate space; so the component at a
sheaf is the comparison functor applied to one spaces-étale arrow. -/
theorem smallEtaleDirectImageCompIso_hom_app (h : U ⟶ V) (g : V ⟶ W)
    (P : Sheaf (SmallEtale.topology B S hS U.1) (Type u)) :
    (smallEtaleDirectImageCompIso B S hS h g).hom.app P =
      (smallEtaleComparisonRestriction B S hS W).map
        ((spacesSetBaseChange B S hS g).map
            ((smallEtaleComparisonRestriction B S hS V).asEquivalence.unitIso.inv.app
              ((spacesSetBaseChange B S hS h).obj
                ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj P))) ≫
          (spacesBaseChange_pushforward_compTypeU B S hS h g).hom.app
            ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj P)) :=
  ((smallEtaleComparisonRestriction B S hS W).map_comp _ _).symm

/-- The cartesian composition of spaces-étale direct images is restriction of sections along
`AlgebraicGeometry.Space.spacesBaseChange_comp`: `Mathlib`'s
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` is the identity followed by the action
of the comparison of the functors of sites, so this holds by `Eq.refl`. -/
theorem spacesBaseChange_pushforward_compTypeU_hom_app_apply (h : U ⟶ V) (g : V ⟶ W)
    (M : Sheaf (SpacesEtale.topology B S hS U) (Type u)) (T : SpacesEtale B S hS W)
    (x : (((spacesBaseChange B S hS g).functor ⋙
        (spacesBaseChange B S hS h).functor).op ⋙ M.obj).obj (op T)) :
    ((spacesBaseChange_pushforward_compTypeU B S hS h g).hom.app M).hom.app (op T) x =
      M.obj.map ((spacesBaseChange_comp B S hS h g).inv.app T).op x := rfl

end Spelling

/-! ### Bridges for the comparison equivalence -/

section Bridge

variable {A : AlgebraicSpaces B S hS}

/-- `CategoryTheory.Equivalence.inv_fun_map` for the comparison equivalence of Stacks 03G1,
spelled with `AlgebraicGeometry.Space.smallEtaleComparisonRestriction` so that it can be
rewritten with. -/
private theorem comp_inv_map_map
    {M N : Sheaf (SpacesEtale.topology B S hS A) (Type u)} (m : M ⟶ N) :
    (smallEtaleComparisonRestriction B S hS A).asEquivalence.inverse.map
        ((smallEtaleComparisonRestriction B S hS A).asEquivalence.functor.map m) =
      (smallEtaleComparisonRestriction B S hS A).asEquivalence.unitIso.inv.app M ≫ m ≫
        (smallEtaleComparisonRestriction B S hS A).asEquivalence.unitIso.hom.app N :=
  Equivalence.inv_fun_map _ _ _ m

/-- `CategoryTheory.Equivalence.unit_app_inverse` for the comparison equivalence of
Stacks 03G1. -/
private theorem comp_inv_map_counitInv (P : Sheaf (SmallEtale.topology B S hS A.1) (Type u)) :
    (smallEtaleComparisonRestriction B S hS A).asEquivalence.inverse.map
        ((smallEtaleComparisonRestriction B S hS A).asEquivalence.counitIso.inv.app P) =
      (smallEtaleComparisonRestriction B S hS A).asEquivalence.unitIso.hom.app
        ((smallEtaleComparisonRestriction B S hS A).asEquivalence.inverse.obj P) :=
  (Equivalence.unit_app_inverse _ P).symm

end Bridge

/-! ### Generic lemmas on an equivalence of categories -/

section Generic

variable {C D : Type*} [Category C] [Category D] (e : C ≌ D)

/-- A morphism `m : P ⟶ e.functor.obj A` is determined by its transpose: if `v` satisfies
`e.functor.map v = e.counit.app P ≫ m`, then `e.inverse.map m` is `v` followed by the unit.

This is how the inverse of the comparison equivalence of Stacks 03G1 is eliminated below: the
transpose is an arrow of the spaces-étale site, which is what the geometric half of the proof
works with. -/
private theorem inverse_map_eq_of {A : C} {P : D} (m : P ⟶ e.functor.obj A)
    (v : e.inverse.obj P ⟶ A) (hv : e.functor.map v = e.counitIso.hom.app P ≫ m) :
    e.inverse.map m = v ≫ e.unitIso.hom.app A := by
  calc e.inverse.map m
      = (e.unitIso.hom.app (e.inverse.obj P) ≫
          e.inverse.map (e.counitIso.hom.app P)) ≫ e.inverse.map m := by
        rw [Equivalence.unit_inverse_comp]
        exact (Category.id_comp _).symm
    _ = e.unitIso.hom.app (e.inverse.obj P) ≫ e.inverse.map (e.functor.map v) := by
        rw [Category.assoc, ← Functor.map_comp, ← hv]
    _ = v ≫ e.unitIso.hom.app A := by
        rw [Equivalence.inv_fun_map]
        simp

/-- The same determination for a morphism *out of* the image of `e.functor`: if
`e.functor.map a ≫ e.counit.app P` is `m`, then the unit followed by `e.inverse.map m` is `a`. -/
private theorem unit_comp_inverse_map_eq_of {A : C} {P : D} (m : e.functor.obj A ⟶ P)
    (a : A ⟶ e.inverse.obj P) (ha : e.functor.map a ≫ e.counitIso.hom.app P = m) :
    e.unitIso.hom.app A ≫ e.inverse.map m = a := by
  subst ha
  rw [Functor.map_comp, Equivalence.inv_fun_map]
  simp

/-- Conjugating the image of `w` under `e.functor` back along `e.inverse` by the unit returns
`w`.  This is the step that makes the two unit isomorphisms inserted by
`CategoryTheory.MorphismOfTopoi.transport_comp_pushforward` cancel. -/
private theorem conj_functor_map {A A' : C} (w : A ⟶ A') :
    e.unitIso.hom.app A ≫ e.inverse.map (e.functor.map w) ≫ e.unitIso.inv.app A' = w := by
  rw [Equivalence.inv_fun_map]
  simp

/-- An isomorphism whose forward direction is `F.map j.hom` has `F.map j.inv` for its
inverse. -/
private theorem iso_inv_eq_map_inv (F : C ⥤ D) {A A' : C} (j : A ≅ A')
    (i : F.obj A ≅ F.obj A') (h : i.hom = F.map j.hom) : i.inv = F.map j.inv :=
  congrArg Iso.inv (Iso.ext h : i = F.mapIso j)

end Generic

/-! ### The extension of an étale restriction and the mate -/

section Mate

variable {U V : AlgebraicSpaces B S hS} (h : U ⟶ V) (hh : IsEtale B S hS h.hom)

/-- The component of `AlgebraicGeometry.Space.spacesEtaleExtensionRestrictionIso` is the mate
`AlgebraicGeometry.Space.smallEtaleSetRestrictionConjMate` of the comparison of the two
restriction functors.  It holds by `Eq.refl`, and it is what makes
`AlgebraicGeometry.Space.smallEtaleSetRestrictionConjMate_counit` available for the extension
isomorphism. -/
theorem spacesEtaleExtensionRestrictionIso_app_hom
    (P : Sheaf (SmallEtale.topology B S hS V.1) (Type u)) :
    ((spacesEtaleExtensionRestrictionIso B S hS h hh).app P).hom =
      smallEtaleSetRestrictionConjMate B S hS h hh P := rfl

/-- **The extension comparison is compatible with the counits of Stacks 03G1.**  Reading the
inverse of `AlgebraicGeometry.Space.spacesEtaleExtensionRestrictionIso` on the small étale site
and following it with the counit at `P|_U` is the restriction to `U` of the counit at `P`.

It is `AlgebraicGeometry.Space.smallEtaleSetRestrictionConjMate_counit` with the isomorphism
moved across. -/
theorem comparison_map_extensionRestrictionIso_inv_comp_counit
    (P : Sheaf (SmallEtale.topology B S hS V.1) (Type u)) :
    (smallEtaleComparisonRestriction B S hS U).map
          ((spacesEtaleExtensionRestrictionIso B S hS h hh).app P).inv ≫
        (smallEtaleComparisonRestriction B S hS U).asEquivalence.counitIso.hom.app
          ((smallEtaleSetRestriction B S hS h hh).obj P) =
      (smallEtaleSetRestriction B S hS h hh).map
        ((smallEtaleComparisonRestriction B S hS V).asEquivalence.counitIso.hom.app P) := by
  have hc : (smallEtaleComparisonRestriction B S hS U).map
          ((spacesEtaleExtensionRestrictionIso B S hS h hh).app P).hom ≫
        (smallEtaleSetRestriction B S hS h hh).map
          ((smallEtaleComparisonRestriction B S hS V).asEquivalence.counitIso.hom.app P) =
      (smallEtaleComparisonRestriction B S hS U).asEquivalence.counitIso.hom.app
        ((smallEtaleSetRestriction B S hS h hh).obj P) :=
    smallEtaleSetRestrictionConjMate_counit B S hS h hh P
  rw [← hc]
  erw [← Functor.map_comp_assoc]
  rw [Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  exact Category.id_comp _

end Mate

/-! ### The arrow `(G^ext)|_R` of the factorization -/

section Factorization

variable {X U R Y : AlgebraicSpaces B S hS} (τ : U ⟶ X) (hτ : IsEtale B S hS τ.hom)
    (θ : R ⟶ U) (hθ' : IsEtale B S hS θ.hom) (hc : IsEtale B S hS (θ ≫ τ).hom)
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u))

/-- **The arrow `(G^{ext})|_R` attached to a factorization.**  For étale `τ : U ⟶ X` and
`θ : R ⟶ U`, the spaces-étale arrow that the unit of étale restriction at `θ` contributes to the
parallel arrow of Stacks 03M8 — the comparison unit at `R` followed by the restriction along `θ`
of the counit at `G|_U` — is the restriction along `θ` of
`AlgebraicGeometry.Space.spacesEtaleExtensionRestrictionIso` at `τ` followed by the inverse of
that isomorphism at `θ ≫ τ`.

Both sides are morphisms into the extension of `G|_R`, so by
`AlgebraicGeometry.Space.unit_comp_inverse_map_eq_of` it is enough to compare their transposes,
and those agree by `AlgebraicGeometry.Space.smallEtaleSetRestrictionConjMate_counit` at `τ` and
at `θ ≫ τ`. -/
theorem extensionRestriction_factorization :
    (smallEtaleComparisonRestriction B S hS R).asEquivalence.unitIso.hom.app
          ((spacesEtaleSetRestriction B S hS θ hθ').obj
            ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
              ((smallEtaleSetRestriction B S hS τ hτ).obj G))) ≫
        (smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.map
          ((smallEtaleSetRestriction B S hS θ hθ').map
            ((smallEtaleComparisonRestriction B S hS U).asEquivalence.counitIso.hom.app
              ((smallEtaleSetRestriction B S hS τ hτ).obj G))) =
      (spacesEtaleSetRestriction B S hS θ hθ').map
          ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom ≫
        ((spacesEtaleExtensionRestrictionIso B S hS (θ ≫ τ) hc).app G).inv := by
  refine unit_comp_inverse_map_eq_of _ _ _ ?_
  have hτc := smallEtaleSetRestrictionConjMate_counit B S hS τ hτ G
  have hρm := comparison_map_extensionRestrictionIso_inv_comp_counit B S hS (θ ≫ τ) hc G
  erw [Functor.map_comp, Category.assoc, hρm]
  exact ((smallEtaleSetRestriction B S hS θ hθ').map_comp _ _).symm.trans
    (congrArg (smallEtaleSetRestriction B S hS θ hθ').map hτc)

end Factorization

/-! ### The unit at the extension -/

section UnitExtension

variable {U V : AlgebraicSpaces B S hS} (h : U ⟶ V) (hh : IsEtale B S hS h.hom)

/-- The geometric comparison of direct images of Stacks 03G2, part (3) is the comparison functor
applied to the inverse unit of the comparison equivalence of Stacks 03G1: the comparison is a
whiskered unit followed by a left unitor, so this is `CategoryTheory.Category.comp_id`. -/
theorem smallToposMorphismTypeU_comparison_hom_app
    (H : Sheaf (SpacesEtale.topology B S hS U) (Type u)) :
    (smallToposMorphismTypeU_comparison B S hS h).hom.app H =
      (smallEtaleComparisonRestriction B S hS V).map
        ((spacesSetBaseChange B S hS h).map
          ((smallEtaleComparisonRestriction B S hS U).asEquivalence.unitIso.inv.app H)) :=
  Category.comp_id _

/-- The inverse of the geometric comparison of direct images, read the same way. -/
theorem smallToposMorphismTypeU_comparison_inv_app
    (H : Sheaf (SpacesEtale.topology B S hS U) (Type u)) :
    (smallToposMorphismTypeU_comparison B S hS h).inv.app H =
      (smallEtaleComparisonRestriction B S hS V).map
        ((spacesSetBaseChange B S hS h).map
          ((smallEtaleComparisonRestriction B S hS U).asEquivalence.unitIso.hom.app H)) :=
  iso_inv_eq_map_inv (smallEtaleComparisonRestriction B S hS V)
    ((spacesSetBaseChange B S hS h).mapIso
      (((smallEtaleComparisonRestriction B S hS U).asEquivalence.unitIso.app H).symm))
    ((smallToposMorphismTypeU_comparison B S hS h).app H)
    (smallToposMorphismTypeU_comparison_hom_app B S hS h H)

/-- **The unit of étale restriction at a sheaf read from the spaces-étale site.**  For a sheaf
`H` on the spaces-étale site of `V`, the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at the sheaf `H` becomes on the
small étale site is the comparison functor applied to the spaces-étale unit followed by the
comparison unit at `U`.

It is `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comparison` with the
geometric comparison moved across and
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comparison_inv_app` substituted for it. -/
theorem smallEtaleSetRestrictionAdjunction_unit_app_comparison
    (H : Sheaf (SpacesEtale.topology B S hS V) (Type u)) :
    (smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app
        ((smallEtaleComparisonRestriction B S hS V).obj H) =
      (smallEtaleComparisonRestriction B S hS V).map
          ((spacesEtalePostcompSheafAdjunction B S hS (Type u) h hh).unit.app H) ≫
        (smallEtaleComparisonRestriction B S hS V).map
          ((spacesSetBaseChange B S hS h).map
            ((smallEtaleComparisonRestriction B S hS U).asEquivalence.unitIso.hom.app
              ((spacesEtaleSetRestriction B S hS h hh).obj H))) := by
  refine Eq.trans ((Iso.eq_comp_inv
    ((smallToposMorphismTypeU_comparison B S hS h).app
      ((spacesEtaleSetRestriction B S hS h hh).obj H))).2
    (smallEtaleSetRestrictionAdjunction_unit_comparison B S hS h hh H)) ?_
  exact congrArg (fun z ↦ (smallEtaleComparisonRestriction B S hS V).map
      ((spacesEtalePostcompSheafAdjunction B S hS (Type u) h hh).unit.app H) ≫ z)
    (smallToposMorphismTypeU_comparison_inv_app B S hS h
      ((spacesEtaleSetRestriction B S hS h hh).obj H))

end UnitExtension

/-! ### The unit of the factorization, descended -/

section Descend

variable {X U R Y : AlgebraicSpaces B S hS} (τ : U ⟶ X) (hτ : IsEtale B S hS τ.hom)
    (θ : R ⟶ U) (hθ' : IsEtale B S hS θ.hom) (hc : IsEtale B S hS (θ ≫ τ).hom)
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u))

/-- **The spaces-étale arrow underlying the unit of the factorization.**  For étale `τ : U ⟶ X`
and `θ : R ⟶ U` and a sheaf of sets `G` on the small étale site of `X`, it is the spaces-étale
unit at the extension of `G|_U`, followed by the base change along `θ` of
`AlgebraicGeometry.Space.extensionRestriction_factorization`.

It is the arrow whose image under the comparison functor of Stacks 03G1 is the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at `G|_U`, read after the counit;
that is `AlgebraicGeometry.Space.comparison_map_factorizationUnitArrow`. -/
noncomputable def factorizationUnitArrow :
    (smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
        ((smallEtaleSetRestriction B S hS τ hτ).obj G) ⟶
      (spacesSetBaseChange B S hS θ).obj
        ((smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.obj
          ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G)) :=
  (spacesEtalePostcompSheafAdjunction B S hS (Type u) θ hθ').unit.app
      ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
        ((smallEtaleSetRestriction B S hS τ hτ).obj G)) ≫
    (spacesSetBaseChange B S hS θ).map
      ((spacesEtaleSetRestriction B S hS θ hθ').map
          ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom ≫
        ((spacesEtaleExtensionRestrictionIso B S hS (θ ≫ τ) hc).app G).inv)

/-- **The unit of étale restriction at `G|_U`, descended to the spaces-étale site.**  The
comparison functor of Stacks 03G1 applied to
`AlgebraicGeometry.Space.factorizationUnitArrow` is the counit at `G|_U` followed by the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at `θ`.

The unit at `G|_U` is moved to the unit at the sheaf the extension of `G|_U` becomes, by its own
naturality; there it is
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_app_comparison`, and the
remaining factor is `AlgebraicGeometry.Space.extensionRestriction_factorization`. -/
theorem comparison_map_factorizationUnitArrow :
    (smallEtaleComparisonRestriction B S hS U).map
        (factorizationUnitArrow B S hS τ hτ θ hθ' hc G) =
      (smallEtaleComparisonRestriction B S hS U).asEquivalence.counitIso.hom.app
          ((smallEtaleSetRestriction B S hS τ hτ).obj G) ≫
        (smallEtaleSetRestrictionAdjunction B S hS θ hθ').unit.app
          ((smallEtaleSetRestriction B S hS τ hτ).obj G) := by
  have hnat := (smallEtaleSetRestrictionAdjunction B S hS θ hθ').unit.naturality
    ((smallEtaleComparisonRestriction B S hS U).asEquivalence.counitIso.hom.app
      ((smallEtaleSetRestriction B S hS τ hτ).obj G))
  have hinner : (spacesEtalePostcompSheafAdjunction B S hS (Type u) θ hθ').unit.app
          ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
            ((smallEtaleSetRestriction B S hS τ hτ).obj G)) ≫
        (spacesSetBaseChange B S hS θ).map
          ((smallEtaleComparisonRestriction B S hS R).asEquivalence.unitIso.hom.app
              ((spacesEtaleSetRestriction B S hS θ hθ').obj
                ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
                  ((smallEtaleSetRestriction B S hS τ hτ).obj G))) ≫
            (smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.map
              ((smallEtaleSetRestriction B S hS θ hθ').map
                ((smallEtaleComparisonRestriction B S hS U).asEquivalence.counitIso.hom.app
                  ((smallEtaleSetRestriction B S hS τ hτ).obj G)))) =
      factorizationUnitArrow B S hS τ hτ θ hθ' hc G :=
    congrArg (fun z ↦ (spacesEtalePostcompSheafAdjunction B S hS (Type u) θ hθ').unit.app
          ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
            ((smallEtaleSetRestriction B S hS τ hτ).obj G)) ≫
        (spacesSetBaseChange B S hS θ).map z)
      (extensionRestriction_factorization B S hS τ hτ θ hθ' hc G)
  refine Eq.trans ?_ hnat.symm
  refine Eq.trans (congrArg (smallEtaleComparisonRestriction B S hS U).map hinner.symm) ?_
  refine Eq.trans ((smallEtaleComparisonRestriction B S hS U).map_comp _ _) ?_
  refine Eq.trans (congrArg (fun z ↦ (smallEtaleComparisonRestriction B S hS U).map
      ((spacesEtalePostcompSheafAdjunction B S hS (Type u) θ hθ').unit.app
        ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
          ((smallEtaleSetRestriction B S hS τ hτ).obj G))) ≫
      (smallEtaleComparisonRestriction B S hS U).map z)
    ((spacesSetBaseChange B S hS θ).map_comp _ _)) ?_
  refine Eq.trans (congrArg (fun z ↦ (smallEtaleComparisonRestriction B S hS U).map
      ((spacesEtalePostcompSheafAdjunction B S hS (Type u) θ hθ').unit.app
        ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
          ((smallEtaleSetRestriction B S hS τ hτ).obj G))) ≫ z)
    ((smallEtaleComparisonRestriction B S hS U).map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun z ↦ z ≫ (smallEtaleDirectImage B S hS θ).map
      ((smallEtaleSetRestriction B S hS θ hθ').map
        ((smallEtaleComparisonRestriction B S hS U).asEquivalence.counitIso.hom.app
          ((smallEtaleSetRestriction B S hS τ hτ).obj G))))
    (smallEtaleSetRestrictionAdjunction_unit_app_comparison B S hS θ hθ'
      ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
        ((smallEtaleSetRestriction B S hS τ hτ).obj G))).symm

end Descend

/-! ### The arrow of the factorization, descended -/

section Arrow

variable {X U R Y : AlgebraicSpaces B S hS} (τ : U ⟶ X) (hτ : IsEtale B S hS τ.hom)
    (θ : R ⟶ U) (hθ' : IsEtale B S hS θ.hom) (hc : IsEtale B S hS (θ ≫ τ).hom)
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u))

/-- `AlgebraicGeometry.Space.restrictionUnitArrow` at the factorization `θ ≫ τ` of `θ ≫ τ`
itself, with the substitution carried out: the direct image along `τ` of the unit at `θ`,
followed by the composition comparison.  It holds by `Eq.refl`. -/
theorem restrictionUnitArrow_rfl :
    restrictionUnitArrow B S hS hτ hθ' hc rfl G =
      (smallEtaleDirectImage B S hS τ).map
          ((smallEtaleSetRestrictionAdjunction B S hS θ hθ').unit.app
            ((smallEtaleSetRestriction B S hS τ hτ).obj G)) ≫
        (smallEtaleDirectImageCompIso B S hS θ τ).hom.app
          ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G) := rfl

/-- **The spaces-étale arrow underlying `AlgebraicGeometry.Space.restrictionUnitArrow`.**  The
base change along `τ` of `AlgebraicGeometry.Space.factorizationUnitArrow`, followed by the
cartesian composition of the base changes along `θ` and along `τ`. -/
noncomputable def factorizationSpacesArrow :
    (spacesSetBaseChange B S hS τ).obj
        ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
          ((smallEtaleSetRestriction B S hS τ hτ).obj G)) ⟶
      (spacesSetBaseChange B S hS (θ ≫ τ)).obj
        ((smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.obj
          ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G)) :=
  (spacesSetBaseChange B S hS τ).map (factorizationUnitArrow B S hS τ hτ θ hθ' hc G) ≫
    (spacesBaseChange_pushforward_compTypeU B S hS θ τ).hom.app
      ((smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.obj
        ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G))

/-- **`AlgebraicGeometry.Space.restrictionUnitArrow` is the image of
`AlgebraicGeometry.Space.factorizationSpacesArrow`.**  Its two factors are the direct image of
the unit, which `AlgebraicGeometry.Space.comparison_map_factorizationUnitArrow` and
`AlgebraicGeometry.Space.inverse_map_eq_of` descend, and the composition comparison, which
`AlgebraicGeometry.Space.smallEtaleDirectImageCompIso_hom_app` descends; the comparison unit
that the first produces cancels the one the second carries. -/
theorem restrictionUnitArrow_comparison :
    restrictionUnitArrow B S hS hτ hθ' hc rfl G =
      (smallEtaleComparisonRestriction B S hS X).map
        (factorizationSpacesArrow B S hS τ hτ θ hθ' hc G) := by
  have h3 : (smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.map
        ((smallEtaleSetRestrictionAdjunction B S hS θ hθ').unit.app
          ((smallEtaleSetRestriction B S hS τ hτ).obj G)) =
      factorizationUnitArrow B S hS τ hτ θ hθ' hc G ≫
        (smallEtaleComparisonRestriction B S hS U).asEquivalence.unitIso.hom.app
          ((spacesSetBaseChange B S hS θ).obj
            ((smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.obj
              ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G))) :=
    inverse_map_eq_of _ _ _ (comparison_map_factorizationUnitArrow B S hS τ hτ θ hθ' hc G)
  refine Eq.trans (restrictionUnitArrow_rfl B S hS τ hτ θ hθ' hc G) ?_
  refine Eq.trans (congrArg (fun z ↦ (smallEtaleComparisonRestriction B S hS X).map
      ((spacesSetBaseChange B S hS τ).map z) ≫
      (smallEtaleDirectImageCompIso B S hS θ τ).hom.app
        ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G)) h3) ?_
  refine Eq.trans (congrArg (fun z ↦ (smallEtaleComparisonRestriction B S hS X).map
      ((spacesSetBaseChange B S hS τ).map
        (factorizationUnitArrow B S hS τ hτ θ hθ' hc G ≫
          (smallEtaleComparisonRestriction B S hS U).asEquivalence.unitIso.hom.app
            ((spacesSetBaseChange B S hS θ).obj
              ((smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.obj
                ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G))))) ≫ z)
    (smallEtaleDirectImageCompIso_hom_app B S hS θ τ
      ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G))) ?_
  refine Eq.trans ((smallEtaleComparisonRestriction B S hS X).map_comp _ _).symm ?_
  refine congrArg (smallEtaleComparisonRestriction B S hS X).map ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine congrArg (fun z ↦ z ≫ (spacesBaseChange_pushforward_compTypeU B S hS θ τ).hom.app
      ((smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.obj
        ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G))) ?_
  refine Eq.trans ((spacesSetBaseChange B S hS τ).map_comp _ _).symm ?_
  refine congrArg (spacesSetBaseChange B S hS τ).map ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z ↦ factorizationUnitArrow B S hS τ hτ θ hθ' hc G ≫ z)
    (Iso.hom_inv_id_app _ _)) ?_
  exact Category.comp_id _

end Arrow

/-! ### The inverse of the composition comparison -/

section CompInv

variable {U V W : AlgebraicSpaces B S hS}

/-- The inverse of the composition comparison of small étale direct images, read on the
spaces-étale side: `AlgebraicGeometry.Space.smallEtaleDirectImageCompIso_hom_app` through
`AlgebraicGeometry.Space.iso_inv_eq_map_inv`. -/
theorem smallEtaleDirectImageCompIso_inv_app (h : U ⟶ V) (g : V ⟶ W)
    (P : Sheaf (SmallEtale.topology B S hS U.1) (Type u)) :
    (smallEtaleDirectImageCompIso B S hS h g).inv.app P =
      (smallEtaleComparisonRestriction B S hS W).map
        ((spacesBaseChange_pushforward_compTypeU B S hS h g).inv.app
            ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj P) ≫
          (spacesSetBaseChange B S hS g).map
            ((smallEtaleComparisonRestriction B S hS V).asEquivalence.unitIso.hom.app
              ((spacesSetBaseChange B S hS h).obj
                ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj P)))) :=
  iso_inv_eq_map_inv (smallEtaleComparisonRestriction B S hS W)
    ((spacesSetBaseChange B S hS g).mapIso
        (((smallEtaleComparisonRestriction B S hS V).asEquivalence.unitIso.app
          ((spacesSetBaseChange B S hS h).obj
            ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj P))).symm) ≪≫
      (spacesBaseChange_pushforward_compTypeU B S hS h g).app
        ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj P))
    ((smallEtaleDirectImageCompIso B S hS h g).app P)
    (smallEtaleDirectImageCompIso_hom_app B S hS h g P)

end CompInv

/-! ### The canonical parallel arrow, descended -/

section Canonical

variable {X U R Y : AlgebraicSpaces B S hS} (τ : U ⟶ X) (hτ : IsEtale B S hS τ.hom)
    (θ : R ⟶ U) (hθ' : IsEtale B S hS θ.hom) (hc : IsEtale B S hS (θ ≫ τ).hom)
    (f : X ⟶ Y) (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u))

/-- **The spaces-étale arrow underlying
`AlgebraicGeometry.Space.chartDirectImageParallelArrow`.**  The base change along `f` of
`AlgebraicGeometry.Space.factorizationSpacesArrow`, conjugated by the cartesian compositions of
the base changes along `τ` and `f` and along `θ ≫ τ` and `f`. -/
noncomputable def chartParallelSpacesArrow :
    (spacesSetBaseChange B S hS (τ ≫ f)).obj
        ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
          ((smallEtaleSetRestriction B S hS τ hτ).obj G)) ⟶
      (spacesSetBaseChange B S hS ((θ ≫ τ) ≫ f)).obj
        ((smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.obj
          ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G)) :=
  (spacesBaseChange_pushforward_compTypeU B S hS τ f).inv.app
      ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
        ((smallEtaleSetRestriction B S hS τ hτ).obj G)) ≫
    (spacesSetBaseChange B S hS f).map (factorizationSpacesArrow B S hS τ hτ θ hθ' hc G) ≫
    (spacesBaseChange_pushforward_compTypeU B S hS (θ ≫ τ) f).hom.app
      ((smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.obj
        ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G))

/-- `AlgebraicGeometry.Space.chartDirectImageParallelArrow` at the factorization `θ ≫ τ` of
`θ ≫ τ` itself, with the substitution carried out.  It holds by `Eq.refl`. -/
theorem chartDirectImageParallelArrow_rfl :
    chartDirectImageParallelArrow B S hS f hτ hθ' hc rfl G =
      (smallEtaleDirectImageCompIso B S hS τ f).inv.app
          ((smallEtaleSetRestriction B S hS τ hτ).obj G) ≫
        (smallEtaleDirectImage B S hS f).map
          (restrictionUnitArrow B S hS hτ hθ' hc rfl G) ≫
        (smallEtaleDirectImageCompIso B S hS (θ ≫ τ) f).hom.app
          ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G) := rfl

/-- **The canonical parallel arrow of Stacks 03M8 is the image of a spaces-étale arrow.**  The
comparison functor of Stacks 03G1 for `Y` applied to
`AlgebraicGeometry.Space.chartParallelSpacesArrow` is
`AlgebraicGeometry.Space.chartDirectImageParallelArrow`.

This is the descent of the small étale spelling of the arrow to the spaces-étale one.  The two
composition comparisons are descended by
`AlgebraicGeometry.Space.smallEtaleDirectImageCompIso_hom_app` and
`AlgebraicGeometry.Space.smallEtaleDirectImageCompIso_inv_app`, the arrow between them by
`AlgebraicGeometry.Space.restrictionUnitArrow_comparison`, and the four comparison units that
those insert cancel in pairs by `AlgebraicGeometry.Space.conj_functor_map`. -/
theorem chartDirectImageParallelArrow_comparison :
    chartDirectImageParallelArrow B S hS f hτ hθ' hc rfl G =
      (smallEtaleComparisonRestriction B S hS Y).map
        (chartParallelSpacesArrow B S hS τ hτ θ hθ' hc f G) := by
  have hconj : (smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.hom.app
          ((spacesSetBaseChange B S hS τ).obj
            ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
              ((smallEtaleSetRestriction B S hS τ hτ).obj G))) ≫
        (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
          (restrictionUnitArrow B S hS hτ hθ' hc rfl G) ≫
        (smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app
          ((spacesSetBaseChange B S hS (θ ≫ τ)).obj
            ((smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.obj
              ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G))) =
      factorizationSpacesArrow B S hS τ hτ θ hθ' hc G := by
    refine Eq.trans (congrArg (fun z ↦
      (smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.hom.app _ ≫
        (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map z ≫
        (smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app _)
      (restrictionUnitArrow_comparison B S hS τ hτ θ hθ' hc G)) ?_
    exact conj_functor_map _ _
  have hmid : (spacesSetBaseChange B S hS f).map
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.hom.app
            ((spacesSetBaseChange B S hS τ).obj
              ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
                ((smallEtaleSetRestriction B S hS τ hτ).obj G)))) ≫
        (spacesSetBaseChange B S hS f).map
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
            (restrictionUnitArrow B S hS hτ hθ' hc rfl G)) ≫
        (spacesSetBaseChange B S hS f).map
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app
            ((spacesSetBaseChange B S hS (θ ≫ τ)).obj
              ((smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.obj
                ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G)))) =
      (spacesSetBaseChange B S hS f).map
        (factorizationSpacesArrow B S hS τ hτ θ hθ' hc G) := by
    refine Eq.trans (congrArg (fun z ↦ (spacesSetBaseChange B S hS f).map
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.hom.app
          ((spacesSetBaseChange B S hS τ).obj
            ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
              ((smallEtaleSetRestriction B S hS τ hτ).obj G)))) ≫ z)
      ((spacesSetBaseChange B S hS f).map_comp _ _).symm) ?_
    refine Eq.trans ((spacesSetBaseChange B S hS f).map_comp _ _).symm ?_
    exact congrArg (spacesSetBaseChange B S hS f).map hconj
  refine Eq.trans (chartDirectImageParallelArrow_rfl B S hS τ hτ θ hθ' hc f G) ?_
  refine Eq.trans (congrArg (fun z ↦ z ≫
      (smallEtaleDirectImage B S hS f).map (restrictionUnitArrow B S hS hτ hθ' hc rfl G) ≫
      (smallEtaleDirectImageCompIso B S hS (θ ≫ τ) f).hom.app
        ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G))
    (smallEtaleDirectImageCompIso_inv_app B S hS τ f
      ((smallEtaleSetRestriction B S hS τ hτ).obj G))) ?_
  refine Eq.trans (congrArg (fun z ↦
      (smallEtaleComparisonRestriction B S hS Y).map
        ((spacesBaseChange_pushforward_compTypeU B S hS τ f).inv.app
            ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
              ((smallEtaleSetRestriction B S hS τ hτ).obj G)) ≫
          (spacesSetBaseChange B S hS f).map
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.hom.app
              ((spacesSetBaseChange B S hS τ).obj
                ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
                  ((smallEtaleSetRestriction B S hS τ hτ).obj G))))) ≫
      (smallEtaleDirectImage B S hS f).map (restrictionUnitArrow B S hS hτ hθ' hc rfl G) ≫ z)
    (smallEtaleDirectImageCompIso_hom_app B S hS (θ ≫ τ) f
      ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G))) ?_
  refine Eq.trans (congrArg (fun z ↦
      (smallEtaleComparisonRestriction B S hS Y).map
        ((spacesBaseChange_pushforward_compTypeU B S hS τ f).inv.app
            ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
              ((smallEtaleSetRestriction B S hS τ hτ).obj G)) ≫
          (spacesSetBaseChange B S hS f).map
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.hom.app
              ((spacesSetBaseChange B S hS τ).obj
                ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
                  ((smallEtaleSetRestriction B S hS τ hτ).obj G))))) ≫ z)
    (((smallEtaleComparisonRestriction B S hS Y).map_comp _ _).symm)) ?_
  refine Eq.trans ((smallEtaleComparisonRestriction B S hS Y).map_comp _ _).symm ?_
  refine congrArg (smallEtaleComparisonRestriction B S hS Y).map ?_
  rw [chartParallelSpacesArrow]
  simp only [Category.assoc]
  rw [← hmid]
  simp only [Category.assoc]
  rfl

end Canonical

/-! ### The geometric core: the counit against the comparison of base changes -/

section Geometric

variable {X U R : AlgebraicSpaces B S hS} (τ : U ⟶ X) (hτ : IsEtale B S hS τ.hom)
    (θ : R ⟶ U) (hθ' : IsEtale B S hS θ.hom) (hc : IsEtale B S hS (θ ≫ τ).hom)

/-- **The geometric core of Stacks 03M8.**  Let `τ : U ⟶ X` and `θ : R ⟶ U` be étale and let
`W` be an object of the spaces-étale site of `X`.  The comparison of the base change of `W`
along `θ ≫ τ` with the base change along `θ` of its base change along `τ`, followed by the
counit of `AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction` at the base change
along `τ`, is `AlgebraicGeometry.Space.postcompBaseChangeOverMap`: the arrow
`W ×_X R ⟶ W ×_X U` induced by `θ`.

Both sides are morphisms into the postcomposed base change of `W` along `τ`, whose underlying
square is cartesian, so by
`AlgebraicGeometry.Space.isPullbackOverEtale_hom_ext` it is enough to compare their two
projections.  For the projection to `W` this is
`AlgebraicGeometry.Space.spacesBaseChange_comp_projection`, Stacks 03G2, part (2); for the
projection to `U` it is `CategoryTheory.Over.w` twice, the counit and the comparison both being
morphisms over their base. -/
theorem postcompBaseChange_counit_comp (W : SpacesEtale B S hS X) :
    (spacesEtalePostcomp B S hS (θ ≫ τ) hc).map
          ((spacesBaseChange_comp B S hS θ τ).inv.app W) ≫
        (spacesEtalePostcomp B S hS τ hτ).map
          ((spacesEtalePostcompBaseChangeAdjunction B S hS θ hθ').counit.app
            ((spacesBaseChange B S hS τ).functor.obj W)) =
      postcompBaseChangeOverMap B S hS τ hτ hc θ rfl (spacesBaseChange B S hS (θ ≫ τ))
        (spacesBaseChange B S hS τ) W := by
  have hiso : ((spacesBaseChange_comp B S hS θ τ).inv.app W).hom.left ≫
      ((spacesBaseChange_comp B S hS θ τ).hom.app W).hom.left = 𝟙 _ :=
    congrArg (fun k ↦ k.hom.left) ((spacesBaseChange_comp B S hS θ τ).inv_hom_id_app W)
  refine isPullbackOverEtale_hom_ext B S hS τ hτ
    (postcompBaseChangeFst B S hS τ hτ (spacesBaseChange B S hS τ) W)
    (postcompBaseChangeSnd B S hS τ hτ (spacesBaseChange B S hS τ) W)
    (isPullback_postcompBaseChange B S hS τ hτ (spacesBaseChange B S hS τ) W) ?_ ?_
  · refine Eq.trans ?_ (postcompBaseChangeOverMap_fst B S hS τ hτ hc θ rfl
      (spacesBaseChange B S hS (θ ≫ τ)) (spacesBaseChange B S hS τ) W).symm
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
    have hw1 := Over.w ((spacesBaseChange_comp B S hS θ τ).inv.app W).hom
    have hw2 := Over.w ((spacesEtalePostcompBaseChangeAdjunction B S hS θ hθ').counit.app
      ((spacesBaseChange B S hS τ).functor.obj W)).hom
    refine Eq.trans (congrArg (fun k ↦ ((spacesBaseChange_comp B S hS θ τ).inv.app W).hom.left ≫ k)
      hw2) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact congrArg (fun k ↦ k ≫ θ) hw1
  · refine Eq.trans ?_ (postcompBaseChangeOverMap_snd B S hS τ hτ hc θ rfl
      (spacesBaseChange B S hS (θ ≫ τ)) (spacesBaseChange B S hS τ) W).symm
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
    have hp := spacesBaseChange_comp_projection B S hS θ τ W
    refine Eq.trans (congrArg (fun k ↦ ((spacesBaseChange_comp B S hS θ τ).inv.app W).hom.left ≫ k)
      hp.symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k ↦ k ≫
      (spacesBaseChange B S hS (θ ≫ τ)).projection.app W) hiso) ?_
    exact Category.id_comp _

end Geometric

/-! ### The geometric parallel arrow -/

section Assemble

variable {X U R Y : AlgebraicSpaces B S hS} (τ : U ⟶ X) (hτ : IsEtale B S hS τ.hom)
    (θ : R ⟶ U) (hθ' : IsEtale B S hS θ.hom) (hc : IsEtale B S hS (θ ≫ τ).hom)
    (f : X ⟶ Y) (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u))

/-- **The middle of the canonical parallel arrow, read on the extension of `G`.**  What is left
of `AlgebraicGeometry.Space.chartParallelSpacesArrow` once the two extension comparisons are
moved to its two ends: the spaces-étale unit at `θ` of the extension of `G`, conjugated by the
cartesian compositions.

`AlgebraicGeometry.Space.coreParallelArrow_eq` identifies it with
`AlgebraicGeometry.Space.parallelSectionsArrow`. -/
noncomputable def coreParallelArrow :
    (spacesSetBaseChange B S hS (τ ≫ f)).obj
        ((spacesEtaleSetRestriction B S hS τ hτ).obj
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)) ⟶
      (spacesSetBaseChange B S hS ((θ ≫ τ) ≫ f)).obj
        ((spacesEtaleSetRestriction B S hS (θ ≫ τ) hc).obj
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)) :=
  (spacesBaseChange_pushforward_compTypeU B S hS τ f).inv.app
      ((spacesEtaleSetRestriction B S hS τ hτ).obj
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)) ≫
    (spacesSetBaseChange B S hS f).map
      ((spacesSetBaseChange B S hS τ).map
          ((spacesEtalePostcompSheafAdjunction B S hS (Type u) θ hθ').unit.app
            ((spacesEtaleSetRestriction B S hS τ hτ).obj
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G))) ≫
        (spacesBaseChange_pushforward_compTypeU B S hS θ τ).hom.app
          ((spacesEtaleSetRestriction B S hS (θ ≫ τ) hc).obj
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G))) ≫
    (spacesBaseChange_pushforward_compTypeU B S hS (θ ≫ τ) f).hom.app
      ((spacesEtaleSetRestriction B S hS (θ ≫ τ) hc).obj
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G))

/-- **The parallel arrow of the fork of Stacks 03M8, as a morphism of sheaves of sets.**
Restriction of the sections of the extension of `G` along
`AlgebraicGeometry.Space.postcompBaseChangeCompOverMapNat`.  It is the arrow
`AlgebraicGeometry.Space.directImageEtaleRestrictionParallel` is built from. -/
noncomputable def parallelSectionsArrow :
    (spacesSetBaseChange B S hS (τ ≫ f)).obj
        ((spacesEtaleSetRestriction B S hS τ hτ).obj
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)) ⟶
      (spacesSetBaseChange B S hS ((θ ≫ τ) ≫ f)).obj
        ((spacesEtaleSetRestriction B S hS (θ ≫ τ) hc).obj
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)) :=
  ObjectProperty.homMk (Functor.whiskerRight
    (NatTrans.op (postcompBaseChangeCompOverMapNat B S hS τ hτ hc θ rfl f))
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj)

/-- Two successive restrictions of a section are the restriction along the composite. -/
private theorem map_op_comp_apply {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type u)
    {A A' A'' : C} (a : A ⟶ A') (b : A'' ⟶ A) (y : P.obj (op A')) :
    P.map b.op (P.map a.op y) = P.map (b ≫ a).op y :=
  (Functor.map_comp_apply P a.op b.op y).symm

/-- **The middle of the canonical parallel arrow is restriction along the comparison of the two
postcomposed base changes.**  Over an object of the spaces-étale site of `Y`, both sides are
restrictions of sections of the extension of `G`, so the statement is an equation between
morphisms of that site; it is `AlgebraicGeometry.Space.postcompBaseChange_counit_comp` at the
base change of that object along `f`. -/
theorem coreParallelArrow_eq :
    coreParallelArrow B S hS τ hτ θ hθ' hc f G =
      parallelSectionsArrow B S hS τ hτ θ hc f G := by
  refine Sheaf.hom_ext_sections (fun V x ↦ ?_)
  change ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj.map
        (Quiver.Hom.op ((spacesEtalePostcomp B S hS (θ ≫ τ) hc).map
            ((spacesBaseChange_comp B S hS (θ ≫ τ) f).inv.app V.unop)))
      (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj.map
        (Quiver.Hom.op ((spacesEtalePostcomp B S hS (θ ≫ τ) hc).map
            ((spacesBaseChange_comp B S hS θ τ).inv.app
              ((spacesBaseChange B S hS f).functor.obj V.unop))))
        (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj.map
          (Quiver.Hom.op ((spacesEtalePostcomp B S hS τ hτ).map
            ((spacesEtalePostcompBaseChangeAdjunction B S hS θ hθ').counit.app
              ((spacesBaseChange B S hS τ).functor.obj
                ((spacesBaseChange B S hS f).functor.obj V.unop)))))
          (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj.map
            (Quiver.Hom.op ((spacesEtalePostcomp B S hS τ hτ).map
              ((spacesBaseChange_comp B S hS τ f).hom.app V.unop))) x))) =
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj.map
      (Quiver.Hom.op
        ((postcompBaseChangeCompOverMapNat B S hS τ hτ hc θ rfl f).app V.unop)) x
  refine Eq.trans (map_op_comp_apply _ _ _ _) ?_
  refine Eq.trans (map_op_comp_apply _ _ _ _) ?_
  refine Eq.trans (map_op_comp_apply _ _ _ _) ?_
  refine congrArg (fun m ↦
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj.map
      (Quiver.Hom.op m) x) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun m ↦ ((spacesEtalePostcomp B S hS (θ ≫ τ) hc).map
        ((spacesBaseChange_comp B S hS (θ ≫ τ) f).inv.app V.unop)) ≫ m)
    (Category.assoc _ _ _).symm) ?_
  exact congrArg (fun m ↦ ((spacesEtalePostcomp B S hS (θ ≫ τ) hc).map
        ((spacesBaseChange_comp B S hS (θ ≫ τ) f).inv.app V.unop)) ≫ m ≫
      ((spacesEtalePostcomp B S hS τ hτ).map ((spacesBaseChange_comp B S hS τ f).hom.app V.unop)))
    (postcompBaseChange_counit_comp B S hS τ hτ θ hθ' hc
      ((spacesBaseChange B S hS f).functor.obj V.unop))

end Assemble

/-! ### Moving the extension comparison to the ends -/

section Move

variable {X U R Y : AlgebraicSpaces B S hS} (τ : U ⟶ X) (hτ : IsEtale B S hS τ.hom)
    (θ : R ⟶ U) (hθ' : IsEtale B S hS θ.hom) (hc : IsEtale B S hS (θ ≫ τ).hom)
    (f : X ⟶ Y) (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u))

/-- Replace a prefix of a composite of three morphisms. -/
private theorem comp_comp_congr {C : Type*} [Category C] {A₀ B₀ B₁ D₀ E₀ : C}
    {p : A₀ ⟶ B₀} {q : B₀ ⟶ D₀} {p' : A₀ ⟶ B₁} {q' : B₁ ⟶ D₀}
    (h : p ≫ q = p' ≫ q') (r : D₀ ⟶ E₀) : p ≫ q ≫ r = p' ≫ q' ≫ r := by
  rw [← Category.assoc, h, Category.assoc]

/-- `AlgebraicGeometry.Space.factorizationUnitArrow` with the extension comparison at `τ` moved
to the front, by the naturality of the unit of
`AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction`. -/
theorem factorizationUnitArrow_eq :
    factorizationUnitArrow B S hS τ hτ θ hθ' hc G =
      ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom ≫
        ((spacesEtalePostcompSheafAdjunction B S hS (Type u) θ hθ').unit.app
          ((spacesEtaleSetRestriction B S hS τ hτ).obj
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G))) ≫
        (spacesSetBaseChange B S hS θ).map
          ((spacesEtaleExtensionRestrictionIso B S hS (θ ≫ τ) hc).app G).inv := by
  change ((spacesEtalePostcompSheafAdjunction B S hS (Type u) θ hθ').unit.app
        ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
          ((smallEtaleSetRestriction B S hS τ hτ).obj G))) ≫
      (spacesSetBaseChange B S hS θ).map
        ((spacesEtaleSetRestriction B S hS θ hθ').map
          ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom ≫
          ((spacesEtaleExtensionRestrictionIso B S hS (θ ≫ τ) hc).app G).inv) = _
  refine Eq.trans (congrArg (fun z ↦
      ((spacesEtalePostcompSheafAdjunction B S hS (Type u) θ hθ').unit.app
        ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
          ((smallEtaleSetRestriction B S hS τ hτ).obj G))) ≫ z)
    ((spacesSetBaseChange B S hS θ).map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z ↦ z ≫ (spacesSetBaseChange B S hS θ).map
      ((spacesEtaleExtensionRestrictionIso B S hS (θ ≫ τ) hc).app G).inv)
    ((spacesEtalePostcompSheafAdjunction B S hS (Type u) θ hθ').unit.naturality
      ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom).symm) ?_
  exact Category.assoc _ _ _

/-- `AlgebraicGeometry.Space.factorizationSpacesArrow` with the extension comparison at `τ`
moved to the front and the one at `θ ≫ τ` to the back, by the previous statement and the
naturality of `AlgebraicGeometry.Space.spacesBaseChange_pushforward_compTypeU`. -/
theorem factorizationSpacesArrow_eq :
    factorizationSpacesArrow B S hS τ hτ θ hθ' hc G =
      (spacesSetBaseChange B S hS τ).map
          ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom ≫
        ((spacesSetBaseChange B S hS τ).map
            ((spacesEtalePostcompSheafAdjunction B S hS (Type u) θ hθ').unit.app
              ((spacesEtaleSetRestriction B S hS τ hτ).obj
                ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G))) ≫
          ((spacesBaseChange_pushforward_compTypeU B S hS θ τ).hom.app
            ((spacesEtaleSetRestriction B S hS (θ ≫ τ) hc).obj
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)))) ≫
        (spacesSetBaseChange B S hS (θ ≫ τ)).map
          ((spacesEtaleExtensionRestrictionIso B S hS (θ ≫ τ) hc).app G).inv := by
  change (spacesSetBaseChange B S hS τ).map (factorizationUnitArrow B S hS τ hτ θ hθ' hc G) ≫
      ((spacesBaseChange_pushforward_compTypeU B S hS θ τ).hom.app
        ((smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.obj
          ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G))) = _
  refine Eq.trans (congrArg (fun z ↦ (spacesSetBaseChange B S hS τ).map z ≫
      ((spacesBaseChange_pushforward_compTypeU B S hS θ τ).hom.app
        ((smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.obj
          ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G))))
    (factorizationUnitArrow_eq B S hS τ hτ θ hθ' hc G)) ?_
  refine Eq.trans (congrArg (fun z ↦ z ≫
      ((spacesBaseChange_pushforward_compTypeU B S hS θ τ).hom.app
        ((smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.obj
          ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G))))
    ((spacesSetBaseChange B S hS τ).map_comp _ _)) ?_
  refine Eq.trans (congrArg (fun z ↦ ((spacesSetBaseChange B S hS τ).map
        ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom ≫ z) ≫
      ((spacesBaseChange_pushforward_compTypeU B S hS θ τ).hom.app
        ((smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.obj
          ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G))))
    ((spacesSetBaseChange B S hS τ).map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg (fun z ↦ (spacesSetBaseChange B S hS τ).map
    ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom ≫ z) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z ↦ (spacesSetBaseChange B S hS τ).map
        ((spacesEtalePostcompSheafAdjunction B S hS (Type u) θ hθ').unit.app
          ((spacesEtaleSetRestriction B S hS τ hτ).obj
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G))) ≫ z)
    ((spacesBaseChange_pushforward_compTypeU B S hS θ τ).hom.naturality
      ((spacesEtaleExtensionRestrictionIso B S hS (θ ≫ τ) hc).app G).inv)) ?_
  exact (Category.assoc _ _ _).symm

/-- **`AlgebraicGeometry.Space.chartParallelSpacesArrow` with the extension comparisons at its
two ends.**  Between them sits `AlgebraicGeometry.Space.coreParallelArrow`.  The two cartesian
compositions conjugating the arrow are natural, which is what moves the comparisons out. -/
theorem chartParallelSpacesArrow_eq :
    chartParallelSpacesArrow B S hS τ hτ θ hθ' hc f G =
      (spacesSetBaseChange B S hS (τ ≫ f)).map
          ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom ≫
        coreParallelArrow B S hS τ hτ θ hθ' hc f G ≫
        (spacesSetBaseChange B S hS ((θ ≫ τ) ≫ f)).map
          ((spacesEtaleExtensionRestrictionIso B S hS (θ ≫ τ) hc).app G).inv := by
  change ((spacesBaseChange_pushforward_compTypeU B S hS τ f).inv.app
        ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
          ((smallEtaleSetRestriction B S hS τ hτ).obj G))) ≫
      (spacesSetBaseChange B S hS f).map (factorizationSpacesArrow B S hS τ hτ θ hθ' hc G) ≫
      ((spacesBaseChange_pushforward_compTypeU B S hS (θ ≫ τ) f).hom.app
        ((smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.obj
          ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G))) = _
  refine Eq.trans (congrArg (fun z ↦
      ((spacesBaseChange_pushforward_compTypeU B S hS τ f).inv.app
          ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
            ((smallEtaleSetRestriction B S hS τ hτ).obj G))) ≫
        (spacesSetBaseChange B S hS f).map z ≫
        ((spacesBaseChange_pushforward_compTypeU B S hS (θ ≫ τ) f).hom.app
          ((smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.obj
            ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G))))
    (factorizationSpacesArrow_eq B S hS τ hτ θ hθ' hc G)) ?_
  refine Eq.trans (congrArg (fun z ↦
      ((spacesBaseChange_pushforward_compTypeU B S hS τ f).inv.app
          ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
            ((smallEtaleSetRestriction B S hS τ hτ).obj G))) ≫ z ≫
        ((spacesBaseChange_pushforward_compTypeU B S hS (θ ≫ τ) f).hom.app
          ((smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.obj
            ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G))))
    ((spacesSetBaseChange B S hS f).map_comp _ _)) ?_
  refine Eq.trans (congrArg (fun z ↦
      ((spacesBaseChange_pushforward_compTypeU B S hS τ f).inv.app
          ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
            ((smallEtaleSetRestriction B S hS τ hτ).obj G))) ≫
        ((spacesSetBaseChange B S hS f).map ((spacesSetBaseChange B S hS τ).map
          ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom) ≫ z) ≫
        ((spacesBaseChange_pushforward_compTypeU B S hS (θ ≫ τ) f).hom.app
          ((smallEtaleComparisonRestriction B S hS R).asEquivalence.inverse.obj
            ((smallEtaleSetRestriction B S hS (θ ≫ τ) hc).obj G))))
    ((spacesSetBaseChange B S hS f).map_comp _ _)) ?_
  refine Eq.trans (congrArg (fun z ↦
      ((spacesBaseChange_pushforward_compTypeU B S hS τ f).inv.app
          ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
            ((smallEtaleSetRestriction B S hS τ hτ).obj G))) ≫ z)
    (Category.assoc _ _ _)) ?_
  refine Eq.trans (congrArg (fun z ↦
      ((spacesBaseChange_pushforward_compTypeU B S hS τ f).inv.app
          ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
            ((smallEtaleSetRestriction B S hS τ hτ).obj G))) ≫
        (spacesSetBaseChange B S hS f).map ((spacesSetBaseChange B S hS τ).map
          ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom) ≫ z)
    (Category.assoc _ _ _)) ?_
  refine Eq.trans (comp_comp_congr
    ((spacesBaseChange_pushforward_compTypeU B S hS τ f).inv.naturality
      ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom).symm _) ?_
  refine Eq.trans (congrArg (fun z ↦
      (spacesSetBaseChange B S hS (τ ≫ f)).map
          ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom ≫
        ((spacesBaseChange_pushforward_compTypeU B S hS τ f).inv.app
          ((spacesEtaleSetRestriction B S hS τ hτ).obj
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G))) ≫
        (spacesSetBaseChange B S hS f).map ((spacesSetBaseChange B S hS τ).map
            ((spacesEtalePostcompSheafAdjunction B S hS (Type u) θ hθ').unit.app
              ((spacesEtaleSetRestriction B S hS τ hτ).obj
                ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G))) ≫
          ((spacesBaseChange_pushforward_compTypeU B S hS θ τ).hom.app
            ((spacesEtaleSetRestriction B S hS (θ ≫ τ) hc).obj
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)))) ≫ z)
    ((spacesBaseChange_pushforward_compTypeU B S hS (θ ≫ τ) f).hom.naturality
      ((spacesEtaleExtensionRestrictionIso B S hS (θ ≫ τ) hc).app G).inv)) ?_
  refine Eq.trans (congrArg (fun z ↦
      (spacesSetBaseChange B S hS (τ ≫ f)).map
          ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom ≫
        ((spacesBaseChange_pushforward_compTypeU B S hS τ f).inv.app
          ((spacesEtaleSetRestriction B S hS τ hτ).obj
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G))) ≫ z)
    (Category.assoc _ _ _).symm) ?_
  exact congrArg (fun z ↦ (spacesSetBaseChange B S hS (τ ≫ f)).map
      ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom ≫ z)
    (Category.assoc _ _ _).symm

end Move

/-! ### The two readings of the parallel arrow agree -/

section Main

variable {X U R Y : AlgebraicSpaces B S hS} (τ : U ⟶ X) (hτ : IsEtale B S hS τ.hom)
    (θ : R ⟶ U) (hθ' : IsEtale B S hS θ.hom) (f : X ⟶ Y)
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u))

/-- **The geometric and the canonical parallel arrow of Stacks 03M8 agree**, for the
factorization `θ ≫ τ` of `θ ≫ τ` itself.  See
`AlgebraicGeometry.Space.directImageEtaleRestrictionParallel_eq_chartDirectImageParallelArrow`
for the statement at an arbitrary factorization. -/
theorem directImageEtaleRestrictionParallel_eq_chartDirectImageParallelArrow_comp
    (hc : IsEtale B S hS (θ ≫ τ).hom) :
    directImageEtaleRestrictionParallel B S hS τ hτ hc θ rfl f G =
      (chartDirectImageParallelArrow B S hS f hτ hθ' hc rfl G).hom := by
  have hgeo : directImageEtaleRestrictionParallel B S hS τ hτ hc θ rfl f G =
      ((smallEtaleComparisonRestriction B S hS Y).map
        ((spacesSetBaseChange B S hS (τ ≫ f)).map
            ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom ≫
          parallelSectionsArrow B S hS τ hτ θ hc f G ≫
          (spacesSetBaseChange B S hS ((θ ≫ τ) ≫ f)).map
            ((spacesEtaleExtensionRestrictionIso B S hS (θ ≫ τ) hc).app G).inv)).hom := rfl
  refine Eq.trans hgeo ?_
  refine Eq.trans (congrArg (fun z ↦ ((smallEtaleComparisonRestriction B S hS Y).map
      ((spacesSetBaseChange B S hS (τ ≫ f)).map
          ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom ≫ z ≫
        (spacesSetBaseChange B S hS ((θ ≫ τ) ≫ f)).map
          ((spacesEtaleExtensionRestrictionIso B S hS (θ ≫ τ) hc).app G).inv)).hom)
    (coreParallelArrow_eq B S hS τ hτ θ hθ' hc f G).symm) ?_
  refine Eq.trans (congrArg (fun z ↦ ((smallEtaleComparisonRestriction B S hS Y).map z).hom)
    (chartParallelSpacesArrow_eq B S hS τ hτ θ hθ' hc f G).symm) ?_
  exact congrArg (fun z ↦ z.hom)
    (chartDirectImageParallelArrow_comparison B S hS τ hτ θ hθ' hc f G).symm

/-- **The two readings of the second arrow of the sequence of Stacks 03M8 agree.**  Let
`f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, let `τ : U ⟶ X` and `ρ : R ⟶ X` be étale, let `θ : R ⟶ U` be étale with `θ ≫ τ = ρ`, and
let `G` be a sheaf of sets on the small étale site of `X` at the universe of the structure
rings.  Then the arrow

`a_*(G|_U) ⟶ b_*(G|_R)`

that the proof of Stacks 03M8 displays — restriction of the sections of the extension of `G`
along the comparison of the two postcomposed base changes, which is
`AlgebraicGeometry.Space.directImageEtaleRestrictionParallel` — is the canonical arrow
`AlgebraicGeometry.Space.chartDirectImageParallelArrow`, namely the direct image along `f` of
the unit of `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at `θ` conjugated by
the composition comparisons of Stacks 03G2, part (3).

With `R = U ×_X U` and `θ` one of its two projections `t, s : R ⟶ U` this says that the source's
`t^*` and `s^*`, read as the canonical arrows attached to the two factorizations of `ρ`, are the
two arrows of the displayed sequence of sections.

It is `AlgebraicGeometry.Space.chartDirectImageParallelArrow_comparison`, which descends the
canonical arrow to the spaces-étale site, followed by
`AlgebraicGeometry.Space.chartParallelSpacesArrow_eq` and
`AlgebraicGeometry.Space.coreParallelArrow_eq`, which identify the result with the geometric
arrow. -/
theorem directImageEtaleRestrictionParallel_eq_chartDirectImageParallelArrow
    {ρ : R ⟶ X} (hρ : IsEtale B S hS ρ.hom) (hθ : θ ≫ τ = ρ) :
    directImageEtaleRestrictionParallel B S hS τ hτ hρ θ hθ f G =
      (chartDirectImageParallelArrow B S hS f hτ hθ' hρ hθ G).hom := by
  subst hθ
  exact directImageEtaleRestrictionParallel_eq_chartDirectImageParallelArrow_comp
    B S hS τ hτ θ hθ' f G hρ

end Main

end AlgebraicGeometry.Space

end
