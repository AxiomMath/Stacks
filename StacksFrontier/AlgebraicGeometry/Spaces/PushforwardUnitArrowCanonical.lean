module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardPresentationArrows
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardUnitArrowSections

/-!
# The first arrow of Stacks 03M8 is restriction along the counit of the base change

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `τ : U ⟶ X` be étale and put `a = τ ≫ f`.  Stacks 03M8 asserts the exactness of

`0 → f_*F → a_*(F|_U) → b_*(F|_R)`,

and `AlgebraicGeometry.Space.isLimitForkDirectImage` proves it with the arrows written as
restrictions of sections over the products of the spaces-étale site of `X`, which is the form the
source's proof displays.  The *canonical* first arrow — the direct image along `f` of the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at `τ`, followed by the composition
comparison of Stacks 03G2, part (3) — is
`AlgebraicGeometry.Space.chartDirectImageUnitArrow`.  This file identifies the two.

The identification is the first-arrow analogue of
`AlgebraicGeometry.Space.directImageEtaleRestrictionParallel_sectionsIso`, which does the same
for the two parallel arrows, and it completes
`StacksFrontier/AlgebraicGeometry/Spaces/PushforwardSectionsEtaleRestriction.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/PushforwardUnitArrowSections.lean`: the former proves the
geometric half (the counit of the base-change adjunction *is* the second projection of the
product), the latter the statement on sections, and this file the sheaf-theoretic half — that the
small étale unit pushed forward along `f` is restriction along that counit.

## Main definitions

* `AlgebraicGeometry.Space.postcompBaseChangeCompSnd` is the first arrow of the sequence as a
  morphism of functors of sites: the comparison
  `AlgebraicGeometry.Space.spacesBaseChange_comp` of Stacks 03G2, part (2), followed by the
  counit of `AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction`, which reads
  `(V ×_Y U) over X ⟶ V ×_Y X`.

## Main results

* `AlgebraicGeometry.Space.postcompBaseChangeCompSnd_app_prodIso`: under the product comparison
  `AlgebraicGeometry.Space.postcompBaseChangeCompProdIso` that morphism is
  `CategoryTheory.Limits.prod.snd`, so restriction of sections along it is the first arrow of the
  fork of `AlgebraicGeometry.Space.isLimitForkProdOfEtalePresentation` and hence of
  `AlgebraicGeometry.Space.isLimitForkDirectImage`.
* `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_extensionRestriction`: **the
  unit of small étale restriction at an arbitrary sheaf of sets is the spaces-étale unit of its
  extension.**  This is
  `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comparison`, which is stated
  only at sheaves of the form `(smallEtaleComparisonRestriction X).obj H`, moved to a general
  sheaf `G` by the counit of the comparison equivalence of Stacks 03G1 and naturality of the
  unit; the extension of the restriction is identified with the restriction of the extension by
  `AlgebraicGeometry.Space.spacesEtaleExtensionRestrictionIso`.
* `AlgebraicGeometry.Space.spacesDirectImageUnitArrow_hom`: the spaces-étale canonical first
  arrow — the direct image along `f` of the unit of
  `AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction`, followed by the cartesian
  composition `AlgebraicGeometry.Space.spacesBaseChange_pushforward_compTypeU` — is restriction
  of sections along `AlgebraicGeometry.Space.postcompBaseChangeCompSnd`.
* `AlgebraicGeometry.Space.chartDirectImageUnitArrow_baseChangeIso`: **the canonical first arrow
  of Stacks 03M8 is the geometric one.**  Under the identification
  `AlgebraicGeometry.Space.directImageEtaleRestrictionBaseChangeIso` of the sections of
  `a_*(G|_U)` with the sections of the extension of `G` over the base change along `a`, the arrow
  `AlgebraicGeometry.Space.chartDirectImageUnitArrow` is restriction along
  `AlgebraicGeometry.Space.postcompBaseChangeCompSnd`.
* `AlgebraicGeometry.Space.chartDirectImageUnitArrow_sectionsIso`: **the canonical first arrow of
  Stacks 03M8 is the first arrow of the fork of
  `AlgebraicGeometry.Space.isLimitForkDirectImage`.**  The previous statement composed with the
  geometric comparison, so that the identification is with
  `AlgebraicGeometry.Space.directImageEtaleRestrictionSectionsIso` and the right-hand side is
  verbatim the arrow that fork carries: restriction along the counit
  `CategoryTheory.prodComonad` of the product comonad of `U`, which is
  `CategoryTheory.Limits.prod.snd`.

## Implementation notes

The chain is a transport across the comparison equivalence of Stacks 03G1 for `X`.  Writing `e`
for that equivalence and `M = e.inverse.obj G` for the extension of `G` to the spaces-étale site,
`AlgebraicGeometry.Space.chartDirectImageUnitArrow` is `e.functor` applied to a composite of
three spaces-étale morphisms, the first of which is `e.inverse` applied to the small étale unit;
the identification therefore needs that `e.inverse` of the unit is the spaces-étale unit of `M`
followed by the comparison `e.unitIso`, which is
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_extensionRestriction`.  Only
then do the cartesian composition and the extension isomorphism cancel, by naturality of
`AlgebraicGeometry.Space.spacesBaseChange_pushforward_compTypeU`.

Every step is carried out in term mode, with `Eq.trans` and `congrArg`, and not
with `rw`.  The reason: the composites that appear here are not type-correct at
`implicit` transparency — for instance the target of
`(smallEtaleComparisonRestriction U).map ((spacesEtaleExtensionRestrictionIso τ hτ).app G).inv`
is spelled
`(smallEtaleComparisonRestriction U).obj ((smallEtaleSetRestriction τ hτ ⋙ e.inverse).obj G)`
while the source of the counit it composes with is spelled
`(e.inverse ⋙ e.functor).obj ((smallEtaleSetRestriction τ hτ).obj G)`, and the two agree only
after the composition of functors is unfolded.  `rw` checks the goal at `implicit` transparency
and refuses, with the pattern reported as not found; term-mode elaboration works at default
transparency and accepts.  The arithmetic of composites is therefore isolated in the `private`
shape lemmas of the first section, which are stated in a bare category and so carry no project
types and no such spellings; `rw` is used only there.

For the same reason the statements about `AlgebraicGeometry.Space.postcompBaseChangeCompSnd` are
made at a single object `W` of the spaces-étale site rather than as equalities of natural
transformations, and its naturality is proved as a separate theorem whose statement spells the
composite functors out: a generic Mathlib lemma such as `CategoryTheory.Adjunction.unit_naturality`
is `dsimp`-normalized in its own statement and no longer matches the goal, so the two naturality
squares are instanced as `have`s with the spelling the goal carries before being used.

Nothing here raises a compiler limit or disables a linter.

## What is not done

Everything here is at the level of sheaves of *sets* at the universe of the structure rings.  The
`𝒪_Y`-linearity that would lift the identification from sheaves of sets to `Mod(𝒪_Y)` — so that
`AlgebraicGeometry.Space.moduleChartDirectImageUnitArrow`, and not only the arrow of underlying
sheaves of sets, is identified with the first arrow of the fork — is not proved here, and the
registration of the tag therefore stays on
`AlgebraicGeometry.Space.isLimitForkDirectImage`.

Nor is the statement combined with that fork into the assertion that the sequence
`0 → f_*G → a_*(G|_U) → b_*(G|_R)` written with the canonical arrows is exact: that needs this
file's first arrow together with
`AlgebraicGeometry.Space.directImageEtaleRestrictionParallel_sectionsIso` for the parallel arrows
and the identification of
`AlgebraicGeometry.Space.chartDirectImageParallelArrow` with
`AlgebraicGeometry.Space.directImageEtaleRestrictionParallel`, which is not here.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ u₁ v₂ u₂ u

namespace AlgebraicGeometry.Space

/-! ### The arithmetic of composites, in a bare category -/

section Shapes

variable {CC : Type u₁} [Category.{v₁} CC]

/-- An inverse pair cancelled off the end of a four-factor composite. -/
private theorem comp₃_cancel_right {O₀ O₁ O₂ O₃ : CC} (p : O₀ ⟶ O₁) (q : O₁ ⟶ O₂)
    {r : O₂ ⟶ O₃} {s : O₃ ⟶ O₂} (h : r ≫ s = 𝟙 O₂) : (p ≫ q ≫ r) ≫ s = p ≫ q := by
  rw [Category.assoc, Category.assoc, h, Category.comp_id]

/-- A morphism with a left inverse moved across a factorization: if `u` is a left inverse of
`v` and `v ≫ w` is `z`, then `w` is `u ≫ z`. -/
private theorem eq_comp_of_inv_comp {O₀ O₁ O₂ : CC} {u : O₀ ⟶ O₁} {v : O₁ ⟶ O₀}
    {w : O₀ ⟶ O₂} {z : O₁ ⟶ O₂} (hid : u ≫ v = 𝟙 O₀) (hc : v ≫ w = z) : w = u ≫ z := by
  rw [← hc, ← Category.assoc, hid, Category.id_comp]

/-- A split monomorphism cancelled on the left of an equality of composites. -/
private theorem cancel_left_of_comp_id {O₀ O₁ O₂ : CC} {p : O₀ ⟶ O₁} {p' : O₁ ⟶ O₀}
    (hp : p ≫ p' = 𝟙 O₀) {a b : O₀ ⟶ O₂} (h : p' ≫ a = p' ≫ b) : a = b := by
  rw [← Category.id_comp a, ← Category.id_comp b, ← hp, Category.assoc, Category.assoc, h]

/-- An inverse pair cancelled in the middle, after a factorization of the leading morphism. -/
private theorem comp_cancel_mid {O₀ O₁ O₂ O₃ : CC} {m : O₀ ⟶ O₂} {v : O₀ ⟶ O₁}
    {t : O₁ ⟶ O₂} {ti : O₂ ⟶ O₁} (w : O₁ ⟶ O₃) (h : m = v ≫ t) (hti : t ≫ ti = 𝟙 O₁) :
    m ≫ ti ≫ w = v ≫ w := by
  rw [h, Category.assoc, ← Category.assoc t, hti, Category.id_comp]

/-- An inverse pair cancelled off the end of a three-factor composite. -/
private theorem comp_comp_cancel {O₀ O₁ O₂ : CC} (a : O₀ ⟶ O₁) {b : O₁ ⟶ O₂} {b' : O₂ ⟶ O₁}
    (h : b ≫ b' = 𝟙 O₁) : (a ≫ b) ≫ b' = a := by
  rw [Category.assoc, h, Category.comp_id]

/-- An inverse cancelled on the left of a morphism given as a factorization through the
corresponding isomorphism. -/
private theorem inv_comp_of_eq {O₀ O₁ O₂ : CC} {ki : O₀ ⟶ O₁} {kh : O₁ ⟶ O₀} {e : O₁ ⟶ O₂}
    {p : O₀ ⟶ O₂} (hid : ki ≫ kh = 𝟙 O₀) (h : e = kh ≫ p) : ki ≫ e = p := by
  rw [h, ← Category.assoc, hid, Category.id_comp]

/-- Regrouping of a four-factor composite off its first three factors. -/
private theorem comp₄_assoc {O₀ O₁ O₂ O₃ O₄ : CC} (a : O₀ ⟶ O₁) (b : O₁ ⟶ O₂) (c : O₂ ⟶ O₃)
    (d : O₃ ⟶ O₄) : (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by
  rw [Category.assoc, Category.assoc]

end Shapes

section Generic

variable {CC : Type u₁} [Category.{v₁} CC] {DD : Type u₂} [Category.{v₂} DD]

/-- **The inverse of an equivalence carries its counit to the inverse unit.**  For an
equivalence `e` and an object `Q` of its target, `e.inverse` applied to the counit at `Q` is the
inverse unit at `e.inverse.obj Q`.

It is `CategoryTheory.Equivalence.unit_inverse_comp`, one of the two triangle identities, read as
the statement that the unit and that morphism are inverse to one another. -/
private theorem inverse_map_counit_app (e : CC ≌ DD) (Q : DD) :
    e.inverse.map (e.counitIso.hom.app Q) = e.unitIso.inv.app (e.inverse.obj Q) :=
  (Iso.hom_comp_eq_id (e.unitIso.app (e.inverse.obj Q))).mp (e.unit_inverse_comp Q)

end Generic

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The first arrow of the fork as a morphism of functors of sites -/

section Counit

variable {X U Y : AlgebraicSpaces B S hS} (τ : U ⟶ X) (hτ : IsEtale B S hS τ.hom) (f : X ⟶ Y)

/-- **The first arrow of Stacks 03M8 is natural in the object of the site.**  For a morphism
`k : W ⟶ W'` of the spaces-étale site of `Y`, base changing `k` along `a = τ ≫ f` and then
projecting to the base change of `W'` along `f` is projecting and then base changing along `f`.

The composition comparison `AlgebraicGeometry.Space.spacesBaseChange_comp` of Stacks 03G2,
part (2), is natural, and the counit of
`AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction` is natural; both are instanced
as hypotheses in the spelling the goal carries, because the generic form of the second is
`dsimp`-normalized in its own statement and does not match. -/
theorem postcompBaseChangeCompSnd_naturality {W W' : SpacesEtale B S hS Y} (k : W ⟶ W') :
    (spacesEtalePostcomp B S hS τ hτ).map
          ((spacesBaseChange B S hS (τ ≫ f)).functor.map k) ≫
        ((spacesEtalePostcomp B S hS τ hτ).map
              ((spacesBaseChange_comp B S hS τ f).inv.app W') ≫
            (spacesEtalePostcompBaseChangeAdjunction B S hS τ hτ).counit.app
              ((spacesBaseChange B S hS f).functor.obj W')) =
      ((spacesEtalePostcomp B S hS τ hτ).map
              ((spacesBaseChange_comp B S hS τ f).inv.app W) ≫
            (spacesEtalePostcompBaseChangeAdjunction B S hS τ hτ).counit.app
              ((spacesBaseChange B S hS f).functor.obj W)) ≫
        (spacesBaseChange B S hS f).functor.map k := by
  have h : (spacesBaseChange B S hS (τ ≫ f)).functor.map k ≫
        (spacesBaseChange_comp B S hS τ f).inv.app W' =
      (spacesBaseChange_comp B S hS τ f).inv.app W ≫
        (spacesBaseChange B S hS τ).functor.map ((spacesBaseChange B S hS f).functor.map k) :=
    (spacesBaseChange_comp B S hS τ f).inv.naturality k
  have hc : (spacesEtalePostcomp B S hS τ hτ).map
          ((spacesBaseChange B S hS τ).functor.map
            ((spacesBaseChange B S hS f).functor.map k)) ≫
        (spacesEtalePostcompBaseChangeAdjunction B S hS τ hτ).counit.app
          ((spacesBaseChange B S hS f).functor.obj W') =
      (spacesEtalePostcompBaseChangeAdjunction B S hS τ hτ).counit.app
          ((spacesBaseChange B S hS f).functor.obj W) ≫
        (spacesBaseChange B S hS f).functor.map k :=
    (spacesEtalePostcompBaseChangeAdjunction B S hS τ hτ).counit.naturality
      ((spacesBaseChange B S hS f).functor.map k)
  rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc, hc,
    ← Category.assoc]

/-- **The first arrow `V ×_Y U ⟶ V ×_Y X` of Stacks 03M8 as a morphism of functors.**  For
`a = τ ≫ f`, the base change along `a` of an object `V` of the spaces-étale site of `Y`, read
over `X` by postcomposition with `τ`, maps to the base change of `V` along `f`, naturally in `V`.

It is the composition comparison of Stacks 03G2, part (2), followed by the counit of the
adjunction of sites of Stacks 03LP and 03G2, part (1).  By
`AlgebraicGeometry.Space.postcompBaseChangeCompSnd_app_prodIso` it is the second projection of
the product `U ⨯ (V ×_Y X)`, which is the first arrow of the fork of
`AlgebraicGeometry.Space.isLimitForkDirectImage`.

Its naturality is `AlgebraicGeometry.Space.postcompBaseChangeCompSnd_naturality`. -/
noncomputable def postcompBaseChangeCompSnd :
    (spacesBaseChange B S hS (τ ≫ f)).functor ⋙ spacesEtalePostcomp B S hS τ hτ ⟶
      (spacesBaseChange B S hS f).functor where
  app W := (spacesEtalePostcomp B S hS τ hτ).map
        ((spacesBaseChange_comp B S hS τ f).inv.app W) ≫
      (spacesEtalePostcompBaseChangeAdjunction B S hS τ hτ).counit.app
        ((spacesBaseChange B S hS f).functor.obj W)
  naturality _ _ k := postcompBaseChangeCompSnd_naturality B S hS τ hτ f k

/-- **The first arrow of Stacks 03M8 is the second projection of the product.**  Under the
comparison `AlgebraicGeometry.Space.postcompBaseChangeCompProdIso`, which reads `V ×_Y U` over
`X` as the product `U ⨯ (V ×_Y X)`, the component of
`AlgebraicGeometry.Space.postcompBaseChangeCompSnd` at an object `W` of the spaces-étale site of
`Y` is `CategoryTheory.Limits.prod.snd`.

This is the first-arrow analogue of
`AlgebraicGeometry.Space.postcompBaseChangeCompOverMapNat_prodIso`: the composition comparisons
of `τ` with `f` cancel, and what is left is
`AlgebraicGeometry.Space.postcompBaseChangeProdIsoApp_hom_snd` against
`AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction_counit_app_eq`, which is the
identification `AlgebraicGeometry.Space.postcompBaseChangeProdIsoApp_inv_comp_counit` of
`StacksFrontier/AlgebraicGeometry/Spaces/PushforwardUnitArrowSections.lean` read in the composite
setting. -/
theorem postcompBaseChangeCompSnd_app_prodIso (W : SpacesEtale B S hS Y) :
    (postcompBaseChangeCompSnd B S hS τ hτ f).app W =
      (postcompBaseChangeCompProdIso B S hS τ hτ f).hom.app W ≫ prod.snd := by
  have h : (postcompBaseChangeProdIso B S hS τ hτ (spacesBaseChange B S hS τ)).hom.app
        ((spacesBaseChange B S hS f).functor.obj W) ≫ prod.snd =
      (spacesEtalePostcompBaseChangeAdjunction B S hS τ hτ).counit.app
        ((spacesBaseChange B S hS f).functor.obj W) :=
    (postcompBaseChangeProdIsoApp_hom_snd B S hS τ hτ (spacesBaseChange B S hS τ)
        ((spacesBaseChange B S hS f).functor.obj W)).trans
      (spacesEtalePostcompBaseChangeAdjunction_counit_app_eq B S hS τ hτ
        ((spacesBaseChange B S hS f).functor.obj W)).symm
  simp only [postcompBaseChangeCompSnd, postcompBaseChangeCompProdIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp]
  rw [← h]
  exact (Category.assoc _ _ _).symm

/-! ### The spaces-étale canonical arrow on sections -/

/-- **The spaces-étale canonical first arrow is restriction along the counit.**  For a sheaf of
sets `M` on the spaces-étale site of `X` at the universe of the structure rings, the direct image
along `f` of the unit of `AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction` at `τ`,
followed by the cartesian composition
`AlgebraicGeometry.Space.spacesBaseChange_pushforward_compTypeU`, is restriction of sections
along `AlgebraicGeometry.Space.postcompBaseChangeCompSnd`.

Each of the two factors is itself a restriction of sections — the unit by
`AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction_unit_app` and the cartesian
composition by its construction from `AlgebraicGeometry.Space.spacesBaseChange_comp` — so at
every object of the site the statement is the functor law of `M` for the composite of the two
morphisms of sites. -/
theorem spacesDirectImageUnitArrow_hom
    (M : Sheaf (SpacesEtale.topology B S hS X) (Type u)) :
    ((spacesSetBaseChange B S hS f).map
          ((spacesEtalePostcompSheafAdjunction B S hS (Type u) τ hτ).unit.app M) ≫
        (spacesBaseChange_pushforward_compTypeU B S hS τ f).hom.app
          ((spacesEtaleSetRestriction B S hS τ hτ).obj M)).hom =
      Functor.whiskerRight (NatTrans.op (postcompBaseChangeCompSnd B S hS τ hτ f)) M.obj := by
  refine NatTrans.ext (funext fun W ↦ ?_)
  exact (M.obj.map_comp
    ((spacesEtalePostcompBaseChangeAdjunction B S hS τ hτ).counit.app
      ((spacesBaseChange B S hS f).functor.obj W.unop)).op
    ((spacesEtalePostcomp B S hS τ hτ).map
      ((spacesBaseChange_comp B S hS τ f).inv.app W.unop)).op).symm

end Counit

/-! ### The transport across the comparison equivalence of Stacks 03G1 -/

section Transport

variable {X U Y : AlgebraicSpaces B S hS} (τ : U ⟶ X) (hτ : IsEtale B S hS τ.hom)
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u))

/-- **The restriction to `U` of the counit at `X`.**  The small étale restriction along `τ` of
the counit of the comparison equivalence of Stacks 03G1 for `X` at a sheaf of sets `G` is the
inverse of `AlgebraicGeometry.Space.spacesEtaleExtensionRestrictionIso`, read on the small étale
site of `U`, followed by the counit for `U` at `G|_U`.

It is `AlgebraicGeometry.Space.smallEtaleSetRestrictionConjMate_counit` with the comparison
isomorphism moved across; the mate of that statement is
`AlgebraicGeometry.Space.spacesEtaleExtensionRestrictionIso` at `G` on the nose. -/
private theorem smallEtaleSetRestriction_map_counit :
    (smallEtaleSetRestriction B S hS τ hτ).map
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app G) =
      (smallEtaleComparisonRestriction B S hS U).map
          ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).inv ≫
        (smallEtaleComparisonRestriction B S hS U).asEquivalence.counitIso.hom.app
          ((smallEtaleSetRestriction B S hS τ hτ).obj G) :=
  eq_comp_of_inv_comp
    (Functor.map_inv_hom' (smallEtaleComparisonRestriction B S hS U)
      ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G))
    (smallEtaleSetRestrictionConjMate_counit B S hS τ hτ G)

/-- **The extension of the restricted counit.**  Applying the inverse of the comparison
equivalence for `U` to the previous statement leaves the inverse unit at the restriction of the
extension of `G`, followed by the inverse of
`AlgebraicGeometry.Space.spacesEtaleExtensionRestrictionIso`: the two occurrences of the unit
isomorphism for `U` cancel, by
`CategoryTheory.Equivalence.inv_fun_map` and
`AlgebraicGeometry.Space.inverse_map_counit_app`. -/
private theorem inverse_map_restriction_counit :
    (smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.map
        ((smallEtaleSetRestriction B S hS τ hτ).map
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app G)) =
      (smallEtaleComparisonRestriction B S hS U).asEquivalence.unitIso.inv.app
          ((spacesEtaleSetRestriction B S hS τ hτ).obj
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)) ≫
        ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).inv := by
  have hfm : (smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.map
        ((smallEtaleComparisonRestriction B S hS U).map
          ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).inv) =
      (smallEtaleComparisonRestriction B S hS U).asEquivalence.unitIso.inv.app
          ((spacesEtaleSetRestriction B S hS τ hτ).obj
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)) ≫
        ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).inv ≫
          (smallEtaleComparisonRestriction B S hS U).asEquivalence.unitIso.hom.app
            ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
              ((smallEtaleSetRestriction B S hS τ hτ).obj G)) :=
    Equivalence.inv_fun_map _ _ _ _
  refine Eq.trans (congrArg
    (fun m ↦ (smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.map m)
    (smallEtaleSetRestriction_map_counit B S hS τ hτ G)) ?_
  refine Eq.trans (Functor.map_comp _ _ _) ?_
  refine Eq.trans (congrArg₂ (fun m n ↦ m ≫ n) hfm
    (inverse_map_counit_app (smallEtaleComparisonRestriction B S hS U).asEquivalence
      ((smallEtaleSetRestriction B S hS τ hτ).obj G))) ?_
  exact comp₃_cancel_right _ _
    ((smallEtaleComparisonRestriction B S hS U).asEquivalence.unitIso.hom_inv_id_app _)

/-- The previous statement pushed forward along `τ`.  The direct image of sheaves of sets on the
small étale sites is the spaces-étale one conjugated by the comparison equivalences of
Stacks 03G1, so this is the previous statement with two functors applied to it. -/
private theorem smallEtaleDirectImage_map_restriction_counit :
    (smallEtaleDirectImage B S hS τ).map
        ((smallEtaleSetRestriction B S hS τ hτ).map
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app G)) =
      (smallEtaleComparisonRestriction B S hS X).map
        ((spacesSetBaseChange B S hS τ).map
          ((smallEtaleComparisonRestriction B S hS U).asEquivalence.unitIso.inv.app
              ((spacesEtaleSetRestriction B S hS τ hτ).obj
                ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)) ≫
            ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).inv)) :=
  congrArg (fun m ↦ (smallEtaleComparisonRestriction B S hS X).map
      ((spacesSetBaseChange B S hS τ).map m))
    (inverse_map_restriction_counit B S hS τ hτ G)

/-- **The counit of Stacks 03G1 followed by the small étale unit.**  For a sheaf of sets `G` on
the small étale site of `X`, the counit of the comparison equivalence at `G` followed by the unit
of `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at `G` is the comparison
equivalence applied to the spaces-étale unit at the extension of `G`, corrected by the inverse of
`AlgebraicGeometry.Space.spacesEtaleExtensionRestrictionIso`.

This is the step that moves
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comparison` — which is stated
only at a sheaf of the form `(smallEtaleComparisonRestriction X).obj H` — to an arbitrary `G`:
naturality of the unit against the counit at `G` replaces the unit at `G` by the unit at the
extension of `G` read back, and the comparison of direct images is evaluated by
`CategoryTheory.Category.comp_id`. -/
private theorem counit_comp_unit_eq :
    (smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app G ≫
        (smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app G =
      (smallEtaleComparisonRestriction B S hS X).map
        ((spacesEtalePostcompSheafAdjunction B S hS (Type u) τ hτ).unit.app
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G) ≫
          (spacesSetBaseChange B S hS τ).map
            ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).inv) := by
  have hnat : (smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app G ≫
        (smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app G =
      (smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app
          ((smallEtaleComparisonRestriction B S hS X).obj
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)) ≫
        (smallEtaleDirectImage B S hS τ).map
          ((smallEtaleSetRestriction B S hS τ hτ).map
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app G)) :=
    (smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.naturality _
  have hcmp : (smallToposMorphismTypeU_comparison B S hS τ).hom.app
        ((spacesEtaleSetRestriction B S hS τ hτ).obj
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)) =
      (smallEtaleComparisonRestriction B S hS X).map
        ((spacesSetBaseChange B S hS τ).map
          ((smallEtaleComparisonRestriction B S hS U).asEquivalence.unitIso.inv.app
            ((spacesEtaleSetRestriction B S hS τ hτ).obj
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)))) :=
    Category.comp_id _
  have hstep : (smallEtaleDirectImage B S hS τ).map
        ((smallEtaleSetRestriction B S hS τ hτ).map
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app G)) =
      (smallToposMorphismTypeU_comparison B S hS τ).hom.app
          ((spacesEtaleSetRestriction B S hS τ hτ).obj
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)) ≫
        (smallEtaleComparisonRestriction B S hS X).map
          ((spacesSetBaseChange B S hS τ).map
            ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).inv) :=
    (smallEtaleDirectImage_map_restriction_counit B S hS τ hτ G).trans
      ((congrArg (smallEtaleComparisonRestriction B S hS X).map
          ((spacesSetBaseChange B S hS τ).map_comp _ _)).trans
        (((smallEtaleComparisonRestriction B S hS X).map_comp _ _).trans
          (congrArg (fun m ↦ m ≫ (smallEtaleComparisonRestriction B S hS X).map
              ((spacesSetBaseChange B S hS τ).map
                ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).inv))
            hcmp.symm)))
  refine hnat.trans ?_
  refine Eq.trans (congrArg
    (fun m ↦ (smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app
      ((smallEtaleComparisonRestriction B S hS X).obj
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)) ≫ m)
    hstep) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg
    (fun m ↦ m ≫ (smallEtaleComparisonRestriction B S hS X).map
      ((spacesSetBaseChange B S hS τ).map
        ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).inv))
    (smallEtaleSetRestrictionAdjunction_unit_comparison B S hS τ hτ
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G))) ?_
  exact ((smallEtaleComparisonRestriction B S hS X).map_comp _ _).symm

/-- **The unit of small étale restriction at an arbitrary sheaf is the spaces-étale unit of its
extension.**  For a sheaf of sets `G` on the small étale site of `X`, the extension to the
spaces-étale site of the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at `τ`, read through the comparison
`AlgebraicGeometry.Space.spacesEtaleExtensionRestrictionIso` of the extension of a restriction
with the restriction of an extension, is the unit of
`AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction` at the extension of `G`.

This is the sheaf-theoretic half that the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/PushforwardUnitArrowSections.lean` record as missing.  It
is `AlgebraicGeometry.Space.counit_comp_unit_eq` with the comparison equivalence inverted:
`CategoryTheory.Equivalence.inv_fun_map` and
`AlgebraicGeometry.Space.inverse_map_counit_app` turn that statement into a factorization of the
extended unit through the unit isomorphism, and the extension isomorphism then cancels against
its own inverse. -/
theorem smallEtaleSetRestrictionAdjunction_unit_extensionRestriction :
    (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
          ((smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app G) ≫
        (smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app
            ((spacesSetBaseChange B S hS τ).obj
              ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
                ((smallEtaleSetRestriction B S hS τ hτ).obj G))) ≫
          (spacesSetBaseChange B S hS τ).map
            ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom =
      (spacesEtalePostcompSheafAdjunction B S hS (Type u) τ hτ).unit.app
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G) := by
  have hfun : (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
        ((smallEtaleComparisonRestriction B S hS X).map
          ((spacesEtalePostcompSheafAdjunction B S hS (Type u) τ hτ).unit.app
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G) ≫
            (spacesSetBaseChange B S hS τ).map
              ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).inv)) =
      (smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G) ≫
        ((spacesEtalePostcompSheafAdjunction B S hS (Type u) τ hτ).unit.app
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G) ≫
            (spacesSetBaseChange B S hS τ).map
              ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).inv) ≫
          (smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.hom.app
            ((spacesSetBaseChange B S hS τ).obj
              ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
                ((smallEtaleSetRestriction B S hS τ hτ).obj G))) :=
    Equivalence.inv_fun_map _ _ _ _
  have hmapid : (spacesSetBaseChange B S hS τ).map
          ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).inv ≫
        (spacesSetBaseChange B S hS τ).map
          ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom = 𝟙 _ :=
    Functor.map_inv_hom' (spacesSetBaseChange B S hS τ)
      ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G)
  have hkey := (((congrArg
          (fun m ↦ m ≫ (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
            ((smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app G))
          (inverse_map_counit_app (smallEtaleComparisonRestriction B S hS X).asEquivalence
            G)).symm.trans
        (Functor.map_comp (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app G)
          ((smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app G)).symm).trans
      (congrArg
        (fun m ↦ (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map m)
        (counit_comp_unit_eq B S hS τ hτ G))).trans hfun
  refine Eq.trans (comp_cancel_mid _
    (cancel_left_of_comp_id
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.hom_inv_id_app _) hkey)
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.hom_inv_id_app _)) ?_
  exact comp_comp_cancel _ hmapid

/-! ### The canonical first arrow of Stacks 03M8 is the geometric one -/

/-- **The canonical first arrow of Stacks 03M8 is the geometric one.**  Let `f : X ⟶ Y` be a
morphism of algebraic spaces, let `τ : U ⟶ X` be étale, put `a = τ ≫ f` and let `G` be a sheaf of
sets on the small étale site of `X` at the universe of the structure rings.  Then under the
identification `AlgebraicGeometry.Space.directImageEtaleRestrictionBaseChangeIso` of the sections
of `a_*(G|_U)` with the sections of the extension of `G` over the base change along `a`, the
canonical arrow `AlgebraicGeometry.Space.chartDirectImageUnitArrow` — the direct image along `f`
of the unit of `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at `τ`, followed by
the composition comparison of Stacks 03G2, part (3) — is restriction of sections along
`AlgebraicGeometry.Space.postcompBaseChangeCompSnd`, which by
`AlgebraicGeometry.Space.postcompBaseChangeCompSnd_app_prodIso` is the second projection of the
product `U ⨯ (V ×_Y X)`.

So the first arrow `f_*P → a_*(P|_U)` of the source's sequence is the first arrow of the fork of
`AlgebraicGeometry.Space.isLimitForkDirectImage`, which is what the `a_*(F|_U)` reading of
Stacks 03M8 asks for on the first arrow.

The arrow is `(smallEtaleComparisonRestriction Y)` applied to a composite of three spaces-étale
morphisms; the extension isomorphism is moved past the cartesian composition by its naturality,
and the three remaining factors become the spaces-étale unit by
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_extensionRestriction`.  What is
left is `AlgebraicGeometry.Space.spacesDirectImageUnitArrow_hom`. -/
theorem chartDirectImageUnitArrow_baseChangeIso (f : X ⟶ Y) :
    (chartDirectImageUnitArrow B S hS f hτ G).hom ≫
        (directImageEtaleRestrictionBaseChangeIso B S hS τ hτ f G).hom =
      Functor.whiskerLeft (comparisonFunctor B S hS Y).op
        (Functor.whiskerRight (NatTrans.op (postcompBaseChangeCompSnd B S hS τ hτ f))
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj) := by
  have hchart : chartDirectImageUnitArrow B S hS f hτ G =
      (smallEtaleComparisonRestriction B S hS Y).map
        ((spacesSetBaseChange B S hS f).map
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
              ((smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app G)) ≫
          (spacesSetBaseChange B S hS f).map
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app
                ((spacesSetBaseChange B S hS τ).obj
                  ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
                    ((smallEtaleSetRestriction B S hS τ hτ).obj G)))) ≫
            (spacesBaseChange_pushforward_compTypeU B S hS τ f).hom.app
              ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
                ((smallEtaleSetRestriction B S hS τ hτ).obj G))) :=
    ((Functor.map_comp (smallEtaleComparisonRestriction B S hS Y) _ _).trans
      (congrArg
        (fun m ↦ (smallEtaleComparisonRestriction B S hS Y).map
            ((spacesSetBaseChange B S hS f).map
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
                ((smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app G))) ≫ m)
        (Functor.map_comp (smallEtaleComparisonRestriction B S hS Y) _ _))).symm
  have hcompnat : (spacesBaseChange_pushforward_compTypeU B S hS τ f).hom.app
          ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
            ((smallEtaleSetRestriction B S hS τ hτ).obj G)) ≫
        (spacesSetBaseChange B S hS (τ ≫ f)).map
          ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom =
      (spacesSetBaseChange B S hS f).map
          ((spacesSetBaseChange B S hS τ).map
            ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom) ≫
        (spacesBaseChange_pushforward_compTypeU B S hS τ f).hom.app
          ((spacesEtaleSetRestriction B S hS τ hτ).obj
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)) :=
    ((spacesBaseChange_pushforward_compTypeU B S hS τ f).hom.naturality
      ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom).symm
  have hunitpush : (spacesSetBaseChange B S hS f).map
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
              ((smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app G)) ≫
          (spacesSetBaseChange B S hS f).map
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app
                ((spacesSetBaseChange B S hS τ).obj
                  ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
                    ((smallEtaleSetRestriction B S hS τ hτ).obj G)))) ≫
            (spacesSetBaseChange B S hS f).map
              ((spacesSetBaseChange B S hS τ).map
                ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom) =
      (spacesSetBaseChange B S hS f).map
        ((spacesEtalePostcompSheafAdjunction B S hS (Type u) τ hτ).unit.app
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)) :=
    (((spacesSetBaseChange B S hS f).map_comp _ _).trans
        (congrArg
          (fun m ↦ (spacesSetBaseChange B S hS f).map
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
              ((smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app G)) ≫ m)
          ((spacesSetBaseChange B S hS f).map_comp _ _))).symm.trans
      (congrArg (spacesSetBaseChange B S hS f).map
        (smallEtaleSetRestrictionAdjunction_unit_extensionRestriction B S hS τ hτ G))
  have hinner : ((spacesSetBaseChange B S hS f).map
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
              ((smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app G)) ≫
          (spacesSetBaseChange B S hS f).map
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app
                ((spacesSetBaseChange B S hS τ).obj
                  ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
                    ((smallEtaleSetRestriction B S hS τ hτ).obj G)))) ≫
            (spacesBaseChange_pushforward_compTypeU B S hS τ f).hom.app
              ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
                ((smallEtaleSetRestriction B S hS τ hτ).obj G))) ≫
        (spacesSetBaseChange B S hS (τ ≫ f)).map
          ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom =
      (spacesSetBaseChange B S hS f).map
          ((spacesEtalePostcompSheafAdjunction B S hS (Type u) τ hτ).unit.app
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)) ≫
        (spacesBaseChange_pushforward_compTypeU B S hS τ f).hom.app
          ((spacesEtaleSetRestriction B S hS τ hτ).obj
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)) := by
    refine Eq.trans (comp₄_assoc _ _ _ _) ?_
    refine Eq.trans (congrArg
      (fun m ↦ (spacesSetBaseChange B S hS f).map
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
              ((smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app G)) ≫
          (spacesSetBaseChange B S hS f).map
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app
              ((spacesSetBaseChange B S hS τ).obj
                ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
                  ((smallEtaleSetRestriction B S hS τ hτ).obj G)))) ≫ m)
      hcompnat) ?_
    refine Eq.trans (comp₄_assoc _ _ _ _).symm ?_
    exact congrArg
      (fun m ↦ m ≫ (spacesBaseChange_pushforward_compTypeU B S hS τ f).hom.app
        ((spacesEtaleSetRestriction B S hS τ hτ).obj
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)))
      hunitpush
  have key : chartDirectImageUnitArrow B S hS f hτ G ≫
        (smallEtaleComparisonRestriction B S hS Y).map
          ((spacesSetBaseChange B S hS (τ ≫ f)).map
            ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom) =
      (smallEtaleComparisonRestriction B S hS Y).map
        ((spacesSetBaseChange B S hS f).map
            ((spacesEtalePostcompSheafAdjunction B S hS (Type u) τ hτ).unit.app
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)) ≫
          (spacesBaseChange_pushforward_compTypeU B S hS τ f).hom.app
            ((spacesEtaleSetRestriction B S hS τ hτ).obj
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G))) :=
    (congrArg
        (fun m ↦ m ≫ (smallEtaleComparisonRestriction B S hS Y).map
          ((spacesSetBaseChange B S hS (τ ≫ f)).map
            ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G).hom))
        hchart).trans
      (((smallEtaleComparisonRestriction B S hS Y).map_comp _ _).symm.trans
        (congrArg (smallEtaleComparisonRestriction B S hS Y).map hinner))
  refine Eq.trans (Sheaf.hom_ext_iff.mp key) ?_
  exact congrArg (Functor.whiskerLeft (comparisonFunctor B S hS Y).op)
    (spacesDirectImageUnitArrow_hom B S hS τ hτ f
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G))

/-- **The canonical first arrow of Stacks 03M8 is the first arrow of the fork.**  Under the
identification `AlgebraicGeometry.Space.directImageEtaleRestrictionSectionsIso` of the sections of
`a_*(G|_U)` with the middle term `V ↦ G^{ext}(U ⨯ (V ×_Y X))` of the fork of
`AlgebraicGeometry.Space.isLimitForkDirectImage`, the canonical arrow
`AlgebraicGeometry.Space.chartDirectImageUnitArrow` is restriction of sections along
`CategoryTheory.Limits.prod.snd`, written as the counit of the product comonad — which is
verbatim the first arrow that fork carries.

With `τ` the structure morphism of a surjective étale scheme chart `U` of `X`, so that
`AlgebraicGeometry.Space.etaleOverObj_comparisonFunctor_obj` identifies `etaleOverObj τ hτ` with
`(comparisonFunctor X).obj U`, this says that the sequence
`0 → f_*G → a_*(G|_U) → b_*(G|_R)` of Stacks 03M8 has as its first arrow the first arrow of the
exact sequence that carries the tag.

It is `AlgebraicGeometry.Space.chartDirectImageUnitArrow_baseChangeIso` followed by the geometric
comparison, where `AlgebraicGeometry.Space.postcompBaseChangeCompSnd_app_prodIso` makes the
comparison cancel against its own inverse. -/
theorem chartDirectImageUnitArrow_sectionsIso (f : X ⟶ Y) :
    (chartDirectImageUnitArrow B S hS f hτ G).hom ≫
        (directImageEtaleRestrictionSectionsIso B S hS τ hτ f G).hom =
      Functor.whiskerLeft (chartBaseChangeFunctor B S hS f).op
        (Functor.whiskerRight (NatTrans.op ((prodComonad (etaleOverObj B S hS τ hτ)).ε))
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj :
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj ⟶
            (prod.functor.obj (etaleOverObj B S hS τ hτ)).op ⋙
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj) := by
  have hsections : Functor.whiskerRight
          (NatTrans.op (postcompBaseChangeCompSnd B S hS τ hτ f))
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj ≫
        (postcompBaseChangeCompSectionsIso B S hS τ hτ f
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj).hom =
      Functor.whiskerLeft (spacesBaseChange B S hS f).functor.op
        (Functor.whiskerRight (NatTrans.op ((prodComonad (etaleOverObj B S hS τ hτ)).ε))
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj) := by
    refine NatTrans.ext (funext fun W ↦ ?_)
    refine Eq.trans
      (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj.map_comp
        ((postcompBaseChangeCompSnd B S hS τ hτ f).app W.unop).op
        ((postcompBaseChangeCompProdIso B S hS τ hτ f).inv.app W.unop).op).symm ?_
    exact congrArg
      (fun m ↦ ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj.map
        (Quiver.Hom.op m))
      (inv_comp_of_eq ((postcompBaseChangeCompProdIso B S hS τ hτ f).inv_hom_id_app W.unop)
        (postcompBaseChangeCompSnd_app_prodIso B S hS τ hτ f W.unop))
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg
    (fun m ↦ m ≫ Functor.whiskerLeft (comparisonFunctor B S hS Y).op
      (postcompBaseChangeCompSectionsIso B S hS τ hτ f
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj).hom)
    (chartDirectImageUnitArrow_baseChangeIso B S hS τ hτ G f)) ?_
  exact congrArg (Functor.whiskerLeft (comparisonFunctor B S hS Y).op) hsections

end Transport

end AlgebraicGeometry.Space

end
