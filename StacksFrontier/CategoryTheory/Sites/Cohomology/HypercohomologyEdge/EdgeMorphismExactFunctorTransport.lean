module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismExactFunctor

/-!
# Transporting the unit of a postcomposed right derived functor

`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit F G RF unit`
exhibits `RF ⋙ G.mapDerivedCategory` as a right derived functor of `F ⋙ G`, for `F` additive with
right derived functor `RF` presented by `unit` and `G` exact. A chase that composes a chain of
right derived descents meets that unit repeatedly, and each time it has to move something past it:
a comparison `RF ⟶ RF'` of the two right derived functors upstairs, a transformation `F ⟶ F'` of
the degreewise functors appearing as a prefix of the unit, or an exact functor **precomposed** on
the other side. This file records those transports.

The transports are statements about `exactPostcomposeUnit` alone: no site, no sheaf of modules
and no geometry occurs, nothing is assumed of `F` or `F'` beyond additivity, and nothing of `G`
beyond exactness.

## Main results

* `…HomologyComparison.exactPostcomposeUnit_comp`: **postcomposing a comparison of the two right
  derived functors upstairs.** Composing `exactPostcomposeUnit F G RF unit` with `G` applied to
  `ν : RF ⟶ RF'` is `exactPostcomposeUnit F G RF' (unit ≫ ν)`.
* `…HomologyComparison.exactPostcomposeUnit_whiskerRight`: **pulling a degreewise prefix out.**
  If the unit handed to `exactPostcomposeUnit` is the degreewise action of `δ : F ⟶ F'` followed
  by a unit `u` for `F'`, then the result is the degreewise action of `δ` postcomposed with `G`,
  followed by `exactPostcomposeUnit F' G RF u`.
* `…HomologyComparison.exactPostcomposeUnit_precompose`: **precomposing an exact functor.** For
  `r` exact, the transformation `(r ⋙ F).mapHC ⋙ Qh ⟶ Qh ⋙ r.mapDerivedCategory ⋙ RF` built from
  `unit` by the degreewise crossing of the composite, `unit` upstairs and
  `CategoryTheory.Functor.mapDerivedCategoryFactorsh` of `r` inverted — the shape every
  `CategoryTheory.Functor.rightDerivedDesc` out of a precomposition is fed — commutes with
  postcomposing `G`: applying `exactPostcomposeUnit … G` to it gives the same transformation built
  from `exactPostcomposeUnit F G RF unit`.
* `…HomologyComparison.exactPostcomposeUnit_precompose_comp`: the same for two exact functors
  postcomposed in succession, with the result written out left-associated — the spelling a
  `rightDerivedDesc` out of a precomposition is stated at, so that no reassociation is left at the
  call site.
* `…HomologyComparison.mapHomotopyCategoryCompIso_refl_inv_app`: the comparison of homotopy
  categories attached to the identity isomorphism of a composite is the identity.

## Implementation notes

*The two identities and the identity-valued comparison.* `exactPostcomposeUnit F G RF unit` is a
comparison isomorphism of the two readings of `G` on the derived category followed by `unit`
pushed along `G`, and the comparison's first factor is
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` at `Iso.refl`, whose components are
identities. Rewriting them away with `CategoryTheory.Category.id_comp` is **refused**: the target
is then not type-correct at `implicit` transparency, because the identity's source and target are
the two definitionally equal but differently spelled readings of the degreewise composite. The
cancellation is therefore performed by a private lemma at variables, where `exact` runs at
default transparency; the same discipline `Stacks.EdgeCompat`
`.derivedHomologyComparison_preimageSectionsModelComparison` records for
`CategoryTheory.Category.comp_id`.

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe vA vB vC vD vE uA uB uC uD uE

namespace Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory C]
  {Dd : Type uD} [Category.{vD} Dd] [Abelian Dd] [HasDerivedCategory Dd]
  {Ee : Type uE} [Category.{vE} Ee] [Abelian Ee] [HasDerivedCategory Ee]

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] in
/-- **The comparison of homotopy categories attached to the identity isomorphism of a composite
is the identity.** Both sides are the quotient of an identity of complexes. -/
theorem mapHomotopyCategoryCompIso_refl_inv_app (F : A ⥤ B) [F.Additive] (G : B ⥤ C)
    [G.Additive] (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv.app K =
      𝟙 _ := by
  show (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (𝟙 _) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

/-- Cancelling a morphism known to be an identity, at variables: at the application the two
definitionally equal spellings of its source and target are crossed by `exact`, at default
transparency, instead of inside a rewrite motive. -/
private theorem id_comp_of_eq_id {D : Type*} [Category* D] {Y Z : D} {p : Y ⟶ Y}
    (hp : p = 𝟙 Y) (q : Y ⟶ Z) : p ≫ q = q := by rw [hp, Category.id_comp]

/-- Replacing the first two factors of a three-fold composite, at variables, where the
reassociation is free. -/
private theorem comp_comp_congr {D : Type*} [Category* D] {X Y Y' Z W : D} {a : X ⟶ Y}
    {b : Y ⟶ Z} {d : X ⟶ Y'} {ee : Y' ⟶ Z} (h : a ≫ b = d ≫ ee) (c : Z ⟶ W) :
    a ≫ b ≫ c = d ≫ ee ≫ c := by rw [← Category.assoc, h, Category.assoc]

/-- `Qh` sends the comparison of homotopy categories at an identity isomorphism to an identity. -/
private theorem Qh_map_compIso_refl_inv_app {A' B' C' : Type*} [Category* A']
    [Abelian A'] [Category* B'] [Abelian B'] [Category* C'] [Abelian C'] [HasDerivedCategory C']
    (F : A' ⥤ B') [F.Additive] (G : B' ⥤ C') [G.Additive]
    (K : HomotopyCategory A' (ComplexShape.up ℤ)) :
    DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv.app K) =
        𝟙 _ := DerivedCategory.Qh.map_id _

/-- **Postcomposing a comparison of the two right derived functors upstairs onto
`exactPostcomposeUnit`.** For `ν : RF ⟶ RF'` a transformation of two functors out of the derived
category of `A`, composing `exactPostcomposeUnit F G RF unit` with `G` applied to `ν` is
`exactPostcomposeUnit F G RF' (unit ≫ ν)`: the comparison isomorphism the definition carries does
not mention `RF`, and `CategoryTheory.Functor.whiskerRight` is functorial.

`RF'` is **not** assumed to be a right derived functor of anything. Nothing is assumed of `F`
beyond additivity, nothing of `G` beyond exactness. -/
theorem exactPostcomposeUnit_comp (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (RF RF' : DerivedCategory A ⥤ DerivedCategory B)
    (unit : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (ν : RF ⟶ RF') :
    exactPostcomposeUnit F G RF unit ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.whiskerRight ν G.mapDerivedCategory) =
      exactPostcomposeUnit F G RF' (unit ≫ Functor.whiskerLeft DerivedCategory.Qh ν) := by
  ext K
  simp only [exactPostcomposeUnit, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Category.assoc, Functor.map_comp]

/-- **Pulling a degreewise prefix out of `exactPostcomposeUnit`.** If the unit handed to
`exactPostcomposeUnit F G RF` is the degreewise action of `δ : F ⟶ F'` followed by a unit `u`
presenting `RF` for `F'`, then the result is the degreewise action of `δ` postcomposed with `G`,
followed by `exactPostcomposeUnit F' G RF u`.

This is the naturality of the comparison isomorphism `exactPostcomposeUnit` carries in its first
argument: the `mapHomotopyCategoryCompIso` factor is an identity at either functor by
`mapHomotopyCategoryCompIso_refl_inv_app`, and what is left is the naturality of
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` of `G` at the degreewise action of `δ`,
together with the fact that `G` applied degreewise to that action is the degreewise action of `δ`
postcomposed with `G` — which holds by definition.

Nothing is assumed of `F` or `F'` beyond additivity, nothing of `G` beyond exactness, and `RF` is
not assumed to be a right derived functor of anything. -/
theorem exactPostcomposeUnit_whiskerRight (F F' : A ⥤ B) [F.Additive] [F'.Additive]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (RF : DerivedCategory A ⥤ DerivedCategory B) (δ : F ⟶ F')
    (u : F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) :
    exactPostcomposeUnit F G RF
        (Functor.whiskerRight (NatTrans.mapHomotopyCategory δ (ComplexShape.up ℤ))
          DerivedCategory.Qh ≫ u) =
      Functor.whiskerRight
          (NatTrans.mapHomotopyCategory (Functor.whiskerRight δ G) (ComplexShape.up ℤ))
          DerivedCategory.Qh ≫
        exactPostcomposeUnit F' G RF u := by
  ext K
  have hnat := G.mapDerivedCategoryFactorsh.inv.naturality
    ((NatTrans.mapHomotopyCategory δ (ComplexShape.up ℤ)).app K)
  simp only [Functor.comp_map] at hnat
  have hnat2 : G.mapDerivedCategoryFactorsh.inv.app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      G.mapDerivedCategory.map (DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory δ (ComplexShape.up ℤ)).app K)) =
    DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory (Functor.whiskerRight δ G)
        (ComplexShape.up ℤ)).app K) ≫
      G.mapDerivedCategoryFactorsh.inv.app
        ((F'.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) := hnat.symm
  simp only [exactPostcomposeUnit, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Category.assoc, Functor.map_comp]
  exact (id_comp_of_eq_id (Qh_map_compIso_refl_inv_app _ _ _) _).trans
    ((comp_comp_congr hnat2 _).trans
      (congrArg _ (id_comp_of_eq_id (Qh_map_compIso_refl_inv_app _ _ _) _).symm))

/-- Four morphisms known to be identities cancelled out of two four-fold composites, at
variables: at the application the definitionally equal spellings of their sources and targets are
crossed by `exact`, at default transparency, instead of inside a rewrite motive. -/
private theorem glue_two_sides {E : Type*} [Category* E] {W X T : E} {i₁ : W ⟶ W}
    (h₁ : i₁ = 𝟙 W) {m : W ⟶ X} {i₂ : X ⟶ X} (h₂ : i₂ = 𝟙 X) (t : X ⟶ T) {j₁ j₂ : W ⟶ W}
    (k₁ : j₁ = 𝟙 W) (k₂ : j₂ = 𝟙 W) :
    i₁ ≫ m ≫ i₂ ≫ t = j₁ ≫ j₂ ≫ m ≫ t := by
  rw [h₁, h₂, k₁, k₂, Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp]

/-- **Precomposing an exact functor, on `exactPostcomposeUnit`.** Let `r` be exact, `F` additive
with a right derived functor `RF` presented by `unit`, and `G` exact. Both
`r.mapDerivedCategory ⋙ RF` and the transformation

> `(r ⋙ F).mapHC ⋙ Qh ⟶ Qh ⋙ r.mapDerivedCategory ⋙ RF`

built from `unit` by the degreewise crossing of the composite, `unit` upstairs and
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` of `r` inverted — the shape every
`CategoryTheory.Functor.rightDerivedDesc` out of a precomposition in this subtree is fed — may be
postcomposed with `G` in either order: applying `exactPostcomposeUnit … G` to that transformation
is the same transformation built from `exactPostcomposeUnit F G RF unit`.

Both sides are the same four factors in the same order. They differ only by four components of
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` at identity isomorphisms, which are
identities by `mapHomotopyCategoryCompIso_refl_inv_app`, and by the distribution of `G` over a
composite. Nothing is assumed of `r` or `G` beyond exactness, nothing of `F` beyond additivity,
and `RF` is not assumed to be a right derived functor of anything. -/
theorem exactPostcomposeUnit_precompose (r : A ⥤ B) [r.Additive] [PreservesFiniteLimits r]
    [PreservesFiniteColimits r] (F : B ⥤ C) [F.Additive] (G : C ⥤ Dd) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (RF : DerivedCategory B ⥤ DerivedCategory C)
    (unit : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) :
    exactPostcomposeUnit (r ⋙ F) G (r.mapDerivedCategory ⋙ RF)
        (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (r ⋙ F))
              (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
          Functor.whiskerLeft (r.mapHomotopyCategory (ComplexShape.up ℤ)) unit ≫
            Functor.whiskerRight r.mapDerivedCategoryFactorsh.inv RF) =
      Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (r ⋙ F ⋙ G))
            (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
        Functor.whiskerLeft (r.mapHomotopyCategory (ComplexShape.up ℤ))
            (exactPostcomposeUnit F G RF unit) ≫
          Functor.whiskerRight r.mapDerivedCategoryFactorsh.inv (RF ⋙ G.mapDerivedCategory) := by
  ext K
  have h₂ := (congrArg G.mapDerivedCategory.map
    (Qh_map_compIso_refl_inv_app r F K)).trans (G.mapDerivedCategory.map_id _)
  simp only [exactPostcomposeUnit, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Category.assoc, Functor.map_comp]
  exact glue_two_sides (Qh_map_compIso_refl_inv_app _ _ _) h₂ _
    (Qh_map_compIso_refl_inv_app _ _ _)
    (Qh_map_compIso_refl_inv_app _ _ _)

/-- **The same twice over, with the result written out left-associated.** For `r` and two exact
functors `G`, `G'` in succession, applying `exactPostcomposeUnit … G'` to
`exactPostcomposeUnit … G` applied to the transformation built from `unit` is the transformation
built the same way from `exactPostcomposeUnit F G RF unit` — the single postcomposition by the
composite — and its leading comparison is spelled as the two-step splitting of the two exact
factors off the homotopy category.

Two applications of `exactPostcomposeUnit_precompose` and the distribution of
`CategoryTheory.Functor.whiskerLeft` over a composite; the left-associated spelling is the one a
`CategoryTheory.Functor.rightDerivedDesc` out of a precomposition is written at, so that no
reassociation is left at the call site. -/
theorem exactPostcomposeUnit_precompose_comp (r : A ⥤ B) [r.Additive] [PreservesFiniteLimits r]
    [PreservesFiniteColimits r] (F : B ⥤ C) [F.Additive] (G : C ⥤ Dd) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (G' : Dd ⥤ Ee) [G'.Additive]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (RF : DerivedCategory B ⥤ DerivedCategory C)
    (unit : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) :
    exactPostcomposeUnit ((r ⋙ F) ⋙ G) G'
        ((r.mapDerivedCategory ⋙ RF) ⋙ G.mapDerivedCategory)
        (exactPostcomposeUnit (r ⋙ F) G (r.mapDerivedCategory ⋙ RF)
          (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (r ⋙ F))
                (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
            Functor.whiskerLeft (r.mapHomotopyCategory (ComplexShape.up ℤ)) unit ≫
              Functor.whiskerRight r.mapDerivedCategoryFactorsh.inv RF)) =
      (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
              (Iso.refl (r ⋙ (F ⋙ G) ⋙ G')) (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
            Functor.whiskerLeft (r.mapHomotopyCategory (ComplexShape.up ℤ))
              (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
                    (Iso.refl ((F ⋙ G) ⋙ G')) (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
                Functor.whiskerLeft ((F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ))
                  G'.mapDerivedCategoryFactorsh.inv)) ≫
        Functor.whiskerLeft (r.mapHomotopyCategory (ComplexShape.up ℤ))
            (Functor.whiskerRight (exactPostcomposeUnit F G RF unit) G'.mapDerivedCategory) ≫
          Functor.whiskerRight r.mapDerivedCategoryFactorsh.inv
            ((RF ⋙ G.mapDerivedCategory) ⋙ G'.mapDerivedCategory) := by
  refine ((congrArg (exactPostcomposeUnit ((r ⋙ F) ⋙ G) G'
        ((r.mapDerivedCategory ⋙ RF) ⋙ G.mapDerivedCategory))
      (exactPostcomposeUnit_precompose r F G RF unit)).trans
    ((exactPostcomposeUnit_precompose r (F ⋙ G) G' (RF ⋙ G.mapDerivedCategory)
        (exactPostcomposeUnit F G RF unit)).trans ?_))
  simp only [exactPostcomposeUnit, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_comp, Category.assoc]

end Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

end
