module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedDescAlongPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedPushforwardStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleUnboundedDerivations

/-!
# The specialization map and the maps to the strict henselization and the fibre

Let `f : X ⟶ S` be a morphism of schemes, let `K` be an object of the unbounded derived category
`D(X_étale)`, let `s` be a geometric point of `S` and let `t` be a geometric point of the strict
henselization `Spec(𝒪^{sh}_{S,s})`, with `c` the specialization morphism of strict henselizations
of Stacks 0GJ4. The square

```
(Rf_*K)_s -----> RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), K)
   | sp                        | (id_X × c)⁻¹
   v                           v
(Rf_*K)_{t ≫ p} -> RΓ(X ×_S Spec(𝒪^{sh}_{S,t ≫ p}), K)
```

commutes, the horizontal arrows being the maps of Stacks 0GIX from the stalk of the derived
direct image. This is the content of Stacks 0GJ9: the source's diagram has a third column, the
cohomology of `K` on the two geometric fibres, but states that in general no vertical map exists
between those, so the left square above is the whole commutativity assertion.

Transposed — `sp` horizontal and the maps of Stacks 0GIX vertical — the same square is the
diagram of Stacks 0GJ8, whose two vertical arrows are the identifications of Theorem 03Q9,
available there because the morphism is quasi-compact and quasi-separated and `K` is bounded
below. The commutativity is the assertion of both tags, and it is proved below with no
hypothesis on `f` or on `K`, which is the generality Stacks 0GJ9 states it in.

## Main results

* `derivedPushforwardStalkToStrictHenselizationSections_comp_sectionsSpecialization`, in
  `AlgebraicGeometry` — **[Stacks, Tag 0GJ9]** the square above.
* `AlgebraicGeometry.specializationStalk_comp_derivedPushforwardStalkToStrictHenselizationSections`
  — **[Stacks, Tag 0GJ8]** the same square, read with `sp` on top.

## The square has no hypotheses

The three `CategoryTheory.Functor.HasRightDerivedFunctor` arguments below, which are what makes
`Rf_*` and the two `RΓ`s exist on the unbounded derived categories, are instances of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmallEtaleUnboundedDerivations.lean`: abelian
sheaves on a small étale site are Grothendieck abelian, so Stacks 079P gives K-injective
resolutions of unbounded complexes and Stacks 070K the derivations. The square therefore holds
at every big étale site, every morphism of schemes and every pair of geometric points, with
nothing assumed.

## Implementation notes

Both sides of the square are transformations out of `smallEtaleDerivedPushforwardAb f ⋙
smallEtaleDerivedStalkAb s.hom`, which is a right derived functor, so
`CategoryTheory.Functor.rightDerived_ext` reduces the square to the corresponding square on the
comparisons which `AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections`
descends. That square is `AlgebraicGeometry.unitSquare`, and its core is an instance of the
generic `Stacks.DerivedFunctor.exactDerivedDescUnit_comp_restriction`: a commuting square of
transformations out of additive functors, together with right derived functors of the two targets
and a restriction between them, yields a commuting square after descent. The input on abelian
sheaves is `AlgebraicGeometry.sheafSquare`, which is Stacks 0GJ8's square
`pushforwardStalkToStrictHenselizationSectionsAb_comp_sectionsRestrictionAb` with the restriction
of sections along `id_X × c` written out.

*The cost problem, and what resolves it.* A category of abelian sheaves carries two
reducibly-unequal preadditive structures: the one registered for it directly, as a full
subcategory of presheaves, and the one read off its abelian structure. Instance synthesis at a
concrete sheaf category finds the first, while every generic lemma about additive functors
between abelian categories carries the second, and reconciling the two forces the kernel to
unfold two preadditive structures on a category of abelian sheaves — which, at the sheaf
categories of the base changes to the two strict henselizations, exceeds the kernel's heartbeat
allowance. Raising the priority of `CategoryTheory.Abelian.toPreadditive` locally makes the
statements of this file agree with the generic lemmas on the nose, and the one existing statement
that must still be converted,
`Stacks.EtaleCohomology.smallEtaleDerivedPullbackAbCompIsoQhLift_hom_app`, is converted at an
arbitrary triple of schemes rather than at those sheaf categories, where the terms are far
larger; that is
`AlgebraicGeometry.smallEtaleDerivedPullbackAbCompIsoQhLiftHomApp`. Without both of those the
single application of the generic chase lemma does not type-check within budget, and neither
splitting it into concrete steps nor restating it helps, because each concrete statement pays the
same reconciliation.

*Why the `At` aliases exist.* The library carries two spellings of the specialized point: the
composite morphism `t.hom ≫ p`, used by Stacks 0GJ4 and 0GJ8, and the geometric point `t.map p`,
used by Stacks 0GIX, whose maps are indexed by a `AlgebraicGeometry.GeometricPoint`. The `…At`
aliases below are the library's maps of the first spelling restated in the second, presented through
`AlgebraicGeometry.specializedGeometricPoint`, with the derivation instances of
`AlgebraicGeometry.strictHenselizationSectionsSpecializationAt` supplied positionally because
instance synthesis cannot see through that presentation. Each alias comes with a stated equality
to its original, so faithfulness against the registry rests on those equalities rather than on a
definitional unfolding the reader must take on trust. The maps of Stacks 0GIX need no alias: they
parameterize their instance arguments by their own point argument, so applying them at the
specialized point already yields that spelling.

## References

* [Stacks Project, Tag 0GJ9](https://stacks.math.columbia.edu/tag/0GJ9)
* [Stacks Project, Tag 0GIX](https://stacks.math.columbia.edu/tag/0GIX)
* [Stacks Project, Tag 0GJ4](https://stacks.math.columbia.edu/tag/0GJ4)
* [Stacks Project, Tag 0GJ8](https://stacks.math.columbia.edu/tag/0GJ8)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.EtaleCohomology

universe u

namespace Stacks.DerivedFunctor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A₁ : Type u₁} [Category.{v₁} A₁] [Abelian A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [Abelian A₂]
  {A₃ : Type u₃} [Category.{v₃} A₃] [Abelian A₃]
  {A₄ : Type u₄} [Category.{v₄} A₄] [Abelian A₄]

/-- The comparison of homotopy categories attached to the identity isomorphism of a composite of
additive functors is the identity: it is the quotient of an identity. -/
theorem mapHomotopyCategoryCompIso_refl_hom_app (G : A₂ ⥤ A₃) (H : A₃ ⥤ A₄) [G.Additive]
    [H.Additive] (Y : HomotopyCategory A₂ (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ H)) (ComplexShape.up ℤ)).hom.app Y =
      𝟙 _ := by
  show (HomotopyCategory.quotient A₄ (ComplexShape.up ℤ)).map (𝟙 _) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

/-- The degreewise action on homotopy categories of a transformation whiskered by a functor is
the action of the transformation itself, at the image of the complex. -/
theorem mapHomotopyCategory_whiskerLeft_app (P : A₁ ⥤ A₂) [P.Additive] {G H : A₂ ⥤ A₃}
    [G.Additive] [H.Additive] (α : G ⟶ H)
    (J : HomotopyCategory A₁ (ComplexShape.up ℤ)) :
    (NatTrans.mapHomotopyCategory (Functor.whiskerLeft P α) (ComplexShape.up ℤ)).app J =
      (NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)).app
        ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) :=
  rfl

/-- The degreewise action of a transformation `F ⟶ G ⋙ H` precomposed with a transformation of
the source functor is the action of that transformation, followed by the action of the rest. -/
theorem mapHomotopyCategoryOfComp_comp_left (F F' : A₁ ⥤ A₃) [F.Additive] [F'.Additive]
    (G : A₁ ⥤ A₂) [G.Additive] (H : A₂ ⥤ A₃) [H.Additive] (σ : F ⟶ F') (τ : F' ⟶ G ⋙ H)
    (J : HomotopyCategory A₁ (ComplexShape.up ℤ)) :
    (mapHomotopyCategoryOfComp F G H (σ ≫ τ)).app J =
      (NatTrans.mapHomotopyCategory σ (ComplexShape.up ℤ)).app J ≫
        (mapHomotopyCategoryOfComp F' G H τ).app J := by
  rw [mapHomotopyCategoryOfComp_app, mapHomotopyCategoryOfComp_app]
  refine Eq.trans (congrArg (HomotopyCategory.quotient A₃ (ComplexShape.up ℤ)).map
      (?_ : (NatTrans.mapHomologicalComplex (σ ≫ τ) (ComplexShape.up ℤ)).app J.as =
        (NatTrans.mapHomologicalComplex σ (ComplexShape.up ℤ)).app J.as ≫
          (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app J.as))
    ((HomotopyCategory.quotient A₃ (ComplexShape.up ℤ)).map_comp _ _)
  exact HomologicalComplex.hom_ext _ _ fun i => rfl

/-- **A commuting square of transformations acts degreewise on homotopy categories.** Let
`τ : F ⟶ G ⋙ H` and `τ' : F' ⟶ G' ⋙ H'` be transformations out of additive functors, let
`σ : F ⟶ F'` and `ρ : H ⟶ P ⋙ H'`, and let `e : G ⋙ P ≅ G'`. If the square they form commutes,
then so does the square of their degreewise actions on homotopy categories. -/
theorem mapHomotopyCategoryOfComp_square (F F' : A₁ ⥤ A₄) [F.Additive] [F'.Additive]
    (G : A₁ ⥤ A₂) [G.Additive] (H : A₂ ⥤ A₄) [H.Additive] (P : A₂ ⥤ A₃) [P.Additive]
    (H' : A₃ ⥤ A₄) [H'.Additive] (G' : A₁ ⥤ A₃) [G'.Additive] (σ : F ⟶ F') (τ : F ⟶ G ⋙ H)
    (τ' : F' ⟶ G' ⋙ H') (ρ : H ⟶ P ⋙ H') (e : G ⋙ P ≅ G')
    (hsq : τ ≫ Functor.whiskerLeft G ρ ≫ (Functor.associator G P H').inv ≫
      Functor.whiskerRight e.hom H' = σ ≫ τ')
    (J : HomotopyCategory A₁ (ComplexShape.up ℤ)) :
    (mapHomotopyCategoryOfComp F G H τ).app J ≫
        (mapHomotopyCategoryOfComp H P H' ρ).app
            ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
          (H'.mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app J) =
      (NatTrans.mapHomotopyCategory σ (ComplexShape.up ℤ)).app J ≫
        (mapHomotopyCategoryOfComp F' G' H' τ').app J := by
  rw [mapHomotopyCategoryOfComp_trans F G H P H' G' τ ρ e J, hsq,
    mapHomotopyCategoryOfComp_comp_left F F' G' H' σ τ' J]

universe v₀ u₀ w₀ w₁ w₂ w₃ w₄

/-- On the unbounded derived category, the comparison of homotopy categories attached to the
identity isomorphism of a composite of additive functors cancels: it is an identity. -/
theorem Qh_map_mapHomotopyCategoryCompIso_refl_hom_app_comp [HasDerivedCategory.{w₄} A₄]
    (G : A₂ ⥤ A₃) (H : A₃ ⥤ A₄) [G.Additive] [H.Additive]
    (Y : HomotopyCategory A₂ (ComplexShape.up ℤ)) {Z : DerivedCategory A₄}
    (g : DerivedCategory.Qh.obj
      (((G ⋙ H).mapHomotopyCategory (ComplexShape.up ℤ)).obj Y) ⟶ Z) :
    DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ H))
        (ComplexShape.up ℤ)).hom.app Y) ≫ g = g := by
  have h : DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ H))
      (ComplexShape.up ℤ)).hom.app Y) = 𝟙 _ :=
    (congrArg DerivedCategory.Qh.map
      (mapHomotopyCategoryCompIso_refl_hom_app G H Y)).trans
        (CategoryTheory.Functor.map_id _ _)
  rw [h]
  exact Category.id_comp g

/-- **The prefix of a descended comparison, on a complex.** The three bookkeeping factors which
carry a transformation `U` out of the degreewise action of `Φ ⋙ St` to one out of
`Φ_h ⋙ Qh ⋙ St_D` contribute, on a complex, only the identification of the two actions of `St`.

This is the junction at which the assembly of the square of Stacks 0GJ9 is split in two, so that
the kernel checks the two halves as separate declarations. -/
theorem derivedStalkDescUnit_app [HasDerivedCategory.{w₁} A₁] [HasDerivedCategory.{w₄} A₄]
    {A₀ : Type u₀} [Category.{v₀} A₀] [Abelian A₀] [HasDerivedCategory.{w₀} A₀] (Φ : A₀ ⥤ A₁)
    [Φ.Additive] (St : A₁ ⥤ A₄) [St.Additive] [PreservesFiniteLimits St]
    [PreservesFiniteColimits St] (V : DerivedCategory A₀ ⥤ DerivedCategory A₄)
    (U : (Φ ⋙ St).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ V) (J : HomotopyCategory A₀ (ComplexShape.up ℤ)) :
    (Functor.whiskerLeft (Φ.mapHomotopyCategory (ComplexShape.up ℤ))
          St.mapDerivedCategoryFactorsh.hom ≫
        (Functor.associator (Φ.mapHomotopyCategory (ComplexShape.up ℤ))
          (St.mapHomotopyCategory (ComplexShape.up ℤ)) DerivedCategory.Qh).inv ≫
        Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (Φ ⋙ St))
          (ComplexShape.up ℤ)).hom DerivedCategory.Qh ≫ U).app J =
      St.mapDerivedCategoryFactorsh.hom.app
          ((Φ.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫ U.app J := by
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp]
  rw [Qh_map_mapHomotopyCategoryCompIso_refl_hom_app_comp]

/-- **A commuting square of transformations out of additive functors, after descent.** With the
data of `Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_square`, right derived functors `RH` and
`RH'` of `H` and `H'` with units `η` and `η'`, a transformation `Res : RH ⟶ P_D ⋙ RH'` descending
`ρ`, and an identification `χ` of `G_D ⋙ P_D` with `G'_D` lifting `e` through
`DerivedCategory.Qh`, the comparison on the homotopy category induced by `τ` and `η`, followed by
`Res` and `χ`, is the degreewise action of `σ` followed by the comparison induced by `τ'` and
`η'`. -/
theorem exactDerivedDescUnit_comp_restriction
    [HasDerivedCategory.{w₁} A₁] [HasDerivedCategory.{w₂} A₂] [HasDerivedCategory.{w₃} A₃]
    [HasDerivedCategory.{w₄} A₄] {F F' : A₁ ⥤ A₄} [F.Additive] [F'.Additive] {G : A₁ ⥤ A₂}
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] {H : A₂ ⥤ A₄}
    [H.Additive] {P : A₂ ⥤ A₃} [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    {H' : A₃ ⥤ A₄} [H'.Additive] {G' : A₁ ⥤ A₃} [G'.Additive] [PreservesFiniteLimits G']
    [PreservesFiniteColimits G'] {RH : DerivedCategory A₂ ⥤ DerivedCategory A₄}
    {η : H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RH} {RH' : DerivedCategory A₃ ⥤ DerivedCategory A₄}
    {η' : H'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RH'} {σ : F ⟶ F'} {τ : F ⟶ G ⋙ H} {τ' : F' ⟶ G' ⋙ H'}
    {ρ : H ⟶ P ⋙ H'} {e : G ⋙ P ≅ G'}
    {χ : G.mapDerivedCategory ⋙ P.mapDerivedCategory ≅ G'.mapDerivedCategory}
    {Res : RH ⟶ P.mapDerivedCategory ⋙ RH'}
    (hsq : τ ≫ Functor.whiskerLeft G ρ ≫ (Functor.associator G P H').inv ≫
      Functor.whiskerRight e.hom H' = σ ≫ τ')
    (hRes : ∀ Y, η.app Y ≫ Res.app (DerivedCategory.Qh.obj Y) =
      DerivedCategory.Qh.map ((mapHomotopyCategoryOfComp H P H' ρ).app Y) ≫
        η'.app ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj Y) ≫
          RH'.map (P.mapDerivedCategoryFactorsh.inv.app Y))
    (hχ : ∀ Z, χ.hom.app (DerivedCategory.Qh.obj Z) =
      P.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app Z) ≫
        P.mapDerivedCategoryFactorsh.hom.app
            ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj Z) ≫
          DerivedCategory.Qh.map
              ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app Z) ≫
            G'.mapDerivedCategoryFactorsh.inv.app Z)
    (J : HomotopyCategory A₁ (ComplexShape.up ℤ)) :
    (exactDerivedDescUnit F G H RH η τ).app J ≫
        Res.app (G.mapDerivedCategory.obj (DerivedCategory.Qh.obj J)) ≫
          RH'.map (χ.hom.app (DerivedCategory.Qh.obj J)) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory σ (ComplexShape.up ℤ)).app J) ≫
        (exactDerivedDescUnit F' G' H' RH' η' τ').app J := by
  rw [exactDerivedDescUnit_app, exactDerivedDescUnit_app, hχ]
  simp only [Functor.map_comp, Category.assoc]
  have hnat : RH.map (G.mapDerivedCategoryFactorsh.inv.app J) ≫
        Res.app (G.mapDerivedCategory.obj (DerivedCategory.Qh.obj J)) =
      Res.app (DerivedCategory.Qh.obj
          ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) ≫
        RH'.map (P.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.inv.app J)) :=
    Res.naturality (G.mapDerivedCategoryFactorsh.inv.app J)
  rw [reassoc_of% hnat,
    reassoc_of% (hRes ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj J))]
  have hc1 : RH'.map (P.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.inv.app J)) ≫
        RH'.map (P.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app J)) = 𝟙 _ :=
    (RH'.mapIso (P.mapDerivedCategory.mapIso
      (G.mapDerivedCategoryFactorsh.app J))).inv_hom_id
  have hc2 : RH'.map (P.mapDerivedCategoryFactorsh.inv.app
          ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) ≫
        RH'.map (P.mapDerivedCategoryFactorsh.hom.app
          ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) = 𝟙 _ :=
    (RH'.mapIso (P.mapDerivedCategoryFactorsh.app
      ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj J))).inv_hom_id
  have hη : DerivedCategory.Qh.map ((H'.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app J)) ≫
        η'.app ((G'.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) =
      η'.app ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) ≫
        RH'.map (DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app J)) :=
    η'.naturality ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app J)
  have hbig : ((mapHomotopyCategoryOfComp F G H τ).app J ≫
        (mapHomotopyCategoryOfComp H P H' ρ).app
          ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) ≫
        (H'.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app J) =
      (NatTrans.mapHomotopyCategory σ (ComplexShape.up ℤ)).app J ≫
        (mapHomotopyCategoryOfComp F' G' H' τ').app J :=
    (Category.assoc _ _ _).trans
      (mapHomotopyCategoryOfComp_square F F' G H P H' G' σ τ τ' ρ e hsq J)
  rw [reassoc_of% hc1, reassoc_of% hc2, ← reassoc_of% hη, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, hbig, Functor.map_comp, Category.assoc]

/-- **The square of a specialization of stalks against a restriction of derived sections.** Let
`Φ` be additive, let `St, St'` be exact with a transformation `spSheaf : St ⟶ St'` whose action on
unbounded derived categories is `spD`, and let `τ : Φ ⋙ St ⟶ G ⋙ H`, `τ' : Φ ⋙ St' ⟶ G' ⋙ H'`,
`ρ : H ⟶ P ⋙ H'` and `e : G ⋙ P ≅ G'` form a commuting square. Then the comparison on homotopy
categories descending `τ`, followed by the restriction built from `Res` and `χ`, is `spD`
followed by the comparison descending `τ'`. -/
theorem derivedStalkDescUnit_comp_restriction {A₀ : Type u₀} [Category.{v₀} A₀] [Abelian A₀]
    [HasDerivedCategory.{w₀} A₀] [HasDerivedCategory.{w₁} A₁] [HasDerivedCategory.{w₂} A₂]
    [HasDerivedCategory.{w₃} A₃]
    [HasDerivedCategory.{w₄} A₄] (Φ : A₀ ⥤ A₁) [Φ.Additive] (St St' : A₁ ⥤ A₄) [St.Additive]
    [St'.Additive] [PreservesFiniteLimits St] [PreservesFiniteColimits St]
    [PreservesFiniteLimits St'] [PreservesFiniteColimits St'] {G : A₀ ⥤ A₂} [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] {H : A₂ ⥤ A₄} [H.Additive]
    {P : A₂ ⥤ A₃} [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    {H' : A₃ ⥤ A₄} [H'.Additive] {G' : A₀ ⥤ A₃} [G'.Additive] [PreservesFiniteLimits G']
    [PreservesFiniteColimits G'] {RH : DerivedCategory A₂ ⥤ DerivedCategory A₄}
    {η : H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RH} {RH' : DerivedCategory A₃ ⥤ DerivedCategory A₄}
    {η' : H'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RH'} {spSheaf : St ⟶ St'} {τ : Φ ⋙ St ⟶ G ⋙ H}
    {τ' : Φ ⋙ St' ⟶ G' ⋙ H'} {ρ : H ⟶ P ⋙ H'} {e : G ⋙ P ≅ G'}
    {χ : G.mapDerivedCategory ⋙ P.mapDerivedCategory ≅ G'.mapDerivedCategory}
    {Res : RH ⟶ P.mapDerivedCategory ⋙ RH'}
    {spD : St.mapDerivedCategory ⟶ St'.mapDerivedCategory}
    (hsq : τ ≫ Functor.whiskerLeft G ρ ≫ (Functor.associator G P H').inv ≫
      Functor.whiskerRight e.hom H' = Functor.whiskerLeft Φ spSheaf ≫ τ')
    (hRes : ∀ Y, η.app Y ≫ Res.app (DerivedCategory.Qh.obj Y) =
      DerivedCategory.Qh.map ((mapHomotopyCategoryOfComp H P H' ρ).app Y) ≫
        η'.app ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj Y) ≫
          RH'.map (P.mapDerivedCategoryFactorsh.inv.app Y))
    (hχ : ∀ Z, χ.hom.app (DerivedCategory.Qh.obj Z) =
      P.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app Z) ≫
        P.mapDerivedCategoryFactorsh.hom.app
            ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj Z) ≫
          DerivedCategory.Qh.map
              ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app Z) ≫
            G'.mapDerivedCategoryFactorsh.inv.app Z)
    (hsp : ∀ W, spD.app (DerivedCategory.Qh.obj W) =
      St.mapDerivedCategoryFactorsh.hom.app W ≫
        DerivedCategory.Qh.map
            ((NatTrans.mapHomotopyCategory spSheaf (ComplexShape.up ℤ)).app W) ≫
          St'.mapDerivedCategoryFactorsh.inv.app W)
    (J : HomotopyCategory A₀ (ComplexShape.up ℤ)) :
    (Functor.whiskerLeft (Φ.mapHomotopyCategory (ComplexShape.up ℤ))
            St.mapDerivedCategoryFactorsh.hom ≫
          (Functor.associator (Φ.mapHomotopyCategory (ComplexShape.up ℤ))
            (St.mapHomotopyCategory (ComplexShape.up ℤ)) DerivedCategory.Qh).inv ≫
          Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (Φ ⋙ St))
            (ComplexShape.up ℤ)).hom DerivedCategory.Qh ≫
          exactDerivedDescUnit (Φ ⋙ St) G H RH η τ).app J ≫
        (Functor.whiskerLeft G.mapDerivedCategory Res ≫
          (Functor.associator G.mapDerivedCategory P.mapDerivedCategory RH').inv ≫
          Functor.whiskerRight χ.hom RH').app (DerivedCategory.Qh.obj J) =
      spD.app (DerivedCategory.Qh.obj
          ((Φ.mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) ≫
        (Functor.whiskerLeft (Φ.mapHomotopyCategory (ComplexShape.up ℤ))
            St'.mapDerivedCategoryFactorsh.hom ≫
          (Functor.associator (Φ.mapHomotopyCategory (ComplexShape.up ℤ))
            (St'.mapHomotopyCategory (ComplexShape.up ℤ)) DerivedCategory.Qh).inv ≫
          Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (Φ ⋙ St'))
            (ComplexShape.up ℤ)).hom DerivedCategory.Qh ≫
          exactDerivedDescUnit (Φ ⋙ St') G' H' RH' η' τ').app J := by
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc, hsp]
  rw [exactDerivedDescUnit_comp_restriction hsq hRes hχ J,
    mapHomotopyCategory_whiskerLeft_app,
    Qh_map_mapHomotopyCategoryCompIso_refl_hom_app_comp,
    Qh_map_mapHomotopyCategoryCompIso_refl_hom_app_comp]
  exact congrArg (fun y => St.mapDerivedCategoryFactorsh.hom.app
        ((Φ.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory spSheaf (ComplexShape.up ℤ)).app
        ((Φ.mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) ≫ y)
    (Iso.inv_hom_id_app_assoc St'.mapDerivedCategoryFactorsh
      ((Φ.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) _).symm

end Stacks.DerivedFunctor

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/- The preadditive structure on a category of abelian sheaves is registered directly, as that of
a full subcategory of presheaves, and is also derivable from the abelian structure. The two are
definitionally equal but not syntactically so, and every generic lemma about additive functors
between abelian categories carries the second spelling. Reading it off the abelian structure here
makes the statements of this file agree with those lemmas on the nose; the one place where the
existing vocabulary must be converted is
`AlgebraicGeometry.smallEtaleDerivedPullbackAbCompIsoQhLiftHomApp`, where the conversion is paid
once, at an arbitrary pair of schemes, where the terms involved are small. -/
attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive

/-! ### The specialized geometric point, and the existing data read at it -/

section PointAliases

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))

/-- The geometric point `t ≫ p` of `S` attached to a geometric point `t` of the strict
henselization of `S` at `s`, presented as a `AlgebraicGeometry.GeometricPoint` rather than as a
morphism out of the spectrum of a separably closed field.

The maps of Stacks 0GIX are indexed by a geometric point, so this is the spelling in which they
can be formed at the specialized point, whereas Stacks 0GJ4 and 0GJ8 index the stalk there by
the composite morphism `t.hom ≫ p`. The two agree definitionally; the aliases below are the
original maps restated in this spelling, each with a stated equality to its original. -/
def specializedGeometricPoint : GeometricPoint S :=
  t.map (strictHenselizationToBase B S hS s)

/-- The specialization map `sp` on stalks of abelian sheaves, with the stalk at the specialized
point indexed by `AlgebraicGeometry.specializedGeometricPoint`.

This aliases `AlgebraicGeometry.smallEtaleSpecializationStalkAb`, whose target is the stalk at
the composite morphism `t.hom ≫ p`; the two types are definitionally equal, and
`AlgebraicGeometry.smallEtaleSpecializationStalkAbAt_eq` records the identity. -/
def smallEtaleSpecializationStalkAbAt :
    smallEtaleStalkAb s.hom ⟶
      smallEtaleStalkAb (specializedGeometricPoint B S hS s t).hom :=
  smallEtaleSpecializationStalkAb B S hS s t

/-- The alias of the specialization map on stalks is the original specialization map. -/
theorem smallEtaleSpecializationStalkAbAt_eq :
    smallEtaleSpecializationStalkAbAt B S hS s t = smallEtaleSpecializationStalkAb B S hS s t :=
  rfl

/-- The specialization map `sp` on derived stalks, with the stalk at the specialized point
indexed by `AlgebraicGeometry.specializedGeometricPoint`.

This aliases `AlgebraicGeometry.smallEtaleDerivedSpecializationStalkAb`, whose target is the
derived stalk at the composite morphism `t.hom ≫ p`; the two types are definitionally equal, and
`AlgebraicGeometry.smallEtaleDerivedSpecializationStalkAbAt_eq` records the identity. -/
def smallEtaleDerivedSpecializationStalkAbAt :
    smallEtaleDerivedStalkAb s.hom ⟶
      smallEtaleDerivedStalkAb (specializedGeometricPoint B S hS s t).hom :=
  smallEtaleDerivedSpecializationStalkAb B S hS s t

/-- The alias of the specialization map on derived stalks is the original specialization map. -/
theorem smallEtaleDerivedSpecializationStalkAbAt_eq :
    smallEtaleDerivedSpecializationStalkAbAt B S hS s t =
      smallEtaleDerivedSpecializationStalkAb B S hS s t :=
  rfl

/-- On every complex, the alias of the specialization map on derived stalks is the degreewise
specialization map, read through the identifications of the degreewise actions of the two stalk
functors with their actions on derived categories. This is
`AlgebraicGeometry.smallEtaleDerivedSpecializationStalkAb_app` with every stalk index written in
the spelling of `AlgebraicGeometry.specializedGeometricPoint`, which is where the conversion
between the two spellings is paid. -/
theorem smallEtaleDerivedSpecializationStalkAbAt_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology S) Ab.{u + 1}) (.up ℤ)) :
    (smallEtaleDerivedSpecializationStalkAbAt B S hS s t).app (DerivedCategory.Qh.obj J) =
      (smallEtaleStalkAb s.hom).mapDerivedCategoryFactorsh.hom.app J ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
          (smallEtaleSpecializationStalkAbAt B S hS s t) (.up ℤ)).app J) ≫
          (smallEtaleStalkAb
            (specializedGeometricPoint B S hS s t).hom).mapDerivedCategoryFactorsh.inv.app J :=
  smallEtaleDerivedSpecializationStalkAb_app B S hS s t J

end PointAliases

section MapAliases

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))

/-- The morphism `id_X × c` of base changes, with the second base change indexed by
`AlgebraicGeometry.specializedGeometricPoint`.

This aliases `AlgebraicGeometry.strictHenselizationBaseChangeSpecializationMap`, whose source is
the base change at `t.map p`; the two types are definitionally equal, and
`AlgebraicGeometry.strictHenselizationBaseChangeSpecializationMapAt_eq` records the identity. -/
def strictHenselizationBaseChangeSpecializationMapAt :
    strictHenselizationBaseChange B hS f (specializedGeometricPoint B S hS s t) ⟶
      strictHenselizationBaseChange B hS f s :=
  strictHenselizationBaseChangeSpecializationMap B hS f s t

/-- The alias of the morphism `id_X × c` is the original morphism. -/
theorem strictHenselizationBaseChangeSpecializationMapAt_eq :
    strictHenselizationBaseChangeSpecializationMapAt B hS f s t =
      strictHenselizationBaseChangeSpecializationMap B hS f s t :=
  rfl

/-- The identification of the composite of the two inverse images with the inverse image along
the projection of the second base change, with that base change indexed by
`AlgebraicGeometry.specializedGeometricPoint`.

This aliases `AlgebraicGeometry.strictHenselizationBaseChangeSpecializationPullbackAbCompIso`;
the two types are definitionally equal, and
`AlgebraicGeometry.strictHenselizationBaseChangeSpecializationPullbackAbCompIsoAt_eq` records
the identity. -/
def strictHenselizationBaseChangeSpecializationPullbackAbCompIsoAt :
    smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s) ⋙
        smallEtalePullbackAb (strictHenselizationBaseChangeSpecializationMapAt B hS f s t) ≅
      smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f
        (specializedGeometricPoint B S hS s t)) :=
  strictHenselizationBaseChangeSpecializationPullbackAbCompIso B hS f s t

/-- The alias of the composition identification is the original identification. -/
theorem strictHenselizationBaseChangeSpecializationPullbackAbCompIsoAt_eq :
    strictHenselizationBaseChangeSpecializationPullbackAbCompIsoAt B hS f s t =
      strictHenselizationBaseChangeSpecializationPullbackAbCompIso B hS f s t :=
  rfl

/-- The bottom arrow of Stacks 0GJ8 — pullback along `id_X × c` on derived global sections — with
the second base change indexed by `AlgebraicGeometry.specializedGeometricPoint` and with both
derivation instances supplied positionally.

This aliases `AlgebraicGeometry.strictHenselizationSectionsSpecialization`, whose instance
arguments are fixed at the `t.map p` spelling and so cannot be reached by instance synthesis
here; `AlgebraicGeometry.strictHenselizationSectionsSpecializationAt_eq` records the identity. -/
def strictHenselizationSectionsSpecializationAt
    [IS : ((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
          Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
            Ab.{u + 1}) (.up ℤ))]
    [IAt : ((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f
            (specializedGeometricPoint B S hS s t)))
          Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (smallEtaleTopology (strictHenselizationBaseChange B hS f
            (specializedGeometricPoint B S hS s t))) Ab.{u + 1}) (.up ℤ))] :
    smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s) ⋙
        smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s) ⟶
      smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f
          (specializedGeometricPoint B S hS s t)) ⋙
        smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f
          (specializedGeometricPoint B S hS s t)) :=
  @strictHenselizationSectionsSpecialization B X S hS f s t IS IAt

/-- The alias of the bottom arrow of Stacks 0GJ8 is the original bottom arrow. -/
theorem strictHenselizationSectionsSpecializationAt_eq
    [IS : ((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
          Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
            Ab.{u + 1}) (.up ℤ))]
    [IAt : ((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f
            (specializedGeometricPoint B S hS s t)))
          Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (smallEtaleTopology (strictHenselizationBaseChange B hS f
            (specializedGeometricPoint B S hS s t))) Ab.{u + 1}) (.up ℤ))] :
    strictHenselizationSectionsSpecializationAt B hS f s t =
      @strictHenselizationSectionsSpecialization B X S hS f s t IS IAt :=
  rfl

end MapAliases

/-! ### The square -/

section Square

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))

set_option maxHeartbeats 1600000 in
/-- The sheaf-level square of Stacks 0GJ8 in the vocabulary of the original maps, with the
restriction of sections along `id_X × c` written out as restriction of global sections followed
by the composition isomorphism for inverse images. -/
private theorem sheafSquareLanded :
    pushforwardStalkToStrictHenselizationSectionsAb B hS f s ≫
        (Functor.whiskerLeft
            (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
            (smallEtaleGlobalSectionsRestrictionAb
              (strictHenselizationBaseChangeSpecializationMap B hS f s t)) ≫
          (Functor.associator
            (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
            (smallEtalePullbackAb (strictHenselizationBaseChangeSpecializationMap B hS f s t))
            (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f
              (t.map (strictHenselizationToBase B S hS s)))) Ab.{u + 1})).inv ≫
          Functor.whiskerRight
            (strictHenselizationBaseChangeSpecializationPullbackAbCompIso B hS f s t).hom
            (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f
              (t.map (strictHenselizationToBase B S hS s)))) Ab.{u + 1})) =
      Functor.whiskerLeft (smallEtalePushforwardAb f)
          (smallEtaleSpecializationStalkAb B S hS s t) ≫
        pushforwardStalkToStrictHenselizationSectionsAb B hS f
          (t.map (strictHenselizationToBase B S hS s)) := by
  refine Eq.trans (congrArg (pushforwardStalkToStrictHenselizationSectionsAb B hS f s ≫ ·) ?_)
    (pushforwardStalkToStrictHenselizationSectionsAb_comp_sectionsRestrictionAb B hS f s t)
  rw [smallEtaleSectionsRestrictionAb,
    strictHenselizationBaseChangeSpecializationPullbackAbCompIso]
  ext F : 2
  simp

/-- The sheaf-level square of Stacks 0GJ8, with the restriction of sections along `id_X × c`
written out as restriction of global sections followed by the composition isomorphism for inverse
images, and every occurrence of the specialized point in the spelling of
`AlgebraicGeometry.specializedGeometricPoint`. -/
private theorem sheafSquare :
    pushforwardStalkToStrictHenselizationSectionsAb B hS f s ≫
        (Functor.whiskerLeft
            (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
            (smallEtaleGlobalSectionsRestrictionAb
              (strictHenselizationBaseChangeSpecializationMapAt B hS f s t)) ≫
          (Functor.associator
            (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
            (smallEtalePullbackAb (strictHenselizationBaseChangeSpecializationMapAt B hS f s t))
            (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f
              (specializedGeometricPoint B S hS s t))) Ab.{u + 1})).inv ≫
          Functor.whiskerRight
            (strictHenselizationBaseChangeSpecializationPullbackAbCompIsoAt B hS f s t).hom
            (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f
              (specializedGeometricPoint B S hS s t))) Ab.{u + 1})) =
      Functor.whiskerLeft (smallEtalePushforwardAb f)
          (smallEtaleSpecializationStalkAbAt B S hS s t) ≫
        pushforwardStalkToStrictHenselizationSectionsAb B hS f
          (specializedGeometricPoint B S hS s t) :=
  sheafSquareLanded B hS f s t

variable
  [((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))]
  [((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
        Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1}) (.up ℤ))]
  [((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f
          (specializedGeometricPoint B S hS s t)))
        Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (smallEtaleTopology (strictHenselizationBaseChange B hS f
          (specializedGeometricPoint B S hS s t))) Ab.{u + 1}) (.up ℤ))]

omit [((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))] in
/-- The comparison descended by the map of Stacks 0GIX from the stalk at `s`, written out. -/
private theorem unitEqSource :
    derivedPushforwardStalkToStrictHenselizationSectionsUnit B hS f s =
      Functor.whiskerLeft ((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ))
          (Functor.mapDerivedCategoryFactorsh (smallEtaleStalkAb s.hom)).hom ≫
        (Functor.associator ((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ))
          ((smallEtaleStalkAb s.hom).mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh).inv ≫
        Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
            (Iso.refl (smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom)) (.up ℤ)).hom
          DerivedCategory.Qh ≫
        Stacks.DerivedFunctor.exactDerivedDescUnit
          (smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom)
          (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1})
          (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s))
          (smallEtaleDerivedGlobalSectionsUnit (strictHenselizationBaseChange B hS f s))
          (pushforwardStalkToStrictHenselizationSectionsAb B hS f s) :=
  rfl

omit [((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))]
  [((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
      Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso
      (Sheaf (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1})
      (.up ℤ))] in
/-- The comparison descended by the map of Stacks 0GIX from the stalk at `t ≫ p`, written out. -/
private theorem unitEqTarget :
    derivedPushforwardStalkToStrictHenselizationSectionsUnit B hS f
        (specializedGeometricPoint B S hS s t) =
      Functor.whiskerLeft ((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ))
          (Functor.mapDerivedCategoryFactorsh (smallEtaleStalkAb
            (specializedGeometricPoint B S hS s t).hom)).hom ≫
        (Functor.associator ((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ))
          (Functor.mapHomotopyCategory (smallEtaleStalkAb
            (specializedGeometricPoint B S hS s t).hom) (.up ℤ))
          DerivedCategory.Qh).inv ≫
        Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
            (Iso.refl (smallEtalePushforwardAb f ⋙ smallEtaleStalkAb
              (specializedGeometricPoint B S hS s t).hom)) (.up ℤ)).hom
          DerivedCategory.Qh ≫
        Stacks.DerivedFunctor.exactDerivedDescUnit
          (smallEtalePushforwardAb f ⋙ smallEtaleStalkAb
            (specializedGeometricPoint B S hS s t).hom)
          (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f
            (specializedGeometricPoint B S hS s t)))
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f
            (specializedGeometricPoint B S hS s t))) Ab.{u + 1})
          (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f
            (specializedGeometricPoint B S hS s t)))
          (smallEtaleDerivedGlobalSectionsUnit (strictHenselizationBaseChange B hS f
            (specializedGeometricPoint B S hS s t)))
          (pushforwardStalkToStrictHenselizationSectionsAb B hS f
            (specializedGeometricPoint B S hS s t)) :=
  rfl

omit [((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))] in
/-- Pullback along `id_X × c` on derived global sections over the base changes, written out. -/
private theorem botEq :
    strictHenselizationSectionsSpecializationAt B hS f s t =
      Functor.whiskerLeft
          (smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s))
          (smallEtaleDerivedGlobalSectionsRestriction
            (strictHenselizationBaseChangeSpecializationMapAt B hS f s t)) ≫
        (Functor.associator
          (smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s))
          (smallEtaleDerivedPullbackAb
            (strictHenselizationBaseChangeSpecializationMapAt B hS f s t))
          (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f
            (specializedGeometricPoint B S hS s t)))).inv ≫
        Functor.whiskerRight (smallEtaleDerivedPullbackAbCompIsoQhLift
            (strictHenselizationBaseChangeSpecializationPullbackAbCompIsoAt B hS f s t)).hom
          (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f
            (specializedGeometricPoint B S hS s t))) :=
  rfl

omit [((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))] in
/-- The comparison descended at `s`, on a complex: the bookkeeping prefix contributes only the
identification of the two actions of the stalk at `s`. -/
private theorem unitAppSource
    (J : HomotopyCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :
    (derivedPushforwardStalkToStrictHenselizationSectionsUnit B hS f s).app J =
      (smallEtaleStalkAb s.hom).mapDerivedCategoryFactorsh.hom.app
        (((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ)).obj J) ≫
        (Stacks.DerivedFunctor.exactDerivedDescUnit
          (smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom)
          (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1})
          (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s))
          (smallEtaleDerivedGlobalSectionsUnit (strictHenselizationBaseChange B hS f s))
          (pushforwardStalkToStrictHenselizationSectionsAb B hS f s)).app J := by
  rw [unitEqSource B hS f s]
  exact Stacks.DerivedFunctor.derivedStalkDescUnit_app _ _ _ _ J

omit [((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))]
  [((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
      Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso
      (Sheaf (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1})
      (.up ℤ))] in
/-- The comparison descended at the specialized point, on a complex. -/
private theorem unitAppTarget
    (J : HomotopyCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :
    (derivedPushforwardStalkToStrictHenselizationSectionsUnit B hS f
          (specializedGeometricPoint B S hS s t)).app J =
      (Functor.mapDerivedCategoryFactorsh (smallEtaleStalkAb
          (specializedGeometricPoint B S hS s t).hom)).hom.app
            (((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ)).obj J) ≫
        (Stacks.DerivedFunctor.exactDerivedDescUnit
          (smallEtalePushforwardAb f ⋙
            smallEtaleStalkAb (specializedGeometricPoint B S hS s t).hom)
          (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f
            (specializedGeometricPoint B S hS s t)))
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f
            (specializedGeometricPoint B S hS s t))) Ab.{u + 1})
          (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f
            (specializedGeometricPoint B S hS s t)))
          (smallEtaleDerivedGlobalSectionsUnit (strictHenselizationBaseChange B hS f
            (specializedGeometricPoint B S hS s t)))
          (pushforwardStalkToStrictHenselizationSectionsAb B hS f
            (specializedGeometricPoint B S hS s t))).app J := by
  rw [unitEqTarget B hS f s t]
  exact Stacks.DerivedFunctor.derivedStalkDescUnit_app _ _ _ _ J

omit [((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))] in
/-- Pullback along `id_X × c` on an object of the unbounded derived category, in components. -/
private theorem botAppEq (K : smallEtaleDerivedCategory X) :
    (strictHenselizationSectionsSpecializationAt B hS f s t).app K =
      (smallEtaleDerivedGlobalSectionsRestriction
          (strictHenselizationBaseChangeSpecializationMapAt B hS f s t)).app
          ((smallEtaleDerivedPullbackAb
            (strictHenselizationBaseChangeToSource B hS f s)).obj K) ≫
        (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f
          (specializedGeometricPoint B S hS s t))).map
          ((smallEtaleDerivedPullbackAbCompIsoQhLift
          (strictHenselizationBaseChangeSpecializationPullbackAbCompIsoAt B hS f s t)).hom.app
            K) := by
  rw [botEq B hS f s t]
  simp

section Lift

variable {Z T T' : Scheme.{u}} {b : T ⟶ Z} {a : T' ⟶ T} {c : T' ⟶ Z}

/-- **The lifted composition isomorphism on the image of a complex**, with the preadditive
structures of the three categories of abelian sheaves read off their abelian structures.

This is `Stacks.EtaleCohomology.smallEtaleDerivedPullbackAbCompIsoQhLift_hom_app`; only the
spelling of those structures differs, and the identification of the two spellings is made here,
at an arbitrary triple of schemes, rather than at the sheaf categories of the base changes to the
two strict henselizations, where the terms are far larger. -/
theorem smallEtaleDerivedPullbackAbCompIsoQhLiftHomApp
    (χ : smallEtalePullbackAb b ⋙ smallEtalePullbackAb a ≅ smallEtalePullbackAb c)
    (J : HomotopyCategory (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ)) :
    (smallEtaleDerivedPullbackAbCompIsoQhLift χ).hom.app (DerivedCategory.Qh.obj J) =
      (smallEtalePullbackAb a).mapDerivedCategory.map
          ((smallEtalePullbackAb b).mapDerivedCategoryFactorsh.hom.app J) ≫
        (smallEtalePullbackAb a).mapDerivedCategoryFactorsh.hom.app
            (((smallEtalePullbackAb b).mapHomotopyCategory (.up ℤ)).obj J) ≫
          DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso χ (.up ℤ)).hom.app J) ≫
            (smallEtalePullbackAb c).mapDerivedCategoryFactorsh.inv.app J :=
  smallEtaleDerivedPullbackAbCompIsoQhLift_hom_app χ J

end Lift

omit [((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))] in
/-- The square of Stacks 0GJ9 on the two comparisons themselves, which is the generic descent
square of `Stacks.DerivedFunctor.exactDerivedDescUnit_comp_restriction` at the data of Stacks
0GJ8's sheaf-level square. -/
private theorem unitCore
    (J : HomotopyCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :
    (Stacks.DerivedFunctor.exactDerivedDescUnit
          (smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom)
          (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1})
          (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s))
          (smallEtaleDerivedGlobalSectionsUnit (strictHenselizationBaseChange B hS f s))
          (pushforwardStalkToStrictHenselizationSectionsAb B hS f s)).app J ≫
        (smallEtaleDerivedGlobalSectionsRestriction
          (strictHenselizationBaseChangeSpecializationMapAt B hS f s t)).app
            ((smallEtaleDerivedPullbackAb
              (strictHenselizationBaseChangeToSource B hS f s)).obj
              (DerivedCategory.Qh.obj J)) ≫
          (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f
          (specializedGeometricPoint B S hS s t))).map
            ((smallEtaleDerivedPullbackAbCompIsoQhLift
          (strictHenselizationBaseChangeSpecializationPullbackAbCompIsoAt B hS f s t)).hom.app
            (DerivedCategory.Qh.obj J)) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
          (Functor.whiskerLeft (smallEtalePushforwardAb f)
            (smallEtaleSpecializationStalkAbAt B S hS s t)) (.up ℤ)).app J) ≫
        (Stacks.DerivedFunctor.exactDerivedDescUnit
          (smallEtalePushforwardAb f ⋙
            smallEtaleStalkAb (specializedGeometricPoint B S hS s t).hom)
          (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f
            (specializedGeometricPoint B S hS s t)))
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f
            (specializedGeometricPoint B S hS s t))) Ab.{u + 1})
          (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f
            (specializedGeometricPoint B S hS s t)))
          (smallEtaleDerivedGlobalSectionsUnit (strictHenselizationBaseChange B hS f
            (specializedGeometricPoint B S hS s t)))
          (pushforwardStalkToStrictHenselizationSectionsAb B hS f
            (specializedGeometricPoint B S hS s t))).app J :=
  Stacks.DerivedFunctor.exactDerivedDescUnit_comp_restriction (sheafSquare B hS f s t)
    (smallEtaleDerivedGlobalSectionsRestriction_fac_app
      (strictHenselizationBaseChangeSpecializationMapAt B hS f s t))
    (smallEtaleDerivedPullbackAbCompIsoQhLiftHomApp
      (strictHenselizationBaseChangeSpecializationPullbackAbCompIsoAt B hS f s t)) J

omit [((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))] in
/-- The square of Stacks 0GJ9 on the comparisons from which the two maps of Stacks 0GIX from the
stalk of the derived direct image are descended. -/
private theorem unitSquare
    (J : HomotopyCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :
    (derivedPushforwardStalkToStrictHenselizationSectionsUnit B hS f s).app J ≫
        (strictHenselizationSectionsSpecializationAt B hS f s t).app
          (DerivedCategory.Qh.obj J) =
      (smallEtaleDerivedSpecializationStalkAbAt B S hS s t).app
          (DerivedCategory.Qh.obj
            (((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ)).obj J)) ≫
        (derivedPushforwardStalkToStrictHenselizationSectionsUnit B hS f
          (specializedGeometricPoint B S hS s t)).app J := by
  rw [unitAppSource B hS f s J, unitAppTarget B hS f s t J,
    botAppEq B hS f s t (DerivedCategory.Qh.obj J),
    smallEtaleDerivedSpecializationStalkAbAt_app B S hS s t
      (((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ)).obj J)]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun y =>
      (smallEtaleStalkAb s.hom).mapDerivedCategoryFactorsh.hom.app
        (((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ)).obj J) ≫ y)
    (unitCore B hS f s t J)) ?_
  rw [Stacks.DerivedFunctor.mapHomotopyCategory_whiskerLeft_app]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]

/-- **Stacks 0GJ9.** For `K` in `D(X_etale)` the specialization map on the stalk of `Rf_*K` at a
geometric point `s` of `S`, and pullback along `id_X × c` on global sections over the base change
to the strict henselization, form a commutative square with the two maps of Stacks 0GIX from
those stalks.

Read with `sp` vertical this is the left square of the diagram of Stacks 0GJ9; read with `sp`
horizontal it is the square of Stacks 0GJ8, which is
`AlgebraicGeometry.specializationStalk_comp_derivedPushforwardStalkToStrictHenselizationSections`.
It is proved here for an arbitrary morphism of schemes and an arbitrary object of `D(X_etale)`,
which is the generality Stacks 0GJ9 asserts it in. -/
@[stacks 0GJ9 "the left square, whose verticals are the specialization map `sp` and pullback \
along `id_X × c`; the source states that in general no vertical map exists between the \
cohomologies of `K` on the two fibres, so the right-hand column carries no square"]
theorem derivedPushforwardStalkToStrictHenselizationSections_comp_sectionsSpecialization :
    derivedPushforwardStalkToStrictHenselizationSections B hS f s ≫
        strictHenselizationSectionsSpecializationAt B hS f s t =
      Functor.whiskerLeft (smallEtaleDerivedPushforwardAb f)
          (smallEtaleDerivedSpecializationStalkAbAt B S hS s t) ≫
        derivedPushforwardStalkToStrictHenselizationSections B hS f
          (specializedGeometricPoint B S hS s t) := by
  refine Functor.rightDerived_ext
    (smallEtaleDerivedPushforwardAb f ⋙ smallEtaleDerivedStalkAb s.hom)
    (Functor.whiskerRight (smallEtaleDerivedPushforwardAbUnit f)
        (smallEtaleDerivedStalkAb s.hom) ≫
      (Functor.associator DerivedCategory.Qh (smallEtaleDerivedPushforwardAb f)
        (smallEtaleDerivedStalkAb s.hom)).hom)
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) _ _ _ ?_
  ext J
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, Category.assoc]
  have hnat :
      (smallEtaleDerivedStalkAb s.hom).map ((smallEtaleDerivedPushforwardAbUnit f).app J) ≫
          (smallEtaleDerivedSpecializationStalkAbAt B S hS s t).app
            ((smallEtaleDerivedPushforwardAb f).obj (DerivedCategory.Qh.obj J)) =
        (smallEtaleDerivedSpecializationStalkAbAt B S hS s t).app
            (DerivedCategory.Qh.obj
              (((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ)).obj J)) ≫
          (smallEtaleDerivedStalkAb
              (specializedGeometricPoint B S hS s t).hom).map
            ((smallEtaleDerivedPushforwardAbUnit f).app J) :=
    (smallEtaleDerivedSpecializationStalkAbAt B S hS s t).naturality _
  rw [← Category.assoc, derivedPushforwardStalkToStrictHenselizationSections_fac_app,
    ← Category.assoc, hnat, Category.assoc,
    derivedPushforwardStalkToStrictHenselizationSections_fac_app]
  exact unitSquare B hS f s t J

/-- For `K` in `D(X_etale)`, the square whose top arrow is the specialization map `sp` on the
stalk of `Rf_*K` and whose verticals are the maps of Stacks 0GIX from those stalks to the global
sections over the base changes to the strict henselizations commutes, its bottom arrow being
pullback along `id_X × c`.  The verticals are the identifications of Theorem 03Q9 when `f` is
quasi-compact and quasi-separated and `K` is bounded below; the square commutes for an arbitrary
morphism of schemes and an arbitrary object of `D(X_etale)`.  It is the square of
`derivedPushforwardStalkToStrictHenselizationSections_comp_sectionsSpecialization` read with
`sp` on top. -/
@[stacks 0GJ8 "the square, with `sp` on top and the maps of Stacks 0GIX as its verticals, \
proved for an arbitrary morphism of schemes and an arbitrary object of `D(X_etale)`"]
theorem specializationStalk_comp_derivedPushforwardStalkToStrictHenselizationSections :
    Functor.whiskerLeft (smallEtaleDerivedPushforwardAb f)
          (smallEtaleDerivedSpecializationStalkAbAt B S hS s t) ≫
        derivedPushforwardStalkToStrictHenselizationSections B hS f
          (specializedGeometricPoint B S hS s t) =
      derivedPushforwardStalkToStrictHenselizationSections B hS f s ≫
        strictHenselizationSectionsSpecializationAt B hS f s t :=
  (derivedPushforwardStalkToStrictHenselizationSections_comp_sectionsSpecialization B hS f s t).symm

end Square

/-! ### The square has no hypotheses -/

/- The square above is stated with three `CategoryTheory.Functor.HasRightDerivedFunctor`
arguments, those being what makes the unbounded `Rf_*` and the two unbounded `RΓ`s exist. They
are all found by instance search, from
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmallEtaleUnboundedDerivations.lean`, at an
arbitrary big étale site, an arbitrary morphism of schemes and an arbitrary pair of geometric
points; this example checks that, written out so that the reading of Stacks 0GJ8 and
0GJ9 above does not rest on prose. -/
example (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
    (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s)) :
    derivedPushforwardStalkToStrictHenselizationSections B hS f s ≫
        strictHenselizationSectionsSpecializationAt B hS f s t =
      Functor.whiskerLeft (smallEtaleDerivedPushforwardAb f)
          (smallEtaleDerivedSpecializationStalkAbAt B S hS s t) ≫
        derivedPushforwardStalkToStrictHenselizationSections B hS f
          (specializedGeometricPoint B S hS s t) :=
  derivedPushforwardStalkToStrictHenselizationSections_comp_sectionsSpecialization B hS f s t

end AlgebraicGeometry

end
