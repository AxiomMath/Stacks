module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoCompositionLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProduct

/-!
# The relative cup product and composition of morphisms of ringed spaces

For morphisms of ringed spaces `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and `g : (Y, 𝒪_Y) ⟶ (Z, 𝒪_Z)` the
relative cup product of Stacks 0B68 built from the composite adjunction `Lg^*Lf^* ⊣ Rf_*Rg_*` and
the composite derived pullback-tensor comparison is the relative cup product for `g` at the pair
`(Rf_*K, Rf_*L)` followed by `Rg_*` of the relative cup product for `f`.

## Main results

* `Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap_comp`: the abstract form.
  For composable adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂`, bifunctors `A`, `B`, `B'` on the three
  categories and comparisons `α : A ⋙ L₁ ⟶ (L₁ × L₁) ⋙ B` and `β : B ⋙ L₂ ⟶ (L₂ × L₂) ⋙ B'`,
  the doubled-counit adjunction morphism of the composite adjunction at the comparison
  `L₂α ≫ β` factors as the morphism for `L₁ ⊣ R₁` followed by `R₁` of the morphism for
  `L₂ ⊣ R₂`.
* `Stacks.Cohomology.DerivedRelativeCupProduct.pullbackTensorComparisonComp`: the derived
  pullback-tensor comparison of a composite assembled from the comparisons of Stacks 079U for
  its two factors.
* `Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_comp`: the geometric
  statement for the composite adjunction and the composite comparison, for arbitrary
  `K, L ∈ D(𝒪_X)` and with no finiteness, flatness or quasi-coherence hypothesis.
* `Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap_transport`: the abstract
  transport.  Two adjunctions related by natural isomorphisms `cl : L ≅ L'` and `cr : R ≅ R'`
  which exhibit `adj'` as `adj` transported along them, and comparisons related by `cl` through
  the same conjugation, have doubled-counit adjunction morphisms related by `cr`.
* `Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_comp'`: **Stacks 0FP6 as the
  source states it**, i.e. the square whose vertical edges are `relativeCupProduct (f ≫ g)` and
  the two-step relative cup product, and whose horizontal edges are the composition isomorphism
  `Rf_*Rg_* ≅ R(g ∘ f)_*` of
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso` in each tensor
  factor and at the tensor product.

## Implementation notes

*What the source asserts and how it is reached.*  Stacks 0FP6 is the commutativity of a square
whose horizontal edges are the identifications `R(g ∘ f)_* = Rg_*Rf_*` and whose vertical edges
are relative cup products.  `relativeCupProduct_comp` is that square with the identifications
taken as the spelling: the composite is written as `(derivedAdjunction g).comp
(derivedAdjunction f)` and `pullbackTensorComparisonComp`, which are the composite adjunction and
the composite comparison that the source's `=` signs name.  The source's own argument is
reproduced: both routes are the same adjoint transpose, because the chained counits are the
counit of the composite adjunction (Stacks 0DV0, `CategoryTheory.Adjunction.comp_counit_app`).

`relativeCupProduct_comp'` then says it of `relativeCupProduct (f ≫ g)` itself, so the source's
two `=` signs are proved to be respected rather than taken as a spelling.  The transport needs
exactly two inputs, and both are available unconditionally:

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_comp`, that the derived
  adjunction for `f ≫ g` *is* the composite adjunction transported along the composition
  isomorphisms of Stacks 0D5S and 0D5T;
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp`, that the comparison of
  Stacks 079U for `f ≫ g` is `pullbackTensorComparisonComp f g` conjugated by the isomorphism
  `Lg^*Lf^* ≅ L(g ∘ f)^*` of Stacks 0D5S.

*Why the transport is abstract.*  Both inputs are statements about an adjunction and a comparison
and nothing else, so the transport is carried out for an arbitrary adjunction, arbitrary
bifunctors and arbitrary comparisons in `adjunctionBitensorMap_transport`; the geometric
statement is one application of it.  The whole content of the transport is the counit identity
`adjunctionBitensorMap_counit_transport`, that `L(cr) ≫ cl ≫ counit'` is `counit`.

## References

* [Stacks Project, Tag 0FP6](https://stacks.math.columbia.edu/tag/0FP6)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0DV0](https://stacks.math.columbia.edu/tag/0DV0)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedRelativeCupProduct

section Abstract

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} (adj₁ : L₁ ⊣ R₁)
  {L₂ : D ⥤ E} {R₂ : E ⥤ D} (adj₂ : L₂ ⊣ R₂)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (B' : E × E ⥤ E)
  (α : A ⋙ L₁ ⟶ L₁.prod L₁ ⋙ B) (β : B ⋙ L₂ ⟶ L₂.prod L₂ ⋙ B')

/-- The abstract relative cup product of a composite of adjunctions, at the comparison obtained
by applying `L₂` to the outer comparison and then the inner comparison, is the abstract relative
cup product for `L₁ ⊣ R₁` followed by `R₁` applied to the one for `L₂ ⊣ R₂`. -/
theorem adjunctionBitensorMap_comp (G H : E) :
    adjunctionBitensorMap (adj₁.comp adj₂) A B'
        (Functor.whiskerRight α L₂ ≫ Functor.whiskerLeft (L₁.prod L₁) β) G H =
      adjunctionBitensorMap adj₁ A B α (R₂.obj G) (R₂.obj H) ≫
        R₁.map (adjunctionBitensorMap adj₂ B B' β G H) := by
  unfold adjunctionBitensorMap
  dsimp only [Functor.comp_obj]
  rw [Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply]
  rw [← Adjunction.homEquiv_naturality_right, Equiv.apply_eq_iff_eq,
    ← Adjunction.homEquiv_naturality_left, Equiv.apply_eq_iff_eq]
  have key : ((adj₁.comp adj₂).counit.app G ×ₘ (adj₁.comp adj₂).counit.app H) =
      (L₂.map (adj₁.counit.app (R₂.obj G)) ×ₘ L₂.map (adj₁.counit.app (R₂.obj H))) ≫
        (adj₂.counit.app G ×ₘ adj₂.counit.app H) := by
    rw [Adjunction.comp_counit_app, Adjunction.comp_counit_app, CategoryTheory.prod_comp]
  have hβ := β.naturality (adj₁.counit.app (R₂.obj G) ×ₘ adj₁.counit.app (R₂.obj H))
  simp only [Functor.comp_map, Functor.prod_map] at hβ
  rw [key, Functor.map_comp, Functor.map_comp]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj, Functor.id_obj, Functor.prod_obj, Category.assoc] at hβ ⊢
  rw [reassoc_of% hβ]

end Abstract

section Transport

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L L' : C ⥤ D} {R R' : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R')
  (cl : L ≅ L') (cr : R ≅ R')

/-- **The counit of a transported adjunction, read back through the transport.**  If `adj'` is
`adj` transported along `cl : L ≅ L'` on the left and `cr : R ≅ R'` on the right, then applying
`L` to `cr` and then `cl` carries the counit of `adj'` to the counit of `adj`.

This is the whole content of `adjunctionBitensorMap_transport`: the doubled-counit adjunction
morphism depends on the adjunction only through its counit and its transposition bijection, and
transposition is handled by `CategoryTheory.Adjunction.homEquiv_ofNatIsoLeft_apply` and
`CategoryTheory.Adjunction.homEquiv_ofNatIsoRight_apply`. -/
private lemma adjunctionBitensorMap_counit_transport (G : D) :
    L.map (cr.hom.app G) ≫ cl.hom.app (R'.obj G) ≫
        ((adj.ofNatIsoLeft cl).ofNatIsoRight cr).counit.app G = adj.counit.app G := by
  rw [NatTrans.naturality_assoc]
  simp only [Adjunction.ofNatIsoRight_counit, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.hom_inv_id_app_assoc]

variable (A : C × C ⥤ C) (B : D × D ⥤ D)
  (α : A ⋙ L ⟶ L.prod L ⋙ B) (α' : A ⋙ L' ⟶ L'.prod L' ⋙ B)

/-- **The abstract relative cup product is carried along a transport of its adjunction.**  Let
`adj'` be `adj` transported along `cl : L ≅ L'` and `cr : R ≅ R'`, and let the comparison `α'`
be `α` conjugated by `cl` — once on the source and once in each tensor factor of the target.
Then the doubled-counit adjunction morphism of `adj'` at `α'` is the one of `adj` at `α`, read
through `cr` in each argument on the source and at the tensor product on the target.

Both sides are adjoint transposes under `adj'`, so it suffices to compare the maps they
transpose, and there the hypothesis on the comparisons, naturality of `α` and of `cl`, and
`adjunctionBitensorMap_counit_transport` reduce one to the other. -/
theorem adjunctionBitensorMap_transport
    (hadj : (adj.ofNatIsoLeft cl).ofNatIsoRight cr = adj')
    (hα : Functor.whiskerLeft A cl.hom ≫ α' =
      α ≫ Functor.whiskerRight (NatTrans.prod cl.hom cl.hom) B)
    (G G' : D) :
    A.map (cr.hom.app G ×ₘ cr.hom.app G') ≫ adjunctionBitensorMap adj' A B α' G G' =
      adjunctionBitensorMap adj A B α G G' ≫ cr.hom.app (B.obj (G, G')) := by
  have hαpt : ∀ M N : C, cl.hom.app (A.obj (M, N)) ≫ α'.app (M, N) =
      α.app (M, N) ≫ B.map (cl.hom.app M ×ₘ cl.hom.app N) :=
    fun M N => NatTrans.congr_app hα (M, N)
  have ha := α.naturality (cr.hom.app G ×ₘ cr.hom.app G')
  change L.map (A.map (cr.hom.app G ×ₘ cr.hom.app G')) ≫ α.app (R'.obj G, R'.obj G') =
    α.app (R.obj G, R.obj G') ≫
      B.map (L.map (cr.hom.app G) ×ₘ L.map (cr.hom.app G')) at ha
  subst hadj
  unfold adjunctionBitensorMap
  rw [← Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_ofNatIsoLeft_apply]
  refine congrArg (fun z => z ≫ cr.hom.app (B.obj (G, G'))) ?_
  rw [Equiv.apply_eq_iff_eq, ← NatTrans.naturality_assoc,
    reassoc_of% (hαpt (R'.obj G) (R'.obj G')), reassoc_of% ha,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 2
  exact Prod.hom_ext (adjunctionBitensorMap_counit_transport adj cl cr G)
    (adjunctionBitensorMap_counit_transport adj cl cr G')

end Transport

universe u

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The derived pullback-tensor comparison
`Lg^*Lf^*(K ⊗^L_{𝒪_Z} L) ⟶ Lg^*Lf^*K ⊗^L_{𝒪_X} Lg^*Lf^*L` of a composite of morphisms of
ringed spaces: the derived pullback along `f` of the comparison of Stacks 079U for `g`, followed
by the comparison of Stacks 079U for `f` at the derived pullbacks along `g`. -/
def pullbackTensorComparisonComp :
    Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf) ⋙
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g ⋙
          Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) ⟶
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g ⋙
            Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).prod
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g ⋙
            Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) ⋙
        Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf) :=
  Functor.whiskerRight (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison g)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) ≫
    Functor.whiskerLeft
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g).prod
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g))
      (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)

/-- **The relative cup product is compatible with composition.**  For the composite adjunction
`Lg^*Lf^* ⊣ Rf_*Rg_*` and the composite derived pullback-tensor comparison, the relative cup
product of Stacks 0B68 is the relative cup product for `g` at the pair `(Rf_*K, Rf_*L)` followed
by `Rg_*` of the relative cup product for `f`. -/
@[stacks 0FP6 "for the composite adjunction and the composite pullback-tensor comparison"]
theorem relativeCupProduct_comp
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    adjunctionBitensorMap
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction g).comp
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f))
        (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf))
        (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
        (pullbackTensorComparisonComp f g) K L =
      relativeCupProduct g
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K)
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj L) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward g).map
          (relativeCupProduct f K L) :=
  adjunctionBitensorMap_comp
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction g)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison g)
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f) K L

/-- **Stacks 0FP6: the relative cup product is compatible with composition.**  For composable
morphisms of ringed spaces `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and `g : (Y, 𝒪_Y) ⟶ (Z, 𝒪_Z)` and
arbitrary `K, L ∈ D(𝒪_X)` the square

```
Rg_*Rf_*K ⊗^L Rg_*Rf_*L ⟶ R(g ∘ f)_*K ⊗^L R(g ∘ f)_*L
          |                            |
          |                            | relative cup product for f ≫ g
          v                            v
   Rg_*Rf_*(K ⊗^L L)     ⟶      R(g ∘ f)_*(K ⊗^L L)
```

commutes in `D(𝒪_Z)`, where the horizontal arrows are the composition isomorphism
`Rf_* ⋙ Rg_* ≅ R(g ∘ f)_*` of Stacks 0D5T — in each tensor factor on top and at the tensor
product on the bottom — and the left vertical arrow is the relative cup product for `g` at
`(Rf_*K, Rf_*L)` followed by `Rg_*` of the relative cup product for `f`.

This is the statement of the source, the two identifications being the composition isomorphism.
It is
`relativeCupProduct_comp` transported by `adjunctionBitensorMap_transport`, whose two inputs are
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_comp` and
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp`. -/
@[stacks 0FP6]
theorem relativeCupProduct_comp'
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso f
              g).hom.app K ×ₘ
            (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso f
              g).hom.app L) ≫
        relativeCupProduct (f ≫ g) K L =
      relativeCupProduct g
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K)
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj L) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward g).map
            (relativeCupProduct f K L) ≫
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso f
              g).hom.app
            (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj K).obj
              L) := by
  have hα : Functor.whiskerLeft
          (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf))
          (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom ≫
        Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison (f ≫ g) =
      pullbackTensorComparisonComp f g ≫
        Functor.whiskerRight
          (NatTrans.prod
            (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom
            (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom)
          (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)) :=
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp f g).trans
      (Category.assoc _ _ _).symm
  have h := adjunctionBitensorMap_transport
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction g).comp
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f))
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction (f ≫ g))
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso f g)
    (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf))
    (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (pullbackTensorComparisonComp f g)
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison (f ≫ g))
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_comp f g) hα K L
  rw [relativeCupProduct_comp f g K L] at h
  exact h.trans (Category.assoc _ _ _)

end Stacks.Cohomology.DerivedRelativeCupProduct

end
