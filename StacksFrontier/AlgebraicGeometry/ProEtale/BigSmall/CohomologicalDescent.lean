module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Triple
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.HigherDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.ProEtale.BigSmall.AbelianSheaves
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallProjection
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardExact

/-!
# Cohomological descent for the pro-étale projection

Let `S` be a scheme of a chosen big pro-étale site and let
`π_S : Sh((Sch/S)_proetale) ⟶ Sh(S_proetale)` be the projection of topoi of Stacks 098Q. Its
direct image is restriction to the small site, so it is exact, and the composite
`π_{S,*} ∘ π_S^{-1}` is the identity. Consequently the derived unit
`K ⟶ Rπ_{S,*} π_S^{-1} K` is an isomorphism for every complex `K` of abelian sheaves on the
small pro-étale site: cohomology computed on the big site agrees with cohomology computed on
the small one.

## Main definitions

* `AlgebraicGeometry.ProEtale.projectionAbelianInverseImage` and
  `AlgebraicGeometry.ProEtale.projectionAbelianDirectImage`: the inverse and direct images of
  abelian sheaves along `π_S`.
* `AlgebraicGeometry.ProEtale.projectionAbelianAdjunction`: the adjunction between them.
* `AlgebraicGeometry.ProEtale.derivedProjectionAdjunction`: its localization to unbounded
  derived categories, whose right adjoint is the unbounded right derived direct image.

## Main results

* `AlgebraicGeometry.ProEtale.projectionDirectImage_exact`: `π_{S,*}` is exact on abelian
  sheaves.
* `AlgebraicGeometry.ProEtale.projectionUnit_isIso`: the unit of `π_S` is an isomorphism of
  sheaves of sets.
* `AlgebraicGeometry.ProEtale.projectionAbelianAdjunction_unit_isIso`: the unit of the abelian
  adjunction is an isomorphism.
* `AlgebraicGeometry.ProEtale.proetaleCohomologicalDescent`: the derived unit
  `K ⟶ Rπ_{S,*} π_S^{-1} K` is an isomorphism.

## Implementation notes

Exactness of `π_{S,*}` comes from Stacks 04DB applied to the criterion that `π_{S,*}`
preserves epimorphisms, which holds because it is isomorphic to the inverse image of the
inclusion `i_S` of the small site, a left adjoint.

That the unit of `π_S` is an isomorphism is the adjoint triple
`π_S^{-1} ⊣ π_{S,*} ⊣ i_{S,*}`: its unit is invertible exactly when its counit is, and the
counit is invertible because `π_{S,*} ∘ i_{S,*}` is the identity.

The unit of the abelian adjunction is the unit of `π_S` on underlying sheaves of sets — this is
`projectionAbelianAdjunction_unit_forget`, which holds definitionally and is what pins the map
of cohomological descent down to the canonical one. Forgetting the group structure reflects
isomorphisms, so invertibility transfers back.

The derived adjunction is the localization of the adjunction on cochain complexes; because the
direct image is exact, its right adjoint is literally the unbounded right derived direct image
of Stacks 015F. Invertibility of the derived unit is checked on complexes, where it is
degreewise the abelian unit, and transported to an arbitrary object of the derived category
along the canonical isomorphism with the image of a representing complex.

## References

* [Stacks Project, Tag 0F6A](https://stacks.math.columbia.edu/tag/0F6A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Topos.AbelianPushforward

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inverse image `π_S^{-1}` of abelian sheaves along the projection from the big
pro-étale topos over `S` to the small pro-étale topos of `S`.

See [Stacks Project, Tag 0F6A](https://stacks.math.columbia.edu/tag/0F6A). -/
public abbrev projectionAbelianInverseImage :
    Sheaf (SmallProetale.topology B S hS) AddCommGrpCat.{u + 1} ⥤
      Sheaf (BigProetaleOver.topology B S hS) AddCommGrpCat.{u + 1} :=
  Sites.abelianInverseImage (bigProetaleToSmallProetaleMorphism B S hS)

/-- The direct image `π_{S,*}` of abelian sheaves along the projection from the big pro-étale
topos over `S` to the small pro-étale topos of `S`; it is restriction to the small site.

See [Stacks Project, Tag 0F6A](https://stacks.math.columbia.edu/tag/0F6A). -/
public abbrev projectionAbelianDirectImage :
    Sheaf (BigProetaleOver.topology B S hS) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallProetale.topology B S hS) AddCommGrpCat.{u + 1} :=
  abelianPushforward (BigProetaleOver.topology B S hS)
    (bigProetaleToSmallProetaleMorphism B S hS)

/-- The direct image of the pro-étale projection is exact on abelian sheaves: it preserves
epimorphisms, being restriction to the small site, which is the inverse image of the inclusion
`i_S` and hence a left adjoint. -/
public theorem projectionDirectImage_exact :
    exactFunctor (Sheaf (BigProetaleOver.topology B S hS) AddCommGrpCat.{u + 1})
      (Sheaf (SmallProetale.topology B S hS) AddCommGrpCat.{u + 1})
      (projectionAbelianDirectImage B S hS) := by
  let : (smallProetaleToBigProetaleMorphism B (⟨S, hS⟩ : B.Scheme)
      (⟨S, hS⟩ : B.Scheme) (𝟙 (⟨S, hS⟩ : B.Scheme))).inverseImage.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (smallProetaleToBigProetaleMorphism B (⟨S, hS⟩ : B.Scheme)
        (⟨S, hS⟩ : B.Scheme) (𝟙 (⟨S, hS⟩ : B.Scheme))).adj
  have hp : (bigProetaleToSmallProetaleMorphism B S hS).pushforward.PreservesEpimorphisms :=
    Functor.PreservesEpimorphisms.of_iso
      (inclusionInverseImageIsoProjectionPushforward B S hS)
  exact abelianPushforward_exact _ _ (Or.inl hp)

/-- The inverse image of abelian sheaves along the pro-étale projection is left adjoint to the
direct image. -/
public def projectionAbelianAdjunction :
    projectionAbelianInverseImage B S hS ⊣ projectionAbelianDirectImage B S hS :=
  abelianInverseImageAdjPushforward _ _

/-- The unit of the pro-étale projection is an isomorphism of sheaves of sets: in the adjoint
triple `π_S^{-1} ⊣ π_{S,*} ⊣ i_{S,*}` the unit is invertible exactly when the counit is, and
the counit is invertible because `π_{S,*} ∘ i_{S,*}` is the identity. -/
public theorem projectionUnit_isIso :
    IsIso (bigProetaleToSmallProetaleMorphism B S hS).adj.unit := by
  let i := smallProetaleToBigProetaleMorphism B (⟨S, hS⟩ : B.Scheme)
    (⟨S, hS⟩ : B.Scheme) (𝟙 (⟨S, hS⟩ : B.Scheme))
  let p := bigProetaleToSmallProetaleMorphism B S hS
  let adj₂ := i.adj.ofNatIsoLeft (inclusionInverseImageIsoProjectionPushforward B S hS)
  let t : Adjunction.Triple p.inverseImage p.pushforward i.pushforward := ⟨p.adj, adj₂⟩
  exact t.isIso_unit_iff_isIso_counit.2
    (adj₂.isIso_counit_of_iso (projectionCompInclusionPushforwardIso B S hS))

/-- On underlying sheaves of sets the unit of the abelian projection adjunction is the unit of
the projection of topoi. This pins down the canonical map of cohomological descent, rather than
an arbitrary adjunction unit. -/
public theorem projectionAbelianAdjunction_unit_forget
    (A : Sheaf (SmallProetale.topology B S hS) AddCommGrpCat.{u + 1}) :
    (sheafCompose (SmallProetale.topology B S hS) (forget AddCommGrpCat.{u + 1})).map
        ((projectionAbelianAdjunction B S hS).unit.app A) =
      (bigProetaleToSmallProetaleMorphism B S hS).adj.unit.app
        ((sheafCompose (SmallProetale.topology B S hS)
          (forget AddCommGrpCat.{u + 1})).obj A) :=
  rfl

/-- The unit of the abelian projection adjunction is an isomorphism: it is the unit of the
projection of topoi after forgetting the group structure, and forgetting the group structure
reflects isomorphisms. -/
public theorem projectionAbelianAdjunction_unit_isIso :
    IsIso (projectionAbelianAdjunction B S hS).unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro A
  let U := sheafCompose (SmallProetale.topology B S hS) (forget AddCommGrpCat.{u + 1})
  have : IsIso (U.map ((projectionAbelianAdjunction B S hS).unit.app A)) := by
    rw [projectionAbelianAdjunction_unit_forget]
    exact (NatTrans.isIso_iff_isIso_app _).1 (projectionUnit_isIso B S hS) _
  exact isIso_of_reflects_iso ((projectionAbelianAdjunction B S hS).unit.app A) U

/-- The inverse image of abelian sheaves along the pro-étale projection is additive. -/
public instance projectionAbelianInverseImage_additive :
    (projectionAbelianInverseImage B S hS).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The direct image of abelian sheaves along the pro-étale projection preserves finite
limits. -/
public instance projectionAbelianDirectImage_preservesFiniteLimits :
    PreservesFiniteLimits (projectionAbelianDirectImage B S hS) :=
  (projectionDirectImage_exact B S hS).1

/-- The direct image of abelian sheaves along the pro-étale projection preserves finite
colimits. -/
public instance projectionAbelianDirectImage_preservesFiniteColimits :
    PreservesFiniteColimits (projectionAbelianDirectImage B S hS) :=
  (projectionDirectImage_exact B S hS).2

/-- The direct image of abelian sheaves along the pro-étale projection is additive. -/
public instance projectionAbelianDirectImage_additive :
    (projectionAbelianDirectImage B S hS).Additive :=
  Functor.additive_of_preserves_binary_products _

section Derived

variable
  [HasDerivedCategory (Sheaf (BigProetaleOver.topology B S hS) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (SmallProetale.topology B S hS) AddCommGrpCat.{u + 1})]

/-- The derived adjunction of the pro-étale projection, obtained by localizing the abelian
adjunction on cochain complexes. Its right adjoint is the unbounded right derived direct image,
which is computed by the direct image itself because that functor is exact. -/
public def derivedProjectionAdjunction :
    (projectionAbelianInverseImage B S hS).mapDerivedCategory ⊣
      Stacks.DerivedFunctor.HigherDerivedOfExact.RF (projectionAbelianDirectImage B S hS) := by
  let F := projectionAbelianInverseImage B S hS
  let G := projectionAbelianDirectImage B S hS
  change F.mapDerivedCategory ⊣ G.mapDerivedCategory
  let : CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (G.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  exact (Adjunction.mapHomologicalComplexAdjunction (projectionAbelianAdjunction B S hS)
    (ComplexShape.up ℤ)).localization
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _

/-- **Stacks 0F6A.** For a scheme `S` of a chosen big pro-étale site and a complex `K` of
abelian sheaves on the small pro-étale site of `S`, the canonical map
`K ⟶ Rπ_{S,*} π_S^{-1} K` is an isomorphism. -/
@[stacks 0F6A]
public theorem proetaleCohomologicalDescent
    (K : DerivedCategory (Sheaf (SmallProetale.topology B S hS) AddCommGrpCat.{u + 1})) :
    IsIso ((derivedProjectionAdjunction B S hS).unit.app K) := by
  let F := projectionAbelianInverseImage B S hS
  let G := projectionAbelianDirectImage B S hS
  let adj := projectionAbelianAdjunction B S hS
  let adjC := Adjunction.mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)
  have : IsIso adj.unit := projectionAbelianAdjunction_unit_isIso B S hS
  have hterm (P : CochainComplex
      (Sheaf (SmallProetale.topology B S hS) AddCommGrpCat.{u + 1}) ℤ) :
      IsIso (adjC.unit.app P) := by
    have : ∀ i, IsIso ((adjC.unit.app P).f i) := fun i => by
      dsimp [adjC, Adjunction.mapHomologicalComplexAdjunction]
      infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  let P : CochainComplex
      (Sheaf (SmallProetale.topology B S hS) AddCommGrpCat.{u + 1}) ℤ :=
    DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let : CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (G.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  have hQ : IsIso ((derivedProjectionAdjunction B S hS).unit.app
      (DerivedCategory.Q.obj P)) := by
    show IsIso ((adjC.localization
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      F.mapDerivedCategory G.mapDerivedCategory).unit.app (DerivedCategory.Q.obj P))
    rw [Adjunction.localization_unit_app]
    have := hterm P
    infer_instance
  have hn' : e.hom ≫ (derivedProjectionAdjunction B S hS).unit.app K =
      (derivedProjectionAdjunction B S hS).unit.app (DerivedCategory.Q.obj P) ≫
        (F.mapDerivedCategory ⋙
          Stacks.DerivedFunctor.HigherDerivedOfExact.RF G).map e.hom := by
    simpa only [Functor.id_map] using (derivedProjectionAdjunction B S hS).unit.naturality e.hom
  have hc : IsIso (e.hom ≫ (derivedProjectionAdjunction B S hS).unit.app K) := by
    rw [hn']
    infer_instance
  exact (isIso_comp_left_iff _ _).mp hc

end Derived

end AlgebraicGeometry.ProEtale

end
