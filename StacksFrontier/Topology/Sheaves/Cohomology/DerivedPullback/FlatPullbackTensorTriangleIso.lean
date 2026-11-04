module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatPullbackTensorTriangle

/-!
# The descent of `M ↦ Tot(f^*M ⊗ 𝒢)` carries triangles of short exact sequences to triangles

With `Ψ : M ↦ Tot(f^*M ⊗_{𝒪_X} 𝒢)` and its descent `R : D(𝒪_Y) ⥤ D(𝒪_X)` as in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatPullbackTensorTriangle`, this file
proves that for a short exact sequence `S` of complexes of `𝒪_Y`-modules whose image under `Ψ` is
short exact, `R` carries the distinguished triangle of `S` to the distinguished triangle of
`Ψ(S)`, by an isomorphism of triangles whose components are those of `Q ⋙ R ≅ Ψ ⋙ Q`.

## Main results

* `Stacks.Cohomology.FlatPullbackTensor.derivedFunctor_map_triangleOfSESδ`: the square of
  connecting morphisms.
* `Stacks.Cohomology.FlatPullbackTensor.mapTriangleOfSESIso`: the isomorphism of triangles.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Pretriangulated

namespace Stacks.Cohomology.FlatPullbackTensor

universe u

attribute [local instance] HasDerivedCategory.standard

open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (Modules)

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (G : CochainComplex (Modules X) ℤ)
  (hflat : ∀ q : ℤ, AlgebraicGeometry.IsFlatOver f (G.X q))
  (hb : ∃ a b : ℤ, G.IsStrictlyGE a ∧ G.IsStrictlyLE b)

/-- The inverse of the isomorphism `Q ⋙ R ≅ Ψ ⋙ Q` commutes with the shifts by `ℤ`. -/
instance natTransCommShift_derivedFunctorFactors_inv :
    NatTrans.CommShift (derivedFunctorFactors f G hflat hb).inv ℤ :=
  NatTrans.CommShift.of_iso_inv _ ℤ

/-- `map_mappingConeTriangle_mor₃` at `Ψ = M ↦ Tot(f^*M ⊗ 𝒢)`. -/
theorem complexFunctor_map_mappingConeTriangle_mor₃
    (S : ShortComplex (CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)) :
    (complexFunctor f G).map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
        ((complexFunctor f G).commShiftIso (1 : ℤ)).hom.app S.X₁ =
      (coneIso (bifunctor f) G S.f).hom ≫
        (CochainComplex.mappingCone.triangle ((complexFunctor f G).map S.f)).mor₃ :=
  map_mappingConeTriangle_mor₃ (bifunctor f) G S.f

/-- `map_descShortComplex_eq` at `Ψ = M ↦ Tot(f^*M ⊗ 𝒢)`. -/
theorem complexFunctor_map_descShortComplex
    (S : ShortComplex (CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)) :
    (complexFunctor f G).map (CochainComplex.mappingCone.descShortComplex S) =
      (coneIso (bifunctor f) G S.f).hom ≫
        CochainComplex.mappingCone.descShortComplex (S.map (complexFunctor f G)) :=
  map_descShortComplex_eq (bifunctor f) G S

/-- **The connecting morphisms are compatible with `Q ⋙ R ≅ Ψ ⋙ Q`**: for a short exact
sequence `S` of complexes of `𝒪_Y`-modules whose image under `Ψ` is short exact, `R` applied to
the connecting morphism of `S`, followed by the commutation of `R` with the shift, is the
connecting morphism of `Ψ S`, up to the components of the isomorphism at `S.X₃` and `S.X₁`. -/
theorem derivedFunctor_map_triangleOfSESδ
    {S : ShortComplex (CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)}
    (hS : S.ShortExact) (hΨS : (S.map (complexFunctor f G)).ShortExact) :
    (derivedFunctor f G hflat hb).map (DerivedCategory.triangleOfSESδ hS) ≫
        ((derivedFunctor f G hflat hb).commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj S.X₁) ≫
        ((derivedFunctorFactors f G hflat hb).inv.app S.X₁)⟦(1 : ℤ)⟧' =
      (derivedFunctorFactors f G hflat hb).inv.app S.X₃ ≫ DerivedCategory.triangleOfSESδ hΨS :=
  DerivedCategory.map_triangleOfSESδ_comp_natTrans.{u + 1, u + 1, u, u, u + 1, u + 1}
    (complexFunctor f G)
    (derivedFunctor f G hflat hb) (derivedFunctorFactors f G hflat hb).inv hS hΨS
    (coneIso (bifunctor f) G S.f).hom (complexFunctor_map_mappingConeTriangle_mor₃ f G S)
    (complexFunctor_map_descShortComplex f G S)

/-- **The morphism of triangles `R(triangle of S) ⟶ triangle of Ψ(S)`** whose components are
those of `Q ⋙ R ≅ Ψ ⋙ Q`; it is an isomorphism, see `mapTriangleOfSESIso`. -/
def mapTriangleOfSESHom
    {S : ShortComplex (CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)}
    (hS : S.ShortExact) (hΨS : (S.map (complexFunctor f G)).ShortExact) :
    (derivedFunctor f G hflat hb).mapTriangle.obj (DerivedCategory.triangleOfSES hS) ⟶
      DerivedCategory.triangleOfSES hΨS :=
  Triangle.homMk _ _ ((derivedFunctorFactors f G hflat hb).inv.app S.X₁)
    ((derivedFunctorFactors f G hflat hb).inv.app S.X₂)
    ((derivedFunctorFactors f G hflat hb).inv.app S.X₃)
    ((derivedFunctorFactors f G hflat hb).inv.naturality S.f)
    ((derivedFunctorFactors f G hflat hb).inv.naturality S.g)
    ((Category.assoc _ _ _).trans (derivedFunctor_map_triangleOfSESδ f G hflat hb hS hΨS))

/-- **The isomorphism of triangles `R(triangle of S) ≅ triangle of Ψ(S)`**. -/
def mapTriangleOfSESIso
    {S : ShortComplex (CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)}
    (hS : S.ShortExact) (hΨS : (S.map (complexFunctor f G)).ShortExact) :
    (derivedFunctor f G hflat hb).mapTriangle.obj (DerivedCategory.triangleOfSES hS) ≅
      DerivedCategory.triangleOfSES hΨS :=
  Triangle.isoMk _ _ ((derivedFunctorFactors f G hflat hb).app S.X₁).symm
    ((derivedFunctorFactors f G hflat hb).app S.X₂).symm
    ((derivedFunctorFactors f G hflat hb).app S.X₃).symm
    ((derivedFunctorFactors f G hflat hb).inv.naturality S.f)
    ((derivedFunctorFactors f G hflat hb).inv.naturality S.g)
    ((Category.assoc _ _ _).trans (derivedFunctor_map_triangleOfSESδ f G hflat hb hS hΨS))

end Stacks.Cohomology.FlatPullbackTensor

end
