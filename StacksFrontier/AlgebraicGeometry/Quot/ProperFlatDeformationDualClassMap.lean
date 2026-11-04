module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationMapGlobalSection

/-!
# Naturality of the deformation classes over `k[V]`

For a morphism `φ : x ⟶ x'` of deformations of `x₀ = (X₀ ⟶ Spec k)` in
`Spaces'_{fp, flat, proper}` lying over `k[f] : k[V] ⟶ k[V']`, the class of `x'` in
`Ext¹(NL_{X₀/k}, 𝒪_{X₀} ⊗_k V')` is the class of `x` pushed along `𝒪_{X₀} ⊗_k f`: the morphism of
extensions of `φ` is along the map of ideals it induces, and that map is `𝒪_{X₀} ⊗_k f`. Read on
linear forms, the classes `V^* ⟶ Ext¹(NL_{X₀/k}, 𝒪_{X₀})` of `x` and `x'` differ by the transpose
of `f`. This is the naturality in `V` of the classes in the proof of Stacks 0D1K.

## Main results

* `AlgebraicGeometry.Space.deformationTangentClass_map`
* `AlgebraicGeometry.Space.deformationDualClass_map`
* `CategoryTheory.Functor.dualClassMap_eq_of_eq_comp`
* `CategoryTheory.Functor.dualClassMap_id_apply`
* `AlgebraicGeometry.Space.deformationTangentClass_eq_of_deformationDualClass_eq`

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory Deformation Deformation.Artin

universe u

namespace CategoryTheory.Functor

variable {k : Type u} [CommRing k] {C : Type*} [Category C] [Preadditive C]
  (G : ModuleCat.{u} k ⥤ C) [G.Additive] {X : C} {V V' : ModuleCat.{u} k}

attribute [local instance] evalModule

/-- If `ξ' = ξ ≫ G.map f`, then the class of `ξ'` at a linear form `l` on `V'` is the class of `ξ`
at `l ∘ f`. -/
theorem dualClassMap_eq_of_eq_comp (ξ : X ⟶ G.obj V) (ξ' : X ⟶ G.obj V') (f : V ⟶ V')
    (h : ξ' = ξ ≫ G.map f) (l : Module.Dual k V') :
    G.dualClassMap ξ' l = G.dualClassMap ξ (l ∘ₗ f.hom) := by
  subst h
  exact G.dualClassMap_comp ξ f l

/-- The class at the identity form of `k` is the morphism itself. -/
theorem dualClassMap_id_apply (ξ : X ⟶ G.obj (ModuleCat.of k k)) :
    G.dualClassMap ξ (LinearMap.id (R := k) (M := k)) = ξ := by
  rw [dualClassMap_apply, ModuleCat.ofHom_id, G.map_id, Category.comp_id]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {y₀ : CartesianProperFlatSpaces B S hS}
  {hy₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj y₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  {x x' : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
    y₀ hy₀}
  (φ : DeformationMorphism iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
    y₀ hy₀ x x')
  (V V' : FGModuleCat.{u} k)
  (hx : x.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)
  (hx' : x'.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V')

/-- **Naturality of the class of a deformation over `k[V]`**: for a morphism of deformations
over `k[f] : k[V] ⟶ k[V']`, the class of the target in `Ext¹(NL_{X₀/k}, 𝒪_{X₀} ⊗_k V')` is the
class of the source pushed along `𝒪_{X₀} ⊗_k f`. -/
theorem deformationTangentClass_map (f : V ⟶ V')
    (hρ : φ.ringHom = eqToHom hx ≫ (artinianSquareZeroExtensionFunctor Λ k).map f ≫
      eqToHom hx'.symm) :
    deformationTangentClass B S hS V' x' hx' =
      deformationTangentClass B S hS V x hx ≫
        (deformationClassFunctor B S hS Λ y₀ hy₀).map
          ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).map f) := by
  have key : ∀ ψ : (baseRingTensorModule B S hS y₀.obj.obj.left
        (baseFieldHom B S hS (hy₀ := hy₀))).obj
          ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) ⟶
      (baseRingTensorModule B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))).obj
        ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V'),
      ψ = (baseRingTensorModule B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))).map
        ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).map f) →
      AlgebraExtension.extOneMap ((AlgebraExtension.moduleRes
          (smallEtaleModelTopology B S hS y₀.obj.obj.left.1)
          (modelEquiv B S hS y₀.obj.obj.left).inverse
          (structureSheaf B S hS y₀.obj.obj.left.1 y₀.obj.obj.left.2)).map ψ)
        (deformationTangentClass B S hS V x hx) =
      deformationTangentClass B S hS V x hx ≫
        (deformationClassFunctor B S hS Λ y₀ hy₀).map
          ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).map f) := by
    rintro ψ rfl
    rfl
  exact (modelExtClass_mapAlong B S hS (deformationTangentMapAlong B S hS φ V V' hx hx'
    (deformationMorphismSpaceMap_comp_tangentRetraction B S hS φ V V' hx hx' f hρ))).trans
    (key _ (deformationTangentKernelMap_eq B S hS φ V hx V' hx' f hρ))

attribute [local instance] Functor.evalModule

/-- **Naturality of the classes on linear forms**: for a morphism of deformations over
`k[f] : k[V] ⟶ k[V']` and a linear form `λ` on `V'`, the class of the target at `λ` is the class
of the source at `λ ∘ f`. -/
theorem deformationDualClass_map (f : V ⟶ V')
    (hρ : φ.ringHom = eqToHom hx ≫ (artinianSquareZeroExtensionFunctor Λ k).map f ≫
      eqToHom hx'.symm)
    (l : Module.Dual k ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V')) :
    deformationDualClass B S hS V' x' hx' l =
      deformationDualClass B S hS V x hx
        (l ∘ₗ ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).map f).hom) :=
  Functor.dualClassMap_eq_of_eq_comp _ _ _ _
    (deformationTangentClass_map B S hS φ V V' hx hx' f hρ) l

/-- **Over `k[ε]`, the classes on linear forms determine the classes**: two deformations over
`k[k] = k[ε]` whose classes on linear forms agree have the same class in
`Ext¹(NL_{X₀/k}, 𝒪_{X₀} ⊗_k k)`, the class at the identity form being the class itself. -/
theorem deformationTangentClass_eq_of_deformationDualClass_eq
    {z z' : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
      y₀ hy₀}
    (hz : z.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k))
    (hz' : z'.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k))
    (h : deformationDualClass B S hS (FGModuleCat.of k k) z hz =
      deformationDualClass B S hS (FGModuleCat.of k k) z' hz') :
    deformationTangentClass B S hS (FGModuleCat.of k k) z hz =
      deformationTangentClass B S hS (FGModuleCat.of k k) z' hz' :=
  ((Functor.dualClassMap_id_apply (deformationClassFunctor B S hS Λ y₀ hy₀)
      (deformationTangentClass B S hS (FGModuleCat.of k k) z hz)).symm.trans
    (DFunLike.congr_fun h (LinearMap.id (R := k) (M := k)))).trans
    (Functor.dualClassMap_id_apply (deformationClassFunctor B S hS Λ y₀ hy₀)
      (deformationTangentClass B S hS (FGModuleCat.of k k) z' hz'))

end AlgebraicGeometry.Space

end
