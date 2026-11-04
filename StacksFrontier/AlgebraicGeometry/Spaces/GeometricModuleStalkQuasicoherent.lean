module

public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedMinimalSupport

/-!
# The geometric stalk of a quasi-coherent module over an affine neighbourhood

Let `X` be an algebraic space over a scheme `S`, let `x̄` be a geometric point of `X` and let
`G` be a quasi-coherent `𝒪_X`-module.  For a small étale neighbourhood `(U, ū)` of `x̄` whose
chart `U` is an affine scheme, the stalk of `G` at `x̄` is the base change of the sections over
`U` along the germ map `𝒪(U) ⟶ 𝒪_{X, x̄}`:

`𝒪_{X, x̄} ⊗_{𝒪(U)} G(U) ≅ G_{x̄}`,  `a ⊗ s ↦ a · s_{x̄}`.

This is the description of the stalk of a quasi-coherent module on the small étale site of an
affine scheme as the tensor product with the strict henselization; on an algebraic space it
holds over every affine étale neighbourhood.

## Main definitions

* `AlgebraicGeometry.Space.etaleLocalRingChartAlgebra`: the `𝒪(U)`-algebra structure on
  `𝒪_{X, x̄}` given by the germ map of a neighbourhood.
* `AlgebraicGeometry.Space.geometricModuleStalkTensorMap`: the comparison
  `𝒪_{X, x̄} ⊗_{𝒪(U)} G(U) ⟶ G_{x̄}`.
* `AlgebraicGeometry.Space.geometricModuleStalkTensorEquiv`: the comparison is an isomorphism
  of `𝒪_{X, x̄}`-modules when `U` is affine and `G` is quasi-coherent.

## Main results

* `AlgebraicGeometry.Space.exists_etaleLocalRingGerm_eq`: every element of the étale local ring
  is the germ of a regular function on some small étale neighbourhood.
* `AlgebraicGeometry.Space.bijective_geometricModuleStalkTensorMap`: the comparison is
  bijective.

## Implementation notes

The proof is a filtered colimit argument carried out with the germ maps rather than with the
colimit presentation of either side.  Every element of the tensor product comes from
`𝒪(V) ⊗_{𝒪(U)} G(U)` for an affine neighbourhood `V` refining `U` and the neighbourhoods of the
coefficients, and there the comparison is the germ of the base change map
`𝒪(V) ⊗_{𝒪(U)} G(U) ⟶ G(V)`, which is bijective because a quasi-coherent module is cartesian
on affine charts (`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`).
Surjectivity is then joint surjectivity of the germ maps, and injectivity is the vanishing
criterion for germs.

## References

* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)

/-- **Every element of the étale local ring is a germ** of a regular function on some small
étale neighbourhood of the geometric point. -/
theorem exists_etaleLocalRingGerm_eq (a : etaleLocalRing B S hS X.1 x) :
    ∃ (N : SmallEtaleNeighborhood x) (r : chartRing B S hS X.1 X.2 N.chart),
      etaleLocalRingGerm B S hS X.1 x (op N) r = a := by
  obtain ⟨U, v, s, hs⟩ := (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber_jointly_surjective
    ((pointStalkRingEquiv B S hS X x).symm a)
  refine ⟨⟨U, v.1, v.2⟩, s, ?_⟩
  rw [← pointStalkRingEquiv_germ B S hS X x U v s]
  exact (congrArg (pointStalkRingEquiv B S hS X x) hs).trans
    ((pointStalkRingEquiv B S hS X x).apply_symm_apply a)

/-- The étale local ring at `x̄` as an algebra over the regular functions on a small étale
neighbourhood, through the germ map.  Not an instance: it depends on the neighbourhood. -/
@[instance_reducible]
noncomputable def etaleLocalRingChartAlgebra (N : SmallEtaleNeighborhood x) :
    Algebra (chartRing B S hS X.1 X.2 N.chart) (etaleLocalRing B S hS X.1 x) :=
  (etaleLocalRingGerm B S hS X.1 x (op N)).toAlgebra

variable (G : Modules.{u, u} B S hS X.1 X.2)

section Comparison

variable (N : SmallEtaleNeighborhood x)

attribute [local instance] etaleLocalRingChartAlgebra

/-- The geometric stalk as a module over the regular functions on a neighbourhood, by
restriction of scalars along the germ map. -/
@[instance_reducible]
noncomputable def geometricModuleStalkChartModule :
    Module (chartRing B S hS X.1 X.2 N.chart) (geometricModuleStalk B S hS X x G) :=
  Module.compHom _ (etaleLocalRingGerm B S hS X.1 x (op N))

attribute [local instance] geometricModuleStalkChartModule

/-- The scalar actions of `𝒪(U)` and `𝒪_{X, x̄}` on the geometric stalk are compatible through
the germ map. -/
instance : IsScalarTower (chartRing B S hS X.1 X.2 N.chart) (etaleLocalRing B S hS X.1 x)
    (geometricModuleStalk B S hS X x G) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The germ map of a neighbourhood, as a linear map over the regular functions on it. -/
noncomputable def geometricModuleStalkGermLinear :
    (G.val.obj (op N.chart) : Type u) →ₗ[chartRing B S hS X.1 X.2 N.chart]
      geometricModuleStalk B S hS X x G where
  toFun := geometricModuleStalkGerm B S hS X x G N
  map_add' := map_add _
  map_smul' r s := geometricModuleStalkGerm_smul B S hS X x G N r s

/-- **The comparison `𝒪_{X, x̄} ⊗_{𝒪(U)} G(U) ⟶ G_{x̄}`**, `a ⊗ s ↦ a · s_{x̄}`. -/
noncomputable def geometricModuleStalkTensorMap :
    etaleLocalRing B S hS X.1 x ⊗[chartRing B S hS X.1 X.2 N.chart] (G.val.obj (op N.chart))
      →ₗ[etaleLocalRing B S hS X.1 x] geometricModuleStalk B S hS X x G :=
  LinearMap.liftBaseChange _ (geometricModuleStalkGermLinear X x G N)

/-- The comparison map sends `a ⊗ s` to `a • s_{x̄}`. -/
@[simp]
theorem geometricModuleStalkTensorMap_tmul (a : etaleLocalRing B S hS X.1 x)
    (s : G.val.obj (op N.chart)) :
    geometricModuleStalkTensorMap X x G N (a ⊗ₜ s) =
      a • geometricModuleStalkGerm B S hS X x G N s :=
  LinearMap.liftBaseChange_tmul _ _ _ _

end Comparison

section Refinement

variable {N M : SmallEtaleNeighborhood x} (f : M ⟶ N)

/-- The germ map of a refinement `f : M ⟶ N`, linear over the functions on `N` acting on those
on `M` by restriction. -/
noncomputable def etaleLocalRingGermLinear :
    letI := chartAlgebra (hF := X.2) f.hom
    letI := etaleLocalRingChartAlgebra X x N
    chartRing B S hS X.1 X.2 M.chart →ₗ[chartRing B S hS X.1 X.2 N.chart]
      etaleLocalRing B S hS X.1 x :=
  letI := chartAlgebra (hF := X.2) f.hom
  letI := etaleLocalRingChartAlgebra X x N
  { toFun := etaleLocalRingGerm B S hS X.1 x (op M)
    map_add' := map_add _
    map_smul' r b := by
      exact ((etaleLocalRingGerm B S hS X.1 x (op M)).map_mul (chartRestrict f.hom r) b).trans
        (congrArg (· * etaleLocalRingGerm B S hS X.1 x (op M) b)
          (etaleLocalRingGerm_chartRestrict (hF := X.2) f r)) }

/-- On the image of `𝒪(M) ⊗_{𝒪(N)} G(N)`, the comparison is the germ of the base change map
`𝒪(M) ⊗_{𝒪(N)} G(N) ⟶ G(M)`. -/
theorem geometricModuleStalkTensorMap_rTensor (w : letI := chartAlgebra (hF := X.2) f.hom
      chartRing B S hS X.1 X.2 M.chart ⊗[chartRing B S hS X.1 X.2 N.chart]
        (G.val.obj (op N.chart))) :
    letI := chartAlgebra (hF := X.2) f.hom
    letI := etaleLocalRingChartAlgebra X x N
    geometricModuleStalkTensorMap X x G N
        (LinearMap.rTensor _ (etaleLocalRingGermLinear X x f) w) =
      geometricModuleStalkGerm B S hS X x G M (sectionsBaseChange G f.hom w) := by
  let := chartAlgebra (hF := X.2) f.hom
  let := etaleLocalRingChartAlgebra X x N
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add w w' hw hw' => simp only [map_add, hw, hw']
  | tmul b s =>
    rw [LinearMap.rTensor_tmul, geometricModuleStalkTensorMap_tmul, chartBaseChange_tmul,
      geometricModuleStalkGerm_smul, chartRestrictLinear_apply]
    show etaleLocalRingGerm B S hS X.1 x (op M) b • _ = _
    rw [geometricModuleStalkGerm_map B S hS X x G f s]

/-- Restriction of regular functions along `g : M' ⟶ M`, linear over the functions on `N` for
the algebra structures given by `f` and `g ≫ f`. -/
noncomputable def chartRestrictLinearOver {M' : SmallEtaleNeighborhood x} (g : M' ⟶ M) :
    letI := chartAlgebra (hF := X.2) f.hom
    letI := chartAlgebra (hF := X.2) (g ≫ f).hom
    chartRing B S hS X.1 X.2 M.chart →ₗ[chartRing B S hS X.1 X.2 N.chart]
      chartRing B S hS X.1 X.2 M'.chart :=
  letI := chartAlgebra (hF := X.2) f.hom
  letI := chartAlgebra (hF := X.2) (g ≫ f).hom
  { toFun := chartRestrict g.hom
    map_add' := map_add _
    map_smul' r b := by
      change chartRestrict g.hom (chartRestrict f.hom r * b) =
        chartRestrict (g ≫ f).hom r * chartRestrict g.hom b
      rw [map_mul]
      change _ = chartRestrict (g.hom ≫ f.hom) r * _
      rw [chartRestrict_comp]
      rfl }

/-- The base change map is compatible with restriction to a smaller neighbourhood. -/
theorem sectionsBaseChange_rTensor_chartRestrictLinearOver {M' : SmallEtaleNeighborhood x}
    (g : M' ⟶ M) (w : letI := chartAlgebra (hF := X.2) f.hom
      chartRing B S hS X.1 X.2 M.chart ⊗[chartRing B S hS X.1 X.2 N.chart]
        (G.val.obj (op N.chart))) :
    letI := chartAlgebra (hF := X.2) f.hom
    letI := chartAlgebra (hF := X.2) (g ≫ f).hom
    sectionsBaseChange G (g ≫ f).hom
        (LinearMap.rTensor _ (chartRestrictLinearOver X x f g) w) =
      G.val.map g.hom.op (sectionsBaseChange G f.hom w) := by
  let := chartAlgebra (hF := X.2) f.hom
  let := chartAlgebra (hF := X.2) (g ≫ f).hom
  induction w using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add w w' hw hw' =>
    rw [map_add, map_add, hw, hw', map_add]
    exact (map_add (ConcreteCategory.hom (G.val.map g.hom.op)) _ _).symm
  | tmul b s =>
    rw [LinearMap.rTensor_tmul, chartBaseChange_tmul, chartBaseChange_tmul,
      chartRestrictLinear_apply, chartRestrictLinear_apply]
    let := chartSectionsModule G g.hom
    have key₂ : G.val.map (g ≫ f).hom.op s = G.val.map g.hom.op (G.val.map f.hom.op s) :=
      PresheafOfModules.map_comp_apply G.val f.hom.op g.hom.op s
    rw [key₂]
    exact ((chartRestrictLinear G g.hom).map_smul b (G.val.map f.hom.op s)).symm

/-- The germ maps of `M` and of a refinement `M'` agree on functions restricted from `M`. -/
theorem rTensor_etaleLocalRingGermLinear_comp {M' : SmallEtaleNeighborhood x} (g : M' ⟶ M)
    (w : letI := chartAlgebra (hF := X.2) f.hom
      chartRing B S hS X.1 X.2 M.chart ⊗[chartRing B S hS X.1 X.2 N.chart]
        (G.val.obj (op N.chart))) :
    letI := chartAlgebra (hF := X.2) f.hom
    letI := chartAlgebra (hF := X.2) (g ≫ f).hom
    letI := etaleLocalRingChartAlgebra X x N
    LinearMap.rTensor _ (etaleLocalRingGermLinear X x (g ≫ f))
        (LinearMap.rTensor _ (chartRestrictLinearOver X x f g) w) =
      LinearMap.rTensor _ (etaleLocalRingGermLinear X x f) w := by
  let := chartAlgebra (hF := X.2) f.hom
  let := chartAlgebra (hF := X.2) (g ≫ f).hom
  let := etaleLocalRingChartAlgebra X x N
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  congr 2
  exact LinearMap.ext fun b => etaleLocalRingGerm_chartRestrict (hF := X.2) g b

end Refinement

section Bijective

attribute [local instance] etaleLocalRingChartAlgebra

/-- Every element of `𝒪_{X, x̄} ⊗_{𝒪(U)} G(U)` comes from `𝒪(V) ⊗_{𝒪(U)} G(U)` for some affine
neighbourhood `V` refining `U`. -/
theorem exists_isAffine_mem_range_rTensor (N : SmallEtaleNeighborhood x)
    (z : etaleLocalRing B S hS X.1 x ⊗[chartRing B S hS X.1 X.2 N.chart]
      (G.val.obj (op N.chart))) :
    ∃ (M : SmallEtaleNeighborhood x) (f : M ⟶ N), IsAffine (chartScheme M.chart) ∧
      letI := chartAlgebra (hF := X.2) f.hom
      z ∈ LinearMap.range (LinearMap.rTensor (G.val.obj (op N.chart))
        (etaleLocalRingGermLinear X x f)) := by
  classical
  have := isCofiltered_smallEtaleNeighborhood B S hS X.1 X.2 x
  -- the property for one neighbourhood propagates to any refinement
  have hmono : ∀ {M M' : SmallEtaleNeighborhood x} (f : M ⟶ N) (g : M' ⟶ M)
      (z : etaleLocalRing B S hS X.1 x ⊗[chartRing B S hS X.1 X.2 N.chart]
        (G.val.obj (op N.chart))),
      (letI := chartAlgebra (hF := X.2) f.hom;
        z ∈ LinearMap.range (LinearMap.rTensor (G.val.obj (op N.chart))
          (etaleLocalRingGermLinear X x f))) →
      letI := chartAlgebra (hF := X.2) (g ≫ f).hom
      z ∈ LinearMap.range (LinearMap.rTensor (G.val.obj (op N.chart))
        (etaleLocalRingGermLinear X x (g ≫ f))) := by
    rintro M M' f g z ⟨w, rfl⟩
    exact ⟨_, rTensor_etaleLocalRingGermLinear_comp X x G f g w⟩
  suffices h : ∀ z, ∃ (M : SmallEtaleNeighborhood x) (f : M ⟶ N),
      letI := chartAlgebra (hF := X.2) f.hom
      z ∈ LinearMap.range (LinearMap.rTensor (G.val.obj (op N.chart))
        (etaleLocalRingGermLinear X x f)) by
    obtain ⟨M, f, hz⟩ := h z
    obtain ⟨M', g, hM'⟩ := exists_smallEtaleNeighborhoodHom_isAffine B S hS X x M
    exact ⟨M', g ≫ f, hM', hmono f g z hz⟩
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨N, 𝟙 N, Submodule.zero_mem _⟩
  | tmul a s =>
    obtain ⟨N', r, rfl⟩ := exists_etaleLocalRingGerm_eq X x a
    obtain ⟨M, f, f', -⟩ := IsCofilteredOrEmpty.cone_objs N N'
    let := chartAlgebra (hF := X.2) f.hom
    refine ⟨M, f, chartRestrict f'.hom r ⊗ₜ s, ?_⟩
    rw [LinearMap.rTensor_tmul]
    exact congrArg (· ⊗ₜ s) (etaleLocalRingGerm_chartRestrict (hF := X.2) f' r)
  | add z z' hz hz' =>
    obtain ⟨M, f, hz⟩ := hz
    obtain ⟨M', f', hz'⟩ := hz'
    obtain ⟨P, g, g', -⟩ := IsCofilteredOrEmpty.cone_objs M M'
    obtain ⟨Q, k, hk⟩ := IsCofilteredOrEmpty.cone_maps (g ≫ f) (g' ≫ f')
    have e : (k ≫ g') ≫ f' = (k ≫ g) ≫ f := by
      simp only [Category.assoc, hk]
    refine ⟨Q, (k ≫ g) ≫ f, Submodule.add_mem _ (hmono f (k ≫ g) z hz) ?_⟩
    rw [← e]
    exact hmono f' (k ≫ g') z' hz'

/-- **The geometric stalk of a quasi-coherent module is the base change of its sections over an
affine neighbourhood**: for `G` quasi-coherent and `U` affine, the comparison
`𝒪_{X, x̄} ⊗_{𝒪(U)} G(U) ⟶ G_{x̄}` is bijective. -/
theorem bijective_geometricModuleStalkTensorMap (hG : G.IsQuasicoherentOnSite)
    (N : SmallEtaleNeighborhood x) (hN : IsAffine (chartScheme N.chart)) :
    Function.Bijective (geometricModuleStalkTensorMap X x G N) := by
  classical
  have := isCofiltered_smallEtaleNeighborhood B S hS X.1 X.2 x
  have hcart : IsCartesianOnAffineCharts G :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 G hG
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨M, f, hM, w, rfl⟩ := exists_isAffine_mem_range_rTensor X x G N z
    let := chartAlgebra (hF := X.2) f.hom
    rw [geometricModuleStalkTensorMap_rTensor] at hz
    obtain ⟨M', g, hg⟩ := (geometricModuleStalkGerm_eq_zero_iff B S hS X x G M _).1 hz
    obtain ⟨M'', g', hM''⟩ := exists_smallEtaleNeighborhoodHom_isAffine B S hS X x M'
    let := chartAlgebra (hF := X.2) ((g' ≫ g) ≫ f).hom
    have h0 : sectionsBaseChange G ((g' ≫ g) ≫ f).hom
        (LinearMap.rTensor _ (chartRestrictLinearOver X x f (g' ≫ g)) w) = 0 := by
      have key : G.val.map (g' ≫ g).hom.op (sectionsBaseChange G f.hom w) =
          G.val.map g'.hom.op (G.val.map g.hom.op (sectionsBaseChange G f.hom w)) :=
        PresheafOfModules.map_comp_apply G.val g.hom.op g'.hom.op _
      rw [sectionsBaseChange_rTensor_chartRestrictLinearOver]
      exact key.trans ((congrArg _ hg).trans (map_zero _))
    have h1 : LinearMap.rTensor _ (chartRestrictLinearOver X x f (g' ≫ g)) w = 0 :=
      (injective_iff_map_eq_zero _).1 (hcart _ _ hN hM'' _).1 _ h0
    rw [← rTensor_etaleLocalRingGermLinear_comp X x G f (g' ≫ g) w, h1, map_zero]
  · intro z
    obtain ⟨M, t, rfl⟩ := geometricModuleStalkGerm_jointly_surjective B S hS X x G z
    obtain ⟨P, g, g', -⟩ := IsCofilteredOrEmpty.cone_objs M N
    obtain ⟨Q, k, hQ⟩ := exists_smallEtaleNeighborhoodHom_isAffine B S hS X x P
    let := chartAlgebra (hF := X.2) (k ≫ g').hom
    obtain ⟨w, hw⟩ := (hcart _ _ hN hQ (k ≫ g').hom).2 (G.val.map (k ≫ g).hom.op t)
    refine ⟨LinearMap.rTensor _ (etaleLocalRingGermLinear X x (k ≫ g')) w, ?_⟩
    rw [geometricModuleStalkTensorMap_rTensor, hw, geometricModuleStalkGerm_map]

/-- **`𝒪_{X, x̄} ⊗_{𝒪(U)} G(U) ≅ G_{x̄}`** for a quasi-coherent `G` and an affine small étale
neighbourhood `U` of `x̄`, as modules over the étale local ring `𝒪_{X, x̄}`. -/
noncomputable def geometricModuleStalkTensorEquiv (hG : G.IsQuasicoherentOnSite)
    (N : SmallEtaleNeighborhood x) (hN : IsAffine (chartScheme N.chart)) :
    etaleLocalRing B S hS X.1 x ⊗[chartRing B S hS X.1 X.2 N.chart] (G.val.obj (op N.chart))
      ≃ₗ[etaleLocalRing B S hS X.1 x] geometricModuleStalk B S hS X x G :=
  LinearEquiv.ofBijective _ (bijective_geometricModuleStalkTensorMap X x G hG N hN)

/-- The comparison isomorphism sends `a ⊗ s` to `a • s_{x̄}`. -/
@[simp]
theorem geometricModuleStalkTensorEquiv_tmul (hG : G.IsQuasicoherentOnSite)
    (N : SmallEtaleNeighborhood x) (hN : IsAffine (chartScheme N.chart))
    (a : etaleLocalRing B S hS X.1 x) (s : G.val.obj (op N.chart)) :
    geometricModuleStalkTensorEquiv X x G hG N hN (a ⊗ₜ s) =
      a • geometricModuleStalkGerm B S hS X x G N s :=
  geometricModuleStalkTensorMap_tmul X x G N a s

end Bijective

end AlgebraicGeometry.Space

end
