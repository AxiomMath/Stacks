module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPushforwardSheafHomExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDerivedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorHomHomComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorBimodule
public import StacksCore.Tactic.StacksAttribute

/-!
# The exact functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` along a morphism of ringed topoi

Let `(f, f♯) : (Sh(𝒞), O_𝒞) ⟶ (Sh(𝒟), O_𝒟)` be a morphism of ringed topoi, let `𝒜` and `𝒜'` be
sheaves of differential graded `O_𝒞`-algebras, let `ℬ` be a sheaf of differential graded
`O_𝒟`-algebras, let `φ : ℬ ⟶ f_*𝒜` be a unital homomorphism and let `𝒩` be a differential graded
`(𝒜, 𝒜')`-bimodule. The functor

`Mod(ℬ, d) ⥤ Mod(𝒜', d)`, `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩`

extends to homogeneous maps: the pullback of sheaves of modules is applied degreewise, and a
tensor product with a bimodule sends `c` to `c ⊗ 1`. So it is a functor of differential graded
categories, and it induces an exact functor

`K(Mod(ℬ, d)) ⥤ K(Mod(𝒜', d))`

of triangulated categories, which is [Stacks, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE).

## Main definitions

* `SheafOfModules.DifferentialGradedModule.tensorHomogeneousMap`: the tensor product `c ⊗ 1` of
  a homogeneous map with the identity of a bimodule.
* `SheafOfModules.DifferentialGradedModule.tensorConcreteDGFunctor`: a tensor product functor
  with a bimodule, extended to homogeneous maps.
* `SheafOfModules.DifferentialGradedModule.toposPullbackTensorConcreteDGFunctor`: the functor
  `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩`, extended to homogeneous maps.

## Main results

* `SheafOfModules.DifferentialGradedModule.homotopyToposPullbackTensor_eq`: the functor
  `homotopyToposPullbackTensor` of homotopy categories is the one induced by that extension, so
  it carries the instances `homotopyToposPullbackTensor_commShift` and
  `homotopyToposPullbackTensor_isTriangulated`.
* `SheafOfModules.DifferentialGradedModule.exists_isTriangulated_homotopyToposPullbackTensorTopos`:
  **Tag 0FTE**.

## References

* [Stacks Project, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE)
* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open CochainComplex.HomComplex

universe u

namespace SheafOfModules.DifferentialGradedModule

/-! ### The tensor product of a homogeneous map with the identity of a bimodule -/

section Tensor

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A A' : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  {N : DifferentialGradedBimodule.{u, u, u} A A'}

/-- A homogeneous map is determined by its local homomorphisms. -/
theorem homogeneousMap_ext_localHom {M M' : DifferentialGradedModule.{u, u, u} A} {k : ℤ}
    {f g : HomogeneousMap A M M' k} (h : ∀ U : X.C, f.localHom U = g.localHom U) : f = g := by
  rw [← f.cochain_localHomFamily, ← g.cochain_localHomFamily]
  exact congrArg LocalHomFamily.cochain (LocalHomFamily.ext h)

/-- The local homomorphisms of a sum. -/
theorem localHom_add {M M' : DifferentialGradedModule.{u, u, u} A} {k : ℤ}
    (f g h : HomogeneousMap A M M' k) (hfg : h.val = f.val + g.val) (U : X.C) :
    h.localHom U = f.localHom U + g.localHom U :=
  LocalHom.ext fun i j hij V x => by
    rw [HomogeneousMap.localHom_app, LocalHom.add_app, HomogeneousMap.localHom_app,
      HomogeneousMap.localHom_app, hfg, Cochain.add_v]
    rfl

/-- The local homomorphisms of the differential of a homogeneous map are the differentials of
its local homomorphisms. -/
theorem localHom_delta {M M' : DifferentialGradedModule.{u, u, u} A} {k : ℤ}
    (f : HomogeneousMap A M M' k) (g : HomogeneousMap A M M' (k + 1))
    (hg : g.val = δ k (k + 1) f.val) (U : X.C) :
    g.localHom U = (f.localHom U).diffAt :=
  LocalHom.ext fun i j hij V x => by
    rw [HomogeneousMap.localHom_app, LocalHom.diffAt_app, HomogeneousMap.localHom_app,
      HomogeneousMap.localHom_app, hg,
      δ_v k (k + 1) rfl f.val i j hij (i + k) (i + 1) (by omega) rfl, homSections_add,
      homSections_comp, homSections_units_smul, homSections_comp, Int.negOnePow_succ]
    simp only [Units.val_neg, neg_smul, sub_eq_add_neg]
    rfl

/-- The local homomorphisms of a composite are the composites of the local homomorphisms. -/
theorem localHom_comp {M M' M'' : DifferentialGradedModule.{u, u, u} A} {k l m : ℤ}
    (f : HomogeneousMap A M M' k) (g : HomogeneousMap A M' M'' l)
    (fg : HomogeneousMap A M M'' m) (h : k + l = m) (hfg : fg.val = f.val.comp g.val h)
    (U : X.C) :
    fg.localHom U = (f.localHom U).comp (g.localHom U) h :=
  LocalHom.ext fun i j hij V x => by
    rw [HomogeneousMap.localHom_app, LocalHom.comp_app _ _ h rfl (by omega),
      HomogeneousMap.localHom_app, HomogeneousMap.localHom_app, hfg,
      Cochain.comp_v _ _ h i (i + k) j rfl (by omega), homSections_comp]

variable (D : TensorFunctorData.{u, u, u, u, u} A A' N)

/-- The family of tensor products `c ⊗ 1` of the local homomorphisms of a homogeneous map. -/
noncomputable def tensorLocalHomFamily {M M' : DifferentialGradedModule.{u, u, u} A} {k : ℤ}
    (f : HomogeneousMap A M M' k) :
    LocalHomFamily (D.functor.obj M) (D.functor.obj M') k where
  hom U := (D.isTensorProduct M).transport (D.isTensorProduct M') (f.localHom U)
  restrict g := ((D.isTensorProduct M).transport_restrict (D.isTensorProduct M') g _).trans
    (congrArg _ (f.localHom_restrict g))

/-- **The tensor product `c ⊗ 1` of a homogeneous map with the identity of the bimodule.** -/
noncomputable def tensorHomogeneousMap {M M' : DifferentialGradedModule.{u, u, u} A} {k : ℤ}
    (f : HomogeneousMap A M M' k) :
    HomogeneousMap A' (D.functor.obj M) (D.functor.obj M') k :=
  (tensorLocalHomFamily D f).cochain

/-- The local homomorphisms of `c ⊗ 1` are the tensor products of those of `c`. -/
theorem localHom_tensorHomogeneousMap {M M' : DifferentialGradedModule.{u, u, u} A} {k : ℤ}
    (f : HomogeneousMap A M M' k) (U : X.C) :
    (tensorHomogeneousMap D f).localHom U =
      (D.isTensorProduct M).transport (D.isTensorProduct M') (f.localHom U) :=
  LocalHomFamily.localHom_cochain _ U

/-- The tensor product of the cochain of a morphism is the cochain of the tensored morphism. -/
theorem tensorHomogeneousMap_ofHom {M M' : DifferentialGradedModule.{u, u, u} A} (φ : M ⟶ M') :
    tensorHomogeneousMap D ⟨Cochain.ofHom φ.toHomologicalComplex, actionLinear_ofHom A φ⟩ =
      ⟨Cochain.ofHom (D.functor.map φ).toHomologicalComplex,
        actionLinear_ofHom A' (D.functor.map φ)⟩ := by
  refine homogeneousMap_ext_localHom fun U => ?_
  rw [localHom_tensorHomogeneousMap]
  refine ((D.isTensorProduct M).localHom_ext fun i j kk hijk V x y => ?_).symm
  obtain rfl : kk = i + j := by omega
  rw [IsTensorProduct.transport_tmul, HomogeneousMap.localHom_app, Cochain.ofHom_v,
    homSections_apply, D.map_spec]
  refine eq_of_heq (HEq.trans ?_ (heq_castHom _ _ _ _).symm)
  refine (D.isTensorProduct M').tmul_heq_left (by omega) j _ ?_ y
  rw [HomogeneousMap.localHom_app]
  have e : (Cochain.ofHom φ.toHomologicalComplex).v i i (add_zero i) = φ.toHomologicalComplex.f i :=
    Cochain.ofHom_v _ i
  refine HEq.symm ((cochain_v_app_heq_of_eq (Cochain.ofHom φ.toHomologicalComplex)
    (add_zero i) rfl (add_zero i) _ x).trans ?_)
  rw [e]

/-- **A tensor product functor with a bimodule, extended to homogeneous maps** by `c ↦ c ⊗ 1`. -/
noncomputable def tensorConcreteDGFunctor :
    ConcreteDGFunctor.{u, u, u, u, u} (X := X) (Y := X) A A' where
  functor := D.functor
  mapCochain c hc := (tensorHomogeneousMap D ⟨c, hc⟩).val
  isActionLinear_mapCochain c hc := (tensorHomogeneousMap D ⟨c, hc⟩).property
  mapCochain_add c c' hc hc' hcc' := by
    have h : tensorHomogeneousMap D ⟨c + c', hcc'⟩ =
        ⟨(tensorHomogeneousMap D ⟨c, hc⟩).val + (tensorHomogeneousMap D ⟨c', hc'⟩).val,
          actionLinear_add A' _ _ (tensorHomogeneousMap D ⟨c, hc⟩).property
            (tensorHomogeneousMap D ⟨c', hc'⟩).property⟩ := by
      refine homogeneousMap_ext_localHom fun U => ?_
      rw [localHom_tensorHomogeneousMap, localHom_add ⟨c, hc⟩ ⟨c', hc'⟩ ⟨c + c', hcc'⟩ rfl,
        IsTensorProduct.transport_add,
        localHom_add (tensorHomogeneousMap D ⟨c, hc⟩) (tensorHomogeneousMap D ⟨c', hc'⟩)
          ⟨_, actionLinear_add A' _ _ (tensorHomogeneousMap D ⟨c, hc⟩).property
            (tensorHomogeneousMap D ⟨c', hc'⟩).property⟩ rfl,
        localHom_tensorHomogeneousMap, localHom_tensorHomogeneousMap]
    exact congrArg Subtype.val h
  mapCochain_delta c hc hδ := by
    have h : tensorHomogeneousMap D ⟨δ _ _ c, hδ⟩ =
        ⟨δ _ _ (tensorHomogeneousMap D ⟨c, hc⟩).val,
          actionLinear_delta A' _ (tensorHomogeneousMap D ⟨c, hc⟩).property⟩ := by
      refine homogeneousMap_ext_localHom fun U => ?_
      rw [localHom_tensorHomogeneousMap, localHom_delta ⟨c, hc⟩ ⟨δ _ _ c, hδ⟩ rfl,
        ← IsTensorProduct.transport_diffAt,
        localHom_delta (tensorHomogeneousMap D ⟨c, hc⟩)
          ⟨_, actionLinear_delta A' _ (tensorHomogeneousMap D ⟨c, hc⟩).property⟩ rfl,
        localHom_tensorHomogeneousMap]
    exact congrArg Subtype.val h
  mapCochain_comp c c' h hc hc' hcc' := by
    have e : tensorHomogeneousMap D ⟨c.comp c' h, hcc'⟩ =
        ⟨(tensorHomogeneousMap D ⟨c, hc⟩).val.comp (tensorHomogeneousMap D ⟨c', hc'⟩).val h,
          actionLinear_comp A' _ _ _ (tensorHomogeneousMap D ⟨c, hc⟩).property
            (tensorHomogeneousMap D ⟨c', hc'⟩).property⟩ := by
      refine homogeneousMap_ext_localHom fun U => ?_
      rw [localHom_tensorHomogeneousMap, localHom_comp ⟨c, hc⟩ ⟨c', hc'⟩ ⟨c.comp c' h, hcc'⟩ h rfl,
        IsTensorProduct.transport_comp _ (D.isTensorProduct _),
        localHom_comp (tensorHomogeneousMap D ⟨c, hc⟩) (tensorHomogeneousMap D ⟨c', hc'⟩)
          ⟨_, actionLinear_comp A' _ _ _ (tensorHomogeneousMap D ⟨c, hc⟩).property
            (tensorHomogeneousMap D ⟨c', hc'⟩).property⟩ h rfl,
        localHom_tensorHomogeneousMap, localHom_tensorHomogeneousMap]
    exact congrArg Subtype.val e
  mapCochain_ofHom φ := congrArg Subtype.val (tensorHomogeneousMap_ofHom D φ)

end Tensor

/-! ### The functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` along a morphism of ringed topoi -/

section Topos

open Stacks.Sheaves.RingedToposModules

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory
  AlgebraicGeometry.RingedTopos.hasSheafify_addCommGrpCat
  AlgebraicGeometry.RingedTopos.wEqualsLocallyBijective_addCommGrpCat

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (f : RingedToposHom X Y)
  {A A' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  {B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
  (φ : B ⟶ toposPushforwardAlgebra (toposDirectImageModules f) A) (hφ : φ.IsUnital)
  (N : DifferentialGradedBimodule.{u, u, u} A A')

/-- **The functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` along a morphism of ringed topoi, extended to homogeneous
maps**: the pullback of sheaves of modules degreewise, then `c ↦ c ⊗ 1` for the extension of
scalars to `𝒜` and for the tensor product with `𝒩`. -/
noncomputable def toposPullbackTensorConcreteDGFunctor :
    ConcreteDGFunctor.{u, u, u, u, u} (X := Y.toRingedSite) (Y := X.toRingedSite) B A' :=
  ((transportConcreteDGFunctor (toposInverseImageModules f) B).comp
    (tensorConcreteDGFunctor (X := X.toRingedSite) (toposBaseChangeData f φ hφ))).comp
    (tensorConcreteDGFunctor (X := X.toRingedSite) (toposPullbackTensorData N))

/-- **The functor `homotopyToposPullbackTensor` of homotopy categories is the one induced by the
extension of `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` to homogeneous maps.** -/
theorem homotopyToposPullbackTensor_eq :
    homotopyToposPullbackTensor f φ hφ N =
      (toposPullbackTensorConcreteDGFunctor f φ hφ N).homotopyFunctor :=
  rfl

/-- The functor of Tag 0FTE commutes with the translations. -/
@[instance_reducible]
noncomputable instance homotopyToposPullbackTensor_commShift :
    (homotopyToposPullbackTensor f φ hφ N).CommShift ℤ :=
  (toposPullbackTensorConcreteDGFunctor f φ hφ N).commShift

/-- The functor of Tag 0FTE is a triangulated functor. -/
instance homotopyToposPullbackTensor_isTriangulated :
    (homotopyToposPullbackTensor f φ hφ N).IsTriangulated :=
  (toposPullbackTensorConcreteDGFunctor f φ hφ N).isTriangulated

/-- **The exact functor of Tag 0FTE, with the compatibility of `forget₂ CommRingCat RingCat` with
sheaves as instance arguments.** The statement of
[Stacks, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE) itself, in which that
compatibility is discharged, is
`SheafOfModules.DifferentialGradedModule.exists_isTriangulated_homotopyToposPullbackTensorTopos`.
-/
theorem exists_isTriangulated_homotopyToposPullbackTensor :
    ∃ (Φ : HomotopyCategory.{u, u, u} B ⥤ HomotopyCategory.{u, u, u} A')
      (_ : Φ.CommShift ℤ), Φ.IsTriangulated ∧
      HomotopyCategory.quotient B ⋙ Φ =
        toposPullbackTensor f φ hφ N ⋙ HomotopyCategory.quotient A' ∧
      ∀ Ψ : HomotopyCategory.{u, u, u} B ⥤ HomotopyCategory.{u, u, u} A',
        HomotopyCategory.quotient B ⋙ Ψ =
          toposPullbackTensor f φ hφ N ⋙ HomotopyCategory.quotient A' → Ψ = Φ :=
  ⟨homotopyToposPullbackTensor f φ hφ N, inferInstance, inferInstance,
    HomotopyCategory.quotient_comp_descend _ _,
    fun Ψ hΨ => HomotopyCategory.eq_descend _ _ Ψ hΨ⟩

end Topos

/-! ### Tag 0FTE -/

section Tag

open Stacks.Sheaves.RingedToposModules

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory
  AlgebraicGeometry.RingedTopos.hasSheafify_addCommGrpCat
  AlgebraicGeometry.RingedTopos.wEqualsLocallyBijective_addCommGrpCat
  AlgebraicGeometry.RingedTopos.hasSheafCompose_forget₂_ringCat

/-- **Stacks 0FTE.** Let `(f, f♯) : (Sh(𝒞), O_𝒞) ⟶ (Sh(𝒟), O_𝒟)` be a morphism of ringed topoi,
let `𝒜` and `𝒜'` be sheaves of differential graded `O_𝒞`-algebras, let `ℬ` be a sheaf of
differential graded `O_𝒟`-algebras, let `φ : ℬ ⟶ f_*𝒜` be a homomorphism and let `𝒩` be a
differential graded `(𝒜, 𝒜')`-bimodule. Then the functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` induces an exact
functor

`K(Mod(ℬ, d)) ⥤ K(Mod(𝒜', d))`

of triangulated categories: there is a functor `Φ` of homotopy categories through which the
functor of modules factors along the two quotient functors, it is the only one, and it commutes
with the translations and carries distinguished triangles to distinguished triangles.

Here `f^*ℳ` is the pullback `f^*ℳ ⊗_{f^*ℬ} 𝒜` along `(f, 𝒜, φ)`, the homomorphism `φ` is
unital, as a homomorphism of differential graded algebras is in the source, and `Φ` is
`homotopyToposPullbackTensor`, by `homotopyToposPullbackTensor_eq`. -/
@[stacks 0FTE]
theorem exists_isTriangulated_homotopyToposPullbackTensorTopos
    {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}} (f : RingedToposHom X Y)
    {A A' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
    {B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
    (φ : B ⟶ toposPushforwardAlgebra (Osharp := X.O) (Psharp := Y.O)
      (toposDirectImageModules (X := X) (Y := Y) f) A) (hφ : φ.IsUnital)
    (N : DifferentialGradedBimodule.{u, u, u} A A') :
    ∃ (Φ : HomotopyCategory.{u, u, u} B ⥤ HomotopyCategory.{u, u, u} A')
      (_ : Φ.CommShift ℤ), Φ.IsTriangulated ∧
      HomotopyCategory.quotient B ⋙ Φ =
        toposPullbackTensor (X := X) (Y := Y) f φ hφ N ⋙ HomotopyCategory.quotient A' ∧
      ∀ Ψ : HomotopyCategory.{u, u, u} B ⥤ HomotopyCategory.{u, u, u} A',
        HomotopyCategory.quotient B ⋙ Ψ =
          toposPullbackTensor (X := X) (Y := Y) f φ hφ N ⋙ HomotopyCategory.quotient A' →
            Ψ = Φ :=
  exists_isTriangulated_homotopyToposPullbackTensor f φ hφ N

end Tag

end SheafOfModules.DifferentialGradedModule
