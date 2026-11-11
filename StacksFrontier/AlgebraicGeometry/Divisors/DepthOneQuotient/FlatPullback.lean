module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import StacksFrontier.RingTheory.CohenMacaulay.Module
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.PresheafOfModules.StalkMap
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat pullback of the depth-one quotient

The depth-one quotient of a coherent module along a specialization-closed set is preserved by
flat pullback to a Noetherian scheme: the pullback of the quotient map is again a depth-one
quotient, along the inverse image of that set.

## Main results

* `AlgebraicGeometry.isDepthOneQuotient_pullback`: the pullback of the canonical depth-one
  quotient map along a flat morphism of Noetherian schemes satisfies the defining properties
  of the depth-one quotient along the preimage of the set.
* `AlgebraicGeometry.depthOneQuotient_pullback_unique`: hence the depth-one quotient of the
  pullback is the pullback of the depth-one quotient, by a unique isomorphism over the source.

## Implementation notes

The four clauses of `AlgebraicGeometry.IsDepthOneQuotient` are checked separately. Coherence of
the pullback is [Stacks, Tag 0EBF]; epimorphy is preserved by any left adjoint. The clause away
from the set is bijectivity of a stalk map, which transports along the identification of the
stalk of a pullback with an extension of scalars; `modulePullback_stalkMap_bijective` records
that transport. The depth clause uses the behaviour of depth under a flat local extension,
`Module.depth_tensorProduct_of_flat`, through the same identification.

## References

* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v w

namespace AlgebraicGeometry



/-- If a morphism `φ : G ⟶ H` of sheaves of modules on `Y` induces a bijection on stalks at
`f x`, then its pullback along `f : X ⟶ Y` induces a bijection on stalks at `x`. -/
lemma modulePullback_stalkMap_bijective
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G H : SheafOfModules.{u} (structureSheafRing Y))
    (φ : G ⟶ H) (x : X)
    (hφ : Function.Bijective
      (stalkMapLinear (R := Y.presheaf) G.val H.val φ.val (f.hom.base x))) :
    Function.Bijective
      (stalkMapLinear (R := X.presheaf)
        ((RingedSpaceModuleAdjunction.modulePullback f).obj G).val
        ((RingedSpaceModuleAdjunction.modulePullback f).obj H).val
        ((RingedSpaceModuleAdjunction.modulePullback f).map φ).val x) := by
  let R := Y.presheaf.stalk (f.hom.base x)
  let S := X.presheaf.stalk x
  let M := TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f.hom.base x)
  let M' := TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf (f.hom.base x)
  let N := TopCat.Presheaf.stalk (C := Ab.{u})
    ((RingedSpaceModuleAdjunction.modulePullback f).obj G).val.presheaf x
  let N' := TopCat.Presheaf.stalk (C := Ab.{u})
    ((RingedSpaceModuleAdjunction.modulePullback f).obj H).val.presheaf x
  let :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) G.val (f.hom.base x)
  let :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) H.val (f.hom.base x)
  let :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) ((RingedSpaceModuleAdjunction.modulePullback f).obj G).val x
  let :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) ((RingedSpaceModuleAdjunction.modulePullback f).obj H).val x
  let : Algebra R S := (f.hom.stalkMap x).hom.toAlgebra
  obtain ⟨E, hE⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f G x
  obtain ⟨E', hE'⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f H x
  let a := stalkMapLinear (R := Y.presheaf) G.val H.val φ.val (f.hom.base x)
  let b := stalkMapLinear (R := X.presheaf)
    ((RingedSpaceModuleAdjunction.modulePullback f).obj G).val
    ((RingedSpaceModuleAdjunction.modulePullback f).obj H).val
    ((RingedSpaceModuleAdjunction.modulePullback f).map φ).val x
  let ae : M ≃ₗ[R] M' := LinearEquiv.ofBijective a hφ
  let te : TensorProduct R S M ≃ₗ[R] TensorProduct R S M' :=
    TensorProduct.congr (LinearEquiv.refl R S) ae
  let teS : TensorProduct R S M →ₗ[S] TensorProduct R S M' := {
    toFun := te
    map_add' := te.map_add
    map_smul' := by
      intro s z
      induction z using TensorProduct.inductionOn with
      | add z w hz hw => simp [hz, hw]
      | tmul r m =>
          simp [te, TensorProduct.smul_tmul']
  }
  let lhs : TensorProduct R S M →ₗ[S] TensorProduct R S M' :=
    E'.toLinearMap.comp (b.comp E.symm.toLinearMap)
  have hgen : ∀ m : M, lhs (1 ⊗ₜ[R] m) = teS (1 ⊗ₜ[R] m) := by
    intro m
    obtain ⟨V, hxV, s, hs⟩ :=
      TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) G.val.presheaf m
    let uG := ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f).unit.app
      G).val.app (op V) s
    let z := TopCat.Presheaf.germ
      ((RingedSpaceModuleAdjunction.modulePullback f).obj G).val.presheaf
      ((RingedSpaceModuleAdjunction.opensMap f).obj V) x hxV uG
    have hunitG : E z = (1 : S) ⊗ₜ[R] m := by
      rw [← hs]
      exact hE V hxV s
    have hz : E.symm ((1 : S) ⊗ₜ[R] m) = z :=
      (congrArg E.symm hunitG.symm).trans (E.symm_apply_apply z)
    let ψ := (PresheafOfModules.toPresheaf
      (structureSheafRing X).obj).map
        ((RingedSpaceModuleAdjunction.modulePullback f).map φ).val
    have hmap : b z = TopCat.Presheaf.germ
        ((RingedSpaceModuleAdjunction.modulePullback f).obj H).val.presheaf
        ((RingedSpaceModuleAdjunction.opensMap f).obj V) x hxV
        ((ψ.app (op ((RingedSpaceModuleAdjunction.opensMap f).obj V))).hom uG) := by
      dsimp [b, z]
      exact TopCat.Presheaf.stalkFunctor_map_germ_apply' _ _ _
        ψ uG
    have hnat :=
      (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f).unit_naturality φ
    let uH := ConcreteCategory.hom
      (((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f).unit.app
        H).val.app (op V)) ((φ.val.app (op V)).hom s)
    let zH := TopCat.Presheaf.germ
      ((RingedSpaceModuleAdjunction.modulePullback f).obj H).val.presheaf
      ((RingedSpaceModuleAdjunction.opensMap f).obj V) x hxV uH
    have hsec : (ψ.app (op ((RingedSpaceModuleAdjunction.opensMap f).obj V))).hom uG =
        uH := congrArg (fun q => (q.val.app (op V)).hom s) hnat
    have hunitH : E' zH = (1 : S) ⊗ₜ[R]
        TopCat.Presheaf.germ H.val.presheaf V (f.hom.base x) hxV
          ((φ.val.app (op V)).hom s) :=
      hE' V hxV ((φ.val.app (op V)).hom s)
    have hφgerm : a m = TopCat.Presheaf.germ H.val.presheaf V (f.hom.base x) hxV
        ((φ.val.app (op V)).hom s) := by
      rw [← hs]
      exact TopCat.Presheaf.stalkFunctor_map_germ_apply' V (f.hom.base x) hxV
        ((PresheafOfModules.toPresheaf
          (Y.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})).map φ.val) s
    change E' (b (E.symm (1 ⊗ₜ[R] m))) = teS (1 ⊗ₜ[R] m)
    rw [hz, hmap, hsec]
    change E' zH = teS (1 ⊗ₜ[R] m)
    have hte : teS (1 ⊗ₜ[R] m) = (1 : S) ⊗ₜ[R] a m := by
      change (1 : S) ⊗ₜ[R] (LinearEquiv.ofBijective a hφ m) =
        (1 : S) ⊗ₜ[R] a m
      rfl
    rw [hunitH, hte, hφgerm]
  have hmaps : ∀ z : TensorProduct R S M, lhs z = teS z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp [hz, hw]
    | tmul s m =>
        rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, map_smul, hgen]
  have hcomm (n : N) : E' (b n) = te (E n) := by
    have hh : E' (b (E.symm (E n))) = te (E n) := hmaps (E n)
    rwa [E.symm_apply_apply] at hh
  refine ⟨fun n₁ n₂ h => E.injective (te.injective
    (((hcomm n₁).symm.trans (congrArg E' h)).trans (hcomm n₂))), fun n' => ?_⟩
  obtain ⟨t, ht⟩ := te.surjective (E' n')
  obtain ⟨n, hn⟩ := E.surjective t
  exact ⟨n, E'.injective (((hcomm n).trans (congrArg te hn)).trans ht)⟩

/-- For a flat morphism `f : Y ⟶ X` of Noetherian schemes, the pullback of the canonical
depth-one quotient of a coherent module along a specialization-closed set `T` is a depth-one
quotient along `f ⁻¹' T`. -/
@[stacks 0DX3 "flat_pullback", ega "IV 5.9.4" "Noetherian, coherent F"]
public theorem isDepthOneQuotient_pullback
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : Y ⟶ X) [Flat f]
    (T : Set X) (hT : StableUnderSpecialization T)
    (F : X.Modules) [F.IsCoherent] :
    IsDepthOneQuotient (f.base ⁻¹' T)
      ((Scheme.Modules.pullback f).map
        (toDepthOneQuotient X T hT F)) := by
  let g := toDepthOneQuotient X T hT F
  have hspec := depthOneQuotient_spec X T hT F
  let : (depthOneQuotient X T hT F).IsCoherent := hspec.1
  have : Epi g := hspec.2.1
  unfold IsDepthOneQuotient
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isCoherent_pullback f _
  · infer_instance
  · intro y hy
    have hiso := hspec.2.2.1 (f.base y) (by simpa using hy)
    have hbij : Function.Bijective
        (stalkMapLinear (R := X.presheaf)
          F.val
          (depthOneQuotient X T hT F).val
          g.val (f.base y)) :=
      (ConcreteCategory.isIso_iff_bijective
        ((TopCat.Presheaf.stalkFunctor Ab.{u} (f.base y)).map g.mapPresheaf)).mp hiso
    have hpb := modulePullback_stalkMap_bijective f.toLRSHom.toShHom
      F (depthOneQuotient X T hT F) g y hbij
    let q := (TopCat.Presheaf.stalkFunctor Ab.{u} y).map
      (Scheme.Modules.Hom.mapPresheaf ((Scheme.Modules.pullback f).map g))
    exact (ConcreteCategory.isIso_iff_bijective q).mpr hpb
  · intro y hy
    let G := depthOneQuotient X T hT F
    let R := X.presheaf.stalk (f.base y)
    let S := Y.presheaf.stalk y
    let M := TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f.base y)
    let N := TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pullback f).obj G).val.presheaf y
    let :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) G.val (f.base y)
    let :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) ((Scheme.Modules.pullback f).obj G).val y
    let : Algebra R S := (f.stalkMap y).hom.toAlgebra
    let : IsNoetherianRing R := inferInstance
    let : IsNoetherianRing S := inferInstance
    have hyT : f.base y ∈ T := by simpa using hy
    have hdepth : 1 ≤ Module.depth R (IsLocalRing.maximalIdeal R) M :=
      hspec.2.2.2 (f.base y) hyT
    let : G.IsFiniteType := IsCoherent.toIsFiniteType G
    have : Module.Finite R M :=
      SheafOfModules.finite_stalk X.sheaf G (f.base y)
    have : IsLocalHom (algebraMap R S) := by
      rw [RingHom.algebraMap_toAlgebra]
      infer_instance
    have : Module.Flat R S := Flat.stalkMap f y
    have hformula := Module.depth_tensorProduct_of_flat (R := R) (S := S)
      (M := M) (N := S)
    obtain ⟨E, -⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
      f.toLRSHom.toShHom G y
    have hdepthEq : Module.depth S (IsLocalRing.maximalIdeal S) N =
        Module.depth S (IsLocalRing.maximalIdeal S) (TensorProduct R S M) :=
      Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal S) E
    have hTensor : 1 ≤ Module.depth S (IsLocalRing.maximalIdeal S)
        (TensorProduct R S M) := by
      rw [hformula]
      exact le_trans hdepth (le_add_of_nonneg_right (by positivity))
    change 1 ≤ Module.depth S (IsLocalRing.maximalIdeal S) N
    rwa [hdepthEq]

/-- **Stacks Project, Tag 0DX3**, flat pullback. For a flat morphism `f : Y ⟶ X` of Noetherian
schemes, `f^*F ⟶ f^*F'` is the depth-one quotient of `f^*F` along `f ⁻¹' T`: the canonical
depth-one quotient of the coherent module `f^*F` along `f ⁻¹' T` is identified with the pullback
of the canonical depth-one quotient of `F` along `T` by a unique isomorphism over `f^*F`. -/
@[stacks 0DX3 "flat_pullback"]
public theorem depthOneQuotient_pullback_unique
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : Y ⟶ X) [Flat f]
    (T : Set X) (hT : StableUnderSpecialization T)
    (F : X.Modules) [F.IsCoherent] :
    letI : ((Scheme.Modules.pullback f).obj F).IsCoherent := isCoherent_pullback f F
    ∃! e : depthOneQuotient Y (f.base ⁻¹' T) (hT.preimage f.base.hom.continuous)
        ((Scheme.Modules.pullback f).obj F) ≅
        (Scheme.Modules.pullback f).obj (depthOneQuotient X T hT F),
      toDepthOneQuotient Y (f.base ⁻¹' T) (hT.preimage f.base.hom.continuous)
          ((Scheme.Modules.pullback f).obj F) ≫ e.hom =
        (Scheme.Modules.pullback f).map (toDepthOneQuotient X T hT F) := by
  let : ((Scheme.Modules.pullback f).obj F).IsCoherent := isCoherent_pullback f F
  exact depthOneQuotient_unique Y (f.base ⁻¹' T) (hT.preimage f.base.hom.continuous)
    ((Scheme.Modules.pullback f).obj F) _ _ (isDepthOneQuotient_pullback f T hT F)

end AlgebraicGeometry

end

