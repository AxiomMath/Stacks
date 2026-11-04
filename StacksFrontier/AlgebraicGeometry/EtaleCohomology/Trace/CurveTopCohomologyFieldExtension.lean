module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFieldExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSheafExcisionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicFieldExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.ImageStabilizer

/-!
# `H²_c` of a sheaf and the geometric fundamental group after a finite extension of the base

Let `X` be a separated scheme of finite type over a finite field `k` with a compactification `j`,
`k'` an extension of `k` inside `k̄`, and `g : X' = X ×_k k' ⟶ X` the projection. Then for every
sheaf `G` of `Λ`-modules on `X_étale`

`Hⁱ_c(X'_{k̄}, g⁻¹ G) ≅ Hⁱ_c(X_{k̄}, G)`,

which is `Stacks.EtaleCohomology.compactSupportFieldExtensionIso` on a sheaf placed in degree `0`.

Moreover, for `k'` finite over `k`, the image of `π₁(X', x̄') ⟶ π₁(X, x̄)` contains the geometric
fundamental group `ker(π₁(X, x̄) ⟶ π₁(Spec k))`: the image is the stabilizer of a point of the
geometric fibre of `X' ⟶ X` (`AlgebraicGeometry.range_etaleFundamentalGroupMap_eq_stabilizer`),
and `X' ⟶ X` is the base change of `Spec k' ⟶ Spec k`, on whose fibres `π₁(X, x̄)` acts through
`π₁(Spec k)`.

The statements live in the standard model `HasDerivedCategory.standard` of the derived category, in
which `Stacks.EtaleCohomology.compactSupportSheafCohomology` is defined.

## Main results

* `Stacks.EtaleCohomology.compactSupportSheafCohomologyFieldExtensionIso`:
  `Hⁱ_c(X_{k̄}, -) ≅ Hⁱ_c(X'_{k̄}, g⁻¹ -)` on sheaves, naturally.
* `AlgebraicGeometry.smul_eq_self_of_etaleFundamentalGroupMap_eq_one`: the kernel of
  `π₁(X) ⟶ π₁(Y)` acts trivially on the fibres of covers pulled back from `Y`.
* `AlgebraicGeometry.ker_le_range_etaleFundamentalGroupMap_fieldExtension`: the geometric
  fundamental group lies in the image of `π₁(X ×_k L)` for `L` finite étale over `k`.

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section Sheaf

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (k' : Type u) [Field k'] [Algebra k k']
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra k' kbar] [IsScalarTower k k' kbar]
  (i : ℤ)

/-- **`Hⁱ_c(X_{k̄}, -) ≅ Hⁱ_c(X'_{k̄}, g⁻¹ -)`** on sheaves, naturally, for `X' = X ×_k k'`. -/
def compactSupportSheafCohomologyFieldExtensionIso :
    compactSupportSheafCohomology Λ f j kbar i ≅
      etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k k')) ⋙
        compactSupportSheafCohomology Λ (pullback.snd f (specAlgebraMap k k'))
          (compactificationFieldBaseChange f j k') kbar i :=
  singlePlusHomologyIso (etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k k')))
    _ _ (NatIso.ofComponents (compactSupportFieldExtensionIso Λ f j k' kbar)
      (fun φ => compactSupportFieldExtensionIso_hom_naturality Λ f j k' kbar φ)).symm i

end Sheaf

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

section Kernel

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y] (f : X ⟶ Y)
  (x : GeometricPoint X)

/-- **The kernel of `π₁(X) ⟶ π₁(Y)` acts trivially on the fibres of covers pulled back from
`Y`.** -/
theorem smul_eq_self_of_etaleFundamentalGroupMap_eq_one (V : FiniteEtaleOver Y)
    {σ : EtaleFundamentalGroup X x} (hσ : etaleFundamentalGroupMap f x σ = 1)
    (p : (finiteEtaleFiberFunctor x).obj ((finiteEtaleBaseChange f).obj V)) : σ • p = p := by
  apply (finiteEtaleFiberProjectionEquiv f x V).injective
  change finiteEtaleFiberProjection f x V ((σ.app _).hom p) = finiteEtaleFiberProjection f x V p
  rw [etaleFundamentalGroupMap_finiteEtaleFiberProjection, hσ]
  rfl

/-- The kernel of `π₁(X) ⟶ π₁(Y)` acts trivially on the fibre of a cover of `X` isomorphic to one
pulled back from `Y`. -/
theorem smul_eq_self_of_etaleFundamentalGroupMap_eq_one_of_iso (V : FiniteEtaleOver Y)
    {W : FiniteEtaleOver X} (c : W ≅ (finiteEtaleBaseChange f).obj V)
    {σ : EtaleFundamentalGroup X x} (hσ : etaleFundamentalGroupMap f x σ = 1)
    (p : (finiteEtaleFiberFunctor x).obj W) : σ • p = p := by
  have hinj : Function.Injective ((finiteEtaleFiberFunctor x).map c.hom) := fun a b h => by
    have := congrArg ((finiteEtaleFiberFunctor x).map c.inv) h
    simpa [← Functor.map_comp_apply] using this
  apply hinj
  have hnat := ConcreteCategory.congr_hom (σ.hom.naturality c.hom) p
  change (finiteEtaleFiberFunctor x).map c.hom ((σ.app W).hom p) = _
  have h2 := smul_eq_self_of_etaleFundamentalGroupMap_eq_one f x V hσ
    ((finiteEtaleFiberFunctor x).map c.hom p)
  change (σ.app _).hom ((finiteEtaleFiberFunctor x).map c.hom p) = _ at h2
  rw [← h2]
  exact hnat.symm

end Kernel

section FieldExtension

variable {k : Type u} [Field k] {U : Scheme.{u}} [ConnectedSpace U] (f : U ⟶ Spec (.of k))
  (L : Type u) [Field L] [Algebra k L] (hs : finiteEtale (specAlgebraMap k L))
  [ConnectedSpace ↥(pullback (C := Scheme.{u}) f (specAlgebraMap k L))]
  (y : GeometricPoint (pullback (C := Scheme.{u}) f (specAlgebraMap k L)))
  (hfst : finiteEtale (pullback.fst f (specAlgebraMap k L)))

include hs hfst in
/-- **The geometric fundamental group lies in the image of `π₁(X ×_k L)`** for a finite étale
`Spec L ⟶ Spec k`. -/
theorem ker_le_range_etaleFundamentalGroupMap_fieldExtension :
    (etaleFundamentalGroupMap f (y.map (pullback.fst f (specAlgebraMap k L)))).toMonoidHom.ker ≤
      (etaleFundamentalGroupMap (pullback.fst f (specAlgebraMap k L)) y).toMonoidHom.range := by
  intro σ hσ
  rw [range_etaleFundamentalGroupMap_eq_stabilizer hfst y, MulAction.mem_stabilizer_iff]
  let SL : FiniteEtaleOver (Spec (.of k)) := finiteEtaleOverSource hs
  let c : finiteEtaleOverSource hfst ≅ (finiteEtaleBaseChange f).obj SL :=
    MorphismProperty.Over.isoMk (pullbackSymmetry f (specAlgebraMap k L))
      (pullbackSymmetry_hom_comp_snd _ _)
  exact smul_eq_self_of_etaleFundamentalGroupMap_eq_one_of_iso f _ SL c hσ _

end FieldExtension

end AlgebraicGeometry
