module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationLinearIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleSections

/-!
# The sections `1 ⊗ a` of the ideal of a deformation

For a deformation `X' ⟶ Spec A` of `x₀ = (X₀ ⟶ Spec k)` over an algebra with square-zero residue
kernel `𝔪_A`, the ideal of the extension of `x` on `X₀` is `𝒪_{X₀} ⊗_k 𝔪_A`
(`AlgebraicGeometry.Space.deformationBaseExtensionLinearIdealIso`). This file follows the
sections `1 ⊗ a`, `a ∈ 𝔪_A`, through the algebraic part of that identification: they are the
sections `1 ⊗ (1 ⊗ a')` of `𝒪_{X₀} ⊗_R (R ⊗_{R'} I)`, `R' = Γ(Spec A)`, `R = Γ(Spec k)`,
`I = Ker(R' → R)`, `a' ∈ I` the function `a` on `Spec A`. This is the first half of the
computation of the map of ideals of a morphism of deformations in the proof of
[Stacks Project, Tag 0D1K].

## Main results

* `AlgebraicGeometry.Space.baseRingTensorSection_deformationBaseExtensionLinearIdealIso_inv`.

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
-/

@[expose] public noncomputable section

open CategoryTheory Deformation Deformation.Artin

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Range

/-- The identification of the modules of two equal ideals keeps the underlying elements. -/
theorem ModuleCat.eqToHom_ideal_val {R : Type u} [CommRing R] {I J : Ideal R} (h : I = J) (c : I) :
    ((eqToHom (congrArg (fun I : Ideal R => ModuleCat.of R I) h)).hom c : J).1 = c.1 := by
  subst h
  rfl

variable {T T' : BigFppfOver B S hS} (j : T ⟶ T')
  (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j))
  (hψ : Function.Surjective (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom)
  (hsq : RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom ^ 2 = ⊥)

/-- `R ⊗_{R'} I ≅ I` sends `1 ⊗ c` to `c`. -/
theorem rangeConormalBaseModuleIso_hom_unit
    (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)) :
    (show RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom from
      (rangeConormalBaseModuleIso B S hS j hj hψ hsq).hom.hom
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).unit.app
          (ModuleCat.of _ (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)))).hom c)).1 =
      c.1 := by
  have : Fact (Function.Surjective
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom) := ⟨hψ⟩
  let adj := ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom
  let g := (eqToIso (congrArg (fun I : Ideal (baseRing B S hS T') => ModuleCat.of _ I)
        (closedSubspaceBaseIdeal_rangeSubspace B S hS j hj)) ≪≫
      (RingHom.restrictScalarsSquareZeroKerIso _ hψ hsq).symm).hom
  have hn := congrArg (fun k => k.hom c) (adj.unit.naturality g)
  have ht := congrArg (fun k => k.hom (g.hom c)) (adj.right_triangle_components
    (RingHom.squareZeroKer _ hψ hsq))
  dsimp only at hn ht
  change (show RingHom.ker _ from (adj.counit.app _).hom
    (((ModuleCat.extendScalars.{u, u, u} _).map g).hom ((adj.unit.app _).hom c))).1 = c.1
  refine (congrArg (fun z => (show RingHom.ker
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom from
      (adj.counit.app (RingHom.squareZeroKer _ hψ hsq)).hom z).1) hn.symm).trans ?_
  refine (congrArg (fun z => (show RingHom.ker
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom from z).1) ht).trans ?_
  exact ModuleCat.eqToHom_ideal_val (closedSubspaceBaseIdeal_rangeSubspace B S hS j hj) c

/-- `I ≅ R ⊗_{R'} I` sends `c` to `1 ⊗ c`. -/
theorem rangeConormalBaseModuleIso_inv_apply (b : RingHom.squareZeroKer _ hψ hsq) :
    (rangeConormalBaseModuleIso B S hS j hj hψ hsq).inv.hom b =
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).unit.app
          (ModuleCat.of _ (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)))).hom
        ⟨(b : RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).1,
          by rw [closedSubspaceBaseIdeal_rangeSubspace]; exact b.2⟩ := by
  have h : (rangeConormalBaseModuleIso B S hS j hj hψ hsq).hom.hom
      (((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).unit.app
          (ModuleCat.of _ (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)))).hom
        ⟨(b : RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).1,
          by rw [closedSubspaceBaseIdeal_rangeSubspace]; exact b.2⟩) = b :=
    Subtype.ext (rangeConormalBaseModuleIso_hom_unit B S hS j hj hψ hsq _)
  exact (congrArg (rangeConormalBaseModuleIso B S hS j hj hψ hsq).inv.hom h.symm).trans
    ((rangeConormalBaseModuleIso B S hS j hj hψ hsq).hom_inv_id_apply _)

end Range

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {y₀ : CartesianProperFlatSpaces B S hS}
  {hy₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj y₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  (x : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) y₀ hy₀)
  (hsq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥)

/-- **The sections `1 ⊗ a` of `𝒪_{X₀} ⊗_k 𝔪_A`, in the ideal of a deformation**: through
`AlgebraicGeometry.Space.deformationBaseExtensionLinearIdealIso` they are the sections
`1 ⊗ (1 ⊗ a')` of `𝒪_{X₀} ⊗_R (R ⊗_{R'} I)`, `a'` the function `a` on `Spec A`. -/
theorem baseRingTensorSection_deformationBaseExtensionLinearIdealIso_inv
    (a : RingHom.squareZeroKer (residueMap x.algebra) (residueMap_surjective' x.algebra) hsq) :
    baseRingTensorSection B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))
        (RingHom.squareZeroKer (residueMap x.algebra) (residueMap_surjective' x.algebra) hsq) a ≫
        (deformationBaseExtensionLinearIdealIso B S hS x hsq).inv =
      baseRingTensorSection B S hS y₀.obj.obj.left
          (baseRingHomOfMap (baseStructureMap B S hS (y₀ := y₀)))
          (rangeConormalBaseModule B S hS (deformationBaseImmersion B S hS x)
            (isClosedImmersion_deformationBaseImmersion B S hS x hsq))
          ((rangeConormalBaseModuleIso B S hS (deformationBaseImmersion B S hS x)
            (isClosedImmersion_deformationBaseImmersion B S hS x hsq)
            (deformationBaseImmersion_Γ_surjective B S hS x)
            (deformationBaseImmersion_Γ_ker_sq B S hS x hsq)).inv.hom
            ((RingHom.squareZeroKerRingEquivIso _ _ (deformationAlgebraEquiv B S hS x)
              (baseResidueFieldEquiv B S hS hy₀) (deformationBaseImmersion_Γ_comp B S hS x)
              (deformationBaseImmersion_Γ_surjective B S hS x)
              (deformationBaseImmersion_Γ_ker_sq B S hS x hsq)
              (residueMap_surjective' x.algebra) hsq).inv.hom a :
                RingHom.squareZeroKer _ (deformationBaseImmersion_Γ_surjective B S hS x)
                  (deformationBaseImmersion_Γ_ker_sq B S hS x hsq))) ≫
        (deformationBaseExtensionIdealIso B S hS x hsq).inv := by
  have aux : ∀ {C : Type (u + 1)} [Category.{u + 1} C] {U P Q Q' Q'' A' : C}
      (σ : U ⟶ A') (I : P ≅ Q) (m₁ : Q ≅ Q') (e : Q'' ≅ Q') (m₂ : Q'' ≅ A'),
      σ ≫ (I ≪≫ m₁ ≪≫ e.symm ≪≫ m₂).inv = ((σ ≫ m₂.inv ≫ e.hom) ≫ m₁.inv) ≫ I.inv := by
    intros
    simp
  refine (aux _ (deformationBaseExtensionIdealIso B S hS x hsq) _ _ _).trans ?_
  refine congrArg (· ≫ _) ?_
  let REI := RingHom.squareZeroKerRingEquivIso _ _ (deformationAlgebraEquiv B S hS x)
    (baseResidueFieldEquiv B S hS hy₀) (deformationBaseImmersion_Γ_comp B S hS x)
    (deformationBaseImmersion_Γ_surjective B S hS x)
    (deformationBaseImmersion_Γ_ker_sq B S hS x hsq) (residueMap_surjective' x.algebra) hsq
  have h1 := baseRingTensorSection_map B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))
    REI.inv a
  have h2 := baseRingTensorSection_restrictScalarsIso_hom B S hS y₀.obj.obj.left
    (baseRingHomOfMap (baseStructureMap B S hS (y₀ := y₀)))
    (baseResidueFieldEquiv B S hS hy₀).surjective
    (RingHom.squareZeroKer _ (deformationBaseImmersion_Γ_surjective B S hS x)
      (deformationBaseImmersion_Γ_ker_sq B S hS x hsq)) (REI.inv.hom a)
  have h3 := baseRingTensorSection_map B S hS y₀.obj.obj.left
    (baseRingHomOfMap (baseStructureMap B S hS (y₀ := y₀)))
    (rangeConormalBaseModuleIso B S hS (deformationBaseImmersion B S hS x)
      (isClosedImmersion_deformationBaseImmersion B S hS x hsq)
      (deformationBaseImmersion_Γ_surjective B S hS x)
      (deformationBaseImmersion_Γ_ker_sq B S hS x hsq)).inv (REI.inv.hom a)
  exact (congrArg (· ≫ _) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) h1).trans h2))).trans h3

end AlgebraicGeometry.Space

end
