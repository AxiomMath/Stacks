module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.Classification
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.FibreRing
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CodimensionOneIso

/-!
# Points of tame covers of `𝐆_m` factor through the Kummer tower

For a tame cover `Y` of `𝐆_{m,k}` and a point `y` of its fibre at the geometric generic point, the
ring map `Γ(Y) → Ω` of `y` takes values in the image of the base point
`k₀^{(m)} : 𝔽_{m!}[X]_X → Ω` of a layer of the Kummer tower. This is
`exists_forall_mem_range_towerPoint` for the structure map `k[x]_x → Γ(Y)`, which is finite and
étale, and tame at `0` and `∞` since `Y ≅ Spec Γ(Y)` over `𝐆_m`.

## Main results

* `AlgebraicGeometry.TameMultiplicativeGroup.exists_forall_mem_range_towerPoint_of_fiber`.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial

universe u

namespace AlgebraicGeometry.TameMultiplicativeGroup

variable {k : Type u} [Field k]

/-- The spectrum of the structure map `k[x]_x → Γ(Y)` is the structure morphism `Y → 𝐆_m`,
precomposed with `Spec Γ(Y) ≅ Y`. -/
theorem specMap_strHom (Y : FiniteEtaleOver (Gm k)) :
    Spec.map (strHom Y) = Y.left.isoSpec.inv ≫ homGm Y := by
  rw [hom_eq_strHom, Iso.inv_hom_id_assoc]

/-- The structure map `k[x]_x → Γ(Y)` of a finite étale cover is finite. -/
theorem finite_strHom (Y : FiniteEtaleOver (Gm k)) : (strHom Y).hom.Finite := by
  have : IsFinite (homGm Y) := Y.prop.1
  rw [← IsFinite.SpecMap_iff, specMap_strHom]
  infer_instance

/-- The structure map `k[x]_x → Γ(Y)` of a finite étale cover is formally unramified. -/
theorem formallyUnramified_strHom (Y : FiniteEtaleOver (Gm k)) :
    (strHom Y).hom.FormallyUnramified := by
  have : Etale (homGm Y) := Y.prop.2
  have h : Etale (Spec.map (strHom Y)) := by
    rw [specMap_strHom]
    infer_instance
  exact ((HasRingHomProperty.Spec_iff (P := @Etale)).mp h).formallyUnramified

/-- If a cover `Y → 𝐆_m` is tamely ramified in codimension one along `j`, then so is
`Spec Γ(Y) → Spec k[x]_x`. -/
theorem isTamelyRamifiedInCodimensionOne_strHom {Y : FiniteEtaleOver (Gm k)}
    {j : Gm k ⟶ Spec (.of k[X])}
    (h : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne j Y.hom) :
    Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne j
      (Spec.map (CommRingCat.ofHom (strHom Y).hom)) :=
  Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne.of_iso (Iso.refl _) Y.left.isoSpec
    (Category.id_comp _) (by
      rw [Iso.refl_hom, Category.comp_id, CommRingCat.ofHom_hom]
      exact (hom_eq_strHom Y).symm) h

/-- For a point `y` of `Y` over the geometric generic point, the composite `k[x]_x → Γ(Y) → Ω`
is the base map `baseHom k`. -/
theorem pointRingHom_comp_strHom {Y : FiniteEtaleOver (Gm k)}
    (y : Spec (CommRingCat.of (Omega k)) ⟶ Y.left)
    (hy : y ≫ homGm Y = (genericGeometricPoint k).hom) :
    (pointRingHom y).hom.comp (strHom Y).hom = baseHom k :=
  congrArg CommRingCat.Hom.hom ((comp_hom_eq_iff y).mp hy)

variable [Fintype k]

/-- **Classification of tame covers of `𝐆_m`.** The ring map `Γ(Y) → Ω` of a point of the fibre of
a tame cover `Y` at the geometric generic point takes values in the image of a base point
`k₀^{(m)} : 𝔽_{m!}[X]_X → Ω` of the Kummer tower. -/
theorem exists_forall_mem_range_towerPoint_of_fiber (Y : TameCover k)
    (y : (tameFiberFunctor k).obj Y) :
    ∃ m, ∀ c, (pointRingHom y.1).hom c ∈ (towerPoint k m).range :=
  exists_forall_mem_range_towerPoint (strHom Y.obj).hom (finite_strHom Y.obj)
    (formallyUnramified_strHom Y.obj) (pointRingHom y.1).hom
    (pointRingHom_comp_strHom y.1 y.2) (isTamelyRamifiedInCodimensionOne_strHom Y.property.1)
    (isTamelyRamifiedInCodimensionOne_strHom Y.property.2)

end AlgebraicGeometry.TameMultiplicativeGroup

end
