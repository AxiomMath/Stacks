module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.BoundaryDivisorDualityReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.BoundaryPurityComplexVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurvePuritySupport
public import StacksFrontier.Algebra.Homology.DerivedCategory.TwoTermTruncationConnecting
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle

/-!
# The Gysin trace of an étale boundary divisor does not vanish

Let `f̄ : X̄ ⟶ S` be proper and smooth of relative dimension one with geometrically irreducible
fibres, over `S` smooth over an algebraically closed field `k`, `i : Z ⟶ X̄` a nonempty closed
subscheme finite étale over `S`, `ℓ` a prime invertible in `k` and `Λ = ℤ/ℓ`. For a purity class
`γ ∈ Ext²_X̄(i_* Λ_Z, f̄⁻¹ Λ)` and a trace `t : Rf̄_* Λ ⟶ Λ[-2]` inducing an isomorphism on `R²`,
the Gysin trace `t ∘ Rf̄_*(γ) : Rf̄_*(i_* Λ_Z) ⟶ Λ` is nonzero
(`Stacks.EtaleCohomology.boundaryGysinTrace_ne_zero`).

Let `j : U ⟶ X̄` be the complement of `Z` and `X = R j_*(j⁻¹ f̄⁻¹ Λ)`, with cohomology in degrees
`0` and `1` (`(P2)`), `H⁰ X = f̄⁻¹ Λ` (`(P0)`) and `H¹ X` supported on `Z`. The truncation
triangle `τ^{<1} X ⟶ X ⟶ τ^{≥1} X ⟶` carried by `Rf̄_*` gives the exact sequence
`R⁰f̄_*(H¹ X) ⟶ R² f̄_* Λ ⟶ H²(Rf̄_* X)`. At the geometric point over a point under `Z` the last
term vanishes
(`Stacks.EtaleCohomology.isZero_inverseImage_homology_two_derivedDirectImage_purityComplex`),
so the connecting map is onto there, while `R² f̄_* Λ ≅ Λ` is not zero. But if the Gysin trace
vanished, so would every class `Ext²(H¹ X, f̄⁻¹ Λ) = Ext⁰(i⁻¹ H¹ X, Λ_Z) ∘ γ` after `t`, in
particular `t` on the connecting map.

For `Z` irreducible this gives `Stacks.EtaleCohomology.BoundaryDivisorGysinTraceInput` on `Z`
(`Stacks.EtaleCohomology.isIso_boundaryGysinTraceAdjoint_of_irreducibleSpace`).

This is the nonvanishing of the Gysin trace in the duality along the boundary divisor of a
relative curve, part of the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.RelativeDuality.isZero_map_homology_of_comp_shift_eq_zero`.
* `Stacks.RelativeDuality.traceMap_singleFunctor_one_eq_zero`.
* `Stacks.EtaleCohomology.traceMap_eq_zero_of_gysinTrace_eq_zero`.
* `Stacks.EtaleCohomology.boundaryGysinTrace_ne_zero`.
* `Stacks.EtaleCohomology.isIso_boundaryGysinTraceAdjoint_of_irreducibleSpace`.

## Implementation notes

The statements consume the derived direct images in the standard model
`HasDerivedCategory.standard` of the derived category, as a local instance, as do their consumers
in `Stacks.EtaleCohomology.relativeCurveDualityInput_of_inputs`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian CategoryTheory.Pretriangulated
open AlgebraicGeometry

universe u

namespace Stacks.RelativeDuality

/-! ### The connecting map of a triangle, at a point -/

section Connecting

variable {𝒜 𝒜' : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜] [Category* 𝒜']
  [Abelian 𝒜'] (G : 𝒜 ⥤ 𝒜') [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **A morphism out of the first vertex killing the connecting map dies on `H²` at the points
where the middle vertex has no `H²`**: for a distinguished triangle `T` and
`κ = κ₂ ∘ κ₁ : T.obj₁ ⟶ L'` inducing an isomorphism on `H²` with `T.mor₃ ≫ κ[1] = 0`, an exact
functor `G` killing `H²(T.obj₂)` kills `H²(L')`. In the long exact sequence the connecting map
`H¹(T.obj₃) ⟶ H²(T.obj₁)` is followed by `H²(T.obj₂)`, so it is onto after `G`; composed with
`H²(κ)` it is `H²` of `T.mor₃ ≫ κ[1] = 0`. -/
theorem isZero_map_homology_of_comp_shift_eq_zero (T : Triangle (DerivedCategory 𝒜))
    (hT : T ∈ distTriang _) {L₁ L' : DerivedCategory 𝒜} (κ₁ : T.obj₁ ⟶ L₁) (κ₂ : L₁ ⟶ L')
    (hκ₁ : IsIso ((DerivedCategory.homologyFunctor 𝒜 2).map κ₁))
    (hκ₂ : IsIso ((DerivedCategory.homologyFunctor 𝒜 2).map κ₂))
    (h0 : T.mor₃ ≫ κ₁⟦(1 : ℤ)⟧' ≫ κ₂⟦(1 : ℤ)⟧' = 0)
    (hZ : IsZero (G.obj ((DerivedCategory.homologyFunctor 𝒜 2).obj T.obj₂))) :
    IsZero (G.obj ((DerivedCategory.homologyFunctor 𝒜 2).obj L')) := by
  let κ := κ₁ ≫ κ₂
  have hκ : IsIso ((DerivedCategory.homologyFunctor 𝒜 2).map κ) := by
    rw [Functor.map_comp]
    infer_instance
  replace h0 : T.mor₃ ≫ κ⟦(1 : ℤ)⟧' = 0 := by
    rw [Functor.map_comp]
    exact h0
  let δ : (DerivedCategory.homologyFunctor 𝒜 1).obj T.obj₃ ⟶
      (DerivedCategory.homologyFunctor 𝒜 2).obj T.obj₁ :=
    (DerivedCategory.homologyFunctor 𝒜 0).homologySequenceδ T 1 2 rfl
  have hex := ((DerivedCategory.homologyFunctor 𝒜 0).homologySequence_exact₁ T hT 1 2 rfl).map G
  have hepi : Epi (G.map δ) := hex.epi_f (hZ.eq_of_tgt _ _)
  have hcomp : δ ≫ (DerivedCategory.homologyFunctor 𝒜 2).map κ = 0 := by
    change (DerivedCategory.homologyFunctor 𝒜 0).shiftMap T.mor₃ 1 2 _ ≫
      ((DerivedCategory.homologyFunctor 𝒜 0).shift 2).map κ = 0
    rw [← Functor.shiftMap_comp, h0, Functor.shiftMap_zero]
  have h2 : G.map ((DerivedCategory.homologyFunctor 𝒜 2).map κ) = 0 :=
    (cancel_epi (G.map δ)).1 (by rw [comp_zero, ← G.map_comp, hcomp, G.map_zero])
  have : Epi (0 : G.obj ((DerivedCategory.homologyFunctor 𝒜 2).obj T.obj₁) ⟶
      G.obj ((DerivedCategory.homologyFunctor 𝒜 2).obj L')) := by
    rw [← h2]
    infer_instance
  exact IsZero.of_epi_zero (G.obj ((DerivedCategory.homologyFunctor 𝒜 2).obj T.obj₁)) _

end Connecting

/-! ### Trace maps at a sheaf placed in degree one -/

section SingleOne

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]
  {C' : Type*} [Category* C'] [Preadditive C'] [HasShift C' ℤ]
  [∀ n : ℤ, (shiftFunctor C' n).Additive]
  (Φ : DerivedCategory.Plus 𝒜 ⥤ C') [Φ.CommShift ℤ] [Φ.Additive]
  {B : DerivedCategory.Plus 𝒜} {L : C'} (t : ShiftedHom (Φ.obj B) L (-2))

/-- **A trace map vanishing in degree `2` at `M[0]` vanishes in degree `1` at `M[-1]`**: every
`b : M[-1] ⟶ B[1]` is `σ ∘ c[-1]` for some `c : M[0] ⟶ B[2]`, `σ : M[-1] ≅ M[0][-1]` the shift
isomorphism of the single functors. -/
theorem traceMap_singleFunctor_one_eq_zero (M : 𝒜)
    (h0 : ∀ c : ShiftedHom ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj M) B (2 : ℤ),
      traceMap Φ t _ 2 0 (by norm_num) c = 0)
    (b : ShiftedHom ((DerivedCategory.Plus.singleFunctor 𝒜 1).obj M) B (1 : ℤ)) :
    traceMap Φ t _ 1 (-1) (by norm_num) b = 0 := by
  let σ := ((DerivedCategory.Plus.singleFunctors 𝒜).shiftIso (-1) 1 0 (by norm_num)).app M
  let σ' : ShiftedHom ((DerivedCategory.Plus.singleFunctor 𝒜 1).obj M)
      ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj M) (-1 : ℤ) := σ.inv
  obtain ⟨c, hc⟩ := (shiftFunctor (DerivedCategory.Plus 𝒜) (-1 : ℤ)).map_surjective
    (σ.hom ≫ b ≫ (shiftFunctorAdd' (DerivedCategory.Plus 𝒜) (2 : ℤ) (-1) 1 (by norm_num)).hom.app B)
  have hb : b = σ'.comp c (by norm_num : (2 : ℤ) + (-1) = 1) := by
    simp only [σ', ShiftedHom.comp, hc, Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
      Iso.inv_hom_id_assoc]
  have he : traceMap Φ t _ 1 (-1) (by norm_num) (σ'.comp c (by norm_num : (2 : ℤ) + (-1) = 1)) =
      (σ'.map Φ).comp (traceMap Φ t _ 2 0 (by norm_num) c) (by norm_num : (0 : ℤ) + (-1) = -1) := by
    simp only [traceMap_apply, ShiftedHom.map_comp]
    exact ShiftedHom.comp_assoc _ _ _ _ _ (by omega)
  rw [hb, he, h0 c, ShiftedHom.comp_zero]

end SingleOne

end Stacks.RelativeDuality

namespace Stacks.EtaleCohomology

open Stacks.EtaleCohomology.ExtensionTorsor Stacks.RelativeDuality

attribute [local instance] HasDerivedCategory.standard

/-! ### Classes out of a sheaf supported on the divisor -/

section Purity

variable (ℓ : ℕ) [Fact ℓ.Prime] {S Xbar Z : Scheme.{u}} (fbar : Xbar ⟶ S) (i : Z ⟶ Xbar)
  [IsClosedImmersion i]

/-- **A vanishing Gysin trace kills every class out of a sheaf supported on `Z`**: for a purity
class `γ ∈ Ext²_X̄(i_* Λ_Z, f̄⁻¹ Λ)` with `t ∘ Rf̄_*(γ) = 0`, and a sheaf `A` on `X̄` with
`A ≅ i_* i⁻¹ A`, every `c ∈ Ext²_X̄(A, f̄⁻¹ Λ)` has `t[2] ∘ Rf̄_*(c) = 0`: by purity
`c = i_*(m) ∘ γ` up to `A ≅ i_* i⁻¹ A`, for some `m ∈ Ext⁰_Z(i⁻¹ A, Λ_Z)`. -/
theorem traceMap_eq_zero_of_gysinTrace_eq_zero
    (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)) 2)
    (hγ : IsPurityClass i _ γ)
    (t : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ))))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2))
    (hτ : ((Stacks.TopTruncationExt.extPlus γ).map (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ)
      fbar ⋙ DerivedCategory.Plus.ι)).comp t (by norm_num : (-2 : ℤ) + ((2 : ℕ) : ℤ) = 0) = 0)
    (A : EtaleModules.{u, 0} (ZMod ℓ) Xbar)
    [IsIso ((etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) i).unit.app A)]
    (c : ShiftedHom ((DerivedCategory.Plus.singleFunctor _ 0).obj A)
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ))) (2 : ℤ)) :
    traceMap (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι) t _ 2 0
      (by norm_num) c = 0 := by
  let u₀ := (etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) i).unit.app A
  obtain ⟨ε, hε⟩ := (Stacks.HomologicalDuality.extPlus_bijective A
    ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)) 2).2 c
  obtain ⟨m, hm⟩ := (hγ.1 ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) i).obj A) 0).2
    ((Ext.mk₀ (inv u₀)).comp ε (zero_add 2))
  have hm' : (m.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)).comp γ (zero_add 2) =
      (Ext.mk₀ (inv u₀)).comp ε (zero_add 2) := hm
  let y := (Ext.mk₀ u₀).comp (m.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i))
    (zero_add 0)
  have hy : ε = y.comp γ (zero_add 2) := by
    simp only [y]
    rw [Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 2) (zero_add 2), hm',
      Ext.mk₀_comp_mk₀_assoc, IsIso.hom_inv_id, Ext.mk₀_id_comp]
  rw [← hε, hy, Stacks.TopTruncationExt.extPlus_comp]
  rw [traceMap_comp_shiftedHom t _ (by norm_num : (-2 : ℤ) + ((2 : ℕ) : ℤ) = 0) _ (by omega)
    (by norm_num) (by norm_num), hτ, traceMap_apply, ShiftedHom.comp_zero]

end Purity

/-! ### The Gysin trace does not vanish -/

section Nonzero

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **The Gysin trace of a nonempty étale boundary divisor is nonzero.** Let `f̄ : X̄ ⟶ S` be
proper and smooth of relative dimension one with geometrically irreducible fibres, over `S` smooth
over a field `k` in which `ℓ` is invertible, and `i : Z ⟶ X̄` a closed immersion with `Z` nonempty
and finite étale over `S`. For a purity class `γ ∈ Ext²_X̄(i_* Λ_Z, f̄⁻¹ Λ)` and a trace
`t : Rf̄_*(f̄⁻¹ Λ) ⟶ Λ[-2]` inducing an isomorphism on `R²`, `t ∘ Rf̄_*(γ) ≠ 0`. -/
theorem boundaryGysinTrace_ne_zero (k : Type u) [Field k] (hℓ : IsUnit (ℓ : k))
    {S Xbar Z : Scheme.{u}} (q : S ⟶ Spec (.of k)) [Smooth q] (fbar : Xbar ⟶ S)
    [SmoothOfRelativeDimension 1 fbar] [IsProper fbar] [GeometricallyIrreducible fbar]
    (i : Z ⟶ Xbar) [IsClosedImmersion i] [IsFinite (i ≫ fbar)] [Etale (i ≫ fbar)] [Nonempty Z]
    (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)) 2)
    (hγ : IsPurityClass i _ γ)
    (t : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ))))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2))
    (ht : IsIso ((DerivedCategory.homologyFunctor _ 2).map t)) :
    ((Stacks.TopTruncationExt.extPlus γ).map (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ)
      fbar ⋙ DerivedCategory.Plus.ι)).comp t (by norm_num : (-2 : ℤ) + ((2 : ℕ) : ℤ) = 0) ≠ 0 := by
  intro hτ
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨z⟩ := ‹Nonempty Z›
  let y := (i ≫ fbar).base z
  let s := (GeometricPoint.ofPoint S y).hom
  let Gs := etaleModuleInverseImage.{u, 0} (ZMod ℓ) s
  -- the complement of `Z`
  let O : Xbar.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let j := O.ι
  have hj : Set.range j.base = (Set.range i.base)ᶜ := Scheme.Opens.range_ι O
  have : IsLocallyNoetherian Xbar := LocallyOfFiniteType.isLocallyNoetherian (fbar ≫ q)
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian q
  let H := (etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)
  have hH : lccModules Xbar ℓ H :=
    lccModules_etaleModuleInverseImage ℓ fbar _
      (Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_constantSheaf _ _
        (by rw [ModuleCat.isFG_iff]; exact Module.Finite.of_finite))
  let X := (purityComplex (ZMod ℓ) j).obj H
  have hP0 := Purity.purityUnitIso_of_affineLine k ℓ hℓ (Purity.affineLineConstantUnitIso k) q
    fbar i j hj H hH
  have hP2 := Purity.purityHigherDirectImageVanishing_of_affineLine k ℓ hℓ
    (Purity.affineLineTorsionVanishing k) q fbar i j hj H hH
  have : X.IsGE 0 := Functor.isGE_rightDerivedFunctorPlus_obj _ _ 0
  have : X.IsLE 1 := by
    have h := Stacks.BoundedCohomologicalDimension.isLE_rightDerivedFunctorPlus_single
      (etaleModuleDirectImage.{u, 0} (ZMod ℓ) j)
      ((etaleModuleRestriction.{u, 0} (ZMod ℓ) j).obj H) 1 0 (fun p hp => hP2 p (by omega))
    rw [zero_add] at h
    exact (DerivedCategory.Plus.isLE_ι_obj_iff X 1).1 h
  let F := etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι
  let B := (DerivedCategory.Plus.singleFunctor _ 0).obj H
  let X₂ := (DerivedCategory.Plus.TStructure.t.truncLT 2).obj X
  let T₀ := (DerivedCategory.Plus.TStructure.t.triangleLTGE 1).obj X₂
  have hT₀ : T₀ ∈ distTriang _ := DerivedCategory.Plus.TStructure.t.triangleLTGE_distinguished 1 X₂
  let T := F.mapTriangle.obj T₀
  have hT : T ∈ distTriang _ := F.map_distinguished _ hT₀
  -- `τ^{<1} τ^{<2} X ≅ H⁰(X)[0] ≅ f̄⁻¹ Λ[0]`
  let e₀ : (DerivedCategory.Plus.homologyFunctor _ 0).obj X ≅ H :=
    (((etaleModuleDirectImage.{u, 0} (ZMod ℓ) j).isoRightDerivedPlusSingle 0).app _).symm ≪≫
      (asIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} (ZMod ℓ) j).unit.app H)).symm
  let e₁ : T₀.obj₁ ≅ B :=
    (@asIso _ _ _ _ ((DerivedCategory.Plus.truncationConnectingTargetMap).app X)
      (DerivedCategory.Plus.isIso_truncationConnectingTargetMap_app X)) ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0).mapIso e₀
  -- `τ^{≥1} τ^{<2} X ≅ H¹(X)[-1]`, and `H¹(X)` is supported on `Z`
  let A₃ := (DerivedCategory.Plus.homologyFunctor _ 1).obj X
  let e₃ : T₀.obj₃ ≅ (DerivedCategory.Plus.singleFunctor _ 1).obj A₃ :=
    (DerivedCategory.Plus.truncGELTIsoHomologyFunctorCompSingleFunctor 1).app X
  have : IsIso ((etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) i).unit.app A₃) := by
    have hN : IsUnit ((ℓ : ℤ) : Γ(Xbar, ⊤)) := by
      have := Purity.isUnit_natCast_globalSections_of_over (k := k) (ℓ := ℓ) (fbar ≫ q) hℓ
      simpa using this
    have hu1 := Purity.isIso_unit_rightDerived_directImage_of_isOpenImmersion (NeZero.pos ℓ) hN j
      i hj ((etaleModuleRestriction.{u, 0} (ZMod ℓ) j).obj H) 1 one_pos
    let e := (Stacks.DerivedIndexing.rightDerivedIso
      (etaleModuleDirectImage.{u, 0} (ZMod ℓ) j) 1).app
        ((etaleModuleRestriction.{u, 0} (ZMod ℓ) j).obj H)
    have hnat := (etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) i).unit.naturality e.hom
    rw [CategoryTheory.Functor.id_map] at hnat
    have : IsIso (e.hom ≫ (etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) i).unit.app A₃) := by
      have h5 : e.hom ≫ (etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) i).unit.app A₃ =
          (etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) i).unit.app
            (((etaleModuleDirectImage.{u, 0} (ZMod ℓ) j).rightDerived 1).obj
              ((etaleModuleRestriction.{u, 0} (ZMod ℓ) j).obj H)) ≫
            (etaleModuleInverseImage.{u, 0} (ZMod ℓ) i ⋙
              etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).map e.hom := hnat
      rw [h5]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ hu1 (CategoryTheory.Functor.map_isIso _ e.hom)
    exact IsIso.of_isIso_comp_left e.hom _
  -- every class out of `H¹(X)[-1]` dies under the trace
  have hA : ∀ b : ShiftedHom ((DerivedCategory.Plus.singleFunctor _ 1).obj A₃) B (1 : ℤ),
      traceMap F t _ 1 (-1) (by norm_num) b = 0 :=
    traceMap_singleFunctor_one_eq_zero F t A₃
      (traceMap_eq_zero_of_gysinTrace_eq_zero ℓ fbar i γ hγ t hτ A₃)
  let δ₀ : ShiftedHom T₀.obj₃ T₀.obj₁ (1 : ℤ) := T₀.mor₃
  let b := δ₀.comp (ShiftedHom.mk₀ (0 : ℤ) rfl e₁.hom) (zero_add 1)
  have hb : traceMap F t T₀.obj₃ 1 (-1) (by norm_num) b = 0 := by
    have hfac : b = (ShiftedHom.mk₀ (0 : ℤ) rfl e₃.hom).comp
        ((ShiftedHom.mk₀ (0 : ℤ) rfl e₃.inv).comp b (add_zero 1)) (add_zero 1) := by
      rw [ShiftedHom.mk₀_comp, ShiftedHom.mk₀_comp, Iso.hom_inv_id_assoc]
    rw [hfac, traceMap_mk₀_comp, hA, ShiftedHom.comp_zero]
  -- hence `t` kills the connecting morphism
  have h1 : ((δ₀.map F).comp (ShiftedHom.mk₀ (0 : ℤ) rfl (F.map e₁.hom)) (zero_add 1)).comp t
      (by norm_num : (-2 : ℤ) + 1 = -1) = 0 := by
    simpa only [b, traceMap_apply, ShiftedHom.map_comp, ShiftedHom.map_mk₀] using hb
  rw [ShiftedHom.comp_mk₀] at h1
  let ι₀ := (shiftFunctorAdd' (DerivedCategory (EtaleModules.{u, 0} (ZMod ℓ) S))
      (-2 : ℤ) 1 (-1) (by norm_num)).inv.app
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))
  have h2 : T.mor₃ ≫ (F.map e₁.hom)⟦(1 : ℤ)⟧' ≫ t⟦(1 : ℤ)⟧' ≫ ι₀ = 0 := by
    simp only [ShiftedHom.comp, Category.assoc] at h1
    exact h1
  have h0 : T.mor₃ ≫ (F.map e₁.hom)⟦(1 : ℤ)⟧' ≫ t⟦(1 : ℤ)⟧' = 0 :=
    (cancel_mono ι₀).1 (by simpa only [Category.assoc, zero_comp] using h2)
  have := ht
  -- at the point under `z`, `H²(Rf̄_* X)` vanishes
  have hZ : IsZero (Gs.obj ((DerivedCategory.homologyFunctor _ 2).obj T.obj₂)) :=
    (isZero_inverseImage_homology_two_derivedDirectImage_purityComplex k ℓ hℓ q fbar i j hj H hH
      y ⟨z, rfl⟩).of_iso (Gs.mapIso ((DerivedCategory.Plus.homologyFunctor _ 2).mapIso
        ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar).mapIso
          (@asIso _ _ _ _ ((DerivedCategory.Plus.TStructure.t.truncLTι 2).app X)
            ((DerivedCategory.Plus.TStructure.t.isLE_iff_isIso_truncLTι_app 1 2 rfl X).1
              inferInstance)))))
  have hL := isZero_map_homology_of_comp_shift_eq_zero Gs T hT (F.mapIso e₁).hom t
    (Iso.isIso_hom ((DerivedCategory.homologyFunctor _ 2).mapIso (F.mapIso e₁))) ht h0 hZ
  -- but `R² f̄_* Λ ≅ Λ` does not vanish there
  let e₄ := (Stacks.TopTruncationExt.singleShiftHomologyIso
    (B := EtaleModules.{u, 0} (ZMod ℓ) S) 2).app (unitSheaf (X := S) ℓ)
  let e₅ := (etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) s).app
    (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))
  have hzero := hL.of_iso (Gs.mapIso e₄ ≪≫ e₅).symm
  have h1' : (1 : ZMod ℓ) • 𝟙 (unitSheaf (X := Spec (.of (GeometricPoint.ofPoint S y).residueField))
      ℓ) = 0 := by
    rw [one_smul]
    exact hzero.eq_of_src _ _
  exact one_ne_zero (Purity.eq_zero_of_smul_id_unitSheaf (N := ℓ) _ 1 h1')

/-- **The Gysin trace input for an irreducible boundary divisor**: in the setting of
`Stacks.EtaleCohomology.BoundaryDivisorGysinTraceInput`, with `Z` irreducible, the adjoint
`Λ_Z ⟶ π⁻¹ Λ` of the Gysin trace is an isomorphism
(`Stacks.EtaleCohomology.isIso_boundaryGysinTraceAdjoint_of_ne_zero`,
`Stacks.EtaleCohomology.boundaryGysinTrace_ne_zero`). -/
theorem isIso_boundaryGysinTraceAdjoint_of_irreducibleSpace (k : Type u) [Field k]
    (hℓ : IsUnit (ℓ : k)) {S Xbar Z : Scheme.{u}} (q : S ⟶ Spec (.of k)) (e : ℕ)
    [SmoothOfRelativeDimension e q] (fbar : Xbar ⟶ S) (i : Z ⟶ Xbar)
    [SmoothOfRelativeDimension 1 fbar] [GeometricallyIrreducible fbar] [IsClosedImmersion i]
    [IsFinite (i ≫ fbar)] [Etale (i ≫ fbar)] [IrreducibleSpace Z]
    (hproj : IsProjectiveMorphism fbar)
    (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)) 2)
    (hγ : IsPurityClass i _ γ)
    (t : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ))))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2))
    (ht : IsIso ((DerivedCategory.homologyFunctor _ 2).map t)) :
    IsIso (boundaryGysinTraceAdjoint ℓ fbar i γ t) := by
  have : Smooth q := SmoothOfRelativeDimension.smooth e q
  have : IsProper fbar := isProper_of_isProjectiveMorphism fbar hproj
  have : Nonempty Z := (inferInstance : IrreducibleSpace Z).toNonempty
  exact isIso_boundaryGysinTraceAdjoint_of_ne_zero ℓ fbar i γ t
    (boundaryGysinTrace_ne_zero ℓ k hℓ q fbar i γ hγ t ht)

end Nonzero

end Stacks.EtaleCohomology

end
