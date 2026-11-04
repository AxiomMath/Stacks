module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.SchemeTheoreticImage
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Gluing quasi-coherent ideal sheaves along open immersions

Let `jᵢ : Uᵢ ⟶ Y` be finitely many quasi-compact open immersions and `Zᵢ` quasi-coherent ideal
sheaves on the `Uᵢ` which agree on the overlaps `Uᵢ ×_Y Uₗ`. Then there is a quasi-coherent ideal
sheaf on `Y` restricting to `Zᵢ` on every `Uᵢ`: the intersection of the scheme-theoretic images.

## Main results

* `Stacks.LinearSystemScheme.comap_inf_of_isOpenImmersion`: restriction to an open subscheme
  commutes with finite intersections of ideal sheaves.
* `Stacks.LinearSystemScheme.exists_ideal_comap_eq`: the gluing.
* `Stacks.LinearSystemScheme.ideal_ext_of_comap`: an ideal sheaf is determined by its
  restrictions to an open cover.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.LinearSystemScheme

/-- Restriction to an open subscheme commutes with finite intersections of ideal sheaves. -/
theorem comap_iInf_of_isOpenImmersion {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {ι : Type*} [Finite ι] (I : ι → Y.IdealSheafData) :
    (⨅ i, I i).comap j = ⨅ i, (I i).comap j := by
  ext U : 2
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ideal_iInf,
    Scheme.IdealSheafData.ideal_iInf]
  simp only [iInf_apply, Ideal.comap_iInf, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]

/-- **The scheme-theoretic image of `Zᵢ ⊆ Uᵢ` in `Y`, restricted to an open `Uₗ`**, is the image
under `Uᵢ ×_Y Uₗ ⟶ Uₗ` of the restriction of `Zᵢ` to `Uᵢ ×_Y Uₗ`. -/
theorem comap_map_eq_map_comap {Y Ui Ul : Scheme.{u}} (ji : Ui ⟶ Y) (jl : Ul ⟶ Y)
    [Flat jl] [QuasiCompact ji] (Zi : Ui.IdealSheafData) :
    (Zi.map ji).comap jl = (Zi.comap (pullback.fst ji jl)).map (pullback.snd ji jl) := by
  rw [Scheme.IdealSheafData.map, ← ker_pullback_snd_eq_comap,
    ← Scheme.Hom.ker_comp_of_isIso (pullbackRightPullbackFstIso ji jl Zi.subschemeι).hom,
    pullbackRightPullbackFstIso_hom_snd, ← Scheme.IdealSheafData.map_ker]
  congr 1
  rw [← Scheme.Hom.ker_comp_of_isIso (pullbackSymmetry _ _).hom, pullbackSymmetry_hom_comp_snd,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]

/-- **Gluing ideal sheaves.** Ideal sheaves `Zᵢ` on finitely many open immersions `jᵢ : Uᵢ ⟶ Y`,
compatible on overlaps, are the restrictions of one ideal sheaf on `Y`. -/
theorem comap_iInf_map_eq {Y : Scheme.{u}} {ι : Type*} [Finite ι] {U : ι → Scheme.{u}}
    (j : ∀ i, U i ⟶ Y) [∀ i, IsOpenImmersion (j i)] [∀ i, QuasiCompact (j i)]
    (Z : ∀ i, (U i).IdealSheafData)
    (h : ∀ i l, (Z i).comap (pullback.fst (j i) (j l)) = (Z l).comap (pullback.snd (j i) (j l)))
    (l : ι) : (⨅ i, (Z i).map (j i)).comap (j l) = Z l := by
  rw [comap_iInf_of_isOpenImmersion]
  refine le_antisymm ((iInf_le _ l).trans (Scheme.IdealSheafData.comap_map_le _ _)) ?_
  refine le_iInf fun i => ?_
  rw [comap_map_eq_map_comap, h i l]
  exact Scheme.IdealSheafData.le_map_comap _ _

/-- An ideal sheaf is determined by its restrictions to a jointly surjective family of open
immersions. -/
theorem ideal_ext_of_comap {Y : Scheme.{u}} {ι : Type*} {U : ι → Scheme.{u}}
    (j : ∀ i, U i ⟶ Y) [∀ i, IsOpenImmersion (j i)] (hcov : ∀ y, ∃ i, y ∈ Set.range (j i))
    {I J : Y.IdealSheafData} (h : ∀ i, I.comap (j i) = J.comap (j i)) : I = J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun W : Σ i, (U i).affineOpens => ⟨j W.1 ''ᵁ W.2.1, W.2.2.image_of_isOpenImmersion _⟩)
    ?_ fun W => ?_
  · refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨i, x, rfl⟩ := hcov y
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      (U i).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, ⟨V, hV⟩⟩, ⟨x, hxV, rfl⟩⟩
  · have e := congrArg (fun K : (U W.1).IdealSheafData => K.ideal W.2) (h W.1)
    simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at e
    exact Ideal.comap_injective_of_surjective _
      (ConcreteCategory.bijective_of_isIso ((j W.1).appIso W.2.1).inv).2 e

end Stacks.LinearSystemScheme

end
