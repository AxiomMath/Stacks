module

public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.NormGroupTensor
public import StacksFrontier.AlgebraicGeometry.NormInvertible.ChartGeneratorRatio
public import StacksFrontier.AlgebraicGeometry.NormInvertible.PullbackGenerator
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorListGenerator

/-!
# The norm–tensor isomorphism from an identity on functions

Let `π : P ⟶ Q` be finite with a norm `Norm_π` of degree `d`, and let `a : G → (P ⟶ P)` be a
finite family of endomorphisms of `P` with `a σ ≫ π = π`. If `π^♯ ∘ Norm_π = ∏_{σ ∈ G} (a σ)^♯` on
functions, then every invertible module `ℒ` on `P` satisfies

  `π^*(Norm_π ℒ) ≅ ⨂_{σ ∈ G} (a σ)^*ℒ`,

that is, `Stacks.Divisors.HasNormGroupProductTensor` holds.

## Main results

* `Stacks.Divisors.preimage_preimage_of_comp_eq`: an endomorphism `b` with `b ≫ π = π` fixes every
  open pulled back along `π`.
* `Stacks.Divisors.generatorRatioUnit_restrict_pullbackGenerator`: the transition unit of two
  pulled-back generators, restricted to any open of the source inside the preimage, is the
  `AlgebraicGeometry.Scheme.Hom.appLE` of the transition unit upstairs.
* `Stacks.Divisors.hasNormGroupProductTensor_of_app_norm_eq_prod`: the identity on functions
  implies `Stacks.Divisors.HasNormGroupProductTensor`.

## References

* Stacks Project, Tag 0FH9: https://stacks.math.columbia.edu/tag/0FH9
* Stacks Project, Tag 0BCY: https://stacks.math.columbia.edu/tag/0BCY
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.SheafOfModules
open Stacks.Norm (MorphismNorm MorphismNormMap)

universe u

namespace Stacks.Divisors

variable {P Q : Scheme.{u}}

/-- An endomorphism of the source commuting with `π` fixes every open pulled back along `π`:
`b ⁻¹ᵁ (π ⁻¹ᵁ V) = π ⁻¹ᵁ V`. -/
theorem preimage_preimage_of_comp_eq {π : P ⟶ Q} {b : P ⟶ P} (hb : b ≫ π = π) (V : Q.Opens) :
    b ⁻¹ᵁ (π ⁻¹ᵁ V) = π ⁻¹ᵁ V :=
  (Scheme.Hom.comp_preimage b π V).symm.trans (by rw [hb])

/-- The transition unit of `f^*s` and `f^*t` over an open `A ≤ f ⁻¹ᵁ U` is the image of the
transition unit of `s` and `t` under `AlgebraicGeometry.Scheme.Hom.appLE`, the pullback along `f`
followed by restriction to `A`. -/
theorem generatorRatioUnit_restrict_pullbackGenerator {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules)
    (hL : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L)
    {U : Y.Opens} {A : X.Opens} (h : A ≤ f ⁻¹ᵁ U) (s t : GeneratorSections Y.toRingedSpace L U) :
    generatorRatioUnit ((modulePullback f.toLRSHom.toShHom).obj L) A
        (generatorRestrict _ h (pullbackGenerator f L hL U s))
        (generatorRestrict _ h (pullbackGenerator f L hL U t)) =
      Units.map (f.appLE U A h).hom.toMonoidHom (generatorRatioUnit L U s t) :=
  (generatorRatioUnit_restrict _ h (pullbackGenerator f L hL U s)
      (pullbackGenerator f L hL U t)).trans
    ((congrArg (Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom)
      (generatorRatioUnit_pullbackGenerator f L hL U s t)).trans rfl)

/-- The transition unit of two generators pulled back along `f` and restricted to `A` is the image
under `AlgebraicGeometry.Scheme.Hom.appLE` of the transition unit of their restrictions to `V`. -/
private theorem generatorRatioUnit_restrict_pullbackGenerator_of_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules)
    (hL : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L)
    {U₁ U₂ V : Y.Opens} (h₁ : V ≤ U₁) (h₂ : V ≤ U₂) {A : X.Opens} (hA : A ≤ f ⁻¹ᵁ V)
    (hA₁ : A ≤ f ⁻¹ᵁ U₁) (hA₂ : A ≤ f ⁻¹ᵁ U₂) (s : GeneratorSections Y.toRingedSpace L U₁)
    (t : GeneratorSections Y.toRingedSpace L U₂) :
    generatorRatioUnit ((modulePullback f.toLRSHom.toShHom).obj L) A
        (generatorRestrict _ hA₁ (pullbackGenerator f L hL U₁ s))
        (generatorRestrict _ hA₂ (pullbackGenerator f L hL U₂ t)) =
      Units.map (f.appLE V A hA).hom.toMonoidHom
        (generatorRatioUnit L V (generatorRestrict L h₁ s) (generatorRestrict L h₂ t)) :=
  (congrArg₂ (generatorRatioUnit _ A)
    ((generatorRestrict_trans _ ((Opens.map f.base).map (homOfLE h₁)).le hA _).symm.trans
      (congrArg (generatorRestrict _ hA) (pullbackGenerator_restrict f L hL h₁ s)))
    ((generatorRestrict_trans _ ((Opens.map f.base).map (homOfLE h₂)).le hA _).symm.trans
      (congrArg (generatorRestrict _ hA) (pullbackGenerator_restrict f L hL h₂ t)))).trans
    (generatorRatioUnit_restrict_pullbackGenerator f L hL hA _ _)

/-- Let `π : P ⟶ Q` be finite with a norm `N` of degree `d`, and let `a : G → (P ⟶ P)` be a
finite family of endomorphisms of the source with `a σ ≫ π = π`. If the norm factors through the
family on functions,

  `π^♯ (Norm_π s) = ∏_{σ ∈ G} (a σ)^♯ s`   for every section `s` over a preimage open,

then `Stacks.Divisors.HasNormGroupProductTensor` holds: for every invertible `ℒ` on `P`,

  `π^*(Norm_π ℒ) ≅ ⨂_{σ ∈ G} (a σ)^*ℒ`. -/
theorem hasNormGroupProductTensor_of_app_norm_eq_prod (π : P ⟶ Q) [IsFinite π] {d : ℕ}
    (N : MorphismNorm π d) {G : Type*} [Fintype G] (a : G → (P ⟶ P))
    (ha : ∀ σ, a σ ≫ π = π)
    (hhint : ∀ (V : Q.Opens) (s : Γ(P, π ⁻¹ᵁ V)),
      (π.app V).hom (N.app V s) =
        ∏ σ : G, ((a σ).appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V)
          (le_of_eq (preimage_preimage_of_comp_eq (ha σ) V).symm)).hom s) :
    HasNormGroupProductTensor π N a := by
  classical
  intro L hL
  have htc : HasTrivializingTargetCover π L :=
    hasTrivializingTargetCover_of_isFinite_of_isInvertible π L hL
  have hNinv : IsInvertible Q.presheaf (structureSheafRing Q.toRingedSpace).property
      (normInvertible π N.toMorphismNormMap L) :=
    isInvertible_normInvertible π N.toMorphismNormMap L htc
  have hLinv : IsInvertible P.presheaf (structureSheafRing P.toRingedSpace).property L := hL
  have hcov : (⊤ : Q.Opens) ≤ ⨆ i : NormChart π L, i.val := normChart_cover htc
  have hcovP : (⊤ : P.Opens) ≤ ⨆ i : NormChart π L, π ⁻¹ᵁ (i.val : Q.Opens) := by
    intro x _
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcov (show π.base x ∈ (⊤ : Q.Opens) from trivial))
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  refine ⟨isoOfChartGenerators _ _
    (fun i : NormChart π L ↦ pullbackGenerator π (normInvertible π N.toMorphismNormMap L) hNinv
      (i.val : Q.Opens)
      ((normTransitionCocycle π N.toMorphismNormMap L).chartGenerator hcov i))
    (fun i : NormChart π L ↦
      tensorListGenerator P (fun σ : G ↦ (modulePullback (a σ).toLRSHom.toShHom).obj L)
        (fun σ ↦ generatorRestrict _
          (le_of_eq (preimage_preimage_of_comp_eq (ha σ) (i.val : Q.Opens)).symm)
          (pullbackGenerator (a σ) L hLinv (π ⁻¹ᵁ (i.val : Q.Opens))
            (normChartSourceGenerator π L i))) Finset.univ.toList)
    ?_ hcovP⟩
  intro i j A hi hj
  have hiW : (i.val ⊓ j.val : Q.Opens) ≤ i.val := inf_le_left
  have hjW : (i.val ⊓ j.val : Q.Opens) ≤ j.val := inf_le_right
  have hAB : A ≤ π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens) := by
    rw [Scheme.Hom.preimage_inf]; exact le_inf hi hj
  have hBi : π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens) ≤ π ⁻¹ᵁ (i.val : Q.Opens) :=
    ((Opens.map π.base).map (homOfLE hiW)).le
  have hBj : π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens) ≤ π ⁻¹ᵁ (j.val : Q.Opens) :=
    ((Opens.map π.base).map (homOfLE hjW)).le
  have kk : ∀ σ : G, A ≤ (a σ) ⁻¹ᵁ (π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens)) := fun σ ↦
    hAB.trans (le_of_eq (preimage_preimage_of_comp_eq (ha σ) (i.val ⊓ j.val : Q.Opens)).symm)
  have hP : generatorRatioUnit
        ((modulePullback π.toLRSHom.toShHom).obj (normInvertible π N.toMorphismNormMap L)) A
        (generatorRestrict _ hj (pullbackGenerator π (normInvertible π N.toMorphismNormMap L)
          hNinv (j.val : Q.Opens)
          ((normTransitionCocycle π N.toMorphismNormMap L).chartGenerator hcov j)))
        (generatorRestrict _ hi (pullbackGenerator π (normInvertible π N.toMorphismNormMap L)
          hNinv (i.val : Q.Opens)
          ((normTransitionCocycle π N.toMorphismNormMap L).chartGenerator hcov i))) =
      Units.map (π.appLE (i.val ⊓ j.val : Q.Opens) A hAB).hom.toMonoidHom
        (normUnitsMap π N.toMorphismNormMap (i.val ⊓ j.val : Q.Opens)
          (generatorRatioUnit L (π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens))
            (normChartGeneratorOver π L j (i.val ⊓ j.val : Q.Opens) hjW)
            (normChartGeneratorOver π L i (i.val ⊓ j.val : Q.Opens) hiW))) :=
    (generatorRatioUnit_restrict_pullbackGenerator_of_le π _ hNinv hjW hiW hAB hj hi _ _).trans
      (congrArg (Units.map (π.appLE (i.val ⊓ j.val : Q.Opens) A hAB).hom.toMonoidHom)
        ((normTransitionCocycle π N.toMorphismNormMap L).generatorRatioUnit_chartGenerator
          hcov i j hiW hjW))
  have hQfac : ∀ σ : G, generatorRatioUnit
        ((modulePullback (a σ).toLRSHom.toShHom).obj L) A
        (generatorRestrict _ hj (generatorRestrict _
          (le_of_eq (preimage_preimage_of_comp_eq (ha σ) (j.val : Q.Opens)).symm)
          (pullbackGenerator (a σ) L hLinv (π ⁻¹ᵁ (j.val : Q.Opens))
            (normChartSourceGenerator π L j))))
        (generatorRestrict _ hi (generatorRestrict _
          (le_of_eq (preimage_preimage_of_comp_eq (ha σ) (i.val : Q.Opens)).symm)
          (pullbackGenerator (a σ) L hLinv (π ⁻¹ᵁ (i.val : Q.Opens))
            (normChartSourceGenerator π L i)))) =
      Units.map ((a σ).appLE (π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens)) A (kk σ)).hom.toMonoidHom
        (generatorRatioUnit L (π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens))
          (normChartGeneratorOver π L j (i.val ⊓ j.val : Q.Opens) hjW)
          (normChartGeneratorOver π L i (i.val ⊓ j.val : Q.Opens) hiW)) := fun σ ↦
    (congrArg₂ (generatorRatioUnit _ A) (generatorRestrict_trans _ _ hj _)
        (generatorRestrict_trans _ _ hi _)).trans
      (generatorRatioUnit_restrict_pullbackGenerator_of_le (a σ) L hLinv hBj hBi (kk σ) _ _ _ _)
  refine Eq.trans ?_ hP.symm
  refine ((congrArg₂ (generatorRatioUnit _ A)
      (tensorListGenerator_restrict P _ hj _ Finset.univ.toList)
      (tensorListGenerator_restrict P _ hi _ Finset.univ.toList)).trans
    ((generatorRatioUnit_tensorListGenerator P _ A _ _ Finset.univ.toList).trans
      (congrArg (fun f : G → (Γ(P, A))ˣ ↦ (Finset.univ.toList.map f).prod)
        (funext hQfac)))).trans ?_
  have hlist : (Finset.univ.toList.map fun σ : G ↦
        Units.map ((a σ).appLE (π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens)) A (kk σ)).hom.toMonoidHom
          (generatorRatioUnit L (π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens))
            (normChartGeneratorOver π L j (i.val ⊓ j.val : Q.Opens) hjW)
            (normChartGeneratorOver π L i (i.val ⊓ j.val : Q.Opens) hiW))).prod =
      ∏ σ : G, Units.map ((a σ).appLE (π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens)) A (kk σ)).hom.toMonoidHom
          (generatorRatioUnit L (π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens))
            (normChartGeneratorOver π L j (i.val ⊓ j.val : Q.Opens) hjW)
            (normChartGeneratorOver π L i (i.val ⊓ j.val : Q.Opens) hiW)) := by
    simp
  have ee : ∀ σ : G, π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens) ≤
      (a σ) ⁻¹ᵁ (π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens)) := fun σ ↦
    le_of_eq (preimage_preimage_of_comp_eq (ha σ) (i.val ⊓ j.val : Q.Opens)).symm
  have key : ∀ x : Γ(P, π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens)),
      (π.appLE (i.val ⊓ j.val : Q.Opens) A hAB).hom (N.app (i.val ⊓ j.val : Q.Opens) x) =
        ∏ σ : G, ((a σ).appLE (π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens)) A (kk σ)).hom x := by
    intro x
    calc (π.appLE (i.val ⊓ j.val : Q.Opens) A hAB).hom (N.app (i.val ⊓ j.val : Q.Opens) x)
        = (P.presheaf.map (homOfLE hAB).op).hom
            ((π.app (i.val ⊓ j.val : Q.Opens)).hom (N.app (i.val ⊓ j.val : Q.Opens) x)) := rfl
      _ = (P.presheaf.map (homOfLE hAB).op).hom
            (∏ σ : G, ((a σ).appLE (π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens))
              (π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens)) (ee σ)).hom x) := by
            rw [hhint]
      _ = ∏ σ : G, (P.presheaf.map (homOfLE hAB).op).hom
            (((a σ).appLE (π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens))
              (π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens)) (ee σ)).hom x) := map_prod _ _ _
      _ = ∏ σ : G, ((a σ).appLE (π ⁻¹ᵁ (i.val ⊓ j.val : Q.Opens)) A (kk σ)).hom x :=
            Finset.prod_congr rfl fun σ _ ↦ by
              rw [← Scheme.Hom.appLE_map (a σ) (ee σ) (homOfLE hAB).op]
              rfl
  refine hlist.trans (Units.ext ?_)
  push_cast
  exact (key _).symm

end Stacks.Divisors

end
