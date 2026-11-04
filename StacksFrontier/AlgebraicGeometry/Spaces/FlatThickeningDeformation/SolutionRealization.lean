module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.ClassesMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionPulledBackSize

/-!
# A solution of the extension problem of a flat thickening is realized by a thickening

Let `Y ⊂ Y'` be a first-order thickening of algebraic spaces with inclusion `t`, and `f : X ⟶ Y`.
A solution `0 → f^*𝒞_{Y/Y'} → 𝒪' → 𝒪_X → 0` of the extension problem of
[Stacks Project, Tag 08UF] attached to `f` (`FlatThickeningDeformation.problem`) is in
particular a square-zero extension of `𝒪_X` relative to `f ≫ t : X ⟶ Y'` whose ideal
`f^*𝒞_{Y/Y'} = f^*t^*ℐ_Y ≅ (f ≫ t)^*ℐ_Y` is pulled back from the ideal sheaf of `Y ⊂ Y'`; by
Stacks 05ZT, in the form
`SquareZeroExtension.nonempty_realization_of_iso_modulePullback_definingIdealSheaf`,
it is realized by a first-order thickening `X ⊂ X'` over `Y'` of the given big fppf site. This is
the first step of the surjectivity half of the proof of [Stacks Project, Tag 0D17].

## Main definitions

* `AlgebraicGeometry.Space.FlatThickeningDeformation.solutionSquareZeroExtension`: the
  square-zero extension over `f ≫ t` underlying a solution.

## Main results

* `FlatThickeningDeformation.nonempty_realization_solutionSquareZeroExtension`:
  it is realized on the given site.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

open _root_.Deformation.ToposThickening.RingedToposExtensionProblem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1) {X : AlgebraicSpaces B S hS}
  {f : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)}

/-- The prescribed module `f^*𝒞_{Y/Y'}` of the problem is `(f ≫ t)^*ℐ_Y`, the pullback of the ideal
sheaf of `Y ⊂ Y'`: the conormal module is `t^*ℐ_Y` by definition, and `f^*t^* ≅ (f ≫ t)^*` by
Stacks 03LU. -/
def pulledBackConormalIso (f : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) :
    pulledBackConormal f ≅ (modulePullback B S hS (f ≫ subspaceInclusion B S hS Y' Z)).obj
      (definingIdealSheaf B S hS Y' Z).toSheafOfModules :=
  (modulePullbackCompIso B S hS f (subspaceInclusion B S hS Y' Z)).app _

/-- The prescribed module `f^*𝒞_{Y/Y'}` of the problem is quasi-coherent (Stacks 03GA twice: the
ideal sheaf is quasi-coherent, and so are its pullbacks). -/
theorem isQuasicoherentOnSite_pulledBackConormal
    (f : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) :
    (pulledBackConormal f).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
      (isQuasicoherentOnSite_definingIdealSheaf B S hS Y' Z))

/-- In a commutative ring, the product of two elements of an ideal of square zero vanishes. -/
theorem mul_eq_zero_of_mem_of_sq_eq_bot {R : Type*} [CommRing R] {I : Ideal R} (hI : I ^ 2 = ⊥)
    {a b : R} (ha : a ∈ I) (hb : b ∈ I) : a * b = 0 := by
  have h := Ideal.mul_mem_mul ha hb
  rw [← pow_two, hI] at h
  exact h

variable {hZ} in
/-- **The square-zero extension underlying a solution.** A solution `𝒪' ⟶ 𝒪_X` of the problem
attached to `f` is a square-zero extension of `𝒪_X` relative to `f ≫ t : X ⟶ Y'`: its algebra
structure is the base map `f⁻¹t⁻¹𝒪_{Y'} ⟶ 𝒪'` through the comparison
`(f ≫ t)⁻¹𝒪_{Y'} ≅ f⁻¹t⁻¹𝒪_{Y'}` of Stacks 03G8, and its kernel is the prescribed module
`f^*𝒞_{Y/Y'}`, quasi-coherent by Stacks 03GA. -/
def solutionSquareZeroExtension (P : (problem f hZ).CompatibleFirstOrderThickening) :
    SquareZeroExtension B S hS (f ≫ subspaceInclusion B S hS Y' Z) where
  A := P.extension
  π := P.reduction
  locallySurjective_π := P.locallySurjective
  toBase := (smallEtaleRingedToposHom_compInverseImageRingIso B S hS f
      (subspaceInclusion B S hS Y' Z)).inv.app (smallEtaleRingedTopos B S hS Y').O ≫ P.baseMap
  toBase_π := by
    have h := smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage B S hS f
      (subspaceInclusion B S hS Y' Z)
    refine (Category.assoc _ _ _).trans ((congrArg (fun φ => _ ≫ φ) P.baseMap_reduction).trans
      ((congrArg (fun φ => _ ≫ φ) h.symm).trans ?_))
    rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  I := pulledBackConormal f
  quasicoherent := isQuasicoherentOnSite_pulledBackConormal f
  ι U := (P.kernelInclusion.val.app U).hom.toAddMonoidHom
  naturality g x := PresheafOfModules.naturality_apply P.kernelInclusion.val g x
  mem_kernel U x := P.kernelZero U x
  exact_kernel U a ha := P.kernelUniversal U a ha
  smul_lift U a x := (P.kernelInclusion.val.app U).hom.map_smul a x
  square_zero U x y :=
    mul_eq_zero_of_mem_of_sq_eq_bot (P.squareZero U) (P.kernelZero U x) (P.kernelZero U y)

variable {hZ} in
/-- **Stacks 05ZT for a solution, on the given site.** The square-zero extension underlying a
solution of the problem attached to `f` is realized by a first-order thickening `X ⊂ X'` over
`Y'` of the given big fppf site: its ideal `f^*𝒞_{Y/Y'} ≅ (f ≫ t)^*ℐ_Y` is pulled back from the
ideal sheaf of `Y ⊂ Y'`. -/
theorem nonempty_realization_solutionSquareZeroExtension
    (P : (problem f hZ).CompatibleFirstOrderThickening) :
    Nonempty (SquareZeroExtension.Realization B S hS (solutionSquareZeroExtension P)) :=
  (solutionSquareZeroExtension P).nonempty_realization_of_iso_modulePullback_definingIdealSheaf Z
    (pulledBackConormalIso f)

/-- Transport of a commuting square along an isomorphism of its corner (categorical helper). -/
theorem comp_eq_of_iso_hom_comp {𝒞 : Type*} [Category 𝒞] {A A' B₀ Y₀ T₀ : 𝒞} (e : A ≅ A')
    (ι : A' ⟶ B₀) (im : A ⟶ B₀) (hi : e.hom ≫ ι = im) (g : B₀ ⟶ T₀) (f₀ : A ⟶ Y₀)
    (t : Y₀ ⟶ T₀) (h : im ≫ g = f₀ ≫ t) : ι ≫ g = (e.inv ≫ f₀) ≫ t := by
  subst hi
  rw [Category.assoc, ← h, Category.assoc, Iso.inv_hom_id_assoc]

section Realized

variable {hZ} {P : (problem f hZ).CompatibleFirstOrderThickening}
  (r : SquareZeroExtension.Realization B S hS (solutionSquareZeroExtension P))

/-- The closed subspace `X₀ ⊂ X'` of a realization, a first-order thickening. -/
def realizedSubspace : ClosedSubspaces B S hS r.ambient.1 :=
  ⟨r.closed, r.firstOrder.isThickening.1⟩

/-- `X` is isomorphic to the closed subspace `X₀ ⊂ X'` of a realization. -/
def realizedIso :
    X ≅ (⟨(realizedSubspace r).1.toFunctor, (realizedSubspace r).2.1⟩ : AlgebraicSpaces B S hS) :=
  (ObjectProperty.fullyFaithfulι _).preimageIso r.closedIso

/-- The morphism `X₀ ⟶ Y` of a realization: `f` through `X ≅ X₀`. -/
def realizedReduction :
    (⟨(realizedSubspace r).1.toFunctor, (realizedSubspace r).2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) :=
  (realizedIso r).inv ≫ f

/-- The inclusion `X₀ ⊂ X'` through `X ≅ X₀` is the immersion of the realization. -/
theorem realizedIso_hom_comp_subspaceInclusion :
    (realizedIso r).hom ≫ subspaceInclusion B S hS r.ambient (realizedSubspace r) =
      r.immersion :=
  ObjectProperty.hom_ext _ r.immersion_eq.symm

/-- The square of inclusions of a realization over `Y ⊂ Y'` commutes. -/
theorem realized_comm :
    subspaceInclusion B S hS r.ambient (realizedSubspace r) ≫ r.toBase =
      realizedReduction r ≫ subspaceInclusion B S hS Y' Z :=
  comp_eq_of_iso_hom_comp (realizedIso r) _ _ (realizedIso_hom_comp_subspaceInclusion r) _ _ _
    r.over_base

/-- **The realized thickening is a flat deformation once its conormal map is invertible**
(Stacks 06BH, (2) ⟹ (1)). For flat `f`, if the canonical map `f₀^*𝒞_{Y/Y'} ⟶ 𝒞_{X₀/X'}` of the
realization is an isomorphism, then `X' ⟶ Y'` is flat and `X = Y ×_{Y'} X'`. -/
def deformationOfIsIsoConormalMap (hf : IsFlat B S hS f.hom)
    (h : IsIso (conormalMap B S hS (realizedSubspace r) Z r.toBase (realizedReduction r)
      (realized_comm r))) :
    Deformation f := by
  have hflat₀ : IsFlat B S hS (realizedReduction r).hom :=
    isFlat_comp B S hS (realizedSubspace r).2.1 X.2 Z.2.1 _ _
      (isFlat_of_isEtale B S hS (isEtale_hom_of_iso B S hS (realizedIso r).symm)) hf
  have h06BH := (isFlat_and_isPullback_iff_isIso_conormalMap B S hS r.toBase (realizedSubspace r)
    Z (realizedReduction r) (realized_comm r) r.firstOrder hZ hflat₀).2 h
  refine ⟨r.ambient, r.toBase, h06BH.1, r.immersion, ?_⟩
  refine h06BH.2.of_iso (realizedIso r).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    (by simp) (by simp)
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← realizedIso_hom_comp_subspaceInclusion r,
      Iso.inv_hom_id_assoc]
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, realizedReduction]

end Realized

end AlgebraicGeometry.Space.FlatThickeningDeformation

end
