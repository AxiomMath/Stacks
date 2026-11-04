module

public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFiniteCoverDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleRule
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme

/-!
# Preservation of a rule by higher direct images: reduction to an affine target

Let `M` be a rule of modules on algebraic stacks which is closed under isomorphisms, stable under
smooth inverse images and local for smooth jointly surjective families, and let `D` be a direct
image satisfying smooth base change along the canonical 2-fibre product. If the higher direct
images of `D` along quasi-compact quasi-separated 1-morphisms with affine target preserve `M`,
then so do those along every quasi-compact quasi-separated 1-morphism.

## Main definitions

* `AlgebraicGeometry.Stack.StackModuleRule.HasSmoothBaseChange`: the base change identification
  `g⁻¹ Rⁱf_* ℱ ≅ Rⁱf'_* (g')⁻¹ ℱ` for `D` along smooth charts from objects of the site.

## Main results

* `AlgebraicGeometry.Stack.StackModuleRule.exists_smooth_jointlySurjective_affine_family`: an
  algebraic stack receives a smooth jointly surjective family from affine objects of the site.
* `AlgebraicGeometry.Stack.StackModuleRule.preservedBy_of_affineTarget`: if the higher direct
  images along every quasi-compact quasi-separated 1-morphism with affine target preserve the
  rule in degree `i`, so do those along every quasi-compact quasi-separated 1-morphism.

## References

* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
* [Stacks Project, Tag 0770](https://stacks.math.columbia.edu/tag/0770)
* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u t

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace StackModuleRule

variable {τ : SiteKind} (D : StackModuleDirectImage.{u, t} B S hS τ)

/-- **The base change identification for the direct image `D`**, along a smooth
1-morphism from the algebraic stack of an object of the site and at the canonical 2-fibre
product: for `f : 𝒳 ⟶ 𝒴`, a smooth `g : (Sch/V) ⟶ 𝒴` and the 2-fibre product
`𝒳' = 𝒳 ×_𝒴 (Sch/V)` with projections `g' : 𝒳' ⟶ 𝒳` and `f' : 𝒳' ⟶ (Sch/V)`,
`g⁻¹ Rⁱf_* ℱ ≅ Rⁱf'_* (g')⁻¹ ℱ`. -/
abbrev HasSmoothBaseChange : Prop :=
  ∀ {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} {V : BigFppfOver B S hS} (f : 𝒳 ⟶ 𝒴)
    (g : schemeStack.{u, t} B S hS V ⟶ 𝒴), AlgebraicStacks.IsSmooth B S hS g →
    ∀ (i : ℕ) (F : StackModules B S hS τ 𝒳),
      Nonempty ((stackModuleInverseImage B S hS τ g).obj ((D.higherDirectImage f i).obj F) ≅
        (D.higherDirectImage (twoFibreProductSquareAlgebraicStacks B S hS f g).snd i).obj
          ((stackModuleInverseImage B S hS τ
            (twoFibreProductSquareAlgebraicStacks B S hS f g).fst).obj F))

/-- An algebraic stack receives a smooth family of 1-morphisms from the algebraic stacks of
objects of the site with affine underlying schemes, jointly surjective on points, indexed by a
type in the universe of the schemes. -/
theorem exists_smooth_jointlySurjective_affine_family (𝒴 : AlgebraicStacks.{u, t} B S hS) :
    ∃ (J : Type u) (V : J → BigFppfOver B S hS) (c : ∀ j, schemeStack.{u, t} B S hS (V j) ⟶ 𝒴),
      (∀ j, IsAffine (V j).left.1) ∧ (∀ j, AlgebraicStacks.IsSmooth B S hS (c j)) ∧
        (Set.univ : Set (AlgebraicStacks.points B S hS 𝒴)) =
          ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (c j)) := by
  classical
  obtain ⟨U, a, ha, hasurj⟩ := exists_smooth_surjective_schemeStack B S hS 𝒴
  choose V v hv hrange hVaff using fun W : ((BigFppfOver.toScheme B S hS).obj U).affineOpens =>
    BigFppfOver.exists_affineOpen_restrict B S hS U W
  refine ⟨_, V, fun j => schemeStackMap.{u, t} B S hS (v j) ≫ a, hVaff, fun j => ?_, ?_⟩
  · have := hv j
    exact AlgebraicStacks.isSmooth_comp B S hS _ a
      (isSmooth_schemeStackMap.{u, t} B S hS (v j) inferInstance) ha
  · refine (Set.eq_univ_of_forall fun z => ?_).symm
    obtain ⟨y, rfl⟩ := hasurj z
    have hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj U,
        ∃ j, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (v j)).base := by
      intro x
      have hx : x ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens) := trivial
      rw [← iSup_affineOpens_eq_top] at hx
      obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact ⟨W, (hrange W).symm ▸ hW⟩
    obtain ⟨j, w, rfl⟩ := exists_mem_range_pointsMap_schemeStackMap.{u, t} B S hS V v hcov y
    refine Set.mem_iUnion.2 ⟨j, w, ?_⟩
    rw [AlgebraicStacks.pointsMap_comp]
    rfl

/-- **Reduction to an affine target.** Let `M` be a rule which is closed under isomorphisms,
stable under smooth inverse images and local for smooth jointly surjective families, and let the
direct image `D` satisfy the base change identification `HasSmoothBaseChange` along smooth
charts. If the higher direct images in degree `i` along every quasi-compact quasi-separated
1-morphism with target the algebraic stack of an affine object preserve `M`, then so do those along
every quasi-compact quasi-separated 1-morphism. -/
theorem preservedBy_of_affineTarget (M : StackModuleRule.{u, t} B S hS τ)
    (h1 : ∀ 𝒳, (M 𝒳).IsClosedUnderIsomorphisms) (h2 : IsStableUnderSmoothPullback τ M)
    (h3 : IsSmoothLocal.{u, t, u} τ M) (hbc : HasSmoothBaseChange D) (i : ℕ)
    (haff : ∀ {𝒳' : AlgebraicStacks.{u, t} B S hS} {Y : BigFppfOver B S hS}, IsAffine Y.left.1 →
      ∀ f' : 𝒳' ⟶ schemeStack.{u, t} B S hS Y, IsQuasiCompactMorphism B S hS f' →
        AlgebraicStacks.IsQuasiSeparated B S hS f' → PreservedBy D M f' i)
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴) (hqc : IsQuasiCompactMorphism B S hS f)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f) : PreservedBy D M f i := by
  intro F hF
  obtain ⟨J, V, c, hVaff, hc, hjs⟩ := exists_smooth_jointlySurjective_affine_family 𝒴
  refine (h3 c hc hjs _).2 fun j => ?_
  let P := twoFibreProductSquareAlgebraicStacks B S hS f (c j)
  have hP := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f (c j)
  obtain ⟨e⟩ := hbc f (c j) (hc j) i F
  refine (M _).prop_of_iso e.symm (haff (hVaff j) P.snd ?_ ?_ _ (h2 P.fst ?_ F hF))
  · exact isQuasiCompactMorphism_baseChange B S hS f (c j) P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hqc
  · exact AlgebraicStacks.isQuasiSeparated_baseChange_of_isTwoFibreProduct B S hS f (c j) P hP hqs
  · exact AlgebraicStacks.isSmooth_baseChange B S hS (c j) f P hP (hc j)

end StackModuleRule

end AlgebraicGeometry.Stack

end
