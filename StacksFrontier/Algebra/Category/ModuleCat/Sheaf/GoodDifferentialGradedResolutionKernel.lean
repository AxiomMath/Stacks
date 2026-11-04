module

public import Mathlib.CategoryTheory.Abelian.Pseudoelements
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionPairs
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionStep

/-!
# The inductive step of a flat resolution: the kernel dies in the next stage

Let `(C, O)` be a ringed site, let `A` be a sheaf of differential graded `O`-algebras, let `M`
and `P` be right differential graded `A`-modules and let `τ : P ⟶ M` be a homomorphism. The
first proof of Tag 0FSH builds a tower `P₀ → P₁ → ⋯ → M` in which each stage is the twisted
extension of the previous one by the free module on the sheaf of graded sets of boundary pairs,
and the property which makes the colimit of the tower resolve `M` is that at every stage the
kernel of `Hⁿ(Pᵢ) → Hⁿ(M)` is annihilated by `Hⁿ(Pᵢ) → Hⁿ(Pᵢ₊₁)`. This file proves that
property for one stage.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.towerStep` is the next stage of the tower: the twisted
  extension of `P` by the free module on the sheaf of graded sets of boundary pairs of `τ`, along
  the family of cocycles those pairs carry.
* `SheafOfModules.DifferentialGradedModule.towerStepInclusion` is the inclusion of `P` into it.

## Main results

* `DifferentialGradedModule.boundaryPairCycle_comp_homologyπ_comp_homologyMap_eq_zero`:
  **the class of the cocycle component of a boundary pair dies in the next stage**: every
  boundary pair names a canonical generator of the free module, that generator is a cocycle
  there, and the lift carries it to the cocycle component of the pair; so the class of that
  cocycle comes from the free module, and classes coming from the free module die in the cone.
* `SheafOfModules.DifferentialGradedModule.comp_homologyMap_towerStepInclusion_eq_zero`:
  **a map into `Hⁿ(P)` killed by `Hⁿ(P) → Hⁿ(M)` is killed by `Hⁿ(P) → Hⁿ(P₊)`**, which is the
  annihilation statement of the first proof of Tag 0FSH for one stage of its tower.

## Implementation notes

**The sectionwise lemma and the diagram chase.** The first result is proved on sections: a
morphism of sheaves of modules vanishes as soon as it vanishes on sections over every object of
the site (`SheafOfModules.DifferentialGradedModule.eq_zero_of_sections`), and over a fixed object
a boundary pair of degree `n` names a local section of the sheaf of graded sets, hence a
canonical generator of the free module which is closed and whose image under the lift is the
cocycle component of the pair. Taking sections over an object of the site is left exact, so that
generator is the image of a section of the cocycle sheaf, and the inclusion of the cocycle sheaf
being injective on sections identifies the two cocycles. The second result is a diagram chase
with `CategoryTheory.Abelian.Pseudoelement`: a class of `Hⁿ(P)` killed in `Hⁿ(M)` lifts to a
cocycle of `P` of degree `n`, whose image in `M` is the differential of a section of `M^{n-1}`
by exactness of `M^{n-1} → Z^n(M) → Hⁿ(M)`, and that pair of pseudoelements comes from a
pseudoelement of the fibre product — a boundary pair, to which the first result applies.

## References

* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf CategoryTheory.Abelian

universe t m v u

namespace SheafOfModules.DifferentialGradedModule

open Stacks Stacks.SheafOfGradedSets

/-! ### Vanishing of a morphism of sheaves of modules on sections -/

section Sections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- A morphism of sheaves of modules which vanishes on sections over every object of the site is
zero: a morphism of sheaves of modules is a morphism of presheaves of modules, and such a
morphism is determined by the maps it induces on sections. -/
theorem eq_zero_of_sections {X Y : SheafOfModules.{m} R} (f : X ⟶ Y)
    (hf : ∀ (U : Cᵒᵖ) (x : X.val.obj U), homSections f U x = 0) : f = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact hf U x

end Sections

section Kernel

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasWeakSheafify J (Type m)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {Osharp : Sheaf J CommRingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}
  {M P : DifferentialGradedModule.{t, m, m} A}

/-! ### The next stage of the tower -/

/-- The next stage of the tower of the first proof of Tag 0FSH. -/
noncomputable abbrev towerStep (τ : P ⟶ M) : DifferentialGradedModule.{t, m, m} A :=
  twistedExtension (boundaryPairs τ.toHomologicalComplex) P (boundaryPairFamily τ)
    (boundaryPairFamily_closed τ)

/-- The inclusion of a stage of the tower into the next one. -/
noncomputable abbrev towerStepInclusion (τ : P ⟶ M) : P ⟶ towerStep τ :=
  twistedExtensionInclusion (boundaryPairs τ.toHomologicalComplex) P (boundaryPairFamily τ)
    (boundaryPairFamily_closed τ)

/-! ### The class of a boundary pair dies in the next stage -/

/-- **The class of the cocycle component of a boundary pair dies in the next stage of the
tower.** Over an object of the site, a boundary pair of degree `n` names a local section of the
sheaf of graded sets of boundary pairs, hence a canonical generator of the free module; that
generator is closed, and the lift to `P` carries it to the cocycle component of the pair. So the
cocycle component is the image of a cocycle of the free module, and every class coming from the
free module dies in the cone, which is the next stage. -/
theorem boundaryPairCycle_comp_homologyπ_comp_homologyMap_eq_zero (τ : P ⟶ M) (n : ℤ) :
    boundaryPairCycle τ.toHomologicalComplex n ≫ P.complex.homologyπ n ≫
        HomologicalComplex.homologyMap (towerStepInclusion τ).toHomologicalComplex n = 0 := by
  set L := (dgLiftHom (boundaryPairs τ.toHomologicalComplex) A P (boundaryPairFamily τ)
    (boundaryPairFamily_closed τ)).toHomologicalComplex
  have hcyc : HomologicalComplex.cyclesMap L n ≫ P.complex.homologyπ n ≫
        HomologicalComplex.homologyMap (towerStepInclusion τ).toHomologicalComplex n = 0 := by
    rw [← Category.assoc, ← HomologicalComplex.homologyπ_naturality, Category.assoc,
      ← HomologicalComplex.homologyMap_comp,
      show L ≫ (towerStepInclusion τ).toHomologicalComplex = (dgLiftHom
          (boundaryPairs τ.toHomologicalComplex) A P (boundaryPairFamily τ)
          (boundaryPairFamily_closed τ) ≫ towerStepInclusion τ).toHomologicalComplex from rfl,
      homologyMap_comp_twistedExtensionInclusion_eq_zero (boundaryPairs τ.toHomologicalComplex) P
        (boundaryPairFamily τ) (boundaryPairFamily_closed τ) n, comp_zero]
  refine eq_zero_of_sections _ fun V y => ?_
  obtain ⟨ζ, hζ⟩ :=
    exists_cycles_section (freeDGModule (boundaryPairs τ.toHomologicalComplex) A).complex n V
      (freeGeneratorSection A.toGradedAlgebra (boundaryPairs τ.toHomologicalComplex) n V
        (boundaryPairSection τ.toHomologicalComplex n V y)
        (boundaryPairSection_hasDegree τ.toHomologicalComplex n V y))
      (freeDGModule_d_freeGenerator (boundaryPairs τ.toHomologicalComplex) A n V
        (boundaryPairSection τ.toHomologicalComplex n V y)
        (boundaryPairSection_hasDegree τ.toHomologicalComplex n V y))
  have hmap : homSections (HomologicalComplex.cyclesMap L n) V ζ =
      homSections (boundaryPairCycle τ.toHomologicalComplex n) V y := by
    refine injective_iCycles_sections P.complex n V ?_
    refine (homSections_congr (HomologicalComplex.cyclesMap_i L n) V ζ).trans ?_
    rw [homSections_comp, hζ]
    exact (dgLiftHom_generator (boundaryPairs τ.toHomologicalComplex) A P (boundaryPairFamily τ)
      (boundaryPairFamily_closed τ) n V (boundaryPairSection τ.toHomologicalComplex n V y)
      (boundaryPairSection_hasDegree τ.toHomologicalComplex n V y)).trans
      (boundaryPairFamily_eq_iCycles τ n V y)
  change homSections (P.complex.homologyπ n ≫ HomologicalComplex.homologyMap
    (towerStepInclusion τ).toHomologicalComplex n) V
    (homSections (boundaryPairCycle τ.toHomologicalComplex n) V y) = 0
  rw [← hmap]
  exact (homSections_congr hcyc V ζ).trans (homSections_zero V ζ)

/-! ### The annihilation of the kernel -/

/-- **A map into `Hⁿ(P)` annihilated by `Hⁿ(P) → Hⁿ(M)` is annihilated by the map to the next
stage of the tower.** This is the property of the tower of the first proof of Tag 0FSH which
makes its colimit resolve `M`, at one stage. The proof is a diagram chase: a class of `Hⁿ(P)`
killed in `Hⁿ(M)` lifts to a cocycle of `P` of degree `n`, whose image in `M` is the differential
of a section of `M^{n-1}`; the two together are a boundary pair, whose class dies in the next
stage. -/
theorem comp_homologyMap_towerStepInclusion_eq_zero (τ : P ⟶ M) (n : ℤ)
    {Z : SheafOfModules.{m} (toRingCat J Osharp)} (g : Z ⟶ P.complex.homology n)
    (hg : g ≫ HomologicalComplex.homologyMap τ.toHomologicalComplex n = 0) :
    g ≫ HomologicalComplex.homologyMap (towerStepInclusion τ).toHomologicalComplex n = 0 := by
  refine Pseudoelement.zero_morphism_ext _ fun z => ?_
  rw [Pseudoelement.comp_apply]
  obtain ⟨ξ, hξ⟩ := Pseudoelement.pseudo_surjective_of_epi (P.complex.homologyπ n)
    (Pseudoelement.pseudoApply g z)
  have hzero : Pseudoelement.pseudoApply (M.complex.homologyπ n)
      (Pseudoelement.pseudoApply
        (HomologicalComplex.cyclesMap τ.toHomologicalComplex n) ξ) = 0 := by
    rw [← Pseudoelement.comp_apply, ← HomologicalComplex.homologyπ_naturality,
      Pseudoelement.comp_apply, hξ, ← Pseudoelement.comp_apply, hg, Pseudoelement.zero_apply]
  have hexact : (ShortComplex.mk (M.complex.toCycles (n - 1) n) (M.complex.homologyπ n)
      (M.complex.toCycles_comp_homologyπ (n - 1) n)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (M.complex.homologyIsCokernel (n - 1) n (by simp))
  obtain ⟨μ, hμ⟩ := Pseudoelement.pseudo_exact_of_exact hexact _ hzero
  obtain ⟨y, hy, -⟩ :
      ∃ y : Pseudoelement (boundaryPairObj τ.toHomologicalComplex n),
        Pseudoelement.pseudoApply (boundaryPairCycle τ.toHomologicalComplex n) y = ξ ∧
          Pseudoelement.pseudoApply (boundaryPairPrimitive τ.toHomologicalComplex n) y = μ :=
    Pseudoelement.pseudo_pullback hμ.symm
  calc Pseudoelement.pseudoApply
        (HomologicalComplex.homologyMap (towerStepInclusion τ).toHomologicalComplex n)
        (Pseudoelement.pseudoApply g z)
      = Pseudoelement.pseudoApply (boundaryPairCycle τ.toHomologicalComplex n ≫
          P.complex.homologyπ n ≫
          HomologicalComplex.homologyMap
            (towerStepInclusion τ).toHomologicalComplex n) y := by
        rw [Pseudoelement.comp_apply, Pseudoelement.comp_apply, hy, hξ]
    _ = 0 := by
        rw [boundaryPairCycle_comp_homologyπ_comp_homologyMap_eq_zero τ n,
          Pseudoelement.zero_apply]

end Kernel

end SheafOfModules.DifferentialGradedModule

end
