module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.BasicOpen
public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.Degreewise
public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.SectionModule

/-!
# Sections of a graded module over a standard open of the base

Let `s` be a relative `Proj` situation, let `ℳ` be a graded module over its graded algebra whose
homogeneous pieces are quasi-coherent, let `W'` be an affine open of the base and let `g` be a
function on `W'`. Over the standard open `D(g) ⊆ W'` the graded module of local sections of `ℳ`
is the localization of the one over `W'` away from `g`, degree by degree, because each
homogeneous piece of `ℳ` is quasi-coherent. This is the module companion of
`Stacks.RelativeProj.Situation.isAwayDegreewise_basicOpen`.

## Main results

* `Stacks.RelativeProj.Situation.sectionRingBaseMap_smul_of`: the action of the image of a
  function on the base on a homogeneous summand of the module of sections is the module action of
  that function on that homogeneous piece.
* `Stacks.RelativeProj.Situation.isAwayDegreewiseModule_basicOpen`: restriction of the graded
  modules of local sections to a standard open is, degree by degree, the localization away from
  the function cutting it out.

## Implementation notes

The three hypotheses of `Stacks.GradedLocalization.IsAwayDegreewiseModule` come from
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ` applied to each
homogeneous piece of `ℳ`, together with
`Stacks.RelativeProj.Situation.sectionRingBaseMap_smul_of` to turn the module action of a
function on the base into the action of the section ring on the module of sections.

The universes are those of the base scheme throughout, as they are for the graded module of
local sections: the homogeneous pieces of `ℳ` have to be modules of the base scheme for their
quasi-coherence to be stated at all.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)

## Not done here

No Stacks tag is carried. Nothing is proved here about the sheaf attached to `ℳ` on a chart, nor
about the comparison of two such sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite DirectSum
open Stacks.GradedLocalization Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.RelativeProj.Situation

variable {s : Situation.{u}} (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)

/-- **The image of a function on the base acts on a homogeneous summand of the module of sections
as that function acts on the homogeneous piece.** -/
public theorem sectionRingBaseMap_smul_of (U : s.base.Opens) (n : ℤ)
    (r : s.base.ringCatSheaf.obj.obj (op U)) (x : sectionModulePieces ℳ U n) :
    s.sectionRingBaseMap U r • DirectSum.of (sectionModulePieces ℳ U) n x =
      DirectSum.of (sectionModulePieces ℳ U) n (r • x) := by
  have key : ∀ (d : ℤ) (_ : d = n) (y : (ℳ.piece d).val.obj (op U)),
      y ≍ x → (r • y) ≍ (r • x) := by
    rintro d rfl y hy
    rw [eq_of_heq hy]
  rw [sectionRingBaseMap, (sectionRingStructure s).baseMap_apply,
    sectionModule_of_smul_of ℳ U]
  refine DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext (zero_add n) ?_)
  have hleft : ℳ.smul ((0 : ℕ) : ℤ) n (op U) (r • s.algebra.one.eval (op U)) x =
      r • ℳ.smul ((0 : ℕ) : ℤ) n (op U) (s.algebra.one.eval (op U)) x :=
    ℳ.smul_smul_left _ n (op U) r _ x
  exact (heq_of_eq hleft).trans (key _ (zero_add n) _ (ℳ.one_smul n (op U) x))

/-- A power of the image of a function on the base acts on a homogeneous summand of the module of
sections as the same power of that function acts on the homogeneous piece. -/
private theorem sectionRingBaseMap_pow_smul_of (U : s.base.Opens) (n : ℤ)
    (r : s.base.ringCatSheaf.obj.obj (op U)) (k : ℕ) (x : sectionModulePieces ℳ U n) :
    s.sectionRingBaseMap U r ^ k • DirectSum.of (sectionModulePieces ℳ U) n x =
      DirectSum.of (sectionModulePieces ℳ U) n (r ^ k • x) := by
  rw [← map_pow, sectionRingBaseMap_smul_of]

variable [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] {W' : s.base.Opens} (g₀ : Γ(s.base, W'))

/-- Every homogeneous section of `ℳ` over `D(g)` becomes the restriction of one over `W'` after
multiplication by a power of `g`. -/
private theorem surj_restrict_module (hW' : IsAffineOpen W') (i : ℤ)
    (y : sectionModule ℳ (s.base.basicOpen g₀))
    (hy : y ∈ sectionModuleGrading ℳ (s.base.basicOpen g₀) i) :
    ∃ (k : ℕ) (x : sectionModule ℳ W'), x ∈ sectionModuleGrading ℳ W' i ∧
      sectionModuleRestrictₛₗ ℳ (s.base.basicOpen_le g₀) x =
        gradedSectionRestriction s (s.base.basicOpen g₀) W' (s.base.basicOpen_le g₀)
            (s.sectionRingBaseMap W' g₀) ^ k • y := by
  obtain ⟨a, rfl⟩ := hy
  let hle := s.base.basicOpen_le g₀
  let := moduleOfLE (ℳ.piece i) hle
  have hloc := isLocalizedModule_restrictₗ (ℳ.piece i) hW' g₀ rfl hle
  obtain ⟨⟨a', ⟨c, k, rfl⟩⟩, hac⟩ :=
    IsLocalizedModule.surj (Submonoid.powers g₀) (restrictₗ (ℳ.piece i) hle) a
  refine ⟨k, DirectSum.of (sectionModulePieces ℳ W') i a', ⟨a', rfl⟩, ?_⟩
  have hbase := gradedSectionRestriction_baseMap s _ W' hle g₀
  rw [sectionModuleRestrictₛₗ_apply, sectionModuleRestrict_of ℳ hle a', hbase,
    sectionRingBaseMap_pow_smul_of ℳ _ i _ k a]
  refine congrArg (DirectSum.of (sectionModulePieces ℳ (s.base.basicOpen g₀)) i) ?_
  have hac2 : (ConcreteCategory.hom (s.base.ringCatSheaf.obj.map (homOfLE hle).op)) (g₀ ^ k) • a =
      (ℳ.piece i).val.map (homOfLE hle).op a' := hac
  exact hac2.symm.trans (congrArg (fun r => r • a)
    (map_pow (ConcreteCategory.hom (s.base.ringCatSheaf.obj.map (homOfLE hle).op)) g₀ k))

/-- A homogeneous section of `ℳ` over `W'` that restricts to zero on `D(g)` is killed by a power
of the image of `g`. -/
private theorem torsion_restrict_module (hW' : IsAffineOpen W') (i : ℤ)
    (x : sectionModule ℳ W') (hx : x ∈ sectionModuleGrading ℳ W' i)
    (hzero : sectionModuleRestrictₛₗ ℳ (s.base.basicOpen_le g₀) x = 0) :
    ∃ k : ℕ, s.sectionRingBaseMap W' g₀ ^ k • x = 0 := by
  obtain ⟨a', rfl⟩ := hx
  let hle := s.base.basicOpen_le g₀
  rw [sectionModuleRestrictₛₗ_apply, sectionModuleRestrict_of ℳ hle a'] at hzero
  obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero (ℳ.piece i) hW' g₀ a'
    ((DFinsupp.single_eq_zero (β := sectionModulePieces ℳ (s.base.basicOpen g₀))).mp hzero)
  refine ⟨k, ?_⟩
  rw [sectionRingBaseMap_pow_smul_of ℳ W' i g₀ k a']
  exact (congrArg (DirectSum.of (sectionModulePieces ℳ W') i) hk).trans (map_zero _)

/-- **Restriction of the graded module of local sections to a standard open is a degreewise
localization** away from the image of `g`. -/
public theorem isAwayDegreewiseModule_basicOpen (hW' : IsAffineOpen W') :
    IsAwayDegreewiseModule
      (gradedSectionRestriction s (s.base.basicOpen g₀) W' (s.base.basicOpen_le g₀))
      (sectionModuleGrading ℳ W') (sectionModuleGrading ℳ (s.base.basicOpen g₀))
      (sectionModuleRestrictₛₗ ℳ (s.base.basicOpen_le g₀)) (s.sectionRingBaseMap W' g₀) where
  map_mem _ _ hm := sectionModuleRestrict_mem_grading ℳ (s.base.basicOpen_le g₀) hm
  surj i y hy := surj_restrict_module ℳ g₀ hW' i y hy
  torsion i x hx hzero := torsion_restrict_module ℳ g₀ hW' i x hx hzero

end Stacks.RelativeProj.Situation

end
