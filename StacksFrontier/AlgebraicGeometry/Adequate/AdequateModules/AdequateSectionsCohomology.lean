module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedZariskiAdjunction
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.CoveringSheafCondition
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.TopologyIndependence
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightAcyclicComposite
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.InjectiveModuleSheafAcyclicityAtMorphismUniverse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfModuleOverObjectEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationConvergenceWeakSerre
public import StacksFrontier.AlgebraicGeometry.Cohomology.TruncationTowerInput

/-!
# The cohomology of an adequate module over an affine object, as module cohomology

Let `S` be a scheme and `(Sch/S)_τ` a chosen big site over `S`. [Stacks, Tag 06VM] (3) says that
an adequate `𝒪`-module `𝓕` has `H^q(U, 𝓕) = 0` for `q > 0` and every affine object `U` of the
site, the cohomology being that of the underlying abelian sheaf. This file reads the vanishing
in the cohomology of `𝒪`-modules, and assembles from it the Olsson--Laszlo situation of
[Stacks, Tag 0D6R] for the adequate modules: the affine objects cover every object of the site,
the coverings of an object by affine objects are cofinal among all its coverings, and on their
members the cohomology of an adequate module vanishes above degree `0`.

## Main definitions

* `Stacks.Adequate.BigSite.sectionsOver`: sections over an object of the site, as a functor from
  `𝒪`-modules to abelian groups.
* `Stacks.Adequate.BigSite.affineOpenHypercover`: the covering of an object of the site by the
  open subschemes of its scheme that are affine.
* `Stacks.Adequate.BigSite.affineCoveringSystem`: the coverings of an object by affine objects,
  as a cofinal system of coverings.
* `Stacks.Adequate.BigSite.adequateOlssonLaszlo`: the Olsson--Laszlo situation of
  [Stacks, Tag 0D6R] for the adequate modules on a chosen big site.

## Main results

* `Stacks.Adequate.BigSite.isZero_rightDerived_sectionsOver_of_isAdequate`: the higher right
  derived functors of sections over an affine object vanish at an adequate module.
* `Stacks.Adequate.BigSite.isZero_moduleCohomology_of_isAdequate`: the same in the spelling
  `Stacks.Cohomology.moduleCohomology`.

## Implementation notes

The module cohomology and the abelian cohomology of [Stacks, Tag 06VM] (3) agree because the
forgetful functor from `𝒪`-modules to abelian sheaves is exact and carries injective modules to
abelian sheaves with vanishing higher cohomology over every object ([Stacks, Tag 03FD]); the
comparison is `Stacks.Cohomology.AffineComparison.rightDerivedCollapseIso`.

## References

* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 0D6R](https://stacks.math.columbia.edu/tag/0D6R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

attribute [local instance] Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Sections over an object, and the vanishing at an affine object -/

/-- Sections over an object `W` of a chosen big site, as a functor from `𝒪`-modules to abelian
groups. -/
abbrev BigSite.sectionsOver (W : B.category) :
    SheafOfModules.{u} B.structureSheaf ⥤ AddCommGrpCat.{u} :=
  Stacks.Cohomology.Localization.OfEssentiallySmall.sectionsOverObject B.topology
    B.structureSheaf W

/-- Sections over an object of a chosen big site form an additive functor. -/
instance BigSite.additive_sectionsOver (W : B.category) : (B.sectionsOver W).Additive :=
  Stacks.Cohomology.Localization.OfEssentiallySmall.additive_sectionsOverObject _ _ _

/-- **[Stacks, Tag 06VM] (3) in the cohomology of modules.** The higher right derived functors of
sections over an affine object of a chosen big site vanish at an adequate module. -/
theorem BigSite.isZero_rightDerived_sectionsOver_of_isAdequate
    (F : SheafOfModules.{u} B.structureSheaf) (hF : IsAdequate B F)
    (W : B.category) [IsAffine W.left.obj] (q : ℕ) (hq : 0 < q) :
    IsZero (((B.sectionsOver W).rightDerived q).obj F) := by
  let := HasDerivedCategory.standard (Sheaf B.topology AddCommGrpCat.{u})
  let := HasDerivedCategory.standard (SheafOfModules.{u} B.structureSheaf)
  let := HasDerivedCategory.standard AddCommGrpCat.{u}
  have hFG : ∀ I : SheafOfModules.{u} B.structureSheaf, Injective I →
      ((sheafSections B.topology AddCommGrpCat.{u}).obj (op W)).rightAcyclic
        ((SheafOfModules.toSheaf B.structureSheaf).obj I) := by
    intro I hI
    rw [Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat]
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    open Stacks.Cohomology.InjectiveModuleSheafAcyclicity in
    exact isZero_rightDerived_sections_toSheaf_succAtMorphismUniverse.{u}
      B.topology B.structureSheaf I W k
  exact IsZero.of_iso (BigSite.isZero_rightDerived_sections_of_isAdequate.{u, u} B F hF W q hq)
    (Stacks.Cohomology.AffineComparison.rightDerivedCollapseIso
      (SheafOfModules.toSheaf B.structureSheaf)
      ((sheafSections B.topology AddCommGrpCat.{u}).obj (op W)) hFG F
      (Functor.rightAcyclic_of_exact _ F) q)

/-- **[Stacks, Tag 06VM] (3) in the spelling `Stacks.Cohomology.moduleCohomology`.** The
positive-degree cohomology over an affine object of a chosen big site of an adequate module
vanishes, as a module over the sections of the structure sheaf there. -/
theorem BigSite.isZero_moduleCohomology_of_isAdequate
    (F : SheafOfModules.{u} B.structureSheaf) (hF : IsAdequate B F)
    (W : B.category) [IsAffine W.left.obj] (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.Cohomology.moduleCohomology B.structureSheaf W p F) := by
  let E := _root_.SheafOfModules.evaluation B.structureSheaf (op W)
  let G := forget₂ (ModuleCat.{u} (B.structureSheaf.obj.obj (op W))) AddCommGrpCat.{u}
  have hEadd : E.Additive := ⟨rfl⟩
  have hcomp : E ⋙ G ≅ B.sectionsOver W := Iso.refl _
  have hGz : IsZero (G.obj (Stacks.Cohomology.moduleCohomology B.structureSheaf W p F)) :=
    (B.isZero_rightDerived_sectionsOver_of_isAdequate F hF W p hp).of_iso
      ((Stacks.Cohomology.rightDerivedExactPostcompositionIso E G F p).trans
        ((Stacks.Cohomology.rightDerivedIsoOfFunctorIso hcomp p).app F))
  refine (IsZero.iff_id_eq_zero _).2 (G.map_injective ?_)
  rw [G.map_id, G.map_zero]
  exact hGz.eq_of_src _ _

/-! ### The affine objects and their coverings -/

/-- **The covering of an object of a chosen big site by its affine opens.** The members are the
open subschemes `V` of the scheme of `T` that are affine, each mapping to `T` by its open
immersion. -/
def BigSite.affineOpenHypercover (T : B.category) : PreZeroHypercover.{u + 1} T where
  I₀ := ULift.{u + 1} {V : T.left.obj.Opens // IsAffineOpen V}
  X i := B.restrictOpen T i.down.1
  f i := B.restrictOpenι T i.down.1

/-- The affine opens of the scheme of an object cover it for the topology of the site, open
immersions being `τ`-covering morphisms. -/
theorem BigSite.affineOpenHypercover_sieve₀_mem (T : B.category) :
    (B.affineOpenHypercover T).sieve₀ ∈ B.topology T := by
  refine sieve_generate_mem_topology_of_coveringMorphismProperty B _ _ (fun i => ?_)
    (fun x => ?_)
  · exact isOpenImmersion_le_coveringMorphismProperty τ _
      (inferInstanceAs (IsOpenImmersion (i.down.1.ι)))
  · obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := T.left.obj.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
    exact ⟨⟨⟨V, hV⟩⟩, ⟨x, hx⟩, rfl⟩

/-- The members of `Stacks.Adequate.BigSite.affineOpenHypercover` are affine objects. -/
theorem BigSite.isAffine_affineOpenHypercover_X (T : B.category)
    (i : (B.affineOpenHypercover T).I₀) :
    IsAffine ((B.affineOpenHypercover T).X i).left.obj :=
  i.down.2

/-- **The coverings of an object by affine objects are cofinal among all its coverings.** Given
a covering, cover each of its members by its affine opens; the composite family is a covering
by affine objects refining the given one, by the transitivity axiom of a Grothendieck topology. -/
def BigSite.affineCoveringSystem (V : B.category) :
    Stacks.Cohomology.CofinalCoveringSystem B.topology V where
  cov 𝒰 := 𝒰.sieve₀ ∈ B.topology V ∧ ∀ i, IsAffine (𝒰.X i).left.obj
  isCover _ h := h.1
  cofinal 𝒰 h𝒰 := by
    let 𝒱 := fun i : 𝒰.I₀ ↦ B.affineOpenHypercover (𝒰.X i)
    refine ⟨𝒰.bind 𝒱, ⟨?_, fun ij ↦ B.isAffine_affineOpenHypercover_X _ ij.2⟩,
      ⟨{ s₀ := Sigma.fst, h₀ := fun ij ↦ (𝒱 ij.1).f ij.2, w₀ := fun _ ↦ rfl }⟩⟩
    refine B.topology.transitive h𝒰 _ fun Y g hg ↦ ?_
    obtain ⟨Z, a, b, hb, rfl⟩ := hg
    obtain ⟨i⟩ := hb
    rw [Sieve.pullback_comp]
    refine B.topology.pullback_stable _
      (B.topology.superset_covering (fun W k hk ↦ ?_) (B.affineOpenHypercover_sieve₀_mem _))
    obtain ⟨W', c, d, hd, rfl⟩ := hk
    obtain ⟨j⟩ := hd
    simpa [PreZeroHypercover.bind] using
      (𝒰.bind 𝒱).sieve₀.downward_closed ((𝒰.bind 𝒱).sieve₀_f ⟨i, j⟩) c

/-- **The Olsson--Laszlo situation of [Stacks, Tag 0D6R] for the adequate modules** on a chosen
big site: the affine objects, with the coverings by affine objects as cofinal systems and the
bound `0`, on whose members the higher cohomology of an adequate module vanishes by
[Stacks, Tag 06VM] (3). -/
def BigSite.adequateOlssonLaszlo : Stacks.Cohomology.OlssonLaszloSituation.{u, u + 1, u, u} where
  C := B.category
  J := B.topology
  O := B.structureSheaf
  A := adequate.{u, u} B
  weakSerre := adequate_isWeakSerreClass B
  B := B.affineObjects
  basis_cover U := ⟨B.affineOpenHypercover U, B.affineOpenHypercover_sieve₀_mem U,
    fun i ↦ B.isAffine_affineOpenHypercover_X U i⟩
  degreeBound _ _ := 0
  coverings V _ := B.affineCoveringSystem V
  vanishing V _ 𝒰 h𝒰 i p hp F hF := by
    have : IsAffine (𝒰.X i).left.obj := h𝒰.2 i
    exact B.isZero_moduleCohomology_of_isAdequate F hF (𝒰.X i) p (by exact_mod_cast hp)

end Stacks.Adequate

end
