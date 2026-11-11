module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceRelativeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupportClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupportClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupportProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupportSpecializes

/-!
# The derived existence theorem with supports: the support of each `Hⁱ(K)` is proper

In the situation of `AlgebraicGeometry.Space.SupportedDerivedExistenceSystem` (Stacks 0DIR, `X`
flat over `A`), the source asserts that the object `K ∈ D(𝒪_X)` it constructs is supported on a
closed subset of `|X|` proper over `A`. That assertion fails (see
`StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupported` and the entry for
0DIR in `errata.md`). What holds is the per-degree statement: for every `i` the support of the
cohomology sheaf `Hⁱ(K)` lies in a closed subset `Tᵢ ⊆ |X|` proper over `A`. This file proves it
for every `X` (the affine case is
`StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupportedAffine`).

## The proof

Take `Tᵢ = ⋃_{j ≥ i} Supp Hʲ(K)` for `K = DQ_X(R lim Kₙ)`.

* `Tᵢ` is closed (`…isClosed_iUnion_supportOfSheaf_homology_quasicoherentLimit`, Nakayama on the
  top cohomology of the pseudo-coherent sections of `K` over an affine étale chart);
* `Tᵢ ∩ |X₀|` lies in the image of `Z₀` (`…supportOfSheaf_homology_quasicoherentLimit_inter_…`,
  from `Lj₀^*K ≅ K₀` and Nakayama);
* every point of `Tᵢ` specializes into `|X₀|`
  (`…exists_specializes_mem_range_of_mem_supportOfSheaf_homology_quasicoherentLimit`, from the
  vanishing of `Hʲ(K)` on closed subsets with quasi-compact complement missing `|X₀|`);
* so `Tᵢ` is proper over `A`
  (`AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem.isProperOver_of_forall_specializes`).

## Main results

* `…SupportedDerivedExistenceSystem.exists_isProperOver_supportOfSheaf_homology_…_subset_of_…`:
  for every `i`, `Supp Hⁱ(K)` lies in a closed subset of `|X|` proper over `A`.
* `…SupportedDerivedExistenceSystem.exists_isRelativelyPseudoCoherent_stageDerivedPullback_iso_…`:
  the conclusion of
  `…SupportedDerivedExistenceSystem.exists_isRelativelyPseudoCoherent_stageDerivedPullback_iso`
  together with the per-degree support clause.
* `…RelativeDerivedExistenceSystem.exists_isRelativelyPseudoCoherent_stageDerivedPullback_iso_…`:
  the same for the data of the remark (`Kₙ` pseudo-coherent relative to `Aₙ`), `X` flat.

## References

* [Stacks Project, Tag 0DIR](https://stacks.math.columbia.edu/tag/0DIR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] pointTopology
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

namespace SupportedDerivedExistenceSystem

variable (D : SupportedDerivedExistenceSystem.{u})

/-- **The support of each cohomology sheaf of `K` is proper over `A`.** For
`K = DQ_X(R lim Kₙ)` and every `i` there is a closed subset `T ⊆ |X|`, proper over `Spec A`,
containing the support of `Hⁱ(K)`: `T = ⋃_{j ≥ i} Supp Hʲ(K)` is closed, meets `|X₀|` inside
`Z₀`, and each of its points specializes into `|X₀|`. -/
theorem exists_isProperOver_supportOfSheaf_homology_quasicoherentLimit_subset_of_separated
    (i : ℤ) :
    ∃ (T : Set (points D.B (limitBase D.system) D.containsLimitBase D.X.left.1))
      (hT : IsClosed T),
      IsProperOver D.B (limitBase D.system) D.containsLimitBase D.X.left.2
          (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2 D.X.hom.hom
          (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
            D.containsLimitBase D.finitePresentation.1) T hT ∧
        supportOfSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left.1
          ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite D.B (limitBase D.system) D.containsLimitBase D.X.left.1
              D.X.left.2).O)).obj
            ((DerivedCategory.homologyFunctor (Modules.{u, u} D.B (limitBase D.system)
              D.containsLimitBase D.X.left.1 D.X.left.2) i).obj
              ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
                D.X.left).ι.obj D.quasicoherentLimit))) ⊆ T := by
  have hT := D.isClosed_iUnion_supportOfSheaf_homology_quasicoherentLimit i
  refine ⟨_, hT, D.1.isProperOver_of_forall_specializes (D.support 0) (D.isClosed_support 0)
    (D.isProperOver_support 0) _ hT ?_ ?_, fun x hx => Set.mem_iUnion₂.2 ⟨i, le_rfl, hx⟩⟩
  · rintro x ⟨hx, hx₀⟩
    obtain ⟨j, -, hj⟩ := Set.mem_iUnion₂.1 hx
    exact D.supportOfSheaf_homology_quasicoherentLimit_inter_range_subset j ⟨hj, hx₀⟩
  · intro x hx
    obtain ⟨j, -, hj⟩ := Set.mem_iUnion₂.1 hx
    exact D.exists_specializes_mem_range_of_mem_supportOfSheaf_homology_quasicoherentLimit j x hj

/-- `exists_isProperOver_supportOfSheaf_homology_quasicoherentLimit_subset_of_separated`, for an
object of `D(𝒪_X)` given as equal to `K = DQ_X(R lim Kₙ)`. -/
theorem exists_isProperOver_supportOfSheaf_homology_subset_of_eq_of_separated
    (K : D.limitDerivedCategory)
    (hK : K = (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
      D.quasicoherentLimit) (i : ℤ) :
    ∃ (T : Set (points D.B (limitBase D.system) D.containsLimitBase D.X.left.1))
      (hT : IsClosed T),
      IsProperOver D.B (limitBase D.system) D.containsLimitBase D.X.left.2
          (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2 D.X.hom.hom
          (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
            D.containsLimitBase D.finitePresentation.1) T hT ∧
        supportOfSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left.1
          ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite D.B (limitBase D.system) D.containsLimitBase D.X.left.1
              D.X.left.2).O)).obj
            ((DerivedCategory.homologyFunctor (Modules.{u, u} D.B (limitBase D.system)
              D.containsLimitBase D.X.left.1 D.X.left.2) i).obj K)) ⊆ T := by
  subst hK
  exact D.exists_isProperOver_supportOfSheaf_homology_quasicoherentLimit_subset_of_separated i

/-- **Grothendieck's existence theorem in its derived form, with supports proper over the base
(Stacks 0DIR, `X` flat over `A`, the per-degree support clause).** There is `K ∈ D(𝒪_X)`,
pseudo-coherent relative to `A`, with isomorphisms `ψₙ : Ljₙ^* K ≅ Kₙ` such that
`ψₙ = (Ljₙ^* ≅ Liₙ^* Ljₙ₊₁^*) ≫ Liₙ^* ψₙ₊₁ ≫ φₙ`, and such that for every `i` the support of the
cohomology sheaf `Hⁱ(K)` lies in a closed subset of `|X|` proper over `Spec A`. The source's
clause that the whole of `K` is supported on one closed subset proper over `A` fails (see the
module `StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupported`); this is
the per-degree form, which holds. -/
@[stacks 0DIR "corrected form, X flat: K pseudo-coherent relative to A, Lj_n^* K = K_n \
compatibly with the phi_n, and each cohomology sheaf of K supported on a closed subset proper \
over A; the one-subset support clause and the case of non-flat X are false (errata 0DIR)"]
theorem exists_isRelativelyPseudoCoherent_stageDerivedPullback_iso_isProperOver_supportOfSheaf :
    ∃ (K : D.limitDerivedCategory)
      (ψ : ∀ n : ℕ, (D.stageDerivedPullback n).obj K ≅ D.K n)
      (hK : QcohDerived D.B (limitBase D.system) D.containsLimitBase D.X.left K),
      IsRelativelyPseudoCoherent D.B (limitBase D.system) D.containsLimitBase D.X.left.1
          D.X.left.2 D.X.hom.hom
          (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
            D.containsLimitBase D.finitePresentation.1) ⟨K, hK⟩ ∧
        (∀ n : ℕ, (ψ n).hom = (D.stageDerivedPullbackCompIso n).inv.app K ≫
          (transitionDerivedPullback D.system D.B D.containsLimitBase D.containsBaseAt D.X n).map
            (ψ (n + 1)).hom ≫ D.φ n) ∧
        ∀ i : ℤ, ∃ (T : Set (points D.B (limitBase D.system) D.containsLimitBase D.X.left.1))
          (hT : IsClosed T),
          IsProperOver D.B (limitBase D.system) D.containsLimitBase D.X.left.2
              (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2 D.X.hom.hom
              (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
                D.containsLimitBase D.finitePresentation.1) T hT ∧
            supportOfSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left.1
              ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite D.B (limitBase D.system) D.containsLimitBase D.X.left.1
                  D.X.left.2).O)).obj
                ((DerivedCategory.homologyFunctor (Modules.{u, u} D.B (limitBase D.system)
                  D.containsLimitBase D.X.left.1 D.X.left.2) i).obj K)) ⊆ T := by
  obtain ⟨K, ψ, hKeq, hKpc, hψ⟩ :=
    D.1.exists_eq_quasicoherentLimit_isPseudoCoherentOnLimit_stageDerivedPullback_iso
      D.stageSectionsPseudoCoherent
  have hK := derivedCategoryB_of_isPseudoCoherent_unconditional D.B (limitBase D.system)
    D.containsLimitBase _ _ K hKpc
  exact ⟨K, ψ, hK, (isRelativelyPseudoCoherent_iff_isPseudoCoherent D.B (limitBase D.system)
    D.containsLimitBase D.X.hom D.flat D.finitePresentation.1 ⟨K, hK⟩).2 hKpc, hψ,
    D.exists_isProperOver_supportOfSheaf_homology_subset_of_eq_of_separated K hKeq⟩

end SupportedDerivedExistenceSystem

namespace RelativeDerivedExistenceSystem

variable (D : RelativeDerivedExistenceSystem.{u})

/-- **The generalized derived existence theorem for the data of Stacks 0DIR, `X` flat over `A`,
with the per-degree support clause.** Let `(Aₙ)`, `X` separated and of finite presentation over
`A = lim Aₙ`, and `Kₙ ∈ D_QCoh(𝒪_{Xₙ})` pseudo-coherent relative to `Aₙ`, supported on closed
subsets of `|Xₙ|` proper over `Aₙ`, with isomorphisms `φₙ : Liₙ^* Kₙ₊₁ ≅ Kₙ`, be as in the
remark, and let `X` be flat over `A`. Then there is `K ∈ D_QCoh(𝒪_X)`, pseudo-coherent relative
to `A`, with isomorphisms `ψₙ : Ljₙ^* K ≅ Kₙ` such that
`ψₙ = (Ljₙ^* ≅ Liₙ^* Ljₙ₊₁^*) ≫ Liₙ^* ψₙ₊₁ ≫ φₙ`, and such that for every `i` the support of
`Hⁱ(K)` lies in a closed subset of `|X|` proper over `Spec A`. -/
@[stacks 0DIR "corrected form on the remark's own data (X separated, of finite presentation, \
K_n pseudo-coherent relative to A_n, supported on closed subsets proper over A_n) with X flat: K \
pseudo-coherent relative to A, Lj_n^* K = K_n compatibly, each cohomology sheaf of K supported on \
a closed subset proper over A; flatness is necessary and one closed subset for all of K fails \
(errata 0DIR)"]
theorem exists_isRelativelyPseudoCoherent_stageDerivedPullback_iso_isProperOver_supportOfSheaf
    (hflat : IsFlat D.B (limitBase D.system) D.containsLimitBase D.X.hom.hom) :
    ∃ (K : (D.toSupported hflat).limitDerivedCategory)
      (ψ : ∀ n : ℕ, ((D.toSupported hflat).stageDerivedPullback n).obj K ≅ D.K n)
      (hK : QcohDerived D.B (limitBase D.system) D.containsLimitBase D.X.left K),
      IsRelativelyPseudoCoherent D.B (limitBase D.system) D.containsLimitBase D.X.left.1
          D.X.left.2 D.X.hom.hom
          (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
            D.containsLimitBase D.finitePresentation.1) ⟨K, hK⟩ ∧
        (∀ n : ℕ, (ψ n).hom = ((D.toSupported hflat).stageDerivedPullbackCompIso n).inv.app K ≫
          (transitionDerivedPullback D.system D.B D.containsLimitBase D.containsBaseAt D.X n).map
            (ψ (n + 1)).hom ≫ D.φ n) ∧
        ∀ i : ℤ, ∃ (T : Set (points D.B (limitBase D.system) D.containsLimitBase D.X.left.1))
          (hT : IsClosed T),
          IsProperOver D.B (limitBase D.system) D.containsLimitBase D.X.left.2
              (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2 D.X.hom.hom
              (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
                D.containsLimitBase D.finitePresentation.1) T hT ∧
            supportOfSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left.1
              ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite D.B (limitBase D.system) D.containsLimitBase D.X.left.1
                  D.X.left.2).O)).obj
                ((DerivedCategory.homologyFunctor (Modules.{u, u} D.B (limitBase D.system)
                  D.containsLimitBase D.X.left.1 D.X.left.2) i).obj K)) ⊆ T :=
  (D.toSupported
    hflat).exists_isRelativelyPseudoCoherent_stageDerivedPullback_iso_isProperOver_supportOfSheaf

end RelativeDerivedExistenceSystem

end AlgebraicGeometry.Space

end
