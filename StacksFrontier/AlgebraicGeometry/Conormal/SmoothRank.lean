module

public import StacksFrontier.AlgebraicGeometry.Conormal.SmoothKZeroClass
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.ShortExact
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank

/-!
# The rank of the conormal sheaf of an immersion of smooth schemes

Let `i : Z ⟶ X` be an immersion of schemes over `S`, with `X` smooth of relative dimension `d`
and `Z` smooth of relative dimension `e` over `S`. The conormal sheaf `𝒞_{Z/X}` is finite locally
free of rank `d - e`: by [Stacks, Tag 06AA] it is the kernel of the surjection
`i^*Ω_{X/S} ⟶ Ω_{Z/S}`, whose source and target are finite locally free of ranks `d` and `e`.

Over a field this says that a closed immersion of equidimensional smooth schemes of dimensions `e`
and `d` has a conormal sheaf of constant rank `d - e`, the codimension, which is the rank the
Grassmannian `𝐆(n - r, n)` of the proof of [Stacks, Tag 0FIR] is built for.

## Main results

* `Stacks.Conormal.isFiniteLocallyFreeOfRank_X₁_of_shortExact`: in a short exact sequence of
  finite locally free modules whose middle and last terms have constant ranks `a` and `c`, the
  first term has constant rank `a - c`.
* `Stacks.Conormal.isFiniteLocallyFreeOfRank_conormalSheaf_of_smoothOfRelativeDimension`: the
  rank of `𝒞_{Z/X}` is `d - e`.
* `Stacks.Conormal.isFiniteLocallyFreeOfRank_conormalSheaf_of_relativeDimension`: the same, for
  smooth morphisms of relative dimension `d` and `e` in the sense of [Stacks, Tag 02NJ].

## References

* [Stacks Project, Tag 06AA](https://stacks.math.columbia.edu/tag/06AA)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 0FIR](https://stacks.math.columbia.edu/tag/0FIR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Conormal

/-- **The first term of a short exact sequence of constant-rank modules has the difference
rank.** If `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` is short exact with `M₁` finite locally free and `M₂`, `M₃` of
constant ranks `a` and `c`, then `M₁` is of constant rank `a - c`. -/
theorem isFiniteLocallyFreeOfRank_X₁_of_shortExact {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (a c : ℕ)
    (h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₁)
    (h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ a)
    (h₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ c) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ (a - c) := by
  choose U hx r hr using fun x : X ↦
    Stacks.ProjectiveBundleSplitting.exists_isFiniteLocallyFreeOfRank_restrict S.X₁ h₁ x
  refine (Scheme.Modules.isFiniteLocallyFreeOfRank_iff S.X₁ (a - c)).mp ?_
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top U ?_ fun x ↦ ?_
  · refine eq_top_iff.mpr fun y _ ↦ ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨y, hx y⟩
  · let G := Scheme.Modules.restrictFunctor (U x).ι
    have hS' : (S.map G).ShortExact := hS.map_of_exact G
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.map G).X₁
        (r x) := hr x
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.map G).X₂ a :=
      (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mp
        (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff S.X₂ a).mpr h₂).restrict (U x).ι)
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.map G).X₃ c :=
      (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mp
        (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff S.X₃ c).mpr h₃).restrict (U x).ι)
    have h := AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact (S.map G) hS' (r x) a c
      (⟨x, hx x⟩ : (U x).toScheme)
    have hrx : r x = a - c := by omega
    exact (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mpr (hrx ▸ hr x)

/-- **The conormal sheaf of an immersion of smooth schemes has rank `d - e`.** For an immersion
`i : Z ⟶ X` over `p : X ⟶ S` with `p` smooth of relative dimension `d` and `i ≫ p` smooth of
relative dimension `e`, the conormal sheaf `𝒞_{Z/X}` is finite locally free of rank `d - e`. -/
theorem isFiniteLocallyFreeOfRank_conormalSheaf_of_smoothOfRelativeDimension {Z X S : Scheme.{u}}
    (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S) (d e : ℕ) [SmoothOfRelativeDimension d p]
    [SmoothOfRelativeDimension e (i ≫ p)] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := Z.ringCatSheaf)
      (conormalSheaf i : Z.Modules) (d - e) := by
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have : Smooth (i ≫ p) := SmoothOfRelativeDimension.smooth e (i ≫ p)
  have hS := Stacks.ConormalSequenceRight.conormalShortComplex_shortExact i p inferInstance
  have h₁ := sheafOfModules_isFiniteLocallyFree_conormalSheaf_of_smooth i p
  have := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials p d
  have h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.ConormalSequenceRight.conormalShortComplex i p).X₂ d :=
    Stacks.Chow.GenuineChern.isFiniteLocallyFreeOfRank_pullback i _ d
  have h₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.ConormalSequenceRight.conormalShortComplex i p).X₃ e :=
    Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials (i ≫ p) e
  have h₁' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.ConormalSequenceRight.conormalShortComplex i p).X₁ :=
    @AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso _ _ _
      (Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso i).symm h₁
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso i)
    (isFiniteLocallyFreeOfRank_X₁_of_shortExact _ hS d e h₁' h₂ h₃)

/-- **The conormal sheaf of an immersion of smooth schemes has rank `d - e`**, for relative
dimension in the sense of [Stacks, Tag 02NJ]: if `p : X ⟶ S` and `i ≫ p` are smooth, with every
nonempty fibre equidimensional of dimensions `d` and `e` respectively, then `𝒞_{Z/X}` is finite
locally free of rank `d - e`. Over a field `S = Spec k` this is the statement that a closed
immersion of smooth equidimensional schemes of dimensions `e` and `d` has conormal sheaf of
constant rank the codimension `d - e`. -/
theorem isFiniteLocallyFreeOfRank_conormalSheaf_of_relativeDimension {Z X S : Scheme.{u}}
    (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S) [Smooth p] [Smooth (i ≫ p)] (d e : ℕ)
    (hp : RelativeDimension p d) (hZ : RelativeDimension (i ≫ p) e) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := Z.ringCatSheaf)
      (conormalSheaf i : Z.Modules) (d - e) := by
  have : SmoothOfRelativeDimension d p :=
    Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq p d
      ((relativeDimension_iff_forall_topologicalKrullDimAt p d).mp hp)
  have : SmoothOfRelativeDimension e (i ≫ p) :=
    Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq (i ≫ p) e
      ((relativeDimension_iff_forall_topologicalKrullDimAt (i ≫ p) e).mp hZ)
  exact isFiniteLocallyFreeOfRank_conormalSheaf_of_smoothOfRelativeDimension i p d e

end Stacks.Conormal

end
