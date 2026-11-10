module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.Modification
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalRankTwo
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SplittingPrinciple

/-!
# Filtrations with invertible quotients after a modification

On an integral scheme `X` a finite locally free module `ℰ` of rank `r` acquires, after pullback
along a modification `f : X' ⟶ X`, a filtration of length `r` whose `r` successive quotients are
invertible `𝒪_{X'}`-modules, provided every finite locally free module of rank at least two on
an integral scheme admits a `Stacks.Divisors.BundleSplittingDatum`.

## Main definitions

* `Stacks.Divisors.BundleSplittingDatum`: a proper morphism `π : P ⟶ Y`, a short exact
  sequence `0 ⟶ ℱ ⟶ π^*ℰ ⟶ 𝒪_P(1) ⟶ 0` which stays short exact under every pullback, with
  invertible quotient and kernel of rank `r`, and a section of `π` over a nonempty open of `Y`.

## Main results

* `Stacks.Divisors.isBirational_of_isOpenImmersion_factorization`: a morphism of irreducible
  schemes which a dominant open immersion factors through is birational.
* `Stacks.Divisors.isModification_imageι_comp`: the scheme-theoretic image of a section of a
  proper morphism over a nonempty open of an integral scheme is a modification of it.
* `Stacks.Divisors.exists_modification_hasInvertibleFiltration`: given splitting data for the
  projective bundles of all finite locally free modules of rank at least two on integral
  schemes, a finite locally free module of rank `r` on an integral scheme acquires, after
  pullback along a modification, a filtration of length `r` with invertible successive
  quotients.

## References

* [Stacks Project, Tag 0AYP](https://stacks.math.columbia.edu/tag/0AYP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.WeilCohomology (HasInvertibleFiltration)
open scoped ZeroObject

universe u

namespace Stacks.Divisors

/-! ### Modifications -/

/-- A morphism of irreducible schemes through which a dominant open immersion factors is
birational. -/
theorem isBirational_of_isOpenImmersion_factorization
    {U X Y : Scheme.{u}} [IrreducibleSpace U] [IrreducibleSpace X] [IrreducibleSpace Y]
    (i : U ⟶ X) (j : U ⟶ Y) (f : X ⟶ Y) [IsOpenImmersion i] [IsDominant i]
    [IsOpenImmersion j] [IsDominant j] (h : i ≫ f = j) : IsBirational f := by
  have hmap {A B : Scheme.{u}} [IrreducibleSpace A] [IrreducibleSpace B] (g : A ⟶ B)
      [IsDominant g] : g (genericPoint A) = genericPoint B := by
    refine IsGenericPoint.eq ?_ (genericPoint_spec B)
    simpa only [Set.image_univ, g.denseRange.closure_range] using
      (genericPoint_spec A).image g.continuous
  have hf : f (genericPoint X) = genericPoint Y := by
    rw [← hmap i, ← hmap j]
    exact congrArg (fun k : U ⟶ Y => k (genericPoint U)) h
  refine ⟨?_, ?_⟩
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
    exact Set.bijOn_singleton.mpr hf
  · intro x hx
    have hx' : x = genericPoint X := by
      simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hx
    subst x
    rw [← hmap i]
    have hiso : IsIso ((i ≫ f).stalkMap (genericPoint U)) := by rw [h]; infer_instance
    rw [Scheme.Hom.stalkMap_comp] at hiso
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (f.stalkMap (i (genericPoint U)))
      (i.stalkMap (genericPoint U)) inferInstance hiso

/-- Let `X` be integral, `p : P ⟶ X` proper and `s` a section of `p` over a nonempty open
`U ⊆ X`. The projection to `X` of the scheme-theoretic image of `s` is a modification of `X`. -/
theorem isModification_imageι_comp {X P : Scheme.{u}} [IsIntegral X] (p : P ⟶ X) [IsProper p]
    (U : X.Opens) [Nonempty U] (s : U.toScheme ⟶ P) (hs : s ≫ p = U.ι) :
    IsModification (s.imageι ≫ p) := by
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have : IrreducibleSpace U.toScheme := inferInstance
  have : IsImmersion (s ≫ p) := by rw [hs]; infer_instance
  have : IsImmersion s := IsImmersion.of_comp s p
  have : IsOpenImmersion s.toImage := isOpenImmersion_toImage s (.inr inferInstance)
  have : IsDominant s.toImage := isDominant_toImage s (.inr inferInstance)
  have : IsReduced s.image := inferInstance
  have : IrreducibleSpace s.image := by
    refine (irreducibleSpace_def _).mpr ?_
    change IsIrreducible (Set.univ : Set s.image)
    rw [← s.toImage.denseRange.closure_range]
    simpa only [Set.image_univ] using
      ((IrreducibleSpace.isIrreducible_univ U.toScheme).image
        s.toImage s.toImage.continuous.continuousOn).closure
  have : IsDominant U.ι :=
    ⟨U.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _⟩
  exact ⟨isBirational_of_isOpenImmersion_factorization s.toImage U.ι (s.imageι ≫ p)
      (by rw [← Category.assoc, Scheme.Hom.toImage_imageι, hs]), inferInstance,
    isIntegral_of_irreducibleSpace_of_isReduced _⟩

/-! ### The splitting data of the projective bundle -/

/-- Splitting data for a module `ℰ` on `Y`: a proper morphism `π : P ⟶ Y`, a short exact
sequence `0 ⟶ ℱ ⟶ π^*ℰ ⟶ 𝒪_P(1) ⟶ 0` which stays short exact under every pullback, whose
quotient is invertible and whose kernel is finite locally free of rank `r`, and a section of `π`
over a nonempty open of `Y`. -/
structure BundleSplittingDatum (Y : Scheme.{u}) (E : Y.Modules) (r : ℕ) where
  /-- The projective bundle of `E`. -/
  bundle : Scheme.{u}
  /-- Its projection to the base. -/
  proj : bundle ⟶ Y
  /-- The projection is proper. -/
  isProper_proj : IsProper proj
  /-- The tautological kernel `ℱ`. -/
  sub : bundle.Modules
  /-- The degree-one twist `𝒪_{𝐏(ℰ)}(1)`. -/
  twist : bundle.Modules
  /-- The inclusion of the tautological kernel. -/
  incl : sub ⟶ (Scheme.Modules.pullback proj).obj E
  /-- The tautological surjection onto the twist. -/
  quot : (Scheme.Modules.pullback proj).obj E ⟶ twist
  /-- The two maps compose to zero. -/
  incl_comp_quot : incl ≫ quot = 0
  /-- The sequence stays short exact under every pullback. -/
  shortExact_pullback : ∀ {Z : Scheme.{u}} (h : Z ⟶ bundle),
    ((ShortComplex.mk incl quot incl_comp_quot).map (Scheme.Modules.pullback h)).ShortExact
  /-- The twist is invertible. -/
  twist_isInvertible : AlgebraicGeometry.SheafOfModules.IsInvertible bundle.presheaf
    bundle.ringCatSheaf.2 twist
  /-- The tautological kernel has rank one less than `E`. -/
  sub_rank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} sub r
  /-- An open of the base. -/
  trivialOpen : Y.Opens
  /-- It is nonempty. -/
  nonempty_trivialOpen : Nonempty trivialOpen
  /-- A section of the projection over `trivialOpen`. -/
  sect : trivialOpen.toScheme ⟶ bundle
  /-- `sect` is a section of the projection. -/
  sect_comp_proj : sect ≫ proj = trivialOpen.ι

/-! ### Tag 0AYP -/

/-- Suppose every finite locally free module of rank `m + 2` on an integral scheme admits a
`BundleSplittingDatum` with kernel of rank `m + 1`. Let `X` be an integral scheme and `ℰ` a
finite locally free `𝒪_X`-module of rank `r`. There is a modification `f : X' ⟶ X` such that
`f^*ℰ` has a filtration of length `r` whose successive quotients are invertible
`𝒪_{X'}`-modules. -/
theorem exists_modification_hasInvertibleFiltration
    (hdatum : ∀ (Y : Scheme.{u}) [IsIntegral Y] (F : Y.Modules) (m : ℕ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (m + 2) →
        Nonempty (BundleSplittingDatum Y F (m + 1)))
    (r : ℕ) (X : Scheme.{u}) [IsIntegral X] (E : X.Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    ∃ (X' : Scheme.{u}) (f : X' ⟶ X), IsModification f ∧
      HasInvertibleFiltration X' ((Scheme.Modules.pullback f).obj E) r := by
  induction r using Nat.strong_induction_on generalizing X with
  | h r ih =>
    by_cases hr : r ≤ 1
    · exact ⟨X, 𝟙 X, isModification_id X,
        HasInvertibleFiltration.of_iso ((Scheme.Modules.pullbackId X).app E).symm
          (Stacks.WeilCohomology.hasInvertibleFiltration_of_rank_le_one E r hE hr)⟩
    obtain ⟨m, hm⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
    subst hm
    obtain ⟨D⟩ := hdatum X E m hE
    have := D.isProper_proj
    have := D.nonempty_trivialOpen
    have hmod := isModification_imageι_comp D.proj D.trivialOpen D.sect D.sect_comp_proj
    have : IsIntegral D.sect.image := hmod.2.2
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.sub (m + 1) :=
      D.sub_rank
    obtain ⟨Z, g, hg, hfilt⟩ := ih (m + 1) (by omega) D.sect.image
      ((Scheme.Modules.pullback D.sect.imageι).obj D.sub)
      (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback D.sect.imageι D.sub (m + 1))
    set h : Z ⟶ D.bundle := g ≫ D.sect.imageι with hh
    have hsubfilt : HasInvertibleFiltration Z ((Scheme.Modules.pullback h).obj D.sub) (m + 1) :=
      HasInvertibleFiltration.of_iso
        ((Scheme.Modules.pullbackComp g D.sect.imageι).app D.sub) hfilt
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback D.proj).obj E) (m + 2) :=
      AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback D.proj E (m + 2)
    have hrk : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback D.proj).obj E)) (m + 2) :=
      AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback h _ (m + 2)
    have hstep : HasInvertibleFiltration Z
        ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback D.proj).obj E)) (m + 1 + 1) :=
      HasInvertibleFiltration.step ((Scheme.Modules.pullback h).map D.incl)
        ((Scheme.Modules.pullback h).map D.quot)
        (by rw [← Functor.map_comp, D.incl_comp_quot, Functor.map_zero])
        (D.shortExact_pullback h)
        (Stacks.RelativeProj.isInvertible_pullback_obj h D.twist D.twist_isInvertible)
        hrk.isFiniteLocallyFree hsubfilt
    refine ⟨Z, g ≫ (D.sect.imageι ≫ D.proj), ?_, ?_⟩
    · have := hg.2.1
      have := hmod.2.1
      exact ⟨AlgebraicGeometry.IsBirational.comp hg.1 hmod.1, inferInstance, hg.2.2⟩
    · have hiso := HasInvertibleFiltration.of_iso
        ((Scheme.Modules.pullbackComp h D.proj).app E) hstep
      simpa only [hh, Category.assoc] using hiso

end Stacks.Divisors

end
