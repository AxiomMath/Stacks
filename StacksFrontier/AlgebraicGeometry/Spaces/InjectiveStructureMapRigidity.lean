module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickening

/-!
# Morphisms of algebraic spaces with injective structure map are epimorphisms to separated targets

Let `c : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` whose structure map
`c♯ : 𝒪_Y ⟶ c_*𝒪_X` is injective, for instance because `𝒪_Y = c_*𝒪_X`. Then the
scheme-theoretic image of `c` is `Y`: a closed subspace `Z ⊆ Y` through which `c` factors is the
whole of `Y`, its defining ideal being contained in the kernel of `c♯` ([Stacks, Tag 03MB]),
which is zero. Consequently `c` is an epimorphism against algebraic spaces separated over a
base: if `a, b : Y ⟶ W` agree after composition with a separated `q : W ⟶ Z` and after
precomposition with `c`, then `a = b`, because their equalizer is a closed subspace of `Y` (the
base change of the diagonal of `q`, a closed immersion) through which `c` factors.

This is the rigidity of the contraction `c : X ⟶ Y` of a prestable family of curves onto its
stable model in [Stacks, Tag 0E8A], where `𝒪_Y = c_*𝒪_X`: a morphism out of `Y` over the base
is determined by its composite with `c`, so an isomorphism of stable models under `X` is unique,
and the stable model is unique up to unique isomorphism.

## Main results

* `AlgebraicGeometry.Space.injective_structureSharp_app_of_mono`: a monomorphism
  `𝒪_Y ⟶ c_*𝒪_X` is injective on sections over every object of the small étale site of `Y`.
* `AlgebraicGeometry.Space.eq_top_of_comp_eq_of_injective_structureSharp`: a closed subspace
  through which `c` factors is the whole of `Y`.
* `AlgebraicGeometry.Space.hom_ext_of_injective_structureSharp`: morphisms out of `Y` into an
  algebraic space separated over a base are determined by their composites with `c`.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E8B](https://stacks.math.columbia.edu/tag/0E8B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **A monomorphism `𝒪_Y ⟶ c_*𝒪_X` is injective on sections**: its kernel inclusion vanishes,
being cancelled by the monomorphism, so a section killed by the structure map of `c` is zero. -/
theorem injective_structureSharp_app_of_mono (c : X ⟶ Y)
    [Mono (pushforwardStructureProjection B S hS c)] (U : (SmallEtale B S hS Y.1)ᵒᵖ) :
    Function.Injective ((structureSharp B S hS c).hom.app U) := by
  have h0 : (SheafOfModules.Submodule.ker (pushforwardStructureProjection B S hS c)).ι = 0 :=
    (cancel_mono (pushforwardStructureProjection B S hS c)).1
      ((SheafOfModules.Submodule.ker_ι_comp (pushforwardStructureProjection B S hS c)).trans
        zero_comp.symm)
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hmem : x ∈ (SheafOfModules.Submodule.ker (pushforwardStructureProjection B S hS c)).obj U :=
    (SheafOfModules.Submodule.mem_ker (pushforwardStructureProjection B S hS c) U x).2 hx
  exact congrArg (fun φ => φ.val.app U ⟨x, hmem⟩) h0

/-- **The scheme-theoretic image of a morphism with injective structure map is everything.** If
`c♯ : 𝒪_Y ⟶ c_*𝒪_X` is injective on sections and `c` factors through a closed subspace `Z ⊆ Y`,
then `Z = Y`: the defining ideal of `Z` is contained in the kernel of `c♯`
([Stacks, Tag 03MB]), which is zero, hence in the defining ideal of `Y`. -/
theorem eq_top_of_comp_eq_of_injective_structureSharp (c : X ⟶ Y)
    (hc : ∀ U, Function.Injective ((structureSharp B S hS c).hom.app U))
    (Z : ClosedSubspaces B S hS Y.1)
    (g : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (hg : g ≫ ObjectProperty.homMk Z.1.ι = c) : Z.1 = ⊤ := by
  refine top_le_iff.mp (le_of_definingIdealSheaf_le B S hS Y
    ⟨⊤, isClosedSubspace_top B S hS Y⟩ Z ?_)
  intro U s hs
  have hk : (structureSharp B S hS c).hom.app U s = 0 :=
    RingHom.mem_ker.1 (definingIdealSheaf_le_kernelIdealSheaf_of_comp_eq B S hS c Z g hg U hs)
  obtain rfl : s = 0 := hc U (hk.trans (map_zero _).symm)
  exact zero_mem _

/-- **A morphism with injective structure map is an epimorphism onto separated targets.** Let
`c : X ⟶ Y` have injective structure map `𝒪_Y ⟶ c_*𝒪_X`, let `q : W ⟶ Z` be separated, and let
`a, b : Y ⟶ W` satisfy `a ≫ q = b ≫ q` and `c ≫ a = c ≫ b`. Then `a = b`: the equalizer of `a`
and `b`, the base change of the diagonal of `q` along `(a, b) : Y ⟶ W ×_Z W`, is a closed
subspace of `Y` through which `c` factors, hence the whole of `Y`. -/
theorem hom_ext_of_injective_structureSharp {W Z : AlgebraicSpaces B S hS} (c : X ⟶ Y)
    (hc : ∀ U, Function.Injective ((structureSharp B S hS c).hom.app U))
    (q : W ⟶ Z) (hq : IsSeparated B S hS q.hom) {a b : Y ⟶ W} (hab : a ≫ q = b ≫ q)
    (hcab : c ≫ a = c ≫ b) : a = b := by
  have hab' : a.hom ≫ q.hom = b.hom ≫ q.hom := congrArg (fun φ => φ.hom) hab
  have hcab' : c.hom ≫ a.hom = c.hom ≫ b.hom := congrArg (fun φ => φ.hom) hcab
  let h : Y.obj ⟶ pullback q.hom q.hom := pullback.lift a.hom b.hom hab'
  let d := pullback.diagonal q.hom
  -- the equalizer `Y ×_{W ×_Z W} W ⟶ Y` is a closed immersion
  have hi : IsClosedImmersion B S hS (pullback.fst h d) :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback (IsPullback.of_hasPullback h d).flip hq
  have hE : IsAlgebraicSpace B S hS (pullback h d) :=
    isAlgebraicSpace_of_relativelyRepresentable B S hS _ hi.rep Y.2
  have hfa : pullback.fst h d ≫ a.hom = pullback.fst h d ≫ b.hom := by
    have h1 := congrArg (fun φ => φ ≫ pullback.fst q.hom q.hom)
      (pullback.condition (f := h) (g := d))
    have h2 := congrArg (fun φ => φ ≫ pullback.snd q.hom q.hom)
      (pullback.condition (f := h) (g := d))
    simp only [Category.assoc, h, d, pullback.lift_fst, pullback.lift_snd,
      pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id] at h1 h2
    exact h1.trans h2.symm
  let E : ClosedSubspaces B S hS Y.1 :=
    ⟨Subfunctor.range (pullback.fst h d),
      isClosedSubspace_range_of_isClosedImmersion B S hS _ hE hi⟩
  -- `c` factors through the equalizer
  have ht : c.hom ≫ h = (c.hom ≫ a.hom) ≫ d := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.diagonal_fst,
        Category.comp_id]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.diagonal_snd,
        Category.comp_id, hcab']
  let t : X.obj ⟶ pullback h d := pullback.lift c.hom (c.hom ≫ a.hom) ht
  let g : X ⟶ (⟨E.1.toFunctor, E.2.1⟩ : AlgebraicSpaces B S hS) :=
    ObjectProperty.homMk (t ≫ Subfunctor.toRange (pullback.fst h d))
  have hg : g ≫ ObjectProperty.homMk E.1.ι = c := by
    apply ObjectProperty.hom_ext
    show (t ≫ Subfunctor.toRange (pullback.fst h d)) ≫
      (Subfunctor.range (pullback.fst h d)).ι = c.hom
    rw [Category.assoc, Subfunctor.toRange_ι, pullback.lift_fst]
  have htop := eq_top_of_comp_eq_of_injective_structureSharp B S hS c hc E g hg
  apply ObjectProperty.hom_ext
  ext T y
  have hy : y ∈ (Subfunctor.range (pullback.fst h d)).obj T := by
    show y ∈ E.1.obj T
    rw [htop]
    trivial
  obtain ⟨e, rfl⟩ := hy
  exact congrArg (fun φ : pullback h d ⟶ W.obj => φ.app T e) hfa

end AlgebraicGeometry.Space

end
