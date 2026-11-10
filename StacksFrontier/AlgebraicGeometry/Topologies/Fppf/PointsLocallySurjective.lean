module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings

/-!
# An fppf covering map is a local surjection on functors of points

A surjective, flat, locally finitely presented morphism `f : U ⟶ M` of schemes over a scheme `S`
induces a locally surjective map of the restricted functors of points on any big fppf site of
`S`: a section of the functor of points of `M` over a test object of the site lifts to `U` after
an fppf covering of that test object, namely one refining the base change of `f`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.isLocallySurjective_points_map_of_fppf` is the local surjection.

## Implementation notes

The one point of the proof is that the fibre product `U ×_M T` of the morphism with a test object
`T` of the site need not itself be an object of the site, because the site carries a cardinality
cutoff. The singleton fppf covering of `T` that the fibre product defines is therefore refined to
one of the site's chosen covering families, by
`AlgebraicGeometry.exists_isCovering_refining_fppfCovering`, before the covering sieve is formed;
the lift of the section is then the first projection, read on a member of the refinement.

There are two `private` copies of this statement in the library,
`points_map_isLocallySurjective_of_fppf` in
`StacksFrontier/AlgebraicGeometry/Groupoids/Stabilizer/AffineQuotient.lean` and the inner `hp` of
`sheafified_fppf_map_locallySurjective` in
`StacksFrontier/AlgebraicGeometry/Spaces/RestrictedQuotientOpenImmersion.lean`. The statement
mentions no groupoid and no quotient, so this is its home; both copies should be deleted in favour
of it, and this module is deliberately small so that either file can import it without acquiring
anything else.

The representable sibling of this statement is, in the namespace
`AlgebraicGeometry.Space` of
`StacksFrontier/AlgebraicGeometry/Spaces/Presentation/Surjective.lean`,
`isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective`,
which carries `@[stacks 05VM]`. It does not subsume this one: it asks the morphism of sheaves to
be relatively representable with the three properties on every represented base change, and that
is exactly what the cutoff of the site obstructs here, since the fibre product with a test object
need not belong to the site.

## References

* [Stacks Project, Tag 05VM](https://stacks.math.columbia.edu/tag/05VM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A surjective, flat, locally finitely presented morphism of `S`-schemes induces a locally
surjective map of the restricted functors of points on a big fppf site of `S`.

The fibre product of the morphism with a test object of the site need not be an object of the
site, so the singleton fppf covering it defines is refined to one of the site's chosen covering
families. -/
theorem isLocallySurjective_points_map_of_fppf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U M : Over S} (f : U ⟶ M)
    [Flat f.left] [LocallyOfFinitePresentation f.left] [Surjective f.left] :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      ((Over.post B.inclusion).op.whiskerLeft (yoneda.map f)) := by
  classical
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let F : C ⥤ Over S := Over.post B.inclusion
  refine ⟨?_⟩
  intro X s
  let P : Over S := Over.mk
    (pullback.snd f.left s.left ≫ ((Over.post B.inclusion).obj X).hom)
  let p₁ : P ⟶ U := Over.homMk (pullback.fst f.left s.left) (by
    calc
      pullback.fst f.left s.left ≫ U.hom =
          pullback.fst f.left s.left ≫ f.left ≫ M.hom := by rw [← Over.w f]
      _ = pullback.snd f.left s.left ≫ s.left ≫ M.hom :=
        congrArg (fun g => g ≫ M.hom) pullback.condition
      _ = pullback.snd f.left s.left ≫ ((Over.post B.inclusion).obj X).hom :=
        congrArg (fun g => pullback.snd f.left s.left ≫ g) (Over.w s))
  let p₂ : P ⟶ (Over.post B.inclusion).obj X :=
    Over.homMk (pullback.snd f.left s.left) rfl
  let E : PreZeroHypercover.{u + 1} (B.inclusion.obj X.left) :=
    PreZeroHypercover.singleton p₂.left
  have hPflat : Flat (pullback.snd f.left s.left) := by infer_instance
  have hPlfp : LocallyOfFinitePresentation (pullback.snd f.left s.left) := by infer_instance
  have hPsurj : Surjective (pullback.snd f.left s.left) := by infer_instance
  have hE : E.presieve₀ ∈ Scheme.fppfPrecoverage (B.inclusion.obj X.left) := by
    change E.presieve₀ ∈ Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)
      (B.inclusion.obj X.left)
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro y
      obtain ⟨x, hx⟩ := hPsurj.surj y
      exact ⟨PUnit.unit, x, hx⟩
    · intro i
      exact ⟨hPflat, hPlfp⟩
  obtain ⟨V, hV, href⟩ := exists_isCovering_refining_fppfCovering B X.left E hE
  rcases href with ⟨ref⟩
  have hRcov : (Sieve.overEquiv X).symm V.sieve₀ ∈ J X := by
    rw [GrothendieckTopology.mem_over_iff]
    simpa [PreZeroHypercover.sieve₀, Sieve.ofArrows] using
      (Precoverage.generate_mem_toGrothendieck
        (show V.presieve₀ ∈ B.precoverage X.left from ⟨V, rfl, hV⟩))
  have hle : (Sieve.overEquiv X).symm V.sieve₀ ≤
      Presheaf.imageSieve (F.op.whiskerLeft (yoneda.map f)) s := by
    rw [← ((Sieve.overEquiv X).symm).apply_symm_apply
      (Presheaf.imageSieve (F.op.whiskerLeft (yoneda.map f)) s)]
    rw [((Sieve.overEquiv X).symm).map_rel_iff]
    simp only [OrderIso.symm_symm]
    rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, Sieve.generate_le_iff,
      Presieve.ofArrows_le_iff]
    intro i
    let i' : (PreZeroHypercover.map B.inclusion V).I₀ := i
    let W : C := Over.mk (V.f i ≫ X.hom)
    let α : W ⟶ X := Over.homMk (V.f i) (by simp [W])
    let b := ref.h₀ i'
    have href0 : ref.h₀ i' ≫ p₂.left = (V.f i').hom := by
      simpa [E, F, Over.post, PreZeroHypercover.singleton,
        PreZeroHypercover.map] using ref.w₀ i'
    have hbp : b ≫ p₂.left = B.inclusion.map (V.f i') := by
      simpa [b, BigFppfSite.inclusion, schemeBelowInclusion] using href0
    have hbOver : b ≫ P.hom = (F.obj W).hom := by
      change b ≫ (pullback.snd f.left s.left ≫ B.inclusion.map X.hom) =
        B.inclusion.map (V.f i) ≫ B.inclusion.map X.hom
      exact congrArg (fun g => g ≫ B.inclusion.map X.hom) hbp
    let β : F.obj W ⟶ P := Over.homMk b hbOver
    have hlift : (F.op.whiskerLeft (yoneda.map f)).app (op W) (β ≫ p₁) = F.map α ≫ s := by
      apply Over.OverMorphism.ext
      change b ≫ (p₁.left ≫ f.left) = B.inclusion.map (V.f i') ≫ s.left
      have hpb : b ≫ (p₁.left ≫ f.left) = b ≫ (p₂.left ≫ s.left) :=
        congrArg (fun g => b ≫ g) pullback.condition
      exact hpb.trans ((Category.assoc b p₂.left s.left).symm.trans
        (congrArg (fun g => g ≫ s.left) hbp))
    change (Sieve.overEquiv X
        (Presheaf.imageSieve (F.op.whiskerLeft (yoneda.map f)) s)) (V.f i)
    rw [Sieve.overEquiv_iff, Presheaf.imageSieve_apply]
    exact ⟨β ≫ p₁, hlift⟩
  exact J.superset_covering hle hRcov

end AlgebraicGeometry

end

end
