module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FullnessViaSigmaSite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism

/-!
# Quasi-coherence descends along the charts of the members of an étale family

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be a family of
algebraic spaces étale over `X` whose charts are cover dense in the small étale site of `X`, for
instance a Zariski covering.  An `𝒪_X`-module all of whose étale restrictions to the members of
the family are quasi-coherent is quasi-coherent.

This is the clause of Stacks 03M0 relating conditions (1) and (2),
`AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleModulePullback_iff`, for a *family* of étale
morphisms instead of a single surjective one: no coproduct of the members is formed, and the
single surjective morphism of that statement is replaced by cover density of the charts of the
members, which is what a covering supplies.

All names below are in the namespace `AlgebraicGeometry.Space.QuasiCoherentDescent`.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent`
  `.isQuasicoherentOnSite_of_forall_etaleModulePullback`:
  **an `𝒪_X`-module whose étale restriction to every member of the family is quasi-coherent is
  quasi-coherent.**

## Implementation notes

The proof is the converse direction of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleModulePullback_iff` with the covering of the
final object it uses replaced by cover density.  Quasi-coherence is tested by
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation` on the
charts of `X` carrying a global presentation; over a chart of `X` the sieve of the morphisms
factoring through a chart of a member is covering, and over such a morphism the quasi-coherence
of the étale restriction supplies a covering of the corresponding chart of the member on whose
members a global presentation exists, which
`AlgebraicGeometry.Space.hasGlobalPresentation_over_postcomp_iff` carries back to the composite
charts of `X`.

## References

* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

section CoverDense

variable [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-- **AN `𝒪_X`-MODULE WHOSE ÉTALE RESTRICTION TO EVERY MEMBER OF THE FAMILY IS QUASI-COHERENT IS
QUASI-COHERENT.**  This is the clause of Stacks 03M0 relating conditions (1) and (2) for a family
of étale morphisms whose charts are cover dense, in place of a single surjective one. -/
theorem isQuasicoherentOnSite_of_forall_etaleModulePullback
    (M : Modules.{u, u} B S hS X.1 X.2)
    (h : ∀ i, ((etaleModulePullback.{u, u} B S hS (f i) (hf i)).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite := by
  refine (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation
    M).2 ⟨{Z : (smallEtaleRingedSite B S hS X.1 X.2).C // (M.over Z).HasGlobalPresentation},
      fun z => z.1, fun W => ?_, fun z => z.2⟩
  refine (smallEtaleRingedSite B S hS X.1 X.2).J.transitive
    ((memberFunctor B S hS Yi f hf).is_cover_of_isCoverDense
      (SmallEtale.topology B S hS X.1) W) _ ?_
  intro W' g hg
  obtain ⟨⟨p, a, -, -⟩⟩ := hg
  obtain ⟨I₁, W₁, g₁, hcov₁, hpres₁⟩ := (h p.1).locally_hasGlobalPresentation
    ((SmallEtale.postcompOverInverse B S hS (f p.1) (hf p.1) p.2).obj (Over.mk a)).left
  have hpush := (SmallEtale.coverPreserving_smallEtalePostcomp B S hS (f p.1)
    (hf p.1)).cover_preserve hcov₁
  have hle : Sieve.functorPushforward (ringedSitePostcomp B S hS (f p.1) (hf p.1))
      (Sieve.ofArrows W₁ g₁) ≤
      Sieve.ofObjects (fun z : {Z : (smallEtaleRingedSite B S hS X.1 X.2).C //
        (M.over Z).HasGlobalPresentation} => z.1)
        ((ringedSitePostcomp B S hS (f p.1) (hf p.1)).obj
          ((SmallEtale.postcompOverInverse B S hS (f p.1) (hf p.1) p.2).obj
            (Over.mk a)).left) := by
    rintro T r ⟨Z₀, r₀, q, hr₀, rfl⟩
    obtain ⟨i₁, b, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hr₀
    exact ⟨⟨_, (hasGlobalPresentation_over_postcomp_iff B S hS (f p.1) (hf p.1) M (W₁ i₁)).1
      (hpres₁ i₁)⟩, ⟨q ≫ (ringedSitePostcomp B S hS (f p.1) (hf p.1)).map b⟩⟩
  have hobj := (smallEtaleRingedSite B S hS X.1 X.2).J.superset_covering hle hpush
  have hα := (smallEtaleRingedSite B S hS X.1 X.2).J.pullback_stable
    ((Over.forget ((smallEtalePostcomp B S hS (f p.1) (hf p.1)).obj p.2)).mapIso
      ((SmallEtale.postcompOverCounitIso B S hS (f p.1) (hf p.1) p.2).app (Over.mk a))).inv hobj
  refine (smallEtaleRingedSite B S hS X.1 X.2).J.superset_covering ?_ hα
  intro T b hb
  exact hb

end CoverDense

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
