module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.AlgebraicGeometry.SigmaPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.FppfCovering
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coproducts in the big fppf site of a family with a uniform size bound

`AlgebraicGeometry.BigFppfOver.sigmaObj` forms the coproduct of a family of objects of the big
fppf site of `S` under the hypothesis `AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`
that the index lies below the *cofinality* of the size cutoff, which is what an arbitrary family
needs. As the docstring of that class records, a family carrying a *uniform* size bound needs
only that the index lie below the cutoff itself. This file supplies that second construction:
the coproduct of a family whose coproduct scheme is known to lie in the site, together with
the statement that its universe-lifted representable sheaf is the coproduct of the
representable sheaves of the summands.

The containment hypothesis is discharged for a family with a uniform size bound by
`AlgebraicGeometry.BigFppfSite.contains_sigma_of_size_le` (in
`StacksFrontier/AlgebraicGeometry/Spaces/SiteCoproductLargeValued.lean`).

## Main definitions

* `AlgebraicGeometry.BigFppfOver.sigmaObjOfContains`: the coproduct object.
* `AlgebraicGeometry.BigFppfOver.sigmaInclOfContains`: its inclusions.

## Main results

* `AlgebraicGeometry.BigFppfOver.isColimitUliftYonedaSigmaCofanOfContains`: the
  universe-lifted representable sheaf of the coproduct object is the coproduct of the
  representable sheaves of the summands.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {I : Type u} (U : I → BigFppfOver B S hS)
  (hU : B.Contains (∐ fun i ↦ (toScheme B S hS).obj (U i)))

/-- The coproduct of a family of objects of the big fppf site of `S` whose coproduct scheme
lies in the site, with underlying scheme that coproduct. -/
def sigmaObjOfContains : BigFppfOver B S hS :=
  Over.mk (B.inclusion.preimage (X := B.obj hU) (Y := B.obj hS)
    (Sigma.desc fun i ↦ B.inclusion.map (U i).hom))

/-- The `i`-th inclusion into `AlgebraicGeometry.BigFppfOver.sigmaObjOfContains`. -/
def sigmaInclOfContains (i : I) : U i ⟶ sigmaObjOfContains B S hS U hU :=
  Over.homMk (B.inclusion.preimage (X := (U i).left) (Y := B.obj hU)
    (Sigma.ι (fun i ↦ (toScheme B S hS).obj (U i)) i)) (by
    apply B.inclusion.map_injective
    change B.inclusion.map (B.inclusion.preimage (X := (U i).left) (Y := B.obj hU)
        (Sigma.ι (fun i ↦ (toScheme B S hS).obj (U i)) i) ≫
      B.inclusion.preimage (X := B.obj hU) (Y := B.obj hS)
        (Sigma.desc fun i ↦ B.inclusion.map (U i).hom)) = _
    rw [Functor.map_comp, B.inclusion.map_preimage, B.inclusion.map_preimage]
    exact Sigma.ι_comp_desc _ i)

/-- The underlying scheme morphism of an inclusion into
`AlgebraicGeometry.BigFppfOver.sigmaObjOfContains` is the coproduct inclusion. -/
theorem toScheme_map_sigmaInclOfContains (i : I) :
    (toScheme B S hS).map (sigmaInclOfContains B S hS U hU i) =
      Sigma.ι (fun i ↦ (toScheme B S hS).obj (U i)) i := by
  change B.inclusion.map (B.inclusion.preimage (X := (U i).left) (Y := B.obj hU)
    (Sigma.ι (fun i ↦ (toScheme B S hS).obj (U i)) i)) = _
  exact B.inclusion.map_preimage _

/-- **The atlas mechanism of Stacks 02WQ** for a family whose coproduct lies in the site: the
universe-lifted representable sheaf of `AlgebraicGeometry.BigFppfOver.sigmaObjOfContains` is
the coproduct, in sheaves of `Type (u + 1)`, of the representable sheaves of the summands.

The summands are open immersions with jointly surjective, pairwise disjoint images, so they
form a covering by monomorphisms with initial pairwise intersections, and
`CategoryTheory.GrothendieckTopology.isColimitCofanMkUliftYoneda` applies. -/
@[sga "4 II 4.6.2" "special case"]
def isColimitUliftYonedaSigmaCofanOfContains
    [(BigFppfOver.topology B S hS).Subcanonical] :
    IsColimit (Cofan.mk
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj (sigmaObjOfContains B S hS U hU))
      fun i ↦ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map
        (sigmaInclOfContains B S hS U hU i)) := by
  let c : Cofan U := Cofan.mk (sigmaObjOfContains B S hS U hU) (sigmaInclOfContains B S hS U hU)
  have (i : I) : Mono (c.inj i) := by
    refine (Over.forget (B.obj hS)).mono_of_mono_map (B.inclusion.mono_of_mono_map ?_)
    change Mono ((toScheme B S hS).map (sigmaInclOfContains B S hS U hU i))
    rw [toScheme_map_sigmaInclOfContains]
    exact inferInstanceAs (Mono (Sigma.ι (fun i ↦ (toScheme B S hS).obj (U i)) i))
  have hcov : Sieve.ofArrows U c.inj ∈ BigFppfOver.topology B S hS c.pt := by
    refine Space.generate_ofArrows_mem_topology_of_openCover B S hS U c.inj (fun i ↦ ?_)
      (fun x ↦ ?_)
    · change IsOpenImmersion ((toScheme B S hS).map (sigmaInclOfContains B S hS U hU i))
      rw [toScheme_map_sigmaInclOfContains]
      exact inferInstanceAs (IsOpenImmersion (Sigma.ι (fun i ↦ (toScheme B S hS).obj (U i)) i))
    · obtain ⟨i, y, hy⟩ := exists_sigmaι_eq (fun i ↦ (toScheme B S hS).obj (U i)) x
      refine ⟨i, y, ?_⟩
      change ((toScheme B S hS).map (sigmaInclOfContains B S hS U hU i)).base y = x
      rwa [toScheme_map_sigmaInclOfContains]
  exact (BigFppfOver.topology B S hS).isColimitCofanMkUliftYoneda.{u + 1} U (c := c) hcov
    (bot_mem_topology_of_isInitial B S hS)
    (by
      intro i j hij Y x y hxy
      have hxy' : (toScheme B S hS).map x ≫ Sigma.ι (fun i ↦ (toScheme B S hS).obj (U i)) i =
          (toScheme B S hS).map y ≫ Sigma.ι (fun i ↦ (toScheme B S hS).obj (U i)) j := by
        have h : (toScheme B S hS).map (x ≫ sigmaInclOfContains B S hS U hU i) =
            (toScheme B S hS).map (y ≫ sigmaInclOfContains B S hS U hU j) :=
          congrArg (toScheme B S hS).map hxy
        simp only [Functor.map_comp, toScheme_map_sigmaInclOfContains] at h
        exact h
      exact ⟨Over.isInitialOfIsInitialLeft (Y := Y)
        (isInitial_schemeBelow B
          (isInitial_iff_isEmpty.mpr (isEmpty_of_commSq_sigmaι_of_ne ⟨hxy'⟩ hij)).some)⟩)

end BigFppfOver

end AlgebraicGeometry

end
