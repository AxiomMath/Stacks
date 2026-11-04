module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.RepresentablePresentation
public import StacksFrontier.CategoryTheory.Sites.CoequalizerOfEpi

/-!
# Producing a finite coequalizer presentation by quasi-compact quasi-separated representables

`AlgebraicGeometry.HasFiniteQCSRepresentableCoequalizerPresentation` asks for a sheaf of sets on
the small étale site to be a coequalizer of two maps between finite coproducts of sheaves
represented by quasi-compact quasi-separated étale objects. This file gives the two ways of
producing one which do not need any geometry.

The first is the categorical step of the proof of Stacks 09Y9: *two surjections suffice*. If
`∐ h_{U i} ⟶ F` is surjective and `∐ h_{V j}` surjects onto its kernel pair, then `F` is the
coequalizer of the two composites, by
`CategoryTheory.Sheaf.nonempty_coequalizer_iso_of_epi_of_epi`. What Stacks 09Y9 adds to this is
the geometry: that a constructible sheaf admits the first surjection at all, and that the kernel
pair is again constructible so that it admits the second. Neither is proved here.

The second is the degenerate case in which no relations are needed: a finite coproduct of such
representables is the coequalizer of the identity with itself. This is what exhibits the
predicate on a concrete sheaf, so that a statement taking it as a hypothesis — for instance
`AlgebraicGeometry.isFinitelyPresentable_of_hasFiniteQCSRepresentableCoequalizerPresentation`,
the sheaves-of-sets half of Stacks 09Z4 — is not vacuous.

## Main results

* `AlgebraicGeometry.hasFiniteQCSRepresentableCoequalizerPresentation_of_epi` — the reduction to
  two surjections.
* `AlgebraicGeometry.hasFiniteQCSRepresentableCoequalizerPresentation_of_iso_sigma` — a sheaf
  isomorphic to a finite coproduct of quasi-compact quasi-separated representables has a
  presentation.

## Implementation notes

No declaration here carries a Stacks tag. Tag 09Y9 is the equivalence of constructibility with
the existence of such a presentation; what is proved here is neither direction of it, only the
step by which the forward direction passes from surjections to a coequalizer.

The coproducts of `AlgebraicGeometry.HasFiniteQCSRepresentableCoequalizerPresentation` are taken
with respect to the instances the definition itself introduces with `letI`, because typeclass
inference does not find `CategoryTheory.Limits.HasColimit` for a finite discrete diagram of
sheaves within its heartbeat budget. The statements below therefore repeat those `letI`s
verbatim; `CategoryTheory.Limits.HasColimit` is a proposition, so which proof is used does not
affect the coproduct.

The kernel pair is passed as an arbitrary limiting `CategoryTheory.Limits.PullbackCone` rather
than as the chosen `CategoryTheory.Limits.pullback`, so that a consumer which builds the cone
from the geometry need not identify its vertex with the chosen pullback.

## References

* [Stacks Project, Tag 09Y9](https://stacks.math.columbia.edu/tag/09Y9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Two surjections give a finite coequalizer presentation.** If a finite coproduct of sheaves
represented by quasi-compact quasi-separated objects of the small étale site surjects onto `F`,
and a second such coproduct surjects onto the kernel pair of that surjection, then `F` has a
finite coequalizer presentation by quasi-compact quasi-separated representables.

This is the step with which the proof of Stacks 09Y9 reduces its forward direction to the
existence of surjections; the existence of the two surjections for a constructible sheaf is the
geometric content and is not proved here. -/
public theorem hasFiniteQCSRepresentableCoequalizerPresentation_of_epi
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (n m : ℕ) (U : Fin n → SmallEtale B X.1 X.property)
    (V : Fin m → SmallEtale B X.1 X.property)
    (hU : ∀ i, CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj (U i)) ∧
      QuasiSeparatedSpace ((SmallEtale.toScheme B X.1 X.property).obj (U i)))
    (hV : ∀ j, CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj (V j)) ∧
      QuasiSeparatedSpace ((SmallEtale.toScheme B X.1 X.property).obj (V j)))
    (hpq :
      letI : HasFiniteColimits (Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :=
        CategoryTheory.Sheaf.instHasFiniteColimits
      letI : HasColimitsOfShape (Discrete (Fin n))
          (Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :=
        HasFiniteColimits.out _
      letI : HasColimitsOfShape (Discrete (Fin m))
          (Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :=
        HasFiniteColimits.out _
      ∃ p : (∐ fun i ↦
          (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.1 X.property)).obj (U i)) ⟶ F,
        Epi p ∧ ∃ (c : PullbackCone p p) (_ : IsLimit c)
          (q : (∐ fun j ↦
              (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.1 X.property)).obj (V j)) ⟶ c.pt),
            Epi q) :
    HasFiniteQCSRepresentableCoequalizerPresentation B X F := by
  obtain ⟨p, hp, c, hc, q, hq⟩ := hpq
  exact ⟨n, m, U, V, hU, hV, q ≫ c.fst, q ≫ c.snd,
    Sheaf.nonempty_coequalizer_iso_of_epi_of_epi p c hc q⟩

/-- **A finite coproduct of quasi-compact quasi-separated representables has a finite coequalizer
presentation**, namely the one with no relations: it is the coequalizer of the identity of that
coproduct with itself.

This exhibits `AlgebraicGeometry.HasFiniteQCSRepresentableCoequalizerPresentation` on a concrete
sheaf of sets, so a statement taking it as a hypothesis is not vacuous. -/
public theorem hasFiniteQCSRepresentableCoequalizerPresentation_of_iso_sigma
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (n : ℕ) (U : Fin n → SmallEtale B X.1 X.property)
    (hU : ∀ i, CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj (U i)) ∧
      QuasiSeparatedSpace ((SmallEtale.toScheme B X.1 X.property).obj (U i)))
    (hF :
      letI : HasFiniteColimits (Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :=
        CategoryTheory.Sheaf.instHasFiniteColimits
      letI : HasColimitsOfShape (Discrete (Fin n))
          (Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :=
        HasFiniteColimits.out _
      Nonempty (F ≅ ∐ fun i ↦
        (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.1 X.property)).obj (U i))) :
    HasFiniteQCSRepresentableCoequalizerPresentation B X F := by
  obtain ⟨e⟩ := hF
  exact ⟨n, n, U, U, hU, hU, 𝟙 _, 𝟙 _,
    ⟨coequalizer.isoTargetOfSelf (𝟙 _) ≪≫ e.symm⟩⟩

end AlgebraicGeometry

end
