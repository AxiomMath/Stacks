module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedQuotientsPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanCriterionPresentation
public import StacksFrontier.Topology.Algebra.AdicTopology.QuotientDirectedLimit

/-!
# The closed-immersion criterion produces the presenting ring (Stacks 0AIC)

Let `X` be an affine formal algebraic space over a scheme `S` admitting a morphism
`f : X ⟶ Spec A` to an affine scheme through which every closed immersion of an affine
scheme into `X` becomes a closed immersion — condition (2) of **Stacks 0AIC**. This file
constructs the weakly admissible topological ring presenting `X`, which is condition (1).

The construction is the one the source gives. Fix a presentation `X = colim X_λ` by affine
thickenings. Each stage is a closed immersion into `X`, hence a closed subscheme of `Spec A`, so
`Γ(Spec A, 𝒪)` surjects onto every stage ring `Γ(X_λ, 𝒪)`, compatibly with the transition
morphisms. The presenting ring is then the inverse limit `A^ = lim Γ(X_λ, 𝒪)` with its limit
topology: the kernels of its projections are weak ideals of definition forming a fundamental
system of neighbourhoods of `0`, so `A^` is weakly admissible, and the recognition statement for
an arbitrary presentation identifies `X` with the formal spectrum of `A^`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isPresentingRing_of_hasAffineClosedImmersionCriterion`:
  **Stacks 0AIC**, condition (2) implies condition (1).
* `AlgebraicGeometry.FormalSpace.exists_isPresentingRing_of_hasSchemeClosedImmersionCriterion`:
  **Stacks 0AIC**, condition (3) implies condition (1).

## Implementation notes

*Why the limit is taken over ideals and not over the presentation.* The index of a presentation
lives in `Type (u + 1)`, one universe above the schemes, so the inverse limit of the section
rings taken over that index is not a ring of `Type u` and cannot be the presenting ring, whose
quotients have to be schemes of the site. What makes the limit small is precisely the hypothesis
of condition (2): the stage rings are quotients of the *one* ring `Γ(Spec A, 𝒪)`, so the limit
may be taken over the kernels of those quotient maps, which are ideals of a ring of `Type u`.
That reindexing is `TopologicalRing.exists_isWeaklyAdmissible_proj_of_surjective_family`, and it
is the only reason condition (2) rather than condition (4) is the entry point here — the two are
equivalent, but the equivalence runs through this construction.

*The ring of condition (2) is not the presenting ring.* The presenting ring is the limit of the
stage rings, a completion of `Γ(Spec A, 𝒪)`, not `A` itself; `A` need not even be separated for
the topology its stage ideals define, and `Spec A` need neither be an object of the site nor
carry a morphism to `S`.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AI9](https://stacks.math.columbia.edu/tag/0AI9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] sheaf_hasColimits

/-- **Stacks 0AIC, condition (2) implies condition (1).** If some morphism from an affine formal
algebraic space `X` to an affine scheme turns every closed immersion of an affine scheme
into `X` into a closed immersion, then `X` is presented by a weakly admissible topological ring:
the inverse limit of the section rings of any presentation of `X` by affine thickenings.

The stage rings are quotients of the sections of the given affine scheme, so that inverse limit
is a ring in the universe of the schemes; its projections to the stage rings are surjective, and
their kernels are weak ideals of definition forming a fundamental system of neighbourhoods of
`0`. -/
@[stacks 0AIC "(2) implies (1)"]
theorem exists_isPresentingRing_of_hasAffineClosedImmersionCriterion
    {X : FppfSheaf B S hS} (hX : HasAffineClosedImmersionCriterionMapToSpec B S hS X) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A), IsPresentingRing B S hS A X := by
  classical
  obtain ⟨⟨-, I, pre, hne, hdir, D, hD, ⟨e⟩⟩, A, fmap, hf⟩ := hX
  let Fs := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let Tf := BigAffineFppf.inclusion B S hS
  let G := D ⋙ Tf ⋙ Fs
  let q : ∀ i : I, (BigAffineFppf.toScheme B S hS).obj (D.obj i) ⟶ Spec A :=
    fun i ↦ fmap.app (Tf.obj (D.obj i)) (colimit.ι G i ≫ e.inv)
  have hqcomp : ∀ ⦃i j : I⦄ (φ : i ⟶ j),
      q i = (BigAffineFppf.toScheme B S hS).map (D.map φ) ≫ q j := by
    intro i j φ
    have hw : Fs.map (Tf.map (D.map φ)) ≫ colimit.ι G j = colimit.ι G i := colimit.w G φ
    have hnat := fmap.app_naturality (Tf.obj (D.obj j)) (Tf.obj (D.obj i)) (Tf.map (D.map φ))
      (colimit.ι G j ≫ e.inv)
    rwa [← Category.assoc, hw] at hnat
  let Rst : I → Type u := fun i ↦ Γ((BigAffineFppf.toScheme B S hS).obj (D.obj i), ⊤)
  let τ : ∀ ⦃i j : I⦄, i ≤ j → Rst j →+* Rst i := fun {_ _} h ↦
    (((BigAffineFppf.toScheme B S hS).map (D.map (homOfLE h))).appTop).hom
  let ρ : ∀ i : I, Γ(Spec A, ⊤) →+* Rst i := fun i ↦ ((q i).appTop).hom
  have hτnil : ∀ ⦃i j : I⦄ (h : i ≤ j), (RingHom.ker (τ h)).LocallyNilpotent := by
    intro i j h
    have : IsAffine ((BigAffineFppf.toScheme B S hS).obj (D.obj j)) := (D.obj j).property
    exact locallyNilpotent_ker_appTop_of_isThickening (hD (homOfLE h))
  have hρsurj : ∀ i, Function.Surjective (ρ i) := by
    intro i
    have : IsClosedImmersion (q i) :=
      hf (D.obj i) _ (isClosedImmersionInto_colimitι B S hS D hD X e.symm i)
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine (q i)).2
  have hρcompat : ∀ ⦃i j : I⦄ (h : i ≤ j) (x : Γ(Spec A, ⊤)), τ h (ρ j x) = ρ i x := by
    intro i j h x
    change (((BigAffineFppf.toScheme B S hS).map (D.map (homOfLE h))).appTop).hom
        (((q j).appTop).hom x) = ((q i).appTop).hom x
    rw [hqcomp (homOfLE h), Scheme.Hom.comp_appTop]
    exact (CommRingCat.comp_apply _ _ x).symm
  obtain ⟨A', hCR, hTS, hTR, hLT, π, hWA, hπsurj, hπcompat, hπker, hπbasis⟩ :=
    TopologicalRing.exists_isWeaklyAdmissible_proj_of_surjective_family hτnil hρsurj hρcompat
  let P : DirectedQuotients B S hS X A' I :=
    { diagram := D
      isThickening := hD
      colimitIso := e
      proj := π
      proj_surjective := hπsurj
      proj_comp := fun _ _ hle ↦ RingHom.ext (hπcompat hle)
      isWeakIdealOfDefinition_ker := hπker
      hasBasis_nhds_zero := hπbasis }
  obtain ⟨Q, ⟨eQ⟩⟩ := P.exists_quotientSystem_formalSpectrum_iso
  exact ⟨A', hCR, hTS, hTR, hLT, hWA, ⟨{ Q.weakIdealColimitPresentation with
    colimitIso := eQ ≪≫ Q.weakIdealColimitPresentation.colimitIso }⟩⟩

/-- **Stacks 0AIC, condition (3) implies condition (1).** The criterion for closed immersions of
arbitrary schemes restricts to affine schemes, and then condition (2) gives condition (1). -/
@[stacks 0AIC "(3) implies (1)"]
theorem exists_isPresentingRing_of_hasSchemeClosedImmersionCriterion
    {X : FppfSheaf B S hS} (hX : HasSchemeClosedImmersionCriterionMapToSpec B S hS X) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A), IsPresentingRing B S hS A X :=
  exists_isPresentingRing_of_hasAffineClosedImmersionCriterion B S hS
    (hX.hasAffineClosedImmersionCriterionMapToSpec B S hS)

end AlgebraicGeometry.FormalSpace

end
