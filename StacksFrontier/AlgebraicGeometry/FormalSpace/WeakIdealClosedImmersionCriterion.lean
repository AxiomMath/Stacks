module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanCriterion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation

/-!
# A formal spectrum is closed-immersed in the spectrum of its ring (Stacks 0AIC)

Let `A` be a weakly admissible topological ring and let the fppf sheaf `X` over `S` be the
colimit of the spectra of the quotients of `A` by its weak ideals of definition — condition (1)
of **Stacks 0AIC**. This file proves condition (2) for that `X`, with `A` itself as the witness:
`X` is an affine formal algebraic space, and for every closed immersion `T ⟶ X` with `T` an
affine scheme of the site the composition `T ⟶ X ⟶ Spec A` is a closed immersion of schemes.

The map `X ⟶ Spec A` is the one the colimit description gives: on the stage `Spec (A ⧸ K)` it is
the morphism of spectra induced by the quotient homomorphism `A → A ⧸ K`. So the composition
`T ⟶ X ⟶ Spec A` is read off from any factorisation of `T ⟶ X` through a stage, and the
statement below exhibits such a factorisation together with the closed immersion it produces.

The argument is the source's. A closed immersion of an affine scheme into `X` factors through a
stage by a closed immersion of schemes (**Stacks 0AIA**, in the form
`AlgebraicGeometry.FormalSpace.exists_stage_isClosedImmersion_of_isClosedImmersionInto`), the
stages of an arbitrary presentation of `X` are the quotient spectra of `A`
(`AlgebraicGeometry.FormalSpace.presentation_quotients_cofinal`), and `Spec (A ⧸ K) ⟶ Spec A` is
a closed immersion because `A → A ⧸ K` is surjective.

## Main results

* `AlgebraicGeometry.FormalSpace.isClosedImmersion_toSpec_of_weakIdealColimitPresentation`:
  **Stacks 0AIC**, condition (1) implies condition (2), with the morphism to `Spec A` read off
  from a factorisation through a stage.

## Implementation notes

No structure morphism `Spec A ⟶ S` appears anywhere here, and none appears in conditions (2)
and (3) of Stacks 0AIC: the clause proved below is a statement about morphisms of schemes and
about the factorisation of a morphism of sheaves, and a presenting ring carries no morphism to
`S` in general — the stages sit inside `Spec A` as closed subschemes and admit no retraction.
The statement applies verbatim to a ring that does happen to lie over `S`.

What the clause below does *not* produce is the library's
`AlgebraicGeometry.FormalSpace.HasAffineClosedImmersionCriterionMapToSpec`, which packages the same
content with the morphism `X ⟶ Spec A` given globally, as an
`AlgebraicGeometry.FormalSpace.MapToScheme`: a family defined at **every** object `T` of the
site, not only at those carrying a closed immersion into `X`. A point of `X` over an arbitrary
`T` is only *locally* given by a morphism to a stage — `X` is a sheafified colimit — so the
family has to be assembled from local factorisations, which needs the functor of points of a
scheme of arbitrary size to be an fppf sheaf on the site; the subcanonicity of the
site's own topology covers only objects of the site. The clause below is what the factorisation
argument of the source gives, and it is the input to that packaging, which is
`AlgebraicGeometry.FormalSpace.hasAffineClosedImmersionCriterion_of_weakIdealColimitPresentation`
in `StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealMapToSpec`; the sheaf it rests on is
`AlgebraicGeometry.Space.isSheaf_largeSchemePointsPresheaf`.

The factorisation is produced on an arbitrary presentation of `X` by affine thickenings, namely
the one `AlgebraicGeometry.FormalSpace.IsAffineFormalAlgebraicSpace` supplies, and then
transported to the canonical weak-ideal presentation by rigidity; this avoids lifting the
universe of the weak-ideal index by hand, since `presentation_quotients_cofinal` already
compares the two presentations over `X`.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

/-- **Stacks 0AIC, condition (1) implies condition (2).** Let `A` be a weakly admissible
topological ring and let the fppf sheaf `X`, satisfying the set-theoretic condition of
Stacks 0AIS, be the colimit of the spectra of the quotients of `A` by its weak ideals of
definition. Then `X` is an affine formal algebraic space, and every closed immersion of an
affine scheme `T` of the site into `X` factors through the spectrum of a quotient `A ⧸ K` in
such a way that the resulting morphism `T ⟶ Spec A` — which is the composition of `T ⟶ X` with
the canonical `X ⟶ Spec A` — is a closed immersion of schemes. -/
@[stacks 0AIC "(1) implies (2)"]
theorem isClosedImmersion_toSpec_of_weakIdealColimitPresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {X : FppfSheaf B S hS}
    (hset : SatisfiesSetTheoreticCondition B S hS X)
    (P : WeakIdealColimitPresentation B S hS A X) :
    IsAffineFormalAlgebraicSpace B S hS X ∧
      ∀ (T : BigAffineFppf B S hS)
        (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
            ((BigAffineFppf.inclusion B S hS).obj T) ⟶ X),
        IsClosedImmersionInto B S hS g →
        ∃ (K : WeakIdeals A) (c : T ⟶ P.diagram.obj K),
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
              ((BigAffineFppf.inclusion B S hS).map c) ≫
            colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
              Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) K ≫ P.colimitIso.inv = g ∧
          IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map c ≫
            (P.quotientIso K).hom ≫
              Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K.1))) := by
  classical
  have hXaff : IsAffineFormalAlgebraicSpace B S hS X :=
    isAffineFormalAlgebraicSpace_of_weakIdealColimitPresentation B S hS A hA hset P
  refine ⟨hXaff, ?_⟩
  intro T g hg
  obtain ⟨-, I, pre, hne, hdir, D, hD, ⟨eD⟩⟩ := id hXaff
  let : Preorder I := pre
  let : Nonempty I := hne
  let : IsDirected I (· ≤ ·) := hdir
  -- A closed immersion of an affine scheme into `X` factors through a stage of *some*
  -- presentation, by a closed immersion of schemes.
  obtain ⟨i, h, hci, hfac⟩ := exists_stage_isClosedImmersion_of_isClosedImmersionInto
    B S hS D hD eD g hg
  obtain ⟨h', hh'⟩ := Functor.Full.map_surjective (F := BigAffineFppf.inclusion B S hS) h
  -- That stage is the spectrum of a quotient of `A`, compatibly with the two colimits.
  obtain ⟨Jmap, eiso, -, hcanonical, -⟩ :=
    presentation_quotients_cofinal B S hS A hA X P I D hD eD
  refine ⟨Jmap i, h' ≫ (eiso i).hom, ?_, ?_⟩
  · rw [(BigAffineFppf.inclusion B S hS).map_comp,
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp, Category.assoc,
      hcanonical i, hh']
    exact hfac
  · have hci' : IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map h') := by
      have heq : (BigAffineFppf.toScheme B S hS).map h' =
          (BigFppfOver.toScheme B S hS).map h := by rw [← hh']; rfl
      rw [heq]
      exact hci
    have hmk : IsClosedImmersion
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Jmap i).1))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    rw [(BigAffineFppf.toScheme B S hS).map_comp]
    infer_instance

end AlgebraicGeometry.FormalSpace

end
