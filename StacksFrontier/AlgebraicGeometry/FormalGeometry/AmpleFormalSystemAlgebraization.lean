module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemEmbeddedTuple
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemLifting
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemSections

/-!
# The algebraization of the tower in Grothendieck's algebraization theorem

The last line of the proof of Grothendieck's algebraization theorem ([Stacks, Tag 089A]) is "We
win by applying Lemma 30.28.1", that is [Stacks, Tag 0899]. This file performs that application:
given the tower `X₁ ⟶ X₂ ⟶ ⋯` over the thickenings with cartesian squares and the compatible
tower of generating tuples that the lifted sections produce, it produces the proper morphism
`X ⟶ Spec A` of the theorem's conclusion together with the identifications
`Xₙ ≅ X ×_S Sₙ` compatible with the transition maps `iₙ`.

That is the geometric half of the theorem's conclusion. The remaining half — the ample invertible
module `ℒ` on `X` with `ℒₙ ≅ ℒ|_{Xₙ}` compatibly with the `φₙ` — is a separate matter, obtained by
algebraizing the system `(ℒₙ, φₙ)` itself.

## Main results

* `Stacks.AmpleFormalSystemAlgebraization.exists_isProjectiveMorphism_of_tupleTower` — the
  morphism `X ⟶ Spec A` and the cartesian identifications `Xₙ ≅ X ×_S Sₙ`, from a compatible
  tower of generating tuples whose bottom member embeds `X₁` as a closed subscheme of `ℙᴺ_{S₁}`.

The morphism is delivered **H-projective**, not merely proper. [Stacks, Tag 0899] algebraizes the
tower to a *closed subscheme* `g : X ⟶ ℙᴺ_{Spec A}` of the ambient projective space, and that
closed immersion over `Spec A` is exactly the datum of `AlgebraicGeometry.IsProjectiveMorphism`;
properness is then `AlgebraicGeometry.isProper_of_isProjectiveMorphism`, so nothing is lost.
Keeping it is what lets the inputs of the sheaf half be stated for a projective morphism, which
is the hypothesis under which this library proves Grothendieck existence
(`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjective_of_vanishing`).

## Implementation notes

The input is read into [Stacks, Tag 0899] through
`Stacks.AmpleFormalSystemSections.isPullback_adicLift_tupleHom`, which supplies the cartesian
system over the adic base changes of the ambient `ℙᴺ_{Spec A}`, and through
`Stacks.AmpleFormalSystemSections.isClosedImmersion_adicLift`, which supplies the
closed-immersion clause at the bottom of the tower. The ambient morphism is proper by
`Stacks.AmpleFormalSystemAmbient.isProper_ambientHom`, which is more than the separated-of-finite
-type that [Stacks, Tag 0899] asks of it.

Two clauses of the output need no work at all. The conclusion's square is stated over
`jₙ ≫ pullback.snd`, and `Stacks.AmpleFormalSystemAmbient.adicLift_snd` says that composite is
`qₙ` on the nose; and the compatibility of the identifications with the transition maps `iₙ` is
the last clause of [Stacks, Tag 0899] verbatim.

[Stacks, Tag 0899] is carried in this library with Stacks 09ZT and the uniqueness clause of
Stacks 0A42 as the named hypotheses `halg` and `hrig`, so they appear here too; they are inputs
about the ambient projective space alone, and nothing about the given tower enters them.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 0899](https://stacks.math.columbia.edu/tag/0899)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.ProjectiveSpaceModuli
open Stacks.AmpleFormalSystemAmbient Stacks.AmpleFormalSystemSections

universe u

namespace Stacks.AmpleFormalSystemAlgebraization

/-- **The algebraization of the tower, [Stacks, Tag 0899] applied to `ℙᴺ_{Spec A}`.**

Let `A` be Noetherian and complete for `I`, let `Xₙ` be a tower of schemes over the thickenings
`Sₙ` with cartesian squares, and let `tₙ` be a compatible tower of generating tuples on the `Xₙ`
whose bottom member embeds `X₁` as a closed subscheme of `ℙᴺ_{S₁}`, with `X₁ ⟶ S₁` proper. Then
there is an H-projective — in particular proper — morphism `X ⟶ Spec A` and morphisms
`kₙ : Xₙ ⟶ X` compatible with the transition maps which exhibit each `Xₙ` as `X ×_{Spec A} Sₙ`.

This is the source's closing appeal to [Stacks, Tag 0899], with `ℙᴺ_{Spec A}` as the ambient
separated finite-type scheme. That tag algebraizes the tower to a closed subscheme
`g : X ⟶ ℙᴺ_{Spec A}`, so `X ⟶ Spec A` is a closed immersion over `Spec A` into projective
space: H-projectivity in the sense of [Stacks, Tag 01W8], clause (2). -/
public theorem exists_isProjectiveMorphism_of_tupleTower (A : Type u) [CommRing A]
    [IsNoetherianRing A]
    (I : Ideal A) (hcomplete : IsAdicComplete I A) (N : ℕ)
    (halg : AdicFiniteSystemAlgebraization A I (ambientHom A N))
    (hrig : AdicMorphismRigidity A I)
    {Xn : ℕ → Scheme.{u}} (q : ∀ n, Xn n ⟶ adicThickening A I n)
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hcart : ∀ n, IsPullback (i n) (q n) (q (n + 1)) (adicThickeningSucc A I n))
    (t : ∀ n, GeneratingTuple (Xn n) N)
    (ht : ∀ n, Isomorphic (pullbackTuple (i n) (t (n + 1))) (t n))
    (hclosed : IsClosedImmersion
      (Stacks.AmpleProjectiveImmersion.liftOver (n := N) (q 0) (tupleHom (t 0))))
    (hproper : IsProper (q 0)) :
    ∃ (X : Scheme.{u}) (fX : X ⟶ Spec (.of A)), IsProjectiveMorphism fX ∧
      ∃ k : ∀ n, Xn n ⟶ X, (∀ n, i n ≫ k (n + 1) = k n) ∧
        ∀ n, IsPullback (k n) (q n) fX (adicThickeningι A I n) := by
  have : IsProper (ambientHom A N) := isProper_ambientHom A N
  have hjproper : IsProper (adicLift (A := A) (I := I) (N := N) (q 0) (tupleHom (t 0)) ≫
      pullback.snd (ambientHom A N) (adicThickeningι A I 0)) := by
    rw [adicLift_snd]
    exact hproper
  obtain ⟨W, g, k, hgclosed, -, hkcart, -, hktrans⟩ :=
    exists_closedImmersion_algebraization_of_isPullback A I (ambientHom A N) hcomplete halg hrig
      Xn (fun n => adicLift (q n) (tupleHom (t n))) i
      (isPullback_adicLift_tupleHom (A := A) (I := I) (N := N) q i hcart t ht)
      (isClosedImmersion_adicLift 0 (q 0) (tupleHom (t 0)) hclosed) hjproper
  refine ⟨W, g ≫ ambientHom A N, ⟨N, g, hgclosed, rfl⟩, k, hktrans, fun n => ?_⟩
  have h := hkcart n
  rwa [adicLift_snd] at h

/-- **The transition maps of the tower are surjective on points.** They are base changes of the
transition maps of the thickenings, which are surjective because the kernel of
`A / Iⁿ⁺² ⟶ A / Iⁿ⁺¹` is nilpotent. -/
public lemma surjective_base_of_isPullback (A : Type u) [CommRing A] (I : Ideal A)
    {Xn : ℕ → Scheme.{u}} (q : ∀ n, Xn n ⟶ adicThickening A I n)
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hcart : ∀ n, IsPullback (i n) (q n) (q (n + 1)) (adicThickeningSucc A I n)) (n : ℕ) :
    Function.Surjective (i n).base := by
  have : Surjective (i n) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (hcart n).flip inferInstance
  exact (i n).surjective

/-- **Grothendieck's algebraization theorem, the geometric half of the conclusion, from the
lifted sections.**

Let `A` be Noetherian and complete for `I`, let `Xₙ` be a tower of schemes over the thickenings
`Sₙ` with cartesian squares and `X₁ ⟶ S₁` proper. Let `Mₙ` be invertible modules on the `Xₙ`
with isomorphisms `θₙ : iₙ^* M_{n+1} ≅ Mₙ` — in the application the `Mₙ` are the `ℒₙ ^⊗ d` and
the `θₙ` come from the `φₙ` — assume the induced transition maps on global sections are
surjective, and let `s₀` be `N + 1` global sections of `M₀` generating it and embedding `X₁` as
a closed subscheme of `ℙᴺ_{S₁}`. Then there is an H-projective — in particular proper —
morphism `X ⟶ Spec A` and morphisms `kₙ : Xₙ ⟶ X` compatible with the transition maps which
exhibit each `Xₙ` as `X ×_{Spec A} Sₙ`.

This composes the inductive lifting
(`Stacks.AmpleFormalSystemLifting.exists_generatingTupleTower`) with the appeal to
[Stacks, Tag 0899] (`exists_isProjectiveMorphism_of_tupleTower`). Surjectivity of the transition
maps of the tower on points is not a hypothesis: it is `surjective_base_of_isPullback`. -/
public theorem exists_isProjectiveMorphism_of_liftedSections (A : Type u) [CommRing A]
    [IsNoetherianRing A]
    (I : Ideal A) (hcomplete : IsAdicComplete I A) (N : ℕ)
    (halg : AdicFiniteSystemAlgebraization A I (ambientHom A N))
    (hrig : AdicMorphismRigidity A I)
    {Xn : ℕ → Scheme.{u}} (q : ∀ n, Xn n ⟶ adicThickening A I n)
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hcart : ∀ n, IsPullback (i n) (q n) (q (n + 1)) (adicThickeningSucc A I n))
    (M : ∀ n, (Xn n).Modules) (hM : ∀ n, Stacks.Ample.IsInvertibleModule (Xn n) (M n))
    (θ : ∀ n, (Scheme.Modules.pullback (i n)).obj (M (n + 1)) ≅ M n)
    (hres : ∀ n, Function.Surjective
      (Stacks.AmpleFormalSystemLifting.transitionSections i M θ n))
    (s₀ : Fin (N + 1) → Γ(M 0, ⊤)) (hs₀ : Stacks.ProjectiveFromSections.GeneratesStalks s₀)
    (hemb : IsClosedImmersion (Stacks.AmpleProjectiveImmersion.liftOver (n := N) (q 0)
      (tupleHom (⟨M 0, hM 0, s₀, hs₀⟩ : GeneratingTuple (Xn 0) N))))
    (hproper : IsProper (q 0)) :
    ∃ (X : Scheme.{u}) (fX : X ⟶ Spec (.of A)), IsProjectiveMorphism fX ∧
      ∃ k : ∀ n, Xn n ⟶ X, (∀ n, i n ≫ k (n + 1) = k n) ∧
        ∀ n, IsPullback (k n) (q n) fX (adicThickeningι A I n) := by
  obtain ⟨t, ht, ht0⟩ := Stacks.AmpleFormalSystemLifting.exists_generatingTupleTower i M θ
    (surjective_base_of_isPullback A I q i hcart) hM hres N s₀ hs₀
  refine exists_isProjectiveMorphism_of_tupleTower A I hcomplete N halg hrig q i hcart t ht ?_
    hproper
  rwa [tupleHom_congr ht0]

/-- **Grothendieck's algebraization theorem, the geometric half of the conclusion, under the
theorem's own hypotheses on the tower and the sheaves.**

Let `A` be Noetherian and complete for `I`, let `Xₙ` be a tower of schemes over the thickenings
`Sₙ` with cartesian squares, let `ℒₙ` be invertible modules on the `Xₙ`, and assume `X₁ ⟶ S₁` is
proper and `ℒ₁` is ample — hypotheses (1) and (2) of [Stacks, Tag 089A]. Assume moreover that for
arbitrarily large `d` the `d`-th tensor powers of the `ℒₙ` form a tower whose transition maps on
global sections are surjective. Then there is an H-projective — in particular proper — morphism
`X ⟶ Spec A` and morphisms `kₙ : Xₙ ⟶ X` compatible with the transition maps exhibiting each
`Xₙ` as `X ×_{Spec A} Sₙ`.

The degree is chosen by the embedding step
(`Stacks.AmpleFormalSystemEmbeddedTuple.exists_generatingTuple_isClosedImmersion_of_isAmple`),
which fixes a `d₀` and works in every degree beyond it; `htower` is asked for arbitrarily large
`d` for exactly that reason, which is also the form the source's own argument has — its `d` is
any degree above both the bound of the vanishing and the bound of the embedding. -/
public theorem exists_isProjectiveMorphism_of_isAmple (A : Type u) [CommRing A]
    [IsNoetherianRing A]
    (I : Ideal A) (hcomplete : IsAdicComplete I A)
    (halg : ∀ N : ℕ, AdicFiniteSystemAlgebraization A I (ambientHom A N))
    (hrig : AdicMorphismRigidity A I)
    {Xn : ℕ → Scheme.{u}} (q : ∀ n, Xn n ⟶ adicThickening A I n)
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hcart : ∀ n, IsPullback (i n) (q n) (q (n + 1)) (adicThickeningSucc A I n))
    (L : ∀ n, (Xn n).Modules) (hL : ∀ n, Stacks.Ample.IsInvertibleModule (Xn n) (L n))
    (hproper : IsProper (q 0))
    (hample : letI := hL 0; Stacks.Ample.IsAmple (Xn 0) (L 0))
    (htower : ∀ d₁ : ℕ, ∃ d : ℕ, d₁ ≤ d ∧
      ∃ θ : ∀ n, (Scheme.Modules.pullback (i n)).obj
            (letI := hL (n + 1); Stacks.Ample.tensorPowModule (Xn (n + 1)) (L (n + 1)) (d : ℤ)) ≅
          (letI := hL n; Stacks.Ample.tensorPowModule (Xn n) (L n) (d : ℤ)),
        ∀ n, Function.Surjective (Stacks.AmpleFormalSystemLifting.transitionSections i
          (fun m => letI := hL m; Stacks.Ample.tensorPowModule (Xn m) (L m) (d : ℤ)) θ n)) :
    ∃ (X : Scheme.{u}) (fX : X ⟶ Spec (.of A)), IsProjectiveMorphism fX ∧
      ∃ k : ∀ n, Xn n ⟶ X, (∀ n, i n ≫ k (n + 1) = k n) ∧
        ∀ n, IsPullback (k n) (q n) fX (adicThickeningι A I n) := by
  let := hL 0
  obtain ⟨d₀, -, hemb⟩ :=
    Stacks.AmpleFormalSystemEmbeddedTuple.exists_generatingTuple_isClosedImmersion_of_isAmple
      (q 0) (L 0) hample
  obtain ⟨d, hdd, θ, hres⟩ := htower d₀
  obtain ⟨N, s₀, hs₀, hclosed⟩ := hemb d hdd
  exact exists_isProjectiveMorphism_of_liftedSections A I hcomplete N (halg N) hrig q i hcart
    (fun m => let := hL m; Stacks.Ample.tensorPowModule (Xn m) (L m) (d : ℤ))
    (fun m => let := hL m; inferInstance) θ hres s₀ hs₀ hclosed hproper

end Stacks.AmpleFormalSystemAlgebraization

end
