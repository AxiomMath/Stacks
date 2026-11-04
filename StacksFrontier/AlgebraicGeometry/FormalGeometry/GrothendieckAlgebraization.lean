module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicTowerAmpleness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicTowerInvertibility
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicTowerRestrictionEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicTowerTwistVanishing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicFiniteAlgebraizationTags

/-!
# Grothendieck's algebraization theorem

Let `A` be a Noetherian ring complete with respect to an ideal `I`, and let `X₀ ⟶ X₁ ⟶ ⋯` be a
tower of schemes over the thickenings `Sₙ = Spec(A/Iⁿ⁺¹)` with cartesian squares, carrying
invertible modules `ℒₙ` and isomorphisms `φₙ : iₙ^* ℒₙ₊₁ ≅ ℒₙ`. If `X₀ ⟶ S₀` is proper and `ℒ₀` is
ample, the tower is the tower of thickenings of a proper `X ⟶ Spec A` carrying an ample invertible
`ℒ` that restricts to the `(ℒₙ, φₙ)` ([Stacks, Tag 089A]).

The indexing is shifted by one against the source: the `n`-th member here, over
`adicThickening A I n = Spec(A/Iⁿ⁺¹)`, is the source's `Xₙ₊₁`.

## The proof

* The obstruction groups `H¹(Xₙ₊₁, Ker(𝒪_{Xₙ₊₁} ⟶ 𝒪_{Xₙ}) ⊗ ℒₙ₊₁^⊗d)` vanish for `d ≫ 0`, uniformly
  in `n`: `Stacks.AdicTower.exists_isZero_h1_transitionIdeal` ([Stacks, Tag 0897] on the graded
  conormal algebra of the tower).
* Sections of `ℒ₀^⊗d` defining a closed immersion into `𝐏ᴺ` therefore lift along the tower, and
  [Stacks, Tag 0899] (through [Stacks, Tag 09ZT],
  `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_holds`) algebraizes the tower of closed
  subschemes of `𝐏ᴺ_{Sₙ}`:
  `Stacks.AmpleFormalSystemAlgebraization.exists_isProjectiveMorphism_of_isAmple`.
* Grothendieck existence along the tower ([Stacks, Tag 088F],
  `Stacks.AdicTowerRestriction.adicCanonicalTowerModuleAlgebraization`) algebraizes `(ℒₙ, φₙ)` to a
  coherent `ℒ`, which is invertible (`Stacks.AdicTowerInvert.adicTowerInvertibility`) and ample
  (`Stacks.AdicTowerAmple.adicTowerAmpleness`):
  `Stacks.AmpleFormalSystemLineBundle.exists_isAmple_of_restriction_isEquivalence`.

## Main results

* `Stacks.GrothendieckAlgebraization.exists_isProper_isAmple_algebraization`: Grothendieck's
  algebraization theorem.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.AmpleFormalSystemAmbient

universe u

namespace Stacks.GrothendieckAlgebraization

/-- **Grothendieck's algebraization theorem, [Stacks, Tag 089A].**

Let `A` be a Noetherian ring complete with respect to an ideal `I`, let `Xₙ` be a tower of
schemes over the thickenings `Sₙ = Spec (A / Iⁿ⁺¹)` with transitions `iₙ : Xₙ ⟶ Xₙ₊₁` whose squares
over `Sₙ ⟶ Sₙ₊₁` are cartesian, and let `ℒₙ` be invertible modules on the `Xₙ` with isomorphisms
`φₙ : iₙ^* ℒₙ₊₁ ≅ ℒₙ`. If `X₀ ⟶ S₀` is proper and `ℒ₀` is ample on `X₀`, then there are a proper
morphism `fX : X ⟶ Spec A`, an ample invertible `𝒪_X`-module `ℒ`, morphisms `kₙ : Xₙ ⟶ X` with
`iₙ ≫ kₙ₊₁ = kₙ` exhibiting every `Xₙ` as `X ×_{Spec A} Sₙ`, and isomorphisms `ℒₙ ≅ ℒ|_{Xₙ}`
compatible with the `φₙ`. -/
@[stacks 089A]
public theorem exists_isProper_isAmple_algebraization (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A] {Xn : ℕ → Scheme.{u}}
    (q : ∀ n, Xn n ⟶ adicThickening A I n) (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hcart : ∀ n, IsPullback (i n) (q n) (q (n + 1)) (adicThickeningSucc A I n))
    (L : ∀ n, (Xn n).Modules) (hL : ∀ n, IsInvertibleModule (Xn n) (L n))
    (φ : ∀ n, (Scheme.Modules.pullback (i n)).obj (L (n + 1)) ≅ L n)
    (hproper : IsProper (q 0))
    (hample : letI := hL 0; IsAmple (Xn 0) (L 0)) :
    ∃ (X : Scheme.{u}) (fX : X ⟶ Spec (.of A)), IsProper fX ∧
      ∃ (M : X.Modules) (hM : IsInvertibleModule X M), @IsAmple X M hM ∧
        ∃ (k : ∀ n, Xn n ⟶ X) (hk : ∀ n, i n ≫ k (n + 1) = k n),
          (∀ n, IsPullback (k n) (q n) fX (adicThickeningι A I n)) ∧
          ∃ e : ∀ n, L n ≅ (Scheme.Modules.pullback (k n)).obj M,
            ∀ n, (φ n).hom ≫ (e n).hom =
              (Scheme.Modules.pullback (i n)).map (e (n + 1)).hom ≫
                (Scheme.Modules.pullbackComp (i n) (k (n + 1))).hom.app M ≫
                  (Scheme.Modules.pullbackCongr (hk n)).hom.app M := by
  obtain ⟨X, fX, hfX, k, hk, hkcart⟩ :=
    Stacks.AmpleFormalSystemAlgebraization.exists_isProjectiveMorphism_of_isAmple A I ‹_›
      (fun N =>
        AmpleFormalSystemTheorem.adicFiniteSystemAlgebraization_of_adicFiniteAlgebraAlgebraization
          A I (ambientHom A N) (adicFiniteAlgebraAlgebraization_holds A I (ambientHom A N)))
      (Stacks.AmpleFormalSystemTheorem.adicMorphismRigidity_of_adicRigidity A I
        (Stacks.AdicClosedSubschemeRigidity.adicRigidity A I))
      q i hcart L hL hproper hample
      (fun d₁ => by
        have := hproper
        obtain ⟨d, hdd, hv⟩ :=
          Stacks.AdicTower.exists_isZero_h1_transitionIdeal q i hcart L hL φ hample d₁
        exact ⟨d, hdd, Stacks.AmpleFormalSystemTheorem.powTransitionIso i L hL φ d, fun n =>
          Stacks.AmpleFormalSystemTheorem.surjective_transitionSections_of_isZero_h1 A I q i L hL
            φ hcart d n (hv n)⟩)
  have := isProper_of_isProjectiveMorphism fX hfX
  obtain ⟨M, hM, hMample, e, hcomp⟩ :=
    Stacks.AmpleFormalSystemLineBundle.exists_isAmple_of_restriction_isEquivalence A I fX q i k hk
      hkcart L hL φ
      (Stacks.AmpleFormalSystemTheorem.adicTowerModuleAlgebraization_of_canonicalTower A I q i hcart
        (Stacks.AdicTowerRestriction.adicCanonicalTowerModuleAlgebraization A I) fX hfX k hk hkcart)
      (Stacks.AdicTowerInvert.adicTowerInvertibility A I q fX hfX k hkcart)
      (Stacks.AdicTowerAmple.adicTowerAmpleness A I q fX hfX k hkcart) hample
  exact ⟨X, fX, isProper_of_isProjectiveMorphism fX hfX, M, hM, hMample, k, hk, hkcart, e, hcomp⟩

end Stacks.GrothendieckAlgebraization

end
