module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.BaseChangeIso
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeMorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.RelativeSpecCriterion
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.DirectImageInputs
public import StacksFrontier.AlgebraicGeometry.RelativeSpecOpenRestriction.RelativeSpecBaseChange

/-!
# Algebraizing a cartesian system of finite morphisms over the adic thickenings

**Stacks 09ZT.** Let `A` be a Noetherian ring complete with respect to an ideal `I`, write
`S = Spec A` and `Sₙ = Spec (A / Iⁿ)`, and let `f : X ⟶ S` be separated of finite type. Put
`Xₙ = X ×_S Sₙ`. Given a commutative ladder

```
  Y₁ ---> Y₂ ---> Y₃ ---> …
  |       |       |
  X₁ -i₁-> X₂ -i₂-> X₃ ---> …
```

with **cartesian** squares, in which every `Yₙ ⟶ Xₙ` is finite and `Y₁ ⟶ S₁` is proper, there is
a finite morphism `Y ⟶ X` with `Yₙ = Y ×_S Sₙ` for every `n`; moreover `Y` is proper over `S`.

The geometric vocabulary — `adicThickening`, `adicThickeningι`, `adicBaseChange`,
`adicBaseChangeSucc` — is that of `StacksFrontier.AlgebraicGeometry.Algebraization`, so `Xₙ` is the
honest fibre product `pullback f (adicThickeningι A I n)` and the transition `iₙ` is
`adicBaseChangeSucc`.

## The input of the proof

The source's proof is: push the structure sheaves forward to get coherent `𝒪_{Xₙ}`-algebras
`ℱₙ = f_{n,*}𝒪_{Yₙ}`, observe that the cartesian hypothesis makes the pullback of `ℱₙ₊₁` to `Xₙ`
equal to `ℱₙ`, algebraize the system to a single coherent `𝒪_X`-algebra `ℱ` with support proper
over `S` (Grothendieck's existence theorem, **Stacks 088F**, for the module, and full faithfulness
of completion, **Stacks 088E**, for the algebra structure), and take `Y = Spec_X(ℱ)`.

That algebraization step is the deep input. It is named here as the predicate
`AlgebraicGeometry.AdicFiniteAlgebraAlgebraization`, which speaks about sheaves of algebras
alone — it knows nothing of the schemes `Yₙ`, of finite morphisms or of cartesian squares — and it
is proved over a complete Noetherian base as
`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_holds`
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/AdicFiniteAlgebraizationTags.lean`).
Stacks 09ZT with that input discharged is
`AlgebraicGeometry.exists_finite_algebraization_of_adicFiniteSystem_holds`, in the same file,
which carries the tag.

Everything between that predicate and the geometric statement is proved here: the passage from
the cartesian system of finite morphisms to the system of pushforward algebras and back through
the relative spectrum, the finiteness of the algebraization, and the cartesian identification
`Yₙ = Y ×_S Sₙ`.

## Main definitions

* `AlgebraicGeometry.AdicFiniteAlgebraAlgebraization` — the predicate described above.

## Main results

* `AlgebraicGeometry.isFinite_pushforwardAlgebra` — the pushforward algebra of a finite morphism
  is a finite algebra sheaf.
* `AlgebraicGeometry.pushforwardAlgebraIsoOfOverIso` — functoriality of `f ↦ f_* 𝒪` on
  isomorphisms over the base.
* `AlgebraicGeometry.algebraPullback_pushforwardAlgebra_iso_of_isPullback` — a cartesian square
  identifies the pullback of the pushforward algebra with the pushforward algebra of the base
  change.
* `AlgebraicGeometry.exists_finite_algebraization_of_adicFiniteSystem` — **Stacks 09ZT** from
  the predicate `AdicFiniteAlgebraAlgebraization`.
* `AlgebraicGeometry.adicFiniteAlgebraization_of_adicFiniteAlgebraAlgebraization` — the same
  statement in the packaging `AdicFiniteAlgebraization` that Stacks 0A42 consumes.

## Implementation notes

Positive powers `Iⁿ` are indexed by `n : ℕ` through `I ^ (n + 1)`, as in
`StacksFrontier.AlgebraicGeometry.Algebraization`, so index `n` here is the source's `n + 1` and
unrestricted `n : ℕ` gives exactly the thickenings `I¹, I², …` of the source.

A sheaf of algebras is `Stacks.RelativeSpec.AlgebraSheaf X = Under X.sheaf`, its pullback is
`Stacks.AffineAlgebraEquivalence.algebraPullback`, and its relative spectrum is
`Stacks.AffineAlgebraEquivalence.relativeSpecToBase`; quasi-coherence is a typeclass argument of
the latter, so it is bound before the relative spectrum is named. Finiteness of an algebra sheaf
is `Stacks.RelativeSpec.AlgebraSheaf.IsFinite`, module-finiteness of the structural ring map on
every affine open, which is exactly what `IsFinite.finite_app` provides for a finite morphism.

The two properness clauses of Grothendieck existence — that the support of `ℱ₁` is proper over
`S₁`, and that the support of the algebraization is proper over `S` — are stated through the
relative spectrum rather than through the support of the underlying module. For an algebra sheaf
that is finite the relative spectrum is finite over the base with image the support, so the two
readings agree; this one keeps sheaves of modules out of the file.

## References

* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec (AlgebraSheaf)

universe u

namespace AlgebraicGeometry

/-! ### Pushforward algebras of finite morphisms -/

/-- The pushforward of the structure sheaf along a finite morphism is a finite sheaf of
algebras: finiteness of a morphism of schemes is module-finiteness of the structural ring map
over every affine open of the target, which is literally the condition defining
`Stacks.RelativeSpec.AlgebraSheaf.IsFinite`. -/
public theorem isFinite_pushforwardAlgebra {W T : Scheme.{u}} (p : W ⟶ T) [IsFinite p] :
    AlgebraSheaf.IsFinite (pushforwardAlgebra p) :=
  fun U hU => IsFinite.finite_app p U hU

/-- An isomorphism of schemes over `T` induces an isomorphism of pushed-forward structure
sheaves, in the opposite direction. -/
public def pushforwardAlgebraIsoOfOverIso {T : Scheme.{u}} {V W : Over T} (e : V ≅ W) :
    pushforwardAlgebra W.hom ≅ pushforwardAlgebra V.hom :=
  (pushforwardAlgebraFunctor T).mapIso e.op

/-- **A cartesian square identifies the pullback of a pushforward algebra with the pushforward
algebra of the base change.** For an affine morphism `p : W ⟶ T` and a cartesian square
exhibiting `V ⟶ T'` as the base change of `p` along `g : T' ⟶ T`, the base-change comparison of
Stacks 01SA is an isomorphism `g^*(p_* 𝒪_W) ≅ q_* 𝒪_V`. -/
public def algebraPullback_pushforwardAlgebra_iso_of_isPullback {T T' W V : Scheme.{u}}
    {p : W ⟶ T} {g : T' ⟶ T} {q : V ⟶ T'} {r : V ⟶ W} [IsAffineHom p]
    (h : IsPullback r q p g) :
    (algebraPullback g).obj (pushforwardAlgebra p) ≅ pushforwardAlgebra q :=
  haveI : IsAffineHom (Over.mk p).hom := inferInstanceAs (IsAffineHom p)
  (@asIso _ _ _ _ _ (Stacks.AlgebraPullbackQcoh.isIso_baseChangeAlgebraHom g (Over.mk p))) ≪≫
    pushforwardAlgebraIsoOfOverIso
      (Over.isoMk h.isoPullback h.isoPullback_hom_snd :
        (Over.mk q : Over T') ≅ (Over.pullback g).obj (Over.mk p))

/-- An isomorphism in `Over T` has an invertible underlying morphism of schemes. -/
private theorem isIso_left_of_overIso {T : Scheme.{u}} {V W : Over T} (e : V ≅ W) :
    IsIso e.hom.left :=
  inferInstanceAs (IsIso ((Over.forget T).map e.hom))

/-- Properness over a further base is insensitive to replacing a morphism by an isomorphic one
over its target. -/
public theorem isProper_comp_of_overIso {T W W' Z : Scheme.{u}} {p : W ⟶ T} {p' : W' ⟶ T}
    (e : (Over.mk p : Over T) ≅ Over.mk p') (q : T ⟶ Z) (h : IsProper (p ≫ q)) :
    IsProper (p' ≫ q) := by
  have hw : e.inv.left ≫ p = p' := Over.w e.inv
  have hiso : IsIso e.inv.left := isIso_left_of_overIso e.symm
  rw [← hw, Category.assoc]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper e.inv.left (p ≫ q)).mpr h

/-! ### The input Grothendieck existence provides -/

/-- **Grothendieck's existence theorem for finite sheaves of algebras** (Stacks 088F for the
underlying coherent module, Stacks 088E for the algebra structure), in the shape in which the
proof of Stacks 09ZT uses it.

Let `A` be a Noetherian ring complete for `I` and let `f : X ⟶ Spec A` be separated of finite
type. Suppose given, for every `n`, a quasi-coherent sheaf of algebras `B n` on the adic
thickening `Xₙ = X ×_{Spec A} Sₙ`, each finite, such that the pullback of `B (n + 1)` along the
transition `Xₙ ⟶ Xₙ₊₁` is `B n`, and such that the relative spectrum of `B 0` is proper over
`S₀`. Then there is a finite quasi-coherent sheaf of algebras `C` on `X` whose relative spectrum
is proper over `Spec A` and whose pullback to each `Xₙ` is `B n`.

This says nothing about schemes over the thickenings, about finite morphisms or about cartesian
squares: it is purely the algebraization of a system of sheaves of algebras, which is what
Grothendieck existence supplies. For `A` Noetherian and complete along `I` and `f` separated of
finite type it is proved as `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_holds`.

The two properness clauses are stated through the relative spectrum; for a finite algebra sheaf
that is the same as properness of the support of the underlying coherent module over the base,
which is how Stacks 088F states them. -/
public def AdicFiniteAlgebraAlgebraization (A : Type u) [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) : Prop :=
  ∀ (B : ∀ n : ℕ, AlgebraSheaf (adicBaseChange A I f n))
    (hqc : ∀ n, AlgebraSheaf.IsQuasicoherent (B n)),
    (∀ n, AlgebraSheaf.IsFinite (B n)) →
    (∀ n, Nonempty ((algebraPullback (adicBaseChangeSucc A I f n)).obj (B (n + 1)) ≅ B n)) →
    IsProper (@relativeSpecToBase _ (B 0) (hqc 0) ≫
      pullback.snd f (adicThickeningι A I 0)) →
    ∃ (C : AlgebraSheaf X) (hC : AlgebraSheaf.IsQuasicoherent C),
      AlgebraSheaf.IsFinite C ∧
        IsProper (@relativeSpecToBase _ C hC ≫ f) ∧
          ∀ n, Nonempty ((algebraPullback (pullback.fst f (adicThickeningι A I n))).obj C ≅ B n)

/-! ### Stacks 09ZT -/

/-- **Stacks Project, Tag 09ZT.** Let `A` be a Noetherian ring complete with respect to an ideal
`I`, write `S = Spec A` and `Sₙ = Spec (A / Iⁿ)`, and let `f : X ⟶ S` be separated of finite
type; put `Xₙ = X ×_S Sₙ`. Let `(Yₙ)` be a system of schemes over the `Xₙ` whose squares over the
transitions `Xₙ ⟶ Xₙ₊₁` are cartesian, with every `Yₙ ⟶ Xₙ` finite and `Y₀ ⟶ S₀` proper. Then
there is a finite morphism `a : Y ⟶ X` which is proper over `S` and maps `kₙ : Yₙ ⟶ Y` over `X`
exhibiting every `Yₙ` as the fibre product `Y ×_S Sₙ`.

The proof is the source's, read through the anti-equivalence between schemes affine over a base
and quasi-coherent sheaves of algebras (Stacks 01S8, 01SA): the pushforward algebras
`f_{n,*}𝒪_{Yₙ}` are finite, the cartesian squares identify the pullback of the `(n+1)`-st with the
`n`-th (Stacks 01LX part 2), so Grothendieck existence for finite sheaves of algebras, in the
form `halg`, algebraizes them to a finite quasi-coherent algebra `C` on `X` proper over `S`, and
`Y = Spec_X(C)` is finite over `X` with `Y ×_X Xₙ = Spec_{Xₙ}(C|_{Xₙ}) = Yₙ`; pasting that square
with `Xₙ = X ×_S Sₙ` gives `Yₙ = Y ×_S Sₙ`.

The Noetherian and completeness hypotheses on `A` are the ones under which `halg` is proved, by
`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_holds`; the statement with `halg` discharged
is `AlgebraicGeometry.exists_finite_algebraization_of_adicFiniteSystem_holds`, which carries the
tag. -/
public theorem exists_finite_algebraization_of_adicFiniteSystem
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (halg : AdicFiniteAlgebraAlgebraization A I f)
    (Y : ℕ → Scheme.{u}) (y : ∀ n, Y n ⟶ adicBaseChange A I f n)
    (t : ∀ n, Y n ⟶ Y (n + 1))
    (hcart : ∀ n, IsPullback (t n) (y n) (y (n + 1)) (adicBaseChangeSucc A I f n))
    (hfin : ∀ n, IsFinite (y n))
    (hproper : IsProper (y 0 ≫ pullback.snd f (adicThickeningι A I 0))) :
    ∃ (Z : Scheme.{u}) (a : Z ⟶ X), IsFinite a ∧ IsProper (a ≫ f) ∧
      ∃ k : ∀ n, Y n ⟶ Z,
        (∀ n, IsPullback (k n) (y n ≫ pullback.snd f (adicThickeningι A I n)) (a ≫ f)
          (adicThickeningι A I n)) ∧
        ∀ n, k n ≫ a = y n ≫ pullback.fst f (adicThickeningι A I n) := by
  have hfin' : ∀ n, IsFinite (y n) := hfin
  -- the system of pushforward algebras
  let B : ∀ n : ℕ, AlgebraSheaf (adicBaseChange A I f n) := fun n => pushforwardAlgebra (y n)
  have hqc : ∀ n, AlgebraSheaf.IsQuasicoherent (B n) := fun n =>
    have := hfin' n
    isQuasicoherent_pushforwardAlgebra (y n)
  have hBfin : ∀ n, AlgebraSheaf.IsFinite (B n) := fun n =>
    have := hfin' n
    isFinite_pushforwardAlgebra (y n)
  have hBtrans : ∀ n, Nonempty ((algebraPullback (adicBaseChangeSucc A I f n)).obj (B (n + 1)) ≅
      B n) := fun n =>
    have := hfin' (n + 1)
    ⟨algebraPullback_pushforwardAlgebra_iso_of_isPullback (hcart n)⟩
  -- properness of the closed member, transported to its relative spectrum
  have hB0 : IsProper (@relativeSpecToBase _ (B 0) (hqc 0) ≫
      pullback.snd f (adicThickeningι A I 0)) := by
    have := hfin' 0
    exact isProper_comp_of_overIso (relativeSpecPushforwardAlgebraIso (y 0))
      (pullback.snd f (adicThickeningι A I 0)) hproper
  obtain ⟨C, hC, hCfin, hCproper, hCiso⟩ := halg B hqc hBfin hBtrans hB0
  have := hC
  refine ⟨relativeSpec C, relativeSpecToBase C, isFinite_relativeSpecToBase C hCfin, hCproper, ?_⟩
  -- the comparison isomorphism over each thickening
  have hsq : ∀ n, ∃ k : Y n ⟶ relativeSpec C,
      IsPullback k (y n) (relativeSpecToBase C) (pullback.fst f (adicThickeningι A I n)) := by
    intro n
    have := hfin' n
    have := hqc n
    have : AlgebraSheaf.IsQuasicoherent
        ((algebraPullback (pullback.fst f (adicThickeningι A I n))).obj C) :=
      isQuasicoherent_algebraPullback_obj _ C
    let E : (Over.pullback (pullback.fst f (adicThickeningι A I n))).obj
        (Over.mk (relativeSpecToBase C)) ≅ (Over.mk (y n) : Over (adicBaseChange A I f n)) :=
      relativeSpecBaseChangeIso (pullback.fst f (adicThickeningι A I n)) C ≪≫
        relativeSpecOverIso (hCiso n).some ≪≫
        (relativeSpecPushforwardAlgebraIso (y n)).symm
    have hw : E.inv.left ≫ pullback.snd (relativeSpecToBase C)
        (pullback.fst f (adicThickeningι A I n)) = y n := Over.w E.inv
    have hiso : IsIso E.inv.left := isIso_left_of_overIso E.symm
    refine ⟨E.inv.left ≫ pullback.fst (relativeSpecToBase C)
      (pullback.fst f (adicThickeningι A I n)), ?_⟩
    refine IsPullback.of_iso_pullback ⟨?_⟩ (asIso E.inv.left) rfl hw
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
  choose k hk using hsq
  refine ⟨k, fun n => ?_, fun n => (hk n).w⟩
  exact (hk n).paste_vert (IsPullback.of_hasPullback f (adicThickeningι A I n))

/-- **Stacks 09ZT in the packaging that Stacks 0A42 consumes.** The hypothesis
`AlgebraicGeometry.AdicFiniteAlgebraization` of
`AlgebraicGeometry.existsUnique_algebraization_adicBaseChangeMap` is exactly the conclusion of
`exists_finite_algebraization_of_adicFiniteSystem` with the finiteness of the algebraized morphism
forgotten, so the latter discharges it.

Here `halg` is asked of every `fP : P ⟶ Spec A`. The form with `halg` asked of separated
morphisms of finite type is
`adicFiniteAlgebraization_of_adicFiniteAlgebraAlgebraization_of_qcSeparatedFiniteType`,
and `AlgebraicGeometry.adicFiniteAlgebraization_holds` is `AdicFiniteAlgebraization A I` with that
input discharged. -/
public theorem adicFiniteAlgebraization_of_adicFiniteAlgebraAlgebraization
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (halg : ∀ {P : Scheme.{u}} (fP : P ⟶ Spec (.of A)),
      AdicFiniteAlgebraAlgebraization A I fP) :
    AdicFiniteAlgebraization A I := by
  intro P fP hsep hft hqc Zn zToP tr htr hfinite hproper
  have := hsep
  have := hft
  have := hqc
  obtain ⟨Z, a, hafin, haproper, k, hcart, hka⟩ :=
    exists_finite_algebraization_of_adicFiniteSystem A I fP (halg fP) Zn zToP tr htr hfinite
      hproper
  exact ⟨Z, a, haproper, k, hcart, hka⟩

end AlgebraicGeometry

end
