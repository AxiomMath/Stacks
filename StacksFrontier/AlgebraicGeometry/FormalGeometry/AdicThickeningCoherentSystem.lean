module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GrothendieckExistence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalClosedSubschemeAlgebraization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper

/-!
# Systems of coherent modules on the adic thickenings

**Stacks 088F** ("Unwinding Grothendieck's existence theorem") restates Stacks 088E in concrete
geometric language. Let `A` be a Noetherian ring complete with respect to an ideal `I`, write
`S = Spec A` and `Sₙ = Spec (A / Iⁿ)`, let `f : X ⟶ S` be separated of finite type and put
`Xₙ = X ×_S Sₙ`, with transitions `iₙ : Xₙ ⟶ Xₙ₊₁`. The remark considers systems
`(ℱₙ, φₙ)` where

1. `ℱₙ` is a coherent `𝒪_{Xₙ}`-module,
2. `φₙ : iₙ^* ℱₙ₊₁ ⟶ ℱₙ` is an isomorphism, and
3. `Supp(ℱ₁)` is proper over `S₁`,

and asserts that the completion functor

  `{coherent 𝒪_X-modules with support proper over A} ⟶ {systems (ℱₙ) as above}`

is an equivalence of categories, the two support conditions being omissible when `X` is proper
over `A`.

This file introduces that category and that functor, and proves that clause (3) may be dropped
over a proper base. That the functor is an equivalence is
`AlgebraicGeometry.isEquivalence_adicThickeningCompletionFunctor`
(`FormalGeometry/CompletionProper/AdicThickeningEssSurj.lean`), and the proper case with the
support conditions omitted is
`AlgebraicGeometry.isEquivalence_adicThickeningTransitionCompletionFunctor`
(`FormalGeometry/CompletionProper/AdicThickeningProperEquivalence.lean`); both build on this file.

## Main definitions

* `AlgebraicGeometry.AdicCoherentModuleSystem` — the systems `(ℱₙ, φₙ)` of clauses (1), (2), (3),
  with `AdicCoherentModuleSystem.Hom` and the resulting category.
* `AlgebraicGeometry.adicThickeningCompletion` — the restriction `ℱ ↦ ℱ|_{Xₙ}` of a sheaf of
  modules to the `n`-th thickening, with `adicThickeningCompletionNatIso` and
  `adicThickeningCompletionTransition` its transition isomorphism.
* `AlgebraicGeometry.adicThickeningCompletionFunctor` — the completion functor of the remark.

## Main results

* `AlgebraicGeometry.isCoherent_adicThickeningCompletion` — clause (1) for a completion.
* `AlgebraicGeometry.hasProperSupport_adicThickeningCompletion_zero` — clause (3) for a
  completion: the restriction to `X₁` of a coherent module whose support is proper over `A` has
  support proper over `S₁`. This is Stacks 088D read in the thickening picture.
* `AlgebraicGeometry.hasProperSupport_of_isProper_adicBaseChange` — the support half of the
  remark's final clause: when `f` is proper, clause (3) holds for every coherent module on `Xₙ`,
  so it may be omitted.
  On the other side of the arrow the corresponding statement is
  `Stacks.Algebraization.hasProperSupport_of_isProper`, imported from the file carrying Stacks
  088E.
* `AlgebraicGeometry.AdicCoherentModuleSystem.ofIsProper` — the resulting constructor: for a
  proper `f`, coherence and the transition isomorphisms alone produce a system.

## Where the equivalence is proved

The equivalence is Stacks 088E,
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver_holds`, stated against
`Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f)`, read through the unwinding of
`FormalGeometry/AdicThickeningUnwinding.lean`, which identifies the `n`-th term of the
`I`-adic completion with the direct image of the restriction to `Xₙ`. The two are combined in
`FormalGeometry/CompletionProper/AdicThickeningEssSurj.lean`.

## Implementation notes

The adic vocabulary is that of `StacksFrontier.AlgebraicGeometry.Algebraization`: `Xₙ` is the honest
fibre product `adicBaseChange A I f n = pullback f (adicThickeningι A I n)`, the projection to
`X` is `pullback.fst f (adicThickeningι A I n)`, the structure morphism to `Sₙ` is
`pullback.snd f (adicThickeningι A I n)`, and the transition is `adicBaseChangeSucc A I f n`.
Positive powers are indexed through `n ↦ I ^ (n + 1)`, so the index `n` here is the source's
`n + 1`; in particular clause (3) is a condition at index `0`. This is the vocabulary of Stacks
09ZT and 0899 in this library, so the statements here are directly comparable with the
hypothesis `AlgebraicGeometry.AdicFiniteAlgebraAlgebraization` that Stacks 09ZT assumes.

Properness of the support is the library's `Stacks.Algebraization.HasProperSupport`, so clause
(3) reads exactly as the condition on the first term of a coherent adic system in Stacks 088D.

The source's standing hypotheses are carried only where they are used, which makes the
statements below more general than the remark, never less: completeness of `A` for `I` is never
assumed, Noetherianness of `A` only for the coherence of a restriction, and of `f` only
`LocallyOfFiniteType` — not separatedness or quasi-compactness. The equivalence
`AlgebraicGeometry.isEquivalence_adicThickeningCompletionFunctor` assumes all of them.

Coherence is spelled `_root_.SheafOfModules.IsCoherent.{u}`: the predicate is declared more than
once and a relative spelling can resolve to `Stacks.SheafOfModules.IsCoherent`, a different
constant. It is not an instance, so finite-typeness of a term is reached through the projection
`IsCoherent.isFiniteType`.

`Scheme.Modules` is a semireducible `def`, so the transition isomorphism is obtained as the
component of a natural isomorphism of functors assembled from Mathlib's
`Scheme.Modules.pullbackComp` and `Scheme.Modules.pullbackCongr`, and its naturality is that
natural isomorphism's; nothing here rewrites through the functor.

## References

* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 088D](https://stacks.math.columbia.edu/tag/088D)
* [Stacks Project, Tag 0CYP](https://stacks.math.columbia.edu/tag/0CYP)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

open Stacks.Algebraization (HasProperSupport hasProperSupport_of_isProper)

variable (A : Type u) [CommRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-! ### The projections of the adic thickenings -/

/-- The structure morphism `Xₙ ⟶ Sₙ` is proper whenever `f` is, being its base change. -/
public lemma isProper_pullback_snd_adicThickeningι [IsProper f] (n : ℕ) :
    IsProper (pullback.snd f (adicThickeningι A I n)) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback f (adicThickeningι A I n))
    inferInstance

/-! ### The systems of Stacks 088F -/

/-- **The systems `(ℱₙ, φₙ)` of Stacks 088F.** For `f : X ⟶ Spec A` locally of finite type, a
coherent `𝒪_{Xₙ}`-module for every `n`, together with an isomorphism `φₙ : iₙ^* ℱₙ₊₁ ≅ ℱₙ`
along the transition `iₙ : Xₙ ⟶ Xₙ₊₁`, whose first term has support proper over `S₁`.

The three fields other than `obj` are clauses (1), (2) and (3) of the remark. Clause (2) asks
for an isomorphism as *data*, as in the source, not merely for the existence of one: the
transition maps of the system are part of it. -/
@[stacks 088F "the systems (F n, phi n) of clauses (1), (2) and (3)"]
public structure AdicCoherentModuleSystem (A : Type u) [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] where
  /-- The sheaf of modules on the `n`-th adic thickening `Xₙ`. -/
  obj (n : ℕ) : (adicBaseChange A I f n).Modules
  /-- Clause (1): every term is coherent. -/
  isCoherent (n : ℕ) : _root_.SheafOfModules.IsCoherent.{u} (obj n)
  /-- Clause (2): the transition isomorphism `φₙ : iₙ^* ℱₙ₊₁ ≅ ℱₙ`. -/
  transitionIso (n : ℕ) :
    (Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).obj (obj (n + 1)) ≅ obj n
  /-- Clause (3): the support of the first term is proper over `S₁`. -/
  properSupport : HasProperSupport (pullback.snd f (adicThickeningι A I 0)) (obj 0)

namespace AdicCoherentModuleSystem

variable [LocallyOfFiniteType f]

/-- A morphism of systems: a map of sheaves of modules on every thickening, compatible with the
transition isomorphisms. -/
@[ext]
public structure Hom (F G : AdicCoherentModuleSystem A I f) where
  /-- The component on the `n`-th thickening. -/
  app (n : ℕ) : F.obj n ⟶ G.obj n
  /-- Compatibility with the transition isomorphisms. -/
  comm (n : ℕ) :
    (Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).map (app (n + 1)) ≫
        (G.transitionIso n).hom =
      (F.transitionIso n).hom ≫ app n

public instance : Category (AdicCoherentModuleSystem A I f) where
  Hom F G := Hom A I f F G
  id F :=
    { app := fun _ => 𝟙 _
      comm := fun n => by simp }
  comp {F G H} α β :=
    { app := fun n => α.app n ≫ β.app n
      comm := fun n => by
        rw [Functor.map_comp, Category.assoc, β.comm n, ← Category.assoc, α.comm n,
          Category.assoc] }
  id_comp _ := Hom.ext (funext fun _ => Category.id_comp _)
  comp_id _ := Hom.ext (funext fun _ => Category.comp_id _)
  assoc _ _ _ := Hom.ext (funext fun _ => Category.assoc _ _ _)

end AdicCoherentModuleSystem

/-! ### Completion along the adic thickenings -/

/-- **Restriction of a sheaf of modules to the `n`-th adic thickening.** This is `ℱ|_{Xₙ}`, the
pullback of `ℱ` along the projection `Xₙ ⟶ X`. -/
public def adicThickeningCompletion (G : X.Modules) (n : ℕ) : (adicBaseChange A I f n).Modules :=
  (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).obj G

/-- **The transition isomorphism of a completion, as a natural isomorphism of functors.** Since
`iₙ : Xₙ ⟶ Xₙ₊₁` is a morphism over `X`, pulling back along `Xₙ₊₁ ⟶ X` and then along `iₙ` is
pulling back along `Xₙ ⟶ X`. -/
public def adicThickeningCompletionNatIso (n : ℕ) :
    Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I (n + 1))) ⋙
        Scheme.Modules.pullback (adicBaseChangeSucc A I f n) ≅
      Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n)) :=
  Scheme.Modules.pullbackComp (adicBaseChangeSucc A I f n)
      (pullback.fst f (adicThickeningι A I (n + 1))) ≪≫
    Scheme.Modules.pullbackCongr (adicBaseChangeSucc_fst A I f n)

/-- **The transition isomorphism of a completion**, `iₙ^*(ℱ|_{Xₙ₊₁}) ≅ ℱ|_{Xₙ}`. -/
public def adicThickeningCompletionTransition (G : X.Modules) (n : ℕ) :
    (Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).obj
        (adicThickeningCompletion A I f G (n + 1)) ≅
      adicThickeningCompletion A I f G n :=
  (adicThickeningCompletionNatIso A I f n).app G

/-- **Clause (1) for a completion.** The restriction of a coherent module to a thickening is
coherent: the thickening is locally Noetherian, being of finite type over `A / Iⁿ`, so Stacks
0EBF applies. -/
public lemma isCoherent_adicThickeningCompletion [IsNoetherianRing A] [LocallyOfFiniteType f]
    (G : X.Modules) (hG : _root_.SheafOfModules.IsCoherent.{u} G) (n : ℕ) :
    _root_.SheafOfModules.IsCoherent.{u} (adicThickeningCompletion A I f G n) :=
  have := hG
  isCoherent_pullback (pullback.fst f (adicThickeningι A I n)) G

/-- **Clause (3) for a completion — Stacks 088D in the thickening picture.** If the support of a
finite type `𝒪_X`-module `ℱ` is proper over `A`, then the support of `ℱ|_{X₁}` is proper over
`S₁`.

The support of a pullback is the inverse image of the support (Stacks 056J), and a closed subset
proper over the base stays proper after base change (Stacks 0CYP), applied to the cartesian
square defining `X₁`. -/
public lemma hasProperSupport_adicThickeningCompletion_zero [LocallyOfFiniteType f]
    (G : X.Modules) [G.IsFiniteType] (hG : HasProperSupport f G) :
    HasProperSupport (pullback.snd f (adicThickeningι A I 0))
      (adicThickeningCompletion A I f G 0) := by
  obtain ⟨Z, hZeq, hZproper⟩ := hG
  refine ⟨Z.preimage (pullback.fst f (adicThickeningι A I 0)).continuous, ?_, ?_⟩
  · rw [adicThickeningCompletion,
      Stacks.Modules.supp_pullback (pullback.fst f (adicThickeningι A I 0)) G]
    change (pullback.fst f (adicThickeningι A I 0)) ⁻¹' (Z : Set X) = _
    rw [hZeq]
  · exact isProperOver_preimage_baseChange (pullback.fst f (adicThickeningι A I 0))
      (pullback.snd f (adicThickeningι A I 0)) f (adicThickeningι A I 0)
      (IsPullback.of_hasPullback f (adicThickeningι A I 0)) Z hZproper

/-- **The completion functor of Stacks 088F.** It sends a coherent `𝒪_X`-module with support
proper over `A` to the system `(ℱ|_{Xₙ})` of its restrictions to the adic thickenings, with the
transition isomorphisms induced by `iₙ ≫ (Xₙ₊₁ ⟶ X) = (Xₙ ⟶ X)`, and a map of modules to the
system of its restrictions.

This is the arrow displayed in the remark. That it is an **equivalence**, for `A` Noetherian
and `I`-adically complete and `f` separated of finite type, is
`AlgebraicGeometry.isEquivalence_adicThickeningCompletionFunctor`. -/
public def adicThickeningCompletionFunctor (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    Stacks.Algebraization.CoherentModulesProperOver f ⥤ AdicCoherentModuleSystem A I f where
  obj F :=
    { obj := adicThickeningCompletion A I f F.obj.obj
      isCoherent := isCoherent_adicThickeningCompletion A I f F.obj.obj F.obj.property
      transitionIso := adicThickeningCompletionTransition A I f F.obj.obj
      properSupport :=
        have : F.obj.obj.IsFiniteType := F.obj.property.isFiniteType
        hasProperSupport_adicThickeningCompletion_zero A I f F.obj.obj F.property }
  map φ :=
    { app := fun n =>
        (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map φ.hom.hom
      comm := fun n => (adicThickeningCompletionNatIso A I f n).hom.naturality φ.hom.hom }
  map_id _ :=
    AdicCoherentModuleSystem.Hom.ext (funext fun _ => CategoryTheory.Functor.map_id _ _)
  map_comp _ _ :=
    AdicCoherentModuleSystem.Hom.ext (funext fun _ => CategoryTheory.Functor.map_comp _ _ _)

/-! ### The proper case -/

/-- **Over a proper base the support condition (3) on the systems is automatic.**
If `f : X ⟶ Spec A` is proper then the structure morphism `Xₙ ⟶ Sₙ` is proper too, being its
base change, and so the support of any coherent `𝒪_{Xₙ}`-module is proper over `Sₙ`. Hence
clause (3) is automatic. This is the input for
`AlgebraicGeometry.isEquivalence_adicThickeningTransitionCompletionFunctor`, the proper case of
the remark with the support conditions omitted.

The companion statement on the other side of the arrow — that the support of any coherent
`𝒪_X`-module is then proper over `A` — is `Stacks.Algebraization.hasProperSupport_of_isProper`. -/
public lemma hasProperSupport_of_isProper_adicBaseChange [IsProper f] (n : ℕ)
    (F : (adicBaseChange A I f n).Modules) (hF : _root_.SheafOfModules.IsCoherent.{u} F) :
    HasProperSupport (pullback.snd f (adicThickeningι A I n)) F :=
  have : IsProper (pullback.snd f (adicThickeningι A I n)) :=
    isProper_pullback_snd_adicThickeningι A I f n
  have : F.IsFiniteType := hF.isFiniteType
  hasProperSupport_of_isProper (pullback.snd f (adicThickeningι A I n)) F

/-- **The systems of Stacks 088F over a proper base.** For a proper `f`, coherence and the
transition isomorphisms alone — clauses (1) and (2) — produce a system: clause (3) holds
automatically by `hasProperSupport_of_isProper_adicBaseChange`. -/
public def AdicCoherentModuleSystem.ofIsProper [IsProper f]
    (obj : ∀ n : ℕ, (adicBaseChange A I f n).Modules)
    (isCoherent : ∀ n : ℕ, _root_.SheafOfModules.IsCoherent.{u} (obj n))
    (transitionIso : ∀ n : ℕ,
      (Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).obj (obj (n + 1)) ≅ obj n) :
    AdicCoherentModuleSystem A I f where
  obj := obj
  isCoherent := isCoherent
  transitionIso := transitionIso
  properSupport := hasProperSupport_of_isProper_adicBaseChange A I f 0 (obj 0) (isCoherent 0)

end AlgebraicGeometry

end
