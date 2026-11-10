module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ModuleAlgebraData
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicAlgebraTransport
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AsymmetricFormalFunctions
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafMultiplication
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.AffineBaseChange
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.ZeroDimensionalTensor

/-!
# The algebra structure on a module algebraization: the transport, and the repair of its binder

`AlgebraicGeometry.AdicAlgebraStructureTransport`
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/FiniteAlgebraAlgebraization.lean`) is step 5 of
the
reduction `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_moduleAlgebraization`, and through
it the last residual behind the `halg` hypotheses of Stacks 09ZT, 0A42 and 0899. It asks: given a
system `(B n)` of algebra sheaves on the adic thickenings `Xₙ` and a coherent `𝒪_X`-module `𝒩`
with support proper over the base whose restriction to every `Xₙ` is the module underlying
`B n`, put an algebra structure on `𝒩` realizing the system.

**That binder is false as stated, and this file proves why.** The defect is not the coherence or
the proper support of `𝒩` — those are indispensable, as the module docstring of
`FiniteAlgebraAlgebraization` records. The defect is that the hypothesis relates `𝒩` to each
`B n` *separately*, by an unrelated isomorphism of modules for each `n`, while its conclusion
forces the `B n` to be a **cartesian** system of algebra sheaves. Nothing in the hypotheses
supplies that, and it is not a consequence of them: algebra structures on one module are not
determined by the module.

## The refutation

`AlgebraicGeometry.nonempty_algebraTransition_of_algebraPullback_iso` is the engine: if a single
algebra sheaf `C` on `X` has `(algebraPullback vₙ).obj C ≅ B n` for every `n`, where
`vₙ : Xₙ ⟶ X` is the projection, then

  `(algebraPullback iₙ).obj (B (n + 1)) ≅ B n`

for every `n`, because `iₙ ≫ vₙ₊₁ = vₙ` (`AlgebraicGeometry.adicBaseChangeSucc_fst`) and
`algebraPullback` is pseudofunctorial
(`Stacks.AffineAlgebraEquivalence.algebraPullbackComp`). So the conclusion of the transport
*implies* the transition isomorphisms `hBtrans` of
`AlgebraicGeometry.AdicFiniteAlgebraAlgebraization`, which are not among its hypotheses;
`AlgebraicGeometry.not_adicAlgebraStructureTransport_of_not_algebraTransition` turns that into a
refutation from any single incompatible family.

A family witnessing the incompatibility, inside the hypotheses of the reduction: let `k` be a
field, `A = k⟦t⟧` — Noetherian and `t`-adically complete — `I = (t)`, `X = Spec A` and `f = 𝟙`,
which is proper, separated and of finite type, so `Xₙ = Spec (A / tⁿ⁺¹)`. Take `𝒩 = 𝒪_X ⊕ 𝒪_X`,
free of rank two, hence coherent with support `X`, which is proper over `A` because `f` is. Take

* `B n = (A / tⁿ⁺¹)[x] / (x²)` for `n ≥ 1`, and
* `B 0 = (A / t) × (A / t) = k × k`.

Every `B n` is a finite quasi-coherent algebra sheaf whose underlying module is free of rank two
over `𝒪_{Xₙ}`, so `𝒩|_{Xₙ} ≅ underlyingModule (B n)` for every `n` and the hypothesis of the
transport holds. But `(algebraPullback i₀).obj (B 1)` is
`(A / t²)[x] / (x²) ⊗_{A/t²} A/t = k[x] / (x²)`, which is not isomorphic to `k × k`: one is local
with a nonzero nilpotent, the other is reduced with two idempotents. By the engine above no `C`
can satisfy the conclusion, so the transport fails at this `A`, `I`, `f`. The antecedent
`(adicThickeningCompletionFunctor A I f).IsEquivalence` is Grothendieck existence for the
identity of a complete affine base, which is true — it is what Stacks 088E asserts — so the
implication is not vacuous. (The degenerate variant `A = k`, `I = ⊥`, where every `Xₙ` is
`Spec k` and `vₙ` is an isomorphism, refutes it in the same way with no `t` in sight.)

This is why the refutation is stated here as an implication rather than as a closed theorem: the
antecedent of `AdicAlgebraStructureTransport` is exactly the input this library does not carry,
so a Lean `¬ AdicAlgebraStructureTransport A I f` would have to prove Stacks 088E first. The
module docstring of `FiniteAlgebraAlgebraization` refutes an earlier form of the same binder in
the same style, in prose, for the same reason.

## The repair, and that it loses nothing

The fix is to hand the transport the data the source's argument actually runs on, and which the
one call site actually has: an isomorphism **of systems**, not a family of unrelated
isomorphisms. `AlgebraicGeometry.adicAlgebraModuleSystem` assembles the system of Stacks 088F out
of an algebra system — it is the `Sys` that
`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_moduleAlgebraization` builds inline, with
the same fields — and `AlgebraicGeometry.AdicAlgebraStructureSystemTransport` is the transport
stated against it.

No content is lost: `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_systemTransport` is the
reduction again, with the repaired binder in place of the false one, concluding
`AlgebraicGeometry.AdicFiniteAlgebraAlgebraization A I f` and hence — through
`AlgebraicGeometry.exists_finite_algebraization_of_adicFiniteSystem`,
`AlgebraicGeometry.adicFiniteAlgebraization_of_adicFiniteAlgebraAlgebraization` and
`AlgebraicGeometry.adicFiniteSystemAlgebraization_of_adicFiniteAlgebraAlgebraization` — the
`halg` hypotheses of Stacks 09ZT, 0A42 and 0899. The repaired binder is strictly weaker than the
false one and still suffices, which is the whole point.

## What a proof of the repaired binder now has, and what it still needs

The asymmetric comparison of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/AsymmetricFormalFunctions.lean`
removed the obstruction that used to block the unit: `Stacks.Algebraization.HasProperSupport f`
of `SheafOfModules.unit X.ringCatSheaf` is properness of `f`, so the symmetric full faithfulness
of `Stacks.Algebraization.bijective_completionFunctor_map_of_annihilatedByKer` could not move
`AlgebraicGeometry.ModuleAlgebraData.unit`, while
`Stacks.Algebraization.bijective_completionFunctor_map_unit_of_hasProperSupport` can. The
multiplication needs no asymmetry at all: both `𝒩 ⊗ 𝒩` and `𝒩` have proper support, so the
equivalence of `adicThickeningCompletionFunctor` moves `𝒩 ⊗ 𝒩 ⟶ 𝒩` once the tensor square of a
coherent module with proper support is known to be a coherent module with proper support, and the
monoidal comparison `Stacks.RingedSpace.comparisonBifunctorIso` (Stacks 01CD) identifies the
restriction of the tensor square with the tensor square of the restriction. The first half of
that is assembled here — `AlgebraicGeometry.tensorSquareProperOver` and
`AlgebraicGeometry.tensorCubeProperOver` put the tensor square and cube of `𝒩` in
`Stacks.Algebraization.CoherentModulesProperOver f`, which is where the multiplication, its
commutativity and its associativity have to live for the equivalence to see them.

The second half needed one strengthening of a hypothesis, and it is made here.
`AlgebraicGeometry.AlgebraPullbackModuleIso` is what the binder `hpullback` now carries: not a
bare isomorphism between the module underlying an algebra pullback and the module pullback, but
that isomorphism *together with* the two equations making it a morphism of algebra sheaves
underlying-module-wise. Without them the compatibility of the transported multiplications with
the transitions of `AlgebraicGeometry.adicAlgebraModuleSystem` is not derivable at all — an
unconstrained module isomorphism relates the multiplication of a pullback to nothing — and with
them it is a theorem,
`AlgebraicGeometry.AlgebraPullbackModuleIso.multiplication_comp_transition` in
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicAlgebraStructureSystemProof`.
The intended carrier of `hpullback` satisfies the two equations, being induced by a map of
sheaves of rings, so no conclusion is weakened; see the declaration docstring.

What is still missing, after that, is only a change of spelling and a change of picture: the
compatibility of the comparison of Stacks 01CD with the two isomorphisms
`AlgebraicGeometry.adicThickeningCompletionNatIso` is built from — whose ringed-space half is
`Stacks.PullbackCompMonoidal.comparison_tensor` — and, on the unit side, the comparison of
`Stacks.Algebraization.completionFunctor` with `adicThickeningCompletionFunctor` on morphism sets
out of `𝒪_X`, for which the object-level bridge is
`AlgebraicGeometry.adicThickeningCompletionPushforwardIso`.

## Main results

* `AlgebraicGeometry.nonempty_algebraTransition_of_algebraPullback_iso` — a single algebra sheaf
  on `X` whose pullbacks realize a family `(B n)` makes that family cartesian.
* `AlgebraicGeometry.not_adicAlgebraStructureTransport_of_not_algebraTransition` — hence any
  family satisfying the module hypothesis of `AdicAlgebraStructureTransport` but failing one
  transition refutes it.
* `AlgebraicGeometry.AlgebraPullbackModuleIso` — the strengthened `hpullback`: the identification
  of the module underlying an algebra pullback with the module pullback, required to intertwine
  the multiplications and the structure morphisms.
* `AlgebraicGeometry.adicAlgebraModuleSystem` — the system of Stacks 088F underlying a cartesian
  system of quasi-coherent algebra sheaves.
* `AlgebraicGeometry.AdicAlgebraStructureSystemTransport` — the repaired binder.
* `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_systemTransport` — the reduction run off
  the repaired binder, so the chain to Stacks 09ZT, 0A42 and 0899 is unaffected by the repair.
* `AlgebraicGeometry.hasProperSupport_tensorSheaf` — a tensor product of coherent modules has
  support proper over the base as soon as one factor does.
* `AlgebraicGeometry.tensorSquareProperOver`, `AlgebraicGeometry.tensorCubeProperOver` — hence the
  tensor square and cube of a coherent module with proper support are objects of
  `Stacks.Algebraization.CoherentModulesProperOver f`, the category the Stacks 088F equivalence
  moves morphisms in. This is what the descent of the multiplication runs on.
* `AlgebraicGeometry.bijective_adicThickeningCompletionFunctor_map_tensorSquare` and
  `AlgebraicGeometry.injective_adicThickeningCompletionFunctor_map_tensorCube` — the equivalence
  therefore does move a multiplication `𝒩 ⊗ 𝒩 ⟶ 𝒩` and does decide its laws on the thickenings.

## References

* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 0A42](https://stacks.math.columbia.edu/tag/0A42)
* [Stacks Project, Tag 0899](https://stacks.math.columbia.edu/tag/0899)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec (AlgebraSheaf)

universe u

namespace AlgebraicGeometry

open Stacks.Algebraization (HasProperSupport)

/-! ### The conclusion of the transport forces a cartesian system -/

/-- **A family of algebra sheaves realized by the pullbacks of one algebra sheaf on `X` is
cartesian.** If `C` is an algebra sheaf on `X` and `(algebraPullback vₙ).obj C ≅ B n` for every
`n`, where `vₙ : Xₙ ⟶ X` is the projection of the `n`-th adic thickening, then
`(algebraPullback iₙ).obj (B (n + 1)) ≅ B n` for every `n`.

The transition `iₙ : Xₙ ⟶ Xₙ₊₁` satisfies `iₙ ≫ vₙ₊₁ = vₙ`
(`AlgebraicGeometry.adicBaseChangeSucc_fst`), and the pullback of algebra sheaves is
pseudofunctorial (`Stacks.AffineAlgebraEquivalence.algebraPullbackComp`), so the pullback of
`B (n + 1)` along `iₙ` is the pullback of `C` along `vₙ`, which is `B n`.

This is what makes the conclusion of `AlgebraicGeometry.AdicAlgebraStructureTransport` stronger
than its hypotheses: the transition isomorphisms it yields are exactly the hypothesis `hBtrans`
of `AlgebraicGeometry.AdicFiniteAlgebraAlgebraization`, which the transport's own hypothesis list
omits. See the module docstring. -/
public theorem nonempty_algebraTransition_of_algebraPullback_iso
    (A : Type u) [CommRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (C : AlgebraSheaf X) (B : ∀ n : ℕ, AlgebraSheaf (adicBaseChange A I f n))
    (hC : ∀ n, Nonempty ((algebraPullback (pullback.fst f (adicThickeningι A I n))).obj C ≅ B n))
    (n : ℕ) :
    Nonempty ((algebraPullback (adicBaseChangeSucc A I f n)).obj (B (n + 1)) ≅ B n) :=
  ⟨(algebraPullback (adicBaseChangeSucc A I f n)).mapIso (hC (n + 1)).some.symm ≪≫
    ((algebraPullbackComp (adicBaseChangeSucc A I f n)
        (pullback.fst f (adicThickeningι A I (n + 1)))).app C).symm ≪≫
      eqToIso (congrArg (fun k => (algebraPullback k).obj C)
        (adicBaseChangeSucc_fst A I f n)) ≪≫ (hC n).some⟩

/-- **`AlgebraicGeometry.AdicAlgebraStructureTransport` is refuted by any incompatible family.**
If some family `(B n)` of algebra sheaves on the adic thickenings has underlying modules
isomorphic to the restrictions of one coherent `𝒩` with support proper over the base — which is
the whole hypothesis of the transport — but fails to be cartesian at a single index, then the
transport is false at this `A`, `I` and `f`.

Together with `AlgebraicGeometry.nonempty_algebraTransition_of_algebraPullback_iso` this is the
refutation: the module-level hypothesis cannot force the cartesian condition, because the
underlying module of an algebra sheaf does not determine its algebra structure. The module
docstring exhibits a family over `A = k⟦t⟧`, `I = (t)`, `f = 𝟙` with `B 1 = (A/t²)[x]/(x²)` and
`B 0 = k × k`, both free of rank two, for which `(algebraPullback i₀).obj (B 1) = k[x]/(x²)` is
not isomorphic to `B 0`.

The incompatibility is passed in rather than proved because the only inputs to it are the
nonexistence of a ring isomorphism between two concrete finite algebras; what cannot be
discharged here is the *antecedent* of the transport, the Stacks 088E equivalence, which is also
why the conclusion is stated as an implication. -/
public theorem not_adicAlgebraStructureTransport_of_not_algebraTransition
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    (B : ∀ n : ℕ, AlgebraSheaf (adicBaseChange A I f n)) (N : X.Modules)
    (hN : _root_.SheafOfModules.IsCoherent.{u} N) (hNproper : HasProperSupport f N)
    (hiso : ∀ n, Nonempty
      ((Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).obj N ≅
        AlgebraSheaf.underlyingModule (B n)))
    (m : ℕ)
    (hbad : ¬ Nonempty
      ((algebraPullback (adicBaseChangeSucc A I f m)).obj (B (m + 1)) ≅ B m)) :
    ¬ AdicAlgebraStructureTransport A I f := by
  intro htransport
  obtain ⟨C, -, hCpull⟩ := htransport h088F B N hN hNproper hiso
  exact hbad (nonempty_algebraTransition_of_algebraPullback_iso A I f C B hCpull m)

/-! ### The repaired binder -/

/-- **The identification of the module underlying an algebra pullback with the module pullback,
as a morphism of algebra sheaves underlying-module-wise.** For `g : T ⟶ S` and `E` an algebra
sheaf on `S`, this bundles an isomorphism
`underlyingModule ((algebraPullback g).obj E) ≅ g ^* (underlyingModule E)` with the two
statements that it carries the algebra structure of the pullback to the pulled-back algebra
structure: it intertwines the multiplications, and it intertwines the structure morphisms out of
the two structure sheaves. The multiplication on `g ^* (underlyingModule E)` is the pullback of
the multiplication of `E` read through [Stacks, Tag 01CD]
(`Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso`), and the unit is the pullback of the
unit read through `Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso`.

**Why the two equations are part of the datum, and not a weakening.** The intended carrier of
this identification is the missing input of
`Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_of_underlyingModuleIso`, and it
satisfies both: `(algebraPullback g).obj E` is `g⁻¹E ⊗_{g⁻¹𝒪_S} 𝒪_T`, so the isomorphism in
question is induced by a map of sheaves of *rings* and is multiplicative and unital by
construction. A bare module isomorphism is not: nothing relates the multiplication of a pullback
to the pullback of a multiplication, so with only the isomorphism in hand the compatibility of
the descended multiplication with the transitions of
`AlgebraicGeometry.adicAlgebraModuleSystem` is not derivable — see the module docstring of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicAlgebraStructureSystemProof`,
where that compatibility is now proved, from these two fields, by
`AlgebraicGeometry.AlgebraPullbackModuleIso.multiplication_comp_transition` and
`AlgebraicGeometry.AlgebraPullbackModuleIso.unitModuleMap_comp_transition`.

So the strengthening is of a *hypothesis*, in the direction the intended carrier already
satisfies; no conclusion anywhere below is changed. -/
public structure AlgebraPullbackModuleIso {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S)
    where
  /-- The isomorphism of `𝒪_T`-modules itself. -/
  iso : AlgebraSheaf.underlyingModule ((algebraPullback g).obj E) ≅
    (Scheme.Modules.pullback g).obj (AlgebraSheaf.underlyingModule E)
  /-- It intertwines the multiplication of the algebra pullback with the pullback of the
  multiplication of `E`, compared by [Stacks, Tag 01CD]. -/
  multiplication_comp_iso_hom :
    Stacks.RelativeSpec.AlgebraSheaf.multiplication ((algebraPullback g).obj E) ≫ iso.hom =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨T.presheaf, T.IsSheaf⟩)).map
            ((iso.hom, iso.hom) : (_, _) ⟶ (_, _)) ≫
        (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g
            (AlgebraSheaf.underlyingModule E) (AlgebraSheaf.underlyingModule E)).inv ≫
          (Scheme.Modules.pullback g).map
            (Stacks.RelativeSpec.AlgebraSheaf.multiplication E)
  /-- It intertwines the structure morphism of the algebra pullback with the pullback of the
  structure morphism of `E`. -/
  unitModuleMap_comp_iso_hom :
    Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap ((algebraPullback g).obj E) ≫ iso.hom =
      (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g).inv ≫
        (Scheme.Modules.pullback g).map (Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap E)

/-- **The system of Stacks 088F underlying a cartesian system of quasi-coherent algebra
sheaves.** Its terms are the modules `ℳₙ = underlyingModule (B n)`, coherent by hypothesis; its
transition isomorphisms are those of the algebra system, read on underlying modules through the
identification `hpullback` of the module underlying an algebra pullback with the module pullback;
and clause (3) is the properness of the support of `ℳ₀`.

This is the `Sys` that `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_moduleAlgebraization`
builds inline, with the same four fields, so naming it here changes nothing about that reduction;
what it buys is a statement of the transport whose hypothesis is an isomorphism **of systems**
rather than a family of unrelated isomorphisms of modules — which is what the false form of the
binder got wrong.

The second factor of the transition is written `(underlyingModuleFunctor _).mapIso`, not
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleIso`: the two are the same isomorphism, but the
sections of the latter carry an `eqToHom` along an equality of restriction-of-scalars objects and
multiplicativity cannot be read off it (the note at
`AlgebraicGeometry.GradedAlgebraCone` records the same obstruction), while the former has
`hom = underlyingModuleMap e.hom` by `rfl`, which is what
`Stacks.RelativeSpec.AlgebraSheaf.multiplication_comp_underlyingModuleMap` consumes. -/
public def adicAlgebraModuleSystem (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (hpullback : ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
      AlgebraSheaf.IsQuasicoherent E → AlgebraPullbackModuleIso g E)
    (B : ∀ n : ℕ, AlgebraSheaf (adicBaseChange A I f n))
    (hqc : ∀ n, AlgebraSheaf.IsQuasicoherent (B n))
    (hBtrans : ∀ n, Nonempty
      ((algebraPullback (adicBaseChangeSucc A I f n)).obj (B (n + 1)) ≅ B n))
    (hMcoh : ∀ n, _root_.SheafOfModules.IsCoherent.{u} (AlgebraSheaf.underlyingModule (B n)))
    (hM0 : HasProperSupport (pullback.snd f (adicThickeningι A I 0))
      (AlgebraSheaf.underlyingModule (B 0))) :
    AdicCoherentModuleSystem A I f where
  obj n := AlgebraSheaf.underlyingModule (B n)
  isCoherent := hMcoh
  transitionIso n :=
    (hpullback (adicBaseChangeSucc A I f n) (B (n + 1)) (hqc (n + 1))).iso.symm ≪≫
      (Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleFunctor
        (adicBaseChange A I f n)).mapIso (hBtrans n).some
  properSupport := hM0

/-- **The algebra structure on a module algebraization, with the hypothesis the source's argument
runs on.** This is `AlgebraicGeometry.AdicAlgebraStructureTransport` with its one defect
repaired: the coherent module with proper support is related to the system of algebra sheaves by
an isomorphism of *systems* — a morphism of `AlgebraicGeometry.AdicCoherentModuleSystem`, hence
compatible with the transitions — rather than by an unrelated isomorphism of modules at each
index.

The false form is refuted by
`AlgebraicGeometry.not_adicAlgebraStructureTransport_of_not_algebraTransition`; this form is what
the one call site has, and `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_systemTransport`
shows it still gives the `halg` hypotheses of Stacks 09ZT, 0A42 and 0899.

Coherence of `𝒩` and properness of its support are *not* weakened: they are the two components
of membership in `Stacks.Algebraization.CoherentModulesProperOver f`, which is the type of `P`.
They are what put `𝒩` and its tensor square in the domain on which the Stacks 088F equivalence is
full and faithful, and the counterexample of the module docstring of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/FiniteAlgebraAlgebraization.lean` shows the
statement is false without them. -/
public def AdicAlgebraStructureSystemTransport (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] : Prop :=
  (adicThickeningCompletionFunctor A I f).IsEquivalence →
  ∀ (hpullback : ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
      AlgebraSheaf.IsQuasicoherent E → AlgebraPullbackModuleIso g E)
    (B : ∀ n : ℕ, AlgebraSheaf (adicBaseChange A I f n))
    (hqc : ∀ n, AlgebraSheaf.IsQuasicoherent (B n))
    (hBtrans : ∀ n, Nonempty
      ((algebraPullback (adicBaseChangeSucc A I f n)).obj (B (n + 1)) ≅ B n))
    (hMcoh : ∀ n, _root_.SheafOfModules.IsCoherent.{u} (AlgebraSheaf.underlyingModule (B n)))
    (hM0 : HasProperSupport (pullback.snd f (adicThickeningι A I 0))
      (AlgebraSheaf.underlyingModule (B 0)))
    (P : Stacks.Algebraization.CoherentModulesProperOver f),
    ((adicThickeningCompletionFunctor A I f).obj P ≅
        adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh hM0) →
      ∃ C : AlgebraSheaf X, Nonempty (AlgebraSheaf.underlyingModule C ≅ P.obj.obj) ∧
        ∀ n, Nonempty ((algebraPullback (pullback.fst f (adicThickeningι A I n))).obj C ≅ B n)

/-! ### The reduction, run off the repaired binder -/

/-- **Grothendieck existence for coherent modules with proper support gives the algebra
hypothesis of Stacks 09ZT, from the repaired transport.** This is
`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_moduleAlgebraization` with
`AlgebraicGeometry.AdicAlgebraStructureSystemTransport` in place of the false
`AlgebraicGeometry.AdicAlgebraStructureTransport`; every other step of that reduction is
unchanged, and it still carries the same two binders `h088F` and `hpullback`. The second is now
the strengthened `AlgebraicGeometry.AlgebraPullbackModuleIso`, which asks of the identification
it provides what its intended carrier satisfies and what everything downstream of it needs; the
reduction uses it only through `AlgebraicGeometry.adicAlgebraModuleSystem`, exactly as before.

So the repair costs the chain nothing: the `halg` hypotheses of Stacks 09ZT, 0A42 and 0899 still
follow, through `AlgebraicGeometry.exists_finite_algebraization_of_adicFiniteSystem`,
`AlgebraicGeometry.adicFiniteAlgebraization_of_adicFiniteAlgebraAlgebraization` and
`AlgebraicGeometry.adicFiniteSystemAlgebraization_of_adicFiniteAlgebraAlgebraization`.

No tag attribute is attached, for the reason recorded at
`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_moduleAlgebraization`: the statement is
conditional on three named inputs. -/
public theorem adicFiniteAlgebraAlgebraization_of_systemTransport
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    (hpullback : ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
      AlgebraSheaf.IsQuasicoherent E → AlgebraPullbackModuleIso g E)
    (halgstr : AdicAlgebraStructureSystemTransport A I f) :
    AdicFiniteAlgebraAlgebraization A I f := by
  intro B hqc hBfin hBtrans hB0
  have hXnoeth : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  -- the underlying modules of the given algebra sheaves, and their coherence
  have hMcoh : ∀ n, _root_.SheafOfModules.IsCoherent.{u}
      (AlgebraSheaf.underlyingModule (B n)) := by
    intro n
    have : IsLocallyNoetherian (adicBaseChange A I f n) :=
      isLocallyNoetherian_of_isClosedImmersion (pullback.fst f (adicThickeningι A I n))
    exact Stacks.RelativeSpec.AlgebraSheaf.isCoherent_underlyingModule_of_isFinite (B n)
      (hqc n) (hBfin n)
  -- clause (3): the support of the closed member is proper over `S₀`, by the bridge
  have hM0 : HasProperSupport (pullback.snd f (adicThickeningι A I 0))
      (AlgebraSheaf.underlyingModule (B 0)) :=
    (algebraSheafProperSupportBridge (pullback.snd f (adicThickeningι A I 0)) (B 0)
      (hqc 0) (hBfin 0)).1 hB0
  -- the system of Stacks 088F, and its algebraization by Grothendieck existence for modules
  let Sys := adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh hM0
  have := h088F
  have : (adicThickeningCompletionFunctor A I f).EssSurj := inferInstance
  let P := (adicThickeningCompletionFunctor A I f).objPreimage Sys
  let e := (adicThickeningCompletionFunctor A I f).objObjPreimageIso Sys
  have hNproper : HasProperSupport f P.obj.obj := P.property
  -- the algebra structure on the algebraization, from the repaired transport
  obtain ⟨C, ⟨eC⟩, hCpull⟩ := halgstr h088F hpullback B hqc hBtrans hMcoh hM0 P e
  -- the underlying module of `C` is coherent, hence `C` is quasi-coherent and finite
  have hCcoh : _root_.SheafOfModules.IsCoherent.{u} (AlgebraSheaf.underlyingModule C) :=
    have := P.obj.property
    Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso (R := X.ringCatSheaf) eC
  have hCqc : AlgebraSheaf.IsQuasicoherent C :=
    (@Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent X
      (AlgebraSheaf.underlyingModule C) hCcoh).1
  have hCfin : AlgebraSheaf.IsFinite C :=
    Stacks.RelativeSpec.AlgebraSheaf.isFinite_of_isCoherent_underlyingModule C hCcoh
  refine ⟨C, hCqc, hCfin, ?_, hCpull⟩
  -- the relative spectrum of `C` is proper over `Spec A`, the converse of the bridge
  refine (algebraSheafProperSupportBridge f C hCqc hCfin).2 ?_
  obtain ⟨Z, hZ, hZproper⟩ := hNproper
  exact ⟨Z, hZ.trans (SheafOfModules.supp_eq_of_iso eC.symm), hZproper⟩

/-! ### The tensor square and cube of a coherent module with proper support -/

section Tensor

/-- **A tensor product has support proper over the base as soon as one factor does.** For
coherent `ℱ` and `𝒢` on `X` with `Supp ℱ` proper over `S`, the support of the tensor product
sheaf `ℱ ⊗ 𝒢` of [Stacks, Tag 01CA] is proper over `S`.

The support containment `Supp (ℱ ⊗ 𝒢) ⊆ Supp ℱ` is
`AlgebraicGeometry.notMem_supp_tensorSheaf_of_notMem_supp` — the stalk of a tensor product is the
tensor product of the stalks, so it vanishes where either factor's does — and a closed subset of
a closed subset proper over the base is proper over the base
(`AlgebraicGeometry.isProperOver_of_le`). Coherence of the tensor product, needed to know its
support is closed, is `AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent` (Stacks 01CE).

This is what puts the tensor square of `𝒩` in `Stacks.Algebraization.CoherentModulesProperOver f`
and so makes the Stacks 088F equivalence applicable to the multiplication `𝒩 ⊗ 𝒩 ⟶ 𝒩`; the
multiplication of an algebra sheaf is stated for exactly this spelling of the tensor product, in
`Stacks.RelativeSpec.AlgebraSheaf.multiplication`. -/
public theorem hasProperSupport_tensorSheaf {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F G : X.Modules)
    (hF : _root_.SheafOfModules.IsCoherent.{u} F) (hG : _root_.SheafOfModules.IsCoherent.{u} G)
    (hFp : HasProperSupport f F) :
    HasProperSupport f ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (F)).obj (G))) := by
  have := @SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace F G hF hG
  have : ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (F)).obj (G))).IsFiniteType :=
    _root_.SheafOfModules.IsCoherent.isFiniteType (M := (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (F)).obj (G)))
  obtain ⟨Z, hZ, hZproper⟩ := hFp
  refine ⟨⟨_root_.SheafOfModules.supp ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (F)).obj (G))),
    _root_.SheafOfModules.isClosed_supp ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (F)).obj (G)))⟩, rfl, ?_⟩
  refine isProperOver_of_le f ?_ hZproper
  change _root_.SheafOfModules.supp ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (F)).obj (G))) ≤ (Z : Set X)
  rw [hZ]
  intro x hx
  by_contra hxF
  exact notMem_supp_tensorSheaf_of_notMem_supp F G hxF hx

/-- **The tensor square of a coherent module with proper support, as an object of the category on
which the Stacks 088F equivalence lives.** The multiplication of an algebra sheaf is a morphism
out of the tensor square of its underlying module, so this is the object the descent of the
multiplication needs: the equivalence of `AlgebraicGeometry.adicThickeningCompletionFunctor` is an
equivalence of `Stacks.Algebraization.CoherentModulesProperOver f`, and it moves a morphism only
between objects of that category. -/
public def tensorSquareProperOver {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (N : X.Modules) (hN : _root_.SheafOfModules.IsCoherent.{u} N)
    (hNp : HasProperSupport f N) : Stacks.Algebraization.CoherentModulesProperOver f :=
  ⟨⟨(((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (N)).obj (N)),
      @SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace N N hN hN⟩,
    hasProperSupport_tensorSheaf f N N hN hN hNp⟩

/-- **The tensor cube of a coherent module with proper support**, `(𝒩 ⊗ 𝒩) ⊗ 𝒩`, as an object of
`Stacks.Algebraization.CoherentModulesProperOver f`. Associativity of the multiplication is an
equality of two morphisms out of this object, so faithfulness of the Stacks 088F equivalence
applies to it only once it is known to lie in that category. -/
public def tensorCubeProperOver {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (N : X.Modules) (hN : _root_.SheafOfModules.IsCoherent.{u} N)
    (hNp : HasProperSupport f N) : Stacks.Algebraization.CoherentModulesProperOver f :=
  ⟨⟨(((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (N)).obj (N)))).obj (N)),
      @SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ N
        (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace N N hN hN) hN⟩,
    hasProperSupport_tensorSheaf f _ N
      (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace N N hN hN) hN
      (hasProperSupport_tensorSheaf f N N hN hN hNp)⟩

/-! ### What the Stacks 088F equivalence now moves -/

/-- **The multiplication is moved by the Stacks 088F equivalence.** Granted the equivalence, a
morphism `𝒩 ⊗ 𝒩 ⟶ 𝒩` of coherent modules with proper support is the same thing as a morphism of
the systems of their restrictions to the adic thickenings: the map is bijective because an
equivalence is full and faithful.

This is the statement the descent of `Stacks.RelativeSpec.AlgebraSheaf.multiplication` consumes,
and it needs no asymmetry — unlike the unit, both of its objects have support proper over the
base, by `AlgebraicGeometry.tensorSquareProperOver`. What it does not supply is the morphism of
systems itself: building it from the multiplications of the `B n` is where the monoidal
comparison `Stacks.RingedSpace.comparisonBifunctorIso` of Stacks 01CD and the compatibility of
the thickening pullbacks with the transitions are needed. -/
public theorem bijective_adicThickeningCompletionFunctor_map_tensorSquare
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    (N : X.Modules) (hN : _root_.SheafOfModules.IsCoherent.{u} N)
    (hNp : HasProperSupport f N) :
    Function.Bijective
      ((adicThickeningCompletionFunctor A I f).map :
        (tensorSquareProperOver f N hN hNp ⟶
            (⟨⟨N, hN⟩, hNp⟩ : Stacks.Algebraization.CoherentModulesProperOver f)) →
          ((adicThickeningCompletionFunctor A I f).obj (tensorSquareProperOver f N hN hNp) ⟶
            (adicThickeningCompletionFunctor A I f).obj ⟨⟨N, hN⟩, hNp⟩)) :=
  have := h088F
  ⟨Functor.map_injective _, Functor.map_surjective _⟩

/-- **The associativity of a descended multiplication is decided on the thickenings.** Granted
the Stacks 088F equivalence, two morphisms `(𝒩 ⊗ 𝒩) ⊗ 𝒩 ⟶ 𝒩` that agree after restriction to
every adic thickening are equal, because an equivalence is faithful and the tensor cube of a
coherent module with proper support is an object of the category it is an equivalence of
(`AlgebraicGeometry.tensorCubeProperOver`).

This is how the associativity law of `AlgebraicGeometry.ModuleAlgebraData` is proved from the
associativity of the multiplications of the `B n`, and the commutativity law likewise from
`AlgebraicGeometry.tensorSquareProperOver`; it is the pattern of
`Stacks.FundamentalGroup.ModuleAlgebraData`'s own construction in
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/RestrictionEquivalenceOfCompletion.lean`, where
the separating family is the tower of projections rather than this equivalence. -/
public theorem injective_adicThickeningCompletionFunctor_map_tensorCube
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    (N : X.Modules) (hN : _root_.SheafOfModules.IsCoherent.{u} N)
    (hNp : HasProperSupport f N) :
    Function.Injective
      ((adicThickeningCompletionFunctor A I f).map :
        (tensorCubeProperOver f N hN hNp ⟶
            (⟨⟨N, hN⟩, hNp⟩ : Stacks.Algebraization.CoherentModulesProperOver f)) →
          ((adicThickeningCompletionFunctor A I f).obj (tensorCubeProperOver f N hN hNp) ⟶
            (adicThickeningCompletionFunctor A I f).obj ⟨⟨N, hN⟩, hNp⟩)) :=
  have := h088F
  Functor.map_injective _

end Tensor

end AlgebraicGeometry

end
