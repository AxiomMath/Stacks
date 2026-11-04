module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence

/-!
# The dévissage engine for properties of coherent modules

[Stacks, Tag 01YG] asserts that a property `P` of coherent modules on a Noetherian scheme `X`
holds for every coherent module as soon as

1. `P` holds for the zero module,
2. `P` is stable under extensions of coherent modules, and
3. `P` holds for `i_* I` whenever `i : Z ⟶ X` is a closed immersion with `Z` integral and
   `I ⊆ 𝒪_Z` is a quasi-coherent ideal.

That statement is **not** proved here. What is proved here is the whole inductive half of its
proof: conditions (1)–(3) propagate `P` along any finite filtration whose successive quotients
are of the shape in (3). The one remaining input is the *existence* of such a filtration, which
is [Stacks, Tag 01YF]; `property_of_forall_hasIdealDevissage` states 01YG with exactly that
existence statement added as a hypothesis, so what 01YG still owes is isolated in a single
named assumption. See the implementation notes for why that assumption is not discharged.

A point worth recording, because the source leaves it implicit: `P` is an arbitrary predicate
on modules, with **no** invariance under isomorphism assumed. Invariance is not needed as an
extra hypothesis — it is a consequence of (1) and (2), applied to the short exact sequence
`0 → F → G → 0` attached to an isomorphism `F ≅ G`, and that is `property_of_iso` below. Every
later step uses it, since filtrations only ever produce quotients isomorphic to, not equal to,
the modules the hypotheses speak about.

## Main definitions

* `Stacks.AlgebraicGeometry.CoherentDevissage.HasIdealDevissage`: the conclusion of
  [Stacks, Tag 01YF] for one module — a finite filtration by coherent submodules, starting at
  zero and ending at the module, whose successive quotients are direct images of quasi-coherent
  ideal sheaves on integral closed subschemes of `X`.

## Main results

* `Stacks.AlgebraicGeometry.CoherentDevissage.property_of_iso`: a property satisfying (1) and (2)
  is invariant under isomorphism of coherent modules.
* `Stacks.AlgebraicGeometry.CoherentDevissage.property_of_monoChain`: a property satisfying (1) and
  (2) and holding on the successive quotients of a filtration by coherent submodules holds on
  every term of the filtration.
* `Stacks.AlgebraicGeometry.CoherentDevissage.property_of_hasIdealDevissage`: (1)–(3) give `P F`
  for every coherent `F` carrying a filtration as in `HasIdealDevissage`.
* `Stacks.AlgebraicGeometry.CoherentDevissage.property_of_forall_hasIdealDevissage`:
  [Stacks, Tag 01YG], conditional on [Stacks, Tag 01YF].

## Implementation notes

**What is missing, precisely.** [Stacks, Tag 01YF] — every nonzero coherent module on a
Noetherian scheme has a filtration with quotients `i_{Z,*} I` — is not available in this
repository. Its proof needs, in turn: that the support of a coherent module is
closed; that a coherent module killed by the ideal of a closed subscheme is the direct image of
a coherent module on that subscheme ([Stacks, Tag 01PD]); the generic points of the irreducible
components of the support; and Noetherian induction on closed subsets of `X`. None of those
four are present. The Noetherian hypothesis of 01YG is used *only* through 01YF, which is why
`property_of_forall_hasIdealDevissage` does not assume `[IsNoetherian X]`: the statement proved
here is strictly more general than the tag's, and adding the instance would leave it unused.

**Shape of the filtration data.** A filtration is carried as a sequence `G : ℕ → X.Modules`
together with monomorphisms `f i : G i ⟶ G (i + 1)`, rather than as a chain of subobjects. The
short exact sequence that hypothesis (2) consumes is then built by hand as
`ShortComplex.mk (f i) (cokernel.π (f i)) (cokernel.condition (f i))`, whose three terms are
*syntactically* `G i`, `G (i + 1)` and `cokernel (f i)`, so `hext` applies with no transport.
Mathlib's ready-made `ShortComplex.cokernelSequence` is deliberately **not** used: it is an
unexposed `def`, so neither `Mono (cokernelSequence f).f` nor `Epi (cokernelSequence f).g` is
synthesizable here even with `[Mono f]` in context, and rewriting by the `@[simps]` equations
`cokernelSequence_f` / `cokernelSequence_g` leaves goals that `infer_instance` then fails on.
Building the complex from the constructor makes both instances projections of a constructor
application, which reduce. Exactness comes from `ShortComplex.exact_of_g_is_cokernel` applied
to `cokernelIsCokernel`. Making the filtration a chain of `Subobject`s instead would force an
explicit comparison at every step. The sequence is indexed by all of `ℕ` with a cut-off `n`,
rather than by `Fin (n + 1)`, so that the induction is the plain `Nat.rec` and no index
arithmetic appears.

**Coherence of the quotients is carried as data.** `HasIdealDevissage` asks for
`(cokernel (f i)).IsCoherent` explicitly. It would follow from coherence of `G i` and
`G (i + 1)` — a quotient of a coherent module by a coherent submodule is coherent — but that is
[Stacks, Tag 01BX] for the two-out-of-three property of coherence in a short exact sequence,
which this repository does not have either; and 01YF produces the quotients as direct images of
coherent modules, so it delivers their coherence along with the filtration. Asking for it is
therefore free at the point of use, and avoids importing a second missing theorem.

**Transparency gotchas.** `IsZero (⊤_ X.Modules)` is not found by instance search or by
`exact?`: the terminal object of an abelian category is a zero object, but only through
`terminalIsTerminal.uniqueUpToIso HasZeroObject.zeroIsTerminal`, and `isZero_terminal` below
records it once — nothing in this repository had written it down before.

## References

* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SheafOfModules

universe u

namespace Stacks.AlgebraicGeometry.CoherentDevissage

variable {X : Scheme.{u}}

/-- The terminal object of the category of modules on a scheme is a zero object. This is the
form in which hypothesis (1) of Stacks Tag 01YG names the zero module. -/
theorem isZero_terminal : IsZero (⊤_ X.Modules) :=
  (isZero_zero X.Modules).of_iso
    (terminalIsTerminal.uniqueUpToIso HasZeroObject.zeroIsTerminal)

/-- The terminal module is coherent. -/
theorem isCoherent_terminal : (⊤_ X.Modules).IsCoherent :=
  isCoherent_of_isZero isZero_terminal

variable (P : X.Modules → Prop)

/-- **A property holding on the zero module and stable under extensions of coherent modules is
invariant under isomorphism.** For an isomorphism `e : F ≅ G` the complex `F → G → 0` is short
exact, so stability under extensions carries `P F` and `P 0` to `P G`.

No isomorphism-invariance hypothesis is therefore needed in [Stacks, Tag 01YG], even though the
property there is an arbitrary predicate on modules. -/
theorem property_of_iso (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    {F G : X.Modules} (e : F ≅ G) (hF : F.IsCoherent) (hPF : P F) : P G :=
  have := hF
  hext (ShortComplex.mk e.hom (0 : G ⟶ ⊤_ X.Modules) (by simp))
    (ShortComplex.ShortExact.mk' ((ShortComplex.exact_iff_epi _ rfl).2 inferInstance)
      inferInstance (isZero_terminal.epi _))
    hF (isCoherent_of_iso e.symm) isCoherent_terminal hPF hzero

/-- **The dévissage induction.** Let `G : ℕ → X.Modules` be a filtration by coherent
submodules, given by monomorphisms `f i : G i ⟶ G (i + 1)` and starting at a zero module. If
`P` holds on the zero module, is stable under extensions of coherent modules, and holds on
every successive quotient `cokernel (f i)`, then it holds on every `G i`.

This is the step [Stacks, Tag 01YG] takes for granted once a filtration is in hand. -/
theorem property_of_monoChain (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    (G : ℕ → X.Modules) (f : ∀ i, G i ⟶ G (i + 1)) (hmono : ∀ i, Mono (f i))
    (hzeroG : IsZero (G 0)) (hcoh : ∀ i, (G i).IsCoherent)
    (hcoker : ∀ i, (cokernel (f i)).IsCoherent) (hP : ∀ i, P (cokernel (f i))) :
    ∀ i, P (G i) := by
  intro i
  induction i with
  | zero =>
    exact property_of_iso P hzero hext (isZero_terminal.iso hzeroG) isCoherent_terminal hzero
  | succ i ih =>
    exact hext (ShortComplex.mk (f i) (cokernel.π (f i)) (cokernel.condition (f i)))
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (f i))
        mono_f := hmono i
        epi_g := inferInstance }
      (hcoh i) (hcoh (i + 1)) (hcoker i) ih (hP i)

/-- **The conclusion of [Stacks, Tag 01YF] for a single module.** `HasIdealDevissage F` says
that `F` carries a finite filtration by coherent submodules, starting at a zero module and
ending at `F`, each of whose successive quotients is isomorphic to the direct image along a
closed immersion `Z ⟶ X`, with `Z` integral, of a quasi-coherent ideal of `𝒪_Z`.

This is exactly the data that [Stacks, Tag 01YG] feeds to its hypotheses, and the only thing
01YG still needs that this file does not supply. -/
def HasIdealDevissage (F : X.Modules) : Prop :=
  ∃ (n : ℕ) (G : ℕ → X.Modules) (f : ∀ i, G i ⟶ G (i + 1)),
    (∀ i, Mono (f i)) ∧ IsZero (G 0) ∧ (∀ i, (G i).IsCoherent) ∧
      (∀ i, (cokernel (f i)).IsCoherent) ∧ Nonempty (G n ≅ F) ∧
      ∀ i, ∃ (Z : Scheme.{u}) (ι : Z ⟶ X) (_ : IsClosedImmersion ι) (_ : IsIntegral Z)
        (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
        I.toSheafOfModules.IsQuasicoherent ∧
          Nonempty (cokernel (f i) ≅
            (Scheme.Modules.pushforward ι).obj I.toSheafOfModules)

/-- **[Stacks, Tag 01YG] for a module that has a dévissage filtration.** The three hypotheses
of 01YG give `P F` for every coherent `F` carrying a filtration as in `HasIdealDevissage`. -/
theorem property_of_hasIdealDevissage (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent →
      P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (F : X.Modules) (hF : HasIdealDevissage F) : P F := by
  obtain ⟨n, G, f, hmono, hzeroG, hcoh, hcoker, ⟨e⟩, hquot⟩ := hF
  have hP : ∀ i, P (cokernel (f i)) := by
    intro i
    obtain ⟨Z, ι, hι, hZ, I, hI, ⟨eq⟩⟩ := hquot i
    have := hcoker i
    exact property_of_iso P hzero hext eq.symm (isCoherent_of_iso eq.symm) (hideal ι I hI)
  exact property_of_iso P hzero hext e (hcoh n)
    (property_of_monoChain P hzero hext G f hmono hzeroG hcoh hcoker hP n)

/-- **THIS HYPOTHESIS IS NOT SATISFIABLE IN GENERAL, AND NO PROOF OF [Stacks, Tag 01YF]
SUPPLIES IT.** `hdev` is false outright whenever the underlying space of `X` is empty
(`not_hasIdealDevissage_of_isEmpty` of `DevissageFiltration`), because `HasIdealDevissage`
quantifies its last clause over all of `ℕ` where Tag 01YF bounds it and an integral closed
subscheme has a nonempty space; and in every other case it is strictly stronger than what Tag
01YF concludes. Use `property_of_forall_hasIdealFiltration` of `DevissageFiltration` instead.
This declaration is kept only as the strictly weaker form implied by it through
`hasIdealFiltration_of_hasIdealDevissage`.

**[Stacks, Tag 01YG], conditional on [Stacks, Tag 01YF].** A property of modules that holds
on the zero module, is stable under extensions of coherent modules, and holds on the direct
image of every quasi-coherent ideal on every integral closed subscheme, holds on every coherent
module — provided every coherent module has a dévissage filtration.

The hypothesis `hdev` is [Stacks, Tag 01YF] and is **not** proved anywhere in this repository;
it is the sole gap between this statement and Stacks Tag 01YG, whose `[IsNoetherian X]` is used by the
source only to obtain `hdev`. Accordingly no 01YG tag attribute is attached to anything here. -/
theorem property_of_forall_hasIdealDevissage
    (hdev : ∀ F : X.Modules, F.IsCoherent → HasIdealDevissage F)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent →
      P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)) :
    ∀ F : X.Modules, F.IsCoherent → P F :=
  fun F hF => property_of_hasIdealDevissage P hzero hext hideal F (hdev F hF)

end Stacks.AlgebraicGeometry.CoherentDevissage

end

end
