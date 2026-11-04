module

public import StacksFrontier.AlgebraicGeometry.Algebraization.GlobalSectionsComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ExtensionCohomologicalDimensionOne
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.RegularSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.MittagLefflerCriteria
public import StacksFrontier.Topology.Sheaves.Modules.PrincipalAdicLimitKernel
public import StacksFrontier.Topology.Algebra.AdicLimitTopology
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# Algebraization of an adic system over a principal ideal

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)` and the open complement `U = X \ V(𝔞)`. Let `(F_n)` be a coherent `I`-adic system
on `U` and assume `I = (f)` is principal. Stacks 0DXW proves that `(F_n)` extends canonically to
`X` when each `F_n` is a finite locally free `𝒪_U/f^n𝒪_U`-module, `f` is a nonzerodivisor and
`H¹_𝔞(A/fA)`, `H²_𝔞(A/fA)` are finite `A`-modules; the proof verifies the three hypotheses (a),
(b), (c) of the Mittag-Leffler criterion Stacks 0EHH.

This file carries out that verification. The source's two hypotheses enter it only through the
short exact sequences

  `0 → F_n → F_{n+1} → F_1 → 0`

— which the source derives from finite local freeness over `𝒪_U/f^n𝒪_U` and from `f` being a
nonzerodivisor — and through the finiteness of `H⁰(U, F_1)` and `H¹(U, F_1)`, which the source
derives from the finiteness of `H¹_𝔞(A/fA)` and `H²_𝔞(A/fA)` by Local Cohomology 0BK0 and 0BLT.
Both are hypotheses below; from them all three conditions of Stacks 0EHH are proved, and hence
canonical extension.

The short exact sequences are exactly condition (1) of Stacks 0H39 for multiplication by `f`,
which is the shape in which both cohomological inputs of the source are stated in this library:
Stacks 0EHA for (b) and Stacks 0BLC for (a).

## Main definitions

* `Stacks.Algebraization.systemObj`, `Stacks.Algebraization.systemMapSucc` — the terms of the
  adic system and its successive transition maps, as a zero-indexed tower of `𝒪_U`-modules.
* `Stacks.Algebraization.mulBySection` — multiplication by `f`, as an endomorphism of the
  identity functor of `𝒪_U`-modules.
* `Stacks.Algebraization.HasPrincipalShortExactSequences` — the short exact sequences
  `0 → F_n → F_{n+1} → F_1 → 0`, i.e. condition (1) of Stacks 0H39.
* `Stacks.Algebraization.openCohomologyFunctor` — `H^p(U, -)`, as a functor to `A`-modules.

## Main results

* `Stacks.Algebraization.eq_ofOpSequence` — every inverse system indexed by `ℕᵒᵖ` is the one
  built by `CategoryTheory.Functor.ofOpSequence` from its own successive transition maps.
* `Stacks.Algebraization.range_pow_eq_ker_limitProjection_globalSections` — the `f^(n+1)`-multiples
  in `M = limₙ H⁰(U, F_n)` are exactly the compatible sections dying in `F_n`.
* `Stacks.Algebraization.adicModuleTopology_limitGlobalSections` — **condition (b) of Stacks
  0EHH**: the limit topology on `M` is the `I`-adic topology.
* `Stacks.Algebraization.isMittagLeffler_globalSectionsSystem` — **condition (a) of Stacks
  0EHH**: the inverse system `H⁰(U, F_n)` has Mittag-Leffler.
* `Stacks.Algebraization.finite_globalSections_of_shortExactSequences` — **condition (c) of
  Stacks 0EHH**: every `H⁰(U, F_n)` is a finite `A`-module.
* `Stacks.Algebraization.canonicallyExtends_of_principal_shortExactSequences` — **Stacks 0DXW,
  first clause**: the system extends canonically to `X`.
* `Stacks.Algebraization.idealOnOpen_eq_ker_comap` — the ideal `I 𝒪_U` is the pullback of the
  kernel ideal sheaf of `Y ⟶ X`.
* `Stacks.Algebraization.isCompletionNearClosed_of_principal_shortExactSequences` — **Stacks
  0EKZ, the essential-surjectivity half**: over an `I`-adically complete `A` the system is the
  completion of a coherent module on an open neighbourhood of `U ∩ V(f)` in `U`.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and zero-indexed: term `n` is the source's `F_{n+1}`. Condition
(1) of Stacks 0H39 uses the same convention, so `HasPrincipalShortExactSequences` is literally
that condition for the tower `n ↦ F_{n+1}` and multiplication by the image of `f` in
`Γ(U, 𝒪_U)`.

Condition (b) is obtained from the degree-zero, terminal-sections half of Stacks 0EHA, namely
`Stacks.Modules.range_pow_eq_ker_limitProjection_terminalSections`, rather than from the
cohomological statement of that tag: in degree zero no derived functor is needed, and the
sections tower `H⁰(U, F_n)` is `Stacks.Algebraization.globalSectionsSystem` on the nose. That
lemma asks for the tower as an equality with a `CategoryTheory.Functor.ofOpSequence`, which is
what `eq_ofOpSequence` supplies; the two functors have the same objects by definitional
unfolding and the same maps by induction on the length of the composite.

Condition (a) is Stacks 0BLC in degree zero, so the zeroth right derived functor of sections has to
be identified with sections themselves; that is `CategoryTheory.Functor.rightDerivedZeroIsoSelf`,
available because evaluation of a sheaf of modules at an open preserves finite limits. The
Mittag-Leffler condition then travels along the natural isomorphism and along the exact restriction
of scalars from `Γ(U, 𝒪_U)`-modules to `A`-modules.

Two spellings of the ring of sections over `U` meet here.
`Stacks.Algebraization.globalSectionsSystem` restricts scalars along
`Stacks.Algebraization.scalarMap`, whose target is the `CommRingCat`
object `Γ(U, 𝒪_U)`, while Stacks 0BLC and Stacks 0EHA work over the `RingCat` object
`𝒪_U.obj(⊤)` of `S.U.toScheme.ringCatSheaf`. The two carriers are definitionally equal, but
their `Ring` instances are found by different paths, so instance search for the exactness of
restriction of scalars fails on the mixed spelling; `topSectionsRing` names the `RingCat`
spelling and the scalar map is ascribed to it where the criteria are applied.

`mulCommutativeRingCatSheaf` restates an existing instance at the spelling instance search
meets: the rings of sections of `S.U.toScheme.ringCatSheaf` are objects of `RingCat`, so their
commutativity is not found from the `CommRingCat` structure of `Γ(U, 𝒪_U)`. It is a `Prop`, so
nothing depends on which copy of it a term carries. `topSectionsAlgebra` likewise only repackages
`Stacks.Algebraization.scalarMap` as an algebra structure, which is the form Stacks 0BLC states
its coefficient action in.

What this file does **not** do is derive its two hypotheses from the source's. The short exact
sequences come in the source from finite local freeness of `F_n` over `𝒪_U/f^n𝒪_U` together with
the sequences `0 → A/f^nA → A/f^{n+1}A → A/fA → 0` for a nonzerodivisor `f`, a computation on the
stalks of `U` that is not carried out in this library: nothing in it concludes condition (1) of
Stacks 0H39 for a tower, and the criterion that would reduce that condition to the stalks is
`AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact`. The finiteness of
`H⁰(U, F_1)` and `H¹(U, F_1)` comes from Local Cohomology 0BK0 and 0BLT, both of which are
available — 0BLT is
`Stacks.LocalCohomologySequence.isCoherent_rightDerived_of_isFiniteLocallyFree` — but they reach
`F_1` through the closed subscheme `U ∩ V(f)`, and that reduction, whose cohomological half is
`Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward`, is not carried out here. The
tag on the main result says so. The source's second clause — that over an `I`-adically complete
`A` the system is the completion of a coherent `𝒪_U`-module — is reached from the first along the
chain of Stacks 0EIL, and is
`Stacks.Algebraization.isCompletionNearClosed_of_principal_shortExactSequences`.

The source's conditions (2) and (3) are stated in the library's own vocabulary, and the steps of
the two derivations above that the library does support are carried out, in the sibling module
`PrincipalNonzerodivisorHypotheses`. In particular the 0BK0 half of the finiteness argument —
condition (3) makes `H⁰(U, 𝒪_U/f𝒪_U)` and `H¹(U, 𝒪_U/f𝒪_U)` finite `A`-modules — is
`Stacks.Algebraization.finite_complementCohomologyBaseQuotient_of_finite_localCohomology`, and
`Stacks.Algebraization.free_stalk_quotient_of_isFiniteLocallyFreeAdic` is the local content of
condition (2). That module's docstring lists what the two derivations still owe.

## Stacks 0EKZ

Stacks 0EKZ asserts, under hypotheses (1)–(3) of Stacks 0DXW together with `f`-adic completeness
of `A`, that the completion functor `colim_{U₀ ⊆ U' ⊆ U} Coh(𝒪_{U'}) ⟶ Coh(U, f𝒪_U)` is an
equivalence on the full subcategories of finite locally free objects, where `U₀ = U ∩ V(f)`. Its
proof is the conjunction of two cited lemmas: full faithfulness is Stacks 0EKV and essential
surjectivity is Stacks 0DXW. Only the second half is proved here, as
`Stacks.Algebraization.isCompletionNearClosed_of_principal_shortExactSequences`.

Essential surjectivity is stated as `Stacks.Algebraization.IsCompletionNearClosed`, condition (3)
of Stacks 0EIL: the system is the completion of a coherent module on some open neighbourhood of
`U ∩ V(I)` inside `U`. For `I = (f)` that neighbourhood condition reads `U₀ ⊆ U'`, so the
predicate says exactly that the system lies in the image of the colimit functor of Stacks 0EKZ.
Over an `I`-adically complete `A` it follows from canonical extension along the chain of Stacks
0EIL: condition (6) implies (5) by
`Stacks.Algebraization.isRestrictionOfCompletion_of_extendsToX`, and conditions (5), (4), (2) and
(3) agree. The step from canonical extension (Tag 0EIP) to extendability (Tag 0EIM) is part (2) of
Stacks 0EIR, which is `Stacks.Algebraization.extendsToX_of_canonicallyExtends` applied to the
comparison `Stacks.Algebraization.tildeGlobalSectionsPullbackIso`: the latter supplies the
canonical maps `H⁰(U, F_n)^~|_U ⟶ F_n` from the quasi-affineness of `U`, and the former gets the
uniqueness of the extension from the rigidity of pro-isomorphisms of coherent adic systems.

That theorem concludes extendability for `Stacks.Algebraization.toKerSystem`, the transport of
the system along `Stacks.Algebraization.idealOnOpen_eq_ker_comap`, while
`Stacks.Algebraization.IsCompletionNearClosed` is stated here for
`Stacks.Algebraization.kerComapSystem`. The two presentations have the same underlying diagram,
and `Stacks.Algebraization.ExtendsToX` mentions the system only through that diagram, so
`extendsToX_ofDiagram` below passes between them with the diagram as a variable: comparing the
two systems as objects instead would ask the kernel to identify the two ideal sheaves
definitionally, which unfolds `AlgebraicGeometry.Scheme.ΓSpecIso`.

The full-faithfulness half is
`Stacks.Algebraization.completionFullyFaithfulComplete_principal`, which is Stacks 0EKV. Both
halves, at the source's own hypotheses, are assembled in
`Stacks.Algebraization.completionEquivalence_principal_finiteLocallyFree`; the module the
theorem below produces is coherent and is not asserted to be finite locally free, which the
assembled statement supplies by shrinking the neighbourhood to the locus where it is free.

## References

* [Stacks Project, Tag 0DXW](https://stacks.math.columbia.edu/tag/0DXW)
* [Stacks Project, Tag 0EKZ](https://stacks.math.columbia.edu/tag/0EKZ)
* [Stacks Project, Tag 0EKV](https://stacks.math.columbia.edu/tag/0EKV)
* [Stacks Project, Tag 0EIL](https://stacks.math.columbia.edu/tag/0EIL)
* [Stacks Project, Tag 0EIR](https://stacks.math.columbia.edu/tag/0EIR)
* [Stacks Project, Tag 0EHH](https://stacks.math.columbia.edu/tag/0EHH)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
* [Stacks Project, Tag 0EHA](https://stacks.math.columbia.edu/tag/0EHA)
* [Stacks Project, Tag 0BLC](https://stacks.math.columbia.edu/tag/0BLC)
* [Stacks Project, Tag 0H39](https://stacks.math.columbia.edu/tag/0H39)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open Stacks.Cohomology.InverseSystems.TorsionFreeDivisible (Condition1)

universe v u

namespace Stacks.Algebraization

/-! ### Inverse systems and `CategoryTheory.Functor.ofOpSequence` -/

/-- The maps of the inverse system rebuilt from the successive transition maps agree with the
original ones. The composite of `i - j` successive maps is the original map `i ⟶ j` because both
are the image of the same morphism of `ℕᵒᵖ`. -/
theorem ofOpSequence_map_eq_map {C : Type u} [Category.{v} C] (G : ℕᵒᵖ ⥤ C) (i j : ℕ)
    (h : j ≤ i) :
    (Functor.ofOpSequence (X := fun n => G.obj (op n))
        (fun n => G.map (homOfLE (Nat.le_succ n)).op)).map (homOfLE h).op =
      G.map (homOfLE h).op := by
  induction i with
  | zero =>
    obtain rfl : j = 0 := Nat.le_zero.mp h
    have h1 : (homOfLE h).op = 𝟙 (op 0) := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [h1, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  | succ i ih =>
    rcases Nat.lt_or_ge j (i + 1) with hlt | hge
    · have hji : j ≤ i := Nat.lt_succ_iff.mp hlt
      have hstep : (homOfLE h).op = (homOfLE (Nat.le_succ i)).op ≫ (homOfLE hji).op :=
        Quiver.Hom.unop_inj (Subsingleton.elim _ _)
      rw [hstep, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, ih hji,
        CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ]
      rfl
    · obtain rfl : j = i + 1 := le_antisymm h hge
      have h1 : (homOfLE h).op = 𝟙 (op (i + 1)) := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
      rw [h1, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      rfl

/-- Every inverse system indexed by `ℕᵒᵖ` is the one `CategoryTheory.Functor.ofOpSequence` builds
from its own successive transition maps. This is the shape in which the degree-zero half of
Stacks 0EHA asks for its tower. -/
theorem eq_ofOpSequence {C : Type u} [Category.{v} C] (G : ℕᵒᵖ ⥤ C) :
    G = Functor.ofOpSequence (X := fun n => G.obj (op n))
      (fun n => G.map (homOfLE (Nat.le_succ n)).op) := by
  refine CategoryTheory.Functor.ext (fun X => rfl) ?_
  intro X Y f
  obtain ⟨i⟩ := X
  obtain ⟨j⟩ := Y
  have hji : j ≤ i := leOfHom f.unop
  obtain rfl := Subsingleton.elim f (homOfLE hji).op
  exact ((Category.id_comp _).trans
    ((Category.comp_id _).trans (ofOpSequence_map_eq_map G i j hji))).symm

/-! ### The adic topology from a kernel formula -/

/-- A filtration by the images of the powers of a single scalar presents the inverse-limit
topology of a tower as the adic topology of the principal ideal that scalar generates. -/
theorem iInf_induced_eq_adicModuleTopology_of_range_pow
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    {N : ℕ → Type v} [∀ n, AddCommGroup (N n)] [∀ n, Module A (N n)]
    (f : A) (g : ∀ n, M →ₗ[A] N n)
    (hker : ∀ n, LinearMap.ker (g n) = LinearMap.range (LinearMap.lsmul A M (f ^ (n + 1)))) :
    (⨅ n : ℕ, TopologicalSpace.induced (fun y : M => g n y) ⊥) =
      (Ideal.span {f}).adicModuleTopology M := by
  classical
  have hmem (k : ℕ) : f ^ k ∈ (Ideal.span {f} : Ideal A) ^ k :=
    Ideal.pow_mem_pow (Ideal.mem_span_singleton_self f) k
  refine Stacks.AdicLimit.iInf_induced_eq_adicModuleTopology (Ideal.span {f}) g ?_ ?_ ?_
  · intro i j hij y hy
    rw [hker j, LinearMap.mem_range] at hy
    rw [hker i, LinearMap.mem_range]
    obtain ⟨z, hz⟩ := hy
    rw [LinearMap.lsmul_apply] at hz
    refine ⟨f ^ (j - i) • z, ?_⟩
    rw [LinearMap.lsmul_apply, smul_smul, ← pow_add,
      show i + 1 + (j - i) = j + 1 from by omega]
    exact hz
  · refine fun n => ⟨n + 1, ?_⟩
    rw [hker n]
    refine Submodule.smul_le.mpr fun r hr y _ => ?_
    rw [LinearMap.mem_range]
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp
      (by simpa only [Ideal.span_singleton_pow] using hr)
    exact ⟨s • y, by rw [LinearMap.lsmul_apply, smul_smul, ← hs]⟩
  · refine fun k => ⟨k, ?_⟩
    rw [hker k]
    rintro y hy
    rw [LinearMap.mem_range] at hy
    obtain ⟨z, rfl⟩ := hy
    rw [LinearMap.lsmul_apply, pow_succ, mul_smul]
    exact Submodule.smul_mem_smul (hmem k) Submodule.mem_top

/-! ### Bridging instances

The two instances below restate existing structures at the spelling instance search meets, so
nothing new is assumed. -/

/-- The rings of sections of the structure sheaf of a scheme, read as objects of `RingCat`, have
commutative multiplication. This is the hypothesis of
`Stacks.SheafOfModules.terminalSectionToEnd`; instance search does not find it because the
commutative-ring structure is attached to the `CommRingCat` object `Γ(X, U)` instead. -/
local instance mulCommutativeRingCatSheaf (X : Scheme.{u}) (U : (X.Opens)ᵒᵖ) :
    IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  ⟨⟨fun a b => mul_comm (G := Γ(X, U.unop)) a b⟩⟩

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- The ring `Γ(U, 𝒪_U)` of global sections on the open complement, read as the carrier of the
`RingCat` object of `S.U.toScheme.ringCatSheaf` over `⊤`. This is the spelling the
Mittag-Leffler criteria of Stacks 0BLC and Stacks 0EHA use. -/
abbrev topSectionsRing : Type u := S.U.toScheme.ringCatSheaf.obj.obj (op (⊤ : S.U.toScheme.Opens))

/-- The `A`-algebra structure on `Γ(U, 𝒪_U)` given by `Stacks.Algebraization.scalarMap`. Stacks
0BLC states its coefficient action in this form. -/
local instance topSectionsAlgebra : Algebra S.A (topSectionsRing S) :=
  RingHom.toAlgebra (scalarMap S : S.A →+* topSectionsRing S)

/-! ### The adic system as a zero-indexed tower -/

/-- The term of index `n` of a coherent adic system on the open complement, i.e. the source's
`F_{n+1}`. -/
abbrev systemObj (n : ℕ) : S.U.toScheme.Modules := F.obj.obj (op n)

/-- The transition map from the term of index `n + 1` to the term of index `n`. -/
abbrev systemMapSucc (n : ℕ) : systemObj S F (n + 1) ⟶ systemObj S F n :=
  F.obj.map (homOfLE (Nat.le_succ n)).op

/-- Multiplication by an element of the base ring `A`, as an endomorphism of the identity functor
of `𝒪_U`-modules. The element acts through its image in `Γ(U, 𝒪_U)`. -/
abbrev mulBySection (f : S.A) : End (𝟭 (SheafOfModules.{u} S.U.toScheme.ringCatSheaf)) :=
  Stacks.SheafOfModules.terminalSectionToEnd S.U.toScheme.ringCatSheaf (⊤ : S.U.toScheme.Opens)
    isTerminalTop (scalarMap S f)

/-- **Stacks Project, Tag 0DXW (the short exact sequences of the proof).** Multiplication by `f`
on `F_{n+1}` factors through the transition map `F_{n+1} → F_n` by a map `F_n → F_{n+1}` whose
cokernel sequence `0 → F_n → F_{n+1} → F_1 → 0` is short exact.

This is condition (1) of Stacks 0H39 for multiplication by `f`. The source obtains it from finite
local freeness of `F_n` over `𝒪_U/f^n𝒪_U` together with the short exact sequences
`0 → A/f^nA → A/f^{n+1}A → A/fA → 0` for a nonzerodivisor `f`. -/
abbrev HasPrincipalShortExactSequences (f : S.A) : Prop :=
  Condition1 (mulBySection S f) (systemObj S F) (systemMapSucc S F)

/-- `H^p(U, -)` on the open complement, as a functor to `A`-modules. Degree zero of it is
`Stacks.Algebraization.openSectionsFunctor` up to the canonical identification of a left exact
functor with its zeroth right derived functor. -/
abbrev openCohomologyFunctor (p : ℕ) : S.U.toScheme.Modules ⥤ ModuleCat.{u} S.A :=
  (_root_.SheafOfModules.evaluation S.U.toScheme.ringCatSheaf
      (op (⊤ : S.U.toScheme.Opens))).rightDerived p ⋙
    ModuleCat.restrictScalars (scalarMap S)

/-! ### Condition (b) of Stacks 0EHH: the limit topology is the adic topology -/

/-- **Stacks Project, Tag 0EHA in degree zero.** The `f^(n+1)`-multiples in
`M = limₙ H⁰(U, F_n)` are exactly the compatible global sections dying in `F_n`. -/
theorem range_pow_eq_ker_limitProjection_globalSections (f : S.A)
    (h : HasPrincipalShortExactSequences S F f) (n : ℕ) :
    LinearMap.range (LinearMap.lsmul S.A (limitGlobalSections S F) (f ^ (n + 1))) =
      LinearMap.ker (limit.π (globalSectionsSystem S F) (op n)).hom :=
  Stacks.Modules.range_pow_eq_ker_limitProjection_terminalSections
    S.U.toScheme.ringCatSheaf (⊤ : S.U.toScheme.Opens) isTerminalTop (scalarMap S) f
    (systemObj S F) (systemMapSucc S F) h (globalSectionsSystem S F)
    (eq_ofOpSequence (globalSectionsSystem S F)) n

/-- **Stacks Project, Tag 0DXW (condition (b) of Tag 0EHH).** The inverse-limit topology on
`M = limₙ H⁰(U, F_n)` is the `I`-adic topology, for `I = (f)` principal. -/
theorem adicModuleTopology_limitGlobalSections (f : S.A) (hI : S.I = Ideal.span {f})
    (h : HasPrincipalShortExactSequences S F f) :
    (⨅ n : ℕ, TopologicalSpace.induced
        (fun x : limitGlobalSections S F =>
          (limit.π (globalSectionsSystem S F) (op n)).hom x) ⊥) =
      S.I.adicModuleTopology (limitGlobalSections S F) := by
  rw [hI]
  exact iInf_induced_eq_adicModuleTopology_of_range_pow f
    (fun n => (limit.π (globalSectionsSystem S F) (op n)).hom)
    fun n => (range_pow_eq_ker_limitProjection_globalSections S F f h n).symm

/-! ### Condition (a) of Stacks 0EHH: Mittag-Leffler -/

/-- Mittag-Leffler for the zeroth right derived functor of sections along the tower gives it for
`H⁰(U, F_n)`, by `rightDerivedZeroIsoSelf` and exactness of restriction of scalars to `A`. -/
private theorem isMittagLeffler_globalSectionsSystem_of_rightDerived_zero
    (key : IsMittagLefflerCategorical (Functor.ofOpSequence (systemMapSucc S F) ⋙
      (_root_.SheafOfModules.evaluation S.U.toScheme.ringCatSheaf
        (op (⊤ : S.U.toScheme.Opens))).rightDerived 0)) :
    IsMittagLefflerCategorical (globalSectionsSystem S F) := by
  have hzero : IsMittagLefflerCategorical (Functor.ofOpSequence (systemMapSucc S F) ⋙
      _root_.SheafOfModules.evaluation S.U.toScheme.ringCatSheaf
        (op (⊤ : S.U.toScheme.Opens))) :=
    IsMittagLefflerCategorical.of_natIso
      (Functor.isoWhiskerLeft _ (_root_.SheafOfModules.evaluation S.U.toScheme.ringCatSheaf
        (op (⊤ : S.U.toScheme.Opens))).rightDerivedZeroIsoSelf.symm) key
  have hadd : (ModuleCat.restrictScalars (scalarMap S : S.A →+* topSectionsRing S)).Additive :=
    inferInstance
  have hrestrict := @IsMittagLefflerCategorical.map _ _ _ _ _ _ _
    (ModuleCat.restrictScalars (scalarMap S : S.A →+* topSectionsRing S)) hadd inferInstance
    inferInstance hzero
  have hsystem : globalSectionsSystem S F =
      Functor.ofOpSequence (systemMapSucc S F) ⋙ openSectionsFunctor S :=
    congrArg (fun G => G ⋙ openSectionsFunctor S) (eq_ofOpSequence F.obj)
  rw [hsystem]
  exact hrestrict

/-- **Stacks Project, Tag 0DXW (condition (a) of Tag 0EHH).** If `H¹(U, F_1)` is a finite
`A`-module, the inverse system `H⁰(U, F_n)` satisfies the Mittag-Leffler condition.

This is Stacks 0BLC in degree zero, transported along the canonical identification of sections
with their zeroth right derived functor and along restriction of scalars to `A`. -/
theorem isMittagLeffler_globalSectionsSystem (f : S.A)
    (h : HasPrincipalShortExactSequences S F f)
    (hfin : Module.Finite S.A ((openCohomologyFunctor S 1).obj (systemObj S F 0))) :
    IsMittagLefflerCategorical (globalSectionsSystem S F) := by
  have key := Stacks.Cohomology.InverseSystems.isMittagLefflerCategorical_of_finite_cohomology
    S.U.toScheme.ringCatSheaf S.A f (systemObj S F) (systemMapSucc S F) 0
    (Or.inr ⟨S.noetherianA, hfin⟩) h
  exact isMittagLeffler_globalSectionsSystem_of_rightDerived_zero S F key

/-- **Stacks Project, Tag 0DXU (condition (a) of Tag 0EHH).**  If the image of
`H¹(U, F_{n+1}) ⟶ H¹(U, F_1)` has finite length as an `A`-module for some `n`, the inverse
system `H⁰(U, F_n)` satisfies the Mittag-Leffler condition.

This is [Stacks, Tag 0DXG] in degree zero, where `Stacks.Algebraization`
`.isMittagLeffler_globalSectionsSystem` is [Stacks, Tag 0BLC] in degree zero.  The hypothesis is
weaker: 0BLC asks `H¹(U, F_1)` itself to be finite, which is what the proof of
[Stacks, Tag 0DXW] produces, while the proof of [Stacks, Tag 0DXU] produces only the finite
length of the image, and says so in the words "it suffices to show that there exists an `n > 1`
such that the image of `H¹(U, ℱₙ) ⟶ H¹(U, ℱ₁)` has finite length as an `A`-module. Namely, this
will imply hypothesis (a) by Cohomology, Lemma 20.36.5."

The transport is the same as for the 0BLC version: along the canonical identification of
sections with their zeroth right derived functor, and along restriction of scalars to `A`. -/
theorem isMittagLeffler_globalSectionsSystem_of_isFiniteLength_range (f : S.A)
    (h : HasPrincipalShortExactSequences S F f)
    (hfin : ∃ n : ℕ, IsFiniteLength S.A
      (LinearMap.range ((openCohomologyFunctor S 1).map
        (Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj
          (systemObj S F) (systemMapSucc S F) n)).hom)) :
    IsMittagLefflerCategorical (globalSectionsSystem S F) := by
  have key :=
    Stacks.Cohomology.InverseSystems.isMittagLefflerCategorical_of_finite_cohomology_image
      S.U.toScheme.ringCatSheaf S.A f (systemObj S F) (systemMapSucc S F) 0
      (Or.inl hfin) h
  exact isMittagLeffler_globalSectionsSystem_of_rightDerived_zero S F key

/-! ### Condition (c) of Stacks 0EHH: finiteness of the sections -/

/-- If the two outer terms of a short exact sequence of `𝒪_U`-modules have finite `A`-modules of
sections, so has the middle term. Sections on `U` are left exact, so the sections of the middle
term are an extension of a submodule of the sections of the third term by the sections of the
first, and `A` is Noetherian. -/
theorem finite_middle_of_shortExact
    {M N P : S.U.toScheme.Modules} (i : M ⟶ N) (p : N ⟶ P) (w : i ≫ p = 0)
    (hse : (ShortComplex.mk i p w).ShortExact)
    (hM : Module.Finite S.A ((openSectionsFunctor S).obj M))
    (hP : Module.Finite S.A ((openSectionsFunctor S).obj P)) :
    Module.Finite S.A ((openSectionsFunctor S).obj N) := by
  have hnP : IsNoetherian S.A ((openSectionsFunctor S).obj P) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  have hrangefg : (LinearMap.range ((openSectionsFunctor S).map i).hom).FG := by
    rw [← Submodule.map_top]
    exact (Module.finite_def.mp hM).map _
  have hrange : Module.Finite S.A (LinearMap.range ((openSectionsFunctor S).map i).hom) :=
    Module.Finite.iff_fg.mpr hrangefg
  have hrnoeth : IsNoetherian S.A (LinearMap.range ((openSectionsFunctor S).map i).hom) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  have hle : LinearMap.ker ((openSectionsFunctor S).map p).hom ≤
      LinearMap.range ((openSectionsFunctor S).map i).hom := by
    intro y hy
    have hy0 : Scheme.Modules.Hom.app p (⊤ : S.U.toScheme.Opens) y = 0 := hy
    obtain ⟨x, hx⟩ := exists_app_eq_of_shortExact (ShortComplex.mk i p w) hse
      (⊤ : S.U.toScheme.Opens) y hy0
    exact ⟨x, hx⟩
  have hkerfg : (LinearMap.ker ((openSectionsFunctor S).map p).hom).FG := by
    have hmc := Submodule.map_comap_eq_self
      (f := (LinearMap.range ((openSectionsFunctor S).map i).hom).subtype)
      (q := LinearMap.ker ((openSectionsFunctor S).map p).hom)
      (by rw [Submodule.range_subtype]; exact hle)
    rw [← hmc]
    exact (IsNoetherian.noetherian _).map _
  refine Module.finite_def.mpr (Submodule.fg_of_fg_map_of_fg_inf_ker
    ((openSectionsFunctor S).map p).hom ?_ ?_)
  · exact IsNoetherian.noetherian _
  · rwa [top_inf_eq]

/-- **Stacks Project, Tag 0DXW (condition (c) of Tag 0EHH).** If `H⁰(U, F_1)` is a finite
`A`-module, then so is `H⁰(U, F_n)` for every `n`.

This is the source's "using induction and the short exact sequences we find that `H⁰(U, F_n)` are
finite `A`-modules for all `n`": the sequence `0 → F_n → F_{n+1} → F_1 → 0` has both outer terms
with finite sections by the inductive hypothesis and the base case. -/
theorem finite_globalSections_of_shortExactSequences (f : S.A)
    (h : HasPrincipalShortExactSequences S F f)
    (h0 : Module.Finite S.A ((globalSectionsSystem S F).obj (op 0))) :
    ∀ n, Module.Finite S.A ((globalSectionsSystem S F).obj (op n)) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    obtain ⟨i, w, _, hse⟩ := h n
    exact finite_middle_of_shortExact S i _ w hse ih h0

/-! ### Stacks 0DXW -/

/-- **Stacks Project, Tag 0DXW, first clause.** Let `S` be an algebraization situation whose ideal
`I` is the principal ideal generated by `f ∈ A`, and let `(F_n)` be a coherent `I`-adic system on
the open complement `U`. If the system has the short exact sequences
`0 → F_n → F_{n+1} → F_1 → 0` of the source's proof, and if `H⁰(U, F_1)` and `H¹(U, F_1)` are
finite `A`-modules, then `(F_n)` extends canonically to `X = Spec(A)`.

The three hypotheses (a), (b), (c) of the Mittag-Leffler criterion Stacks 0EHH are proved here:
(b) from the degree-zero half of Stacks 0EHA, (a) from Stacks 0BLC, and (c) by the source's
induction on the short exact sequences.

The source's hypotheses (2) and (3) are replaced by the two consequences its proof uses. Finite
local freeness of `F_n` over `𝒪_U/f^n𝒪_U` and the nonzerodivisor property of `f` are used only
to produce the short exact sequences `0 → F_n → F_{n+1} → F_1 → 0`, which is the hypothesis `h`;
and the finiteness of `H¹_𝔞(A/fA)` and `H²_𝔞(A/fA)` is used only to produce the finiteness of
`H⁰(U, F_1)` and `H¹(U, F_1)`, by Local Cohomology 0BK0 and 0BLT, which are the hypotheses `h0`
and `h1`. Neither derivation is carried out here.

The source's second clause, algebraizability over an `I`-adically complete `A`, is
`Stacks.Algebraization.isCompletionNearClosed_of_principal_shortExactSequences`.

Stacks 0DXW itself, with the source's own hypotheses and both of its clauses, is
`Stacks.Algebraization.canonicallyExtends_and_isCompletion_of_principal`, which derives the two
hypotheses below from them. -/
@[stacks 0DXW "first clause (canonical extension) only; conditions (a), (b), (c) of 0EHH are \
proved, but hypotheses (2) and (3) of the source are replaced by the consequences its proof \
draws from them, namely the short exact sequences 0 → Fₙ → F₍ₙ₊₁₎ → F₁ → 0 and the finiteness \
of H⁰(U, F₁) and H¹(U, F₁)"]
theorem canonicallyExtends_of_principal_shortExactSequences (f : S.A)
    (hI : S.I = Ideal.span {f}) (h : HasPrincipalShortExactSequences S F f)
    (h0 : Module.Finite S.A ((globalSectionsSystem S F).obj (op 0)))
    (h1 : Module.Finite S.A ((openCohomologyFunctor S 1).obj (systemObj S F 0))) :
    CanonicallyExtends S F :=
  canonicallyExtends_of_finite_globalSections S F
    (isMittagLeffler_globalSectionsSystem S F f h h1)
    (adicModuleTopology_limitGlobalSections S F f hI h)
    (finite_globalSections_of_shortExactSequences S F f h h0)

/-! ### Stacks 0EKZ: the essential-surjectivity half -/

/-- The ideal `I 𝒪_U` on the open complement is the pullback along `U ⟶ X` of the kernel ideal
sheaf of the closed immersion `Y ⟶ X`. -/
theorem idealOnOpen_eq_ker_comap : idealOnOpen S = S.Yι.ker.comap S.U.ι := by
  rw [ker_Yι_eq_ofIdealTop]

/-- A coherent `I`-adic system on `U`, read along the kernel ideal sheaf of `Y ⟶ X`. This is the
spelling the algebraization conditions of Stacks 0EIL are stated with. -/
def kerComapSystem : Stacks.Coherent.CoherentAdicSystems (S.Yι.ker.comap S.U.ι) :=
  ⟨F.obj, by rw [← idealOnOpen_eq_ker_comap]; exact F.property⟩

/-- The diagram of a coherent `I 𝒪_U`-adic system is a coherent adic system along the pullback to
`U` of the kernel ideal sheaf of `Y ⟶ X`, the two ideal sheaves being equal. -/
public theorem isCoherentAdicSystem_kerComap :
    Stacks.Coherent.IsCoherentAdicSystem (S.Yι.ker.comap S.U.ι) F.obj := by
  rw [← idealOnOpen_eq_ker_comap]
  exact F.property

/-- `Stacks.Algebraization.ExtendsToX` for a system presented by its underlying diagram, that
diagram being a variable: the predicate mentions the system only through it. -/
private theorem extendsToX_ofDiagram {D D' : ℕᵒᵖ ⥤ S.U.toScheme.Modules}
    (hD : Stacks.Coherent.IsCoherentAdicSystem (S.Yι.ker.comap S.U.ι) D) (hDD' : D' = D)
    (h : ∃ G : Stacks.Coherent.CoherentAdicSystems S.Yι.ker,
      Nonempty (G.obj ⋙ Scheme.Modules.restrictFunctor S.U.ι ≅ D')) :
    ExtendsToX S ⟨D, hD⟩ := by
  obtain ⟨G, ⟨e⟩⟩ := h
  exact ⟨G, ⟨e ≪≫ eqToIso hDD'⟩⟩

/-- **The chain of [Stacks, Tag 0EIL] from canonical extension to algebraizability.**  Over an
`f`-adically complete `A`, a coherent `I`-adic system on `U` that extends canonically to
`X = Spec(A)` is the completion of a coherent module on an open neighbourhood of `U ∩ V(f)`
inside `U`.

Part (2) of [Stacks, Tag 0EIR] turns canonical extension into extendability, applied to the
comparison `Stacks.Algebraization.tildeGlobalSectionsPullbackIso`, which supplies the canonical
maps `H⁰(U, F_n)^~|_U ⟶ F_n` from the quasi-affineness of `U`; adic completeness then runs the
chain of [Stacks, Tag 0EIL]: condition (6) implies (5) by
`Stacks.Algebraization.isRestrictionOfCompletion_of_extendsToX`, and conditions (5), (4), (2)
and (3) agree.

This is the half of the proof of [Stacks, Tag 0DXW] and [Stacks, Tag 0DXU] that does not depend
on which Mittag-Leffler criterion produced the canonical extension. -/
theorem isCompletionNearClosed_of_canonicallyExtends (f : S.A)
    (hI : S.I = Ideal.span {f}) (hcomplete : IsAdicComplete (Ideal.span {f}) S.A)
    (hce : CanonicallyExtends S F) :
    IsCompletionNearClosed S (kerComapSystem S F) := by
  have : IsAdicComplete S.I S.A := by rw [hI]; exact hcomplete
  have hext : ExtendsToX S (kerComapSystem S F) :=
    extendsToX_ofDiagram S (isCoherentAdicSystem_kerComap S F) (toKerSystem_obj S F)
      (extendsToX_of_canonicallyExtends S F (tildeGlobalSectionsPullbackIso S F) hce)
  exact (isCompletion_iff_nearClosed S (kerComapSystem S F)).mp
    ((isCompletion_iff_ofRestriction S (kerComapSystem S F)).mpr
      ((isCompletionOfRestriction_iff_isRestrictionOfCompletion S (kerComapSystem S F)).mpr
        (isRestrictionOfCompletion_of_extendsToX S (kerComapSystem S F) hext)))

/-- **Stacks Project, Tag 0EKZ, the essential-surjectivity half.** Let `S` be an algebraization
situation whose ideal `I` is generated by `f ∈ A`, let `A` be `f`-adically complete, and let
`(F_n)` be a coherent `I`-adic system on the open complement `U`. If the system has the short
exact sequences `0 → F_n → F_{n+1} → F_1 → 0` of the proof of Stacks 0DXW and if `H⁰(U, F_1)` and
`H¹(U, F_1)` are finite `A`-modules, then `(F_n)` is the completion of a coherent module on an
open neighbourhood of `U ∩ V(f)` inside `U`: it lies in the image of the completion functor
`colim_{U₀ ⊆ U' ⊆ U} Coh(𝒪_{U'}) ⟶ Coh(U, f𝒪_U)` of Stacks 0EKZ.

The system extends canonically to `X` by Stacks 0DXW, and part (2) of Stacks 0EIR turns that into
extendability. Adic completeness then runs the chain of Stacks 0EIL: an extendable system is the
restriction of a completion on `X`, hence the completion of a module restricted from `X`, hence a
completion on `U`, hence a completion near the closed subscheme.

Two properties of the system are asked for in place of conditions (2) and (3) of Stacks 0DXW,
being what its proof draws from them, exactly as in
`Stacks.Algebraization.canonicallyExtends_of_principal_shortExactSequences`. The
full-faithfulness half of Stacks 0EKZ is Stacks 0EKV, and the module produced here is coherent,
with finite local freeness not among the conclusions.

Stacks 0EKZ itself, with the source's own hypotheses and all of its content, is
`Stacks.Algebraization.completionEquivalence_principal_finiteLocallyFree`, which derives the two
hypotheses below from them and produces a finite locally free module. -/
@[stacks 0EKZ "the essential-surjectivity half: over an f-adically complete A, a coherent I-adic \
system on U which has the short exact sequences 0 → Fₙ → F₍ₙ₊₁₎ → F₁ → 0 of the proof of Stacks \
0DXW and whose H⁰(U, F₁) and H¹(U, F₁) are finite is the completion of a coherent module on an \
open neighbourhood of U ∩ V(f) in U, i.e. lies in the image of the colimit functor of this tag. \
Those two properties of the system are what the proof of Stacks 0DXW draws from its conditions \
(2) and (3), and they are what is asked for here in their place. This declaration does not \
cover full faithfulness, which is Stacks 0EKV; and finite local freeness of the module \
produced, and so its invertibility, is not among its conclusions, which give coherence alone — \
all that the final clause of Stacks 0DXW gives as well"]
theorem isCompletionNearClosed_of_principal_shortExactSequences (f : S.A)
    (hI : S.I = Ideal.span {f}) (hcomplete : IsAdicComplete (Ideal.span {f}) S.A)
    (h : HasPrincipalShortExactSequences S F f)
    (h0 : Module.Finite S.A ((globalSectionsSystem S F).obj (op 0)))
    (h1 : Module.Finite S.A ((openCohomologyFunctor S 1).obj (systemObj S F 0))) :
    IsCompletionNearClosed S (kerComapSystem S F) :=
  isCompletionNearClosed_of_canonicallyExtends S F f hI hcomplete
    (canonicallyExtends_of_principal_shortExactSequences S F f hI h h0 h1)

/-! ### The conclusions in the shape the proof of Stacks 0DXU reaches them -/

/-- **The first clause of [Stacks, Tag 0DXU] from condition (a) in its weak form.**  Let `S` be
an algebraization situation whose ideal `I` is generated by `f ∈ A`, and let `(F_n)` be a
coherent `I`-adic system on `U` with the short exact sequences `0 → F_n → F_{n+1} → F_1 → 0`.
If `H⁰(U, F_1)` is a finite `A`-module and the image of `H¹(U, F_{n+1}) ⟶ H¹(U, F_1)` has finite
length for some `n`, then `(F_n)` extends canonically to `X = Spec(A)`.

This is `Stacks.Algebraization.canonicallyExtends_of_principal_shortExactSequences` with
[Stacks, Tag 0BLC] replaced by [Stacks, Tag 0DXG]: the finite length of the image of a single
transition map in place of the finiteness of `H¹(U, F_1)` itself.  The proof of
[Stacks, Tag 0DXU] reaches exactly this hypothesis — "it suffices to show that there exists an
`n > 1` such that the image of `H¹(U, ℱₙ) → H¹(U, ℱ₁)` has finite length as an `A`-module" —
and cannot reach the stronger one, `H¹(U, F_1)` being infinite in general under its
hypotheses. -/
theorem canonicallyExtends_of_isFiniteLength_range (f : S.A)
    (hI : S.I = Ideal.span {f}) (h : HasPrincipalShortExactSequences S F f)
    (h0 : Module.Finite S.A ((globalSectionsSystem S F).obj (op 0)))
    (h1 : ∃ n : ℕ, IsFiniteLength S.A
      (LinearMap.range ((openCohomologyFunctor S 1).map
        (Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj
          (systemObj S F) (systemMapSucc S F) n)).hom)) :
    CanonicallyExtends S F :=
  canonicallyExtends_of_finite_globalSections S F
    (isMittagLeffler_globalSectionsSystem_of_isFiniteLength_range S F f h h1)
    (adicModuleTopology_limitGlobalSections S F f hI h)
    (finite_globalSections_of_shortExactSequences S F f h h0)

/-- **The second clause of [Stacks, Tag 0DXU] from condition (a) in its weak form.**  In the
situation of `Stacks.Algebraization.canonicallyExtends_of_isFiniteLength_range`, if `A` is
moreover `f`-adically complete then `(F_n)` is the completion of a coherent module on an open
neighbourhood of `U ∩ V(f)` inside `U`.

The two clauses are related exactly as in [Stacks, Tag 0DXW]: canonical extension plus adic
completeness run the chain of [Stacks, Tag 0EIL], which is
`Stacks.Algebraization.isCompletionNearClosed_of_canonicallyExtends`. -/
theorem isCompletionNearClosed_of_isFiniteLength_range (f : S.A)
    (hI : S.I = Ideal.span {f}) (hcomplete : IsAdicComplete (Ideal.span {f}) S.A)
    (h : HasPrincipalShortExactSequences S F f)
    (h0 : Module.Finite S.A ((globalSectionsSystem S F).obj (op 0)))
    (h1 : ∃ n : ℕ, IsFiniteLength S.A
      (LinearMap.range ((openCohomologyFunctor S 1).map
        (Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj
          (systemObj S F) (systemMapSucc S F) n)).hom)) :
    IsCompletionNearClosed S (kerComapSystem S F) :=
  isCompletionNearClosed_of_canonicallyExtends S F f hI hcomplete
    (canonicallyExtends_of_isFiniteLength_range S F f hI h h0 h1)

end Stacks.Algebraization

end
