module

public import StacksFrontier.AlgebraicGeometry.EulerCharVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.ZeroDimensionalTensor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Twisting is exact, and Tag 0BEM from its geometry alone

The induction of [Stacks, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM) is driven by the
first difference of the Euler characteristic in one twisting direction. The source computes that
difference from two short exact sequences: for a coherent `ℱ` with positive-dimensional support
it produces, out of a regular meromorphic section of `𝓛_i` and its ideal of denominators `ℐ`,
the two injections

  `ℐℱ ⟶ ℱ`,  `ℐℱ ⟶ ℱ ⊗ 𝓛_i`

whose cokernels `𝒬`, `𝒬'` are supported on nowhere dense closed subschemes, and then says
"tensoring with an invertible module is exact, hence using additivity again" to conclude

  `χ(ℱ ⊗ 𝓛_i ⊗ twist) - χ(ℱ ⊗ twist) = χ(𝒬' ⊗ twist) - χ(𝒬 ⊗ twist)`.

This file supplies everything in that sentence. Twisting is exact because tensoring by an
invertible sheaf of modules is an *equivalence* of categories
(`Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence`), and a tensor power of an
invertible sheaf is invertible; so the twisting fold is a composite of equivalences and carries
short exact sequences to short exact sequences. Additivity is then
`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional`, which asks for
finite-dimensionality of the cohomology of the two *outer* terms only.

The outcome is `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_differenceSequences`:
Tag 0BEM's full conclusion from two hypotheses, each of which is a Stacks statement in its own
right rather than a bespoke identity about Euler characteristics.

## Main definitions

* `Stacks.SheafOfModules.Invertible.twistStepFunctor`: one step of the twisting fold, namely
  tensoring on the right by `𝓛_i^{⊗ e i}`.
* `Stacks.SheafOfModules.Invertible.twistListFunctor` and its generalization
  `twistListFunctorFrom`: the twisting fold along a list of indices, as an endofunctor.
* `AlgebraicGeometry.twistedSheafFunctor`: twisting by a fixed exponent vector, as an
  endofunctor of `X.Modules`, whose value at `ℱ` is `AlgebraicGeometry.twistedSheaf ℱ 𝓛 n`.
* `AlgebraicGeometry.twistedSheafTensorIso`: `(ℱ ⊗ 𝓛_i) ⊗ twist ≅ (ℱ ⊗ twist) ⊗ 𝓛_i`.

## Main results

* `Stacks.SheafOfModules.Invertible.twistListFunctor_isEquivalence`: **the twisting fold is an
  equivalence of categories.**
* `AlgebraicGeometry.shortExact_map_twistedSheafFunctor`: **twisting is exact.** Twisting a
  short exact sequence of sheaves of modules by integer powers of invertible sheaves gives a
  short exact sequence.
* `AlgebraicGeometry.eulerCharacteristic_twistedSheaf_add_of_shortExact`: **additivity of the
  Euler characteristic on twists**, from Tag 02O6 for the two outer terms.
* `AlgebraicGeometry.eulerCharacteristic_twistedSheaf_update_eq`: raising the `i`-th exponent by
  one computes the Euler characteristic of the twist of `ℱ ⊗ 𝓛_i`. This is the identification
  that turns the source's two sequences into a first difference.
* `AlgebraicGeometry.eulerCharacteristic_twistedSheaf_update_sub_eq_of_differenceSequences`:
  **the first difference from one pair of difference sequences**, which is the whole
  Euler-characteristic content of the theorem below with the quantifiers removed, so that a
  supplier holding the sequences for a single sheaf can use it.
* `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_differenceSequences`: **Tag 0BEM
  from Tag 02O6 and the source's difference sequences.**

## Implementation notes

**Why the functors are built at the `Stacks.SheafOfModules.TensorSheafification` spelling.**
  `AlgebraicGeometry.Scheme.Modules`
is `SheafOfModules X.ringCatSheaf`, while right tensoring by a fixed sheaf of modules —
`(Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, _⟩).flip.obj` — is an endofunctor of
`SheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf
  X.presheaf X.ringCatSheaf.2)`.
The two categories are definitionally equal, but instance search — being syntactic — does not
bridge them, and ascribing the step functor's type to `X.Modules ⥤ X.Modules` makes
`tensorRightFunctor_isEquivalence` fail to fire. The fold is therefore constructed over an
abstract sheaf of rings `(O, hO)`, where the instance resolves natively, and specialized to a
scheme only in `AlgebraicGeometry.twistedSheafFunctor`, where the conversion is an
`exact`-level definitional equality. This is the same discipline `TwistedSheaf/Basic.lean`
follows for the same reason.

**The fold on objects is not `rfl`.** `twistListFunctor` folds over *functors*, accumulating
`G ⋙ twistStepFunctor`, whereas `AlgebraicGeometry.twistList` folds over *objects*. Commuting
`.obj` through the fold is an induction on the list, not a definitional equality, so
`twistListFunctorFrom_obj` is proved by induction with the starting functor generalized. Its
`eqToIso` is `AlgebraicGeometry.twistedSheafFunctorObjIso`, which is what the Euler-characteristic
statements travel along: transporting the dependent coherence argument of
`AlgebraicGeometry.eulerCharacteristic` across a propositional equality of sheaves is awkward,
while `AlgebraicGeometry.eulerCharacteristic_eq_of_iso` takes the two coherence proofs
independently and needs only an isomorphism.

**What Tag 0BEM needs beyond this file.** Exactly two things, and no Euler-characteristic
bookkeeping. Of the two, only the first remains a hypothesis in this development: the second is supplied
by `AlgebraicGeometry.isTwistDifferenceStep_hasNoEmbeddedAssociatedPoints`
(`StacksFrontier/AlgebraicGeometry/TwistedSheaf/StepAssembly.lean`), at the level of the weaker
hypothesis of `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_hstep`, so that
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_finiteDimensional_cohomology` there is
Tag 0BEM's full conclusion from `hfin` alone.

* `hfin` is Tag 02O6 — finite-dimensionality over `k` of the cohomology of a coherent sheaf on a
  proper scheme over a field. The narrowest reduction of it in the library is
  `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_forall_isFiniteType`, which
  asks instead that the higher direct images be of finite type.
* `hseq` is the source's first paragraph of geometry: Tags 02OZ (existence of a regular
  meromorphic section) and 02P2 (the two injections from the ideal of denominators, with
  nowhere dense cokernel supports), together with the reductions of Tags 02OL and 02OM to a
  sheaf without embedded associated points and of full support. Of these, 02OL is proved in
  four clauses (`CoherentSubquotients/NowhereDense.lean`), 02OZ in its three cases
  (`StacksFrontier/AlgebraicGeometry/Meromorphic/RegularSectionExistence.lean`), 02OM in four clauses
  (`StacksFrontier/AlgebraicGeometry/SchemeTheoreticSupport/Basic.lean`), and 02P2 in full for a
  general `ℱ` (`StacksFrontier/AlgebraicGeometry/Meromorphic/IdealTimesModule.lean`). From those,
  `AlgebraicGeometry.exists_differenceSequences_of_supp_eq_univ`
  (`StacksFrontier/AlgebraicGeometry/TwistedSheaf/DifferenceSequences.lean`) supplies `hseq` **for a coherent sheaf of full
  support without embedded associated points**; what remains is the reduction of an
  arbitrary coherent sheaf to that case, which is the source's own second and third paragraphs
  (02OL, then 089W and 02OM to replace the scheme by the support and carry the Euler
  characteristic back along the closed immersion). **Both of those paragraphs are proved**, at
  the level of the weaker hypothesis of
  `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_hstep` rather than of `hseq`:
  `AlgebraicGeometry.isTwistDifferenceStep_of_hasNoEmbeddedAssociatedPoints`
  (`StacksFrontier/AlgebraicGeometry/TwistedSheaf/EmbeddedPointStep.lean`) removes the embedded associated points, which cannot
  be done at `hseq` because Tag 02OL destroys the common first term, and
  `AlgebraicGeometry.isTwistDifferenceStep_hasNoEmbeddedAssociatedPoints`
  (`StacksFrontier/AlgebraicGeometry/TwistedSheaf/StepAssembly.lean`) performs the scheme change and the transport back.

**No attribute for Tag 0BEM is attached.** The tag's statement is unconditional, and
everything here is conditional on `hfin` and `hseq`.

## References

* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02OZ](https://stacks.math.columbia.edu/tag/02OZ)
* [Stacks Project, Tag 02P2](https://stacks.math.columbia.edu/tag/02P2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.TensorSheafification

universe v u w

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  {r : ℕ} (L : Fin r → SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
    O hO))
  [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible O hO (L i)]

/-- One step of the twisting fold: tensoring on the right by `𝓛_i^{⊗ e i}`. -/
noncomputable abbrev twistStepFunctor (e : Fin r → ℤ) (i : Fin r) :
    SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
      (tensorPower O hO (L i) (e i))

/-- A tensor power of an invertible sheaf of modules is invertible, and tensoring by an
invertible sheaf of modules is an equivalence, so each step of the fold is an equivalence. -/
noncomputable instance twistStepFunctor_isEquivalence (e : Fin r → ℤ) (i : Fin r) :
    (twistStepFunctor O hO L e i).IsEquivalence :=
  have : AlgebraicGeometry.SheafOfModules.IsInvertible O hO (tensorPower O hO (L i) (e i)) :=
    tensorPower_isInvertible O hO (L i) (e i)
  tensorRightFunctor_isEquivalence O hO (tensorPower O hO (L i) (e i))

/-- The twisting fold along a list of indices, started from an arbitrary endofunctor. -/
noncomputable def twistListFunctorFrom (e : Fin r → ℤ) (l : List (Fin r))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
  l.foldl (fun G i => G ⋙ twistStepFunctor O hO L e i) G

/-- A fold of equivalences, started from an equivalence, is an equivalence. -/
noncomputable instance twistListFunctorFrom_isEquivalence (e : Fin r → ℤ) :
    ∀ (l : List (Fin r)) (G : SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⥤
        SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
          [G.IsEquivalence],
      (twistListFunctorFrom O hO L e l G).IsEquivalence := by
  intro l
  induction l with
  | nil => exact fun _ _ => ‹_›
  | cons i t ih => exact fun G _ => ih (G ⋙ twistStepFunctor O hO L e i)

/-- The twisting fold along a list of indices, as an endofunctor. -/
noncomputable def twistListFunctor (e : Fin r → ℤ) (l : List (Fin r)) :
    SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
  twistListFunctorFrom O hO L e l (Functor.id _)

/-- **The twisting fold is an equivalence of categories.** -/
noncomputable instance twistListFunctor_isEquivalence (e : Fin r → ℤ) (l : List (Fin r)) :
    (twistListFunctor O hO L e l).IsEquivalence :=
  twistListFunctorFrom_isEquivalence O hO L e l (Functor.id _)

/-- The fold of functors acts on objects as the fold of tensor products. The starting functor is
generalized because the statement is proved by induction on the list. -/
theorem twistListFunctorFrom_obj (e : Fin r → ℤ) :
    ∀ (l : List (Fin r)) (G : SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⥤
        SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)),
      (twistListFunctorFrom O hO L e l G).obj M
        = l.foldl (fun M i => (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
            Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj
            ((tensorPower O hO (L i) (e i))))) (G.obj M) := by
  intro l
  induction l with
  | nil => exact fun _ _ => rfl
  | cons i t ih => exact fun G M => ih (G ⋙ twistStepFunctor O hO L e i) M

/-- The twisting endofunctor acts on objects as the twisting fold. -/
theorem twistListFunctor_obj (e : Fin r → ℤ) (l : List (Fin r))
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (twistListFunctor O hO L e l).obj M
      = l.foldl (fun M i => (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
          Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj
          ((tensorPower O hO (L i) (e i))))) M :=
  twistListFunctorFrom_obj O hO L e l (Functor.id _) M

end Stacks.SheafOfModules.Invertible

namespace AlgebraicGeometry

open Stacks.SheafOfModules.Invertible

variable {X : Scheme.{u}} {r : ℕ} (L : Fin r → X.Modules)
  [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]

/-- Twisting by a fixed exponent vector, as an endofunctor of `X.Modules`. -/
noncomputable def twistedSheafFunctor (n : Fin r → ℤ) : X.Modules ⥤ X.Modules :=
  twistListFunctor X.presheaf X.ringCatSheaf.2 L n (List.finRange r)

/-- The twisting endofunctor computes the twisted sheaf. -/
theorem twistedSheafFunctor_obj (n : Fin r → ℤ) (M : X.Modules) :
    (twistedSheafFunctor L n).obj M = twistedSheaf M L n :=
  twistListFunctor_obj X.presheaf X.ringCatSheaf.2 L n (List.finRange r) M

/-- Twisting is an equivalence of categories. -/
noncomputable instance twistedSheafFunctor_isEquivalence (n : Fin r → ℤ) :
    (twistedSheafFunctor L n).IsEquivalence :=
  twistListFunctor_isEquivalence X.presheaf X.ringCatSheaf.2 L n (List.finRange r)

/-- The twisting endofunctor's value, as an isomorphism rather than an equality: this is the
form the Euler-characteristic statements travel along. -/
noncomputable def twistedSheafFunctorObjIso (n : Fin r → ℤ) (M : X.Modules) :
    (twistedSheafFunctor L n).obj M ≅ twistedSheaf M L n :=
  eqToIso (twistedSheafFunctor_obj L n M)

/-- **Twisting is exact.** Twisting by integer powers of invertible sheaves of modules carries a
short exact sequence to a short exact sequence, being an equivalence of categories. -/
theorem shortExact_map_twistedSheafFunctor {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (n : Fin r → ℤ) : (S.map (twistedSheafFunctor L n)).ShortExact :=
  hS.map_of_exact (twistedSheafFunctor L n)

/-- Coherence of `ℱ ⊗ 𝓛_i`, from coherence of `ℱ`, with the coherence taken as an explicit
argument rather than an instance. -/
theorem isCoherent_tensorSheaf_invertible (G : X.Modules) (hG : SheafOfModules.IsCoherent G)
    (i : Fin r) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
        (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩).obj (G)).obj ((L i))) :
        X.Modules).IsCoherent :=
  have := hG
  SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X G (L i)

/-- Twisting a sheaf already tensored by `𝓛_i` is the twist tensored by `𝓛_i`: the index `i`
is not twisted by the fold, so it passes through it. -/
noncomputable def twistedSheafTensorIso (G : X.Modules) (n : Fin r → ℤ) (i : Fin r) :
    twistedSheaf ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.2)⟩).obj (G)).obj ((L i)))) L n ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
          (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩).obj
          ((twistedSheaf G L n))).obj ((L i))) :=
  twistListTensorIso L n (List.finRange r) G (L i)

section EulerCharacteristic

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {r : ℕ}
  (L : Fin r → X.Modules)
  [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]

/-- **Additivity of the Euler characteristic on twists.** Given Tag 02O6 — finite-dimensionality
of the cohomology of a coherent sheaf — the Euler characteristic of the twists of a short exact
sequence of coherent sheaves is additive, because twisting is exact.

Only the two outer terms of the twisted sequence need their cohomology finite-dimensional, which
is what `AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional` asks for;
the hypothesis is stated for every coherent sheaf because the twists are produced inside the
proof. -/
@[ega "III 2.5.2" "special case", ega "III 7.9.6" "special case"]
theorem eulerCharacteristic_twistedSheaf_add_of_shortExact [IsProper f]
    (hfin : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m : ℕ, FiniteDimensional k (cohomologyOverField k f G m))
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h1 : SheafOfModules.IsCoherent S.X₁) (h2 : SheafOfModules.IsCoherent S.X₂)
    (h3 : SheafOfModules.IsCoherent S.X₃) (n : Fin r → ℤ) :
    @eulerCharacteristic k _ X f _ (twistedSheaf S.X₂ L n)
        (@twistedSheaf_isCoherent X r S.X₂ L _ h2 n)
      = @eulerCharacteristic k _ X f _ (twistedSheaf S.X₁ L n)
          (@twistedSheaf_isCoherent X r S.X₁ L _ h1 n)
        + @eulerCharacteristic k _ X f _ (twistedSheaf S.X₃ L n)
          (@twistedSheaf_isCoherent X r S.X₃ L _ h3 n) := by
  set T := S.map (twistedSheafFunctor L n)
  have c : ∀ {M : X.Modules}, SheafOfModules.IsCoherent M →
      SheafOfModules.IsCoherent ((twistedSheafFunctor L n).obj M) := fun {M} h => by
    rw [twistedSheafFunctor_obj]
    exact @twistedSheaf_isCoherent X r M L _ h n
  have c1 : SheafOfModules.IsCoherent T.X₁ := c h1
  have c2 : SheafOfModules.IsCoherent T.X₂ := c h2
  have c3 : SheafOfModules.IsCoherent T.X₃ := c h3
  have hadd := eulerCharacteristic_add_of_shortExact_of_finiteDimensional k f
    (shortExact_map_twistedSheafFunctor L hS n)
    (fun m => hfin T.X₁ c1 m) (fun m => hfin T.X₃ c3 m)
  rwa [@eulerCharacteristic_eq_of_iso k _ X f _ _ _ c2
      (@twistedSheaf_isCoherent X r S.X₂ L _ h2 n) (twistedSheafFunctorObjIso L n S.X₂),
    @eulerCharacteristic_eq_of_iso k _ X f _ _ _ c1
      (@twistedSheaf_isCoherent X r S.X₁ L _ h1 n) (twistedSheafFunctorObjIso L n S.X₁),
    @eulerCharacteristic_eq_of_iso k _ X f _ _ _ c3
      (@twistedSheaf_isCoherent X r S.X₃ L _ h3 n) (twistedSheafFunctorObjIso L n S.X₃)] at hadd

/-- The Euler characteristic of a twist is an invariant of the isomorphism class of the sheaf
being twisted. -/
theorem eulerCharacteristic_twistedSheaf_eq_of_iso [IsProper f] {M N : X.Modules}
    (hM : SheafOfModules.IsCoherent M) (hN : SheafOfModules.IsCoherent N) (e : M ≅ N)
    (n : Fin r → ℤ) :
    @eulerCharacteristic k _ X f _ (twistedSheaf M L n)
        (@twistedSheaf_isCoherent X r M L _ hM n)
      = @eulerCharacteristic k _ X f _ (twistedSheaf N L n)
          (@twistedSheaf_isCoherent X r N L _ hN n) :=
  @eulerCharacteristic_eq_of_iso k _ X f _ _ _
    (@twistedSheaf_isCoherent X r M L _ hM n) (@twistedSheaf_isCoherent X r N L _ hN n)
    (twistedSheafIsoOfIso L e n)

/-- **Raising one exponent by one computes the Euler characteristic of the twist of `ℱ ⊗ 𝓛_i`.**
This is the identification that turns the source's two short exact sequences into a first
difference: the second sequence has `ℱ ⊗ 𝓛_i` in the middle, while the difference being computed
is in the `i`-th twisting direction. -/
theorem eulerCharacteristic_twistedSheaf_update_eq [IsProper f] (G : X.Modules)
    (hG : SheafOfModules.IsCoherent G) (n : Fin r → ℤ) (i : Fin r) :
    @eulerCharacteristic k _ X f _ (twistedSheaf G L (Function.update n i (n i + 1)))
        (@twistedSheaf_isCoherent X r G L _ hG _)
      = @eulerCharacteristic k _ X f _
          (twistedSheaf ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
              Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
              (X.ringCatSheaf.2)⟩).obj (G)).obj ((L i)))) L n)
          (@twistedSheaf_isCoherent X r _ L _ (isCoherent_tensorSheaf_invertible L G hG i) n) := by
  have h2 : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
        X.ringCatSheaf.2⟩).obj (twistedSheaf G L n)).obj (L i) : X.Modules).IsCoherent :=
    isCoherent_tensorSheaf_invertible L (twistedSheaf G L n)
      (@twistedSheaf_isCoherent X r G L _ hG n) i
  rw [@eulerCharacteristic_twistedSheaf_update k _ X f r G L _ _ n i
    (@twistedSheaf_isCoherent X r G L _ hG _) h2]
  exact (@eulerCharacteristic_eq_of_iso k _ X f _ _ _
    (@twistedSheaf_isCoherent X r _ L _ (isCoherent_tensorSheaf_invertible L G hG i) n) h2
    (twistedSheafTensorIso L G n i)).symm

/-- **The first difference of the Euler characteristic, from one pair of difference sequences.**
Given the two short exact sequences of [Stacks, Tag 02P2] for a single coherent `𝒢` and a single
twisting direction `i` — `𝒢` in the middle of one, `𝒢 ⊗ 𝓛ᵢ` in the middle of the other, with a
common first term, all up to isomorphism — the first difference of the twisted Euler
characteristics of `𝒢` in the direction `i` is the difference of those of the two third terms.

Additivity (`AlgebraicGeometry.eulerCharacteristic_twistedSheaf_add_of_shortExact`, which is
where [Stacks, Tag 02O6] enters) expresses both Euler characteristics through the common first
term, which cancels in the difference, and
`AlgebraicGeometry.eulerCharacteristic_twistedSheaf_update_eq` identifies the difference being
computed with the one the second sequence computes.

This is the Euler-characteristic bookkeeping of
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_differenceSequences` on its own, so
that a supplier holding *one* pair of sequences — rather than the universally quantified `hseq` —
can reach the identity. The quantified form below is this lemma under its quantifiers. -/
theorem eulerCharacteristic_twistedSheaf_update_sub_eq_of_differenceSequences [IsProper f]
    (hfin : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m : ℕ, FiniteDimensional k (cohomologyOverField k f G m))
    (G : X.Modules) (hG : SheafOfModules.IsCoherent G) (i : Fin r)
    {S T : ShortComplex X.Modules} (hS : S.ShortExact) (hT : T.ShortExact)
    (cS1 : SheafOfModules.IsCoherent S.X₁) (cS2 : SheafOfModules.IsCoherent S.X₂)
    (cS3 : SheafOfModules.IsCoherent S.X₃) (cT1 : SheafOfModules.IsCoherent T.X₁)
    (cT2 : SheafOfModules.IsCoherent T.X₂) (cT3 : SheafOfModules.IsCoherent T.X₃)
    (eS : S.X₂ ≅ G)
    (eT : T.X₂ ≅ ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.2)⟩).obj (G)).obj ((L i))) : X.Modules))
    (e01 : S.X₁ ≅ T.X₁) (n : Fin r → ℤ) :
    (@eulerCharacteristic k _ X f _ (twistedSheaf G L (Function.update n i (n i + 1)))
        (@twistedSheaf_isCoherent X r G L _ hG _) : ℚ)
      - (@eulerCharacteristic k _ X f _ (twistedSheaf G L n)
          (@twistedSheaf_isCoherent X r G L _ hG n) : ℚ)
      = (@eulerCharacteristic k _ X f _ (twistedSheaf T.X₃ L n)
          (@twistedSheaf_isCoherent X r T.X₃ L _ cT3 n) : ℚ)
        - (@eulerCharacteristic k _ X f _ (twistedSheaf S.X₃ L n)
            (@twistedSheaf_isCoherent X r S.X₃ L _ cS3 n) : ℚ) := by
  rw [eulerCharacteristic_twistedSheaf_update_eq k f L G hG n i,
    ← eulerCharacteristic_twistedSheaf_eq_of_iso k f L cT2
      (isCoherent_tensorSheaf_invertible L G hG i) eT n,
    eulerCharacteristic_twistedSheaf_add_of_shortExact k f L hfin hT cT1 cT2 cT3 n,
    ← eulerCharacteristic_twistedSheaf_eq_of_iso k f L cS2 hG eS n,
    eulerCharacteristic_twistedSheaf_add_of_shortExact k f L hfin hS cS1 cS2 cS3 n,
    eulerCharacteristic_twistedSheaf_eq_of_iso k f L cS1 cT1 e01 n]
  push_cast
  ring

/-- **[Stacks, Tag 0BEM] from Tag 02O6 and the source's difference sequences.** The Euler
characteristics of the twists `ℱ ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r}` of a coherent sheaf on a
proper scheme over a field are the values of a rational polynomial which is zero or of total
degree at most `dim Supp ℱ`, given:

* `hfin`, Tag 02O6: the cohomology of a coherent sheaf is finite-dimensional over `k`;
* `hseq`, the source's first paragraph of geometry: for a coherent `ℱ` with positive-dimensional
  support and each direction `i`, two short exact sequences of coherent sheaves with a common
  first term, with `ℱ` in the middle of one and `ℱ ⊗ 𝓛_i` in the middle of the other, whose
  third terms have strictly smaller support dimension.

This is `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_hstep` with its
first-difference hypothesis derived: additivity applied to each twisted sequence expresses both
Euler characteristics through the common first term, which cancels in the difference, and
`AlgebraicGeometry.eulerCharacteristic_twistedSheaf_update_eq` identifies the difference being
computed. No Euler-characteristic bookkeeping remains in Tag 0BEM's debt.

The middle terms are asked for only up to isomorphism, and the two first terms only up to
isomorphism with each other, so that a supplier need not produce them on the nose. -/
theorem exists_eulerPolynomial_twistedSheaf_of_differenceSequences [IsProper f]
    (hfin : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m : ℕ, FiniteDimensional k (cohomologyOverField k f G m))
    (hseq : ∀ G : X.Modules, SheafOfModules.IsCoherent G → natDimSupp G ≠ 0 → ∀ i : Fin r,
      ∃ S T : ShortComplex X.Modules,
        S.ShortExact ∧ T.ShortExact ∧
        SheafOfModules.IsCoherent S.X₁ ∧ SheafOfModules.IsCoherent S.X₂ ∧
          SheafOfModules.IsCoherent S.X₃ ∧
        SheafOfModules.IsCoherent T.X₁ ∧ SheafOfModules.IsCoherent T.X₂ ∧
          SheafOfModules.IsCoherent T.X₃ ∧
        Nonempty (S.X₂ ≅ G) ∧
        Nonempty (T.X₂ ≅ ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
            (X.ringCatSheaf.2)⟩).obj (G)).obj ((L i))) : X.Modules)) ∧
        Nonempty (S.X₁ ≅ T.X₁) ∧
        natDimSupp S.X₃ < natDimSupp G ∧ natDimSupp T.X₃ < natDimSupp G)
    (F : X.Modules) (hF : SheafOfModules.IsCoherent F) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤
        topologicalKrullDim (SheafOfModules.supp F)) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
        = (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
            (@twistedSheaf_isCoherent X r F L _ hF n) : ℚ) := by
  refine exists_eulerPolynomial_twistedSheaf_of_hstep k f L ?_ F hF
  intro G hG hG0 i
  obtain ⟨S, T, hS, hT, cS1, cS2, cS3, cT1, cT2, cT3, ⟨eS⟩, ⟨eT⟩, ⟨e01⟩, dS, dT⟩ :=
    hseq G hG hG0 i
  exact ⟨T.X₃, S.X₃, cT3, cS3, dT, dS, fun n =>
    eulerCharacteristic_twistedSheaf_update_sub_eq_of_differenceSequences k f L hfin G hG i
      hS hT cS1 cS2 cS3 cT1 cT2 cT3 eS eT e01 n⟩

end EulerCharacteristic

end AlgebraicGeometry

end
