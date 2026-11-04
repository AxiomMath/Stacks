module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.IdealSheafSequence.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.NoetherianSource
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.PushforwardTwist
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.DivisorDifference
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The first difference of a twisted Euler characteristic along an effective Cartier divisor

Let `k` be a field, let `X` be a proper scheme over `k`, let `i : Z ⟶ X` be a closed subscheme
and let `𝓛_1, …, 𝓛_{d+1}` be invertible `𝒪_X`-modules.  Let `D ⊆ Z` be an effective Cartier
divisor with `𝓛_1|_Z ≅ 𝒪_Z(D)`.  This file proves the **first-difference relation**

`χ(Z, 𝓛_2^{⊗ n_2} ⊗ ⋯ |_Z) - χ(Z, 𝓛_1^{⊗ -1} ⊗ 𝓛_2^{⊗ n_2} ⊗ ⋯ |_Z)
  = χ(D, 𝓛_2^{⊗ n_2} ⊗ ⋯ |_D)`

at the indicator tuples, which is the one geometric hypothesis of
`AlgebraicGeometry.intersectionNumber_eq_of_sub_eulerCharacteristic_eq_of_finiteDimensional`,
and feeds it in, obtaining [Stacks, Tag 0BEU] with [Stacks, Tag 02O6] as its only input.  That
input is itself proved in this library, so the tag is discharged outright in
`StacksFrontier/AlgebraicGeometry/Variety/NumericalIntersections/DivisorIntersectionProper.lean`.

The mechanism is the source's own: the short exact sequence

`0 ⟶ 𝒪_Z(-D) ⟶ 𝒪_Z ⟶ 𝒪_D ⟶ 0`

of [Stacks, Tag 0C6K], twisted by `𝓛_1^{⊗ 0} ⊗ 𝓛_2^{⊗ n_2} ⊗ ⋯ ⊗ 𝓛_{d+1}^{⊗ n_{d+1}}` and fed
to additivity of the Euler characteristic.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `twistedSheafCongrIso`: equal exponent vectors give isomorphic — indeed equal — twists.
* `twistedSheafConsZeroIso`: **dropping a twisting direction whose exponent is zero.** For a
  family `𝓜_0, …, 𝓜_r` and an exponent vector beginning with `0`, the twist by the whole family
  is the twist by `𝓜_1, …, 𝓜_r` alone.
* `SheafOfModules.isCoherent_of_isInvertible`: an invertible sheaf of modules on a proper scheme
  over a field is coherent.
* `twistedSheafNegativeTwistConsZeroIso`: **the identification that turns the ideal sheaf of `D`
  into a negative first exponent.** If `𝓛_1 ≅ 𝒪_Z(D)` then
  `𝒪_Z(-D) ⊗ 𝓛_1^{⊗ 0} ⊗ ⋯ ≅ 𝒪_Z ⊗ 𝓛_1^{⊗ -1} ⊗ ⋯`.
* `eulerCharacteristic_twistedSheaf_unit_sub_eq_of_isEffectiveCartierDivisor`: **the
  first-difference relation**, in exactly the shape the hypothesis `hdiff` of
  `AlgebraicGeometry.intersectionNumber_eq_of_sub_eulerCharacteristic_eq` demands.
* `intersectionNumber_eq_intersectionNumber_of_isEffectiveCartierDivisor`: **[Stacks, Tag 0BEU]
  with [Stacks, Tag 02O6] carried.**  `(𝓛_1 ⋯ 𝓛_{d+1} · Z) = (𝓛_2 ⋯ 𝓛_{d+1} · D)`.

## Implementation notes

**Why the computation is run on `X` and not on `Z`.**  The three Euler characteristics the
relation compares live on two different schemes — two on `Z` and one on `D` — while additivity
applies to a short exact sequence on one scheme.  The divisor sequence is therefore pushed
forward from `Z` to `X` along the closed immersion `i`, which is exact, and additivity is applied
there; each of the three terms is then read back downstairs by
`AlgebraicGeometry.eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion`, which is
[Stacks, Tag 089W] and the projection formula folded over the exponent vector.  Running the
computation on `Z` instead would need the twist to be transported along an isomorphism of the
twisting *family* — `(i_D)^*i^*𝓛_t` against `(i_D ≫ i)^*𝓛_t` — for which the library has no
comparison, whereas pushing forward only ever moves the sheaf being twisted, which
`AlgebraicGeometry.twistedSheafIsoOfIso` handles.  That is also what makes the third term come
out with the family `(i_D ≫ i)^*𝓛_t` that the consumer asks for, and not a composite of two
pullbacks.

**Why the difference is taken between `n_1 = 0` and `n_1 = -1`.**  This is forced by the
consumer; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Variety/NumericalIntersections/DivisorDifference.lean`.  The
effect here is that the third term of the twisted sequence carries `𝓛_1^{⊗ 0}`, so that
`AlgebraicGeometry.twistedSheafConsZeroIso` removes the first direction outright and leaves the
twist of `𝒪_D` by `𝓛_2, …, 𝓛_{d+1}` — the module whose Euler characteristics define
`(𝓛_2 ⋯ 𝓛_{d+1} · D)`.  The first term, which carries `𝓛_1^{⊗ 0}` on `𝒪_Z(-D)` instead, is
moved to the twist of `𝒪_Z` with first exponent `-1` by
`AlgebraicGeometry.twistedSheafNegativeTwistConsZeroIso`; no cancellation of a tensor factor is
needed, because `AlgebraicGeometry.twistedSheafUpdateIso` and
`AlgebraicGeometry.twistedSheafTensorIso` both produce the *same* sheaf tensored by `𝓛_1`, and
the pairing `𝒪_Z(-D) ⊗ 𝒪_Z(D) ≅ 𝒪_Z` of [Stacks, Tag 01WX] identifies the two bases.

**Local Noetherianity is derived, not assumed.**  The coherence of a direct image along a closed
immersion and the Euler-characteristic comparison across it both ask for
`AlgebraicGeometry.IsLocallyNoetherian X`.  It is not an instance for a scheme proper over a
field, but it is a theorem: `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`, the
locally Noetherian half of [Stacks, Tag 01T6], applies because `Spec k` is locally Noetherian
and a proper morphism is locally of finite type.  So it is discharged inside the proofs and is
not a hypothesis of either statement.

**What is still carried, and why no attribute is attached.**  The only input of
`AlgebraicGeometry.intersectionNumber_eq_intersectionNumber_of_isEffectiveCartierDivisor` beyond
the data of Tag 0BEU is `hfin`, which is [Stacks, Tag 02O6] — finite dimensionality over `k` of
the cohomology of a coherent module on `X`.  It is stated for `X`, and the corresponding
statement for `Z` that the consumer wants is derived from it through
`AlgebraicGeometry.cohomologyOverFieldPushforwardIsoOfIsClosedImmersion`, so that a single
hypothesis suffices.  **No `@[stacks 0BEU]` attribute is attached** for that reason: `hfin` is
not part of the tag's data.  Tag 02O6 *is* proved in this library, as
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`, so `hfin` is dischargeable;
the statement with it discharged, and with the attribute, is
`AlgebraicGeometry.intersectionNumber_eq_of_isEffectiveCartierDivisor` in
`StacksFrontier/AlgebraicGeometry/Variety/NumericalIntersections/DivisorIntersectionProper.lean`.
The dimension bounds `hd` and `hdD` are hypotheses of
`AlgebraicGeometry.intersectionNumber` itself and are part of the tag's data.

**Where the generic twisting lemmas live.**  `AlgebraicGeometry.twistedSheafCongrIso`,
`AlgebraicGeometry.twistList_map_succ`, `AlgebraicGeometry.twistedSheafConsZeroIso` and
`AlgebraicGeometry.SheafOfModules.isCoherent_of_isInvertible` are facts about
`AlgebraicGeometry.twistedSheaf` and about coherence with no reference to divisors, and would sit
as well in `StacksFrontier/AlgebraicGeometry/TwistedSheaf/Basic.lean` and
`StacksFrontier/AlgebraicGeometry/TensorCoherence/Basic.lean`.  They are kept here because this is
their only consumer; a second one should move them.  Following the note in
`TwistedSheaf/Basic.lean`, none of them rewrites inside the type of an isomorphism: the one
object-level equality needed, that the fold over `List.finRange (r + 1)` splits off its head, is
proved separately and applied as `CategoryTheory.eqToIso`.

## References

* [Stacks Project, Tag 0BEU](https://stacks.math.columbia.edu/tag/0BEU)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

open Stacks.SheafOfModules.Invertible
open Stacks.Divisors

/-! ### Generic comparisons of twists -/

section Twists

variable {X : Scheme.{u}} {r : ℕ}

/-- **Equal exponent vectors give isomorphic twists.**  The two twists are in fact equal; the
isomorphism is produced by `AlgebraicGeometry.twistListCongrIso` rather than by `eqToIso` so that
it is the same comparison the rest of the twisting development uses. -/
public def twistedSheafCongrIso (F : X.Modules) (L : Fin r → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L t)] {n₁ n₂ : Fin r → ℤ}
    (h : n₁ = n₂) : twistedSheaf F L n₁ ≅ twistedSheaf F L n₂ :=
  twistListCongrIso L (List.finRange r) (fun t _ => by rw [h]) F

/-- **Reindexing the fold along `Fin.succ`.**  Folding the twist of `𝓜_0, …, 𝓜_r` at the
exponent vector `Fin.cons a e` over the image of a list of indices under `Fin.succ` is folding
the twist of `𝓜_1, …, 𝓜_r` at `e` over that list: the two step functions agree at every index
of the list, so the folds are equal, not merely isomorphic. -/
public theorem twistList_map_succ (M : Fin (r + 1) → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M t)] (a : ℤ)
    (e : Fin r → ℤ) :
    ∀ (l : List (Fin r)) (G : X.Modules),
      twistList M (Fin.cons a e) (l.map Fin.succ) G = twistList (fun t => M t.succ) e l G := by
  intro l
  induction l with
  | nil => intro G; rfl
  | cons t ts ih => intro G; exact ih _

/-- **A twisting direction whose exponent is zero can be dropped.**  For a family
`𝓜_0, …, 𝓜_r` of invertible sheaves of modules,

`ℱ ⊗ 𝓜_0^{⊗ 0} ⊗ 𝓜_1^{⊗ e_1} ⊗ ⋯ ⊗ 𝓜_r^{⊗ e_r} ≅ ℱ ⊗ 𝓜_1^{⊗ e_1} ⊗ ⋯ ⊗ 𝓜_r^{⊗ e_r}`.

The fold over `List.finRange (r + 1)` splits off its head by `List.finRange_succ`, the head
contributes the factor `𝓜_0^{⊗ 0}` which `AlgebraicGeometry.twistListZeroIso` removes, and
`AlgebraicGeometry.twistList_map_succ` reindexes the remaining fold. -/
public def twistedSheafConsZeroIso (F : X.Modules) (M : Fin (r + 1) → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M t)] (e : Fin r → ℤ) :
    twistedSheaf F M (Fin.cons 0 e) ≅ twistedSheaf F (fun t => M t.succ) e :=
  have key : twistedSheaf F M (Fin.cons 0 e) =
      twistedSheaf (twistList M (Fin.cons (0 : ℤ) e) [(0 : Fin (r + 1))] F)
        (fun t => M t.succ) e := by
    change twistList M (Fin.cons 0 e) (List.finRange (r + 1)) F = _
    rw [List.finRange_succ]
    exact twistList_map_succ M 0 e (List.finRange r) _
  eqToIso key ≪≫
    twistedSheafIsoOfIso (fun t => M t.succ)
      (twistListCongrIso M [(0 : Fin (r + 1))] (fun t ht => by
          simp only [List.mem_singleton] at ht
          subst ht
          simp) F ≪≫
        twistListZeroIso M [(0 : Fin (r + 1))] F) e

/-- **An invertible sheaf of modules on a proper scheme over a field is coherent.**  The
structure sheaf is coherent (`Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit`), so its
tensor product with an invertible sheaf is coherent by
`AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible`, and that tensor
product is the invertible sheaf itself. -/
public theorem SheafOfModules.isCoherent_of_isInvertible (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] (A : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A] :
    _root_.SheafOfModules.IsCoherent A :=
  have h1 : _root_.SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  have h2 : _root_.SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
        ((X.toRingedSpace)).IsSheaf⟩).obj ((SheafOfModules.unit X.ringCatSheaf))).obj (A)) :
          X.Modules) :=
    @SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X _ A h1 ‹_›
  @Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso _ _ X.ringCatSheaf A _
    (SheafOfModules.tensorSheafUnitLeftIso X.toRingedSpace A).symm h2

end Twists

/-! ### The ideal sheaf of the divisor as a negative first exponent -/

/-- **Turning the ideal sheaf of an effective Cartier divisor into a negative first exponent.**
Let `D ⊆ Z` be an effective Cartier divisor and let `𝓛_1, …, 𝓛_{d+1}` be invertible
`𝒪_Z`-modules with `𝓛_1 ≅ 𝒪_Z(D)`.  Then

`𝒪_Z(-D) ⊗ 𝓛_1^{⊗ 0} ⊗ 𝓛_2^{⊗ e_2} ⊗ ⋯ ≅ 𝒪_Z ⊗ 𝓛_1^{⊗ -1} ⊗ 𝓛_2^{⊗ e_2} ⊗ ⋯`.

Both sides become the *same* sheaf tensored by `𝓛_1`: the left-hand side by
`AlgebraicGeometry.twistedSheafUpdateIso`, which raises the first exponent from `-1` to `0`, and
the right-hand side by `AlgebraicGeometry.twistedSheafTensorIso`, which carries a factor of
`𝓛_1` on the sheaf being twisted out through the fold — and
`Stacks.Divisors.invertibleSheafPairing'`, which is [Stacks, Tag 01WX], identifies
`𝒪_Z(-D) ⊗ 𝓛_1` with `𝒪_Z`. -/
@[ega "IV 21.2.8" "21.2.8.3, special case"]
public def twistedSheafNegativeTwistConsZeroIso {Z : Scheme.{u}} {d : ℕ} (Dv : Z.IdealSheafData)
    [hDv : IsEffectiveCartierDivisor Dv] (L : Fin (d + 1) → Z.Modules)
    [∀ t, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 (L t)]
    (hL : L 0 ≅ (invertibleSheaf Dv : Z.Modules)) (e : Fin d → ℤ) :
    twistedSheaf (negativeTwist Dv : Z.Modules) L (Fin.cons 0 e) ≅
      twistedSheaf (SheafOfModules.unit Z.ringCatSheaf) L (Fin.cons (-1) e) :=
  have hupd : Function.update (Fin.cons (-1 : ℤ) e : Fin (d + 1) → ℤ) 0
      ((Fin.cons (-1 : ℤ) e : Fin (d + 1) → ℤ) 0 + 1) = Fin.cons 0 e := by
    refine funext fun t => ?_
    refine Fin.cases ?_ (fun l => ?_) t
    · simp
    · simp
  have hNL : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ (Z.presheaf) (forget₂ CommRingCat RingCat)
        (Z.ringCatSheaf.2)⟩).obj ((negativeTwist Dv))).obj ((L 0))) : Z.Modules) ≅
      (SheafOfModules.unit Z.ringCatSheaf : Z.Modules) :=
    tensorProductIso Z.presheaf Z.ringCatSheaf.2 (Iso.refl _) hL ≪≫ invertibleSheafPairing' Dv
  twistedSheafCongrIso _ L hupd.symm ≪≫
    twistedSheafUpdateIso (negativeTwist Dv : Z.Modules) L (Fin.cons (-1) e) 0 ≪≫
    (twistedSheafTensorIso L (negativeTwist Dv : Z.Modules) (Fin.cons (-1) e) 0).symm ≪≫
    twistedSheafIsoOfIso L hNL (Fin.cons (-1) e)

/-! ### The first-difference relation -/

/-- **The first-difference relation of [Stacks, Tag 0BEU].**  Let `k` be a field, let `X` be a
scheme proper over `k`, let `i : Z ⟶ X` be a closed subscheme, let `𝓛_1, …, 𝓛_{d+1}` be
invertible `𝒪_X`-modules and let `D ⊆ Z` be an effective Cartier divisor with
`𝓛_1|_Z ≅ 𝒪_Z(D)`.  Then for every `S ⊆ {2, …, d + 1}`

`χ(Z, ⨂_{t ∈ S} 𝓛_t|_Z) - χ(Z, 𝓛_1^{⊗ -1} ⊗ ⨂_{t ∈ S} 𝓛_t|_Z) = χ(D, ⨂_{t ∈ S} 𝓛_t|_D)`.

This is the hypothesis `hdiff` of
`AlgebraicGeometry.intersectionNumber_eq_of_sub_eulerCharacteristic_eq` and of
`AlgebraicGeometry.intersectionNumber_eq_of_sub_eulerCharacteristic_eq_of_finiteDimensional`, at
the closed immersion `D ⟶ Z ⟶ X` that those statements allow their divisor to be presented by.

The proof is the source's.  The short exact sequence `0 ⟶ 𝒪_Z(-D) ⟶ 𝒪_Z ⟶ 𝒪_D ⟶ 0` of
[Stacks, Tag 0C6K] is pushed forward to `X`, where it stays short exact because `i_*` is exact
along a closed immersion, and additivity of the Euler characteristic on twists
(`AlgebraicGeometry.eulerCharacteristic_twistedSheaf_add_of_shortExact`, which is where `hfin`
enters) is applied to it at the exponent vector `(0, 1_S)`.  Its three terms are then read back
downstairs by
`AlgebraicGeometry.eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion`; the first
becomes the twist with first exponent `-1` by
`AlgebraicGeometry.twistedSheafNegativeTwistConsZeroIso`, and the third loses its first twisting
direction by `AlgebraicGeometry.twistedSheafConsZeroIso`.

The hypothesis `hfin` is [Stacks, Tag 02O6]; it is the only one that is not part of Tag 0BEU's
data, so no attribute is attached. -/
public theorem eulerCharacteristic_twistedSheaf_unit_sub_eq_of_isEffectiveCartierDivisor
    (k : Type u) [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ) (L : Fin (d + 1) → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L t)]
    (Dv : Z.IdealSheafData) [hDv : IsEffectiveCartierDivisor Dv]
    (hL : (Scheme.Modules.pullback i).obj (L 0) ≅ (invertibleSheaf Dv : Z.Modules))
    (hfin : ∀ G : X.Modules, _root_.SheafOfModules.IsCoherent G →
      ∀ m : ℕ, FiniteDimensional k (cohomologyOverField k f G m))
    (S : Finset (Fin d)) :
    (@eulerCharacteristic k _ Z (i ≫ f) inferInstance
        (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun t => (Scheme.Modules.pullback i).obj (L t))
          (Fin.cons 0 fun t => if t ∈ S then 1 else 0))
        (isCoherent_twistedSheafUnitPullback k f i L
          (Fin.cons 0 fun t => if t ∈ S then 1 else 0)) : ℤ) -
      (@eulerCharacteristic k _ Z (i ≫ f) inferInstance
        (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun t => (Scheme.Modules.pullback i).obj (L t))
          (Fin.cons (-1) fun t => if t ∈ S then 1 else 0))
        (isCoherent_twistedSheafUnitPullback k f i L
          (Fin.cons (-1) fun t => if t ∈ S then 1 else 0)) : ℤ) =
    (@eulerCharacteristic k _ Dv.subscheme ((Dv.subschemeι ≫ i) ≫ f) inferInstance
      (twistedSheaf (SheafOfModules.unit Dv.subscheme.ringCatSheaf)
        (fun t : Fin d => (Scheme.Modules.pullback (Dv.subschemeι ≫ i)).obj (L t.succ))
        (fun t => if t ∈ S then 1 else 0))
      (isCoherent_twistedSheafUnitPullback k f (Dv.subschemeι ≫ i)
        (fun t : Fin d => L t.succ) fun t => if t ∈ S then 1 else 0) : ℤ) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hinvZ : ∀ t, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      ((Scheme.Modules.pullback i).obj (L t)) :=
    fun t => SheafOfModules.isInvertible_pullback i (L t)
  have hinvW : ∀ t, SheafOfModules.IsInvertible Dv.subscheme.presheaf
      Dv.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (Dv.subschemeι ≫ i)).obj (L t)) :=
    fun t => SheafOfModules.isInvertible_pullback _ (L t)
  -- the divisor short exact sequence on `Z`, pushed forward to `X`
  let Sq : ShortComplex Z.Modules :=
    ShortComplex.mk (C := Z.Modules) (Stacks.IdealSheafSequence.divisorIdealMap Dv)
      (Stacks.IdealSheafSequence.divisorQuotientMap Dv)
      (Stacks.IdealSheafSequence.divisorIdeal_shortExact Dv).choose
  have hSq : Sq.ShortExact := (Stacks.IdealSheafSequence.divisorIdeal_shortExact Dv).choose_spec
  let T : ShortComplex X.Modules := Sq.map (Scheme.Modules.pushforward i)
  have hT : T.ShortExact := ShortComplex.ShortExact.map_of_exact hSq _
  -- coherence of the three terms upstairs
  have cOZ : _root_.SheafOfModules.IsCoherent (SheafOfModules.unit Z.ringCatSheaf : Z.Modules) :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f)
  have cOW : _root_.SheafOfModules.IsCoherent
      (SheafOfModules.unit Dv.subscheme.ringCatSheaf : Dv.subscheme.Modules) :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k ((Dv.subschemeι ≫ i) ≫ f)
  have cN : _root_.SheafOfModules.IsCoherent (negativeTwist Dv : Z.Modules) :=
    @SheafOfModules.isCoherent_of_isInvertible Z k _ (i ≫ f) _ _ hDv
  have cT1 : _root_.SheafOfModules.IsCoherent T.X₁ :=
    @isCoherent_pushforward_of_isClosedImmersion Z X i _ _ _ cN
  have cT2 : _root_.SheafOfModules.IsCoherent T.X₂ :=
    @isCoherent_pushforward_of_isClosedImmersion Z X i _ _ _ cOZ
  have cjW : _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward (Dv.subschemeι ≫ i)).obj
        (SheafOfModules.unit Dv.subscheme.ringCatSheaf) : X.Modules) :=
    @isCoherent_pushforward_of_isClosedImmersion Dv.subscheme X (Dv.subschemeι ≫ i) _ _ _ cOW
  have ecomp : T.X₃ ≅ (Scheme.Modules.pushforward (Dv.subschemeι ≫ i)).obj
      (SheafOfModules.unit Dv.subscheme.ringCatSheaf) :=
    (Scheme.Modules.pushforwardComp Dv.subschemeι i).app _
  have cT3 : _root_.SheafOfModules.IsCoherent T.X₃ :=
    @Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso _ _ X.ringCatSheaf _ _
      ecomp cjW
  have hadd := eulerCharacteristic_twistedSheaf_add_of_shortExact k f L hfin hT cT1 cT2 cT3
    (Fin.cons 0 fun t => if t ∈ S then (1 : ℤ) else 0)
  -- coherence of the individual twists
  have cZ0 : _root_.SheafOfModules.IsCoherent
      (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
        (fun t => (Scheme.Modules.pullback i).obj (L t))
        (Fin.cons 0 fun t => if t ∈ S then (1 : ℤ) else 0)) :=
    isCoherent_twistedSheafUnitPullback k f i L (Fin.cons 0 fun t => if t ∈ S then 1 else 0)
  have cZm : _root_.SheafOfModules.IsCoherent
      (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
        (fun t => (Scheme.Modules.pullback i).obj (L t))
        (Fin.cons (-1) fun t => if t ∈ S then (1 : ℤ) else 0)) :=
    isCoherent_twistedSheafUnitPullback k f i L (Fin.cons (-1) fun t => if t ∈ S then 1 else 0)
  have cZN : _root_.SheafOfModules.IsCoherent
      (twistedSheaf (negativeTwist Dv : Z.Modules)
        (fun t => (Scheme.Modules.pullback i).obj (L t))
        (Fin.cons 0 fun t => if t ∈ S then (1 : ℤ) else 0)) :=
    @twistedSheaf_isCoherent Z (d + 1) _ _ hinvZ cN _
  have cW0 : _root_.SheafOfModules.IsCoherent
      (twistedSheaf (SheafOfModules.unit Dv.subscheme.ringCatSheaf)
        (fun t => (Scheme.Modules.pullback (Dv.subschemeι ≫ i)).obj (L t))
        (Fin.cons 0 fun t => if t ∈ S then (1 : ℤ) else 0)) :=
    isCoherent_twistedSheafUnitPullback k f (Dv.subschemeι ≫ i) L
      (Fin.cons 0 fun t => if t ∈ S then 1 else 0)
  have cWf : _root_.SheafOfModules.IsCoherent
      (twistedSheaf (SheafOfModules.unit Dv.subscheme.ringCatSheaf)
        (fun t : Fin d => (Scheme.Modules.pullback (Dv.subschemeι ≫ i)).obj (L t.succ))
        (fun t => if t ∈ S then (1 : ℤ) else 0)) :=
    isCoherent_twistedSheafUnitPullback k f (Dv.subschemeι ≫ i) (fun t : Fin d => L t.succ)
      (fun t => if t ∈ S then 1 else 0)
  have cXjW : _root_.SheafOfModules.IsCoherent
      (twistedSheaf ((Scheme.Modules.pushforward (Dv.subschemeι ≫ i)).obj
          (SheafOfModules.unit Dv.subscheme.ringCatSheaf) : X.Modules) L
        (Fin.cons 0 fun t => if t ∈ S then (1 : ℤ) else 0)) :=
    @twistedSheaf_isCoherent X (d + 1) _ L _ cjW _
  -- the middle term is read on `Z`
  have hmid : (@eulerCharacteristic k _ X f _ (twistedSheaf T.X₂ L
        (Fin.cons 0 fun t => if t ∈ S then (1 : ℤ) else 0))
        (@twistedSheaf_isCoherent X (d + 1) T.X₂ L _ cT2 _) : ℤ) =
      @eulerCharacteristic k _ Z (i ≫ f) _
        (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun t => (Scheme.Modules.pullback i).obj (L t))
          (Fin.cons 0 fun t => if t ∈ S then (1 : ℤ) else 0)) cZ0 :=
    @eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion k _ Z X i f _ _ _
      (d + 1) L _ hinvZ (SheafOfModules.unit Z.ringCatSheaf)
      (Fin.cons 0 fun t => if t ∈ S then (1 : ℤ) else 0)
      (@twistedSheaf_isCoherent X (d + 1) T.X₂ L _ cT2 _) cZ0
  -- the first term is read on `Z`, then becomes the twist with first exponent `-1`
  have hfirst : (@eulerCharacteristic k _ X f _ (twistedSheaf T.X₁ L
        (Fin.cons 0 fun t => if t ∈ S then (1 : ℤ) else 0))
        (@twistedSheaf_isCoherent X (d + 1) T.X₁ L _ cT1 _) : ℤ) =
      @eulerCharacteristic k _ Z (i ≫ f) _
        (twistedSheaf (negativeTwist Dv : Z.Modules)
          (fun t => (Scheme.Modules.pullback i).obj (L t))
          (Fin.cons 0 fun t => if t ∈ S then (1 : ℤ) else 0)) cZN :=
    @eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion k _ Z X i f _ _ _
      (d + 1) L _ hinvZ (negativeTwist Dv) (Fin.cons 0 fun t => if t ∈ S then (1 : ℤ) else 0)
      (@twistedSheaf_isCoherent X (d + 1) T.X₁ L _ cT1 _) cZN
  have hneg : (@eulerCharacteristic k _ Z (i ≫ f) _
        (twistedSheaf (negativeTwist Dv : Z.Modules)
          (fun t => (Scheme.Modules.pullback i).obj (L t))
          (Fin.cons 0 fun t => if t ∈ S then (1 : ℤ) else 0)) cZN : ℤ) =
      @eulerCharacteristic k _ Z (i ≫ f) _
        (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun t => (Scheme.Modules.pullback i).obj (L t))
          (Fin.cons (-1) fun t => if t ∈ S then (1 : ℤ) else 0)) cZm :=
    @eulerCharacteristic_eq_of_iso k _ Z (i ≫ f) _ _ _ cZN cZm
      (@twistedSheafNegativeTwistConsZeroIso Z d Dv hDv
        (fun t => (Scheme.Modules.pullback i).obj (L t)) hinvZ hL
        fun t => if t ∈ S then 1 else 0)
  -- the third term is read on the divisor, and loses its first twisting direction
  have hthird : (@eulerCharacteristic k _ X f _ (twistedSheaf T.X₃ L
        (Fin.cons 0 fun t => if t ∈ S then (1 : ℤ) else 0))
        (@twistedSheaf_isCoherent X (d + 1) T.X₃ L _ cT3 _) : ℤ) =
      @eulerCharacteristic k _ X f _
        (twistedSheaf ((Scheme.Modules.pushforward (Dv.subschemeι ≫ i)).obj
            (SheafOfModules.unit Dv.subscheme.ringCatSheaf) : X.Modules) L
          (Fin.cons 0 fun t => if t ∈ S then (1 : ℤ) else 0)) cXjW :=
    @eulerCharacteristic_eq_of_iso k _ X f _ _ _
      (@twistedSheaf_isCoherent X (d + 1) T.X₃ L _ cT3 _) cXjW
      (twistedSheafIsoOfIso L ecomp (Fin.cons 0 fun t => if t ∈ S then (1 : ℤ) else 0))
  have hdown3 : (@eulerCharacteristic k _ X f _
        (twistedSheaf ((Scheme.Modules.pushforward (Dv.subschemeι ≫ i)).obj
            (SheafOfModules.unit Dv.subscheme.ringCatSheaf) : X.Modules) L
          (Fin.cons 0 fun t => if t ∈ S then (1 : ℤ) else 0)) cXjW : ℤ) =
      @eulerCharacteristic k _ Dv.subscheme ((Dv.subschemeι ≫ i) ≫ f) _
        (twistedSheaf (SheafOfModules.unit Dv.subscheme.ringCatSheaf)
          (fun t => (Scheme.Modules.pullback (Dv.subschemeι ≫ i)).obj (L t))
          (Fin.cons 0 fun t => if t ∈ S then (1 : ℤ) else 0)) cW0 :=
    @eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion k _ Dv.subscheme X
      (Dv.subschemeι ≫ i) f _ _ _ (d + 1) L _ hinvW
      (SheafOfModules.unit Dv.subscheme.ringCatSheaf)
      (Fin.cons 0 fun t => if t ∈ S then (1 : ℤ) else 0) cXjW cW0
  have hdrop : (@eulerCharacteristic k _ Dv.subscheme ((Dv.subschemeι ≫ i) ≫ f) _
        (twistedSheaf (SheafOfModules.unit Dv.subscheme.ringCatSheaf)
          (fun t => (Scheme.Modules.pullback (Dv.subschemeι ≫ i)).obj (L t))
          (Fin.cons 0 fun t => if t ∈ S then (1 : ℤ) else 0)) cW0 : ℤ) =
      @eulerCharacteristic k _ Dv.subscheme ((Dv.subschemeι ≫ i) ≫ f) _
        (twistedSheaf (SheafOfModules.unit Dv.subscheme.ringCatSheaf)
          (fun t : Fin d => (Scheme.Modules.pullback (Dv.subschemeι ≫ i)).obj (L t.succ))
          (fun t => if t ∈ S then (1 : ℤ) else 0)) cWf :=
    @eulerCharacteristic_eq_of_iso k _ Dv.subscheme ((Dv.subschemeι ≫ i) ≫ f) _ _ _ cW0 cWf
      (@twistedSheafConsZeroIso Dv.subscheme d (SheafOfModules.unit Dv.subscheme.ringCatSheaf)
        (fun t => (Scheme.Modules.pullback (Dv.subschemeι ≫ i)).obj (L t)) hinvW
        fun t => if t ∈ S then 1 else 0)
  rw [hmid, hfirst, hneg, hthird, hdown3, hdrop] at hadd
  omega

/-! ### Tag 0BEU -/

/-- **[Stacks, Tag 0BEU], with [Stacks, Tag 02O6] carried.**  Let `k` be a field, let `X` be a
scheme proper over `k`, let `i : Z ⟶ X` be a closed subscheme of dimension at most `d + 1` and
let `𝓛_1, …, 𝓛_{d+1}` be invertible `𝒪_X`-modules.  Let `D ⊆ Z` be an effective Cartier divisor
of dimension at most `d` with `𝓛_1|_Z ≅ 𝒪_Z(D)`.  Then

`(𝓛_1 ⋯ 𝓛_{d+1} · Z) = (𝓛_2 ⋯ 𝓛_{d+1} · D)`,

the intersection number of the divisor being taken along the composite closed immersion
`D ⟶ Z ⟶ X`.

This is
`AlgebraicGeometry.intersectionNumber_eq_of_sub_eulerCharacteristic_eq_of_finiteDimensional` with
its first-difference hypothesis discharged by
`AlgebraicGeometry.eulerCharacteristic_twistedSheaf_unit_sub_eq_of_isEffectiveCartierDivisor`.
That statement asks for finite dimensionality of the cohomology of the coherent modules on `Z`;
it is derived here from the same statement on `X` through
`AlgebraicGeometry.cohomologyOverFieldPushforwardIsoOfIsClosedImmersion`, so that the single
hypothesis `hfin` — [Stacks, Tag 02O6] for `X` — covers both.

**No `@[stacks 0BEU]` attribute is attached**: `hfin` is Tag 02O6, which is not part of
Tag 0BEU's data.  Everything else the tag needs is proved here: the divisor sequence, its
additivity and the numerical argument.  Tag 02O6 is proved in this library too, so `hfin` is
discharged in
`StacksFrontier/AlgebraicGeometry/Variety/NumericalIntersections/DivisorIntersectionProper.lean`,
and the attribute sits on
`AlgebraicGeometry.intersectionNumber_eq_of_isEffectiveCartierDivisor` there. -/
public theorem intersectionNumber_eq_intersectionNumber_of_isEffectiveCartierDivisor
    (k : Type u) [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Z ≤ (d + 1 : ℕ)) (L : Fin (d + 1) → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L t)]
    (Dv : Z.IdealSheafData) [hDv : IsEffectiveCartierDivisor Dv]
    (hdD : topologicalKrullDim Dv.subscheme ≤ d)
    (hL : (Scheme.Modules.pullback i).obj (L 0) ≅ (invertibleSheaf Dv : Z.Modules))
    (hfin : ∀ G : X.Modules, _root_.SheafOfModules.IsCoherent G →
      ∀ m : ℕ, FiniteDimensional k (cohomologyOverField k f G m)) :
    intersectionNumber k f i (d + 1) hd L =
      intersectionNumber k f (Dv.subschemeι ≫ i) d hdD fun t : Fin d => L t.succ := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine intersectionNumber_eq_of_sub_eulerCharacteristic_eq_of_finiteDimensional k f i
    (Dv.subschemeι ≫ i) d hd hdD L (fun G hG m => ?_) fun S =>
      eulerCharacteristic_twistedSheaf_unit_sub_eq_of_isEffectiveCartierDivisor k f i d L Dv hL
        hfin S
  have hpush : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward i).obj G) :=
    @isCoherent_pushforward_of_isClosedImmersion Z X i _ _ _ hG
  have := hfin _ hpush m
  exact (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k i f G m).symm.toLinearEquiv
    |>.finiteDimensional

end AlgebraicGeometry

end
