module

public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Meromorphic.RegularSectionExistence
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticSupport.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Abelian
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward

/-!
# The twist of a direct image along a closed immersion

Let `i : Z ⟶ X` be a closed immersion of schemes, `𝒢` a sheaf of modules on `Z` and
`𝓛_1, …, 𝓛_r` invertible sheaves of modules on `X`. This file identifies the twist of the
direct image with the direct image of the twist,

`(i_*𝒢) ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r} ≅ i_*(𝒢 ⊗ (i^*𝓛_1)^{⊗ n_1} ⊗ ⋯ ⊗ (i^*𝓛_r)^{⊗ n_r})`,

for an arbitrary integer exponent vector, and shows that the three measures the induction of
[Stacks, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM) descends on — the support, its
dimension `AlgebraicGeometry.natDimSupp`, and nowhere density inside the support — are unchanged
by `i_*`.

Together these are what carries the inductive step of Tag 0BEM between a scheme and the closed
subscheme supplied by [Stacks, Tag 02OM]: the step is run downstairs, where the sheaf has full
support and [Stacks, Tag 02OZ] and [Stacks, Tag 02P2] apply, and its conclusion is read upstairs.

## The two halves

The unfolded case — one twisting factor, no exponent — is the projection formula for a
closed immersion, `Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso` (the
`X.Modules` spelling of `Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso`).
Folding it over the exponent vector is then an induction over the list of indices which
`AlgebraicGeometry.twistListIso` already carries, and costs nothing beyond it.

What the fold needs at each index is the comparison

`f^*(𝓛^{⊗ n}) ≅ (f^*𝓛)^{⊗ n}` for `n : ℤ`.

`AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso` is this comparison for `n : ℕ` only,
by a recursion whose successor step is [Stacks, Tag 01CD]; the exponents of Tag 0BEM are
integers. The negative half is obtained here by *cancellation* rather than by recursion:
tensoring on the right by an invertible sheaf is an equivalence
(`Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence`), hence full and faithful,
so `AlgebraicGeometry.SheafOfModules.cancelTensorRightIso` turns an isomorphism of the two
sheaves tensored by `f^*𝓛` into an isomorphism of the two sheaves — and tensoring the comparison
at `n + 1` by `f^*𝓛` *is* such an isomorphism, by Tag 01CD and the successor comparison of
[Stacks, Tag 01CU]. The two steps then drive `Int.induction_on` in both directions from the
exponent `0`, where the comparison is `f^*𝒪_X ≅ 𝒪_Z`.

## Main definitions

The elided prefix is `AlgebraicGeometry`.

* `SheafOfModules.cancelTensorRightIso`: tensoring on the right by an invertible sheaf reflects
  isomorphisms.
* `Scheme.Modules.pullbackTensorPowerIntIso`: `f^*(𝓛^{⊗ n}) ≅ (f^*𝓛)^{⊗ n}` for `n : ℤ`.
* `pushforwardTwistListIso`: the projection formula folded over a list of twisting indices.
* `pushforwardTwistedSheafIso`: **the twist of a direct image is the direct image of the
  twist.**
* `suppPushforwardHomeomorph`: `Supp 𝒢` and `Supp (i_*𝒢)` are homeomorphic.

## Main results

* `Homeomorph.isNowhereDense_image_iff`: nowhere density is a homeomorphism invariant.
* `SheafOfModules.isInvertible_pullback`: the pullback of an invertible sheaf of modules is
  invertible, at the `AlgebraicGeometry.SheafOfModules.IsInvertible` spelling.
* `mem_supp_pushforward_iff`: `i(z) ∈ Supp (i_*𝒢) ↔ z ∈ Supp 𝒢`.
* `notMem_supp_pushforward_of_notMemRange`: `i_*𝒢` is supported on the image of `i`.
* `supp_pushforward_of_isClosedImmersion`: `Supp (i_*𝒢) = i(Supp 𝒢)`.
* `topologicalKrullDim_supp_pushforward_of_isClosedImmersion` and
  `natDimSupp_pushforward_of_isClosedImmersion`: the dimension of the support is unchanged.
* `isNowhereDense_preimage_val_supp_pushforward_iff`: nowhere density of `Supp 𝒢₁` inside
  `Supp 𝒢` is unchanged by `i_*`.
* `eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion`:
  `χ(X, (i_*𝒩) ⊗ 𝓜^{⊗ n}) = χ(Z, 𝒩 ⊗ (i^*𝓜)^{⊗ n})`. This is the form the inductive step of
  Tag 0BEM consumes: the fold above composed with
  `AlgebraicGeometry.eulerCharacteristic_pushforward_of_isClosedImmersion`.
* `exists_isRegularMeromorphicSection_pullback_subscheme_annihilatorIdeal`: [Stacks, Tag 02OZ]
  case (3) **on the scheme-theoretic support of [Stacks, Tag 02OM]**, which is the other input
  the step needs there — see below.

## The regular meromorphic section downstairs

`AlgebraicGeometry.exists_differenceSequences_of_supp_eq_univ`, which supplies the two
difference sequences on the subscheme, takes a meromorphic section and its regularity as
*explicit arguments*; and the invertible sheaf there is `i^*𝓛`, not `𝓛`. Both are available:

* `AlgebraicGeometry.exists_isCoherent_pushforward_iso_of_hasNoEmbeddedAssociatedPoints`
  (Tag 02OM) returns `HasNoEmbeddedPoints (annihilatorIdeal F).subscheme` as its *first*
  conjunct, and a closed subscheme of a locally Noetherian scheme is locally Noetherian, so
  [Stacks, Tag 02OZ] case (3)
  (`AlgebraicGeometry.exists_isRegularMeromorphicSection_of_hasNoEmbeddedPoints`) applies there
  verbatim;
* `i^*𝓛` is invertible by `AlgebraicGeometry.SheafOfModules.isInvertible_pullback` above.

`exists_isRegularMeromorphicSection_pullback_subscheme_annihilatorIdeal` is the two put together.
Nothing further is owed on that route.

## Implementation notes

**Which `IsInvertible`, and why the pullback statement is restated.** The repository carries two
invertibility predicates with the same body,
`AlgebraicGeometry.SheafOfModules.IsInvertible` and `Stacks.SheafOfModules.IsInvertible`, with
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry` between them.
`Stacks.Modules.isInvertible_pullback` is stated at the second, while
`AlgebraicGeometry.twistedSheaf` and `AlgebraicGeometry.tensorPower` ask for the first, so the
pullback of a twisting sheaf is not a twisting sheaf until the equivalence is applied twice.
`SheafOfModules.isInvertible_pullback` below is that composite. It is deliberately **not** an
instance: the existing instance form `Stacks.Modules.instIsInvertiblePullbackObj` is at the other
predicate, and an instance whose subject is `(Scheme.Modules.pullback f).obj L` with `f` free is
a search hazard this file has no need to create. Consumers bind it with `have`.

**Why the equivalence of the native right-tensor functor is applied, not synthesized.**
`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, while
`Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence` is stated for
`SheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)`. The two are
  definitionally equal, but instance
search is syntactic and does not cross the gap: `inferInstance` for
`((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).flip.obj L).IsEquivalence` fails even with the
invertibility of `L` in scope at *either* predicate, whereas the
same instance *applied* — `tensorRightFunctor_isEquivalence X.presheaf X.ringCatSheaf.2 L` — is
accepted, which is the documented behaviour that an application crosses a spelling gap where an
instance binder does not. `Full` and `Faithful` are then taken off it by projection and are local
instances, which is all `CategoryTheory.Functor.preimageIso` needs.

**Why the integer comparison is `Nonempty`-then-`.some`.** `Int.induction_on` eliminates into
`Prop`, so the two-sided induction is run on `Nonempty (… ≅ …)` and the isomorphism is extracted
afterwards. A `Int.rec` recursion producing the isomorphism directly would have to transport
across `((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1` and `Int.negSucc k = -((k + 1 : ℕ) : ℤ)` at every step,
by `Stacks.SheafOfModules.Invertible.tensorPowerReindex` on both sides; running the induction in
`Prop` removes all of it, at the cost of `Classical.choice`. Nothing
downstream needs an equation for the comparison — it is consumed only as data, inside
`AlgebraicGeometry.twistListIso`.

**No new fold.** `AlgebraicGeometry.twistList` of
`StacksFrontier/AlgebraicGeometry/TwistedSheaf/Basic.lean` is the fold the statements below
induct over, and `AlgebraicGeometry.twistedSheaf F L n` is `twistList L n (List.finRange r) F` on
the nose, so `pushforwardTwistedSheafIso` is `pushforwardTwistListIso` at
`List.finRange r` with no comparison in between.

**The support statements are in term mode on purpose.**
`SheafOfModules.mem_supp_iff_nontrivial_stalk` has the sheaf of rings implicit, so
`rw [SheafOfModules.mem_supp_iff_nontrivial_stalk]` against a goal mentioning `X.Modules` fails
with *"the target expression is not type-correct under the `implicit` transparency level"* —
in all three directions of `supp_pushforward_of_isClosedImmersion`. Applying the
iff to its sheaf argument and composing with `Iff.trans` forms no motive and goes through.

**No attribute is attached.** [Stacks, Tag 01E8] is the projection formula, whose
closed-immersion case is
`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso`; nothing here states a
clause of it, the fold being a statement about the iterated tensor product of
`AlgebraicGeometry.twistedSheaf`, which is this repository's definition and not the source's
notation. [Stacks, Tag 01CD] is already attached where it is proved, and
`Scheme.Modules.pullbackTensorPowerIntIso` is not a clause of [Stacks, Tag 01CU] either — that
tag's clauses are about the tensor powers on one scheme. The support statements are not the
statement of a tag.

## References

* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 02OM](https://stacks.math.columbia.edu/tag/02OM)
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

universe u

/-- **Nowhere density is a homeomorphism invariant.** A homeomorphism commutes with `closure`
and with `interior`, and an image is empty exactly when the set is. -/
theorem Homeomorph.isNowhereDense_image_iff {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (s : Set A) :
    IsNowhereDense (e '' s) ↔ IsNowhereDense s := by
  unfold IsNowhereDense
  rw [← e.image_closure, ← e.image_interior, Set.image_eq_empty]

namespace AlgebraicGeometry

open Stacks.SheafOfModules.Invertible

/-! ### Cancelling a tensor factor, and the integer tensor powers of a pullback -/

/-- **Tensoring on the right by an invertible sheaf of modules reflects isomorphisms.** Right
tensoring by an invertible sheaf is an equivalence
(`Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence`), hence full and faithful,
and a full and faithful functor reflects isomorphisms of objects. -/
def SheafOfModules.cancelTensorRightIso {X : Scheme.{u}} (A : X.Modules)
    [hA : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A] {M N : X.Modules}
    (e : ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
            (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj M).obj A ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
            (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj N).obj A) :
    M ≅ N :=
  have hE : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj
      A).IsEquivalence :=
    tensorRightFunctor_isEquivalence X.presheaf X.ringCatSheaf.2 A
  have := hE.full
  have := hE.faithful
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj A).preimageIso
    (X := M) (Y := N) e

/-- **The pullback of an invertible sheaf of modules is invertible**, at the
`AlgebraicGeometry.SheafOfModules.IsInvertible` spelling that `AlgebraicGeometry.tensorPower` and
`AlgebraicGeometry.twistedSheaf` ask for. This is `Stacks.Modules.isInvertible_pullback`
conjugated by `Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`. -/
theorem SheafOfModules.isInvertible_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Scheme.Modules.pullback f).obj L) :=
  have _ : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hL
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
    (Stacks.Modules.isInvertible_pullback f L)

namespace Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
  [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
  [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
    ((Scheme.Modules.pullback f).obj L)]

/-- The comparison `f^*(𝓛^{⊗ n}) ≅ (f^*𝓛)^{⊗ n}` at `n = 0`: both tensor powers are the
structure sheaf by `Stacks.SheafOfModules.Invertible.tensorPower_zero`, so this is
`f^*𝒪_Y ≅ 𝒪_X`. -/
def pullbackTensorPowerZeroIso :
    (Scheme.Modules.pullback f).obj (tensorPower Y.presheaf Y.ringCatSheaf.2 L 0) ≅
      tensorPower X.presheaf X.ringCatSheaf.2 ((Scheme.Modules.pullback f).obj L) 0 :=
  AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f

/-- The step of `AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIntIso` upwards, at an
arbitrary integer exponent: split the extra factor off by
`Stacks.SheafOfModules.Invertible.tensorPowerSuccIso`, distribute the pullback over the tensor
product by [Stacks, Tag 01CD], apply the comparison at `n` in the first factor, and reassemble.

This is the successor step of
`AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso` with its exponent an integer rather
than a natural number; nothing in it used nonnegativity. -/
def pullbackTensorPowerSuccStep (n : ℤ)
    (φ : (Scheme.Modules.pullback f).obj (tensorPower Y.presheaf Y.ringCatSheaf.2 L n) ≅
      tensorPower X.presheaf X.ringCatSheaf.2 ((Scheme.Modules.pullback f).obj L) n) :
    (Scheme.Modules.pullback f).obj (tensorPower Y.presheaf Y.ringCatSheaf.2 L (n + 1)) ≅
      tensorPower X.presheaf X.ringCatSheaf.2 ((Scheme.Modules.pullback f).obj L) (n + 1) :=
  (Scheme.Modules.pullback f).mapIso
      (tensorPowerSuccIso Y.presheaf Y.ringCatSheaf.2 L n).symm ≪≫
    Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f _ L ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj
      ((Scheme.Modules.pullback f).obj L)).mapIso φ ≪≫
    tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 ((Scheme.Modules.pullback f).obj L) n

/-- The step of `AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIntIso` downwards. There is
no recursion available here — the negative tensor powers are iterates of the *quasi-inverse* of
right tensoring, which the pullback has no reason to commute with — so the step is taken by
cancellation instead: both sides tensored by `f^*𝓛` become the two sides of the comparison at
`n + 1`, by [Stacks, Tag 01CD] and
`Stacks.SheafOfModules.Invertible.tensorPowerSuccIso`, and
`AlgebraicGeometry.SheafOfModules.cancelTensorRightIso` removes the factor. -/
def pullbackTensorPowerPredStep (n : ℤ)
    (φ : (Scheme.Modules.pullback f).obj (tensorPower Y.presheaf Y.ringCatSheaf.2 L (n + 1)) ≅
      tensorPower X.presheaf X.ringCatSheaf.2 ((Scheme.Modules.pullback f).obj L) (n + 1)) :
    (Scheme.Modules.pullback f).obj (tensorPower Y.presheaf Y.ringCatSheaf.2 L n) ≅
      tensorPower X.presheaf X.ringCatSheaf.2 ((Scheme.Modules.pullback f).obj L) n :=
  SheafOfModules.cancelTensorRightIso ((Scheme.Modules.pullback f).obj L)
    ((Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
          (tensorPower Y.presheaf Y.ringCatSheaf.2 L n) L).symm ≪≫
      (Scheme.Modules.pullback f).mapIso
        (tensorPowerSuccIso Y.presheaf Y.ringCatSheaf.2 L n) ≪≫ φ ≪≫
      (tensorPowerSuccIso X.presheaf X.ringCatSheaf.2
        ((Scheme.Modules.pullback f).obj L) n).symm)

/-- **The pullback of an integer tensor power of an invertible sheaf of modules is that tensor
power of its pullback**, in the existential form `Int.induction_on` produces. The two steps are
`pullbackTensorPowerSuccStep` and `pullbackTensorPowerPredStep`, and the base point is the
exponent `0`. -/
theorem nonempty_pullbackTensorPowerIntIso (n : ℤ) :
    Nonempty ((Scheme.Modules.pullback f).obj
        (tensorPower Y.presheaf Y.ringCatSheaf.2 L n) ≅
      tensorPower X.presheaf X.ringCatSheaf.2 ((Scheme.Modules.pullback f).obj L) n) := by
  induction n using Int.induction_on with
  | zero => exact ⟨pullbackTensorPowerZeroIso f L⟩
  | succ k ih => exact ⟨pullbackTensorPowerSuccStep f L (k : ℤ) ih.some⟩
  | pred k ih =>
      have h : (-(k : ℤ) - 1) + 1 = -(k : ℤ) := by ring
      exact ⟨pullbackTensorPowerPredStep f L (-(k : ℤ) - 1)
        ((Scheme.Modules.pullback f).mapIso
            (tensorPowerReindex Y.presheaf Y.ringCatSheaf.2 L h) ≪≫ ih.some ≪≫
          tensorPowerReindex X.presheaf X.ringCatSheaf.2
            ((Scheme.Modules.pullback f).obj L) h.symm)⟩

/-- **`f^*(𝓛^{⊗ n}) ≅ (f^*𝓛)^{⊗ n}` for an arbitrary integer exponent.** This is
`AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso` with its exponent in `ℤ` rather than
`ℕ`; see the module docstring for why it is obtained from the `Nonempty` form. -/
def pullbackTensorPowerIntIso (n : ℤ) :
    (Scheme.Modules.pullback f).obj (tensorPower Y.presheaf Y.ringCatSheaf.2 L n) ≅
      tensorPower X.presheaf X.ringCatSheaf.2 ((Scheme.Modules.pullback f).obj L) n :=
  (nonempty_pullbackTensorPowerIntIso f L n).some

end Scheme.Modules

/-! ### The projection formula folded over the exponent vector -/

section Fold

variable {Z X : Scheme.{u}} {r : ℕ} (i : Z ⟶ X) [IsClosedImmersion i]
  (M : Fin r → X.Modules)
  [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j)]
  [∀ j, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
    ((Scheme.Modules.pullback i).obj (M j))]

/-- **The projection formula for a closed immersion, folded over a list of twisting indices.**
At the head of the list
`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso` moves the factor
`𝓜_j^{⊗ e_j}` inside the direct image as `i^*(𝓜_j^{⊗ e_j})`,
`AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIntIso` rewrites that as `(i^*𝓜_j)^{⊗ e_j}`,
and `AlgebraicGeometry.twistListIso` carries the resulting isomorphism through the remaining
factors, where the inductive hypothesis applies. -/
def pushforwardTwistListIso (e : Fin r → ℤ) :
    ∀ (l : List (Fin r)) (N : Z.Modules),
      twistList M e l ((Scheme.Modules.pushforward i).obj N) ≅
        (Scheme.Modules.pushforward i).obj
          (twistList (fun j => (Scheme.Modules.pullback i).obj (M j)) e l N) := by
  intro l
  induction l with
  | nil => exact fun _ => Iso.refl _
  | cons j t ih =>
    exact fun N =>
      twistListIso M e t
          (Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso i N
              (tensorPower X.presheaf X.ringCatSheaf.2 (M j) (e j)) ≪≫
            (Scheme.Modules.pushforward i).mapIso
              (tensorProductIso Z.presheaf Z.ringCatSheaf.2 (Iso.refl N)
                (Scheme.Modules.pullbackTensorPowerIntIso i (M j) (e j)))) ≪≫
        ih _

/-- **The twist of a direct image along a closed immersion is the direct image of the twist**:

`(i_*𝒩) ⊗ 𝓜_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓜_r^{⊗ n_r} ≅ i_*(𝒩 ⊗ (i^*𝓜_1)^{⊗ n_1} ⊗ ⋯ ⊗ (i^*𝓜_r)^{⊗ n_r})`.

This is `AlgebraicGeometry.pushforwardTwistListIso` at `List.finRange r`, which is the list
`AlgebraicGeometry.twistedSheaf` folds over. -/
def pushforwardTwistedSheafIso (N : Z.Modules) (n : Fin r → ℤ) :
    twistedSheaf ((Scheme.Modules.pushforward i).obj N) M n ≅
      (Scheme.Modules.pushforward i).obj
        (twistedSheaf N (fun j => (Scheme.Modules.pullback i).obj (M j)) n) :=
  pushforwardTwistListIso i M n (List.finRange r) N

end Fold

/-! ### The Euler characteristic of a twist of a direct image -/

/-- **The Euler characteristic of a twist of a direct image is computed on the closed
subscheme**: `χ(X, (i_*𝒩) ⊗ 𝓜_1^{⊗ n_1} ⊗ ⋯) = χ(Z, 𝒩 ⊗ (i^*𝓜_1)^{⊗ n_1} ⊗ ⋯)`.

`AlgebraicGeometry.pushforwardTwistedSheafIso` identifies the module on `X` with a direct image,
and `AlgebraicGeometry.eulerCharacteristic_pushforward_of_isClosedImmersion`
([Stacks, Tag 089W] at the level of Euler characteristics) moves the Euler characteristic across.
This is the form in which the inductive step of [Stacks, Tag 0BEM], run on the scheme-theoretic
support of [Stacks, Tag 02OM], is read back on `X`.

Coherence of the two twists is passed explicitly, as everywhere in this part of the development:
a caller holds it as a term produced by
`AlgebraicGeometry.twistedSheaf_isCoherent_of_tensorSheaf_isCoherent`, not as an instance. -/
theorem eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion (k : Type u) [Field k]
    {Z X : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ Spec (.of k)) [IsClosedImmersion i] [IsProper f]
    [IsLocallyNoetherian X] {r : ℕ} (M : Fin r → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j)]
    [∀ j, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      ((Scheme.Modules.pullback i).obj (M j))]
    (N : Z.Modules) (n : Fin r → ℤ)
    (hup : (twistedSheaf ((Scheme.Modules.pushforward i).obj N) M n).IsCoherent)
    (hdown : (twistedSheaf N (fun j => (Scheme.Modules.pullback i).obj (M j)) n).IsCoherent) :
    @eulerCharacteristic k _ X f _
        (twistedSheaf ((Scheme.Modules.pushforward i).obj N) M n) hup =
      @eulerCharacteristic k _ Z (i ≫ f) _
        (twistedSheaf N (fun j => (Scheme.Modules.pullback i).obj (M j)) n) hdown := by
  have hpush : ((Scheme.Modules.pushforward i).obj
      (twistedSheaf N (fun j => (Scheme.Modules.pullback i).obj (M j)) n)).IsCoherent :=
    @isCoherent_pushforward_of_isClosedImmersion Z X i _ _ _ hdown
  refine Eq.trans ?_
    (eulerCharacteristic_pushforward_of_isClosedImmersion k i f _ hdown hpush)
  exact @eulerCharacteristic_eq_of_iso k _ X f _ _ _ hup hpush
    (pushforwardTwistedSheafIso i M N n)

/-! ### The regular meromorphic section on the scheme-theoretic support -/

/-- **[Stacks, Tag 02OZ] case (3) on the scheme-theoretic support of [Stacks, Tag 02OM]**: the
pullback of an invertible sheaf to the scheme-theoretic support of a coherent sheaf without
embedded associated points has a regular meromorphic section.

This discharges, on that subscheme, the two arguments that
`AlgebraicGeometry.exists_differenceSequences_of_supp_eq_univ` takes explicitly. The only two
inputs are the first conjunct of
`AlgebraicGeometry.exists_isCoherent_pushforward_iso_of_hasNoEmbeddedAssociatedPoints` — the
subscheme has no embedded points — and
`AlgebraicGeometry.SheafOfModules.isInvertible_pullback`.

No attribute is attached: Tag 02OZ's three cases are already placed, on
`AlgebraicGeometry.exists_isRegularMeromorphicSection_of_isIntegral`,
`...of_isReduced` and `...of_hasNoEmbeddedPoints`, and this is case (3) at a particular scheme
and a particular sheaf rather than a clause of the tag. -/
theorem exists_isRegularMeromorphicSection_pullback_subscheme_annihilatorIdeal
    {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (hF : HasNoEmbeddedAssociatedPoints F) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ s : MeromorphicSection (annihilatorIdeal F).subscheme.sheaf
        ((Scheme.Modules.pullback (annihilatorIdeal F).subschemeι).obj L),
      IsRegularMeromorphicSection (annihilatorIdeal F).subscheme.sheaf
        ((Scheme.Modules.pullback (annihilatorIdeal F).subschemeι).obj L) s :=
  have _hZ : IsLocallyNoetherian (annihilatorIdeal F).subscheme :=
    isLocallyNoetherian_of_isClosedImmersion (annihilatorIdeal F).subschemeι
  have _hinv : SheafOfModules.IsInvertible
      (annihilatorIdeal F).subscheme.presheaf (annihilatorIdeal F).subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (annihilatorIdeal F).subschemeι).obj L) :=
    SheafOfModules.isInvertible_pullback (annihilatorIdeal F).subschemeι L
  exists_isRegularMeromorphicSection_of_hasNoEmbeddedPoints _
    (hasNoEmbeddedPoints_subscheme_annihilatorIdeal F hF) _

/-! ### The support of a direct image along a closed immersion -/

section Support

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (G : Z.Modules)

/-- **The stalk of a direct image along a closed immersion, read on the image.** The underlying
presheaf of abelian groups of `i_*𝒢` is the topological pushforward of that of `𝒢`, and the
canonical map on stalks of a pushforward along an inducing map is an isomorphism. -/
theorem nontrivial_stalk_pushforward_iff (z : Z) :
    Nontrivial ((show TopCat.Presheaf Ab.{u} (TopCat.of X) from
        ((Scheme.Modules.pushforward i).obj G).val.presheaf).stalk (i.base z)) ↔
      Nontrivial ((show TopCat.Presheaf Ab.{u} (TopCat.of Z) from
        G.val.presheaf).stalk z) :=
  have _ : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} i.base
      (show TopCat.Presheaf Ab.{u} (TopCat.of Z) from G.val.presheaf) z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{u}
      i.isClosedEmbedding.isInducing _ z
  Equiv.nontrivial_congr
    (asIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} i.base
      (show TopCat.Presheaf Ab.{u} (TopCat.of Z) from
        G.val.presheaf) z)).addCommGroupIsoToAddEquiv.toEquiv

/-- **A point of the closed subscheme is in the support of the direct image exactly when it is in
the support.** -/
theorem mem_supp_pushforward_iff (z : Z) :
    i.base z ∈ SheafOfModules.supp ((Scheme.Modules.pushforward i).obj G) ↔
      z ∈ SheafOfModules.supp G :=
  (SheafOfModules.mem_supp_iff_nontrivial_stalk
      ((Scheme.Modules.pushforward i).obj G) (i.base z)).trans
    ((nontrivial_stalk_pushforward_iff i G z).trans
      (SheafOfModules.mem_supp_iff_nontrivial_stalk G z).symm)

/-- **A direct image along a closed immersion is supported on the image**: off the image its
stalks vanish. -/
theorem notMem_supp_pushforward_of_notMemRange (x : X) (hx : x ∉ Set.range i.base) :
    x ∉ SheafOfModules.supp ((Scheme.Modules.pushforward i).obj G) :=
  have hzero : CategoryTheory.Limits.IsZero
      ((show TopCat.Presheaf Ab.{u} (TopCat.of X) from
        ((Scheme.Modules.pushforward i).obj G).val.presheaf).stalk x) :=
    closedInclusion_pushforward_stalk_isZero_of_not_mem_range
      (TopCat.of Z) (TopCat.of X) i.base i.isClosedEmbedding
      ⟨(Scheme.Modules.toPresheaf Z).obj G, Scheme.Modules.isSheaf G⟩ x hx
  fun hmem => (not_nontrivial_iff_subsingleton.mpr
      (AddCommGrpCat.subsingleton_of_isZero hzero))
    ((SheafOfModules.mem_supp_iff_nontrivial_stalk
      ((Scheme.Modules.pushforward i).obj G) x).mp hmem)

/-- **The support of a direct image along a closed immersion is the image of the support**:
`Supp (i_*𝒢) = i(Supp 𝒢)`. -/
theorem supp_pushforward_of_isClosedImmersion :
    SheafOfModules.supp ((Scheme.Modules.pushforward i).obj G) =
      i.base '' SheafOfModules.supp G := by
  ext x
  refine ⟨fun hx => ?_, ?_⟩
  · by_cases hr : x ∈ Set.range i.base
    · obtain ⟨z, rfl⟩ := hr
      exact ⟨z, (mem_supp_pushforward_iff i G z).mp hx, rfl⟩
    · exact absurd hx (notMem_supp_pushforward_of_notMemRange i G x hr)
  · rintro ⟨z, hz, rfl⟩
    exact (mem_supp_pushforward_iff i G z).mpr hz

/-- **The support of `𝒢` and the support of `i_*𝒢` are homeomorphic**, by the restriction of the
closed embedding `i` to the support. -/
def suppPushforwardHomeomorph :
    ↥(SheafOfModules.supp G) ≃ₜ
      ↥(SheafOfModules.supp ((Scheme.Modules.pushforward i).obj G)) :=
  (IsEmbedding.homeomorphImage i.isClosedEmbedding.isEmbedding (SheafOfModules.supp G)).trans
    (Homeomorph.setCongr (supp_pushforward_of_isClosedImmersion i G).symm)

/-- `AlgebraicGeometry.suppPushforwardHomeomorph` is the restriction of `i` on points. -/
theorem coe_suppPushforwardHomeomorph (a : ↥(SheafOfModules.supp G)) :
    ((suppPushforwardHomeomorph i G a : ↥(SheafOfModules.supp
      ((Scheme.Modules.pushforward i).obj G))) : X) = i.base (a : Z) := rfl

/-- **The dimension of the support is unchanged by a direct image along a closed immersion.** -/
theorem topologicalKrullDim_supp_pushforward_of_isClosedImmersion :
    topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pushforward i).obj G)) =
      topologicalKrullDim (SheafOfModules.supp G) :=
  (IsHomeomorph.topologicalKrullDim_eq _ (suppPushforwardHomeomorph i G).isHomeomorph).symm

/-- **The descent measure of [Stacks, Tag 0BEM] is unchanged by a direct image along a closed
immersion**: `natDimSupp (i_*𝒢) = natDimSupp 𝒢`. -/
theorem natDimSupp_pushforward_of_isClosedImmersion :
    natDimSupp ((Scheme.Modules.pushforward i).obj G) = natDimSupp G :=
  congrArg (fun d : WithBot ENat => (d.unbotD 0).toNat)
    (topologicalKrullDim_supp_pushforward_of_isClosedImmersion i G)

/-- The homeomorphism of supports carries the part of `Supp 𝒢` lying in `Supp 𝒢₁` to the part of
`Supp (i_*𝒢)` lying in `Supp (i_*𝒢₁)`. Surjectivity uses the injectivity of `i` on points: a
point of `Supp (i_*𝒢)` over `Supp (i_*𝒢₁)` has one preimage, and it lies in both supports. -/
theorem image_preimage_val_supp_pushforward (G₁ : Z.Modules) :
    suppPushforwardHomeomorph i G ''
        ((Subtype.val : ↥(SheafOfModules.supp G) → Z) ⁻¹' SheafOfModules.supp G₁) =
      (Subtype.val : ↥(SheafOfModules.supp ((Scheme.Modules.pushforward i).obj G)) → X) ⁻¹'
        SheafOfModules.supp ((Scheme.Modules.pushforward i).obj G₁) := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mem_supp_pushforward_iff i G₁ (a : Z)).mpr ha
  · intro hb
    obtain ⟨z, hz, hzb⟩ := (supp_pushforward_of_isClosedImmersion i G).subset b.2
    exact ⟨⟨z, hz⟩, (mem_supp_pushforward_iff i G₁ z).mp (hzb ▸ hb), Subtype.ext hzb⟩

/-- **Nowhere density inside the support is unchanged by a direct image along a closed
immersion.** This is the form in which the inductive step of [Stacks, Tag 0BEM] carries its
support-dimension drops (`AlgebraicGeometry.IsTwistDifferenceStep`), so it is the form the
passage to the scheme-theoretic support of [Stacks, Tag 02OM] has to preserve. -/
theorem isNowhereDense_preimage_val_supp_pushforward_iff (G₁ : Z.Modules) :
    IsNowhereDense ((Subtype.val :
          ↥(SheafOfModules.supp ((Scheme.Modules.pushforward i).obj G)) → X) ⁻¹'
        SheafOfModules.supp ((Scheme.Modules.pushforward i).obj G₁)) ↔
      IsNowhereDense ((Subtype.val : ↥(SheafOfModules.supp G) → Z) ⁻¹'
        SheafOfModules.supp G₁) := by
  rw [← image_preimage_val_supp_pushforward i G G₁]
  exact Homeomorph.isNowhereDense_image_iff _ _

end Support

end AlgebraicGeometry

end
