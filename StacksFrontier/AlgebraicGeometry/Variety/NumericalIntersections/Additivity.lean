module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.IntersectionNumberDivisor
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EulerPolynomialProper
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersection
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.DivisorFirstDifference
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Additivity of the intersection number in each invertible module

Let `k` be a field, let `X` be a proper scheme over `k`, let `i : Z ⟶ X` be a closed subscheme
of dimension at most `d` and let `𝓛_1, …, 𝓛_d` be invertible `𝒪_X`-modules.  [Stacks, Tag 0BER]
says that the intersection number `(𝓛_1 ⋯ 𝓛_d · Z)` of [Stacks, Tag 0BEP] is additive in each
slot: if `𝓛_j ≅ 𝓛_j' ⊗ 𝓛_j''` then

`(𝓛_1 ⋯ 𝓛_j ⋯ 𝓛_d · Z) = (𝓛_1 ⋯ 𝓛_j' ⋯ 𝓛_d · Z) + (𝓛_1 ⋯ 𝓛_j'' ⋯ 𝓛_d · Z)`.

The intersection number used is the library's canonical one,
`AlgebraicGeometry.intersectionNumber`, which is the `d`-fold mixed finite difference

`∑_{T ⊆ {1, …, d}} (-1)^{d - |T|} χ(Z, ⨂_{t ∈ T} 𝓛_t|_Z)`

of the Euler characteristics of the twists.  Nothing is redefined here.

## Main results

* `AlgebraicGeometry.intersectionNumber_tensor`: **[Stacks, Tag 0BER].**  Additivity in the
  `j`-th slot, for three families of invertible modules agreeing away from `j`.
* `AlgebraicGeometry.intersectionNumber_update_tensor`: **[Stacks, Tag 0BER].**  The same with
  the two other families written as `Function.update`, which is how the source presents them.

## Implementation notes

**The route.**  The source's proof is that the function of `d + 1` variables

`(n_1, …, n_{j-1}, n_j', n_j'', n_{j+1}, …, n_d) ↦
  χ(Z, 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ (𝓛_j')^{⊗ n_j'} ⊗ (𝓛_j'')^{⊗ n_j''} ⊗ ⋯ ⊗ 𝓛_d^{⊗ n_d}|_Z)`

is a numerical polynomial of total degree at most `d` in `d + 1` variables, which is
[Stacks, Tag 0BEM].  That tag is available unconditionally in this library, as
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_isProper`, so nothing is carried.

With the mixed finite difference as the *definition* of the intersection number, the source's
"additivity follows" is the following identity, which is what is run below.  Write
`H(a, n) = χ(Z, (𝓛_j'')^{⊗ a} ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯|_Z)` for the `d + 1`-variable family obtained
by putting `𝓛_j''` in front of the family `𝓛_1, …, 𝓛_j', …, 𝓛_d`.  The `d`-fold mixed finite
difference of the first difference `H(1, ·) - H(0, ·)` is the coefficient of `n_1 ⋯ n_{d+1}` in
the interpolating polynomial — this is
`MvPolynomial.sum_neg_one_pow_mul_sub_eval_cons_eq_coeff_one`, the same device as in
`StacksFrontier/AlgebraicGeometry/Variety/NumericalIntersections/DivisorDifference.lean` — and that
coefficient vanishes because the squarefree monomial in `d + 1` variables has degree `d + 1`
while the polynomial has total degree at most `d`.  So

`∑_{T ⊆ {1, …, d}} (-1)^{d - |T|} χ(Z, (⨂_{t ∈ T} 𝓛_t'|_Z) ⊗ 𝓛_j''|_Z)
  = (𝓛_1 ⋯ 𝓛_j' ⋯ 𝓛_d · Z)`,

where `𝓛_t' = 𝓛_t` for `t ≠ j`.  The left-hand side is then evaluated term by term: for
`j ∈ T` the extra factor `𝓛_j''|_Z` completes `𝓛_j'|_Z` to `𝓛_j|_Z`, so the term is the one of
`(𝓛_1 ⋯ 𝓛_j ⋯ 𝓛_d · Z)`; for `j ∉ T` the factor `𝓛_j''|_Z` *creates* the `j`-th factor, so the
term is the one of `(𝓛_1 ⋯ 𝓛_j'' ⋯ 𝓛_d · Z)` at `T ∪ {j}`, whose sign is opposite.  Pairing
`T` with `T ∪ {j}` gives the three-term identity.

**Splitting off the factor of a slot.**  Both evaluations of the left-hand side go through
`AlgebraicGeometry.twistedSheafSplitIso`: a twist whose exponent at `j` exceeds another's by one,
the two agreeing elsewhere, is that other twist tensored by `𝓛_j`.  This is
`AlgebraicGeometry.twistedSheafUpdateIso` with the two exponent vectors described by hypotheses
rather than by `Function.update`, so that they can be taken to be the indicator functions of `T`
and of `T \ {j}` with no rewriting inside the type of an isomorphism.

**The pairing is an involution.**  The three signed sums are compared by
`AlgebraicGeometry.sum_neg_one_pow_mul_eq_add_of_sum_sub_eq_zero`, which runs
`Finset.sum_ninvolution` on `T ↦ if j ∈ T then T \ {j} else T ∪ {j}`.  The two terms of a pair
cancel because `|T ∪ {j}| = |T| + 1` reverses the sign `(-1)^{d - |T|}`, which needs
`|T| < d` for `j ∉ T`.

**Why the twists are compared by equalities where possible.**  A slot whose exponent is `0`
contributes `𝓛^{⊗ 0}`, which is the structure sheaf *by `rfl`*
(`Stacks.SheafOfModules.Invertible.tensorPower_zero`), so two families agreeing away from a slot
carrying exponent `0` give twists that are *equal*, not merely isomorphic
(`AlgebraicGeometry.twistList_eq_of_forall_tensorPower_eq`).  Rewriting an invertible module
inside `Stacks.SheafOfModules.Invertible.tensorPower` is otherwise awkward, because the
invertibility instance depends on the module; `AlgebraicGeometry.tensorPower_congr` substitutes
and then appeals to definitional proof irrelevance, the instance being `Prop`-valued.

**Peeling the first factor off a twist.**  `AlgebraicGeometry.twistedSheaf` is a left fold over
`List.finRange r`, and `List.finRange_succ` splits that list as `0 :: (List.finRange d).map
Fin.succ`.  So a twist by a family indexed by `Fin (d + 1)` *is* the twist, by the shifted
family, of `ℱ ⊗ 𝓛_0^{⊗ n_0}` (`AlgebraicGeometry.twistedSheaf_succ_eq`, an equality).  The two
exponents that occur, `n_0 = 0` and `n_0 = 1`, then give
`AlgebraicGeometry.twistedSheafConsZeroIso` and `AlgebraicGeometry.twistedSheafConsOneIso`.

**Pullback and the tensor product.**  The hypothesis `𝓛_j ≅ 𝓛_j' ⊗ 𝓛_j''` lives on `X` while
the Euler characteristics are taken on `Z`, so it is used through [Stacks, Tag 0BEN's
neighbour] Tag 01CD, `i^*(A ⊗ B) ≅ i^*A ⊗ i^*B`.  That tag is proved in this library as
`Stacks.PullbackTensorIso.pullbackTensorIso`, for a morphism of ringed spaces; at the
`AlgebraicGeometry.Scheme.Modules.pullback` spelling it is
`AlgebraicGeometry.pullbackTensorObjIso` below, which is the same isomorphism, the two spellings
being definitionally equal.

**Why three families rather than one `Function.update`.**  The source's data is "the same
modules except in slot `j`", and both renderings are given: `intersectionNumber_tensor` takes
three families with agreement hypotheses off `j`, which is what a caller holding three families
wants, and `intersectionNumber_update_tensor` specialises it to `Function.update`.  The first
carries the tag.

## References

* [Stacks Project, Tag 0BER](https://stacks.math.columbia.edu/tag/0BER)
* [Stacks Project, Tag 0BEP](https://stacks.math.columbia.edu/tag/0BEP)
* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.SheafOfModules.Invertible
open Stacks.SheafOfModules.TensorSheafification

universe u

namespace AlgebraicGeometry

/-! ### Comparing twists -/

section Twists

variable {X : Scheme.{u}} {r d : ℕ}

/-- **Tensor powers of equal invertible modules are equal.**  Rewriting under
`Stacks.SheafOfModules.Invertible.tensorPower` needs this detour because the invertibility
instance depends on the module; after substituting, the two instances are proofs of the same
proposition and so are definitionally equal. -/
public theorem tensorPower_congr {M N : X.Modules} (h : M = N)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] (m : ℤ) :
    tensorPower X.presheaf X.ringCatSheaf.2 M m =
      tensorPower X.presheaf X.ringCatSheaf.2 N m := by
  subst h
  rfl

/-- **A slot with exponent `0` does not see its module**: the zeroth tensor power of any
invertible module is the structure sheaf. -/
public theorem tensorPower_eq_of_eq_zero (M N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] {m : ℤ} (hm : m = 0) :
    tensorPower X.presheaf X.ringCatSheaf.2 M m =
      tensorPower X.presheaf X.ringCatSheaf.2 N m := by
  subst hm
  rfl

/-- **Two families whose tensor powers at the given exponents agree give the same fold.**  This
is an equality of sheaves, not merely an isomorphism: the fold is a `List.foldl` and the two
folding functions are equal. -/
public theorem twistList_eq_of_forall_tensorPower_eq {L L' : Fin r → X.Modules}
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)]
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L' q)] (e : Fin r → ℤ)
    (h : ∀ q, tensorPower X.presheaf X.ringCatSheaf.2 (L q) (e q) =
      tensorPower X.presheaf X.ringCatSheaf.2 (L' q) (e q))
    (l : List (Fin r)) (M : X.Modules) : twistList L e l M = twistList L' e l M :=
  congrArg (fun g : X.Modules → Fin r → X.Modules => List.foldl g M l)
    (funext fun N => funext fun q =>
      congrArg (fun A => (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
          (X.ringCatSheaf.2)⟩).obj (N)).obj (A))) (h q))

/-- The twist by two families whose tensor powers at the given exponents agree is the same
sheaf. -/
public theorem twistedSheaf_eq_of_forall_tensorPower_eq (F : X.Modules)
    {L L' : Fin r → X.Modules}
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)]
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L' q)] (e : Fin r → ℤ)
    (h : ∀ q, tensorPower X.presheaf X.ringCatSheaf.2 (L q) (e q) =
      tensorPower X.presheaf X.ringCatSheaf.2 (L' q) (e q)) :
    twistedSheaf F L e = twistedSheaf F L' e :=
  twistList_eq_of_forall_tensorPower_eq e h (List.finRange r) F

/-- Folding over the shifted indices is folding over the shifted family.  This is the form for
an arbitrary exponent vector;  `AlgebraicGeometry.twistList_map_succ` is the special case of an
exponent vector written as `Fin.cons`. -/
public theorem twistList_map_succ_tail (M : Fin (d + 1) → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M t)] (n : Fin (d + 1) → ℤ)
    (l : List (Fin d)) (F : X.Modules) : twistList M n (l.map Fin.succ) F =
      twistList (fun q : Fin d => M q.succ) (fun q => n q.succ) l F :=
  List.foldl_map ..

/-- **Peeling the first factor off a twist.**  A twist by a family indexed by `Fin (d + 1)` is
the twist, by the family shifted along `Fin.succ`, of `ℱ ⊗ 𝓛_0^{⊗ n_0}`.  This is an equality:
`List.finRange (d + 1)` is `0 :: (List.finRange d).map Fin.succ`, and the fold over a mapped
list is the fold of the composite. -/
public theorem twistedSheaf_succ_eq (F : X.Modules) (M : Fin (d + 1) → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M t)] (n : Fin (d + 1) → ℤ) :
    twistedSheaf F M n =
      twistedSheaf ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
          (X.ringCatSheaf.2)⟩).obj (F)).obj
          ((tensorPower X.presheaf X.ringCatSheaf.2 (M 0) (n 0)))))
        (fun q : Fin d => M q.succ) (fun q => n q.succ) := by
  show twistList M n (List.finRange (d + 1)) F = _
  rw [List.finRange_succ]
  exact twistList_map_succ_tail M n (List.finRange d) _

/-- **The twist with first exponent `1`** is the twist by the shifted family, tensored by
`𝓛_0`. -/
public noncomputable def twistedSheafConsOneIso (F : X.Modules) (M : Fin (d + 1) → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M t)] (e : Fin d → ℤ) :
    twistedSheaf F M (Fin.cons 1 e) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
          (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩).obj
          ((twistedSheaf F (fun q : Fin d => M q.succ) e))).obj ((M 0))) :=
  have he : tensorPower X.presheaf X.ringCatSheaf.2 (M 0)
        ((Fin.cons 1 e : Fin (d + 1) → ℤ) 0) =
      tensorPower X.presheaf X.ringCatSheaf.2 (M 0) 1 := by
    simp
  eqToIso (twistedSheaf_succ_eq F M (Fin.cons 1 e)) ≪≫
    twistListIso (fun q : Fin d => M q.succ) e (List.finRange d)
      (tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl F)
        (eqToIso he ≪≫ tensorPowerOneIso X.presheaf X.ringCatSheaf.2 (M 0))) ≪≫
    twistListTensorIso (fun q : Fin d => M q.succ) e (List.finRange d) F (M 0)

/-- **Splitting off the factor of one slot.**  If the exponent vector `n` exceeds `m` by one in
the slot `j` and agrees with it in every other slot, the twist by `n` is the twist by `m`
tensored by `𝓛_j`.  This is `AlgebraicGeometry.twistedSheafUpdateIso` with the two exponent
vectors described by hypotheses rather than by `Function.update`. -/
public noncomputable def twistedSheafSplitIso (F : X.Modules) (N : Fin r → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (N q)] {n m : Fin r → ℤ}
    (j : Fin r) (hj : n j = m j + 1) (h : ∀ q, q ≠ j → n q = m q) :
    twistedSheaf F N n ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
          (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩).obj
          ((twistedSheaf F N m))).obj ((N j))) :=
  twistListUpdateIso N j hj (List.finRange r) (List.nodup_finRange r) (List.mem_finRange j)
    (fun q _ hq => h q hq) F

/-- **A family of invertible modules extended by one more is invertible.**  `Fin.cons 𝓜 𝓛` reads
a family of `d` invertible modules together with one further invertible module as a family of
`d + 1` invertible modules. -/
public theorem isInvertible_finCons (M : X.Modules) (N : Fin d → X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (N q)] (t : Fin (d + 1)) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Fin.cons (α := fun _ => X.Modules) M N t) := by
  refine Fin.cases ?_ (fun q => ?_) t
  · simpa only [Fin.cons_zero] using
      (inferInstance : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M)
  · simpa only [Fin.cons_succ] using
      (inferInstance : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (N q))

/-- **A family of invertible modules with one member replaced by an invertible module is
invertible.** -/
public theorem isInvertible_update (N : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (N q)] (j : Fin d)
    (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (q : Fin d) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (Function.update N j M q) := by
  by_cases hq : q = j
  · subst hq
    rw [Function.update_self]
    infer_instance
  · rw [Function.update_of_ne hq]
    infer_instance

end Twists

attribute [local instance] isInvertible_update

/-! ### Pullback and the tensor product -/

/-- **[Stacks, Tag 01CD] at the `AlgebraicGeometry.Scheme.Modules.pullback` spelling**: the
pullback of a tensor product of `𝒪_X`-modules along a morphism of schemes is the tensor product
of the pullbacks.  This is `Stacks.PullbackTensorIso.pullbackTensorIso`, which proves the tag
for a morphism of ringed spaces; the two spellings of the pullback and of the tensor product
are definitionally equal, so nothing is bridged and the tag is not repeated here. -/
public noncomputable def pullbackTensorObjIso {X Z : Scheme.{u}} (i : Z ⟶ X) (A B : X.Modules) :
    (Scheme.Modules.pullback i).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.2)⟩).obj (A)).obj (B))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
          (Z.presheaf) (forget₂ CommRingCat RingCat) (Z.ringCatSheaf.2)⟩).obj
          (((Scheme.Modules.pullback i).obj A))).obj (((Scheme.Modules.pullback i).obj B))) :=
  (Stacks.PullbackTensorIso.pullbackTensorIso i.toLRSHom.toShHom).app (A, B)

/-! ### The alternating sum of cohomology dimensions -/

section Chi

variable (k : Type u) [Field k] {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k))

/-- The alternating sum of the dimensions over `k` of the cohomology groups of a module on `Z`.
This is `AlgebraicGeometry.eulerCharacteristic` with the coherence hypothesis dropped, so that
it can be written for the intermediate modules of the computation below; it is definitionally
the same alternating sum, which is `AlgebraicGeometry.chiOverField_eq_eulerCharacteristic`. -/
public noncomputable def chiOverField (M : Z.Modules) : ℤ :=
  ∑ᶠ m : ℕ, (-1 : ℤ) ^ m * (Module.finrank k (cohomologyOverField k g M m) : ℤ)

/-- `AlgebraicGeometry.chiOverField` is an isomorphism invariant. -/
public theorem chiOverField_eq_of_iso {M N : Z.Modules} (e : M ≅ N) :
    chiOverField k g M = chiOverField k g N :=
  finsum_congr fun m => by rw [finrank_cohomologyOverField_eq_of_iso k g e m]

/-- On a coherent module over a proper scheme, `AlgebraicGeometry.chiOverField` is the Euler
characteristic. -/
public theorem chiOverField_eq_eulerCharacteristic [IsProper g] (M : Z.Modules)
    (h : _root_.SheafOfModules.IsCoherent M) :
    chiOverField k g M = @eulerCharacteristic k _ Z g _ M h := rfl

end Chi

/-! ### The intersection number as a sum of alternating sums -/

/-- The defining mixed finite difference of the intersection number, written with
`AlgebraicGeometry.chiOverField`. -/
public theorem intersectionNumber_eq_sum_chiOverField (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (L : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)] :
    intersectionNumber k f i d hd L =
      ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
        chiOverField k (i ≫ f) (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun q => (Scheme.Modules.pullback i).obj (L q))
          (fun q => if q ∈ T then 1 else 0)) := rfl

/-! ### The first-difference identity of Tag 0BEM -/

/-- **The vanishing mixed finite difference of Tag 0BEM.**  For a family of `d + 1` invertible
`𝒪_X`-modules on a proper scheme and a closed subscheme `Z` of dimension at most `d`, the
`d`-fold mixed finite difference of the first difference of the Euler characteristics of the
twists of `𝒪_Z` in the zeroth variable vanishes.

The interpolating polynomial is [Stacks, Tag 0BEM], available unconditionally as
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_isProper`; its total degree is at most
`dim Supp 𝒪_Z ≤ dim Z ≤ d`, so the coefficient of the squarefree monomial in `d + 1` variables,
which the mixed difference computes by
`MvPolynomial.sum_neg_one_pow_mul_sub_eval_cons_eq_coeff_one`, is zero. -/
@[sga "6 X 2.3.1" "special case"]
public theorem sum_neg_one_pow_mul_sub_chiOverField_twistedSheaf_eq_zero (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (M : Fin (d + 1) → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M t)] :
    ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
        (chiOverField k (i ≫ f) (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
            (fun t => (Scheme.Modules.pullback i).obj (M t))
            (Fin.cons 1 fun q => if q ∈ T then 1 else 0)) -
          chiOverField k (i ≫ f) (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
            (fun t => (Scheme.Modules.pullback i).obj (M t))
            (Fin.cons 0 fun q => if q ∈ T then 1 else 0))) = 0 := by
  classical
  have hunit : _root_.SheafOfModules.IsCoherent (SheafOfModules.unit Z.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f)
  obtain ⟨P, hdeg, hP⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k (i ≫ f)
    (fun t => (Scheme.Modules.pullback i).obj (M t)) (SheafOfModules.unit Z.ringCatSheaf) hunit
  have hPdeg : P.totalDegree ≤ d := by
    rcases hdeg with h | h
    · rw [h]
      simp
    · have hsupp : topologicalKrullDim
          (_root_.SheafOfModules.supp (SheafOfModules.unit Z.ringCatSheaf)) ≤ (d : ℕ) :=
        le_trans (topologicalKrullDim_subspace_le _ _) hd
      exact_mod_cast le_trans h hsupp
  have hcoeff : P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) = 0 := by
    refine MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_
    have hsupport : (Finsupp.equivFunOnFinite.symm (fun _ => 1 : Fin (d + 1) → ℕ)).support =
        Finset.univ := by
      ext t
      simp
    rw [hsupport]
    have : ∑ _t : Fin (d + 1), (Finsupp.equivFunOnFinite.symm
        (fun _ => 1 : Fin (d + 1) → ℕ)) _t = d + 1 := by
      simp
    omega
  have hcast : ∀ (c : ℤ) (T : Finset (Fin d)),
      (fun t : Fin (d + 1) =>
          (((Fin.cons c fun q => if q ∈ T then (1 : ℤ) else 0 : Fin (d + 1) → ℤ) t : ℤ) : ℚ)) =
        (Fin.cons (c : ℚ) fun q => if q ∈ T then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) := by
    intro c T
    refine funext fun t => ?_
    refine Fin.cases ?_ (fun q => ?_) t
    · simp
    · simp only [Fin.cons_succ]
      split_ifs <;> simp
  have hval : ∀ (c : ℤ) (T : Finset (Fin d)),
      MvPolynomial.eval
          (Fin.cons (c : ℚ) fun q => if q ∈ T then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) P =
        ((chiOverField k (i ≫ f) (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun t => (Scheme.Modules.pullback i).obj (M t))
          (Fin.cons c fun q => if q ∈ T then 1 else 0)) : ℤ) : ℚ) := by
    intro c T
    have h := hP (Fin.cons c fun q => if q ∈ T then (1 : ℤ) else 0)
    rw [hcast c T] at h
    exact h
  have hshift := MvPolynomial.sum_neg_one_pow_mul_sub_eval_cons_eq_coeff_one P
    (hPdeg.trans (Nat.le_succ d)) 1
  rw [hcoeff] at hshift
  have hone : ((1 : ℤ) : ℚ) = (1 : ℚ) := by norm_num
  have hzero : ((0 : ℤ) : ℚ) = (1 : ℚ) - 1 := by norm_num
  have hmain : (((∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
      (chiOverField k (i ≫ f) (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun t => (Scheme.Modules.pullback i).obj (M t))
          (Fin.cons 1 fun q => if q ∈ T then 1 else 0)) -
        chiOverField k (i ≫ f) (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun t => (Scheme.Modules.pullback i).obj (M t))
          (Fin.cons 0 fun q => if q ∈ T then 1 else 0)))) : ℤ) : ℚ) = 0 := by
    rw [← hshift]
    push_cast
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [show (Fin.cons (1 : ℚ) fun q => if q ∈ T then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) =
        (Fin.cons (((1 : ℤ) : ℚ)) fun q => if q ∈ T then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) by
      rw [hone],
      show (Fin.cons ((1 : ℚ) - 1) fun q => if q ∈ T then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) =
        (Fin.cons (((0 : ℤ) : ℚ)) fun q => if q ∈ T then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) by
      rw [hzero], hval 1 T, hval 0 T]
  exact_mod_cast hmain

/-! ### The combinatorial identity -/

/-- **Pairing a subset with the one obtained by inserting `j`.**  Let `a`, `c`, `c'` and `c''` be
functions on the subsets of `{1, …, d}`.  If the signed sum of `a - c'` vanishes, if `a` agrees
with `c` on the subsets containing `j`, if `a` at a subset `T` not containing `j` is `c''` at
`T ∪ {j}`, and if `c` and `c''` agree on the subsets not containing `j`, then the signed sums of
`c`, `c'` and `c''` satisfy `Σc = Σc' + Σc''`.

The pairing `T ↦ T △ {j}` is an involution of the subsets of `{1, …, d}` reversing the sign
`(-1)^{d - |T|}`, so the terms of a pair cancel. -/
public theorem sum_neg_one_pow_mul_eq_add_of_sum_sub_eq_zero {d : ℕ} (j : Fin d)
    (a c c' c'' : Finset (Fin d) → ℤ)
    (hsum : ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) * (a T - c' T) = 0)
    (hmem : ∀ T : Finset (Fin d), j ∈ T → a T = c T)
    (hnotMem : ∀ T : Finset (Fin d), j ∉ T → a T = c'' (insert j T))
    (hagree : ∀ T : Finset (Fin d), j ∉ T → c T = c'' T) :
    ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) * c T =
      (∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) * c' T) +
        ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) * c'' T := by
  have hcard : ∀ T : Finset (Fin d), j ∉ T → T.card < d := by
    intro T hT
    have hne : T ≠ Finset.univ := fun h => hT (h ▸ Finset.mem_univ j)
    simpa using (Finset.card_lt_iff_ne_univ T).2 hne
  have hsign : ∀ T : Finset (Fin d), j ∉ T →
      (-1 : ℤ) ^ (d - (insert j T).card) = -(-1 : ℤ) ^ (d - T.card) := by
    intro T hT
    have hlt : T.card < d := hcard T hT
    rw [Finset.card_insert_of_notMem hT, show d - T.card = d - (T.card + 1) + 1 by omega,
      pow_succ]
    ring
  have key : ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) * (c T - c'' T - a T) = 0 := by
    refine Finset.sum_ninvolution (fun T => if j ∈ T then T.erase j else insert j T) ?_
      (fun T _ => ?_) (fun _ => Finset.mem_univ _) ?_
    · intro T
      by_cases hT : j ∈ T
      · have hTe : j ∉ T.erase j := Finset.notMem_erase j T
        have hins : insert j (T.erase j) = T := Finset.insert_erase hT
        have hs : (-1 : ℤ) ^ (d - T.card) = -(-1 : ℤ) ^ (d - (T.erase j).card) := by
          have h := hsign (T.erase j) hTe
          rwa [hins] at h
        rw [ite_eq_left hT, hmem T hT, hagree _ hTe, hnotMem _ hTe, hins, hs]
        ring
      · rw [ite_eq_right hT, hagree T hT, hnotMem T hT,
          hmem _ (Finset.mem_insert_self j T), hsign T hT]
        ring
    · by_cases hT : j ∈ T
      · rw [ite_eq_left hT]
        intro h
        exact Finset.notMem_erase j T (by rw [h]; exact hT)
      · rw [ite_eq_right hT]
        intro h
        exact hT (h ▸ Finset.mem_insert_self j T)
    · intro T
      by_cases hT : j ∈ T
      · rw [ite_eq_left hT, ite_eq_right (Finset.notMem_erase j T), Finset.insert_erase hT]
      · rw [ite_eq_right hT, ite_eq_left (Finset.mem_insert_self j T), Finset.erase_insert hT]
  simp only [mul_sub, Finset.sum_sub_distrib] at hsum key
  linarith

/-- Twists of `𝒪_Z` by the pullbacks of two families agreeing away from `j` are equal when the
exponent at `j` is `0`. -/
private theorem twistedSheaf_pullback_eq_of_eq_off {X Z : Scheme.{u}} {d : ℕ} (i : Z ⟶ X)
    (A B : Fin d → X.Modules) [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (A q)]
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (B q)] (e : Fin d → ℤ)
    (j : Fin d) (hj : e j = 0) (h : ∀ q, q ≠ j → A q = B q) :
    twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
        (fun q => (Scheme.Modules.pullback i).obj (A q)) e =
      twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
        (fun q => (Scheme.Modules.pullback i).obj (B q)) e :=
  twistedSheaf_eq_of_forall_tensorPower_eq _ _ fun q => by
    by_cases hq : q = j
    · subst hq
      exact tensorPower_eq_of_eq_zero _ _ hj
    · exact tensorPower_congr (congrArg (fun A => (Scheme.Modules.pullback i).obj A) (h q hq)) _

/-! ### Additivity of the intersection number -/

/-- **[Stacks, Tag 0BER].**  The intersection number is additive in each slot: if `𝓛_j` is the
tensor product of `𝓛_j'` and `𝓛_j''`, and the three families of invertible modules agree away
from `j`, then

`(𝓛_1 ⋯ 𝓛_j ⋯ 𝓛_d · Z) = (𝓛_1 ⋯ 𝓛_j' ⋯ 𝓛_d · Z) + (𝓛_1 ⋯ 𝓛_j'' ⋯ 𝓛_d · Z)`. -/
@[stacks 0BER "additivity of the intersection number in each invertible module"]
public theorem intersectionNumber_tensor (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (j : Fin d) (L L' L'' : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)]
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L' q)]
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L'' q)]
    (hL' : ∀ q, q ≠ j → L' q = L q) (hL'' : ∀ q, q ≠ j → L'' q = L q)
    (hj : L j ≅ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.2)⟩).obj ((L' j))).obj ((L'' j)))) :
    intersectionNumber k f i d hd L =
      intersectionNumber k f i d hd L' + intersectionNumber k f i d hd L'' := by
  have hinv := isInvertible_finCons (L'' j) L'
  -- the twist by the family of `d + 1` modules with `𝓛_j''` in front, at first exponent `1`
  have hcons : ∀ T : Finset (Fin d),
      twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun t => (Scheme.Modules.pullback i).obj
            (Fin.cons (α := fun _ => X.Modules) (L'' j) L' t))
          (Fin.cons 1 fun q => if q ∈ T then 1 else 0) ≅
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
            (Z.presheaf) (forget₂ CommRingCat RingCat) (Z.ringCatSheaf.2)⟩).obj ((twistedSheaf
            (SheafOfModules.unit Z.ringCatSheaf)
            (fun q => (Scheme.Modules.pullback i).obj (L' q))
            (fun q => if q ∈ T then 1 else 0)))).obj (((Scheme.Modules.pullback i).obj (L'' j)))) :=
    fun T => twistedSheafConsOneIso _ _ _
  -- the same twist at first exponent `0` is the twist by `𝓛_1, …, 𝓛_j', …, 𝓛_d`
  have hzero : ∀ T : Finset (Fin d),
      chiOverField k (i ≫ f) (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun t => (Scheme.Modules.pullback i).obj
            (Fin.cons (α := fun _ => X.Modules) (L'' j) L' t))
          (Fin.cons 0 fun q => if q ∈ T then 1 else 0)) =
        chiOverField k (i ≫ f) (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun q => (Scheme.Modules.pullback i).obj (L' q))
          (fun q => if q ∈ T then 1 else 0)) :=
    fun T => chiOverField_eq_of_iso k (i ≫ f) (twistedSheafConsZeroIso _ _ _)
  have hsum : ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
      (chiOverField k (i ≫ f) (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun t => (Scheme.Modules.pullback i).obj
            (Fin.cons (α := fun _ => X.Modules) (L'' j) L' t))
          (Fin.cons 1 fun q => if q ∈ T then 1 else 0)) -
        chiOverField k (i ≫ f) (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun q => (Scheme.Modules.pullback i).obj (L' q))
          (fun q => if q ∈ T then 1 else 0))) = 0 :=
    Eq.trans (Finset.sum_congr rfl fun T _ => by rw [hzero T])
      (sum_neg_one_pow_mul_sub_chiOverField_twistedSheaf_eq_zero k f i d hd
        (Fin.cons (α := fun _ => X.Modules) (L'' j) L'))
  have hmem : ∀ T : Finset (Fin d), j ∈ T →
      chiOverField k (i ≫ f) (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun t => (Scheme.Modules.pullback i).obj
            (Fin.cons (α := fun _ => X.Modules) (L'' j) L' t))
          (Fin.cons 1 fun q => if q ∈ T then 1 else 0)) =
        chiOverField k (i ≫ f) (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun q => (Scheme.Modules.pullback i).obj (L q))
          (fun q => if q ∈ T then 1 else 0)) := by
    intro T hT
    have hTe : j ∉ T.erase j := Finset.notMem_erase j T
    have hsplit' : twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun q => (Scheme.Modules.pullback i).obj (L' q))
          (fun q => if q ∈ T then 1 else 0) ≅
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
            (Z.presheaf) (forget₂ CommRingCat RingCat) (Z.ringCatSheaf.2)⟩).obj ((twistedSheaf
            (SheafOfModules.unit Z.ringCatSheaf)
            (fun q => (Scheme.Modules.pullback i).obj (L' q))
            (fun q => if q ∈ T.erase j then 1 else 0)))).obj
            (((Scheme.Modules.pullback i).obj (L' j)))) :=
      twistedSheafSplitIso _ _ j (by simp [hT]) fun q hq => by simp [Finset.mem_erase, hq]
    have hsplit : twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun q => (Scheme.Modules.pullback i).obj (L q))
          (fun q => if q ∈ T then 1 else 0) ≅
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
            (Z.presheaf) (forget₂ CommRingCat RingCat) (Z.ringCatSheaf.2)⟩).obj ((twistedSheaf
            (SheafOfModules.unit Z.ringCatSheaf)
            (fun q => (Scheme.Modules.pullback i).obj (L q))
            (fun q => if q ∈ T.erase j then 1 else 0)))).obj
            (((Scheme.Modules.pullback i).obj (L j)))) :=
      twistedSheafSplitIso _ _ j (by simp [hT]) fun q hq => by simp [Finset.mem_erase, hq]
    have heq := twistedSheaf_pullback_eq_of_eq_off i L' L (fun q => if q ∈ T.erase j then 1 else 0)
      j (by simp [hTe]) hL'
    exact chiOverField_eq_of_iso k (i ≫ f)
      (hcons T ≪≫
        tensorProductIso Z.presheaf Z.ringCatSheaf.2 hsplit'
          (Iso.refl ((Scheme.Modules.pullback i).obj (L'' j))) ≪≫
        tensorProductAssociator Z.presheaf Z.ringCatSheaf.2 _
          ((Scheme.Modules.pullback i).obj (L' j)) ((Scheme.Modules.pullback i).obj (L'' j)) ≪≫
        tensorProductIso Z.presheaf Z.ringCatSheaf.2 (eqToIso heq)
          (((Scheme.Modules.pullback i).mapIso hj ≪≫
            pullbackTensorObjIso i (L' j) (L'' j)).symm) ≪≫
        hsplit.symm)
  have hnotMem : ∀ T : Finset (Fin d), j ∉ T →
      chiOverField k (i ≫ f) (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun t => (Scheme.Modules.pullback i).obj
            (Fin.cons (α := fun _ => X.Modules) (L'' j) L' t))
          (Fin.cons 1 fun q => if q ∈ T then 1 else 0)) =
        chiOverField k (i ≫ f) (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun q => (Scheme.Modules.pullback i).obj (L'' q))
          (fun q => if q ∈ insert j T then 1 else 0)) := by
    intro T hT
    have heq := twistedSheaf_pullback_eq_of_eq_off i L' L'' (fun q => if q ∈ T then 1 else 0)
      j (by simp [hT]) fun q hq => (hL' q hq).trans (hL'' q hq).symm
    have hsplit : twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun q => (Scheme.Modules.pullback i).obj (L'' q))
          (fun q => if q ∈ insert j T then 1 else 0) ≅
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
            (Z.presheaf) (forget₂ CommRingCat RingCat) (Z.ringCatSheaf.2)⟩).obj ((twistedSheaf
            (SheafOfModules.unit Z.ringCatSheaf)
            (fun q => (Scheme.Modules.pullback i).obj (L'' q))
            (fun q => if q ∈ T then 1 else 0)))).obj (((Scheme.Modules.pullback i).obj (L'' j)))) :=
      twistedSheafSplitIso _ _ j (by simp [hT]) fun q hq => by simp [Finset.mem_insert, hq]
    exact chiOverField_eq_of_iso k (i ≫ f)
      (hcons T ≪≫
        tensorProductIso Z.presheaf Z.ringCatSheaf.2 (eqToIso heq)
          (Iso.refl ((Scheme.Modules.pullback i).obj (L'' j))) ≪≫
        hsplit.symm)
  have hagree : ∀ T : Finset (Fin d), j ∉ T →
      chiOverField k (i ≫ f) (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun q => (Scheme.Modules.pullback i).obj (L q))
          (fun q => if q ∈ T then 1 else 0)) =
        chiOverField k (i ≫ f) (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun q => (Scheme.Modules.pullback i).obj (L'' q))
          (fun q => if q ∈ T then 1 else 0)) := by
    intro T hT
    exact congrArg (chiOverField k (i ≫ f))
      (twistedSheaf_pullback_eq_of_eq_off i L L'' (fun q => if q ∈ T then 1 else 0) j
        (by simp [hT]) fun q hq => (hL'' q hq).symm)
  rw [intersectionNumber_eq_sum_chiOverField k f i d hd L,
    intersectionNumber_eq_sum_chiOverField k f i d hd L',
    intersectionNumber_eq_sum_chiOverField k f i d hd L'']
  exact sum_neg_one_pow_mul_eq_add_of_sum_sub_eq_zero j
    (fun T => chiOverField k (i ≫ f) (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
      (fun t => (Scheme.Modules.pullback i).obj
        (Fin.cons (α := fun _ => X.Modules) (L'' j) L' t))
      (Fin.cons 1 fun q => if q ∈ T then 1 else 0))) _ _ _ hsum hmem hnotMem hagree

/-- **[Stacks, Tag 0BER], the `Function.update` form.**  If `𝓛_j ≅ 𝓜 ⊗ 𝓝` then

`(𝓛_1 ⋯ 𝓛_j ⋯ 𝓛_d · Z) = (𝓛_1 ⋯ 𝓜 ⋯ 𝓛_d · Z) + (𝓛_1 ⋯ 𝓝 ⋯ 𝓛_d · Z)`,

the two families on the right being the given one with its `j`-th member replaced. -/
@[stacks 0BER "additivity in the j-th slot, written with Function.update"]
public theorem intersectionNumber_update_tensor (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (j : Fin d) (L : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)] (M N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (hj : L j ≅ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.2)⟩).obj (M)).obj (N))) :
    intersectionNumber k f i d hd L =
      intersectionNumber k f i d hd (Function.update L j M) +
        intersectionNumber k f i d hd (Function.update L j N) :=
  intersectionNumber_tensor k f i d hd j L (Function.update L j M) (Function.update L j N)
    (fun q hq => Function.update_of_ne hq _ _) (fun q hq => Function.update_of_ne hq _ _)
    (by simpa only [Function.update_self] using hj)

end AlgebraicGeometry

end
