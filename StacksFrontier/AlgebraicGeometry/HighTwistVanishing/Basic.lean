module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.Twist
public import StacksFrontier.AlgebraicGeometry.HighTwistDevissage.AffineFromNegativeTwists
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.LongExactSequence

/-!
# Eventual vanishing of the higher cohomology of the twists of a module

Clause (2) of the cohomological criterion for ampleness, [Stacks, Tag 0B5U], is a property of a
single `𝒪_X`-module `ℱ`:

> there is an `n₀` with `Hᵖ(X, ℱ ⊗ L^{⊗ n}) = 0` for every `n ≥ n₀` and every `p > 0`.

This file names that property and proves the three closure conditions that the cohomological
dévissage [Stacks, Tag 01YM] asks of it: it holds on the zero module, it is stable under
extensions, and it descends from a finite self-product. Together with the isomorphism invariance
also proved here, these are hypotheses (a), (b) and (c) of 01YM for this property, and they are
exactly the part of the converse of [Stacks, Tag 0B5V] that needs no geometry.

## Main definitions

* `Stacks.HighTwistVanishing.HasHighTwistVanishing`: the property displayed above.

## Main results

* `Stacks.HighTwistVanishing.of_iso`: the property is an isomorphism invariant.
* `Stacks.HighTwistVanishing.terminal`: it holds on the zero module `⊤_ X.Modules`.
* `Stacks.HighTwistVanishing.of_shortExact`: it is stable under extensions — if it holds on the
  outer terms of a short exact sequence it holds on the middle term.
* `Stacks.HighTwistVanishing.of_finiteProduct`: it descends from a finite self-product, i.e. if
  it holds on `ℱ^{×(m+1)}` then it holds on `ℱ`.

## Implementation notes

**Why these proofs are short.** The δ-functor presentation of the repository's cohomology does
all the work. `Stacks.SerreAffinenessCriterion.isZero_hgroup_of_shortExact` is the long exact
sequence read as "vanishing on the outer terms forces it in the middle", for an arbitrary short
exact sequence of `𝒪_X`-modules over an arbitrary open and with no quasi-coherence hypothesis, and
`Stacks.AmpleCohomologicalCriterion.shortExact_map_tensorRight` says that tensoring a short
exact sequence by an invertible module is again short exact, because tensoring by an invertible
module is an
autoequivalence. Those two compose to `of_shortExact` with no derived-category bookkeeping: no
`Functor.rightDerivedPlus`, no comparison of `HomologicalComplex.extend` with a mapped complex,
and hence none of the transparency or heartbeat escapes that a direct derived-functor argument
needs. `of_finiteProduct` is a retract argument through the additive functor
`(- ⊗ L^{⊗ n}) ⋙ Hᵖ(X, -)` and needs nothing about `X` at all.

**The twist is on the right.** The tensor object in clause (2) of [Stacks, Tag 0B5U] is the
value at `ℱ` of `(Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).flip.obj (L^{⊗ n})`.
The functorial lemmas therefore apply to the stated form without transport.

**No `stacks` attribute is attached.** Hypotheses (a), (b) and (c) of [Stacks, Tag 01YM] are
steps inside the proof of a tag, not numbered results of the source, and the tags whose proofs
consume them — [Stacks, Tag 0B5U] and [Stacks, Tag 0B5V] — are each a single unlabelled
assertion, so there is no covering set here to earn either.

## References

* [Stacks Project, Tag 0B5U](https://stacks.math.columbia.edu/tag/0B5U)
* [Stacks Project, Tag 0B5V](https://stacks.math.columbia.edu/tag/0B5V)
* [Stacks Project, Tag 01YM](https://stacks.math.columbia.edu/tag/01YM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

open scoped Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

namespace Stacks.HighTwistVanishing

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **Clause (2) of [Stacks, Tag 0B5U] at a single module.** `HasHighTwistVanishing L ℱ` says
that beyond some degree `n₀` every twist `ℱ ⊗ L^{⊗ n}` has vanishing cohomology in every
positive degree. The tensor product is [Stacks, Tag 05NA]'s, the tensor powers are
[Stacks, Tag 01CU]'s through `Stacks.Ample.tensorPowModule`, and the cohomology is the
repository's `Hgroup`, the right derived functor of global sections. -/
def HasHighTwistVanishing (F : X.Modules) : Prop :=
  ∃ n₀ : ℕ, ∀ n q : ℕ, n₀ ≤ n → 0 < q →
    IsZero (Hgroup X.ringCatSheaf ⊤ q
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj
        (Stacks.Ample.tensorPowModule X L (n : ℤ))))

variable {L}

/-- **The property is an isomorphism invariant.** Isomorphic modules have isomorphic twists, and
`Hᵖ(X, -)` is a functor. -/
theorem of_iso {F G : X.Modules} (e : F ≅ G) (hF : HasHighTwistVanishing L F) :
    HasHighTwistVanishing L G := by
  obtain ⟨n₀, hn₀⟩ := hF
  refine ⟨n₀, fun n q hn hq ↦ ?_⟩
  exact (Iso.isZero_iff ((Hfunctor X.ringCatSheaf ⊤ q).mapIso
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj
      (Stacks.Ample.tensorPowModule X L (n : ℤ))).mapIso e))).mp (hn₀ n q hn hq)

/-- **Hypothesis (a) of [Stacks, Tag 01YM]: the property holds on the zero module.** Tensoring is
additive and `Hᵖ(X, -)` is additive, so both send the zero object to a zero object; `⊤_ X.Modules`
is a zero object because `X.Modules` is abelian. No bound on `n₀` is needed. -/
theorem terminal (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] :
    HasHighTwistVanishing L (⊤_ X.Modules) := by
  refine ⟨0, fun n q _ hq ↦ ?_⟩
  have htop : IsZero (⊤_ X.Modules) :=
    (isZero_zero X.Modules).of_iso HasZeroObject.zeroIsoTerminal.symm
  have _hadd : (Hfunctor X.ringCatSheaf ⊤ q).Additive :=
    Stacks.HighTwistDevissage.additive_hfunctor X ⊤ q
  have : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj
      (Stacks.Ample.tensorPowModule X L (n : ℤ))).Additive :=
    Functor.flip_obj_additive
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
      (Stacks.Ample.tensorPowModule X L (n : ℤ))
  exact (Hfunctor X.ringCatSheaf ⊤ q).map_isZero
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj
      (Stacks.Ample.tensorPowModule X L (n : ℤ))).map_isZero htop)

/-- **Hypothesis (b) of [Stacks, Tag 01YM]: the property is stable under extensions.** If the
outer terms of a short exact sequence of `𝒪_X`-modules satisfy it, so does the middle term; take
for `n₀` the maximum of the two bounds.

Tensoring the sequence by `L^{⊗ n}` keeps it short exact
(`Stacks.AmpleCohomologicalCriterion.shortExact_map_tensorRight`, since tensoring by an
invertible module is an autoequivalence), and then vanishing in the middle is the long exact
cohomology sequence
(`Stacks.SerreAffinenessCriterion.isZero_hgroup_of_shortExact`). Neither step asks for
quasi-coherence, and neither asks anything of `X`. -/
theorem of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : HasHighTwistVanishing L S.X₁) (h₃ : HasHighTwistVanishing L S.X₃) :
    HasHighTwistVanishing L S.X₂ := by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₃, hn₃⟩ := h₃
  refine ⟨max n₁ n₃, fun n q hn hq ↦ ?_⟩
  exact Stacks.SerreAffinenessCriterion.isZero_hgroup_of_shortExact X ⊤
    (Stacks.AmpleCohomologicalCriterion.shortExact_map_tensorRight X
      (Stacks.Ample.tensorPowModule X L (n : ℤ)) hS) q
    (hn₁ n q (le_trans (le_max_left n₁ n₃) hn) hq)
    (hn₃ n q (le_trans (le_max_right n₁ n₃) hn) hq)

/-- **A zero object is detected through any retract.** If `A` is a retract of `B` and `Φ B` is
zero for a functor `Φ` into a category with zero morphisms, then `Φ A` is zero. -/
theorem isZero_of_retract {C D : Type*} [Category C] [Category D] [HasZeroMorphisms D]
    (Φ : C ⥤ D) {A B : C} (i : A ⟶ B) (p : B ⟶ A) (hip : i ≫ p = 𝟙 A)
    (hB : IsZero (Φ.obj B)) : IsZero (Φ.obj A) := by
  rw [IsZero.iff_id_eq_zero, ← Φ.map_id, ← hip, Φ.map_comp, hB.eq_zero_of_tgt (Φ.map i),
    zero_comp]

/-- **Hypothesis (c) of [Stacks, Tag 01YM]: the property descends from a finite self-product.**
If `ℱ^{×(m+1)}` satisfies it then so does `ℱ`, with the same bound.

`ℱ` is a retract of `ℱ^{×(m+1)}` — the diagonal followed by any projection is the identity — and
a retract is carried to a retract by the composite functor `(- ⊗ L^{⊗ n}) ⋙ Hᵖ(X, -)`, under
which the product is sent to a zero object. -/
theorem of_finiteProduct {m : ℕ} (F : X.Modules)
    (hvan : HasHighTwistVanishing L (∏ᶜ fun _ : Fin (m + 1) => F)) :
    HasHighTwistVanishing L F := by
  obtain ⟨n₀, hn₀⟩ := hvan
  refine ⟨n₀, fun n q hn hq ↦ ?_⟩
  exact isZero_of_retract
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj
      (Stacks.Ample.tensorPowModule X L (n : ℤ)) ⋙ Hfunctor X.ringCatSheaf ⊤ q)
    (Pi.lift fun _ : Fin (m + 1) => 𝟙 F)
    (Pi.π (fun _ : Fin (m + 1) => F) ⟨0, Nat.succ_pos m⟩)
    (Pi.lift_comp_π _ _) (hn₀ n q hn hq)

end Stacks.HighTwistVanishing

end
