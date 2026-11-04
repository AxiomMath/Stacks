module

public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormulaGeneral
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSite
public import StacksCore.Tactic.StacksAttribute

/-!
# The bound `d_V` of Stacks 0DC6 is an integer

Stacks 0DC6 takes for `S` the spectrum of a finite field, of a separably closed field, of a
strictly henselian Noetherian local ring, or of a henselian Noetherian local ring with finite
residue field, and attaches to every quasi-compact scheme `V` locally of finite type over `S`
the number

`d_V = 1 + 2 dim(S) + sup_{v ∈ V} (trdeg_{κ(s)} κ(v) + 2 dim 𝒪_{V, v})`,

which condition (3) of the unbounded cohomological descent of Stacks 0DC1 (Tag 0DC4) requires
to be an integer.  This file records the four types of base and proves that for each of them,
and every quasi-compact `V` locally of finite type over it, `d_V` is a natural number.

## Main definitions

* `AlgebraicGeometry.Scheme.IsUnboundedDescentEtaleBase`: `S` is of one of the four types listed
  in Stacks 0DC6.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_natCast_eq_etaleCohomologyBound`: for `f : X ⟶ S`
  locally of finite type, `X` quasi-compact and `S` nonempty, locally Noetherian and of finite
  dimension, the bound `1 + 2 dim S + sup_x (trdeg_{κ(f x)} κ(x) + 2 dim 𝒪_{X, x})` is a natural
  number.
* `AlgebraicGeometry.Scheme.IsUnboundedDescentEtaleBase.exists_natCast_eq_etaleCohomologyBound`:
  for `S` of one of the four types and `V` a quasi-compact object of the locally-finite-type
  étale site over `S`, the bound `d_V` is a natural number.

## Implementation notes

The proof is the dimension formula.  A quasi-compact scheme locally of finite type over a
locally Noetherian scheme is Noetherian, so it has finitely many generic points, at each of which
the residue-field transcendence degree is finite; call `E` their maximum.  The dimension formula
`dim 𝒪_{X, x} + trdeg κ(x) ≤ dim 𝒪_{S, f x} + E` then bounds every term of the supremum by
`2 (dim S + E)`.

The four types of base are stated as in the source; each is the spectrum of a Noetherian local
ring (a field being one), which is all that the integrality of `d_V` uses.

Only the integrality of `d_V` is treated here; the vanishing `H^p(V_i, F) = 0` for `p > d_V`,
which the source deduces from Gabber's theorem on cohomological dimension, is a separate statement.

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
* [Stacks Project, Tag 0DC4](https://stacks.math.columbia.edu/tag/0DC4)
* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- An element of `WithBot ℕ∞` which is nonnegative and finite is a natural number. -/
private lemma exists_natCast_of_nonneg_of_ne_top {a : WithBot ℕ∞} (h0 : 0 ≤ a) (ht : a ≠ ⊤) :
    ∃ n : ℕ, a = n := by
  induction a using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe e =>
    have he : e ≠ ⊤ := fun h ↦ ht (by simp [h])
    obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp he
    exact ⟨n, rfl⟩

/-- An element of `WithBot ℕ∞` which is nonnegative and bounded by a natural number is a
natural number. -/
private lemma exists_natCast_of_nonneg_of_le {a : WithBot ℕ∞} {N : ℕ} (h0 : 0 ≤ a)
    (hN : a ≤ N) : ∃ n : ℕ, a = n :=
  exists_natCast_of_nonneg_of_ne_top h0
    (ne_top_of_le_ne_top (by
      rw [← WithBot.coe_natCast, ← WithBot.coe_top]
      exact WithBot.coe_injective.ne (ENat.natCast_ne_top N)) hN)

/-- The dimension of a local ring of a scheme is at most the dimension of the scheme. -/
@[ega "IV 5.1.4" "partial"]
private lemma ringKrullDim_stalk_le {X : Scheme.{u}} (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
  exact le_iSup_of_le x le_rfl

/-- **The bound of Stacks 0DC6 is finite.**  Let `f : X ⟶ S` be locally of finite type, with
`X` quasi-compact and `S` nonempty, locally Noetherian and of finite dimension.  Then
`1 + 2 dim S + sup_x (trdeg_{κ(f x)} κ(x) + 2 dim 𝒪_{X, x})` is a natural number. -/
theorem Hom.exists_natCast_eq_etaleCohomologyBound {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [CompactSpace X] [Nonempty S]
    (hS : topologicalKrullDim S ≠ ⊤) :
    ∃ d : ℕ, f.etaleCohomologyBound = d := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := ⟨⟩
  -- the dimension of `S` is a natural number `N`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, topologicalKrullDim S = N := by
    obtain ⟨s⟩ := ‹Nonempty S›
    exact exists_natCast_of_nonneg_of_ne_top
      ((ringKrullDim_nonneg_of_nontrivial).trans (ringKrullDim_stalk_le s)) hS
  -- the transcendence degree at a point
  let tr : X → ℕ∞ := fun x ↦ let := (f.residueFieldMap x).hom.toAlgebra
    Cardinal.toENat (Algebra.trdeg (S.residueField (f.base x)) (X.residueField x))
  have htr : ∀ x, ∃ t : ℕ, tr x = t := fun x ↦ by
    let := (f.residueFieldMap x).hom.toAlgebra
    obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.mp (trdeg_residueField_lt_aleph0 f x)
    exact ⟨t, by simp only [tr, ht, Cardinal.toENat_nat]⟩
  -- the maximum `E` of the transcendence degrees at the finitely many generic points
  have hfin : (genericPoints X).Finite :=
    genericPoints.finite (finite_irreducibleComponents_of_isNoetherian (X := X))
  let E : ℕ := hfin.toFinset.sup fun η ↦ (tr η).toNat
  have hE : ∀ η : X, η ∈ genericPoints X → tr η ≤ (E : ℕ∞) := by
    intro η hη
    obtain ⟨t, ht⟩ := htr η
    have : (tr η).toNat ≤ E := Finset.le_sup (f := fun η ↦ (tr η).toNat)
      (hfin.mem_toFinset.mpr hη)
    rw [ht] at this ⊢
    exact_mod_cast this
  -- every term of the supremum is at most `2 (N + E)`
  have hterm : ∀ x : X, (tr x : WithBot ℕ∞) + 2 * ringKrullDim (X.presheaf.stalk x) ≤
      ((2 * (N + E) : ℕ) : WithBot ℕ∞) := by
    intro x
    have hform := ringKrullDim_stalk_add_trdeg_le_of_forall_genericPoints f x (E : ℕ∞)
      (fun η hη _ ↦ by simpa only [tr] using hE η hη)
    have hS' : ringKrullDim (S.presheaf.stalk (f.base x)) ≤ (N : WithBot ℕ∞) :=
      hN ▸ ringKrullDim_stalk_le (f.base x)
    obtain ⟨t, ht⟩ := htr x
    have hle :
        ringKrullDim (X.presheaf.stalk x) + (t : WithBot ℕ∞) ≤ ((N + E : ℕ) : WithBot ℕ∞) := by
      have h1 : ringKrullDim (X.presheaf.stalk x) + (tr x : WithBot ℕ∞) ≤
          ringKrullDim (S.presheaf.stalk (f.base x)) + ((E : ℕ∞) : WithBot ℕ∞) := hform
      rw [ht] at h1
      refine h1.trans ?_
      have := add_le_add hS' (le_refl ((E : ℕ∞) : WithBot ℕ∞))
      refine this.trans (le_of_eq ?_)
      push_cast
      rfl
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) :=
      ringKrullDim_nonneg_of_nontrivial
    obtain ⟨d, hd⟩ := exists_natCast_of_nonneg_of_le h0
      ((le_add_of_nonneg_right (by simp)).trans hle)
    rw [hd] at hle ⊢
    rw [ht]
    have hle' : d + t ≤ N + E := by exact_mod_cast hle
    have : t + 2 * d ≤ 2 * (N + E) := by omega
    rw [WithBot.coe_natCast]
    exact_mod_cast this
  -- hence the joined supremum is a natural number `k`
  have hsup0 : (0 : WithBot ℕ∞) ≤ 0 ⊔ ⨆ x : X, ((tr x : WithBot ℕ∞) +
      2 * ringKrullDim (X.presheaf.stalk x)) := le_sup_left
  have hsupN : 0 ⊔ (⨆ x : X, ((tr x : WithBot ℕ∞) + 2 * ringKrullDim (X.presheaf.stalk x))) ≤
      ((2 * (N + E) : ℕ) : WithBot ℕ∞) :=
    sup_le (by positivity) (iSup_le hterm)
  obtain ⟨k, hk⟩ := exists_natCast_of_nonneg_of_le hsup0 hsupN
  refine ⟨1 + 2 * N + k, ?_⟩
  show 1 + 2 * topologicalKrullDim S + (0 ⊔ ⨆ x : X, ((tr x : WithBot ℕ∞) +
      2 * ringKrullDim (X.presheaf.stalk x))) = _
  rw [hk, hN]
  push_cast
  rfl

/-- **The types of base scheme of Stacks 0DC6.**  `S` is the spectrum of a finite field, the
spectrum of a separably closed field, the spectrum of a strictly henselian Noetherian local ring,
or the spectrum of a henselian Noetherian local ring with finite residue field. -/
@[stacks 0DC6 "the four types of base scheme S"]
def IsUnboundedDescentEtaleBase (S : Scheme.{u}) : Prop :=
  (∃ (k : Type u) (_ : Field k), Finite k ∧ Nonempty (S ≅ Spec (.of k))) ∨
  (∃ (k : Type u) (_ : Field k), IsSepClosed k ∧ Nonempty (S ≅ Spec (.of k))) ∨
  (∃ (A : Type u) (_ : CommRing A) (_ : HenselianLocalRing A), IsNoetherianRing A ∧
    IsSepClosed (IsLocalRing.ResidueField A) ∧ Nonempty (S ≅ Spec (.of A))) ∨
  (∃ (A : Type u) (_ : CommRing A) (_ : HenselianLocalRing A), IsNoetherianRing A ∧
    Finite (IsLocalRing.ResidueField A) ∧ Nonempty (S ≅ Spec (.of A)))

namespace IsUnboundedDescentEtaleBase

/-- The spectrum of a Noetherian local ring is nonempty, locally Noetherian and of finite
dimension. -/
private lemma of_spec (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {S : Scheme.{u}} (e : S ≅ Spec (.of A)) :
    IsLocallyNoetherian S ∧ Nonempty S ∧ topologicalKrullDim S ≠ ⊤ := by
  have hS : IsLocallyNoetherian S := isLocallyNoetherian_of_isOpenImmersion e.hom
  refine ⟨hS, ⟨e.inv.base (IsLocalRing.closedPoint A)⟩, ?_⟩
  have hhomeo : IsHomeomorph e.hom.base :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isHomeomorph
  rw [hhomeo.topologicalKrullDim_eq]
  show topologicalKrullDim (PrimeSpectrum A) ≠ ⊤
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (ringKrullDim_lt_top (R := A)).ne

/-- A base of one of the four types of Stacks 0DC6 is nonempty, locally Noetherian and of finite
dimension. -/
theorem isLocallyNoetherian_and_nonempty_and_ne_top {S : Scheme.{u}}
    (hS : IsUnboundedDescentEtaleBase S) :
    IsLocallyNoetherian S ∧ Nonempty S ∧ topologicalKrullDim S ≠ ⊤ := by
  rcases hS with ⟨k, _, -, ⟨e⟩⟩ | ⟨k, _, -, ⟨e⟩⟩ | ⟨A, _, _, _, -, ⟨e⟩⟩ | ⟨A, _, _, _, -, ⟨e⟩⟩ <;>
    exact of_spec _ e

/-- **The bound `d_V` of Stacks 0DC6 is an integer.**  For `S` of one of the four types of
Stacks 0DC6 and `V` a quasi-compact scheme locally of finite type over `S`, the bound
`d_V = 1 + 2 dim(S) + sup_{v ∈ V} (trdeg_{κ(s)} κ(v) + 2 dim 𝒪_{V, v})` is a natural number. -/
@[stacks 0DC6 "d_V is an integer for V in B"]
theorem exists_natCast_eq_etaleCohomologyBound {S : Scheme.{u}}
    (hS : IsUnboundedDescentEtaleBase S) (V : LocallyFiniteTypeEtale S)
    (hV : LocallyFiniteTypeEtale.IsQuasiCompact V) :
    ∃ d : ℕ, V.obj.hom.etaleCohomologyBound = d := by
  obtain ⟨h1, h2, h3⟩ := hS.isLocallyNoetherian_and_nonempty_and_ne_top
  have : LocallyOfFiniteType V.obj.hom := V.property
  have : CompactSpace V.obj.left := hV
  exact V.obj.hom.exists_natCast_eq_etaleCohomologyBound h3

end IsUnboundedDescentEtaleBase

end AlgebraicGeometry.Scheme

end
