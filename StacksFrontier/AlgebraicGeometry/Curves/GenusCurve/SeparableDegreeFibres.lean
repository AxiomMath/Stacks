module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Geometric
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs

/-!
# Separable degree and the fibres of a proper curve over its field of global functions

Let `k` be a field, let `C` be a proper curve over `k`, and let `κ = Γ(C, ⊤)` be its ring of
global regular functions, a finite field extension of `k`. The genus of a proper scheme over a
field, `dim H¹` of its structure sheaf, is unchanged by base change along an arbitrary embedding
of fields; in particular each fibre `C_t` of `C ⟶ Spec κ` over a `k`-embedding `t : κ →ₐ[k] k̄`
has `dim_{k̄} H¹(C_t, 𝒪) = dim_κ H¹(C, 𝒪_C)`. A sum of numbers indexed by the `k`-embeddings of
`κ` into an algebraically closed field, each at most `g`, is at most `[κ : k]_s · g`. Together
these bound the geometric genus of `C/k` by `[κ : k]_s · dim_κ H¹(C, 𝒪_C)`, the inequality of
Stacks 0CE5, given a decomposition of the geometric genus over the fibres and a bound of the
geometric genus of each fibre by its genus.

## Main results

* `Field.finsum_le_finSepDegree_mul`: a sum indexed by the `F`-algebra maps from a finite
  extension `E` into an algebraically closed field, with all terms at most `g`, is at most
  `Field.finSepDegree F E * g`.
* `AlgebraicGeometry.genus_eq_of_isPullback`: the genus of a proper scheme over a field is
  unchanged by base change along an arbitrary embedding of fields.
* `AlgebraicGeometry.genus_pullback_snd_eq`: the same statement for the chosen categorical
  pullback.
* `AlgebraicGeometry.genus_pullback_snd_toSpecΓ_eq`: for `C` proper and integral over `k`, every
  fibre of `C ⟶ Spec Γ(C, ⊤)` over a `k`-embedding of `Γ(C, ⊤)` into an algebraic closure of `k`
  has the genus of `C` over `Γ(C, ⊤)`.
* `AlgebraicGeometry.geometricGenus_le_finSepDegree_mul_genus_toSpecΓ_of_fibreDecomposition`:
  the inequality of Stacks 0CE5, deduced from two further statements supplied as hypotheses.

## References

* [Stacks Project, Tag 0CE5](https://stacks.math.columbia.edu/tag/0CE5)
* [Stacks Project, Tag 0CE3](https://stacks.math.columbia.edu/tag/0CE3)
* [Stacks Project, Tag 0CDV](https://stacks.math.columbia.edu/tag/0CDV)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 09HJ](https://stacks.math.columbia.edu/tag/09HJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.AlgebraicGeometry.ProperGeomConnected

universe u

namespace Field

/-- If every term of a family of natural numbers indexed by the `F`-algebra maps from a finite
extension `E/F` into an algebraically closed field `L` is at most `g`, then the sum of the family
is at most `[E : F]_s * g`. -/
theorem finsum_le_finSepDegree_mul (F E : Type u) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (L : Type u) [Field L] [Algebra F L] [IsAlgClosed L]
    (G : (E →ₐ[F] L) → ℕ) (g : ℕ) (hle : ∀ t, G t ≤ g) :
    ∑ᶠ t, G t ≤ Field.finSepDegree F E * g := by
  let : Fintype (E →ₐ[F] L) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, Field.finSepDegree_eq_of_isAlgClosed F E L,
    Nat.card_eq_fintype_card]
  calc ∑ t, G t ≤ (Finset.univ : Finset (E →ₐ[F] L)).card • g :=
        Finset.sum_le_card_nsmul _ _ _ fun x _ ↦ hle x
    _ = Fintype.card (E →ₐ[F] L) * g := by rw [Finset.card_univ, smul_eq_mul]

end Field

namespace AlgebraicGeometry

/-- The genus of a proper scheme over a field is unchanged by base change along an arbitrary
embedding of fields `φ : κ →+* L`. -/
theorem genus_eq_of_isPullback (κ L : Type u) [Field κ] [Field L] (φ : κ →+* L)
    {X' X : Scheme.{u}} (g' : X' ⟶ X) (p' : X' ⟶ Spec (.of L)) (p : X ⟶ Spec (.of κ))
    (h : IsPullback g' p' p (Spec.map (CommRingCat.ofHom φ))) [IsProper p] :
    genus p' = genus p := by
  let : Algebra κ L := φ.toAlgebra
  exact genus_baseChange κ L g' p' p h

/-- The genus of a proper scheme over a field is unchanged by base change along an arbitrary
embedding of fields, stated for the chosen categorical pullback. -/
theorem genus_pullback_snd_eq (κ L : Type u) [Field κ] [Field L] (φ : κ →+* L)
    {X : Scheme.{u}} (p : X ⟶ Spec (.of κ)) [IsProper p] :
    genus (pullback.snd p (Spec.map (CommRingCat.ofHom φ))) = genus p :=
  genus_eq_of_isPullback κ L φ _ _ p (IsPullback.of_hasPullback _ _)

/-- For `C` proper and integral over a field `k`, the fibre of `C ⟶ Spec Γ(C, ⊤)` over a
`k`-embedding `t` of `Γ(C, ⊤)` into an algebraic closure of `k` has the same genus as `C` over
`Γ(C, ⊤)`, namely `dim_{k̄} H¹(C_t, 𝒪) = dim_{Γ(C, ⊤)} H¹(C, 𝒪_C)`. -/
theorem genus_pullback_snd_toSpecΓ_eq (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsProper f] [IsIntegral C] :
    letI : Field Γ(C, ⊤) := (isField_of_universallyClosed k f).toField
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    letI : IsProper C.toSpecΓ := isProper_toSpecΓ f
    ∀ t : Γ(C, ⊤) →ₐ[k] AlgebraicClosure k,
      genus (pullback.snd C.toSpecΓ (Spec.map (CommRingCat.ofHom t.toRingHom))) =
        genus C.toSpecΓ := by
  let : Field Γ(C, ⊤) := (isField_of_universallyClosed k f).toField
  let : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  let : IsProper C.toSpecΓ := isProper_toSpecΓ f
  exact fun t ↦ genus_pullback_snd_eq Γ(C, ⊤) (AlgebraicClosure k) t.toRingHom C.toSpecΓ

/-- For a proper curve `C` over a field `k` with field of global functions `κ = Γ(C, ⊤)`, the
geometric genus of `C/k` is at most `[κ : k]_s · dim_κ H¹(C, 𝒪_C)`, provided the geometric genus
of `C/k` is the sum `hsum` of the geometric genera of the fibres of `C ⟶ Spec κ` over the
`k`-embeddings of `κ` into an algebraic closure of `k`, and the geometric genus of each such fibre
is at most its genus. -/
theorem geometricGenus_le_finSepDegree_mul_genus_toSpecΓ_of_fibreDecomposition
    (k : Type u) [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProper f] :
    letI : Field Γ(C, ⊤) := (isField_of_universallyClosed k f).toField
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    letI : IsProper C.toSpecΓ := isProper_toSpecΓ f
    (hsum : geometricGenus k f =
      ∑ᶠ t : Γ(C, ⊤) →ₐ[k] AlgebraicClosure k,
        geometricGenus (AlgebraicClosure k)
          (pullback.snd C.toSpecΓ (Spec.map (CommRingCat.ofHom t.toRingHom)))) →
    (∀ t : Γ(C, ⊤) →ₐ[k] AlgebraicClosure k,
      geometricGenus (AlgebraicClosure k)
          (pullback.snd C.toSpecΓ (Spec.map (CommRingCat.ofHom t.toRingHom))) ≤
        genus (pullback.snd C.toSpecΓ (Spec.map (CommRingCat.ofHom t.toRingHom)))) →
    geometricGenus k f ≤ Field.finSepDegree k Γ(C, ⊤) * genus C.toSpecΓ := by
  let : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  let : Field Γ(C, ⊤) := (isField_of_universallyClosed k f).toField
  let : Module.Finite k Γ(C, ⊤) := by
    rw [← RingHom.finite_algebraMap]
    exact (finite_appTop_of_universallyClosed k f).comp
      (RingHom.Finite.of_surjective ((Scheme.ΓSpecIso (.of k)).inv.hom) fun x ↦
        ⟨(Scheme.ΓSpecIso (.of k)).hom.hom x, by simp⟩)
  let : IsProper C.toSpecΓ := isProper_toSpecΓ f
  intro hsum hbound
  rw [hsum]
  exact Field.finsum_le_finSepDegree_mul k Γ(C, ⊤) (AlgebraicClosure k) _ _
    fun t ↦ (hbound t).trans_eq (genus_pullback_snd_toSpecΓ_eq k f t)

end AlgebraicGeometry

end
