module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusLeGenusUnconditional
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusTensorFibres
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SeparableDegreeFibres

/-!
# Stacks 0CE5

`AlgebraicGeometry.geometricGenus_le_finSepDegree_mul_genus_toSpecΓ_of_fibreDecomposition`
reduces [Stacks, Tag 0CE5] to two hypotheses: the decomposition `hsum` of the geometric genus
over the `k`-embeddings of `κ = Γ(C, ⊤)` into an algebraic closure of `k`, and a bound for the
geometric genus of each fibre by its genus.  This file discharges both and so proves the tag.

The decomposition comes from
`AlgebraicGeometry.geometricGenus_eq_finsum_geometricGenus_pullback_snd`, specialised to the
canonical factorization `C ⟶ Spec Γ(C, ⊤) ⟶ Spec k` of the structure morphism of a proper curve.
The per-fibre bound is `AlgebraicGeometry.geometricGenus_le_genus_of_dim_le_one`, applied to the
fibre of `C ⟶ Spec Γ(C, ⊤)` over an embedding `t`; the fibre is a proper scheme over an
algebraically closed field, and extension of the ground field does not change the dimension, so
it has dimension one like `C`.

## Main results

* `AlgebraicGeometry.geometricGenus_eq_finsum_geometricGenus_pullback_snd_toSpecΓ`: the
  decomposition `hsum`, for the fibres of `C ⟶ Spec Γ(C, ⊤)`.
* `AlgebraicGeometry.geometricGenus_le_finSepDegree_mul_genus_toSpecΓ_of_fibreBound`: [Stacks,
  Tag 0CE5] granted the per-fibre bound — for a proper curve `C` over `k` with `κ = Γ(C, ⊤)`, if
  every fibre of `C ⟶ Spec κ` over a `k`-embedding `κ → k̄` has geometric genus at most its
  genus, then `g_geom(C/k) ≤ [κ : k]_s · dim_κ H¹(C, 𝒪_C)`.
* `AlgebraicGeometry.topologicalKrullDim_pullback_snd_eq`: extension of the ground field along an
  arbitrary embedding of fields does not change the dimension.
* `AlgebraicGeometry.geometricGenus_le_finSepDegree_mul_genus_toSpecΓ_of_isCurve`: **[Stacks,
  Tag 0CE5]**, with no further hypothesis.

## Implementation notes

The field and algebra structures on `Γ(C, ⊤)` and the properness of `C.toSpecΓ` are introduced at
the level of the statement, as in
`StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SeparableDegreeFibres`; finite-dimensionality of
`Γ(C, ⊤)` over `k`, which the decomposition needs, comes from
`AlgebraicGeometry.finite_appTop_of_universallyClosed` together with the surjectivity of
`(Scheme.ΓSpecIso (.of k)).inv`.  That the canonical morphism to `Spec Γ(C, ⊤)` does factor the
structure morphism is `AlgebraicGeometry.Scheme.toSpecΓ_naturality`, exactly as in the proof of
`AlgebraicGeometry.genus_toSpecΓ_eq_genus`.

## References

* [Stacks Project, Tag 0CE5](https://stacks.math.columbia.edu/tag/0CE5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.AlgebraicGeometry.ProperGeomConnected

universe u

namespace AlgebraicGeometry

/-- **The decomposition `hsum` of [Stacks, Tag 0CE5].**  For a proper curve `C` over a field `k`
with field of global functions `κ = Γ(C, ⊤)`, the geometric genus of `C` over `k` is the sum, over
the `k`-embeddings `t` of `κ` into an algebraic closure of `k`, of the geometric genera of the
fibres of `C ⟶ Spec κ` over `t`. -/
public theorem geometricGenus_eq_finsum_geometricGenus_pullback_snd_toSpecΓ
    (k : Type u) [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProper f] :
    letI : Field Γ(C, ⊤) := (isField_of_universallyClosed k f).toField
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    letI : IsProper C.toSpecΓ := isProper_toSpecΓ f
    geometricGenus k f =
      ∑ᶠ t : Γ(C, ⊤) →ₐ[k] AlgebraicClosure k,
        geometricGenus (AlgebraicClosure k)
          (pullback.snd C.toSpecΓ (Spec.map (CommRingCat.ofHom t.toRingHom))) := by
  let : Field Γ(C, ⊤) := (isField_of_universallyClosed k f).toField
  let : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  let : Module.Finite k Γ(C, ⊤) := by
    rw [← RingHom.finite_algebraMap]
    exact (finite_appTop_of_universallyClosed k f).comp
      (RingHom.Finite.of_surjective ((Scheme.ΓSpecIso (.of k)).inv.hom) fun x ↦
        ⟨(Scheme.ΓSpecIso (.of k)).hom.hom x, by simp⟩)
  let : IsProper C.toSpecΓ := isProper_toSpecΓ f
  have hfh : C.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(C, ⊤))) = f := by
    show C.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) = f
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  exact geometricGenus_eq_finsum_geometricGenus_pullback_snd k Γ(C, ⊤) f C.toSpecΓ hfh
    (le_of_eq (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)))

/-- **[Stacks, Tag 0CE5] granted the per-fibre bound.**  Let `C` be a proper curve over a field
`k` and let `κ = Γ(C, ⊤)` be its field of global regular functions.  If every fibre of
`C ⟶ Spec κ` over a `k`-embedding of `κ` into an algebraic closure of `k` has geometric genus at
most its genus, then `g_geom(C/k) ≤ [κ : k]_s · dim_κ H¹(C, 𝒪_C)`.

This is `AlgebraicGeometry.geometricGenus_le_finSepDegree_mul_genus_toSpecΓ_of_fibreDecomposition`
with its decomposition hypothesis discharged by
`AlgebraicGeometry.geometricGenus_eq_finsum_geometricGenus_pullback_snd_toSpecΓ`. -/
public theorem geometricGenus_le_finSepDegree_mul_genus_toSpecΓ_of_fibreBound
    (k : Type u) [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProper f] :
    letI : Field Γ(C, ⊤) := (isField_of_universallyClosed k f).toField
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    letI : IsProper C.toSpecΓ := isProper_toSpecΓ f
    (∀ t : Γ(C, ⊤) →ₐ[k] AlgebraicClosure k,
      geometricGenus (AlgebraicClosure k)
          (pullback.snd C.toSpecΓ (Spec.map (CommRingCat.ofHom t.toRingHom))) ≤
        genus (pullback.snd C.toSpecΓ (Spec.map (CommRingCat.ofHom t.toRingHom)))) →
    geometricGenus k f ≤ Field.finSepDegree k Γ(C, ⊤) * genus C.toSpecΓ := by
  let : Field Γ(C, ⊤) := (isField_of_universallyClosed k f).toField
  let : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  let : IsProper C.toSpecΓ := isProper_toSpecΓ f
  exact geometricGenus_le_finSepDegree_mul_genus_toSpecΓ_of_fibreDecomposition k f
    (geometricGenus_eq_finsum_geometricGenus_pullback_snd_toSpecΓ k f)

/-- Extension of the ground field along an arbitrary embedding of fields `φ : κ →+* L` does not
change the dimension.  No `Algebra κ L` instance is presupposed, so the embedding may vary. -/
public theorem topologicalKrullDim_pullback_snd_eq (κ L : Type u) [Field κ] [Field L]
    (φ : κ →+* L) {X : Scheme.{u}} (p : X ⟶ Spec (.of κ)) [LocallyOfFiniteType p] :
    topologicalKrullDim (pullback (C := Scheme.{u}) p
        (Spec.map (CommRingCat.ofHom φ)) : Type u) =
      topologicalKrullDim (X : Type u) :=
  let : Algebra κ L := φ.toAlgebra
  topologicalKrullDim_baseChange κ L _ _ p (IsPullback.of_hasPullback _ _)

/-- **Stacks Project, Tag 0CE5.**  Let `C` be a proper curve over a field `k` and let
`κ = Γ(C, ⊤)` be its field of global regular functions.  Then the geometric genus of `C` over `k`
is at most `[κ : k]_s · dim_κ H¹(C, 𝒪_C)`.

The sum over the `k`-embeddings `κ → k̄` is
`AlgebraicGeometry.geometricGenus_eq_finsum_geometricGenus_pullback_snd_toSpecΓ`, and each of its
terms is bounded by the genus of the corresponding fibre by
`AlgebraicGeometry.geometricGenus_le_genus_of_dim_le_one`, the fibre being a proper scheme of
dimension one over the algebraically closed field `k̄`. -/
@[stacks 0CE5]
public theorem geometricGenus_le_finSepDegree_mul_genus_toSpecΓ_of_isCurve
    (k : Type u) [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProper f] :
    letI : Field Γ(C, ⊤) := (isField_of_universallyClosed k f).toField
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    letI : IsProper C.toSpecΓ := isProper_toSpecΓ f
    geometricGenus k f ≤ Field.finSepDegree k Γ(C, ⊤) * genus C.toSpecΓ := by
  let : Field Γ(C, ⊤) := (isField_of_universallyClosed k f).toField
  let : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  let : IsProper C.toSpecΓ := isProper_toSpecΓ f
  refine geometricGenus_le_finSepDegree_mul_genus_toSpecΓ_of_fibreBound k f fun t ↦
    geometricGenus_le_genus_of_dim_le_one (AlgebraicClosure k) _ ?_
  rw [topologicalKrullDim_pullback_snd_eq Γ(C, ⊤) (AlgebraicClosure k) t.toRingHom C.toSpecΓ]
  exact le_of_eq (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f))

end AlgebraicGeometry

end
