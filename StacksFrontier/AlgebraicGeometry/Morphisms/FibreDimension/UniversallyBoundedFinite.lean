module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Module
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms whose fibres are universally bounded

A bound on the degrees of the fibres of a morphism of schemes is produced here in two ways.

First, a finite locally free morphism of rank `d` has every fibre of degree `d`: a fibre is a
base change, and the rank of a finite locally free morphism is stable under base change.

Second, for a morphism of affine schemes coming from a ring map that makes the source ring a
finitely generated module over the target ring, the number of generators bounds the degrees of
the fibres. The fibre of such a morphism at a prime `p` is the spectrum of the fibre algebra
`κ(p) ⊗_A B`, a `κ(p)`-vector space spanned by the images of those generators, hence finite free
of rank at most their number.

## Main results

* `Module.IsFiniteLocallyFreeOfRank.of_basis`: a module with a basis indexed by `Fin n` is
  finite locally free of rank `n`.
* `Module.isFiniteLocallyFreeOfRank_of_field`: a finite-dimensional vector space over a field is
  finite locally free of rank its dimension.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_specMap_iff`: a morphism of spectra is finite
  locally free of rank `d` exactly when the source ring is a finite locally free module of rank
  `d` over the target ring.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_specMap_of_field`: the morphism of spectra induced
  by a finite-dimensional algebra over a field is finite locally free of rank the dimension of
  that algebra.
* `AlgebraicGeometry.hasUniversallyBoundedFibers_of_isFiniteLocallyFreeOfRank`: the rank of a
  finite locally free morphism bounds the degrees of its fibres.
* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_fiberToSpecResidueField_specMap`: the fibre of a
  morphism of spectra at a prime is finite locally free of rank the dimension of the fibre
  algebra.
* `AlgebraicGeometry.finrank_tensorProduct_le_of_span_eq_top`: a spanning family bounds the
  dimension of every field-valued base change.
* `AlgebraicGeometry.boundsFiberDegrees_specMap_of_span_eq_top` and
  `AlgebraicGeometry.boundsFiberDegrees_specMap_of_span_range_eq_top`: a spanning family of a
  given finite cardinality bounds the degrees of the fibres of a morphism of spectra by that
  cardinality.
* `AlgebraicGeometry.hasUniversallyBoundedFibers_specMap_of_finite`: a module-finite ring map
  induces a morphism of spectra with universally bounded fibres.

## Implementation notes

The covering family witnessing `Module.IsFiniteLocallyFreeOfRank` is taken to be the single
element `1`, whose away-localization is the ring itself; the basis is transported along
`Module.Basis.ofIsLocalizedModule`. The index type of the covering family lives in the same
universe as the ring, so `PUnit` rather than `Unit` is used.

Passing from the sheaf-level rank condition to the module-level one uses
`Stacks.Morphisms.sheafOfModules_isFiniteLocallyFreeOfRank_iff_module`, whose algebra structure
on the global sections of the source is the one induced by the morphism. For a morphism of
spectra that structure is identified with the given algebra structure through
`AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality`, which is what makes the inverse of
`AlgebraicGeometry.Scheme.ΓSpecIso` a linear equivalence.

The fibre of a morphism of spectra is identified with the spectrum of the fibre algebra by
Mathlib's `AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso`, an isomorphism of arrows; the rank
condition is transported across it as a morphism property, which respects isomorphisms. No
computation of the global sections of the fibre is needed.

The spanning family is indexed by an arbitrary finite type, in its own universe, rather than by
`Fin n`: the generating set supplied by `Module.Finite` is a `Finset`, so coercing it to `Fin` its
cardinality would add a reindexing step to every use, while `Fin n` lives in `Type 0` and so
cannot instantiate an index type constrained to the ring's universe. The `Fin n` form of the
statement, which is the one the source states, is recorded separately.

## References

* [Stacks Project, Tag 03J4](https://stacks.math.columbia.edu/tag/03J4)
* [Stacks Project, Tag 0CC2](https://stacks.math.columbia.edu/tag/0CC2)
* [Stacks Project, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

universe u v

/-- A module with a basis indexed by `Fin n` is finite locally free of rank `n`: the single
element `1` covers the spectrum, and the away-localization at `1` is the module itself.

`Module.IsFiniteLocallyFreeOfRank.of_basis'` is the same statement with the module left in a
universe unrelated to that of the ring. -/
public theorem Module.IsFiniteLocallyFreeOfRank.of_basis {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] {n : ℕ} (b : Module.Basis (Fin n) R M) :
    Module.IsFiniteLocallyFreeOfRank R M n := by
  classical
  refine ⟨PUnit, fun _ => 1, by simp, ?_⟩
  intro _
  let : Algebra R (Localization.Away (1 : R)) :=
    @OreLocalization.instAlgebra R _ (Submonoid.powers (1 : R)) _ R _ (Algebra.id R)
  let : IsLocalization (Submonoid.powers (1 : R)) (Localization.Away (1 : R)) :=
    Localization.isLocalization (R := R) (M := Submonoid.powers 1)
  exact ⟨b.ofIsLocalizedModule (Localization.Away (1 : R)) (Submonoid.powers (1 : R))
    (LocalizedModule.mkLinearMap (Submonoid.powers (1 : R)) M)⟩

/-- A finite-dimensional vector space over a field is finite locally free of rank its
dimension. -/
@[ega "IV 18.2.7" "partial"]
public theorem Module.isFiniteLocallyFreeOfRank_of_field {k : Type u} [Field k] (M : Type u)
    [AddCommGroup M] [Module k M] [Module.Finite k M] :
    Module.IsFiniteLocallyFreeOfRank k M (Module.finrank k M) :=
  .of_basis (Module.finBasis k M)

/-- A morphism of spectra is finite locally free of rank `d` exactly when the source ring is a
finite locally free module of rank `d` over the target ring. -/
public theorem Stacks.Morphisms.isFiniteLocallyFreeOfRank_specMap_iff {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] (d : ℕ) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        (Spec.map (CommRingCat.ofHom (algebraMap R A))) d ↔
      Module.IsFiniteLocallyFreeOfRank R A d := by
  set φ : CommRingCat.of R ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap R A) with hφ
  set f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) := Spec.map φ with hf
  have hnat : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop
      = φ ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).inv :=
    (Scheme.ΓSpecIso_inv_naturality φ).symm
  rw [Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff,
    and_iff_right (inferInstance : IsAffineHom f),
    Stacks.Morphisms.sheafOfModules_isFiniteLocallyFreeOfRank_iff_module f d]
  let _alg : Algebra R ↑Γ(Spec (CommRingCat.of A), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
  have hmap : ∀ c : R, algebraMap R ↑Γ(Spec (CommRingCat.of A), ⊤) c
      = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (algebraMap R A c) := by
    intro c
    show ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom c
      = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (algebraMap R A c)
    rw [hnat]
    rfl
  let ψ : A ≃+* ↑Γ(Spec (CommRingCat.of A), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
  let e : A ≃ₗ[R] ↑Γ(Spec (CommRingCat.of A), ⊤) :=
    { ψ.toAddEquiv with
      map_smul' := by
        intro c a
        show ψ (c • a) = c • ψ a
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, hmap c]
        rfl }
  exact ⟨Module.IsFiniteLocallyFreeOfRank.of_linearEquiv e.symm,
    Module.IsFiniteLocallyFreeOfRank.of_linearEquiv e⟩

/-- The morphism of spectra induced by a finite-dimensional algebra over a field is finite
locally free of rank the dimension of that algebra. -/
public theorem Stacks.Morphisms.isFiniteLocallyFreeOfRank_specMap_of_field {k A : Type u}
    [Field k] [CommRing A] [Algebra k A] [Module.Finite k A] :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) (Module.finrank k A) :=
  (Stacks.Morphisms.isFiniteLocallyFreeOfRank_specMap_iff _).mpr
    (Module.isFiniteLocallyFreeOfRank_of_field A)

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0CC2.** A finite locally free morphism has universally bounded
fibres. -/
public theorem hasUniversallyBoundedFibers_of_isFiniteLocallyFreeOfRank {X Y : Scheme.{u}}
    (f : X ⟶ Y) (d : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] :
    HasUniversallyBoundedFibers f :=
  ⟨(d : ℤ), boundsFiberDegrees_of_isFiniteLocallyFreeOfRank f d⟩

/-- The fibre of a morphism of spectra at a prime `p` is finite locally free of rank the
dimension over `κ(p)` of the fibre algebra `κ(p) ⊗_A B`. -/
public theorem isFiniteLocallyFreeOfRank_fiberToSpecResidueField_specMap {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] (p : PrimeSpectrum A) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberToSpecResidueField p)
      (Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber B)) := by
  have h := Stacks.Morphisms.isFiniteLocallyFreeOfRank_specMap_of_field
    (k := p.asIdeal.ResidueField) (A := p.asIdeal.Fiber B)
  rw [← Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property_iff] at h ⊢
  exact ((Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u}
    (Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber B))).arrow_mk_iso_iff
    (Spec.fiberToSpecResidueFieldIso A B p)).mpr h

/-- A finite family spanning `B` as an `A`-module bounds by its cardinality the dimension of
every field-valued base change `k ⊗_A B`: the images of the family span that base change. -/
public theorem finrank_tensorProduct_le_of_span_eq_top {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (k : Type u) [Field k] [Algebra A k] {ι : Type v} [Fintype ι] (s : ι → B)
    (hs : Submodule.span A (Set.range s) = ⊤) :
    Module.finrank k (k ⊗[A] B) ≤ Fintype.card ι := by
  classical
  have h := Submodule.baseChange_span (R := A) (A := k) (M := B) (Set.range s)
  rw [hs, Submodule.baseChange_top] at h
  have hspan : Submodule.span k (Set.range ((TensorProduct.mk A k B 1) ∘ s))
      = (⊤ : Submodule k (k ⊗[A] B)) := by
    rw [Set.range_comp, ← h]
  simpa using finrank_le_of_span_eq_top (R := k) (v := (TensorProduct.mk A k B 1) ∘ s) hspan

/-- **Stacks Project, Tag 03JA**, the affine case. If `B` is spanned as an `A`-module by a finite
family, then the cardinality of that family bounds the degrees of the fibres of the induced
morphism of spectra. -/
public theorem boundsFiberDegrees_specMap_of_span_eq_top {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] {ι : Type v} [Fintype ι] (s : ι → B)
    (hs : Submodule.span A (Set.range s) = ⊤) :
    BoundsFiberDegrees (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Fintype.card ι : ℤ) := by
  have : Module.Finite A B :=
    Module.finite_def.mpr (Submodule.fg_def.mpr ⟨Set.range s, Set.finite_range s, hs⟩)
  intro y
  let p : PrimeSpectrum A := y
  refine ⟨Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber B), ?_,
    isFiniteLocallyFreeOfRank_fiberToSpecResidueField_specMap p⟩
  exact_mod_cast finrank_tensorProduct_le_of_span_eq_top (A := A) (B := B)
    p.asIdeal.ResidueField s hs

/-- **Stacks Project, Tag 03JA**, the affine case, with the generators indexed as in the source.
If `B` is generated as an `A`-module by `x₁, …, xₙ`, then `n` bounds the degrees of the fibres of
the induced morphism of spectra. -/
public theorem boundsFiberDegrees_specMap_of_span_range_eq_top {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] {n : ℕ} (s : Fin n → B)
    (hs : Submodule.span A (Set.range s) = ⊤) :
    BoundsFiberDegrees (Spec.map (CommRingCat.ofHom (algebraMap A B))) (n : ℤ) :=
  Fintype.card_fin n ▸ boundsFiberDegrees_specMap_of_span_eq_top s hs

/-- **Stacks Project, Tag 03JA**, the affine case. A module-finite ring map induces a morphism of
spectra with universally bounded fibres. -/
public theorem hasUniversallyBoundedFibers_specMap_of_finite {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] :
    HasUniversallyBoundedFibers (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  obtain ⟨t, ht⟩ := Module.finite_def.mp (inferInstance : Module.Finite A B)
  exact ⟨(Fintype.card {x // x ∈ t} : ℤ),
    boundsFiberDegrees_specMap_of_span_eq_top (ι := {x // x ∈ t}) Subtype.val
      (by rw [Subtype.range_coe]; exact ht)⟩

end AlgebraicGeometry

end
