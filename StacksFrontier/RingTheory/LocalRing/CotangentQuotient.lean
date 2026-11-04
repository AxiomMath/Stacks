module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The cotangent space does not change under a quotient inside the square of the maximal ideal

Let `A → B` be a surjective homomorphism of commutative rings, let `K` be an ideal of `A` and
`J` an ideal of `B` with `K = J⁻¹` up to the kernel, and assume the kernel is contained in `K ^ 2`.
Then `Ideal.mapCotangent` is an isomorphism `K/K² ≃ J/J²`.

Specialised to a local ring `(A, 𝔪)` and a surjective local homomorphism `A → B` whose kernel is
contained in `𝔪 ^ 2` — in particular to `B = A ⧸ I` with `I ≤ 𝔪 ^ 2` — this says that the
cotangent space is unchanged: `𝔪/𝔪² ≃ 𝔪_B/𝔪_B²`. The scalar fields are not literally the same
ring, so the isomorphism is `A`-linear and semilinear over the induced isomorphism of residue
fields; `IsLocalRing.basisCotangentSpaceOfKerLeSq` packages the consequence that actually gets
used, namely that a basis of `𝔪/𝔪²` pushes forward to a basis of `𝔪_B/𝔪_B²`.

## Main results

* `Ideal.bijective_mapCotangent_of_ker_le_sq` — the general ideal-theoretic statement.
* `IsLocalRing.cotangentSpaceEquivOfKerLeSq` — the cotangent spaces of `A` and `B` are
  `A`-linearly isomorphic.
* `IsLocalRing.cotangentSpaceQuotientEquiv` — the same for `B = A ⧸ I` with `I ≤ 𝔪 ^ 2`.
* `IsLocalRing.finrank_cotangentSpace_eq_of_ker_le_sq` and
  `IsLocalRing.finrank_cotangentSpace_quotient` — the equality of embedding dimensions.
* `IsLocalRing.basisCotangentSpaceOfKerLeSq` and `IsLocalRing.basisCotangentSpaceQuotient` —
  the transported basis.
* `IsLocalRing.basisCotangentSpaceSymmOfKerLeSq` — the basis transported the other way, along
  the inverse of the isomorphism of cotangent spaces.

## Implementation notes

The two inputs from Mathlib are `Ideal.mapCotangent_surjective_of_comap_eq` and
`Ideal.mapCotangent_ker_of_surjective`. The second computes the kernel of
`Ideal.mapCotangent` as the image of `(ker ⊓ K)` in `K/K²`; the hypothesis `ker ≤ K ^ 2` is
exactly what makes that image vanish, which is the whole content of injectivity.

The cotangent map is spelled `Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B)
(Algebra.ofId A B) (le_of_eq (maximalIdeal_comap (algebraMap A B)).symm)` throughout, matching
the spelling in `StacksCore.RingTheory.LocalRing.RingHom.Basic`. Since the last argument is a proof,
proof irrelevance makes these statements apply to any other proof of the same inequality.
-/

@[expose] public section

open IsLocalRing

universe u v

/-! ### The general ideal-theoretic statement -/

namespace Ideal

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- If `A → B` is surjective with kernel inside `K ^ 2`, then `K/K² → J/J²` has trivial kernel. -/
theorem mapCotangent_ker_eq_bot_of_ker_le_sq (hsurj : Function.Surjective (algebraMap A B))
    {J : Ideal B} {K : Ideal A}
    (hcomap : J.comap (algebraMap A B) = RingHom.ker (algebraMap A B) ⊔ K)
    (hker : RingHom.ker (algebraMap A B) ≤ K ^ 2) :
    LinearMap.ker (Ideal.mapCotangent K J (Algebra.ofId A B)
      (le_of_le_of_eq le_sup_right hcomap.symm)) = ⊥ := by
  rw [Ideal.mapCotangent_ker_of_surjective hsurj hcomap, eq_bot_iff,
    Submodule.map_le_iff_le_comap]
  intro x hx
  exact (K.toCotangent_eq_zero x).2 (hker (Ideal.mem_inf.mp hx).1)

/-- If `A → B` is surjective with kernel inside `K ^ 2`, then `K/K² → J/J²` is injective. -/
theorem injective_mapCotangent_of_ker_le_sq (hsurj : Function.Surjective (algebraMap A B))
    {J : Ideal B} {K : Ideal A}
    (hcomap : J.comap (algebraMap A B) = RingHom.ker (algebraMap A B) ⊔ K)
    (hker : RingHom.ker (algebraMap A B) ≤ K ^ 2) :
    Function.Injective (Ideal.mapCotangent K J (Algebra.ofId A B)
      (le_of_le_of_eq le_sup_right hcomap.symm)) :=
  LinearMap.ker_eq_bot.mp (mapCotangent_ker_eq_bot_of_ker_le_sq hsurj hcomap hker)

/-- If `A → B` is surjective with kernel inside `K ^ 2`, then `K/K² → J/J²` is bijective. -/
theorem bijective_mapCotangent_of_ker_le_sq (hsurj : Function.Surjective (algebraMap A B))
    {J : Ideal B} {K : Ideal A}
    (hcomap : J.comap (algebraMap A B) = RingHom.ker (algebraMap A B) ⊔ K)
    (hker : RingHom.ker (algebraMap A B) ≤ K ^ 2) :
    Function.Bijective (Ideal.mapCotangent K J (Algebra.ofId A B)
      (le_of_le_of_eq le_sup_right hcomap.symm)) :=
  ⟨injective_mapCotangent_of_ker_le_sq hsurj hcomap hker,
    Ideal.mapCotangent_surjective_of_comap_eq hsurj hcomap⟩

end Ideal

/-! ### The local case -/

namespace IsLocalRing

section Surjective

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

/-- The kernel of a local homomorphism is contained in the maximal ideal. -/
theorem ker_algebraMap_le_maximalIdeal :
    RingHom.ker (algebraMap A B) ≤ maximalIdeal A := by
  rw [RingHom.ker_eq_comap_bot, ← maximalIdeal_comap (algebraMap A B)]
  exact Ideal.comap_mono bot_le

/-- For a local homomorphism, the preimage of `𝔪_B` is the kernel joined with `𝔪_A`: the shape
in which `Ideal.mapCotangent_surjective_of_comap_eq` wants its hypothesis. -/
theorem comap_maximalIdeal_eq_ker_sup :
    (maximalIdeal B).comap (algebraMap A B) =
      RingHom.ker (algebraMap A B) ⊔ maximalIdeal A := by
  rw [maximalIdeal_comap (algebraMap A B)]
  exact (sup_eq_right.mpr ker_algebraMap_le_maximalIdeal).symm

/-- The cotangent map of a surjective local homomorphism whose kernel lies in `𝔪 ^ 2` is
injective. -/
theorem injective_mapCotangent_of_ker_le_sq (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) ≤ maximalIdeal A ^ 2) :
    Function.Injective (Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B)
      (Algebra.ofId A B) (le_of_eq (maximalIdeal_comap (algebraMap A B)).symm)) :=
  Ideal.injective_mapCotangent_of_ker_le_sq hsurj comap_maximalIdeal_eq_ker_sup hker

/-- **The cotangent space is unchanged by a quotient inside `𝔪 ^ 2`.** If `A → B` is a surjective
local homomorphism of local rings whose kernel is contained in `𝔪_A ^ 2`, then the induced map
`𝔪_A/𝔪_A² → 𝔪_B/𝔪_B²` is bijective. -/
theorem bijective_mapCotangent_of_ker_le_sq (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) ≤ maximalIdeal A ^ 2) :
    Function.Bijective (Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B)
      (Algebra.ofId A B) (le_of_eq (maximalIdeal_comap (algebraMap A B)).symm)) :=
  ⟨injective_mapCotangent_of_ker_le_sq hsurj hker,
    Ideal.mapCotangent_surjective_of_comap_eq hsurj comap_maximalIdeal_eq_ker_sup⟩

/-- The isomorphism of cotangent spaces induced by a surjective local homomorphism whose kernel
is contained in `𝔪 ^ 2`. It is `A`-linear; see `IsLocalRing.mapCotangent_residueField_smul`
for how it interacts with the residue field scalars. -/
noncomputable def cotangentSpaceEquivOfKerLeSq (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) ≤ maximalIdeal A ^ 2) :
    CotangentSpace A ≃ₗ[A] CotangentSpace B :=
  LinearEquiv.ofBijective _ (bijective_mapCotangent_of_ker_le_sq hsurj hker)

/-- `IsLocalRing.cotangentSpaceEquivOfKerLeSq` sends the class of `x ∈ 𝔪_A` to the class of its
image in `𝔪_B`. -/
@[simp]
theorem cotangentSpaceEquivOfKerLeSq_toCotangent
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) ≤ maximalIdeal A ^ 2) (x : maximalIdeal A) :
    cotangentSpaceEquivOfKerLeSq hsurj hker ((maximalIdeal A).toCotangent x) =
      (maximalIdeal B).toCotangent
        ⟨algebraMap A B x, le_of_eq (maximalIdeal_comap (algebraMap A B)).symm x.2⟩ :=
  rfl

/-- A surjective local homomorphism induces a bijection on residue fields. -/
theorem bijective_residueFieldMap_of_surjective (hsurj : Function.Surjective (algebraMap A B)) :
    Function.Bijective (ResidueField.map (algebraMap A B)) := by
  refine ⟨RingHom.injective _, fun z => ?_⟩
  obtain ⟨s, rfl⟩ := residue_surjective z
  obtain ⟨r, rfl⟩ := hsurj s
  exact ⟨residue A r, ResidueField.map_residue (algebraMap A B) r⟩

/-- The isomorphism of residue fields induced by a surjective local homomorphism. -/
noncomputable def residueFieldEquivOfSurjective (hsurj : Function.Surjective (algebraMap A B)) :
    ResidueField A ≃+* ResidueField B :=
  RingEquiv.ofBijective _ (bijective_residueFieldMap_of_surjective hsurj)

/-- `IsLocalRing.residueFieldEquivOfSurjective` is the induced map of residue fields. -/
@[simp]
theorem residueFieldEquivOfSurjective_apply (hsurj : Function.Surjective (algebraMap A B))
    (x : ResidueField A) :
    residueFieldEquivOfSurjective hsurj x = ResidueField.map (algebraMap A B) x :=
  rfl

/-- The cotangent map is semilinear over the induced map of residue fields. -/
theorem mapCotangent_residueField_smul (r : ResidueField A) (x : CotangentSpace A) :
    Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
        (le_of_eq (maximalIdeal_comap (algebraMap A B)).symm) (r • x) =
      ResidueField.map (algebraMap A B) r •
        Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
          (le_of_eq (maximalIdeal_comap (algebraMap A B)).symm) x := by
  obtain ⟨s, rfl⟩ := residue_surjective r
  set F := Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
    (le_of_eq (maximalIdeal_comap (algebraMap A B)).symm) with hF
  show F (s • x) = algebraMap A B s • F x
  rw [map_smul, IsScalarTower.algebraMap_smul]

/-- A surjective local homomorphism with kernel inside `𝔪 ^ 2` preserves the rank of the
cotangent space. -/
theorem lift_rank_cotangentSpace_eq_of_ker_le_sq
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) ≤ maximalIdeal A ^ 2) :
    Cardinal.lift.{v} (Module.rank (ResidueField A) (CotangentSpace A)) =
      Cardinal.lift.{u} (Module.rank (ResidueField B) (CotangentSpace B)) :=
  lift_rank_eq_of_equiv_equiv (ResidueField.map (algebraMap A B))
    (cotangentSpaceEquivOfKerLeSq hsurj hker).toAddEquiv
    (bijective_residueFieldMap_of_surjective hsurj)
    (fun r x => mapCotangent_residueField_smul (A := A) (B := B) r x)

/-- A surjective local homomorphism with kernel inside `𝔪 ^ 2` preserves the embedding dimension
`dim_κ 𝔪/𝔪²`. -/
theorem finrank_cotangentSpace_eq_of_ker_le_sq (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) ≤ maximalIdeal A ^ 2) :
    Module.finrank (ResidueField A) (CotangentSpace A) =
      Module.finrank (ResidueField B) (CotangentSpace B) := by
  have h := congrArg Cardinal.toNat (lift_rank_cotangentSpace_eq_of_ker_le_sq hsurj hker)
  rwa [Cardinal.toNat_lift, Cardinal.toNat_lift] at h

/-- A family spans a module over the residue field iff it spans it over the local ring. -/
private theorem span_residueField_eq_top_iff {R M ι : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module (ResidueField R) M] [IsScalarTower R (ResidueField R) M]
    (v : ι → M) :
    Submodule.span (ResidueField R) (Set.range v) = ⊤ ↔ Submodule.span R (Set.range v) = ⊤ := by
  rw [← Submodule.restrictScalars_eq_top_iff R,
    Submodule.restrictScalars_span R _ residue_surjective]

/-- The image of a spanning family of `𝔪_A/𝔪_A²` spans `𝔪_B/𝔪_B²`, for a surjective local
homomorphism. -/
theorem span_image_mapCotangent_eq_top_of_surjective
    (hsurj : Function.Surjective (algebraMap A B)) {ι : Type*}
    {v : ι → CotangentSpace A}
    (hv : Submodule.span (ResidueField A) (Set.range v) = ⊤) :
    Submodule.span (ResidueField B) (Set.range fun i =>
        Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
          (le_of_eq (maximalIdeal_comap (algebraMap A B)).symm) (v i)) = ⊤ := by
  set F := Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
    (le_of_eq (maximalIdeal_comap (algebraMap A B)).symm) with hF
  have hA := (span_residueField_eq_top_iff v).1 hv
  have himg : Submodule.span A (Set.range fun i => F (v i)) = ⊤ := by
    rw [Set.range_comp' F v, ← Submodule.map_span, hA, Submodule.map_top,
      LinearMap.range_eq_top]
    exact Ideal.mapCotangent_surjective_of_comap_eq hsurj comap_maximalIdeal_eq_ker_sup
  rw [span_residueField_eq_top_iff, ← Submodule.restrictScalars_eq_top_iff A,
    Submodule.restrictScalars_span A B hsurj, himg]

/-- **A basis of the cotangent space transports along a quotient inside `𝔪 ^ 2`.** If `A → B` is
a surjective local homomorphism whose kernel lies in `𝔪_A ^ 2`, then the images of a (finite)
basis of `𝔪_A/𝔪_A²` form a basis of `𝔪_B/𝔪_B²`. -/
noncomputable def basisCotangentSpaceOfKerLeSq {ι : Type*} [Fintype ι]
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) ≤ maximalIdeal A ^ 2)
    (b : Module.Basis ι (ResidueField A) (CotangentSpace A)) :
    Module.Basis ι (ResidueField B) (CotangentSpace B) :=
  basisOfTopLeSpanOfCardEqFinrank
    (fun i => Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
      (le_of_eq (maximalIdeal_comap (algebraMap A B)).symm) (b i))
    (span_image_mapCotangent_eq_top_of_surjective hsurj b.span_eq).ge
    (by rw [← finrank_cotangentSpace_eq_of_ker_le_sq hsurj hker, Module.finrank_eq_card_basis b])

/-- The vectors of `IsLocalRing.basisCotangentSpaceOfKerLeSq` are the images of the vectors of
`b` under the cotangent isomorphism. -/
@[simp]
theorem basisCotangentSpaceOfKerLeSq_apply {ι : Type*} [Fintype ι]
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) ≤ maximalIdeal A ^ 2)
    (b : Module.Basis ι (ResidueField A) (CotangentSpace A)) (i : ι) :
    basisCotangentSpaceOfKerLeSq hsurj hker b i =
      cotangentSpaceEquivOfKerLeSq hsurj hker (b i) := by
  rw [basisCotangentSpaceOfKerLeSq, coe_basisOfTopLeSpanOfCardEqFinrank]
  rfl

/-- The preimages under the cotangent isomorphism of a spanning family of `𝔪_B/𝔪_B²` span
`𝔪_A/𝔪_A²`, for a surjective local homomorphism with kernel inside `𝔪_A ^ 2`. -/
theorem span_image_symm_cotangentSpaceEquiv_eq_top
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) ≤ maximalIdeal A ^ 2) {ι : Type*}
    {v : ι → CotangentSpace B}
    (hv : Submodule.span (ResidueField B) (Set.range v) = ⊤) :
    Submodule.span (ResidueField A) (Set.range fun i =>
      (cotangentSpaceEquivOfKerLeSq hsurj hker).symm (v i)) = ⊤ := by
  have hA : Submodule.span A (Set.range v) = ⊤ := by
    rw [← Submodule.restrictScalars_span A B hsurj, (span_residueField_eq_top_iff v).1 hv,
      Submodule.restrictScalars_top]
  have himg : Submodule.span A (Set.range fun i =>
      (cotangentSpaceEquivOfKerLeSq hsurj hker).symm (v i)) = ⊤ := by
    rw [Set.range_comp' (cotangentSpaceEquivOfKerLeSq hsurj hker).symm v]
    show Submodule.span A
        (((cotangentSpaceEquivOfKerLeSq hsurj hker).symm :
          CotangentSpace B →ₗ[A] CotangentSpace A) '' Set.range v) = ⊤
    rw [← Submodule.map_span, hA, Submodule.map_top, LinearMap.range_eq_top]
    exact (cotangentSpaceEquivOfKerLeSq hsurj hker).symm.surjective
  rwa [span_residueField_eq_top_iff]

/-- **A basis of the cotangent space transports back along a quotient inside `𝔪 ^ 2`.** If
`A → B` is a surjective local homomorphism whose kernel lies in `𝔪_A ^ 2`, then the preimages of
a (finite) basis of `𝔪_B/𝔪_B²` form a basis of `𝔪_A/𝔪_A²`. -/
noncomputable def basisCotangentSpaceSymmOfKerLeSq {ι : Type*} [Fintype ι]
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) ≤ maximalIdeal A ^ 2)
    (b : Module.Basis ι (ResidueField B) (CotangentSpace B)) :
    Module.Basis ι (ResidueField A) (CotangentSpace A) :=
  basisOfTopLeSpanOfCardEqFinrank
    (fun i => (cotangentSpaceEquivOfKerLeSq hsurj hker).symm (b i))
    (span_image_symm_cotangentSpaceEquiv_eq_top hsurj hker b.span_eq).ge
    (by rw [finrank_cotangentSpace_eq_of_ker_le_sq hsurj hker, Module.finrank_eq_card_basis b])

/-- The vectors of `IsLocalRing.basisCotangentSpaceSymmOfKerLeSq` are the preimages of the
vectors of `b` under the cotangent isomorphism. -/
@[simp]
theorem basisCotangentSpaceSymmOfKerLeSq_apply {ι : Type*} [Fintype ι]
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) ≤ maximalIdeal A ^ 2)
    (b : Module.Basis ι (ResidueField B) (CotangentSpace B)) (i : ι) :
    basisCotangentSpaceSymmOfKerLeSq hsurj hker b i =
      (cotangentSpaceEquivOfKerLeSq hsurj hker).symm (b i) := by
  rw [basisCotangentSpaceSymmOfKerLeSq, coe_basisOfTopLeSpanOfCardEqFinrank]

end Surjective

/-! ### The quotient case -/

section Quotient

variable {A : Type u} [CommRing A] [IsLocalRing A] (I : Ideal A)

/-- The quotient of a local ring by an ideal contained in the maximal ideal is a local ring. -/
theorem isLocalRing_quotient_of_le_maximalIdeal (hI : I ≤ maximalIdeal A) :
    IsLocalRing (A ⧸ I) :=
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (lt_of_le_of_lt hI (lt_top_iff_ne_top.mpr (maximalIdeal.isMaximal A).ne_top)).ne
  .of_surjective' _ Ideal.Quotient.mk_surjective

omit [IsLocalRing A] in
/-- The algebra map `A → A ⧸ I` is surjective. -/
theorem surjective_algebraMap_quotient : Function.Surjective (algebraMap A (A ⧸ I)) := by
  rw [Ideal.Quotient.algebraMap_eq]
  exact Ideal.Quotient.mk_surjective

omit [IsLocalRing A] in
/-- The kernel of the algebra map `A → A ⧸ I` is `I`. -/
theorem ker_algebraMap_quotient : RingHom.ker (algebraMap A (A ⧸ I)) = I := by
  rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]

variable [IsLocalRing (A ⧸ I)]

/-- The quotient map onto a local quotient of a local ring is a local homomorphism. -/
instance isLocalHom_algebraMap_quotient : IsLocalHom (algebraMap A (A ⧸ I)) :=
  IsLocalHom.of_surjective _ (surjective_algebraMap_quotient I)

/-- **Stacks-style statement of the target**: for an ideal `I ≤ 𝔪 ^ 2` of a local ring `A`, the
natural map `𝔪/𝔪² → 𝔪_{A/I}/𝔪_{A/I}²` is bijective. -/
theorem bijective_mapCotangent_quotient (hI : I ≤ maximalIdeal A ^ 2) :
    Function.Bijective (Ideal.mapCotangent (maximalIdeal A) (maximalIdeal (A ⧸ I))
      (Algebra.ofId A (A ⧸ I))
      (le_of_eq (maximalIdeal_comap (algebraMap A (A ⧸ I))).symm)) :=
  bijective_mapCotangent_of_ker_le_sq (surjective_algebraMap_quotient I)
    ((ker_algebraMap_quotient I).le.trans hI)

/-- **The cotangent space is unchanged by a quotient inside `𝔪 ^ 2`.** For an ideal
`I ≤ 𝔪 ^ 2` of a local ring `A`, the cotangent spaces of `A` and of `A ⧸ I` are `A`-linearly
isomorphic. -/
noncomputable def cotangentSpaceQuotientEquiv (hI : I ≤ maximalIdeal A ^ 2) :
    CotangentSpace A ≃ₗ[A] CotangentSpace (A ⧸ I) :=
  LinearEquiv.ofBijective _ (bijective_mapCotangent_quotient I hI)

/-- `IsLocalRing.cotangentSpaceQuotientEquiv` sends the class of `x ∈ 𝔪` to the class of its
image in the maximal ideal of `A ⧸ I`. -/
@[simp]
theorem cotangentSpaceQuotientEquiv_toCotangent (hI : I ≤ maximalIdeal A ^ 2)
    (x : maximalIdeal A) :
    cotangentSpaceQuotientEquiv I hI ((maximalIdeal A).toCotangent x) =
      (maximalIdeal (A ⧸ I)).toCotangent
        ⟨algebraMap A (A ⧸ I) x,
          le_of_eq (maximalIdeal_comap (algebraMap A (A ⧸ I))).symm x.2⟩ :=
  rfl

/-- For an ideal `I ≤ 𝔪 ^ 2` of a local ring `A`, the embedding dimensions of `A` and `A ⧸ I`
agree. -/
theorem finrank_cotangentSpace_quotient (hI : I ≤ maximalIdeal A ^ 2) :
    Module.finrank (ResidueField A) (CotangentSpace A) =
      Module.finrank (ResidueField (A ⧸ I)) (CotangentSpace (A ⧸ I)) :=
  finrank_cotangentSpace_eq_of_ker_le_sq (surjective_algebraMap_quotient I)
    ((ker_algebraMap_quotient I).le.trans hI)

/-- For an ideal `I ≤ 𝔪 ^ 2` of a local ring `A`, a finite basis of the cotangent space of `A`
pushes forward to a basis of the cotangent space of `A ⧸ I`. -/
noncomputable def basisCotangentSpaceQuotient {ι : Type*} [Fintype ι]
    (hI : I ≤ maximalIdeal A ^ 2)
    (b : Module.Basis ι (ResidueField A) (CotangentSpace A)) :
    Module.Basis ι (ResidueField (A ⧸ I)) (CotangentSpace (A ⧸ I)) :=
  basisCotangentSpaceOfKerLeSq (surjective_algebraMap_quotient I)
    ((ker_algebraMap_quotient I).le.trans hI) b

/-- The vectors of `IsLocalRing.basisCotangentSpaceQuotient` are the images of the vectors of
`b` under `IsLocalRing.cotangentSpaceQuotientEquiv`. -/
@[simp]
theorem basisCotangentSpaceQuotient_apply {ι : Type*} [Fintype ι]
    (hI : I ≤ maximalIdeal A ^ 2)
    (b : Module.Basis ι (ResidueField A) (CotangentSpace A)) (i : ι) :
    basisCotangentSpaceQuotient I hI b i = cotangentSpaceQuotientEquiv I hI (b i) := by
  rw [basisCotangentSpaceQuotient, basisCotangentSpaceOfKerLeSq_apply]
  rfl

end Quotient

end IsLocalRing

end
