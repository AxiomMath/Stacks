module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Local coordinates for a closed immersion of smooth schemes

Let `R` be a ring and `I ⊆ R` an ideal, let `B` be a smooth `R`-algebra and let `π : B → C` be a
surjection onto a smooth `R ⧸ I`-algebra, with kernel `J ⊇ I B`. Geometrically, `Spec C` is a
closed subscheme of `Spec (B ⧸ I B)`, both smooth over `R ⧸ I`. This file proves that near every
point of `Spec C` the ideal `J` is cut out, together with `I`, by part of a coordinate system of
`B` over `R`: for every prime `q ⊇ J` there are `g ∉ q` and `t_1, …, t_c ∈ B_g` such that `B_g`
is flat (indeed smooth) over `R[x_1, …, x_c]` along `x_i ↦ t_i` and `J B_g = I B_g + (t_i)`.
This is `Crystalline.exists_localizationAway_flat_mvPolynomial_of_smooth`.

## Proof

Put `B̄ = B ⧸ I B` and `J̄ = J ⧸ I B`. Since `C` and `B̄` are formally smooth over `R ⧸ I`, the
conormal map `J̄/J̄² → C ⊗ Ω_{B̄/(R⧸I)}` has a retraction (Stacks 031I), which gives a `B`-linear
map `Λ : Ω_{B/R} → J̄/J̄²` with `Λ(d j) = [j]` (`Crystalline.exists_kaehler_to_cotangent`).
Choose `t_i ∈ J` whose classes form a basis of the fibre `κ(q) ⊗ J̄/J̄²`
(`Crystalline.exists_basis_residueField_cotangent`). Then

* by Nakayama's lemma, applied twice, some `v ∉ q` multiplies `J` into `I B + (t_i)`
  (`Crystalline.exists_notMem_mul_mem_of_span_residueField`);
* the differentials `d t_i` are linearly independent in `κ(q) ⊗ Ω_{B/R}`, because `Λ` carries
  them to the basis; by the Jacobi–Zariski sequence and the splitting criterion over the local
  ring `B_q`, this makes `B_q` formally smooth over `R[x_1, …, x_c]`
  (`Crystalline.formallySmooth_localization_of_linearIndependent`), and the smooth locus is open.

## References

* [Stacks Project, Tag 07MU](https://stacks.math.columbia.edu/tag/07MU) (the hints)
* [Stacks Project, Tag 031I](https://stacks.math.columbia.edu/tag/031I)
* [Stacks Project, Tag 00TB](https://stacks.math.columbia.edu/tag/00TB)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Crystalline

open KaehlerDifferential

section Nakayama

variable {A : Type u} [CommRing A]

/-- If a prime is outside the support of `M ⧸ L` for a finite module `M`, some `u` outside the
prime multiplies `M` into `L`. -/
private theorem exists_notMem_smul_mem_of_notMem_support_quotient {M : Type*} [AddCommGroup M]
    [Module A M] [Module.Finite A M] (L : Submodule A M) (p : Ideal A) [p.IsPrime]
    (h : (⟨p, inferInstance⟩ : PrimeSpectrum A) ∉ Module.support A (M ⧸ L)) :
    ∃ u ∉ p, ∀ x : M, u • x ∈ L := by
  rw [Module.mem_support_iff_of_finite] at h
  obtain ⟨u, hu, hup⟩ := IsConcreteLE.not_le_iff_exists.mp h
  refine ⟨u, hup, fun x => ?_⟩
  have := Module.mem_annihilator.mp hu (Submodule.Quotient.mk x)
  rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this

/-- **Nakayama's lemma for an ideal modulo its square, at a point.** Let `K` be a finitely
generated ideal contained in a prime `p`, and `s_i ∈ K`. If some `u ∉ p` multiplies `K` into
`(s_i) + K²`, then some `u' ∉ p` multiplies `K` into `(s_i)`. -/
theorem exists_notMem_mul_mem_span_of_mul_mem_span_sup_sq {K : Ideal A} (hK : K.FG)
    (p : Ideal A) [p.IsPrime] (hKp : K ≤ p) {ι : Type*} (s : ι → A) (hs : ∀ i, s i ∈ K)
    {u : A} (hu : u ∉ p) (huK : ∀ x ∈ K, u * x ∈ Ideal.span (Set.range s) ⊔ K ^ 2) :
    ∃ u' ∉ p, ∀ x ∈ K, u' * x ∈ Ideal.span (Set.range s) := by
  let s' : ι → K := fun i => ⟨s i, hs i⟩
  let L : Submodule A K := Submodule.span A (Set.range s')
  have : Module.Finite A K := Module.Finite.iff_fg.mpr hK
  have hmapL : L.map K.subtype = Ideal.span (Set.range s) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  -- the classes of elements of `K²` lie in `K • (K ⧸ L)`
  have hsq : ∀ (y : A) (hy : y ∈ K * K),
      L.mkQ ⟨y, Ideal.mul_le_left hy⟩ ∈ (K • ⊤ : Submodule A (K ⧸ L)) := by
    intro y hy
    induction hy using Submodule.mul_induction_on' with
    | mem_mul_mem a ha b hb =>
      have : (⟨a * b, Ideal.mul_le_left (Ideal.mul_mem_mul ha hb)⟩ : K) = a • ⟨b, hb⟩ := rfl
      rw [this, map_smul]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    | add x hx y hy ihx ihy =>
      have : (⟨x + y, Ideal.mul_le_left (Submodule.add_mem _ hx hy)⟩ : K) =
          ⟨x, Ideal.mul_le_left hx⟩ + ⟨y, Ideal.mul_le_left hy⟩ := rfl
      rw [this, map_add]
      exact Submodule.add_mem _ ihx ihy
  -- `u` kills `(K ⧸ L) ⧸ K (K ⧸ L)`, so `p` is not in its support
  have hu' : u ∈ Module.annihilator A ((K ⧸ L) ⧸ (K • ⊤ : Submodule A (K ⧸ L))) := by
    rw [Module.mem_annihilator]
    intro z
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← Submodule.Quotient.mk_smul]
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (huK x hx)
    have ha' : a ∈ K := Ideal.span_le.mpr (Set.range_subset_iff.mpr hs) ha
    have hb' : b ∈ K * K := by rwa [← pow_two]
    have hsplit : u • (⟨x, hx⟩ : K) = ⟨a, ha'⟩ + ⟨b, Ideal.mul_le_left hb'⟩ := by
      ext
      simp [hab]
    rw [hsplit, Submodule.Quotient.mk_add]
    have haL : (⟨a, ha'⟩ : K) ∈ L := by
      rw [← hmapL] at ha
      obtain ⟨a', ha'L, ha'eq⟩ := ha
      have : a' = ⟨a, ha'⟩ := Subtype.ext ha'eq
      rwa [← this]
    rw [(Submodule.Quotient.mk_eq_zero L).mpr haL, zero_add]
    exact hsq b hb'
  have hnot₁ : (⟨p, inferInstance⟩ : PrimeSpectrum A) ∉
      Module.support A ((K ⧸ L) ⧸ (K • ⊤ : Submodule A (K ⧸ L))) := by
    rw [Module.mem_support_iff_of_finite]
    exact fun h => hu (h hu')
  have hnot : (⟨p, inferInstance⟩ : PrimeSpectrum A) ∉ Module.support A (K ⧸ L) := by
    rw [Module.support_quotient] at hnot₁
    exact fun h => hnot₁ ⟨h, hKp⟩
  obtain ⟨u', hu'p, hu'L⟩ := exists_notMem_smul_mem_of_notMem_support_quotient L p hnot
  refine ⟨u', hu'p, fun x hx => ?_⟩
  rw [← hmapL]
  exact ⟨_, hu'L ⟨x, hx⟩, rfl⟩

end Nakayama

section Conormal

variable {R B C : Type u} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  (I : Ideal R) [Algebra (R ⧸ I) C] [IsScalarTower R (R ⧸ I) C]
  (π : B →ₐ[R] C)

/-- An `R`-algebra map to an `R ⧸ I`-algebra kills `I B`. -/
theorem map_le_ker_of_quotient : I.map (algebraMap R B) ≤ RingHom.ker π.toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  change π (algebraMap R B a) = 0
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R (R ⧸ I) C,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

/-- The map `B ⧸ I B → C` induced by `π`. -/
noncomputable def quotientLift : B ⧸ I.map (algebraMap R B) →ₐ[R ⧸ I] C where
  toRingHom := Ideal.Quotient.lift _ π.toRingHom (map_le_ker_of_quotient I π)
  commutes' := by
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change π (algebraMap R B a) = _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R (R ⧸ I) C]
    rfl

/-- The map `B ⧸ I B → C` on the class of `b` is `π b`. -/
theorem quotientLift_mk (b : B) :
    quotientLift I π (Ideal.Quotient.mk _ b) = π b := rfl

/-- The map `B ⧸ I B → C` is surjective when `π` is. -/
theorem quotientLift_surjective (hπ : Function.Surjective π) :
    Function.Surjective (quotientLift I π) := by
  intro c
  obtain ⟨b, rfl⟩ := hπ c
  exact ⟨Ideal.Quotient.mk _ b, rfl⟩

/-- The class of an element of `ker π` lies in the kernel of `B ⧸ I B → C`. -/
theorem mk_mem_ker_quotientLift {j : B} (hj : j ∈ RingHom.ker π.toRingHom) :
    Ideal.Quotient.mk (I.map (algebraMap R B)) j ∈ RingHom.ker (quotientLift I π).toRingHom :=
  hj

/-- **The conormal module of a smooth closed subscheme splits off.** If `C` is formally smooth
over `R ⧸ I` and `B` is smooth over `R`, there is a `B`-linear map from `Ω_{B/R}` to the conormal
module of `B ⧸ I B → C` sending `d j` to the class of `j` for every `j` in the kernel. -/
theorem exists_kaehler_to_cotangent [Algebra.Smooth R B] [Algebra.FormallySmooth (R ⧸ I) C]
    (hπ : Function.Surjective π) :
    ∃ Λ : Ω[B⁄R] →ₗ[B] (RingHom.ker (quotientLift I π).toRingHom).Cotangent,
      ∀ (j : B) (hj : j ∈ RingHom.ker π.toRingHom),
        Λ (D R B j) = Ideal.toCotangent _ ⟨_, mk_mem_ker_quotientLift I π hj⟩ := by
  let : Algebra (B ⧸ I.map (algebraMap R B)) C := (quotientLift I π).toRingHom.toAlgebra
  have : IsScalarTower (R ⧸ I) (B ⧸ I.map (algebraMap R B)) C :=
    IsScalarTower.of_algebraMap_eq' (quotientLift I π).comp_algebraMap.symm
  have : Algebra.FormallySmooth (R ⧸ I) (B ⧸ I.map (algebraMap R B)) :=
    Algebra.FormallySmooth.of_equiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection
    (R := R ⧸ I) (P := B ⧸ I.map (algebraMap R B)) (A := C)
    (quotientLift_surjective I π hπ)).mp inferInstance
  refine ⟨(l ∘ₗ (TensorProduct.mk (B ⧸ I.map (algebraMap R B)) C _ 1)).restrictScalars B ∘ₗ
    (KaehlerDifferential.map R (R ⧸ I) B (B ⧸ I.map (algebraMap R B))), fun j hj => ?_⟩
  have := congrArg (fun f => f (Ideal.toCotangent _ ⟨_, mk_mem_ker_quotientLift I π hj⟩)) hl
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq,
    KaehlerDifferential.kerCotangentToTensor_toCotangent] at this
  refine Eq.trans ?_ this
  change l (1 ⊗ₜ (KaehlerDifferential.map R (R ⧸ I) B (B ⧸ I.map (algebraMap R B)) (D R B j))) = _
  rw [KaehlerDifferential.map_D]
  rfl

/-- The kernel of `B ⧸ I B → C` is finitely generated, both rings being of finite presentation
over `R ⧸ I`. -/
theorem fg_ker_quotientLift [Algebra.Smooth R B] [Algebra.Smooth (R ⧸ I) C]
    (hπ : Function.Surjective π) : (RingHom.ker (quotientLift I π).toRingHom).FG := by
  have : Algebra.FinitePresentation (R ⧸ I) (B ⧸ I.map (algebraMap R B)) :=
    Algebra.FinitePresentation.equiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm
  exact Algebra.FinitePresentation.ker_fG_of_surjective _ (quotientLift_surjective I π hπ)

/-- The conormal module of `B ⧸ I B → C` is a finite `B`-module. -/
theorem finite_cotangent_ker_quotientLift [Algebra.Smooth R B] [Algebra.Smooth (R ⧸ I) C]
    (hπ : Function.Surjective π) :
    Module.Finite B (RingHom.ker (quotientLift I π).toRingHom).Cotangent := by
  have hfg := fg_ker_quotientLift I π hπ
  have : Module.Finite (B ⧸ I.map (algebraMap R B))
      (RingHom.ker (quotientLift I π).toRingHom).Cotangent := by
    have : Module.Finite (B ⧸ I.map (algebraMap R B))
        (RingHom.ker (quotientLift I π).toRingHom) := Module.Finite.iff_fg.mpr hfg
    exact Module.Finite.of_surjective _ (Ideal.toCotangent_surjective _)
  exact Module.Finite.trans (B ⧸ I.map (algebraMap R B)) _

/-- Every element of the conormal module of `B ⧸ I B → C` is the class of an element of `ker π`. -/
theorem toCotangent_mk_surjective :
    ∀ m : (RingHom.ker (quotientLift I π).toRingHom).Cotangent, ∃ (j : B)
      (hj : j ∈ RingHom.ker π.toRingHom),
        Ideal.toCotangent _ ⟨_, mk_mem_ker_quotientLift I π hj⟩ = m := by
  intro m
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ m
  obtain ⟨j, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨j, hx, rfl⟩

/-- **Choice of the coordinates.** There are elements `t_1, …, t_c` of the kernel of `π` whose
classes form a basis of the fibre at `q` of the conormal module of `B ⧸ I B → C`. -/
theorem exists_basis_residueField_cotangent [Algebra.Smooth R B] [Algebra.Smooth (R ⧸ I) C]
    (hπ : Function.Surjective π) (q : Ideal B) [q.IsPrime] :
    ∃ (c : ℕ) (t : Fin c → B) (ht : ∀ i, t i ∈ RingHom.ker π.toRingHom),
      LinearIndependent q.ResidueField (fun i => (1 : q.ResidueField) ⊗ₜ[B]
        Ideal.toCotangent _ ⟨_, mk_mem_ker_quotientLift I π (ht i)⟩) ∧
      Submodule.span q.ResidueField (Set.range fun i => (1 : q.ResidueField) ⊗ₜ[B]
        Ideal.toCotangent _ ⟨_, mk_mem_ker_quotientLift I π (ht i)⟩) = ⊤ := by
  have := finite_cotangent_ker_quotientLift I π hπ
  set M := (RingHom.ker (quotientLift I π).toRingHom).Cotangent
  let v : RingHom.ker π.toRingHom → q.ResidueField ⊗[B] M := fun j =>
    (1 : q.ResidueField) ⊗ₜ[B] Ideal.toCotangent _ ⟨_, mk_mem_ker_quotientLift I π j.2⟩
  have hv : Submodule.span q.ResidueField (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul a m =>
      obtain ⟨j, hj, rfl⟩ := toCotangent_mk_surjective I π m
      have : a ⊗ₜ[B] Ideal.toCotangent _ ⟨_, mk_mem_ker_quotientLift I π hj⟩ =
          a • v ⟨j, hj⟩ := by
        simp only [v, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
  obtain ⟨κ', a, -, hspan, hli⟩ := exists_linearIndependent' q.ResidueField v
  have : Finite κ' := hli.finite
  let e := Finite.equivFin κ'
  refine ⟨Nat.card κ', fun i => (a (e.symm i)).1, fun i => (a (e.symm i)).2, ?_, ?_⟩
  · exact hli.comp _ e.symm.injective
  · rw [← hv, ← hspan]
    exact congrArg _ (e.symm.surjective.range_comp (v ∘ a))

/-- **Nakayama's lemma at a point.** If the fibre at `q` of a finite module `M` is spanned by
the images of elements `m_i`, then some `u ∉ q` multiplies `M` into the span of the `m_i`. -/
theorem exists_notMem_smul_mem_span_of_span_residueField {M : Type u} [AddCommGroup M]
    [Module B M] [Module.Finite B M] (q : Ideal B) [q.IsPrime] {ι : Type*} (m : ι → M)
    (hspan : Submodule.span q.ResidueField
      (Set.range fun i => (1 : q.ResidueField) ⊗ₜ[B] m i) = ⊤) :
    ∃ u ∉ q, ∀ x : M, u • x ∈ Submodule.span B (Set.range m) := by
  set N₀ := Submodule.span B (Set.range m)
  have hsub : Subsingleton (q.ResidueField ⊗[B] (M ⧸ N₀)) := by
    have hsurj : Function.Surjective (N₀.mkQ.lTensor q.ResidueField) :=
      LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)
    have hzero : ∀ y, N₀.mkQ.lTensor q.ResidueField y = 0 := by
      intro y
      have hy : y ∈ Submodule.span q.ResidueField
          (Set.range fun i => (1 : q.ResidueField) ⊗ₜ[B] m i) := by
        simp [hspan]
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        rw [LinearMap.lTensor_tmul, Submodule.mkQ_apply,
          (Submodule.Quotient.mk_eq_zero N₀).mpr (Submodule.subset_span ⟨i, rfl⟩),
          TensorProduct.tmul_zero]
      | zero => exact map_zero _
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul a x _ hx =>
        rw [show N₀.mkQ.lTensor q.ResidueField (a • x) =
          a • N₀.mkQ.lTensor q.ResidueField x from
            (TensorProduct.AlgebraTensorModule.lTensor q.ResidueField q.ResidueField
              N₀.mkQ).map_smul a x,
          hx, smul_zero]
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := hsurj a
    obtain ⟨b, rfl⟩ := hsurj b
    rw [hzero, hzero]
  have hnot : (⟨q, inferInstance⟩ : PrimeSpectrum B) ∉ Module.support B (M ⧸ N₀) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    exact not_nontrivial_iff_subsingleton.mpr hsub
  exact exists_notMem_smul_mem_of_notMem_support_quotient N₀ q hnot

/-- The preimage in `B` of the extension of `L` to `B ⧸ I B` is `L + I B`. -/
theorem comap_mk_map_mk (L : Ideal B) :
    (L.map (Ideal.Quotient.mk (I.map (algebraMap R B)))).comap
      (Ideal.Quotient.mk (I.map (algebraMap R B))) = L ⊔ I.map (algebraMap R B) := by
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker]

/-- **The kernel of `π` is cut out by the chosen coordinates near `q`.** If the classes of
`t_i ∈ ker π` span the fibre at `q` of the conormal module, then some `v ∉ q` multiplies `ker π`
into `I B + (t_i)`. -/
theorem exists_notMem_mul_mem_of_span_residueField [Algebra.Smooth R B]
    [Algebra.Smooth (R ⧸ I) C] (hπ : Function.Surjective π) (q : Ideal B) [q.IsPrime]
    (hq : RingHom.ker π.toRingHom ≤ q) {c : ℕ} (t : Fin c → B)
    (ht : ∀ i, t i ∈ RingHom.ker π.toRingHom)
    (hspan : Submodule.span q.ResidueField (Set.range fun i => (1 : q.ResidueField) ⊗ₜ[B]
        Ideal.toCotangent _ ⟨_, mk_mem_ker_quotientLift I π (ht i)⟩) = ⊤) :
    ∃ v ∉ q, ∀ j ∈ RingHom.ker π.toRingHom,
      v * j ∈ I.map (algebraMap R B) ⊔ Ideal.span (Set.range t) := by
  have := finite_cotangent_ker_quotientLift I π hπ
  set mk := Ideal.Quotient.mk (I.map (algebraMap R B))
  set K := RingHom.ker (quotientLift I π).toRingHom
  obtain ⟨u, huq, hu⟩ := exists_notMem_smul_mem_span_of_span_residueField q _ hspan
  have hIq : I.map (algebraMap R B) ≤ q := (map_le_ker_of_quotient I π).trans hq
  have hker : RingHom.ker mk ≤ q := by rwa [Ideal.mk_ker]
  have hqbar : (q.map mk).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hcomap : (q.map mk).comap mk = q := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr hker
  have hKq : K ≤ q.map mk := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.mem_map_of_mem _ (hq hx)
  have hmk_u : mk u ∉ q.map mk := fun h => huq (hcomap ▸ h)
  have hsK : ∀ i, mk (t i) ∈ K := fun i => mk_mem_ker_quotientLift I π (ht i)
  let s'' : Fin c → K := fun i => ⟨mk (t i), hsK i⟩
  have key : ∀ y : K,
      K.toCotangent y ∈ Submodule.span B (Set.range fun i => K.toCotangent (s'' i)) →
      (y : B ⧸ I.map (algebraMap R B)) ∈ Ideal.span (Set.range fun i => mk (t i)) ⊔ K ^ 2 := by
    intro y hy
    let f : K →ₗ[B] K.Cotangent := K.toCotangent.restrictScalars B
    have hm : (Set.range fun i => K.toCotangent (s'' i)) = f '' Set.range s'' := by
      rw [← Set.range_comp]
      rfl
    rw [hm, ← Submodule.map_span] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have h0 : K.toCotangent (y - z) = 0 := (map_sub _ y z).trans (sub_eq_zero.mpr hzy.symm)
    rw [Ideal.toCotangent_eq_zero] at h0
    have hz' : (z : B ⧸ I.map (algebraMap R B)) ∈ Ideal.span (Set.range fun i => mk (t i)) := by
      have hle : Submodule.map (K.subtype.restrictScalars B) (Submodule.span B (Set.range s'')) ≤
          (Ideal.span (Set.range fun i => mk (t i))).restrictScalars B := by
        rw [Submodule.map_span]
        apply Submodule.span_le.mpr
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        exact Ideal.subset_span ⟨i, rfl⟩
      exact hle ⟨z, hz, rfl⟩
    have hyz : (y : B ⧸ I.map (algebraMap R B)) =
        z + ((y - z : K) : B ⧸ I.map (algebraMap R B)) := by
      simp
    rw [hyz]
    exact Submodule.add_mem_sup hz' h0
  have huK : ∀ x ∈ K, mk u * x ∈ Ideal.span (Set.range fun i => mk (t i)) ⊔ K ^ 2 := by
    intro x hx
    refine key ⟨mk u * x, K.mul_mem_left _ hx⟩ ?_
    have : K.toCotangent ⟨mk u * x, K.mul_mem_left _ hx⟩ = u • K.toCotangent ⟨x, hx⟩ := by
      rw [← algebraMap_smul (B ⧸ I.map (algebraMap R B)) u, ← map_smul]
      rfl
    rw [this]
    exact hu _
  obtain ⟨u', hu'q, hu'⟩ := exists_notMem_mul_mem_span_of_mul_mem_span_sup_sq
    (fg_ker_quotientLift I π hπ) (q.map mk) hKq (fun i => mk (t i)) hsK hmk_u huK
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective u'
  refine ⟨v, fun h => hu'q (Ideal.mem_map_of_mem _ h), fun j hj => ?_⟩
  have h := hu' (mk j) (mk_mem_ker_quotientLift I π hj)
  rw [← map_mul] at h
  have hspan_map : Ideal.span (Set.range fun i => mk (t i)) =
      (Ideal.span (Set.range t)).map mk := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hspan_map] at h
  have := (comap_mk_map_mk I (Ideal.span (Set.range t))).le h
  rwa [sup_comm] at this

/-- **The Jacobian criterion at `q`.** If the classes of `t_i ∈ ker π` are linearly independent
in the fibre at `q` of the conormal module, then `B_q` is formally smooth over `R[x_1, …, x_c]`
along `x_i ↦ t_i`. -/
theorem formallySmooth_localization_of_linearIndependent [Algebra.Smooth R B]
    [Algebra.Smooth (R ⧸ I) C] (hπ : Function.Surjective π) (q : Ideal B) [q.IsPrime]
    {c : ℕ} (t : Fin c → B) (ht : ∀ i, t i ∈ RingHom.ker π.toRingHom)
    (hli : LinearIndependent q.ResidueField (fun i => (1 : q.ResidueField) ⊗ₜ[B]
        Ideal.toCotangent _ ⟨_, mk_mem_ker_quotientLift I π (ht i)⟩)) :
    letI : Algebra (MvPolynomial (Fin c) R) B := (MvPolynomial.aeval t).toRingHom.toAlgebra
    Algebra.FormallySmooth (MvPolynomial (Fin c) R) (Localization.AtPrime q) := by
  let : Algebra (MvPolynomial (Fin c) R) B := (MvPolynomial.aeval t).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin c) R) B := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact ((MvPolynomial.aeval t).commutes a).symm)
  set P := MvPolynomial (Fin c) R
  set S := Localization.AtPrime q
  set κ := q.ResidueField
  obtain ⟨Λ, hΛ⟩ := exists_kaehler_to_cotangent I π hπ
  set M := (RingHom.ker (quotientLift I π).toRingHom).Cotangent
  set μ := KaehlerDifferential.mapBaseChange R P S
  -- the test map `κ ⊗_S Ω_{S/R} → κ ⊗_B M`
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale R B S
  let g₀ : Ω[B⁄R] →ₗ[B] κ ⊗[B] M := (TensorProduct.mk B κ M 1) ∘ₗ Λ
  let τ₀ : Ω[S⁄R] →ₗ[S] κ ⊗[B] M := hbc.lift g₀
  let τ : κ ⊗[S] Ω[S⁄R] →ₗ[κ] κ ⊗[B] M := τ₀.liftBaseChange κ
  let μκ : κ ⊗[S] (S ⊗[P] Ω[P⁄R]) →ₗ[κ] κ ⊗[S] Ω[S⁄R] :=
    TensorProduct.AlgebraTensorModule.lTensor κ κ μ
  let β := ((KaehlerDifferential.mvPolynomialBasis R (Fin c)).baseChange S).baseChange κ
  have hτμ : ∀ i, τ (μκ (β i)) = (1 : κ) ⊗ₜ[B]
      Ideal.toCotangent _ ⟨_, mk_mem_ker_quotientLift I π (ht i)⟩ := by
    intro i
    have hβ : β i = (1 : κ) ⊗ₜ[S] ((1 : S) ⊗ₜ[P] D R P (MvPolynomial.X i)) := by
      rw [Module.Basis.baseChange_apply, Module.Basis.baseChange_apply,
        KaehlerDifferential.mvPolynomialBasis_apply]
    have hX : algebraMap P S (MvPolynomial.X i) = algebraMap B S (t i) := by
      rw [IsScalarTower.algebraMap_apply P B S]
      congr 1
      exact MvPolynomial.aeval_X t i
    rw [hβ, show μκ ((1 : κ) ⊗ₜ[S] ((1 : S) ⊗ₜ[P] D R P (MvPolynomial.X i))) =
      (1 : κ) ⊗ₜ[S] μ ((1 : S) ⊗ₜ[P] D R P (MvPolynomial.X i)) from rfl,
      LinearMap.liftBaseChange_one_tmul, KaehlerDifferential.mapBaseChange_tmul, one_smul,
      KaehlerDifferential.map_D, hX,
      ← KaehlerDifferential.map_D R R B S (t i), IsBaseChange.lift_eq]
    change (1 : κ) ⊗ₜ[B] Λ (D R B (t i)) = _
    rw [hΛ _ (ht i)]
  have hinj : Function.Injective μκ := by
    refine LinearMap.injective_of_linearIndependent (v := β) β.span_eq (.of_comp τ ?_)
    rwa [show τ ∘ (μκ ∘ β) = _ from funext hτμ]
  -- the Jacobian criterion over the local ring `S`
  have : Module.Free S Ω[S⁄R] := Module.free_of_flat_of_isLocalRing
  obtain ⟨μ', hμ'⟩ : ∃ μ' : Ω[S⁄R] →ₗ[S] S ⊗[P] Ω[P⁄R], μ' ∘ₗ μ = LinearMap.id := by
    rw [IsLocalRing.split_injective_iff_lTensor_residueField_injective,
      ← TensorProduct.AlgebraTensorModule.coe_lTensor (A := κ)]
    exact hinj
  have hμinj : Function.Injective μ := by
    intro x y hxy
    simpa [← LinearMap.comp_apply, hμ'] using congrArg μ' hxy
  have hH1 : Subsingleton (Algebra.H1Cotangent P S) := subsingleton_of_forall_eq 0 fun z => by
    obtain ⟨w, hw⟩ := (Algebra.H1Cotangent.exact_map_δ R P S z).mp <| hμinj <| by
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R P S).apply_apply_eq_zero z
    rw [← hw, Subsingleton.elim w 0, map_zero]
  have h21 := (KaehlerDifferential.exact_mapBaseChange_map R P S).split_tfae'.out 2 1
  obtain ⟨-, l, hl⟩ := h21.mp ⟨KaehlerDifferential.map_surjective R P S, μ', hμ'⟩
  exact ⟨Module.Projective.of_split l (KaehlerDifferential.map R P S S) hl, hH1⟩

/-- **A closed immersion of smooth schemes is locally cut out by part of a coordinate system.**
Let `B` be smooth over `R`, let `π : B → C` be surjective with `C` smooth over `R ⧸ I`, and let
`q ⊇ ker π` be a prime. Then for some `g ∉ q` there are `t_1, …, t_c ∈ B_g` with `B_g` flat
(indeed smooth) over `R[x_1, …, x_c]` along `x_i ↦ t_i` and `(ker π) B_g = I B_g + (t_1, …, t_c)`.
-/
theorem exists_localizationAway_flat_mvPolynomial_of_smooth [Algebra.Smooth R B]
    [Algebra.Smooth (R ⧸ I) C] (hπ : Function.Surjective π) (q : Ideal B) [q.IsPrime]
    (hq : RingHom.ker π.toRingHom ≤ q) :
    ∃ g : B, g ∉ q ∧ ∃ (c : ℕ) (t : Fin c → Localization.Away g),
      (MvPolynomial.aeval t : MvPolynomial (Fin c) R →ₐ[R] Localization.Away g).toRingHom.Flat ∧
      (RingHom.ker π.toRingHom).map (algebraMap B (Localization.Away g)) =
        I.map (algebraMap R (Localization.Away g)) ⊔ Ideal.span (Set.range t) := by
  obtain ⟨c, t, ht, hli, hspan⟩ := exists_basis_residueField_cotangent I π hπ q
  obtain ⟨v, hvq, hv⟩ := exists_notMem_mul_mem_of_span_residueField I π hπ q hq t ht hspan
  let : Algebra (MvPolynomial (Fin c) R) B := (MvPolynomial.aeval t).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin c) R) B := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact ((MvPolynomial.aeval t).commutes a).symm)
  have : Algebra.IsSmoothAt (MvPolynomial (Fin c) R) q :=
    formallySmooth_localization_of_linearIndependent I π hπ q t ht hli
  have : Algebra.FinitePresentation (MvPolynomial (Fin c) R) B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ B
  obtain ⟨f, hfq, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth (MvPolynomial (Fin c) R) q
  have hsub := (Algebra.basicOpen_subset_smoothLocus_iff_smooth (R := MvPolynomial (Fin c) R)
    (f := f)).mpr hsm
  have hsm' : Algebra.Smooth (MvPolynomial (Fin c) R) (Localization.Away (f * v)) :=
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.mp
      (fun x hx => hsub (PrimeSpectrum.basicOpen_mul_le_left f v hx))
  have hg : f * v ∉ q := fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hfq hvq
  refine ⟨f * v, hg, c, fun i => algebraMap B _ (t i), ?_, ?_⟩
  · have heq : (MvPolynomial.aeval (fun i => algebraMap B (Localization.Away (f * v)) (t i)) :
        MvPolynomial (Fin c) R →ₐ[R] Localization.Away (f * v)).toRingHom =
        algebraMap (MvPolynomial (Fin c) R) (Localization.Away (f * v)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]
        rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin c) R)]
        rfl
      · intro i
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
        rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin c) R) B]
        congr 1
        exact (MvPolynomial.aeval_X t i).symm
    rw [heq]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · have hunit : IsUnit (algebraMap B (Localization.Away (f * v)) v) := by
      have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f * v)) (f * v)
      rw [map_mul] at this
      exact isUnit_of_mul_isUnit_right this
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro j hj
      rw [Ideal.mem_comap]
      have h := Ideal.mem_map_of_mem (algebraMap B (Localization.Away (f * v))) (hv j hj)
      rw [Ideal.map_sup, Ideal.map_map, Ideal.map_span, ← IsScalarTower.algebraMap_eq,
        map_mul] at h
      obtain ⟨w, hw⟩ := hunit.exists_left_inv
      have := Ideal.mul_mem_left _ w h
      rw [← mul_assoc, hw, one_mul] at this
      convert this using 3
      ext x
      simp
    · refine sup_le ?_
        (Ideal.span_le.mpr (Set.range_subset_iff.mpr fun i => Ideal.mem_map_of_mem _ (ht i)))
      rw [IsScalarTower.algebraMap_eq R B (Localization.Away (f * v)), ← Ideal.map_map]
      exact Ideal.map_mono (map_le_ker_of_quotient I π)

end Conormal

end Crystalline
