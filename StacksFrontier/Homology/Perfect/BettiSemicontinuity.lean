module

public import Mathlib
public import StacksFrontier.Homology.Perfect.MinimalRepresentative
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Upper semicontinuity of the derived-fibre Betti numbers

Let `R` be a commutative ring and let `K` be a perfect object of the derived category `D(R)`.
For a prime `p` of `R` the derived fibre of `K` at `p` is `K ⊗ᴸ_R κ(p)`, and its `i`-th
cohomology is a finite-dimensional `κ(p)`-vector space. This module proves that its dimension,
as a function of `p` on the prime spectrum of `R`, is upper semicontinuous: this is the affine,
module-theoretic case of part (2) of [stacks 0BDI].

## Main definitions

* `StacksDraft.Perfect.fibreBetti` is the function on `PrimeSpectrum R` sending `p` to
  `dim_{κ(p)} Hⁱ(K ⊗ᴸ_R κ(p))`.

## Main results

* `StacksDraft.Perfect.upperSemicontinuous_finrank_homology_totalDerived`: the fibre dimension
  function of a perfect object is upper semicontinuous, stated directly in terms of the
  canonical total derived extension of scalars to the residue fields.
* `StacksDraft.Perfect.upperSemicontinuous_fibreBetti`: the same statement phrased with
  `fibreBetti`.
* `StacksDraft.Perfect.finrank_homology_le_of_free_term`: the dimension of the `i`-th cohomology
  of a complex of vector spaces is at most the dimension of its term in degree `i`.
* `StacksDraft.Perfect.upperSemicontinuous_finrank_homology_totalDerived_of_isPseudoCoherent`
  and `StacksDraft.Perfect.upperSemicontinuous_fibreBetti_of_isPseudoCoherent`: the same for a
  pseudo-coherent object.
* `StacksDraft.Perfect.upperSemicontinuous_of_eventually_le`: a function with values in `ℕ`
  bounded near each point by its value there is upper semicontinuous.
* `StacksDraft.Perfect.upperSemicontinuous_of_forall_exists_isOpen` and
  `StacksDraft.Perfect.upperSemicontinuous_comp_of_continuous`: upper semicontinuity is local on
  the source and transfers along a continuous map.

## References

* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-! ### Upper semicontinuity of a function with values in `ℕ` -/

/-- A function with values in `ℕ` is upper semicontinuous as soon as it is bounded by its value
at `x` on a neighbourhood of `x`, for every `x`. -/
theorem upperSemicontinuous_of_eventually_le {X : Type*} [TopologicalSpace X]
    (β : X → ℕ) (h : ∀ x : X, ∀ᶠ y in nhds x, β y ≤ β x) :
    UpperSemicontinuous β := by
  intro x n hn
  filter_upwards [h x] with y hy using lt_of_le_of_lt hy hn

/-- Upper semicontinuity of a function with values in `ℕ` transfers along a continuous map. -/
@[sga "3 VIB 4.1" "(i)"]
theorem upperSemicontinuous_comp_of_continuous {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {β : Y → ℕ}
    (h : UpperSemicontinuous β) : UpperSemicontinuous (β ∘ f) :=
  fun x n hn => (hf.continuousAt.eventually_mem (h (f x) n hn))

/-- Upper semicontinuity of a function with values in `ℕ` is local on the source: it suffices
that every point have an open neighbourhood on which the restriction is upper
semicontinuous. -/
theorem upperSemicontinuous_of_forall_exists_isOpen {X : Type*} [TopologicalSpace X] (β : X → ℕ)
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      UpperSemicontinuous (fun y : U => β y.1)) :
    UpperSemicontinuous β := by
  intro x n hn
  obtain ⟨U, hU, hxU, hus⟩ := h x
  have hmap : Filter.map (Subtype.val : U → X) (nhds ⟨x, hxU⟩) = nhds x :=
    hU.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨x, hxU⟩
  rw [← hmap, Filter.eventually_map]
  exact hus ⟨x, hxU⟩ n hn

/-! ### The dimension of cohomology is bounded by the dimension of the term -/

/-- The dimension of the `i`-th cohomology of a cochain complex of vector spaces is at most the
dimension of its term in degree `i`. -/
theorem finrank_homology_le {k : Type u} [Field k]
    (C : CochainComplex (ModuleCat.{v} k) ℤ) (i : ℤ)
    [FiniteDimensional k (C.X i)] :
    Module.finrank k (C.homology i) ≤ Module.finrank k (C.X i) := by
  have hmono : Function.Injective (ModuleCat.Hom.hom (C.iCycles i)) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hfin : FiniteDimensional k (C.cycles i) :=
    FiniteDimensional.of_injective (ModuleCat.Hom.hom (C.iCycles i)) hmono
  have hepi : Function.Surjective (ModuleCat.Hom.hom (C.homologyπ i)) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  exact le_trans (LinearMap.finrank_le_finrank_of_surjective hepi)
    (LinearMap.finrank_le_finrank_of_injective hmono)

/-- If the term in degree `i` of a cochain complex of vector spaces is free of rank `n`, the
`i`-th cohomology has dimension at most `n`. -/
theorem finrank_homology_le_of_free_term {k : Type u} [Field k]
    (C : CochainComplex (ModuleCat.{max v u} k) ℤ) (i : ℤ) (n : ℕ)
    (e : C.X i ≅ ModuleCat.of k (ULift.{v} (Fin n → k))) :
    Module.finrank k (C.homology i) ≤ n := by
  have := Module.Finite.equiv e.toLinearEquiv.symm
  exact (finrank_homology_le C i).trans_eq (by simp [e.toLinearEquiv.finrank_eq])

/-! ### The dimension of the cohomology of a derived object -/

/-- The dimension of the `i`-th cohomology of an object of `D(k)` is invariant under
isomorphism. -/
theorem finrank_homologyFunctor_eq_of_iso {k : Type u} [Field k]
    {X Y : DerivedCategory (ModuleCat.{max v u} k)} (e : X ≅ Y) (i : ℤ) :
    Module.finrank k ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj X) =
      Module.finrank k ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj Y) :=
  (((DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).mapIso e).toLinearEquiv).finrank_eq

/-- The `i`-th cohomology of the image of a complex in the derived category is its `i`-th
cohomology. -/
theorem finrank_homologyFunctor_Q_obj {k : Type u} [Field k]
    (C : CochainComplex (ModuleCat.{max v u} k) ℤ) (i : ℤ) :
    Module.finrank k ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj
        (DerivedCategory.Q.obj C)) =
      Module.finrank k (C.homology i) :=
  (((DerivedCategory.homologyFunctorFactors
    (ModuleCat.{max v u} k) i).app C).toLinearEquiv).finrank_eq

/-! ### The Betti numbers of the derived fibres -/

/-- The `i`-th derived-fibre Betti number of an object `K` of `D(R)`: the dimension over the
residue field `κ(p)` of the `i`-th cohomology of the derived fibre `K ⊗ᴸ_R κ(p)`. -/
noncomputable def fibreBetti {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max v u} R)) (i : ℤ) : PrimeSpectrum R → ℕ :=
  fun p => Module.finrank p.asIdeal.ResidueField
    ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} p.asIdeal.ResidueField) i).obj
      ((totalDerivedExtensionScalars.{u, u, v}
        (algebraMap R p.asIdeal.ResidueField)).functor.obj K))

/-- If an object `X` of `D(k)` is isomorphic to the derived base change of `Q.obj F` for a bounded
above complex `F` of projectives, the dimension of its `i`-th cohomology is that of the `i`-th
cohomology of the degreewise base change of `F`. -/
private theorem finrank_homologyFunctor_eq_of_iso_totalDerived_Q_obj {R : Type u} [CommRing R]
    {k : Type u} [Field k] (ψ : R →+* k) (F : CochainComplex (ModuleCat.{max v u} R) ℤ) (b : ℤ)
    [F.IsStrictlyLE b] [∀ j, Projective (F.X j)] {X : DerivedCategory (ModuleCat.{max v u} k)}
    (e : X ≅ (totalDerivedExtensionScalars.{u, u, v} ψ).functor.obj (DerivedCategory.Q.obj F))
    (i : ℤ) :
    Module.finrank k ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj X) =
      Module.finrank k ((((ModuleCat.extendScalars.{u, u, max v u} ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj F).homology i) := by
  have := (totalDerivedExtensionScalars.{u, u, v} ψ).comparison_isIso_of_projective F b
  have eiso : X ≅ DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, max v u} ψ
      ).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) :=
    e ≪≫ asIso ((totalDerivedExtensionScalars.{u, u, v} ψ).comparison.app F) ≪≫ Iso.refl _
  rw [finrank_homologyFunctor_eq_of_iso eiso i, finrank_homologyFunctor_Q_obj]

/-- Let `R` be a commutative ring and let `K` be a perfect object of `D(R)`. For every `i` the
function sending a prime `p` of `R` to `dim_{κ(p)} Hⁱ(K ⊗ᴸ_R κ(p))` is upper semicontinuous on
`PrimeSpectrum R`. -/
@[ega "III 7.6.9" "(i), special case"]
theorem upperSemicontinuous_finrank_homology_totalDerived {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max v u} R)) (hK : IsPerfect K) (i : ℤ) :
    UpperSemicontinuous (fun q : PrimeSpectrum R =>
      Module.finrank q.asIdeal.ResidueField
        ((DerivedCategory.homologyFunctor
            (ModuleCat.{max v u} q.asIdeal.ResidueField) i).obj
          ((totalDerivedExtensionScalars.{u, u, v}
            (algebraMap R q.asIdeal.ResidueField)).functor.obj K))) := by
  have hKpc : StacksDraft.PseudoCoherence.IsPseudoCoherent K :=
    ((isPerfect_iff_pseudoCoherent_and_finiteTorDimension.{u, v} K).1.mp hK).1
  refine upperSemicontinuous_of_eventually_le _ fun p => ?_
  obtain ⟨-, -, f, hf, P, a, b, hPa, hPb, hPX, ⟨eP⟩⟩ :=
    exists_away_bounded_free_complex_representing.{u, v} p.asIdeal K hK
  set n : ℕ := Module.finrank p.asIdeal.ResidueField
    ((DerivedCategory.homologyFunctor
        (ModuleCat.{max v u} p.asIdeal.ResidueField) i).obj
      ((totalDerivedExtensionScalars.{u, u, v}
        (algebraMap R p.asIdeal.ResidueField)).functor.obj K))
  refine Filter.eventually_of_mem (PrimeSpectrum.isOpen_basicOpen.mem_nhds
    ((PrimeSpectrum.mem_basicOpen f p).2 hf)) fun q hq => ?_
  have hunit : IsUnit (algebraMap R q.asIdeal.ResidueField f) := isUnit_iff_ne_zero.2 fun h =>
    (PrimeSpectrum.mem_basicOpen f q).1 hq (Ideal.algebraMap_residueField_eq_zero.1 h)
  set g : Localization.Away f →+* q.asIdeal.ResidueField :=
    Localization.awayLift (algebraMap R q.asIdeal.ResidueField) f hunit
  have hcomp : g.comp (algebraMap R (Localization.Away f)) =
      algebraMap R q.asIdeal.ResidueField := IsLocalization.Away.lift_comp f hunit
  obtain ⟨ecomp⟩ := totalDerived_comp_of_isPseudoCoherent_of_eq.{u, v} hcomp
    (totalDerivedExtensionScalars.{u, u, v} (algebraMap R (Localization.Away f)))
    (totalDerivedExtensionScalars.{u, u, v} g)
    (totalDerivedExtensionScalars.{u, u, v} (algebraMap R q.asIdeal.ResidueField)) hKpc
  let := hPb
  have hPproj : ∀ j : ℤ, Projective (P.X j) := fun j =>
    Projective.of_iso (hPX j).some.symm
      (ModuleCat.projective_of_free (Module.Free.chooseBasis (Localization.Away f) _))
  let := hPproj
  let Dg := totalDerivedExtensionScalars.{u, u, v} g
  let Pκ := ((ModuleCat.extendScalars.{u, u, max v u} g).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P
  rw [finrank_homologyFunctor_eq_of_iso_totalDerived_Q_obj.{u, v} g P b
    (ecomp.symm ≪≫ Dg.functor.mapIso eP.symm) i]
  exact finrank_homology_le_of_free_term.{u, v} Pκ i n
    ((ModuleCat.extendScalars.{u, u, max v u} g).mapIso (hPX i).some ≪≫
      (extendScalars_standard_free_iso.{u, v} g n).some)

/-- The `i`-th derived-fibre Betti number of a perfect object of `D(R)` is an upper
semicontinuous function on `PrimeSpectrum R`. -/
@[ega "III 7.6.9" "(i), special case"]
theorem upperSemicontinuous_fibreBetti {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max v u} R)) (hK : IsPerfect K) (i : ℤ) :
    UpperSemicontinuous (fibreBetti.{u, v} K i) :=
  upperSemicontinuous_finrank_homology_totalDerived.{u, v} K hK i

/-! ### From perfect to pseudo-coherent objects -/

/-- Two cochain complexes of vector spaces whose terms in degrees `i - 1`, `i` and `i + 1` are
identified compatibly with the differentials have cohomology of the same dimension in degree
`i`. -/
theorem finrank_homology_eq_of_window_iso {k : Type u} [Field k]
    (C D : CochainComplex (ModuleCat.{max v u} k) ℤ) (i : ℤ)
    (e₁ : C.X (i - 1) ≅ D.X (i - 1)) (e₂ : C.X i ≅ D.X i) (e₃ : C.X (i + 1) ≅ D.X (i + 1))
    (h₁ : e₁.hom ≫ D.d (i - 1) i = C.d (i - 1) i ≫ e₂.hom)
    (h₂ : e₂.hom ≫ D.d i (i + 1) = C.d i (i + 1) ≫ e₃.hom) :
    Module.finrank k (C.homology i) = Module.finrank k (D.homology i) := by
  have hprev : (ComplexShape.up ℤ).prev i = i - 1 := by simp
  have hnext : (ComplexShape.up ℤ).next i = i + 1 := by simp
  exact ((C.homologyIsoSc' (i - 1) i (i + 1) hprev hnext) ≪≫
    ShortComplex.homologyMapIso (ShortComplex.isoMk e₁ e₂ e₃ h₁ h₂) ≪≫
    (D.homologyIsoSc' (i - 1) i (i + 1) hprev hnext).symm).toLinearEquiv.finrank_eq

/-- The differential of a stupid truncation, in degrees that the embedding reaches: the
identification of its terms with those of the ambient complex is compatible with the
differentials. -/
theorem stupidTruncXIso_hom_d {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    {C : Type*} [Category C] [Limits.HasZeroMorphisms C] [Limits.HasZeroObject C]
    (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff]
    {i j : ι} {i' j' : ι'} (hi : e.f i = i') (hj : e.f j = j') :
    (K.stupidTrunc e).d i' j' ≫ (K.stupidTruncXIso e hj).hom =
      (K.stupidTruncXIso e hi).hom ≫ K.d i' j' := by
  subst hi hj
  simp only [HomologicalComplex.stupidTrunc, HomologicalComplex.stupidTruncXIso, Iso.trans_hom,
    HomologicalComplex.extend_d_eq _ _ rfl rfl, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.cancel_iso_hom_left]
  change K.d (e.f i) (e.f j) ≫ eqToHom rfl = eqToHom rfl ≫ K.d (e.f i) (e.f j)
  simp

/-- For a bounded above complex `F` of projectives, the dimension of the `i`-th cohomology of the
derived base change of `Q.obj F` is that of the `i`-th cohomology of the degreewise base change of
`F`. -/
theorem finrank_homologyFunctor_totalDerived_Q_obj {R : Type u} [CommRing R] {k : Type u}
    [Field k] (ψ : R →+* k) (F : CochainComplex (ModuleCat.{max v u} R) ℤ) (b : ℤ)
    [F.IsStrictlyLE b] [∀ j, Projective (F.X j)] (i : ℤ) :
    Module.finrank k ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj
        ((totalDerivedExtensionScalars.{u, u, v} ψ).functor.obj (DerivedCategory.Q.obj F))) =
      Module.finrank k ((((ModuleCat.extendScalars.{u, u, max v u} ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj F).homology i) :=
  finrank_homologyFunctor_eq_of_iso_totalDerived_Q_obj.{u, v} ψ F b (Iso.refl _) i

/-- Let `R` be a commutative ring and let `K` be a pseudo-coherent object of `D(R)`. For every `i`
the function sending a prime `p` of `R` to `dim_{κ(p)} Hⁱ(K ⊗ᴸ_R κ(p))` is upper semicontinuous
on `PrimeSpectrum R`. -/
@[ega "III 6.1.2" "special case",
  ega "III 7.6.9" "(i), special case",
  sga "6 III 5.6" "(i), special case",
  sga "6 III 5.7" "(ii), special case"]
theorem upperSemicontinuous_finrank_homology_totalDerived_of_isPseudoCoherent
    {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat.{max v u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ) :
    UpperSemicontinuous (fun q : PrimeSpectrum R =>
      Module.finrank q.asIdeal.ResidueField
        ((DerivedCategory.homologyFunctor
            (ModuleCat.{max v u} q.asIdeal.ResidueField) i).obj
          ((totalDerivedExtensionScalars.{u, u, v}
            (algebraMap R q.asIdeal.ResidueField)).functor.obj K))) := by
  obtain ⟨F, hF, ⟨eF⟩⟩ := hK
  obtain ⟨b, hb⟩ := hF.upperBound
  let := hb
  have hFfree : ∀ j : ℤ, Module.Free R (F.X j) := fun j => (hF.finiteFree j).2
  let := hFfree
  have hFproj : ∀ j : ℤ, Projective (F.X j) := fun j =>
    ModuleCat.projective_of_free (Module.Free.chooseBasis R (F.X j))
  let := hFproj
  have hGfree : ∀ j : ℤ,
      Module.Finite R ((F.stupidTrunc (ComplexShape.embeddingUpIntGE (i - 1))).X j) ∧
        Module.Free R ((F.stupidTrunc (ComplexShape.embeddingUpIntGE (i - 1))).X j) := by
    intro j
    by_cases hj : ∃ n : ℕ, (ComplexShape.embeddingUpIntGE (i - 1)).f n = j
    · obtain ⟨n, hn⟩ := hj
      have eiso := (F.stupidTruncXIso (ComplexShape.embeddingUpIntGE (i - 1)) hn).toLinearEquiv
      obtain ⟨_, _⟩ := hF.finiteFree j
      exact ⟨Module.Finite.equiv eiso.symm, Module.Free.of_equiv eiso.symm⟩
    · have hz : Limits.IsZero
          ((F.stupidTrunc (ComplexShape.embeddingUpIntGE (i - 1))).X j) :=
        F.isZero_stupidTrunc_X _ j (by simpa using hj)
      have := ModuleCat.isZero_iff_subsingleton.mp hz
      exact ⟨Module.Finite.of_finite, Module.Free.of_subsingleton R _⟩
  have hGproj : ∀ j : ℤ,
      Projective ((F.stupidTrunc (ComplexShape.embeddingUpIntGE (i - 1))).X j) := fun j => by
    have := (hGfree j).2
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis R _)
  let := hGproj
  have hGperf : IsPerfect (DerivedCategory.Q.obj
      (F.stupidTrunc (ComplexShape.embeddingUpIntGE (i - 1)))) := by
    refine ⟨F.stupidTrunc (ComplexShape.embeddingUpIntGE (i - 1)), i - 1, b,
      inferInstance, inferInstance, fun j => (hGfree j).1, fun j => ?_, ⟨Iso.refl _⟩⟩
    have := (hGfree j).2
    exact Module.Projective.of_basis (Module.Free.chooseBasis R _)
  have key : (fun q : PrimeSpectrum R =>
      Module.finrank q.asIdeal.ResidueField
        ((DerivedCategory.homologyFunctor
            (ModuleCat.{max v u} q.asIdeal.ResidueField) i).obj
          ((totalDerivedExtensionScalars.{u, u, v}
            (algebraMap R q.asIdeal.ResidueField)).functor.obj K))) =
      fun q : PrimeSpectrum R =>
      Module.finrank q.asIdeal.ResidueField
        ((DerivedCategory.homologyFunctor
            (ModuleCat.{max v u} q.asIdeal.ResidueField) i).obj
          ((totalDerivedExtensionScalars.{u, u, v}
            (algebraMap R q.asIdeal.ResidueField)).functor.obj
            (DerivedCategory.Q.obj
              (F.stupidTrunc (ComplexShape.embeddingUpIntGE (i - 1)))))) := by
    funext q
    rw [finrank_homologyFunctor_eq_of_iso_totalDerived_Q_obj.{u, v} _ F b
        (((totalDerivedExtensionScalars.{u, u, v}
          (algebraMap R q.asIdeal.ResidueField)).functor).mapIso eF.symm) i,
      finrank_homologyFunctor_totalDerived_Q_obj.{u, v} _
        (F.stupidTrunc (ComplexShape.embeddingUpIntGE (i - 1))) b i]
    have h0 : (ComplexShape.embeddingUpIntGE (i - 1)).f 0 = i - 1 := by simp
    have h1 : (ComplexShape.embeddingUpIntGE (i - 1)).f 1 = i := by simp
    have h2 : (ComplexShape.embeddingUpIntGE (i - 1)).f 2 = i + 1 := by simp; ring
    refine (finrank_homology_eq_of_window_iso.{u, v} _ _ i
      ((ModuleCat.extendScalars.{u, u, max v u}
        (algebraMap R q.asIdeal.ResidueField)).mapIso
          (F.stupidTruncXIso (ComplexShape.embeddingUpIntGE (i - 1)) h0))
      ((ModuleCat.extendScalars.{u, u, max v u}
        (algebraMap R q.asIdeal.ResidueField)).mapIso
          (F.stupidTruncXIso (ComplexShape.embeddingUpIntGE (i - 1)) h1))
      ((ModuleCat.extendScalars.{u, u, max v u}
        (algebraMap R q.asIdeal.ResidueField)).mapIso
          (F.stupidTruncXIso (ComplexShape.embeddingUpIntGE (i - 1)) h2))
      ?_ ?_).symm
    · simp only [Functor.mapIso_hom, Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp,
        stupidTruncXIso_hom_d F (ComplexShape.embeddingUpIntGE (i - 1)) h0 h1]
    · simp only [Functor.mapIso_hom, Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp,
        stupidTruncXIso_hom_d F (ComplexShape.embeddingUpIntGE (i - 1)) h1 h2]
  rw [key]
  exact upperSemicontinuous_finrank_homology_totalDerived.{u, v} _ hGperf i

/-- The `i`-th derived-fibre Betti number of a pseudo-coherent object of `D(R)` is an upper
semicontinuous function on `PrimeSpectrum R`. -/
@[ega "III 7.6.9" "(i), special case"]
theorem upperSemicontinuous_fibreBetti_of_isPseudoCoherent {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ) :
    UpperSemicontinuous (fibreBetti.{u, v} K i) :=
  upperSemicontinuous_finrank_homology_totalDerived_of_isPseudoCoherent.{u, v} K hK i

end StacksDraft.Perfect

end
