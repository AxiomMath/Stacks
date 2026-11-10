module

public import StacksFrontier.RingTheory.Smoothing.InseparableResidueField.FlatLocalization

/-!
# Inseparable residue fields: clause (1) of Stacks 07FH with a prescribed residue field

Clause (1) of Stacks 07FH with the residue field of `𝔭` prescribed, and the essential smoothness
of `k[y_1, …, y_m]_𝔭/𝔭^n → Λ_𝔮/𝔮^nΛ_𝔮` when `κ(𝔮)` is finitely generated over `k`.

This is the fifth part of `StacksFrontier.RingTheory.Smoothing.InseparableResidueField`.

## Main results

* `Stacks.Smoothing.exists_mvPolynomial_flat_localization_of_intermediateField`: clause (1) with
  the residue field of `𝔭` prescribed.
-/

@[expose] public section

namespace Stacks.Smoothing

open IsLocalRing MvPolynomial
open scoped TensorProduct

universe u v

/-! ### Stacks 07FH, clause (1) with the residue field of `𝔭` prescribed -/

/-- If an intermediate field `F` of `K/k` is generated over `k` by the images under a ring map
`g : R →+* K` of the elements of a finite subset `S` of `R`, then `Ω[F⁄k]` has a basis given by
the differentials of finitely many of those images. -/
private theorem exists_basis_kaehlerDifferential_of_adjoin {k K : Type*} [Field k] [Field K]
    [Algebra k K] {R : Type*} [CommRing R] (g : R →+* K) (F : IntermediateField k K)
    (S : Finset R)
    (hS : IntermediateField.adjoin k ((fun a => g a) '' (S : Set R)) = F) :
    ∃ (t : ℕ) (lam : Fin t → R) (y : Fin t → F) (b : Module.Basis (Fin t) F (Ω[F⁄k])),
      (∀ j, lam j ∈ S) ∧ (∀ j, (y j : K) = g (lam j)) ∧
        ∀ j, b j = KaehlerDifferential.D k F (y j) := by
  classical
  have hUG : ((fun a => g a) '' (S : Set R)) ⊆ (F : Set K) := by
    rw [← hS]
    exact IntermediateField.subset_adjoin k _
  have hspanD := span_derivation_eq_top_of_adjoin_eq F ((fun a => g a) '' (S : Set R)) hUG hS
  have hfin : Finite ↥((fun a => g a) '' (S : Set R)) := (S.finite_toSet.image _).to_subtype
  have hfd : FiniteDimensional F (Ω[F⁄k]) :=
    Module.finite_def.mpr (hspanD ▸ Submodule.fg_span (Set.finite_range _))
  obtain ⟨t, b, wmap, hb⟩ := exists_basis_fin_range _ hspanD
  have hmem : ∀ j, ∃ a : R, a ∈ S ∧ g a = ((wmap j : K)) := by
    intro j
    obtain ⟨a, haS, hae⟩ := (wmap j).2
    exact ⟨a, Finset.mem_coe.mp haS, hae⟩
  choose lam hlamS hlameq using hmem
  exact ⟨t, lam, fun j => ⟨(wmap j : K), hUG (wmap j).2⟩, b, hlamS,
    fun j => (hlameq j).symm, hb⟩

/-- The construction shared by the two theorems below: from a family `lam` of elements of `Λ` whose
residues in `F` have differentials forming a basis of `Ω[F⁄k]`, and a way of choosing, in each
local quotient of `Λ_𝔮`, elements of `𝔮` whose images generate its maximal ideal, build `φ` with
`g : k[y_1, …, y_m]_𝔭 → Λ_𝔮` flat, `𝔭 Λ_𝔮 = 𝔮 Λ_𝔮`, and the first `t` variables sent to `lam`. -/
private theorem exists_mvPolynomial_flat_localization_of_basis {k Λ : Type u} [Field k]
    [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ] [Algebra.IsGeometricallyRegular k Λ]
    (p : ℕ) [Fact p.Prime] [CharP k p] (𝔮 : Ideal Λ) [𝔮.IsPrime]
    (F : IntermediateField k (ResidueField (Localization.AtPrime 𝔮)))
    [Algebra.EssFiniteType k F] (T : Λ → Prop) {t : ℕ} (lam : Fin t → Λ) (hlam : ∀ j, T (lam j))
    (yF : Fin t → F) (bas : Module.Basis (Fin t) F (Ω[F⁄k]))
    (hbas : ∀ j, bas j = KaehlerDifferential.D k F (yF j))
    (hyF : ∀ j, (yF j : ResidueField (Localization.AtPrime 𝔮))
      = residue (Localization.AtPrime 𝔮) (algebraMap Λ (Localization.AtPrime 𝔮) (lam j)))
    (hmu : ∀ (J : Ideal (Localization.AtPrime 𝔮)) [IsLocalRing (Localization.AtPrime 𝔮 ⧸ J)],
      ∃ (r : ℕ) (mu : Fin r → Λ), (∀ j, mu j ∈ 𝔮 ∧ T (mu j)) ∧
        Ideal.map (Ideal.Quotient.mk J) (maximalIdeal (Localization.AtPrime 𝔮))
          = Ideal.span (Set.range fun j => Ideal.Quotient.mk J
            (algebraMap Λ (Localization.AtPrime 𝔮) (mu j))) ∧
        (maximalIdeal (Localization.AtPrime 𝔮 ⧸ J)).spanFinrank = r) :
    ∃ (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
      (g : Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮) →+* Localization.AtPrime 𝔮),
      Ideal.map ((algebraMap Λ (Localization.AtPrime 𝔮)).comp φ.toRingHom)
          (Ideal.comap φ.toRingHom 𝔮)
        = Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) 𝔮 ∧
      (∀ f, g (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) f)
          = algebraMap Λ (Localization.AtPrime 𝔮) (φ f)) ∧
      g.Flat ∧ (∀ i, T (φ (MvPolynomial.X i))) ∧
      (∀ i, residue (Localization.AtPrime 𝔮)
        (algebraMap Λ (Localization.AtPrime 𝔮) (φ (MvPolynomial.X i))) ∈ F) ∧
      IsLocalHom g ∧
      Ideal.map g (maximalIdeal (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)))
        = maximalIdeal (Localization.AtPrime 𝔮) ∧
      (∀ a : k, g (algebraMap k (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) a)
        = algebraMap k (Localization.AtPrime 𝔮) a) ∧
      ∃ a : Fin t → Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮),
        ∀ j, g (a j) = algebraMap Λ (Localization.AtPrime 𝔮) (lam j) := by
  classical
  have hregT : IsRegularRing (k ⊗[k] Λ) :=
    Algebra.IsGeometricallyRegular.isRegularRing_tensorProduct k
  have hregΛ : IsRegularRing Λ :=
    IsRegularRing.of_ringEquiv (Algebra.TensorProduct.lid k Λ).toRingEquiv
  have hregL : IsRegularLocalRing (Localization.AtPrime 𝔮) := inferInstance
  have hgrL : Algebra.IsGeometricallyRegular k (Localization.AtPrime 𝔮) :=
    Algebra.IsGeometricallyRegular.of_isLocalization 𝔮.primeCompl
  set φ' : MvPolynomial (Fin t) k →ₐ[k] Localization.AtPrime 𝔮 :=
    (IsScalarTower.toAlgHom k Λ (Localization.AtPrime 𝔮)).comp (MvPolynomial.aeval lam)
    with hφ'def
  have hφ'X : ∀ j, φ' (MvPolynomial.X j) = algebraMap Λ (Localization.AtPrime 𝔮) (lam j) :=
    fun j => by simp [hφ'def]
  have hφ : ∀ j, residue (Localization.AtPrime 𝔮) (φ' (MvPolynomial.X j))
      = algebraMap F (ResidueField (Localization.AtPrime 𝔮)) (yF j) := by
    intro j
    rw [hφ'X j]
    exact (hyF j).symm
  let instP'L : Algebra (MvPolynomial (Fin t) k) (Localization.AtPrime 𝔮) :=
    φ'.toRingHom.toAlgebra
  have hP'L : (algebraMap (MvPolynomial (Fin t) k) (Localization.AtPrime 𝔮)) = φ'.toRingHom :=
    RingHom.algebraMap_toAlgebra _
  set 𝔭' : Ideal (MvPolynomial (Fin t) k) :=
    Ideal.comap (algebraMap (MvPolynomial (Fin t) k) (Localization.AtPrime 𝔮))
      (maximalIdeal (Localization.AtPrime 𝔮)) with h𝔭'def
  have hunit' : ∀ y : 𝔭'.primeCompl,
      IsUnit (algebraMap (MvPolynomial (Fin t) k) (Localization.AtPrime 𝔮) (y : _)) := by
    intro y
    refine notMem_maximalIdeal.mp fun hmem => ?_
    exact Ideal.mem_primeCompl_iff.mp y.2 (Ideal.mem_comap.mpr hmem)
  let instA₀L : Algebra (Localization.AtPrime 𝔭') (Localization.AtPrime 𝔮) :=
    (IsLocalization.lift hunit').toAlgebra
  have hA₀L : (algebraMap (Localization.AtPrime 𝔭') (Localization.AtPrime 𝔮))
      = IsLocalization.lift hunit' := RingHom.algebraMap_toAlgebra _
  have htow' : IsScalarTower (MvPolynomial (Fin t) k) (Localization.AtPrime 𝔭')
      (Localization.AtPrime 𝔮) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [hA₀L]
    exact (IsLocalization.lift_eq hunit' x).symm
  have hploc : IsLocalization.AtPrime (Localization.AtPrime 𝔭')
      (Ideal.comap φ' (maximalIdeal (Localization.AtPrime 𝔮))) :=
    inferInstanceAs (IsLocalization.AtPrime (Localization.AtPrime 𝔭') 𝔭')
  -- Lemma 07E6 over the first block of variables
  obtain ⟨hflat0, hregfib⟩ :=
    flat_localization_and_regular_quotient_of_basis_kaehlerDifferential p k
      (Localization.AtPrime 𝔮) t F yF bas hbas φ' hφ (Localization.AtPrime 𝔭')
  have hregfib' : IsRegularLocalRing (Localization.AtPrime 𝔮 ⧸
      Ideal.map (algebraMap (MvPolynomial (Fin t) k) (Localization.AtPrime 𝔮)) 𝔭') := hregfib
  have hlocfib : IsLocalRing (Localization.AtPrime 𝔮 ⧸
      Ideal.map (algebraMap (MvPolynomial (Fin t) k) (Localization.AtPrime 𝔮)) 𝔭') :=
    inferInstance
  -- the second block of variables: elements of `𝔮` generating the maximal ideal of the fibre
  obtain ⟨r, mu, hmuT, hspanmu, hcardmu⟩ := hmu
    (Ideal.map (algebraMap (MvPolynomial (Fin t) k) (Localization.AtPrime 𝔮)) 𝔭')
  have hmuq : ∀ j, mu j ∈ 𝔮 := fun j => (hmuT j).1
  have hdim : ringKrullDim (Localization.AtPrime 𝔮 ⧸
      Ideal.map (algebraMap (MvPolynomial (Fin t) k) (Localization.AtPrime 𝔮)) 𝔭')
      = (r : WithBot ℕ∞) := by
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, hcardmu]
  -- the enlarged polynomial algebra
  set φ : MvPolynomial (Fin (t + r)) k →ₐ[k] Λ := MvPolynomial.aeval (Fin.append lam mu)
    with hφdef
  have happ : (Fin.append lam mu) ∘ (Fin.castLE (Nat.le_add_right t r)) = lam := by
    funext j
    exact Fin.append_left lam mu j
  have hφX : ∀ j : Fin (t + r), φ (MvPolynomial.X j) = Fin.append lam mu j := fun j => by
    simp [hφdef]
  let instPL : Algebra (MvPolynomial (Fin (t + r)) k) (Localization.AtPrime 𝔮) :=
    ((algebraMap Λ (Localization.AtPrime 𝔮)).comp φ.toRingHom).toAlgebra
  have hPL : (algebraMap (MvPolynomial (Fin (t + r)) k) (Localization.AtPrime 𝔮))
      = (algebraMap Λ (Localization.AtPrime 𝔮)).comp φ.toRingHom :=
    RingHom.algebraMap_toAlgebra _
  let instP'P : Algebra (MvPolynomial (Fin t) k) (MvPolynomial (Fin (t + r)) k) :=
    ((MvPolynomial.rename (Fin.castLE (Nat.le_add_right t r)) :
      MvPolynomial (Fin t) k →ₐ[k] MvPolynomial (Fin (t + r)) k) :
      MvPolynomial (Fin t) k →+* MvPolynomial (Fin (t + r)) k).toAlgebra
  have hP'P : (algebraMap (MvPolynomial (Fin t) k) (MvPolynomial (Fin (t + r)) k))
      = ((MvPolynomial.rename (Fin.castLE (Nat.le_add_right t r)) :
        MvPolynomial (Fin t) k →ₐ[k] MvPolynomial (Fin (t + r)) k) :
        MvPolynomial (Fin t) k →+* MvPolynomial (Fin (t + r)) k) :=
    RingHom.algebraMap_toAlgebra _
  have htowP : IsScalarTower (MvPolynomial (Fin t) k) (MvPolynomial (Fin (t + r)) k)
      (Localization.AtPrime 𝔮) := by
    refine IsScalarTower.of_algebraMap_eq fun gg => ?_
    rw [hP'P, hPL, hP'L]
    change φ' gg = algebraMap Λ (Localization.AtPrime 𝔮)
      (MvPolynomial.aeval (Fin.append lam mu) (MvPolynomial.rename _ gg))
    rw [MvPolynomial.aeval_rename, happ]
    rfl
  -- `𝔭 = φ⁻¹(𝔮)` is the contraction of the maximal ideal of `Λ_𝔮`
  set 𝔭 : Ideal (MvPolynomial (Fin (t + r)) k) := Ideal.comap φ.toRingHom 𝔮 with h𝔭def
  have hpeq : Ideal.comap (algebraMap (MvPolynomial (Fin (t + r)) k) (Localization.AtPrime 𝔮))
      (maximalIdeal (Localization.AtPrime 𝔮)) = 𝔭 := by
    refine Ideal.ext fun f => ?_
    rw [Ideal.mem_comap, hPL, h𝔭def, Ideal.mem_comap]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔮) 𝔮 (φ f)
  have hsub : (Ideal.comap (algebraMap (MvPolynomial (Fin (t + r)) k)
        (Localization.AtPrime 𝔮)) (maximalIdeal (Localization.AtPrime 𝔮))).primeCompl
      = 𝔭.primeCompl := by
    refine Submonoid.ext fun x => ?_
    simp only [Ideal.mem_primeCompl_iff, hpeq]
  have hinstA : IsLocalization.AtPrime (Localization.AtPrime 𝔭)
      (Ideal.comap (algebraMap (MvPolynomial (Fin (t + r)) k) (Localization.AtPrime 𝔮))
        (maximalIdeal (Localization.AtPrime 𝔮))) :=
    Eq.mpr (congrArg (fun S => IsLocalization S (Localization.AtPrime 𝔭)) hsub) inferInstance
  have hpmem : ∀ f, f ∈ 𝔭 ↔ algebraMap (MvPolynomial (Fin (t + r)) k)
      (Localization.AtPrime 𝔮) f ∈ maximalIdeal (Localization.AtPrime 𝔮) := fun f => by
    rw [← hpeq, Ideal.mem_comap]
  have hunit : ∀ y : 𝔭.primeCompl,
      IsUnit (algebraMap (MvPolynomial (Fin (t + r)) k) (Localization.AtPrime 𝔮) (y : _)) := by
    intro y
    refine notMem_maximalIdeal.mp fun hmem => ?_
    exact Ideal.mem_primeCompl_iff.mp y.2 ((hpmem _).mpr hmem)
  let instAL : Algebra (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮) :=
    (IsLocalization.lift hunit).toAlgebra
  have hAL : (algebraMap (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮))
      = IsLocalization.lift hunit := RingHom.algebraMap_toAlgebra _
  have htowA : IsScalarTower (MvPolynomial (Fin (t + r)) k) (Localization.AtPrime 𝔭)
      (Localization.AtPrime 𝔮) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [hAL]
    exact (IsLocalization.lift_eq hunit x).symm
  -- the ideal-theoretic input of `map_eq_and_flat_of_fibre`
  have hXmem : ∀ j : Fin r,
      algebraMap (MvPolynomial (Fin (t + r)) k) (Localization.AtPrime 𝔮)
        (MvPolynomial.X (Fin.natAdd t j)) = algebraMap Λ (Localization.AtPrime 𝔮) (mu j) := by
    intro j
    rw [hPL]
    change algebraMap Λ (Localization.AtPrime 𝔮) (φ (MvPolynomial.X (Fin.natAdd t j))) = _
    rw [hφX, Fin.append_right]
  have hX : ∀ j : Fin r, algebraMap (MvPolynomial (Fin (t + r)) k) (Localization.AtPrime 𝔮)
      (MvPolynomial.X (Fin.natAdd t j)) ∈ maximalIdeal (Localization.AtPrime 𝔮) := by
    intro j
    rw [hXmem j]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ 𝔮 (mu j)).mpr (hmuq j)
  have hdecomp : Ideal.comap (algebraMap (MvPolynomial (Fin (t + r)) k) (Localization.AtPrime 𝔮))
        (maximalIdeal (Localization.AtPrime 𝔮))
      = Ideal.map (algebraMap (MvPolynomial (Fin t) k) (MvPolynomial (Fin (t + r)) k))
          (Ideal.comap (algebraMap (MvPolynomial (Fin t) k) (Localization.AtPrime 𝔮))
            (maximalIdeal (Localization.AtPrime 𝔮)))
        ⊔ Ideal.span (Set.range fun j : Fin r =>
            (MvPolynomial.X (Fin.natAdd t j) : MvPolynomial (Fin (t + r)) k)) := by
    rw [comap_eq_sup_span (algebraMap (MvPolynomial (Fin (t + r)) k) (Localization.AtPrime 𝔮))
      (maximalIdeal (Localization.AtPrime 𝔮)) hX,
      IsScalarTower.algebraMap_eq (MvPolynomial (Fin t) k) (MvPolynomial (Fin (t + r)) k)
        (Localization.AtPrime 𝔮), hP'P]
  have hgen : Ideal.map (Ideal.Quotient.mk
        (Ideal.map (algebraMap (MvPolynomial (Fin t) k) (Localization.AtPrime 𝔮))
          (Ideal.comap (algebraMap (MvPolynomial (Fin t) k) (Localization.AtPrime 𝔮))
            (maximalIdeal (Localization.AtPrime 𝔮))))) (maximalIdeal (Localization.AtPrime 𝔮))
      = Ideal.span (Set.range fun j : Fin r => Ideal.Quotient.mk
          (Ideal.map (algebraMap (MvPolynomial (Fin t) k) (Localization.AtPrime 𝔮))
            (Ideal.comap (algebraMap (MvPolynomial (Fin t) k) (Localization.AtPrime 𝔮))
              (maximalIdeal (Localization.AtPrime 𝔮))))
          (algebraMap (MvPolynomial (Fin (t + r)) k) (Localization.AtPrime 𝔮)
            (MvPolynomial.X (Fin.natAdd t j)))) :=
    hspanmu.trans (congrArg Ideal.span (congrArg Set.range (funext fun j => by rw [hXmem j])))
  have hregA : IsRegularLocalRing (Localization.AtPrime 𝔭) := inferInstance
  obtain ⟨hmapeq, hflatA⟩ := map_eq_and_flat_of_fibre
    (L := Localization.AtPrime 𝔮) (P' := MvPolynomial (Fin t) k)
    (P := MvPolynomial (Fin (t + r)) k) (A₀ := Localization.AtPrime 𝔭')
    (A := Localization.AtPrime 𝔭)
    (fun j : Fin r => (MvPolynomial.X (Fin.natAdd t j) : MvPolynomial (Fin (t + r)) k))
    hdecomp hgen hdim
  rw [hpeq] at hmapeq
  -- the scalar towers over `k`
  have hlocAL : IsLocalHom (algebraMap (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮)) :=
    isLocalHom_localization (P := MvPolynomial (Fin (t + r)) k)
  have hg : ∀ f, algebraMap (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮)
      (algebraMap (MvPolynomial (Fin (t + r)) k) (Localization.AtPrime 𝔭) f)
      = algebraMap Λ (Localization.AtPrime 𝔮) (φ f) := fun f => by
    rw [← IsScalarTower.algebraMap_apply (MvPolynomial (Fin (t + r)) k)
      (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮), hPL]
    rfl
  refine ⟨t + r, φ, algebraMap (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮), ?_, hg,
    RingHom.flat_algebraMap_iff.mpr hflatA, fun i => ?_, fun i => ?_, hlocAL, ?_, fun a => ?_,
    fun j => algebraMap (MvPolynomial (Fin (t + r)) k) (Localization.AtPrime 𝔭)
      (MvPolynomial.X (Fin.castAdd r j)), fun j => ?_⟩
  · rw [← hPL]
    exact hmapeq.trans (IsLocalization.AtPrime.map_eq_maximalIdeal 𝔮 _).symm
  · -- every variable is sent either into the prescribed set or to a member of the family `mu`
    induction i using Fin.addCases with
    | left j => rw [hφX, Fin.append_left]; exact hlam j
    | right j => rw [hφX, Fin.append_right]; exact (hmuT j).2
  · -- the residues of the variables lie in `F`
    induction i using Fin.addCases with
    | left j =>
      rw [hφX, Fin.append_left, ← hyF j]
      exact (yF j).2
    | right j =>
      rw [hφX, Fin.append_right, (residue_eq_zero_iff _).mpr
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ 𝔮 (mu j)).mpr (hmuq j))]
      exact F.zero_mem
  · rw [map_maximalIdeal_localization (P := MvPolynomial (Fin (t + r)) k)
      (A := Localization.AtPrime 𝔭), hpeq]
    exact hmapeq
  · rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin (t + r)) k) (Localization.AtPrime 𝔭),
      hg, φ.commutes, ← IsScalarTower.algebraMap_apply k Λ (Localization.AtPrime 𝔮)]
  · rw [hg, hφX, Fin.append_left]


/-- **Stacks 07FH, clause (1), with the residue field of `𝔭` prescribed.** Let `k` be a field of
characteristic `p > 0`, let `Λ` be a Noetherian geometrically regular `k`-algebra, let `𝔮` be a
prime of `Λ`, and let `k ⊆ F ⊆ κ(𝔮)` be an intermediate field which is essentially of finite type
over `k` and is generated over `k` by the residues of the elements of a finite subset `S` of `Λ`.
Then there are `m ≥ 0` and a `k`-algebra map `φ : k[y_1, …, y_m] → Λ` such that, with
`𝔭 = φ^{-1}(𝔮)`, one has `𝔭 Λ_𝔮 = 𝔮 Λ_𝔮`, the induced local map `g : k[y_1, …, y_m]_𝔭 → Λ_𝔮` is
flat, and moreover `κ(𝔭)` embeds into `F` compatibly with `g` — so `κ(𝔭) ⊆ F ⊆ κ(𝔮)` — with
`F/κ(𝔭)` finite and separable. A finite family `μ` of elements of `𝔮` whose images generate
`𝔪_{Λ_𝔮}` is taken as an input, and every variable is sent either into `S` or to a member of
`μ`.

This is the source's own construction run at a general coefficient field instead of at `F = k`:
`y_1, …, y_t` are sent to elements of `Λ` whose residues lie in `F` and have differentials forming
a basis of `Ω[F⁄k]`, and `y_{t+1}, …, y_m` are sent to elements of `𝔮` lifting a minimal system of
generators of the maximal ideal of the fibre `Λ_𝔮/𝔭'Λ_𝔮`, so that their residues are `0 ∈ F`.
Lemma [stacks, 07E6] gives flatness over the localization of `k[y_1, …, y_t]` together with
regularity of the fibre, `map_eq_and_flat_of_fibre` upgrades this to `𝔭 Λ_𝔮 = 𝔮 Λ_𝔮` and flatness
over the localization of `k[y_1, …, y_m]`, `comap_eq_sup_span` supplies the ideal identity
`𝔭 = 𝔭' k[y] + (y_{t+1}, …, y_m)` that those steps consume, and the Jacobi–Zariski surjection
`Ω[κ(𝔭)⁄k] ⊗ F → Ω[F⁄k] → Ω[F⁄κ(𝔭)] → 0` kills `Ω[F⁄κ(𝔭)]` because the chosen basis of `Ω[F⁄k]`
consists of differentials of elements of `κ(𝔭)`; a finitely generated extension with vanishing
differentials is finite separable by
`finite_and_isSeparable_of_subsingleton_kaehlerDifferential` (Lemma [stacks, 07E1]).

The hypotheses added to clause (1) proper (`exists_mvPolynomial_flat_localization`, which is the
case `F = k`) are three, and all three are needed:

* `CharP k p` for a prime `p`, because Lemma [stacks, 07E6] is stated in positive characteristic.
  Clause (1) at `F = k` avoids 07E6 altogether and is therefore characteristic-free.
* `Algebra.EssFiniteType k F`, that is, `F/k` finitely generated: without it `Ω[F⁄k]` need not be
  finite dimensional and there is no finite family of variables to choose.
* `hS`, that `F` is generated over `k` by residues of elements of `Λ`. This cannot be dropped:
  the variables are sent into `Λ`, so `κ(𝔭)` is generated by residues of elements of `Λ` whatever
  `φ` is, and a conclusion `κ(𝔭) ⊆ F` with `F/κ(𝔭)` finite forces `F` to be a finite extension of
  such a field. For `Λ = k[x, y]`, `𝔮 = 0` and `F = k(x/y)` there is no such `φ`: an element of
  `k(x/y)` which is also a polynomial is invariant under `(x, y) ↦ (tx, ty)`, hence constant, so
  `F ∩ k[x, y] = k`, every `φ` has `κ(𝔭) ⊆ F` only if `κ(𝔭) = k`, and `k(x/y)/k` is not finite.
  The hypothesis costs nothing where the statement is used, because `κ(𝔮)` is the fraction field
  of `Λ/𝔮`, so the subfields generated by residues of `Λ` are cofinal among the finitely
  generated subfields of `κ(𝔮)` (`exists_finset_mem_adjoin_image` with
  `exists_mul_residue_eq_residue_localization`).
* `muGlobal`, `hmuqGlobal`, `hmuspan`, a finite family of elements of `𝔮` whose images generate
  the maximal ideal of `Λ_𝔮`. The *second* block of variables is sent to a subfamily of it,
  extracted by Nakayama in the fibre `Λ_𝔮/𝔭'Λ_𝔮` (`exists_subfamily_span_eq_maximalIdeal`), so
  that the images of ALL the variables are controlled: each lies in `S` or in the range of
  `muGlobal`, which is the last conclusion. This costs nothing —
  `exists_fin_span_eq_maximalIdeal_localization` produces such a family for any Noetherian `Λ` —
  and it is the second of Nugent's refinements: keeping the regular parameters of the fibre among
  prescribed GLOBAL elements of `𝔮` is what lets the whole of `φ` be read inside an
  approximating subalgebra of `Λ_𝔮/𝔮^nΛ_𝔮`, which clauses (2) and (3) need and which the
  source's text does not supply.

No `@[stacks]` attribute is attached: the statement is a strengthening of clause (1) under extra
hypotheses, not the clause itself. -/
theorem exists_mvPolynomial_flat_localization_of_intermediateField
    {k Λ : Type u} [Field k] [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ]
    [Algebra.IsGeometricallyRegular k Λ] (p : ℕ) [Fact p.Prime] [CharP k p]
    (𝔮 : Ideal Λ) [𝔮.IsPrime]
    (F : IntermediateField k (ResidueField (Localization.AtPrime 𝔮)))
    [Algebra.EssFiniteType k F] (S : Finset Λ)
    (hS : IntermediateField.adjoin k ((fun a => residue (Localization.AtPrime 𝔮)
        (algebraMap Λ (Localization.AtPrime 𝔮) a)) '' (S : Set Λ)) = F)
    {r₀ : ℕ} (muGlobal : Fin r₀ → Λ) (hmuqGlobal : ∀ j, muGlobal j ∈ 𝔮)
    (hmuspan : Ideal.span (Set.range fun j =>
        algebraMap Λ (Localization.AtPrime 𝔮) (muGlobal j))
      = maximalIdeal (Localization.AtPrime 𝔮)) :
    ∃ (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
      (g : Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮) →+* Localization.AtPrime 𝔮)
      (ι : ResidueField (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) →+* F),
      Ideal.map ((algebraMap Λ (Localization.AtPrime 𝔮)).comp φ.toRingHom)
          (Ideal.comap φ.toRingHom 𝔮)
        = Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) 𝔮 ∧
      (∀ f, g (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) f)
          = algebraMap Λ (Localization.AtPrime 𝔮) (φ f)) ∧
      g.Flat ∧
      (∀ i, (∃ w ∈ S, φ (MvPolynomial.X i) = w) ∨ ∃ j, φ (MvPolynomial.X i) = muGlobal j) ∧
      (∀ y, (ι (residue (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) y) :
            ResidueField (Localization.AtPrime 𝔮))
          = residue (Localization.AtPrime 𝔮) (g y)) ∧
      (letI : Algebra (ResidueField (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮))) F :=
          ι.toAlgebra;
        Module.Finite (ResidueField (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮))) F ∧
          Algebra.IsSeparable
            (ResidueField (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮))) F) := by
  classical
  -- the first block of variables: a basis of `Ω[F⁄k]` among differentials of residues of `Λ`
  obtain ⟨t, lam, yF, bas, hlamS, hyF, hbas⟩ := exists_basis_kaehlerDifferential_of_adjoin
    ((residue (Localization.AtPrime 𝔮)).comp (algebraMap Λ (Localization.AtPrime 𝔮))) F S hS
  obtain ⟨m, φ, g, hmap, hg, hflat, hT, hres, -, -, hgk, a, ha⟩ :=
    exists_mvPolynomial_flat_localization_of_basis p 𝔮 F
      (fun w => (∃ w' ∈ S, w = w') ∨ ∃ j, w = muGlobal j) lam
      (fun j => Or.inl ⟨lam j, hlamS j, rfl⟩) yF bas hbas hyF fun J _ => by
    -- the second block of variables: a subfamily of the GLOBAL family `muGlobal` whose images
    -- generate the maximal ideal of the fibre, extracted by Nakayama
    have hfibspan : Ideal.span (Set.range fun j => Ideal.Quotient.mk J
          (algebraMap Λ (Localization.AtPrime 𝔮) (muGlobal j)))
        = maximalIdeal (Localization.AtPrime 𝔮 ⧸ J) := by
      rw [maximalIdeal_quotient_of_eq_pow, ← hmuspan, Ideal.map_span, ← Set.range_comp]
      rfl
    obtain ⟨r, idx, hspansub, hcardmu⟩ := exists_subfamily_span_eq_maximalIdeal _ hfibspan
    exact ⟨r, fun i => muGlobal (idx i),
      fun j => ⟨hmuqGlobal _, Or.inr ⟨idx j, rfl⟩⟩,
      maximalIdeal_quotient_of_eq_pow.symm.trans hspansub.symm, hcardmu⟩
  set 𝔭 : Ideal (MvPolynomial (Fin m) k) := Ideal.comap φ.toRingHom 𝔮 with h𝔭def
  -- the `k`-algebra map `k[y_1, …, y_m] → F` through which the residues factor
  obtain ⟨χ, hχres⟩ : ∃ χ : MvPolynomial (Fin m) k →ₐ[k] F, ∀ f,
      (χ f : ResidueField (Localization.AtPrime 𝔮))
        = residue (Localization.AtPrime 𝔮) (algebraMap Λ (Localization.AtPrime 𝔮) (φ f)) := by
    refine ⟨MvPolynomial.aeval fun i => ⟨_, hres i⟩, fun f => ?_⟩
    have hcomp : F.val.comp (MvPolynomial.aeval fun i => ⟨_, hres i⟩)
        = (IsScalarTower.toAlgHom k (Localization.AtPrime 𝔮)
              (ResidueField (Localization.AtPrime 𝔮))).comp
            ((IsScalarTower.toAlgHom k Λ (Localization.AtPrime 𝔮)).comp φ) :=
      MvPolynomial.algHom_ext fun i => by simp
    exact DFunLike.congr_fun hcomp f
  have hcoe0 : ∀ x : F, ((x : ResidueField (Localization.AtPrime 𝔮)) = 0) ↔ x = 0 := by
    intro x
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  have hkerχ : ∀ f, χ f = 0 ↔ f ∈ 𝔭 := by
    intro f
    rw [← hcoe0, hχres f, residue_eq_zero_iff, h𝔭def, Ideal.mem_comap]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔮) 𝔮 (φ f)
  have hunitχ : ∀ s : 𝔭.primeCompl, IsUnit (χ.toRingHom (s : MvPolynomial (Fin m) k)) :=
    fun s => isUnit_iff_ne_zero.mpr fun h0 =>
      Ideal.mem_primeCompl_iff.mp s.2 ((hkerχ _).mp h0)
  set ι₀ : Localization.AtPrime 𝔭 →+* F := IsLocalization.lift hunitχ with hι₀def
  have hι₀ : ∀ f, ι₀ (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) f)
      = χ f := fun f => IsLocalization.lift_eq hunitχ f
  have hlocι₀ : IsLocalHom ι₀ := by
    constructor
    intro b hb
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq 𝔭.primeCompl b
    refine (IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime 𝔭) 𝔭 x s).mpr ?_
    intro hx
    have hz : ι₀ (IsLocalization.mk' (Localization.AtPrime 𝔭) x s) = 0 := by
      have hx0 : χ.toRingHom x = 0 := (hkerχ x).mpr hx
      rw [hι₀def, IsLocalization.lift_mk', hx0, zero_mul]
    exact (isUnit_iff_ne_zero.mp hb) hz
  set ι : ResidueField (Localization.AtPrime 𝔭) →+* F := ResidueField.lift ι₀ with hιdef
  have hιcomp : (F.val.toRingHom).comp ι₀ = (residue (Localization.AtPrime 𝔮)).comp g := by
    refine IsLocalization.ringHom_ext 𝔭.primeCompl (RingHom.ext fun f => ?_)
    change ((ι₀ (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) f) : F) :
        ResidueField (Localization.AtPrime 𝔮))
      = residue (Localization.AtPrime 𝔮)
          (g (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) f))
    rw [hι₀ f, hg f]
    exact hχres f
  have hι : ∀ y : Localization.AtPrime 𝔭,
      ((ι (residue (Localization.AtPrime 𝔭) y) : F) : ResidueField (Localization.AtPrime 𝔮))
      = residue (Localization.AtPrime 𝔮) (g y) := by
    intro y
    have h := DFunLike.congr_fun hιcomp y
    rw [hιdef]
    exact h
  refine ⟨m, φ, g, ι, hmap, hg, hflat, hT, hι, ?_⟩
  -- `F/κ(𝔭)` is finite separable
  let instκF : Algebra (ResidueField (Localization.AtPrime 𝔭)) F := ι.toAlgebra
  have hκF : (algebraMap (ResidueField (Localization.AtPrime 𝔭)) F) = ι :=
    RingHom.algebraMap_toAlgebra _
  have htowkκ : IsScalarTower k (ResidueField (Localization.AtPrime 𝔭)) F := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [hκF]
    refine Subtype.ext ?_
    change (algebraMap k (ResidueField (Localization.AtPrime 𝔮)) a) = _
    rw [show (algebraMap k (ResidueField (Localization.AtPrime 𝔭)) a)
        = residue (Localization.AtPrime 𝔭) (algebraMap k (Localization.AtPrime 𝔭) a) from rfl,
      hι (algebraMap k (Localization.AtPrime 𝔭) a), hgk a]
    rfl
  have hEFTκ : Algebra.EssFiniteType (ResidueField (Localization.AtPrime 𝔭)) F :=
    Algebra.EssFiniteType.of_comp k (ResidueField (Localization.AtPrime 𝔭)) F
  have hcι : ∀ j, algebraMap (ResidueField (Localization.AtPrime 𝔭)) F
      (residue (Localization.AtPrime 𝔭) (a j)) = yF j := by
    intro j
    rw [hκF]
    refine Subtype.ext ?_
    rw [hι, ha, hyF]
    rfl
  have hsubΩ : Subsingleton (Ω[F⁄ResidueField (Localization.AtPrime 𝔭)]) := by
    refine subsingleton_kaehlerDifferential_of_span (k := k)
      (fun j => residue (Localization.AtPrime 𝔭) (a j)) ?_
    have hfun : (fun j => KaehlerDifferential.D k F
          (algebraMap (ResidueField (Localization.AtPrime 𝔭)) F
            (residue (Localization.AtPrime 𝔭) (a j))))
        = fun j => KaehlerDifferential.D k F (yF j) :=
      funext fun j => by rw [hcι j]
    rw [hfun, show (fun j => KaehlerDifferential.D k F (yF j)) = bas from
      (funext fun j => (hbas j).symm)]
    exact bas.span_eq
  exact finite_and_isSeparable_of_subsingleton_kaehlerDifferential
    (ResidueField (Localization.AtPrime 𝔭)) F hsubΩ


/-! ### Stacks 07FH, clauses (2) and (3) for a finitely generated residue field -/

/-- Every element of the residue field of `Λ_𝔮` is a quotient of two residues of elements of
`Λ`: that residue field is the fraction field of `Λ/𝔮`. -/
private lemma exists_mul_residue_eq_residue_localization {Λ : Type*} [CommRing Λ]
    (𝔮 : Ideal Λ) [𝔮.IsPrime] (c : ResidueField (Localization.AtPrime 𝔮)) :
    ∃ a b : Λ,
      residue (Localization.AtPrime 𝔮) (algebraMap Λ (Localization.AtPrime 𝔮) b) ≠ 0 ∧
      c * residue (Localization.AtPrime 𝔮) (algebraMap Λ (Localization.AtPrime 𝔮) b)
        = residue (Localization.AtPrime 𝔮) (algebraMap Λ (Localization.AtPrime 𝔮) a) := by
  obtain ⟨w, hw⟩ := residue_surjective c
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl w
  refine ⟨a, (s : Λ), ?_, ?_⟩
  · have h1 : IsUnit (algebraMap Λ (Localization.AtPrime 𝔮) (s : Λ)) :=
      IsLocalization.map_units (Localization.AtPrime 𝔮) s
    intro h0
    exact (mem_maximalIdeal _).mp ((residue_eq_zero_iff _).mp h0) h1
  · have hspec := IsLocalization.mk'_spec (Localization.AtPrime 𝔮) a s
    rw [show IsLocalization.mk' (Localization.AtPrime 𝔮) a s = w from hs] at hspec
    have h := congrArg (residue (Localization.AtPrime 𝔮)) hspec
    simp only [map_mul, hw] at h
    exact h

/-- If the differentials of elements `c j` of a field `K` form a basis of `Ω[⊤⁄k]` for the
intermediate field `⊤` of `K/k`, then those differentials span `Ω[K⁄k]` over `K`. -/
private theorem span_derivation_eq_top_of_basis_top {k K : Type*} [Field k] [Field K]
    [Algebra k K] {t : ℕ} (c : Fin t → K)
    (b : Module.Basis (Fin t) (⊤ : IntermediateField k K) (Ω[(⊤ : IntermediateField k K)⁄k]))
    (hb : ∀ j, b j = KaehlerDifferential.D k (⊤ : IntermediateField k K)
      ⟨c j, IntermediateField.mem_top⟩) :
    Submodule.span K (Set.range fun j => KaehlerDifferential.D k K (c j)) = ⊤ := by
  classical
  refine top_unique ?_
  rw [← KaehlerDifferential.span_range_derivation (R := k) (S := K)]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, rfl⟩
  set X : (⊤ : IntermediateField k K) := ⟨x, IntermediateField.mem_top⟩ with hX
  have h1 := b.sum_repr (KaehlerDifferential.D k (⊤ : IntermediateField k K) X)
  have h2 := congrArg (KaehlerDifferential.map k k (⊤ : IntermediateField k K) K) h1
  rw [map_sum] at h2
  have h3 : ∀ i, (KaehlerDifferential.map k k (⊤ : IntermediateField k K) K)
      (b.repr (KaehlerDifferential.D k (⊤ : IntermediateField k K) X) i • b i)
      = ((b.repr (KaehlerDifferential.D k (⊤ : IntermediateField k K) X) i : K))
        • KaehlerDifferential.D k K (c i) := by
    intro i
    rw [LinearMap.map_smul, hb i, KaehlerDifferential.map_D]
    rfl
  simp only [h3] at h2
  rw [KaehlerDifferential.map_D] at h2
  have h4 : (algebraMap (⊤ : IntermediateField k K) K) X = x := rfl
  rw [h4] at h2
  rw [← h2]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **The construction behind clauses (2) and (3) of Stacks 07FH**, under the extra hypothesis
that `κ(𝔮)` is a finitely generated field extension of `k`. There are `m ≥ 0` and a `k`-algebra
map `φ : k[y_1, …, y_m] → Λ` such that, with `𝔭 = φ^{-1}(𝔮)`, one has `𝔭 Λ_𝔮 = 𝔮 Λ_𝔮` and the
induced map `k[y_1, …, y_m]_𝔭/𝔭^n → Λ_𝔮/𝔮^nΛ_𝔮` is essentially smooth.

The variables split as `y_1, …, y_t, y_{t+1}, …, y_m`: the first `t` are sent to elements of `Λ`
whose residues have differentials forming a basis of `Ω[κ(𝔮)⁄k]`, which is finite dimensional
because `κ(𝔮)/k` is finitely generated, and the remaining ones are sent to elements of `𝔮`
lifting a minimal system of generators of the maximal ideal of the fibre
`Λ_𝔮/𝔭'Λ_𝔮`. Lemma [stacks, 07E6] gives flatness over the localization of `k[y_1, …, y_t]` and
regularity of that fibre, `map_eq_and_flat_of_fibre` upgrades this to `𝔭 Λ_𝔮 = 𝔮 Λ_𝔮` and
flatness over the localization of `k[y_1, …, y_m]`, and
`isEssentiallySmooth_quotient_of_flat` passes to the `n`-th prime-power quotients: the residue
field extension `κ(𝔮)/κ(𝔭)` is finitely generated with vanishing differentials, hence finite
separable. -/
theorem exists_mvPolynomial_isEssentiallySmooth_primePowerQuotient
    {k Λ : Type u} [Field k] [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ]
    [Algebra.IsGeometricallyRegular k Λ] (𝔮 : Ideal Λ) [𝔮.IsPrime] (p : ℕ) [Fact p.Prime]
    [CharP k p] [Algebra.EssFiniteType k (ResidueField (Localization.AtPrime 𝔮))]
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
      (g : Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮) →+* Localization.AtPrime 𝔮)
      (u : primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n →+* primePowerQuotient 𝔮 n),
      Ideal.map ((algebraMap Λ (Localization.AtPrime 𝔮)).comp φ.toRingHom)
          (Ideal.comap φ.toRingHom 𝔮)
        = Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) 𝔮 ∧
      (∀ f, g (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) f)
          = algebraMap Λ (Localization.AtPrime 𝔮) (φ f)) ∧
      g.Flat ∧
      (∀ y, u (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) k)
              (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)))
              (Ideal.comap φ.toRingHom 𝔮 ^ n)) y)
          = Ideal.Quotient.mk (Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) (𝔮 ^ n))
            (g y)) ∧
      u.IsEssentiallySmooth := by
  classical
  -- the first block of variables: a basis of `Ω[κ(𝔮)⁄k]` among residues of `Λ`
  obtain ⟨t, lam, bas, hbas⟩ := exists_basis_kaehlerDifferential_top (k := k)
    ((residue (Localization.AtPrime 𝔮)).comp (algebraMap Λ (Localization.AtPrime 𝔮)))
    (fun c => by simpa using exists_mul_residue_eq_residue_localization 𝔮 c)
  have hEFTtop : Algebra.EssFiniteType k
      (⊤ : IntermediateField k (ResidueField (Localization.AtPrime 𝔮))) :=
    IntermediateField.essFiniteType_iff.mpr
      (IntermediateField.fg_top k (ResidueField (Localization.AtPrime 𝔮)))
  obtain ⟨m, φ, g, hmap, hg, hflat, -, -, hloc, hmax, hgk, a, ha⟩ :=
    exists_mvPolynomial_flat_localization_of_basis p 𝔮
      (⊤ : IntermediateField k (ResidueField (Localization.AtPrime 𝔮))) (fun _ => True) lam
      (fun _ => trivial)
      (fun j => ⟨residue (Localization.AtPrime 𝔮)
        (algebraMap Λ (Localization.AtPrime 𝔮) (lam j)), IntermediateField.mem_top⟩)
      bas hbas (fun _ => rfl) fun J _ => by
    -- the second block of variables: generators of the maximal ideal of the fibre, lifted to `𝔮`
    obtain ⟨r, mu, hmuq, hspanmu, hcardmu⟩ := exists_fin_span_eq_maximalIdeal_quotient 𝔮 J
    exact ⟨r, mu, fun j => ⟨hmuq j, trivial⟩, hspanmu, hcardmu⟩
  let : Algebra (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) (Localization.AtPrime 𝔮) :=
    g.toAlgebra
  have : IsScalarTower k (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮))
      (Localization.AtPrime 𝔮) := IsScalarTower.of_algebraMap_eq fun a => (hgk a).symm
  have : Module.Flat (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) (Localization.AtPrime 𝔮) :=
    RingHom.flat_algebraMap_iff.mp hflat
  have : IsLocalHom (algebraMap (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮))
    (Localization.AtPrime 𝔮)) := hloc
  -- the spanning family of `Ω[κ(𝔮)⁄k]` coming from `κ(𝔭)`
  have hspan : Submodule.span (ResidueField (Localization.AtPrime 𝔮))
      (Set.range fun j => KaehlerDifferential.D k (ResidueField (Localization.AtPrime 𝔮))
        (ResidueField.map (algebraMap (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮))
          (Localization.AtPrime 𝔮))
          (residue (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) (a j)))) = ⊤ := by
    have hfun : (fun j => KaehlerDifferential.D k (ResidueField (Localization.AtPrime 𝔮))
          (ResidueField.map (algebraMap (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮))
            (Localization.AtPrime 𝔮))
            (residue (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) (a j))))
        = fun j => KaehlerDifferential.D k (ResidueField (Localization.AtPrime 𝔮))
          (residue (Localization.AtPrime 𝔮)
            (algebraMap Λ (Localization.AtPrime 𝔮) (lam j))) :=
      funext fun j => by rw [ResidueField.map_residue]; congr 2; exact ha j
    rw [hfun]
    exact span_derivation_eq_top_of_basis_top _ bas hbas
  -- the closing step
  obtain ⟨u, hu, hess⟩ := isEssentiallySmooth_quotient_of_flat (k := k) hmax
    (fun j => residue (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) (a j)) hspan hn
    (map_pow_eq_maximalIdeal_pow (Ideal.comap φ.toRingHom 𝔮) n)
    (map_pow_eq_maximalIdeal_pow 𝔮 n)
  exact ⟨m, φ, g, u, hmap, hg, hflat, hu, hess⟩

end Stacks.Smoothing
