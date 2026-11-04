module

public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.GlobalFunctionsModel
public import StacksFrontier.AlgebraicGeometry.Perfect.CohomologyAndBaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctionsFrom02O8
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
public import StacksFrontier.RingTheory.Flat.FiniteFreeResidueExtension
public import StacksFrontier.RingTheory.Etale.SplitAfterFiniteExtension
public import StacksFrontier.Algebra.Homology.StupidTruncationSplit
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PerfectGlobalSectionsAffineBase
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.OpenImmersion

/-!
# Global functions of a proper smooth family over a Noetherian affine base

Let `A` be a Noetherian ring, `f : X ⟶ Spec A` a proper smooth morphism and `p` a prime of `A`.
This file proves that over a principal open `D(h) ∋ p` the derived global sections of `𝒪_X`
split off their degree-zero cohomology, and that the global functions form a finite étale
algebra, in a form stable under every base change: for every ring map `φ : A ⟶ B` with `φ h` a
unit and every base change `X'` of `X` to `B`,

* `Γ(X', 𝒪_{X'})` is a finite étale `B`-algebra, and
* `RΓ(X', 𝒪_{X'}) ≅ B^r[0] ⊕ K` in `D(B)` with `K` a bounded complex of finite free `B`-modules
  concentrated in degrees `≥ 1`.

This is the affine Noetherian case of [Stacks, Tag 0G7Y] for a smooth family, which is the
content of the first two assertions of [Stacks, Tag 0G8H].

## Main results

* `exists_notMem_matrix_map_eq_zero`: the first differential of the minimal model of `RΓ` vanishes
  near `p`.
* `exists_away_globalFunctions_finiteEtale_and_split`: the two conclusions above.

## Implementation notes

The minimal model `P` of [Stacks, Tag 0BYP] of the base change to `A_g` of the Čech complex has
first differential a matrix `M` vanishing modulo `p` (minimality). The heart of the argument is
that `M` vanishes near `p`; that is the surjectivity of
`(f_*𝒪_X)_p ⟶ H⁰(X_p, 𝒪_{X_p})` used by the source's proof of [Stacks, Tag 0G7Y], and it is
established as in the source, except that the residue field is enlarged only to a *finite*
extension, so that the base stays Noetherian and [Stacks, Tag 0G7X] is available over it:

1. `H⁰(X_p, 𝒪)` is a finite étale `κ(p)`-algebra ([Stacks, Tag 0BUG]), split by a finite
   extension `L` of `κ(p)`
   (`Algebra.Etale.exists_finiteDimensional_span_setOf_isIdempotentElem_eq_top`).
2. `L` is the residue field of a finite free `A`-algebra `S` at `q = pS` ([Stacks, Tag 07NE]);
   `B = S_q` is Noetherian, local and faithfully flat over `A_p`.
3. Over the closed point `y` of `Spec B`, the global functions of the fibre are `κ(y) ⊗ H⁰(X_p, 𝒪)`
   (the kernel model, `M` vanishing over fields), hence spanned by idempotents; each idempotent
   extends to `X_B` by [Stacks, Tag 0G7X]; so `Γ(X_B, 𝒪) ⟶ Γ(X_y, 𝒪)` is surjective.
4. In the coordinates of the kernel model this is the statement that every vector over `κ(y)`
   lifts to the kernel of `M ⊗ B`, so `M ⊗ B = 0` by Nakayama, and then `M` dies near `p` because
   `S` is free over `A`.

## References

* [Stacks Project, Tag 0G7Y](https://stacks.math.columbia.edu/tag/0G7Y)
* [Stacks Project, Tag 0G7X](https://stacks.math.columbia.edu/tag/0G7X)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 07NE](https://stacks.math.columbia.edu/tag/07NE)
* [Stacks Project, Tag 0BYP](https://stacks.math.columbia.edu/tag/0BYP)
-/

@[expose] public noncomputable section

open scoped Stacks.StandardDerivedModel

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

/-- **Clearing denominators through a finite free extension.** If a matrix `M` over `A_g` vanishes
over `S_q` for a free `A`-algebra `S` and a prime `q ⊇ pS`, then it vanishes after inverting some
`t ∉ p`. -/
theorem exists_notMem_matrix_map_eq_zero_of_map_atPrime {A : Type u} {S : Type*} [CommRing A]
    [CommRing S] [Algebra A S] [Module.Free A S] (p : Ideal A) [p.IsPrime] {g : A} {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) (Localization.Away g)) (q : Ideal S) [q.IsPrime]
    (hq : p.map (algebraMap A S) ≤ q) (ψ : Localization.Away g →+* Localization.AtPrime q)
    (hψ : ψ.comp (algebraMap A _) = (algebraMap S _).comp (algebraMap A S))
    (hM : M.map ψ = 0) :
    ∃ t : A, t ∉ p ∧ ∀ {B : Type u} [CommRing B] (φ : A →+* B) (hgφ : IsUnit (φ g)),
      IsUnit (φ t) → M.map (IsLocalization.Away.lift g hgφ) = 0 := by
  classical
  have hentry : ∀ ij : Fin m × Fin n, ∃ (a : A) (k : ℕ) (s : A), s ∉ p ∧ s * a = 0 ∧
      M ij.1 ij.2 * algebraMap A (Localization.Away g) (g ^ k) = algebraMap A _ a := by
    rintro ⟨i, j⟩
    obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers g) (M i j)
    have h0 : ((algebraMap S (Localization.AtPrime q)).comp (algebraMap A S)) a = 0 := by
      rw [← hψ, RingHom.comp_apply, ← ha, map_mul]
      have := congrFun (congrFun hM i) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at this
      rw [this, zero_mul]
    obtain ⟨⟨σ, hσ⟩, hσa⟩ :=
      (IsLocalization.map_eq_zero_iff q.primeCompl _ (algebraMap A S a)).1 h0
    obtain ⟨s, hs, hsa⟩ := exists_notMem_mul_eq_zero_of_free p a σ (fun h => hσ (hq h)) hσa
    exact ⟨a, k, s, hs, hsa, ha⟩
  choose a k s hs hsa ha using hentry
  refine ⟨∏ ij, s ij, fun h => ?_, fun {B} _ φ hgφ htφ => ?_⟩
  · obtain ⟨ij, -, hij⟩ := (Ideal.IsPrime.prod_mem_iff (hp := inferInstance)).1 h
    exact hs ij hij
  · ext i j
    simp only [Matrix.map_apply, Matrix.zero_apply]
    have hφa : φ (a (i, j)) = 0 := by
      have hmul : φ (∏ ij, s ij) * φ (a (i, j)) = 0 := by
        rw [← map_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), mul_assoc,
          hsa (i, j), mul_zero, map_zero]
      exact (htφ.mul_right_eq_zero).1 hmul
    have h1 := congrArg (IsLocalization.Away.lift g hgφ) (ha (i, j))
    rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq, hφa, map_pow] at h1
    exact ((hgφ.pow (k (i, j))).mul_left_eq_zero).1 h1

/-- **Restriction to a fibre is onto when the fibre's functions are spanned by idempotents.** For
`f : Y ⟶ Spec B` proper over a locally Noetherian base and a point `y` whose only open
neighbourhood is `Spec B`, every idempotent of `Γ(Y_y, 𝒪)` extends to `Y` ([Stacks, Tag 0G7X]); so
if they span `Γ(Y_y, 𝒪)` over a quotient `B'` of `B`, then `Γ(Y, 𝒪) ⟶ Γ(Y_y, 𝒪)` is surjective. -/
theorem surjective_appTop_fiberι_of_span_isIdempotentElem {B B' : Type u} [CommRing B]
    [CommRing B'] (ψ : B →+* B') (hψ : Function.Surjective ψ) {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of B)) [IsProper f] [IsLocallyNoetherian (Spec (.of B))] (y : Spec (.of B))
    (hy : ∀ V : (Spec (.of B)).Opens, y ∈ V → V = ⊤) (fy : f.fiber y ⟶ Spec (.of B'))
    (w : f.fiberι y ≫ f = fy ≫ Spec.map (CommRingCat.ofHom ψ))
    (hspan : letI : Algebra B' Γ(f.fiber y, ⊤) :=
        ((Stacks.Cech.globalRingHom fy).hom : B' →+* Γ(f.fiber y, ⊤)).toAlgebra
      Submodule.span B' {x : Γ(f.fiber y, ⊤) | IsIdempotentElem x} = ⊤) :
    Function.Surjective (f.fiberι y).appTop := by
  let : Algebra B' Γ(f.fiber y, ⊤) :=
    ((Stacks.Cech.globalRingHom fy).hom : B' →+* Γ(f.fiber y, ⊤)).toAlgebra
  have hidem : ∀ e : Γ(f.fiber y, ⊤), IsIdempotentElem e → e ∈ Set.range (f.fiberι y).appTop := by
    intro e he
    obtain ⟨V, hyV, a, ha⟩ :=
      Stacks.FormalFunctions.extendsOverNeighbourhood_of_isLocallyNoetherian f y e he
    have hV : V = ⊤ := hy V hyV
    subst hV
    refine ⟨a, ?_⟩
    rw [← ha]
    show (f.fiberι y).app ⊤ a =
      (f.fiberι y).appLE (f ⁻¹ᵁ ⊤) (f.fiberι y ⁻¹ᵁ (f ⁻¹ᵁ ⊤)) le_rfl a
    rw [Scheme.Hom.appLE_eq_app]
    rfl
  let N : Submodule B' Γ(f.fiber y, ⊤) :=
    { carrier := Set.range (f.fiberι y).appTop
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨a', rfl⟩
        exact ⟨a + a', map_add _ _ _⟩
      zero_mem' := ⟨0, map_zero _⟩
      smul_mem' := by
        rintro c _ ⟨a, rfl⟩
        obtain ⟨c', rfl⟩ := hψ c
        refine ⟨Stacks.Cech.globalRingHom f c' * a, ?_⟩
        rw [map_mul, ← globalRingHom_naturality ψ f fy (f.fiberι y) w c', Algebra.smul_def]
        rfl }
  have hspan' : Submodule.span B' {x : Γ(f.fiber y, ⊤) | IsIdempotentElem x} = ⊤ := hspan
  have hN : N = ⊤ := eq_top_iff.2 (hspan' ▸ Submodule.span_le.2 fun e he => hidem e he)
  exact fun x => show x ∈ N from hN ▸ Submodule.mem_top

/-- Global functions of a base change to a field of a proper smooth morphism form a finite étale
algebra ([Stacks, Tag 0BUG]). -/
private theorem etale_and_finite_globalSections_of_isPullback {A K : Type u} [CommRing A] [Field K]
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of A)} [IsProper f] [Smooth f] {fK : Y ⟶ Spec (.of K)}
    {gK : Y ⟶ X} {φ : A →+* K} (hsq : IsPullback gK fK f (Spec.map (CommRingCat.ofHom φ))) :
    letI : Algebra K Γ(Y, ⊤) := ((Stacks.Cech.globalRingHom fK).hom : K →+* Γ(Y, ⊤)).toAlgebra
    Algebra.Etale K Γ(Y, ⊤) ∧ Module.Finite K Γ(Y, ⊤) := by
  have : IsProper fK := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  have : Smooth fK := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  have : GeometricallyReduced fK := geometricallyReduced_of_smooth fK
  exact Stacks.AlgebraicGeometry.ProperSectionsGeom.etale_globalSections_of_geometricallyReduced
    K fK

section KillMatrix

open scoped Matrix

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of A)} [IsProper f] [Smooth f] (p : Ideal A) [p.IsPrime] {g : A}
  {I : Type u} [Fintype I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i))
  (hflat : IsFlatOver f.toLRSHom.toShHom (Scheme.unitModule X))
  {P : CochainComplex (ModuleCat.{u} (Localization.Away g)) ℤ}
  (u : P ⟶ extendScalarsComplex (algebraMap A (Localization.Away g))
    (baseAlternatingCechComplex f U hU (Scheme.unitModule X)))
  [QuasiIso u] [∀ n : ℤ, Module.Flat (Localization.Away g) (P.X n)] (b : ℤ) [P.IsStrictlyLE b]
  (hP : IsZero (P.X (-1)))
  {r β : ℕ} (e₀ : P.X 0 ≅ ModuleCat.of (Localization.Away g) (Fin r → Localization.Away g))
  (e₁ : P.X 1 ≅ ModuleCat.of (Localization.Away g) (Fin β → Localization.Away g))
  (M : Matrix (Fin β) (Fin r) (Localization.Away g))
  (hM : P.d 0 1 = e₀.hom ≫ ModuleCat.ofHom M.mulVecLin ≫ e₁.inv)

omit [IsNoetherianRing A] [Smooth f] in
include hU hUaff hflat u b hP e₀ e₁ hM in
/-- **Nakayama for the kernel model.** Let `ψ : A_g ⟶ B` with `B` local, `π : B ⟶ K` a map to a
field with kernel in the maximal ideal and `M ⊗ K = 0`. If pulling global functions back from a
base change `X'` of `X` to `B` to its base change to `K` is surjective, then `M ⊗ B = 0`. -/
theorem matrix_map_eq_zero_of_surjective_appTop {B K : Type u} [CommRing B] [IsLocalRing B]
    [Field K] (ψ : Localization.Away g →+* B) (π : B →+* K)
    (hπ : ∀ c, π c = 0 → c ∈ IsLocalRing.maximalIdeal B) (hMπ : M.map (π.comp ψ) = 0)
    {X' X'' : Scheme.{u}} {f' : X' ⟶ Spec (.of B)} {f'' : X'' ⟶ Spec (.of K)} {g' : X' ⟶ X}
    {g'' : X'' ⟶ X'}
    (hsq : IsPullback g' f' f
      (Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap A (Localization.Away g))))))
    (hsq' : IsPullback g'' f'' f' (Spec.map (CommRingCat.ofHom π)))
    (hsq'' : IsPullback (g'' ≫ g') f'' f
      (Spec.map (CommRingCat.ofHom ((π.comp ψ).comp (algebraMap A (Localization.Away g))))))
    (hsurj : Function.Surjective g''.appTop) : M.map ψ = 0 := by
  have hker : ∀ w : Fin r → K, w ∈ LinearMap.ker (M.map (π.comp ψ)).mulVecLin := fun w => by
    rw [ker_mulVecLin_map_eq_top M _ hMπ]
    trivial
  refine Matrix.eq_zero_of_forall_exists_mem_ker_map π hπ (M.map ψ) fun w => ?_
  let θ := kernelFunctionsEquiv (algebraMap A (Localization.Away g)) U hU hUaff hflat u b hP
    e₀ e₁ M hM ψ hsq
  let θ' := kernelFunctionsEquiv (algebraMap A (Localization.Away g)) U hU hUaff hflat u b hP
    e₀ e₁ M hM (π.comp ψ) hsq''
  obtain ⟨a, ha⟩ := hsurj (θ' ⟨w, hker w⟩)
  refine ⟨θ.symm a, (θ.symm a).2, ?_⟩
  have hnat := appTop_kernelFunctionsEquiv (algebraMap A (Localization.Away g)) U hU hUaff
    hflat u b hP e₀ e₁ M hM ψ π hsq hsq' hsq'' (θ.symm a) (hker _)
  have h2 : g''.appTop (θ (θ.symm a)) = g''.appTop a := by rw [θ.apply_symm_apply]
  have h3 : θ' ⟨π ∘ ((θ.symm a : LinearMap.ker (M.map ψ).mulVecLin) : Fin r → B),
      hker _⟩ = θ' ⟨w, hker w⟩ := by
    rw [← hnat, h2, ha]
  exact congrArg Subtype.val (θ'.injective h3)

omit [Smooth f] in
include hU hUaff hflat u b hP e₀ e₁ hM in
/-- **Minimality of the model.** If `r` is the dimension of the degree-zero cohomology of the
Čech complex base changed to `κ(p)`, then the matrix `M` of the first differential of the model
vanishes over `κ(p)`. -/
theorem matrix_map_residueField_eq_zero
    (hr : Module.finrank p.ResidueField ((extendScalarsComplex (algebraMap A p.ResidueField)
      (baseAlternatingCechComplex f U hU (Scheme.unitModule X))).homology 0) = r)
    (hgκ : IsUnit (algebraMap A p.ResidueField g)) :
    M.map (IsLocalization.Away.lift g hgκ) = 0 := by
  let α := algebraMap A (Localization.Away g)
  let C := baseAlternatingCechComplex f U hU (Scheme.unitModule X)
  let χ : Localization.Away g →+* p.ResidueField := IsLocalization.Away.lift g hgκ
  have hχ : χ.comp α = algebraMap A p.ResidueField := IsLocalization.Away.lift_comp g hgκ
  have : ∀ n : ℤ, Module.Flat (Localization.Away g) ((extendScalarsComplex α C).X n) :=
    fun n => by
      have : Module.Flat A (C.X n) := flat_baseAlternatingCechComplex_X f U hU _ hUaff hflat n
      let : Algebra A (Localization.Away g) := α.toAlgebra
      exact Module.Flat.baseChange A (Localization.Away g) (C.X n)
  have : QuasiIso (((ModuleCat.extendScalars.{u, u, u} χ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map u) :=
    StacksDraft.PseudoCoherence.quasiIso_extendScalars_map_of_flat χ b (Fintype.card I : ℤ) u
  have hr0 : Module.finrank p.ResidueField ((extendScalarsComplex χ P).homology 0) = r :=
    (isoOfQuasiIsoAt (((ModuleCat.extendScalars.{u, u, u} χ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map u) 0).toLinearEquiv.finrank_eq.trans
      ((((HomologicalComplex.homologyFunctor _ _ 0).mapIso
        ((extendScalarsComplexCompIso α χ).app C)).toLinearEquiv.finrank_eq).trans
        ((finrank_homology_extendScalarsComplex_congr hχ C 0).trans hr))
  exact matrix_map_eq_zero_of_finrank hP e₀ e₁ M hM χ hr0

include hU hUaff hflat u b hP e₀ e₁ hM in
/-- **The first differential of the minimal model vanishes near `p`.** If the matrix `M` of the
first differential of the model vanishes modulo `p`, then it vanishes after inverting some
`t ∉ p`: for every ring map `φ : A ⟶ B` inverting `g` and `t`, `M ⊗ B = 0`. -/
theorem exists_notMem_matrix_map_eq_zero (hg : g ∉ p)
    (hMp : ∀ hgκ : IsUnit (algebraMap A p.ResidueField g),
      M.map (IsLocalization.Away.lift g hgκ) = 0) :
    ∃ t : A, t ∉ p ∧ ∀ {B : Type u} [CommRing B] (φ : A →+* B) (hgφ : IsUnit (φ g)),
      IsUnit (φ t) → M.map (IsLocalization.Away.lift g hgφ) = 0 := by
  classical
  let α := algebraMap A (Localization.Away g)
  have hgκ : IsUnit (algebraMap A p.ResidueField g) := by
    refine isUnit_iff_ne_zero.2 fun h => hg ?_
    rw [← Ideal.ker_algebraMap_residueField p]
    exact h
  let χ : Localization.Away g →+* p.ResidueField := IsLocalization.Away.lift g hgκ
  have hχ : χ.comp α = algebraMap A p.ResidueField := IsLocalization.Away.lift_comp g hgκ
  -- the fibre over `p` and its global functions, a finite étale algebra
  let Xκ := pullback f (Spec.map (CommRingCat.ofHom (χ.comp α)))
  let fκ : Xκ ⟶ Spec (.of p.ResidueField) := pullback.snd _ _
  let gκ : Xκ ⟶ X := pullback.fst _ _
  have hsqκ : IsPullback gκ fκ f (Spec.map (CommRingCat.ofHom (χ.comp α))) :=
    IsPullback.of_hasPullback _ _
  let : Algebra p.ResidueField Γ(Xκ, ⊤) :=
      ((Stacks.Cech.globalRingHom fκ).hom : p.ResidueField →+* Γ(Xκ, ⊤)).toAlgebra
  obtain ⟨hEet, hEfin⟩ := etale_and_finite_globalSections_of_isPullback hsqκ
  let bE := Module.Free.chooseBasis p.ResidueField Γ(Xκ, ⊤)
  obtain ⟨L, _, _, hLfin, hLsplit⟩ :=
    Algebra.Etale.exists_finiteDimensional_span_setOf_isIdempotentElem_eq_top bE
  -- a finite free extension realizing `L` as a residue field
  obtain ⟨S, _, φS, hfree, hqprime, hpq, Φ, hΦ⟩ :=
    exists_isFiniteFree_residueField_equiv A p L
  let q := p.map φS
  have : q.IsPrime := hqprime
  let : Algebra A S := φS.toAlgebra
  have : Module.Free A S := hfree.1
  have : Module.Finite A S := hfree.2
  have : IsNoetherianRing S := IsNoetherianRing.of_finite A S
  let Bq := Localization.AtPrime q
  let φB : A →+* Bq := (algebraMap S Bq).comp φS
  have hgS : φS g ∉ q := fun h => hg (by rwa [hpq])
  have hgB : IsUnit (φB g) := IsLocalization.map_units Bq (⟨φS g, hgS⟩ : q.primeCompl)
  let ψB : Localization.Away g →+* Bq := IsLocalization.Away.lift g hgB
  have hψB : ψB.comp α = φB := IsLocalization.Away.lift_comp g hgB
  -- the base change to `Bq`
  let XB := pullback f (Spec.map (CommRingCat.ofHom (ψB.comp α)))
  let fB : XB ⟶ Spec (.of Bq) := pullback.snd _ _
  let gB : XB ⟶ X := pullback.fst _ _
  have hsqB : IsPullback gB fB f (Spec.map (CommRingCat.ofHom (ψB.comp α))) :=
    IsPullback.of_hasPullback _ _
  have : IsProper fB := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsqB inferInstance
  -- the fibre over the closed point
  let y : Spec (.of Bq) := IsLocalRing.closedPoint Bq
  have hy : y.asIdeal = IsLocalRing.maximalIdeal Bq := rfl
  let κy := (Spec (.of Bq)).residueField y
  let ψy : Bq →+* κy := (CommRingCat.ofHom (algebraMap Bq y.asIdeal.ResidueField) ≫
    (Scheme.Spec.residueFieldIso (.of Bq) y).inv).hom
  have hψy : Spec.map (CommRingCat.ofHom ψy) = (Spec (.of Bq)).fromSpecResidueField y := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp]
    rfl
  let Xy := fB.fiber y
  let gy : Xy ⟶ XB := fB.fiberι y
  let fy : Xy ⟶ Spec (.of κy) := fB.fiberToSpecResidueField y
  have hsqy : IsPullback gy fy fB (Spec.map (CommRingCat.ofHom ψy)) := by
    rw [hψy]
    exact IsPullback.of_hasPullback _ _
  have hsqyA : IsPullback (gy ≫ gB) fy f
      (Spec.map (CommRingCat.ofHom ((ψy.comp ψB).comp α))) := by
    have h := hsqy.paste_horiz hsqB
    rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc] at h
  -- the residue field map `κ(p) ⟶ κ(y)`
  have hqy : q = y.asIdeal.comap (algebraMap S Bq) :=
    (Localization.AtPrime.under_maximalIdeal (I := q)).symm
  let jq : q.ResidueField →+* κy := (Scheme.Spec.residueFieldIso (.of Bq) y).inv.hom.comp
    (Ideal.ResidueField.map q y.asIdeal (algebraMap S Bq) hqy)
  let ι : p.ResidueField →+* κy := jq.comp (Ideal.ResidueField.map p q φS hpq)
  have hι : ι.comp (algebraMap A p.ResidueField) = ψy.comp φB := by
    ext a
    simp only [ι, jq, ψy, φB, RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
    rfl
  have hιχ : ι.comp χ = ψy.comp ψB :=
    IsLocalization.ringHom_ext (Submonoid.powers g) (by
      calc (ι.comp χ).comp α = ι.comp (χ.comp α) := RingHom.comp_assoc _ _ _
        _ = ι.comp (algebraMap A p.ResidueField) := by rw [hχ]
        _ = ψy.comp φB := hι
        _ = (ψy.comp ψB).comp α := by rw [RingHom.comp_assoc, hψB])
  -- the minimal polynomials of the basis of `Γ(X_p, 𝒪)` split over `κ(y)`
  have hsplit : ∀ i, ((minpoly p.ResidueField (bE i)).map ι).Splits := by
    intro i
    have h := (hLsplit i).map (jq.comp Φ.symm.toRingHom)
    have hj : (jq.comp Φ.symm.toRingHom).comp (algebraMap p.ResidueField L) = ι := by
      rw [← hΦ]
      ext x
      simp only [ι, inducedResidueMap, RingHom.comp_apply]
      show jq (Φ.symm (Φ _)) = _
      rw [RingEquiv.symm_apply_apply]
    rwa [Polynomial.map_map, hj] at h
  -- the square exhibiting the fibre over `y` as a base change of the fibre over `p`
  have hcomm : Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (CommRingCat.ofHom (χ.comp α)) =
      Spec.map (CommRingCat.ofHom ((ψy.comp ψB).comp α)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hιχ]
  let gyκ : Xy ⟶ Xκ := hsqκ.lift (gy ≫ gB) (fy ≫ Spec.map (CommRingCat.ofHom ι)) (by
    rw [hsqyA.w, Category.assoc, hcomm])
  have hgyκ : gyκ ≫ gκ = gy ≫ gB := hsqκ.lift_fst _ _ _
  have hsq' : IsPullback gyκ fy fκ (Spec.map (CommRingCat.ofHom ι)) := by
    refine IsPullback.of_right ?_ (hsqκ.lift_snd _ _ _) hsqκ
    rwa [hgyκ, hcomm]
  have hsq'' : IsPullback (gyκ ≫ gκ) fy f
      (Spec.map (CommRingCat.ofHom ((ι.comp χ).comp α))) := by
    rwa [hgyκ, hιχ]
  have hMχ : M.map χ = 0 := hMp hgκ
  -- the global functions of the fibre over `y` are spanned by their idempotents
  let : Algebra κy Γ(Xy, ⊤) :=
      ((Stacks.Cech.globalRingHom fy).hom : κy →+* Γ(Xy, ⊤)).toAlgebra
  have hspanY : Submodule.span κy {x : Γ(Xy, ⊤) | IsIdempotentElem x} = ⊤ := by
    let := ι.toAlgebra
    let : Algebra p.ResidueField Γ(Xy, ⊤) :=
      ((algebraMap κy Γ(Xy, ⊤)).comp (algebraMap p.ResidueField κy)).toAlgebra
    let : IsScalarTower p.ResidueField κy Γ(Xy, ⊤) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hbij := bijective_lift_appTop_of_matrix_map_eq_zero α U hU hUaff hflat u b hP e₀ e₁ M hM
      χ hMχ (B' := κy) hsqκ hsq' hsq''
    let μ := Algebra.TensorProduct.lift (Algebra.ofId κy Γ(Xy, ⊤))
      (Algebra.TensorProduct.algHomOfLiesOver (B := p.ResidueField) (B' := κy) gyκ.appTop.hom
        (fun c =>
          (globalRingHom_naturality (algebraMap p.ResidueField κy) fκ fy gyκ hsq'.w c).symm))
      fun _ _ => Commute.all _ _
    have hspan := Algebra.Etale.span_setOf_isIdempotentElem_tensorProduct_eq_top (F := κy) bE
      hsplit
    have hrange : LinearMap.range μ.toLinearMap = ⊤ := LinearMap.range_eq_top.mpr hbij.2
    have himage := Submodule.span_image μ.toLinearMap (s := {x | IsIdempotentElem x})
    rw [hspan, Submodule.map_top, hrange] at himage
    refine eq_top_iff.2 (himage.symm ▸ Submodule.span_mono ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact hx.map μ
  -- every idempotent of the fibre extends to `X_B` (Tag 0G7X), so restriction to the fibre is onto
  have : y.asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal Bq
  have hψysurj : Function.Surjective ψy :=
    (Scheme.Spec.residueFieldIso (.of Bq) y).commRingCatIsoToRingEquiv.symm.surjective.comp
      (Ideal.algebraMap_residueField_surjective y.asIdeal)
  have hsurj : Function.Surjective gy.appTop :=
    surjective_appTop_fiberι_of_span_isIdempotentElem ψy hψysurj fB y
      (fun V hV => (IsLocalRing.closedPoint_mem_iff (R := Bq) V).1 hV) fy hsqy.w hspanY
  -- Nakayama: every vector over `κ(y)` lifts to the kernel of `M ⊗ B`, so `M ⊗ B = 0`
  have hψyker : ∀ c, ψy c = 0 → c ∈ IsLocalRing.maximalIdeal Bq := fun c hc => by
    show c ∈ y.asIdeal
    rw [← Ideal.algebraMap_residueField_eq_zero]
    exact (Scheme.Spec.residueFieldIso (.of Bq) y).commRingCatIsoToRingEquiv.symm.injective
      (hc.trans (map_zero _).symm)
  have hMy : M.map (ψy.comp ψB) = 0 := by
    rw [← hιχ]
    exact matrix_map_comp_eq_zero M χ hMχ ι
  have hMB : M.map ψB = 0 := matrix_map_eq_zero_of_surjective_appTop U hU hUaff hflat u b hP
    e₀ e₁ M hM ψB ψy hψyker hMy hsqB hsqy hsqyA hsurj
  -- clearing denominators: each entry of `M` is killed by an element outside `p`
  exact exists_notMem_matrix_map_eq_zero_of_map_atPrime p M q le_rfl ψB hψB hMB

include hU hUaff hflat u b hP e₀ e₁ hM in
/-- **Once `M ⊗ B` vanishes, the global functions of the base change are finite étale.** For a
ring map `ψ : A_g ⟶ B` with `M ⊗ B = 0` and a base change `X'` of `X` to `B`, the `B`-algebra
`Γ(X', 𝒪_{X'})` is finite and étale: it is free of rank `r`, and its fibre at a prime `q` of `B`
is the algebra of global functions of the fibre `X'_q`, which is étale over `κ(q)` by
[Stacks, Tag 0BUG] because `X'_q` is proper and smooth over `κ(q)`. -/
theorem etale_globalFunctions_of_matrix_map_eq_zero {B : Type u} [CommRing B]
    (ψ : Localization.Away g →+* B) (hψ : M.map ψ = 0) {X' : Scheme.{u}}
    {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X}
    (hsq : IsPullback g' f' f
      (Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap A (Localization.Away g)))))) :
    letI : Algebra B Γ(X', ⊤) :=
      ((Stacks.Cech.globalRingHom f').hom : B →+* Γ(X', ⊤)).toAlgebra
    Algebra.Etale B Γ(X', ⊤) ∧ Module.Finite B Γ(X', ⊤) := by
  let : Algebra B Γ(X', ⊤) :=
      ((Stacks.Cech.globalRingHom f').hom : B →+* Γ(X', ⊤)).toAlgebra
  let θ := freeFunctionsEquiv (algebraMap A (Localization.Away g)) U hU hUaff hflat u b hP e₀ e₁
    M hM ψ hψ hsq
  have hfree : Module.Free B Γ(X', ⊤) := Module.Free.of_equiv θ
  have hfin : Module.Finite B Γ(X', ⊤) := Module.Finite.equiv θ
  refine ⟨?_, hfin⟩
  refine Algebra.Etale.of_free_of_forall_residueField fun q _ => ?_
  -- the fibre of `X'` over `q`
  let Xq := pullback f' (Spec.map (CommRingCat.ofHom (algebraMap B q.ResidueField)))
  let fq : Xq ⟶ Spec (.of q.ResidueField) := pullback.snd _ _
  let gq : Xq ⟶ X' := pullback.fst _ _
  have hsqq : IsPullback gq fq f' (Spec.map (CommRingCat.ofHom (algebraMap B q.ResidueField))) :=
    IsPullback.of_hasPullback _ _
  have hsqqA : IsPullback (gq ≫ g') fq f (Spec.map (CommRingCat.ofHom
      (((algebraMap B q.ResidueField).comp ψ).comp (algebraMap A (Localization.Away g))))) := by
    have h := hsqq.paste_horiz hsq
    rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc] at h
  have : IsProper f' := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  have : Smooth f' := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  let : Algebra q.ResidueField Γ(Xq, ⊤) :=
      ((Stacks.Cech.globalRingHom fq).hom : q.ResidueField →+* Γ(Xq, ⊤)).toAlgebra
  obtain ⟨hEet, -⟩ := etale_and_finite_globalSections_of_isPullback hsqq
  have hbij := bijective_lift_appTop_of_matrix_map_eq_zero (algebraMap A (Localization.Away g))
    U hU hUaff hflat u b hP e₀ e₁ M hM ψ hψ (B' := q.ResidueField) hsq hsqq hsqqA
  exact Algebra.FormallyUnramified.of_equiv (AlgEquiv.ofBijective _ hbij).symm

omit [IsNoetherianRing A] [Smooth f] in
include hU hUaff hflat u b hP e₀ e₁ hM in
/-- **Once `M ⊗ B` vanishes, the derived global sections of the base change split off their
degree-zero cohomology.** For a ring map `ψ : A_g ⟶ B` with `M ⊗ B = 0` and a base change `X'` of
`X` to `B`,

`RΓ(X', 𝒪_{X'}) ≅ B^r[0] ⊕ K`

in `D(B)`, where `K` is a bounded complex of finite free `B`-modules concentrated in degrees
`[1, b]`: it is the brutal truncation `σ^{≥1}` of `P ⊗ B`, whose first differential `M ⊗ B`
vanishes. -/
theorem nonempty_derivedGlobalSectionsOver_iso_of_matrix_map_eq_zero [LinearOrder I]
    (haff : ∀ (k : ℕ) (s : Fin (k + 1) → I), IsAffineOpen (⨅ j, U (s j)))
    [P.IsStrictlyGE 0]
    (hPX : ∀ n, ∃ k : ℕ, Nonempty (P.X n ≅
      ModuleCat.of (Localization.Away g) (Fin k → Localization.Away g)))
    {B : Type u} [CommRing B] (ψ : Localization.Away g →+* B) (hψ : M.map ψ = 0)
    {X' : Scheme.{u}} {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X}
    (hsq : IsPullback g' f' f
      (Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap A (Localization.Away g)))))) :
    ∃ K : CochainComplex (ModuleCat.{u} B) ℤ, K.IsStrictlyGE 1 ∧ K.IsStrictlyLE b ∧
      (∀ i, Module.Free B (K.X i) ∧ Module.Finite B (K.X i)) ∧
      Nonempty ((derivedGlobalSectionsOver f').obj
          ((DerivedCategory.singleFunctor X'.Modules 0).obj (Scheme.unitModule X')) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B (Fin r → B)) ⊞
          DerivedCategory.Q.obj K) := by
  classical
  let α := algebraMap A (Localization.Away g)
  have : IsSeparated f' := isSeparated_of_isPullback (ψ.comp α) hsq
  let F' := (Scheme.Modules.pullback g').obj (Scheme.unitModule X)
  have : F'.IsQuasicoherent := isQuasicoherent_of_iso _ _ _
    (Scheme.Modules.pullbackUnitIso g').symm inferInstance
  let PB := extendScalarsComplex ψ P
  -- the Čech model of the base change, computed by the model `P ⊗ B`
  have hqi := quasiIso_kernelChainComparison α (Scheme.unitModule X) U hU hUaff u hflat b ψ hsq
  have := (DerivedCategory.isIso_Q_map_iff_quasiIso _
    (kernelChainComparison α (Scheme.unitModule X) U hU hUaff u ψ hsq)).2 hqi
  let e₁' : DerivedCategory.Q.obj PB ≅ DerivedCategory.Q.obj (baseAlternatingCechComplex f'
      (fun j => g' ⁻¹ᵁ U j) (top_eq_iSup_preimage g' U hU) F') :=
    asIso (DerivedCategory.Q.map (kernelChainComparison α (Scheme.unitModule X) U hU hUaff u ψ hsq))
  let e₂' := alternatingCechIsoDerivedGlobalSectionsOverBase f' (fun j => g' ⁻¹ᵁ U j)
    (top_eq_iSup_preimage g' U hU) F' (iInf_preimage_isAffineOpen (ψ.comp α) hsq U hUaff)
  obtain ⟨e₃'⟩ := nonempty_derivedGlobalSectionsOver_iso_derivedGlobalSectionsOverBase f' F'
  let e₄' : (derivedGlobalSectionsOver f').obj
      ((DerivedCategory.singleFunctor X'.Modules 0).obj (Scheme.unitModule X')) ≅
      (derivedGlobalSectionsOver f').obj ((DerivedCategory.singleFunctor X'.Modules 0).obj F') :=
    (derivedGlobalSectionsOver f').mapIso
      ((DerivedCategory.singleFunctor X'.Modules 0).mapIso (Scheme.Modules.pullbackUnitIso g').symm)
  -- the model splits: its first differential vanishes
  have hPB0 : PB.d 0 1 = 0 := by
    ext x
    apply (termEquiv ψ e₁).injective
    show termEquiv ψ e₁ ((ModuleCat.extendScalars.{u, u, u} ψ).map (P.d 0 1) x) = _
    rw [termEquiv_map ψ e₀ e₁ (P.d 0 1) M hM x, hψ, Matrix.zero_mulVec]
    simp
  have : PB.IsStrictlyGE 0 := (CochainComplex.isStrictlyGE_iff PB 0).2 fun i hi =>
    (ModuleCat.extendScalars.{u, u, u} ψ).map_isZero (P.isZero_of_isStrictlyGE 0 i hi)
  have hPBle : ∀ i, b < i → IsZero (PB.X i) := fun i hi =>
    (ModuleCat.extendScalars.{u, u, u} ψ).map_isZero (P.isZero_of_isStrictlyLE b i hi)
  obtain ⟨es⟩ := StacksDraft.StupidTruncation.nonempty_iso_single_biprod_stupidTrunc PB hPB0
  let K := PB.stupidTrunc (ComplexShape.embeddingUpIntGE 1)
  have : PreservesBinaryBiproducts (DerivedCategory.Q (C := ModuleCat.{u} B)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let eX : PB.X 0 ≅ ModuleCat.of B (Fin r → B) := (termEquiv ψ e₀).toModuleIso
  refine ⟨K, inferInstance, (CochainComplex.isStrictlyLE_iff K b).2 fun i hi => ?_,
    fun i => ?_, ⟨e₄' ≪≫ e₃' ≪≫ e₂'.symm ≪≫ e₁'.symm ≪≫ DerivedCategory.Q.mapIso es ≪≫
      DerivedCategory.Q.mapBiprod _ _ ≪≫ biprod.mapIso
        (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} B) 0).app (PB.X 0)).symm ≪≫
          (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).mapIso eX) (Iso.refl _)⟩⟩
  · by_cases h1 : 1 ≤ i
    · exact IsZero.of_iso (hPBle i hi) (StacksDraft.StupidTruncation.stupidTruncGEXIso PB 1 i h1)
    · exact CochainComplex.isZero_of_isStrictlyGE K 1 i (by omega)
  · by_cases h1 : 1 ≤ i
    · obtain ⟨k, ⟨e⟩⟩ := hPX i
      let t : K.X i ≃ₗ[B] (Fin k → B) :=
        (StacksDraft.StupidTruncation.stupidTruncGEXIso PB 1 i h1).toLinearEquiv.trans
          (termEquiv ψ e)
      exact ⟨Module.Free.of_equiv t.symm, Module.Finite.equiv t.symm⟩
    · have : Subsingleton (K.X i) :=
        ModuleCat.subsingleton_of_isZero (CochainComplex.isZero_of_isStrictlyGE K 1 i (by omega))
      exact ⟨Module.Free.of_subsingleton _ _, ⟨⟨∅, Subsingleton.elim _ _⟩⟩⟩

end KillMatrix

/-! ### The main statement -/

/-- **The global functions and the derived global sections of a proper smooth family over a
Noetherian affine base, near a point.** Let `A` be a Noetherian ring, `f : X ⟶ Spec A` proper
and smooth, and `p` a prime of `A`. There are `h ∉ p`, `r ∈ ℕ` and `b ∈ ℤ` such that for every
ring map `φ : A ⟶ B` with `φ h` a unit and every base change `X'` of `X` to `B`:

* `Γ(X', 𝒪_{X'})` is a finite étale `B`-algebra; and
* `RΓ(X', 𝒪_{X'}) ≅ B^r[0] ⊕ K` in `D(B)`, for a complex `K` of finite free `B`-modules
  concentrated in degrees `[1, b]`. -/
theorem exists_away_globalFunctions_finiteEtale_and_split {A : Type u} [CommRing A]
    [IsNoetherianRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] [Smooth f]
    (p : Ideal A) [p.IsPrime] :
    ∃ (h : A) (_ : h ∉ p) (r : ℕ) (b : ℤ),
      ∀ {B : Type u} [CommRing B] (φ : A →+* B), IsUnit (φ h) →
        ∀ {X' : Scheme.{u}} {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X},
        IsPullback g' f' f (Spec.map (CommRingCat.ofHom φ)) →
        (letI : Algebra B Γ(X', ⊤) :=
            ((Stacks.Cech.globalRingHom f').hom : B →+* Γ(X', ⊤)).toAlgebra;
          Algebra.Etale B Γ(X', ⊤) ∧ Module.Finite B Γ(X', ⊤)) ∧
        ∃ K : CochainComplex (ModuleCat.{u} B) ℤ, K.IsStrictlyGE 1 ∧ K.IsStrictlyLE b ∧
          (∀ i, Module.Free B (K.X i) ∧ Module.Finite B (K.X i)) ∧
          Nonempty ((derivedGlobalSectionsOver f').obj
              ((DerivedCategory.singleFunctor X'.Modules 0).obj (Scheme.unitModule X')) ≅
            (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
                (ModuleCat.of B (Fin r → B)) ⊞
              DerivedCategory.Q.obj K) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : (Scheme.unitModule X).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have hflat : IsFlatOver f.toLRSHom.toShHom (Scheme.unitModule X) := isFlatOver_unit_of_flat f
  obtain ⟨I, hIfin, hIlin, U, hU, hUaff, haff⟩ := exists_finiteAffineCover_of_isProper f
  let := hIlin
  have := hIfin
  let C := baseAlternatingCechComplex f U hU (Scheme.unitModule X)
  have hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj C) :=
    isPerfect_Q_baseAlternatingCechComplex f U hU _ hUaff haff hflat
  have hpc := StacksDraft.Perfect.isPseudoCoherent_of_isPerfect.{u, u} _ hperf
  let κ := p.ResidueField
  have hmodel : ∀ i : ℤ, Module.finrank κ
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) i).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A κ)).functor.obj (DerivedCategory.Q.obj C))) =
      Module.finrank κ ((extendScalarsComplex (algebraMap A κ) C).homology i) := fun i =>
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) i).mapIso
      (totalDerivedExtensionScalarsModelIso f U hU _ (algebraMap A κ) hUaff hflat) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} κ) i).app _).toLinearEquiv.finrank_eq
  have hvan : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) i).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A κ)).functor.obj (DerivedCategory.Q.obj C))) := fun i hi => by
    refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) i).mapIso
      (totalDerivedExtensionScalarsModelIso f U hU _ (algebraMap A κ) hUaff hflat) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} κ) i).app _)
    exact ShortComplex.isZero_homology_of_isZero_X₂ _
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap A κ)).map_isZero
        (isZero_baseAlternatingCechComplex_X_of_neg f U hU _ i hi))
  obtain ⟨g, hg, -, P, b, hPge, hPle, hPX, ⟨eP⟩⟩ :=
    open StacksDraft.Perfect in
    exists_away_bounded_free_complex_representing_of_fibre_vanishing_below.{u, u}
      p (DerivedCategory.Q.obj C) hpc ⟨0, inferInstance⟩ 0 hvan
  let Ag := Localization.Away g
  let α := algebraMap A Ag
  let r := Module.finrank κ ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) 0).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A κ)).functor.obj (DerivedCategory.Q.obj C)))
  let β := Module.finrank κ ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) 1).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A κ)).functor.obj (DerivedCategory.Q.obj C)))
  have : P.IsStrictlyLE b := hPle
  have : P.IsStrictlyGE 0 := hPge
  have hproj : ∀ n, Projective (P.X n) := fun n =>
    Projective.of_iso (hPX n).some.symm
      (ModuleCat.projective_of_free (Module.Free.chooseBasis Ag _))
  have : ∀ n, Module.Flat Ag (P.X n) := fun n =>
    Module.Flat.of_linearEquiv (hPX n).some.toLinearEquiv
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  obtain ⟨u, hu⟩ := StacksDraft.PseudoCoherence.exists_chainMap_of_isKProjective P
    (extendScalarsComplex α C)
    (eP.hom ≫ (totalDerivedExtensionScalarsModelIso f U hU _ α hUaff hflat).hom)
  have : QuasiIso u := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 (by
    rw [hu]
    infer_instance)
  have hP : IsZero (P.X (-1)) := P.isZero_of_isStrictlyGE 0 (-1)
  let e₀ : P.X 0 ≅ ModuleCat.of Ag (Fin r → Ag) :=
    (hPX 0).some ≪≫ (ULift.moduleEquiv (R := Ag) (M := Fin r → Ag)).toModuleIso
  let e₁ : P.X 1 ≅ ModuleCat.of Ag (Fin β → Ag) :=
    (hPX 1).some ≪≫ (ULift.moduleEquiv (R := Ag) (M := Fin β → Ag)).toModuleIso
  let L : (Fin r → Ag) →ₗ[Ag] (Fin β → Ag) := e₁.hom.hom ∘ₗ (P.d 0 1).hom ∘ₗ e₀.inv.hom
  let M := LinearMap.toMatrix' L
  have hM : P.d 0 1 = e₀.hom ≫ ModuleCat.ofHom M.mulVecLin ≫ e₁.inv := by
    ext x
    simp [M, L]
  -- the differential vanishes over `κ(p)` by minimality, hence near `p`
  obtain ⟨t, ht, hMt⟩ := exists_notMem_matrix_map_eq_zero p U hU hUaff hflat u b hP e₀ e₁ M hM
    hg (matrix_map_residueField_eq_zero p U hU hUaff hflat u b hP e₀ e₁ M hM (hmodel 0).symm)
  have hPX' : ∀ n, ∃ k : ℕ, Nonempty (P.X n ≅ ModuleCat.of Ag (Fin k → Ag)) := fun n =>
    ⟨_, ⟨(hPX n).some ≪≫ (ULift.moduleEquiv (R := Ag)).toModuleIso⟩⟩
  refine ⟨g * t, fun hmem => (Ideal.IsPrime.mem_or_mem inferInstance hmem).elim hg ht, r, b,
    fun {B} _ φ hφ {X'} {f'} {g'} hsq => ?_⟩
  have hgφ : IsUnit (φ g) := isUnit_of_mul_isUnit_left (by rwa [← map_mul])
  have htφ : IsUnit (φ t) := isUnit_of_mul_isUnit_right (by rwa [← map_mul])
  let ψ : Ag →+* B := IsLocalization.Away.lift g hgφ
  have hψ : ψ.comp α = φ := IsLocalization.Away.lift_comp g hgφ
  have hsq' : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (ψ.comp α))) := by
    rwa [hψ]
  have hMψ : M.map ψ = 0 := hMt φ hgφ htφ
  exact ⟨etale_globalFunctions_of_matrix_map_eq_zero U hU hUaff hflat u b hP e₀ e₁ M hM ψ hMψ hsq',
    nonempty_derivedGlobalSectionsOver_iso_of_matrix_map_eq_zero U hU hUaff hflat u b hP e₀ e₁
      M hM haff hPX' ψ hMψ hsq'⟩

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end
