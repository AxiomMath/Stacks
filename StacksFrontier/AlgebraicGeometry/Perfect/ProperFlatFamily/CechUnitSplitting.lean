module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsKernelModel
public import StacksFrontier.Homology.Perfect.DegreeZeroSplitting
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection

/-!
# The Čech model of `RΓ(X, 𝒪_X)` splits off the base ring near a point

This file carries the commutative-algebra core of [Stacks, Tag 0E62], at the level of the
`A`-linear alternating Čech model `C = Č(U, 𝒪_X)` of a finite affine cover with affine
intersections of a separated `f : X ⟶ Spec A` with `𝒪_X` flat over `A`
(`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.baseAlternatingCechComplex`).

## Main results

* `…ProperFlatFamilyCech.exists_away_unitSplitting`: if `C` is pseudo-coherent in `D(A)`, the
  derived fibre at a prime `p` has one-dimensional degree-zero cohomology, and the cochain of the
  global function `1` survives in `C ⊗_A κ(p)`, then there is `h ∉ p` such that
  - for every `A`-algebra `B` in which `h` is invertible and every base change `X'` of `X` to `B`,
    the global sections of `g^*𝒪_X` on `X'` are free of rank one over `B`, and
  - in `D(A_h)` the localized model is `A_h[0] ⊕ T` with `T` a bounded complex of finite free
    `A_h`-modules concentrated in degrees `≥ 1`.
* `…ProperFlatFamilyCech.finrank_homology_zero_extendScalars_residueField` and
  `…ProperFlatFamilyCech.one_tmul_unitCochain_ne_zero`: the two fibre hypotheses of the previous
  result follow from bijectivity of `κ(p) → Γ(X_{κ(p)}, 𝒪)`.
* `…ProperFlatFamilyCech.pullbackUnitIso_hom_app_pullbackSectionHom_one`: under `g^*𝒪_X ≅ 𝒪_{X'}`
  the pullback of the function `1` is `1`.

## Implementation notes

The argument is the source's steps 3 and 4 (More on Algebra, Lemmas 0A1U, 0658, 00NX, 00O0) run
through the minimal representative of [Stacks, Tag 0BCD]
(`StacksDraft.Perfect.exists_away_bounded_free_complex_representing_of_fibre_vanishing_below`),
following the degree-zero kernel model of
`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.exists_away_kernelModel`, whose only Noetherian
input — perfectness of the Čech model — is here a hypothesis supplied by the caller from
[Stacks, Tag 0A1H]. The minimal model `P` over `A_g` vanishes in negative degrees and has `P⁰`
free of rank `dim H⁰(C ⊗ κ(p)) = 1`. The quasi-isomorphism `P ⟶ C_g` is bijective on degree-zero
cocycles, so the cochain of `1` lifts to a cocycle `z ∈ P⁰ ≅ A_g`; it is nonzero modulo `p`
because the cochain of `1` survives in the fibre. Inverting a numerator `a` of `z` makes `z` a
unit, which forces the first differential of `P` to vanish, so `P_h = A_h[0] ⊕ T`
(`CochainComplex.exists_iso_single_biprod_of_d_zero`). Over every `A_h`-algebra `B` the degree-zero
cocycles of `P ⊗ B` are then all of `P⁰ ⊗ B ≅ B`, and the comparison `P ⊗ B ⟶ Č(X_B)` of
`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.kernelChainComparison` identifies them with the
global sections of the pullback of `𝒪_X`.

## References

* [Stacks Project, Tag 0E62](https://stacks.math.columbia.edu/tag/0E62)
* [Stacks Project, Tag 0A1U](https://stacks.math.columbia.edu/tag/0A1U)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatFamilyCech

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.AlgebraicGeometry.ProperFlatGlobalSections

section UnitSection

/-- The global function `1`, as a global section of the structure module. -/
def oneSection (X : Scheme.{u}) : Γ(Scheme.unitModule X, ⊤) :=
  show Γ(X, ⊤) from 1

/-- The identification `g^* 𝒪_X ≅ 𝒪_{X'}` sends the pullback of the global function `1` to `1`. -/
theorem pullbackUnitIso_hom_app_pullbackSectionHom_one {X X' : Scheme.{u}} (g : X' ⟶ X) :
    (Scheme.Modules.pullbackUnitIso g).hom.app ⊤
      (pullbackSectionHom g (Scheme.unitModule X) ⊤ ⊤ (by simp) (oneSection X)) =
        oneSection X' := by
  have h := Scheme.Modules.pullbackUnitIso_homEquiv g
  rw [Adjunction.homEquiv_unit] at h
  have h1 := congrArg (fun φ => φ.app (⊤ : X.Opens) (oneSection X)) h
  dsimp only at h1
  rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    Scheme.Modules.pushforward_map_app] at h1
  have hle : (⊤ : X'.Opens) ≤ g ⁻¹ᵁ ⊤ := by simp
  set y := ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (Scheme.unitModule X)).app ⊤
      (oneSection X)
  have hnat : (Scheme.Modules.pullbackUnitIso g).hom.app ⊤
        (((Scheme.Modules.pullback g).obj (Scheme.unitModule X)).presheaf.map (homOfLE hle).op y) =
      (Scheme.unitModule X').presheaf.map (homOfLE hle).op
        ((Scheme.Modules.pullbackUnitIso g).hom.app (g ⁻¹ᵁ ⊤) y) :=
    ConcreteCategory.congr_hom
      ((Scheme.Modules.pullbackUnitIso g).hom.mapPresheaf.naturality (homOfLE hle).op) y
  refine hnat.trans ?_
  refine (congrArg (ConcreteCategory.hom ((Scheme.unitModule X').presheaf.map (homOfLE hle).op))
    h1).trans ?_
  change (X'.presheaf.map (homOfLE hle).op).hom ((g.app ⊤).hom 1) = (1 : Γ(X', ⊤))
  rw [map_one, map_one]

end UnitSection


section Core

open scoped ChangeOfRings TensorProduct Matrix

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsSeparated f]
  (hflat : IsFlatOver f.toLRSHom.toShHom (Scheme.unitModule X))
  {I : Type u} [Fintype I] [LinearOrder I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i))

/-- The degree-`0` Čech cochain of the global function `1`. -/
def unitCochain : (baseAlternatingCechComplex f U hU (Scheme.unitModule X)).X 0 :=
  sectionsToModel f U hU (Scheme.unitModule X) (oneSection X)

omit [IsSeparated f] [Fintype I] [LinearOrder I] in
/-- The cochain of `1` is a cocycle: it is the cochain of a global section. -/
theorem unitCochain_mem_ker :
    unitCochain f U hU ∈
      LinearMap.ker ((baseAlternatingCechComplex f U hU (Scheme.unitModule X)).d 0 1).hom := by
  rw [← range_sectionsToModel]
  exact ⟨oneSection X, rfl⟩

/-- If two ring maps to `κ` agree, a pure tensor `1 ⊗ x` vanishes for one exactly when it vanishes
for the other. -/
theorem one_tmul_ne_zero_congr {A k : Type u} [CommRing A] [CommRing k] {M : ModuleCat.{u} A}
    {φ₁ φ₂ : A →+* k} (h : φ₁ = φ₂) (x : M) (hx : (1 : k) ⊗ₜ[A,φ₂] x ≠ 0) :
    (1 : k) ⊗ₜ[A, φ₁] x ≠ 0 :=
  h ▸ hx

/-- Extension of scalars along equal ring maps gives isomorphic complexes. -/
def extendScalarsComplexCongr {A k : Type u} [CommRing A] [CommRing k] {φ₁ φ₂ : A →+* k}
    (h : φ₁ = φ₂) (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    extendScalarsComplex φ₁ K ≅ extendScalarsComplex φ₂ K :=
  eqToIso (congrArg (fun φ => extendScalarsComplex φ K) h)

/-- The kernel of a one-column matrix whose column is killed by a unit is everything. -/
theorem matrix_map_eq_zero_of_mulVec {R B : Type u} [CommRing R] [CommRing B] {β r : ℕ}
    (hr : r = 1) (M : Matrix (Fin β) (Fin r) R) (v : Fin r → R) (hv : M *ᵥ v = 0) (ψ : R →+* B)
    (hu : ∀ k, IsUnit (ψ (v k))) : M.map ψ = 0 := by
  subst hr
  ext i j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  have h1 := congrFun hv i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Pi.zero_apply] at h1
  have h2 := congrArg ψ h1
  rw [map_mul, map_zero] at h2
  simpa using (hu 0).mul_left_eq_zero.mp h2

/-- A complex of finite free modules in degrees `[0, b]` with vanishing first differential is
`K⁰[0] ⊕ T` with `T` a complex of finite free modules in degrees `[1, b]`. -/
private theorem exists_iso_single_biprod_free_of_d_zero {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) (hK : ∀ i : ℤ, i < 0 → IsZero (K.X i))
    (hKb : ∀ i : ℤ, b < i → IsZero (K.X i)) (hd : K.d 0 1 = 0)
    (hfree : ∀ i, Module.Free R (K.X i)) (hfin : ∀ i, Module.Finite R (K.X i)) :
    ∃ T : CochainComplex (ModuleCat.{u} R) ℤ, T.IsStrictlyGE 1 ∧ T.IsStrictlyLE b ∧
      (∀ i, Module.Free R (T.X i)) ∧ (∀ i, Module.Finite R (T.X i)) ∧
      Nonempty (K ≅ (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        (K.X 0) ⊞ T) := by
  obtain ⟨T, hT0, hTX, eT⟩ := CochainComplex.exists_iso_single_biprod_of_d_zero K hK hd
  refine ⟨T, (CochainComplex.isStrictlyGE_iff T 1).2 fun i hi => hT0 i (by omega),
    (CochainComplex.isStrictlyLE_iff T b).2 fun i hi => ?_, fun i => ?_, fun i => ?_, eT⟩
  · rcases le_or_gt i 0 with hi0 | hi0
    · exact hT0 i hi0
    · exact IsZero.of_iso (hKb i hi) (hTX i hi0).some
  · rcases le_or_gt i 0 with hi | hi
    · have := ModuleCat.subsingleton_of_isZero (hT0 i hi)
      exact Module.Free.of_subsingleton _ _
    · have := hfree i
      exact Module.Free.of_equiv (hTX i hi).some.toLinearEquiv.symm
  · rcases le_or_gt i 0 with hi | hi
    · have := ModuleCat.subsingleton_of_isZero (hT0 i hi)
      exact Module.Finite.of_finite
    · have := hfin i
      exact Module.Finite.equiv (hTX i hi).some.toLinearEquiv.symm

/-- An element of `A_g` that survives in `κ(p)` becomes a unit after inverting a numerator of it,
which lies outside `p`. -/
private theorem exists_not_mem_isUnit_awayToAwayRight {A : Type u} [CommRing A] (p : Ideal A)
    [p.IsPrime] {g : A} (hgκ : IsUnit (algebraMap A p.ResidueField g)) (a : Localization.Away g)
    (hχa : IsLocalization.Away.lift (S := Localization.Away g) g hgκ a ≠ 0) :
    ∃ a' : A, a' ∉ p ∧
      IsUnit (IsLocalization.Away.awayToAwayRight (P := Localization.Away (g * a')) g a' a) := by
  let α := algebraMap A (Localization.Away g)
  let χ : Localization.Away g →+* p.ResidueField := IsLocalization.Away.lift g hgκ
  have hχ : χ.comp α = algebraMap A p.ResidueField := IsLocalization.Away.lift_comp g hgκ
  obtain ⟨⟨a', ⟨_, n, rfl⟩⟩, ha'⟩ := IsLocalization.surj (Submonoid.powers g) a
  dsimp only at ha'
  have ha'p : a' ∉ p := by
    intro hmem
    have h1 : algebraMap A p.ResidueField a' = 0 := by
      rwa [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]
    have h2 := congrArg χ ha'
    rw [map_mul, ← RingHom.comp_apply χ α, ← RingHom.comp_apply χ α, hχ, h1, map_pow] at h2
    exact hχa ((mul_eq_zero.mp h2).resolve_right (pow_ne_zero _ hgκ.ne_zero))
  refine ⟨a', ha'p, ?_⟩
  let Ah := Localization.Away (g * a')
  let β' : Localization.Away g →+* Ah := IsLocalization.Away.awayToAwayRight g a'
  have hβ' : β'.comp α = algebraMap A Ah :=
    RingHom.ext fun x => IsLocalization.Away.awayToAwayRight_eq g a' x
  have hgh : algebraMap A Ah (g * a') = algebraMap A Ah g * algebraMap A Ah a' := map_mul _ g a'
  have hua' : IsUnit (algebraMap A Ah a') :=
    isUnit_of_mul_isUnit_right (hgh ▸ IsLocalization.Away.algebraMap_isUnit (g * a'))
  have h2 := congrArg β' ha'
  rw [map_mul, ← RingHom.comp_apply β' α, ← RingHom.comp_apply β' α, hβ', map_pow] at h2
  exact isUnit_of_mul_isUnit_left (h2 ▸ hua')

/-- If a degree-`0` element `z` of a model `u : P ⟶ K ⊗_A R` lifts `1 ⊗ x` and `1 ⊗ x` survives
along `χ ∘ α`, then some coordinate of `z` survives along `χ`. -/
private theorem coord_ne_zero_of_one_tmul_ne_zero {A R k : Type u} [CommRing A] [CommRing R]
    [CommRing k] (α : A →+* R) (χ : R →+* k) {K : CochainComplex (ModuleCat.{u} A) ℤ}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (u : P ⟶ extendScalarsComplex α K) {r : ℕ}
    (e : P.X 0 ≅ ModuleCat.of R (Fin r → R)) (z : P.X 0) (x : K.X 0)
    (hz : u.f 0 z = (1 : R) ⊗ₜ[A,α] x) (hx : (1 : k) ⊗ₜ[A,χ.comp α] x ≠ 0) :
    (fun j => χ (e.hom z j)) ≠ 0 := by
  intro h0
  have key : ((1 : k) ⊗ₜ[R, χ] z : (ModuleCat.extendScalars.{u, u, u} χ).obj (P.X 0)) = 0 := by
    apply (termEquiv χ e).injective
    refine (termEquiv_tmul χ e 1 z).trans (Eq.trans ?_ (termEquiv χ e).map_zero.symm)
    funext j
    simpa using congrFun h0 j
  have h2 : (ModuleCat.extendScalarsComp α χ).inv.app (K.X 0)
      ((ModuleCat.extendScalars.{u, u, u} χ).map (u.f 0) ((1 : k) ⊗ₜ[R, χ] z)) =
      (1 : k) ⊗ₜ[A, χ.comp α] x := by
    rw [ModuleCat.ExtendScalars.map_tmul, hz]
    exact Stacks.Cech.extendScalarsComp_inv_app_one_one_tmul α χ (K.X 0) _
  have h3 : (ModuleCat.extendScalarsComp α χ).inv.app (K.X 0)
      ((ModuleCat.extendScalars.{u, u, u} χ).map (u.f 0) ((1 : k) ⊗ₜ[R, χ] z)) = 0 := by
    rw [key]
    change ((ModuleCat.extendScalarsComp α χ).inv.app (K.X 0)).hom
      (((ModuleCat.extendScalars.{u, u, u} χ).map (u.f 0)).hom 0) = 0
    rw [LinearMap.map_zero, LinearMap.map_zero]
  exact hx (h2.symm.trans h3)

/-- If a degree-`0` element `z` of a model `u : P ⟶ K ⊗_A A_g`, `g ∉ p`, with `P⁰` free of rank
one lifts `1 ⊗ x` and `1 ⊗ x` survives in `K ⊗_A κ(p)`, then the coordinate of `z` becomes a unit
after inverting some `a' ∉ p`. -/
private theorem exists_not_mem_isUnit_coord {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]
    {g : A} (hg : g ∉ p) {K : CochainComplex (ModuleCat.{u} A) ℤ}
    {P : CochainComplex (ModuleCat.{u} (Localization.Away g)) ℤ}
    (u : P ⟶ extendScalarsComplex (algebraMap A (Localization.Away g)) K) {r : ℕ} (hr : r = 1)
    (e : P.X 0 ≅ ModuleCat.of (Localization.Away g) (Fin r → Localization.Away g)) (z : P.X 0)
    (x : K.X 0) (hz : u.f 0 z = (1 : Localization.Away g) ⊗ₜ[A,algebraMap A _] x)
    (hx : (1 : p.ResidueField) ⊗ₜ[A,algebraMap A p.ResidueField] x ≠ 0) :
    ∃ a' : A, a' ∉ p ∧ ∀ k, IsUnit
      (IsLocalization.Away.awayToAwayRight (P := Localization.Away (g * a')) g a' (e.hom z k)) := by
  have hgκ : IsUnit (algebraMap A p.ResidueField g) := by
    refine isUnit_iff_ne_zero.2 fun h => hg ?_
    rwa [← Ideal.ker_algebraMap_residueField p]
  let χ : Localization.Away g →+* p.ResidueField := IsLocalization.Away.lift g hgκ
  subst hr
  obtain ⟨a', ha'p, hβa⟩ := exists_not_mem_isUnit_awayToAwayRight p hgκ (e.hom z 0) fun h0 =>
    coord_ne_zero_of_one_tmul_ne_zero _ χ u e z x hz
      (one_tmul_ne_zero_congr (IsLocalization.Away.lift_comp g hgκ) _ hx)
      (funext fun k => by rwa [Subsingleton.elim k 0])
  exact ⟨a', ha'p, fun k => by rwa [Subsingleton.elim k 0]⟩

/-- If the differential `P^i ⟶ P^j` of a complex of finite free modules is given by a matrix
that vanishes along `ψ`, then the corresponding differential of `P ⊗ B` vanishes. -/
private theorem extendScalarsComplex_d_eq_zero_of_matrix {R B : Type u} [CommRing R] [CommRing B]
    (ψ : R →+* B) (P : CochainComplex (ModuleCat.{u} R) ℤ) {i j : ℤ} {r β : ℕ}
    (e₀ : P.X i ≅ ModuleCat.of R (Fin r → R)) (e₁ : P.X j ≅ ModuleCat.of R (Fin β → R))
    (M : Matrix (Fin β) (Fin r) R) (hM : P.d i j = e₀.hom ≫ ModuleCat.ofHom M.mulVecLin ≫ e₁.inv)
    (hM0 : M.map ψ = 0) : (extendScalarsComplex ψ P).d i j = 0 := by
  ext x
  apply (termEquiv ψ e₁).injective
  refine (termEquiv_map ψ e₀ e₁ (P.d i j) M hM x).trans ?_
  rw [hM0, Matrix.zero_mulVec]
  exact (termEquiv ψ e₁).map_zero.symm

/-- If a degree-`0` cocycle `z` of a complex with `P⁰` free of rank one and `P¹` finite free has
unit coordinates along `ψ`, then the first differential of `P ⊗ B` vanishes. -/
private theorem extendScalarsComplex_d_zero_one_eq_zero_of_isUnit {R B : Type u} [CommRing R]
    [CommRing B] (P : CochainComplex (ModuleCat.{u} R) ℤ) {r β : ℕ} (hr : r = 1)
    (e₀ : P.X 0 ≅ ModuleCat.of R (Fin r → R)) (e₁ : P.X 1 ≅ ModuleCat.of R (Fin β → R))
    {z : P.X 0} (hz : (P.d 0 1).hom z = 0) (ψ : R →+* B) (hu : ∀ k, IsUnit (ψ (e₀.hom z k))) :
    (extendScalarsComplex ψ P).d 0 1 = 0 := by
  let L : (Fin r → R) →ₗ[R] (Fin β → R) := e₁.hom.hom ∘ₗ (P.d 0 1).hom ∘ₗ e₀.inv.hom
  let M := LinearMap.toMatrix' L
  have hM : P.d 0 1 = e₀.hom ≫ ModuleCat.ofHom M.mulVecLin ≫ e₁.inv := by
    ext x
    simp [M, L]
  have hL : L (e₀.hom z) = 0 := by simp [L, hz]
  exact extendScalarsComplex_d_eq_zero_of_matrix ψ P e₀ e₁ M hM
    (matrix_map_eq_zero_of_mulVec hr M _ ((LinearMap.toMatrix'_mulVec L _).trans hL) ψ hu)

/-- A quasi-isomorphism `P ⟶ K` from a complex `P ≅ P⁰[0] ⊕ T` with `P⁰ ≅ R` gives
`K ≅ R[0] ⊕ T` in `D(R)`. -/
private theorem nonempty_Q_obj_iso_single_biprod_of_quasiIso {R : Type u} [CommRing R]
    {P K T : CochainComplex (ModuleCat.{u} R) ℤ} (u : P ⟶ K) [QuasiIso u]
    (eT : P ≅ (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj (P.X 0) ⊞ T)
    (e₀ : P.X 0 ≅ ModuleCat.of R R) :
    Nonempty (DerivedCategory.Q.obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R) ⊞
        DerivedCategory.Q.obj T) := by
  have : PreservesBinaryBiproducts (DerivedCategory.Q (C := ModuleCat.{u} R)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have : IsIso (DerivedCategory.Q.map u) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  exact ⟨(asIso (DerivedCategory.Q.map u)).symm ≪≫ DerivedCategory.Q.mapIso eT ≪≫
    DerivedCategory.Q.mapBiprod _ _ ≪≫
    biprod.mapIso (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app _).symm ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso e₀) (Iso.refl _)⟩

omit [Fintype I] [LinearOrder I] in
include hflat hUaff in
/-- If a model `u : P ⟶ C ⊗_A R` of the Čech model of `𝒪_X` has vanishing first differential and
`P⁰` free of rank one, then over every `R`-algebra `B` the global sections of the pullback of
`𝒪_X` to the base change of `X` are free of rank one. -/
private theorem nonempty_sections_pullback_linearEquiv_of_d_zero [Finite I] {R : Type u}
    [CommRing R] (α : A →+* R) {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (u : P ⟶ extendScalarsComplex α (baseAlternatingCechComplex f U hU (Scheme.unitModule X)))
    [QuasiIso u] [∀ n : ℤ, Module.Flat R (P.X n)] (b : ℤ) [P.IsStrictlyLE b]
    (hP : IsZero (P.X (-1))) (hd : P.d 0 1 = 0) {r : ℕ} [Unique (Fin r)]
    (e : P.X 0 ≅ ModuleCat.of R (Fin r → R)) {B : Type u} [CommRing B] (ψ : R →+* B)
    {X' : Scheme.{u}} {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X}
    (hsq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (ψ.comp α)))) :
    letI := Stacks.Cech.sectionsModule f' ((Scheme.Modules.pullback g').obj (Scheme.unitModule X)) ⊤
    Nonempty (Γ((Scheme.Modules.pullback g').obj (Scheme.unitModule X), ⊤) ≃ₗ[B] B) := by
  have := Fintype.ofFinite I
  have := quasiIso_kernelChainComparison α (Scheme.unitModule X) U hU hUaff u hflat b ψ hsq
  have hbij := bijective_kerRestrict
    (kernelChainComparison α (Scheme.unitModule X) U hU hUaff u ψ hsq)
    (d_neg_one_zero_extendScalarsComplex hP ψ) (d_neg_one_zero_baseAlternatingCechComplex _ _ _ _)
  have htop : LinearMap.ker ((extendScalarsComplex ψ P).d 0 1).hom = ⊤ := by
    have : (extendScalarsComplex ψ P).d 0 1 = 0 := by
      change (ModuleCat.extendScalars.{u, u, u} ψ).map (P.d 0 1) = 0
      rw [hd, Functor.map_zero]
    rw [this]
    exact LinearMap.ker_zero
  let := Stacks.Cech.sectionsModule f' ((Scheme.Modules.pullback g').obj (Scheme.unitModule X)) ⊤
  exact ⟨(sectionsEquivKer f' (fun j => g' ⁻¹ᵁ U j) (top_eq_iSup_preimage g' U hU)
      ((Scheme.Modules.pullback g').obj (Scheme.unitModule X))).trans
    ((LinearEquiv.ofBijective _ hbij).symm.trans
      ((LinearEquiv.ofTop _ htop).trans
        ((termEquiv ψ e).trans (LinearEquiv.funUnique (Fin r) B B))))⟩

omit [Fintype I] [LinearOrder I] in
include hflat hUaff in
/-- **The Čech model of `RΓ(X, 𝒪_X)` splits off the base ring near a point.** -/
theorem exists_away_unitSplitting [Finite I]
    (hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent
      (DerivedCategory.Q.obj (baseAlternatingCechComplex f U hU (Scheme.unitModule X))))
    (p : Ideal A) [p.IsPrime]
    (hrank : Module.finrank p.ResidueField ((extendScalarsComplex (algebraMap A p.ResidueField)
      (baseAlternatingCechComplex f U hU (Scheme.unitModule X))).homology 0) = 1)
    (hne : (1 : p.ResidueField) ⊗ₜ[A,algebraMap A p.ResidueField] unitCochain f U hU ≠ 0) :
    ∃ h : A, h ∉ p ∧
      (∀ {B : Type u} [CommRing B] (φ : A →+* B), IsUnit (φ h) →
        ∀ {X' : Scheme.{u}} {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X}
          (_ : IsPullback g' f' f (Spec.map (CommRingCat.ofHom φ))),
          letI := Stacks.Cech.sectionsModule f'
            ((Scheme.Modules.pullback g').obj (Scheme.unitModule X)) ⊤
          Nonempty (Γ((Scheme.Modules.pullback g').obj (Scheme.unitModule X), ⊤) ≃ₗ[B] B)) ∧
      ∃ (T : CochainComplex (ModuleCat.{u} (Localization.Away h)) ℤ) (b : ℤ),
        T.IsStrictlyGE 1 ∧ T.IsStrictlyLE b ∧
          (∀ i, Module.Free (Localization.Away h) (T.X i)) ∧
          (∀ i, Module.Finite (Localization.Away h) (T.X i)) ∧
          Nonempty (DerivedCategory.Q.obj (extendScalarsComplex
              (algebraMap A (Localization.Away h))
              (baseAlternatingCechComplex f U hU (Scheme.unitModule X))) ≅
            (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away h)) 0).obj
                (ModuleCat.of (Localization.Away h) (Localization.Away h)) ⊞
              DerivedCategory.Q.obj T) := by
  classical
  have := Fintype.ofFinite I
  let F := Scheme.unitModule X
  let C := baseAlternatingCechComplex f U hU F
  let κ := p.ResidueField
  let H : ℤ → ModuleCat.{u} κ := fun i => (DerivedCategory.homologyFunctor (ModuleCat.{u} κ) i).obj
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A κ)).functor.obj (DerivedCategory.Q.obj C))
  let eH : ∀ i, H i ≅ (extendScalarsComplex (algebraMap A κ) C).homology i := fun i =>
    (DerivedCategory.homologyFunctor (ModuleCat.{u} κ) i).mapIso
      (totalDerivedExtensionScalarsModelIso f U hU F (algebraMap A κ) hUaff hflat) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} κ) i).app _
  have hvan : ∀ i : ℤ, i < 0 → IsZero (H i) := fun i hi =>
    IsZero.of_iso (ShortComplex.isZero_homology_of_isZero_X₂ _
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap A κ)).map_isZero
        (isZero_baseAlternatingCechComplex_X_of_neg f U hU F i hi))) (eH i)
  obtain ⟨g, hg, -, P, b, hPge, hPle, hPX, ⟨eP⟩⟩ :=
    StacksDraft.Perfect.exists_away_bounded_free_complex_representing_of_fibre_vanishing_below
      p (DerivedCategory.Q.obj C) hpc ⟨0, inferInstance⟩ 0 hvan
  let Ag := Localization.Away g
  let α := algebraMap A Ag
  let r := Module.finrank κ (H 0)
  let β := Module.finrank κ (H 1)
  have hr : r = 1 := (eH 0).toLinearEquiv.finrank_eq.trans hrank
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
    (eP.hom ≫ (totalDerivedExtensionScalarsModelIso f U hU F α hUaff hflat).hom)
  have : QuasiIso u := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 (by
    rw [hu]
    infer_instance)
  let ei : ∀ i : ℤ, P.X i ≅ ModuleCat.of Ag (Fin (Module.finrank κ (H i)) → Ag) := fun i =>
    (hPX i).some ≪≫ ULift.moduleEquiv.toModuleIso
  let e₀ : P.X 0 ≅ ModuleCat.of Ag (Fin r → Ag) := ei 0
  let e₁ : P.X 1 ≅ ModuleCat.of Ag (Fin β → Ag) := ei 1
  have : ∀ n : ℤ, Module.Flat Ag ((extendScalarsComplex α C).X n) := fun n => by
    have : Module.Flat A (C.X n) := flat_baseAlternatingCechComplex_X f U hU F hUaff hflat n
    let : Algebra A Ag := α.toAlgebra
    exact Module.Flat.baseChange A Ag (C.X n)
  have hPd : P.d (-1) 0 = 0 := (P.isZero_of_isStrictlyGE 0 (-1)).eq_of_src _ _
  have hCd : (extendScalarsComplex α C).d (-1) 0 = 0 :=
    ((ModuleCat.extendScalars.{u, u, u} α).map_isZero
      (isZero_baseAlternatingCechComplex_X_of_neg f U hU F (-1) (by omega))).eq_of_src _ _
  let x₀ : (extendScalarsComplex α C).X 0 := (1 : Ag) ⊗ₜ[A, α] unitCochain f U hU
  have hunit_mem : x₀ ∈ LinearMap.ker ((extendScalarsComplex α C).d 0 1).hom := by
    refine LinearMap.mem_ker.2 ?_
    change (ModuleCat.extendScalars.{u, u, u} α).map (C.d 0 1) ((1 : Ag) ⊗ₜ[A, α] _) = 0
    rw [ModuleCat.ExtendScalars.map_tmul, LinearMap.mem_ker.1 (unitCochain_mem_ker f U hU),
      TensorProduct.tmul_zero]
    rfl
  obtain ⟨z, hz⟩ := (bijective_kerRestrict u hPd hCd).2 ⟨_, hunit_mem⟩
  obtain ⟨a', ha'p, hβa⟩ :=
    exists_not_mem_isUnit_coord p hg u hr e₀ z.1 _ (congrArg Subtype.val hz) hne
  let h := g * a'
  have hh : h ∉ p := fun hm => (‹p.IsPrime›.mem_or_mem hm).elim hg ha'p
  let Ah := Localization.Away h
  let β' : Ag →+* Ah := IsLocalization.Away.awayToAwayRight g a'
  have hβ' : β'.comp α = algebraMap A Ah :=
    RingHom.ext fun x => IsLocalization.Away.awayToAwayRight_eq g a' x
  let Ph := extendScalarsComplex β' P
  have hd0 : Ph.d 0 1 = 0 :=
    extendScalarsComplex_d_zero_one_eq_zero_of_isUnit P hr e₀ e₁ z.2 β' hβa
  have hPhneg : ∀ i : ℤ, i < 0 → IsZero (Ph.X i) := fun i hi =>
    (ModuleCat.extendScalars.{u, u, u} β').map_isZero (P.isZero_of_isStrictlyGE 0 i (by omega))
  have hPhle : ∀ i : ℤ, b < i → IsZero (Ph.X i) := fun i hi =>
    (ModuleCat.extendScalars.{u, u, u} β').map_isZero (P.isZero_of_isStrictlyLE b i hi)
  have hPhfree : ∀ i : ℤ, Module.Free Ah (Ph.X i) := fun i =>
    Module.Free.of_equiv (termEquiv β' (ei i)).symm
  have hPhfin : ∀ i : ℤ, Module.Finite Ah (Ph.X i) := fun i =>
    Module.Finite.equiv (termEquiv β' (ei i)).symm
  obtain ⟨T, hT1, hTb, hTfree, hTfin, ⟨eT⟩⟩ :=
    exists_iso_single_biprod_free_of_d_zero Ph b hPhneg hPhle hd0 hPhfree hPhfin
  have : Unique (Fin r) := (finCongr hr).unique
  have : ∀ n : ℤ, Module.Flat Ah (Ph.X n) := fun n =>
    @Module.Flat.of_free _ _ _ _ _ (hPhfree n)
  have : Ph.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff Ph b).2 hPhle
  let uh :=
    ((ModuleCat.extendScalars.{u, u, u} β').mapHomologicalComplex (ComplexShape.up ℤ)).map u
  have : QuasiIso uh :=
    StacksDraft.PseudoCoherence.quasiIso_extendScalars_map_of_flat β' b (Fintype.card I : ℤ) u
  let e2 := (extendScalarsComplexCompIso α β').app C ≪≫ extendScalarsComplexCongr hβ' C
  let u' : Ph ⟶ extendScalarsComplex (algebraMap A Ah) C := uh ≫ e2.hom
  refine ⟨h, hh, ?_, T, b, hT1, hTb, hTfree, hTfin,
    nonempty_Q_obj_iso_single_biprod_of_quasiIso u' eT
      (termEquiv β' e₀ ≪≫ₗ LinearEquiv.funUnique (Fin r) Ah Ah).toModuleIso⟩
  intro B _ φ hφ X' f' g' hsq
  exact nonempty_sections_pullback_linearEquiv_of_d_zero f hflat U hU hUaff (algebraMap A Ah) u' b
    (hPhneg (-1) (by omega)) hd0 (termEquiv β' e₀).toModuleIso (IsLocalization.Away.lift h hφ)
    (by rwa [IsLocalization.Away.lift_comp h hφ])

end Core

section Fibre

open scoped ChangeOfRings TensorProduct

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsSeparated f]
  {I : Type u} [Finite I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i))

/-- `g^* 𝒪_X ≅ 𝒪_{X'}` on global sections is linear over the base ring of `X'`. -/
def pullbackUnitSectionsEquiv {B : Type u} [CommRing B] {X' : Scheme.{u}} (f' : X' ⟶ Spec (.of B))
    (g' : X' ⟶ X) :
    letI := Stacks.Cech.sectionsModule f' ((Scheme.Modules.pullback g').obj (Scheme.unitModule X)) ⊤
    letI := Stacks.Cech.sectionsModule f' (Scheme.unitModule X') ⊤
    Γ((Scheme.Modules.pullback g').obj (Scheme.unitModule X), ⊤) ≃ₗ[B]
      Γ(Scheme.unitModule X', ⊤) :=
  letI := Stacks.Cech.sectionsModule f' ((Scheme.Modules.pullback g').obj (Scheme.unitModule X)) ⊤
  letI := Stacks.Cech.sectionsModule f' (Scheme.unitModule X') ⊤
  { toFun := (Scheme.Modules.pullbackUnitIso g').hom.app ⊤
    invFun := (Scheme.Modules.pullbackUnitIso g').inv.app ⊤
    map_add' := map_add _
    map_smul' := fun c x => Scheme.Modules.Hom.app_smul _ _ _
    left_inv := fun x => by
      change ((Scheme.Modules.pullbackUnitIso g').hom ≫ (Scheme.Modules.pullbackUnitIso g').inv).app
        ⊤ x = x
      rw [Iso.hom_inv_id]
      rfl
    right_inv := fun x => by
      change ((Scheme.Modules.pullbackUnitIso g').inv ≫ (Scheme.Modules.pullbackUnitIso g').hom).app
        ⊤ x = x
      rw [Iso.inv_hom_id]
      rfl }

/-- A bijective structure map identifies the global functions with the base ring, linearly. -/
def unitSectionsEquivOfBijective {B : Type u} [CommRing B] {X' : Scheme.{u}}
    (f' : X' ⟶ Spec (.of B)) (hb : Function.Bijective (Stacks.Cech.baseRingHom f' ⊤)) :
    letI := Stacks.Cech.sectionsModule f' (Scheme.unitModule X') ⊤
    B ≃ₗ[B] Γ(Scheme.unitModule X', ⊤) :=
  letI := Stacks.Cech.sectionsModule f' (Scheme.unitModule X') ⊤
  LinearEquiv.ofBijective
    (({ toFun := fun c => show Γ(Scheme.unitModule X', ⊤) from Stacks.Cech.baseRingHom f' ⊤ c
        map_add' := fun c d => map_add _ c d
        map_smul' := fun c d => by
          change (Stacks.Cech.baseRingHom f' ⊤) (c * d) =
            (Stacks.Cech.baseRingHom f' ⊤ c) * (Stacks.Cech.baseRingHom f' ⊤ d)
          exact map_mul _ c d } : B →ₗ[B] Γ(Scheme.unitModule X', ⊤))) hb

include hUaff in
/-- **The degree-zero cohomology of the derived fibre is one-dimensional** when the fibre has only
constant functions. -/
theorem finrank_homology_zero_extendScalars_residueField (p : Ideal A) [p.IsPrime]
    {X' : Scheme.{u}} {f' : X' ⟶ Spec (.of p.ResidueField)} {g' : X' ⟶ X}
    (hsq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    (hb : Function.Bijective (Stacks.Cech.baseRingHom f' ⊤)) :
    Module.finrank p.ResidueField ((extendScalarsComplex (algebraMap A p.ResidueField)
      (baseAlternatingCechComplex f U hU (Scheme.unitModule X))).homology 0) = 1 := by
  have := Fintype.ofFinite I
  let := Stacks.Cech.sectionsModule f' ((Scheme.Modules.pullback g').obj (Scheme.unitModule X)) ⊤
  let := Stacks.Cech.sectionsModule f' (Scheme.unitModule X') ⊤
  let E := baseAlternatingCechComplexBaseChangeIso (algebraMap A p.ResidueField) hsq
    (Scheme.unitModule X) U hU hUaff
  let e := ((HomologicalComplex.homologyFunctor _ _ 0).mapIso E ≪≫
    homologyZeroIsoKer _ (d_neg_one_zero_baseAlternatingCechComplex _ _ _ _)).toLinearEquiv ≪≫ₗ
    (sectionsEquivKer f' (fun j => g' ⁻¹ᵁ U j) (top_eq_iSup_preimage g' U hU)
      ((Scheme.Modules.pullback g').obj (Scheme.unitModule X))).symm ≪≫ₗ
    pullbackUnitSectionsEquiv f' g' ≪≫ₗ (unitSectionsEquivOfBijective f' hb).symm
  exact e.finrank_eq.trans (Module.finrank_self _)

include hUaff in
/-- **The cochain of `1` survives in the derived fibre** when the fibre is nonempty, which it is
when it has only constant functions. -/
theorem one_tmul_unitCochain_ne_zero (p : Ideal A) [p.IsPrime]
    {X' : Scheme.{u}} {f' : X' ⟶ Spec (.of p.ResidueField)} {g' : X' ⟶ X}
    (hsq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    (hb : Function.Bijective (Stacks.Cech.baseRingHom f' ⊤)) :
    (1 : p.ResidueField) ⊗ₜ[A, algebraMap A p.ResidueField] unitCochain f U hU ≠ 0 := by
  intro h0
  have h1 := baseChangeIso_sectionsToModel (algebraMap A p.ResidueField) hsq
    (Scheme.unitModule X) U hU hUaff (oneSection X)
  have := Fintype.ofFinite I
  have h2 := congrArg (ConcreteCategory.hom ((baseAlternatingCechComplexBaseChangeIso
    (algebraMap A p.ResidueField) hsq (Scheme.unitModule X) U hU hUaff).hom.f 0)) h0
  have h3 := h1.symm.trans (h2.trans (LinearMap.map_zero (ModuleCat.Hom.hom _)))
  have h4 : pullbackSectionHom g' (Scheme.unitModule X) ⊤ ⊤ (by simp) (oneSection X) = 0 :=
    sectionsToModel_injective f' (fun j => g' ⁻¹ᵁ U j) (top_eq_iSup_preimage g' U hU)
      ((Scheme.Modules.pullback g').obj (Scheme.unitModule X)) (h3.trans (map_zero _).symm)
  have h5 := pullbackUnitIso_hom_app_pullbackSectionHom_one g'
  rw [h4, map_zero] at h5
  have h6 : Stacks.Cech.baseRingHom f' ⊤ 1 = Stacks.Cech.baseRingHom f' ⊤ 0 := by
    rw [map_one, map_zero]
    exact h5.symm
  exact one_ne_zero (hb.1 h6)

end Fibre

end Stacks.AlgebraicGeometry.ProperFlatFamilyCech

end
