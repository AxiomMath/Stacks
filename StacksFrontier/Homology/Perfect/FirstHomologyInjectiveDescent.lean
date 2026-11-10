module

public import StacksFrontier.Homology.Perfect.MinimalChainModel
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# A chain map injective on fibre `H¹`, between complexes with one-dimensional fibre `H⁰`

Let `A` be a ring, `p` a prime of `A` and `ψ : P ⟶ P'` a chain map of bounded complexes of finite
projective `A`-modules such that the derived fibres at `p` have no `H⁻¹`, have a one-dimensional
`H⁰`, and `H¹(ψ ⊗ κ(p))` is injective. This is the algebraic situation in the proof of
[Stacks, Tag 0BF1], where `P` and `P'` model `RΓ(X, L)` and `RΓ(X', L')`.

The conclusion is a finite family `c` of elements of `p` and an element `g ∉ p` with two
properties over every `A`-algebra `B` in which `g` is a unit:

* if `H⁰(P' ⊗ B)` is free of rank one, then every `c k` vanishes in `B`;
* if every `c k` vanishes in `B`, then `P ⊗ B` has a degree-zero cycle whose image in every field
  `K` over `B` with kernel `p` is not a boundary.

## Main results

* `StacksDraft.Perfect.exists_minimal_model`: a bounded complex of finite projective modules is,
  over a principal localization, homotopy equivalent to a complex of finite free modules whose
  ranks are the fibre dimensions and whose differentials vanish on the fibre.
* `StacksDraft.Perfect.exists_vanishing_family_of_mono_homologyMap_one`: the family `c` and the
  element `g` above.

## References

* [Stacks Project, Tag 0BF1](https://stacks.math.columbia.edu/tag/0BF1)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct

universe u

namespace StacksDraft.Perfect

variable {A : Type u} [CommRing A]

/-- **A free module of rank one, after extension of scalars, is identified with the new ring.** -/
noncomputable def baseChangeRankOneIso {R B : Type u} [CommRing R] [CommRing B] (ψ : R →+* B)
    {M : ModuleCat.{u} R} (e : M ≅ ModuleCat.of R (ULift.{u} (Fin 1 → R))) :
    (ModuleCat.extendScalars.{u, u, u} ψ).obj M ≅ ModuleCat.of B B :=
  (ModuleCat.extendScalars.{u, u, u} ψ).mapIso e ≪≫
    (extendScalars_standard_free_iso.{u, u} ψ 1).some ≪≫
    (ULift.moduleEquiv.trans (LinearEquiv.funUnique (Fin 1) B B)).toModuleIso

/-- **A differential out of a free module of rank one, which kills a cycle lying outside
`𝔪 · M` for every maximal ideal `𝔪`, vanishes.** The cycle is a unit multiple of a generator. -/
theorem eq_zero_of_apply_eq_zero_of_notMem_smul_top {R B : Type u} [CommRing R] [CommRing B]
    (ψ : R →+* B) {M : ModuleCat.{u} R} (e : M ≅ ModuleCat.of R (ULift.{u} (Fin 1 → R)))
    {N : ModuleCat.{u} B} (d : (ModuleCat.extendScalars.{u, u, u} ψ).obj M ⟶ N)
    (v : (ModuleCat.extendScalars.{u, u, u} ψ).obj M) (hv : d v = 0)
    (hnot : ∀ m : Ideal B, m.IsMaximal →
      v ∉ m • (⊤ : Submodule B ((ModuleCat.extendScalars.{u, u, u} ψ).obj M))) :
    d = 0 := by
  let ε := baseChangeRankOneIso ψ e
  have hy : ∀ y, y = (ε.hom y) • ε.inv 1 := fun y => by
    conv_lhs => rw [← ε.hom_inv_id_apply y]
    rw [← map_smul, smul_eq_mul, mul_one]
  have ht : IsUnit (ε.hom v) := by
    by_contra hnu
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {ε.hom v})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    apply hnot m hm
    rw [hy v]
    exact Submodule.smul_mem_smul (hle (Ideal.subset_span rfl)) trivial
  obtain ⟨u, hu⟩ := ht
  have h1 : d (ε.inv 1) = 0 := by
    have h2 : d v = (ε.hom v) • d (ε.inv 1) := by
      conv_lhs => rw [hy v]
      rw [map_smul]
    rw [hv, ← hu] at h2
    have h3 := congrArg (fun z => (↑u⁻¹ : B) • z) h2
    simp only [smul_zero, smul_smul, Units.inv_mul, one_smul] at h3
    exact h3.symm
  refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  change d y = 0
  rw [hy y, map_smul, h1, smul_zero]

section ExtendScalarsElements

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) {M N : ModuleCat.{u} R}

/-- The elementary tensor `1 ⊗ m` of an extension of scalars, as an element of the module. -/
def etm1 (m : M) : (ModuleCat.extendScalars.{u, u, u} φ).obj M :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).unit.app M m

/-- The elementary tensor `s ⊗ m` of an extension of scalars, as an element of the module. -/
def etm (s : S) (m : M) : (ModuleCat.extendScalars.{u, u, u} φ).obj M := s • etm1 φ m

/-- The element `etm φ s m` is the pure tensor `s ⊗ₜ m`. -/
theorem etm_eq_tmul (s : S) (m : M) : etm φ s m = s ⊗ₜ[R, φ] m := by
  rw [etm, etm1, ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  exact (ModuleCat.ExtendScalars.smul_tmul (f := φ) (M := M) s 1 m).trans (by rw [mul_one])

/-- Scalar multiplication on elementary tensors: `s • (s' ⊗ m) = (s * s') ⊗ m`. -/
theorem smul_etm (s s' : S) (m : M) : s • etm φ s' m = etm φ (s * s') m := by
  rw [etm, etm, smul_smul]

/-- `1 ⊗ (m + m') = 1 ⊗ m + 1 ⊗ m'`. -/
theorem etm1_add (m m' : M) : etm1 φ (m + m') = etm1 φ m + etm1 φ m' :=
  map_add _ _ _

/-- `s ⊗ (m + m') = s ⊗ m + s ⊗ m'`. -/
theorem etm_add_right (s : S) (m m' : M) : etm φ s (m + m') = etm φ s m + etm φ s m' := by
  rw [etm, etm, etm, etm1_add, smul_add]

/-- `(s + s') ⊗ m = s ⊗ m + s' ⊗ m`. -/
theorem etm_add_left (s s' : S) (m : M) : etm φ (s + s') m = etm φ s m + etm φ s' m := by
  rw [etm, etm, etm, add_smul]

/-- `s ⊗ 0 = 0`. -/
@[simp] theorem etm_zero_right (s : S) : etm φ s (0 : M) = 0 := by
  rw [etm, etm1, map_zero]
  exact smul_zero (A := (ModuleCat.extendScalars.{u, u, u} φ).obj M) s

/-- `0 ⊗ m = 0`. -/
@[simp] theorem etm_zero_left (m : M) : etm φ (0 : S) m = 0 := by
  rw [etm, zero_smul]

/-- `1 ⊗ (r • m) = φ r • (1 ⊗ m)`. -/
theorem etm1_smul (r : R) (m : M) : etm1 φ (r • m) = φ r • etm1 φ m :=
  map_smul ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).unit.app M).hom r m

/-- `s ⊗ (r • m) = (s * φ r) ⊗ m`. -/
theorem etm_smul_right (s : S) (r : R) (m : M) : etm φ s (r • m) = etm φ (s * φ r) m := by
  rw [etm, etm, etm1_smul, smul_smul]

/-- The extension of scalars of `g` sends `1 ⊗ m` to `1 ⊗ g m`. -/
theorem map_etm1 (g : M ⟶ N) (m : M) :
    (ModuleCat.extendScalars.{u, u, u} φ).map g (etm1 φ m) = etm1 φ (g m) :=
  rfl

/-- The extension of scalars of `g` sends `s ⊗ m` to `s ⊗ g m`. -/
theorem map_etm (g : M ⟶ N) (s : S) (m : M) :
    (ModuleCat.extendScalars.{u, u, u} φ).map g (etm φ s m) = etm φ s (g m) := by
  rw [etm, etm, map_smul, map_etm1]

/-- Induction on the elements of an extension of scalars. -/
theorem extendScalars_induction {P : (ModuleCat.extendScalars.{u, u, u} φ).obj M → Prop}
    (hadd : ∀ x y, P x → P y → P (x + y))
    (htmul : ∀ (s : S) (m : M), P (etm φ s m))
    (x : (ModuleCat.extendScalars.{u, u, u} φ).obj M) : P x := by
  induction x using TensorProduct.inductionOn with
  | tmul s m => exact etm_eq_tmul φ s m ▸ htmul s m
  | add x y hx hy => exact hadd x y hx hy

/-- Two linear maps out of an extension of scalars agree as soon as they agree on the
elementary tensors `1 ⊗ m`. -/
theorem extendScalars_ext {T : Type u} [AddCommGroup T] [Module S T]
    {α β : (ModuleCat.extendScalars.{u, u, u} φ).obj M →ₗ[S] T}
    (h : ∀ m : M, α (etm φ 1 m) = β (etm φ 1 m)) : α = β := by
  ext x
  refine extendScalars_induction φ (P := fun x => α x = β x)
    (fun x y hx hy => by rw [map_add, map_add, hx, hy]) (fun s m => ?_) x
  rw [show etm φ s m = s • etm φ 1 m by rw [smul_etm, mul_one], map_smul, map_smul, h m]

end ExtendScalarsElements

/-! ### Fibre dimensions do not depend on the field -/

/-- **The fibre dimensions of a complex do not depend on the field representing the point.** For
a ring map `χ : A → K` to a field with kernel `p`, the dimension of `Hⁱ(P ⊗_A K)` over `K` is the
dimension of `Hⁱ(P ⊗_A κ(p))` over `κ(p)`: extension of scalars along the field extension
`κ(p) → K` is exact and preserves dimensions. -/
theorem finrank_homology_baseChange_eq_residueField {K : Type u} [Field K] (χ : A →+* K)
    [(RingHom.ker χ).IsPrime] (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    Module.finrank K ((baseChangeComplex χ P).homology i) =
      Module.finrank (RingHom.ker χ).ResidueField
        ((baseChangeComplex (algebraMap A (RingHom.ker χ).ResidueField) P).homology i) := by
  classical
  let q := RingHom.ker χ
  let κ := q.ResidueField
  have hu : q.primeCompl ≤ (IsUnit.submonoid K).comap χ := fun x hx => by
    have hx' : χ x ≠ 0 := fun h => hx (by simpa [q, RingHom.mem_ker] using h)
    exact (isUnit_iff_ne_zero.mpr hx' : IsUnit (χ x))
  let ι : κ →+* K := Ideal.ResidueField.lift q χ le_rfl hu
  have hι : ι.comp (algebraMap A κ) = χ := by
    ext r
    exact Ideal.ResidueField.lift_algebraMap q χ le_rfl hu r
  have hflat : ι.Flat := by
    let := ι.toAlgebra
    change Module.Flat κ K
    infer_instance
  have : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} ι) :=
    extendScalars_preservesFiniteLimits_of_flat' ι hflat
  have : Limits.PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} ι) :=
    have : Limits.PreservesColimitsOfSize.{0, 0} (ModuleCat.extendScalars.{u, u, u} ι) :=
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} ι).leftAdjoint_preservesColimits
    Limits.PreservesColimitsOfSize.preservesFiniteColimits _
  let W := (baseChangeComplex (algebraMap A κ) P).homology i
  have e1 : (baseChangeComplex χ P).homology i ≅ (ModuleCat.extendScalars.{u, u, u} ι).obj W := by
    refine (HomologicalComplex.homologyFunctor _ _ i).mapIso ?_ ≪≫
      (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
        (ModuleCat.extendScalars.{u, u, u} ι) (ComplexShape.up ℤ) i).app _
    refine eqToIso ?_ ≪≫ (baseChangeComplexCompIso (algebraMap A κ) ι P).symm
    rw [hι]
  rw [e1.toLinearEquiv.finrank_eq]
  let : Algebra κ K := ι.toAlgebra
  exact Module.finrank_baseChange

/-! ### Lifting through a quasi-isomorphism -/

/-- **A chain map out of a bounded above complex of projectives lifts, up to homotopy, through a
quasi-isomorphism.** -/
theorem exists_homotopy_comp_quasiIso {R : Type u} [CommRing R]
    {M M' C' : CochainComplex (ModuleCat.{u} R) ℤ} (b : ℤ) [M.IsStrictlyLE b]
    [∀ i, Projective (M.X i)] (u' : M' ⟶ C') [QuasiIso u'] (x : M ⟶ C') :
    ∃ φ : M ⟶ M', Nonempty (Homotopy (φ ≫ u') x) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  have : M.IsKProjective := CochainComplex.isKProjective_of_projective M b
  have hiso : IsIso (DerivedCategory.Q.map u') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  let e := DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)
  have key : ∀ {N : CochainComplex (ModuleCat.{u} R) ℤ} (f : M ⟶ N),
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f) =
        e.hom.app M ≫ DerivedCategory.Q.map f ≫ e.inv.app N := by
    intro N f
    rw [← DerivedCategory.quotientCompQhIso_hom_naturality_assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  obtain ⟨φ', hφ'⟩ := (CochainComplex.IsKProjective.Qh_map_bijective M
    ((HomotopyCategory.quotient _ _).obj M')).surjective
      (e.hom.app M ≫ (DerivedCategory.Q.map x ≫ inv (DerivedCategory.Q.map u')) ≫ e.inv.app M')
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective φ'
  refine ⟨φ, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (CochainComplex.IsKProjective.Qh_map_bijective M
    ((HomotopyCategory.quotient _ _).obj C')).injective
  rw [key, key, Functor.map_comp]
  rw [key] at hφ'
  have h2 : DerivedCategory.Q.map φ = DerivedCategory.Q.map x ≫ inv (DerivedCategory.Q.map u') := by
    have := congrArg (fun z => e.inv.app M ≫ z ≫ e.hom.app M') hφ'
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
      Category.comp_id] using this
  rw [h2, Category.assoc]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]

/-! ### Minimal models with prescribed fibre cohomology in low degrees -/

/-- The dimension of the standard free module of rank `n` over a field. -/
theorem finrank_ulift_fin_fun {K : Type u} [Field K] (n : ℕ) :
    Module.finrank K (ULift.{u} (Fin n → K)) = n := by
  rw [ULift.moduleEquiv.finrank_eq, Module.finrank_fin_fun]

/-- **Minimal model of a perfect complex at a field-valued point.** Let `P` be a bounded complex of
finite projective `A`-modules and `χ₀ : A → K` a ring map to a field. Then there is `f` with
`χ₀ f ≠ 0` such that over every `A`-algebra `R` in which `f` is a unit and every `χ : R → K`
compatible with `χ₀`, the complex `P ⊗_A R` is homotopy equivalent to a bounded complex `Q` of
finite free `R`-modules whose term in degree `i` has rank `dim_K Hⁱ(P ⊗_A K)` and whose
differentials vanish after base change to `K`. -/
theorem exists_minimal_model {K : Type u} [Field K] (χ₀ : A →+* K) [(RingHom.ker χ₀).IsPrime]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hfin : ∀ i, Module.Finite A (P.X i)) (hproj : ∀ i, Module.Projective A (P.X i)) :
    ∃ f : A, χ₀ f ≠ 0 ∧ ∀ (R : Type u) [CommRing R] (φ : A →+* R) (χ : R →+* K),
      IsUnit (φ f) → χ.comp φ = χ₀ →
      ∃ Q : CochainComplex (ModuleCat.{u} R) ℤ,
        (∃ a' b' : ℤ, Q.IsStrictlyGE a' ∧ Q.IsStrictlyLE b') ∧
        (∀ i, Nonempty (Q.X i ≅ ModuleCat.of R
          (ULift.{u} (Fin (Module.finrank K ((baseChangeComplex χ₀ P).homology i)) → R)))) ∧
        (∀ i j, i + 1 = j → (baseChangeComplex χ Q).d i j = 0) ∧
        Nonempty (HomotopyEquiv Q (baseChangeComplex φ P)) := by
  classical
  obtain ⟨f, hf, hQ⟩ := exists_homotopyEquiv_free_model_of_isUnit (RingHom.ker χ₀) P a b hfin hproj
  refine ⟨f, fun h => hf (by simpa [RingHom.mem_ker] using h), fun R _ φ χ hφ hχ => ?_⟩
  obtain ⟨Q, hbd, hQX, ⟨e⟩⟩ := hQ R φ hφ
  have hr : ∀ i, Module.finrank (RingHom.ker χ₀).ResidueField
      ((baseChangeComplex (algebraMap A (RingHom.ker χ₀).ResidueField) P).homology i) =
      Module.finrank K ((baseChangeComplex χ₀ P).homology i) := fun i =>
    (finrank_homology_baseChange_eq_residueField χ₀ P i).symm
  refine ⟨Q, hbd, fun i => ?_, fun i j hij => ?_, ⟨e⟩⟩
  · rw [← hr i]
    exact hQX i
  · obtain ⟨eX⟩ := hQX i
    obtain ⟨eF⟩ := extendScalars_standard_free_iso.{u, u} χ (Module.finrank
      (RingHom.ker χ₀).ResidueField
      ((baseChangeComplex (algebraMap A (RingHom.ker χ₀).ResidueField) P).homology i))
    let eQ : (baseChangeComplex χ Q).X i ≅ ModuleCat.of K (ULift.{u} (Fin (Module.finrank
        (RingHom.ker χ₀).ResidueField
        ((baseChangeComplex (algebraMap A (RingHom.ker χ₀).ResidueField) P).homology i)) → K)) :=
      (ModuleCat.extendScalars.{u, u, u} χ).mapIso eX ≪≫ eF
    have : FiniteDimensional K ((baseChangeComplex χ Q).X i) :=
      Module.Finite.equiv eQ.toLinearEquiv.symm
    apply d_eq_zero_of_finrank_homology_eq _ i j hij
    rw [eQ.toLinearEquiv.finrank_eq, finrank_ulift_fin_fun, hr i]
    let G := ModuleCat.extendScalars.{u, u, u} χ
    have eH : (baseChangeComplex χ Q).homology i ≅ (baseChangeComplex χ₀ P).homology i :=
      (G.mapHomotopyEquiv e).toHomologyIso i ≪≫
        (HomologicalComplex.homologyFunctor _ _ i).mapIso
          (baseChangeComplexCompIso φ χ P ≪≫ eqToIso (by rw [hχ]))
    exact eH.toLinearEquiv.finrank_eq

/-! ### Coordinates after extension of scalars -/

section Coordinates

variable {R B : Type u} [CommRing R] [CommRing B] (lam : R →+* B)

/-- Evaluation of the extension of scalars of `R` itself: `b ⊗ r ↦ λ(r) b`. -/
def baseChangeSelf : (ModuleCat.extendScalars.{u, u, u} lam).obj (ModuleCat.of R R) ⟶
    ModuleCat.of B B :=
  ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} lam).homEquiv _ _).symm
    (ModuleCat.ofHom (Y := (ModuleCat.restrictScalars.{u} lam).obj (ModuleCat.of B B))
      { toFun := fun r => (lam r : B)
        map_add' := map_add lam
        map_smul' := fun r r' => by
          change lam (r * r') = lam r * lam r'
          exact map_mul lam r r' })

/-- `baseChangeSelf` sends `1 ⊗ r` to `λ(r)`. -/
theorem baseChangeSelf_etm1 (r : R) :
    baseChangeSelf lam (etm1 lam (show ModuleCat.of R R from r)) = lam r := by
  exact congrArg (fun φ => (ConcreteCategory.hom φ) r)
    (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} lam).homEquiv (ModuleCat.of R R)
      (ModuleCat.of B B)).apply_symm_apply
      (ModuleCat.ofHom (Y := (ModuleCat.restrictScalars.{u} lam).obj (ModuleCat.of B B))
      { toFun := fun r => (lam r : B)
        map_add' := map_add lam
        map_smul' := fun r r' => by
          change lam (r * r') = lam r * lam r'
          exact map_mul lam r r' }))

/-- `baseChangeSelf` sends `s ⊗ r` to `s * λ(r)`. -/
theorem baseChangeSelf_etm (s : B) (r : R) :
    baseChangeSelf lam (etm lam s (show ModuleCat.of R R from r)) = s * lam r := by
  rw [etm, map_smul, baseChangeSelf_etm1, smul_eq_mul]

/-- The `k`-th coordinate, read after extension of scalars, of a module identified with a
standard free module. -/
def baseChangeCoord {M : ModuleCat.{u} R} {n : ℕ} (e : M ≅ ModuleCat.of R (Fin n → R))
    (k : Fin n) : (ModuleCat.extendScalars.{u, u, u} lam).obj M ⟶ ModuleCat.of B B :=
  (ModuleCat.extendScalars.{u, u, u} lam).map (e.hom ≫ ModuleCat.ofHom (LinearMap.proj k)) ≫
    baseChangeSelf lam

/-- The `k`-th coordinate of `s ⊗ m` after extension of scalars is `s * λ((e m) k)`. -/
theorem baseChangeCoord_etm {M : ModuleCat.{u} R} {n : ℕ} (e : M ≅ ModuleCat.of R (Fin n → R))
    (k : Fin n) (s : B) (m : M) :
    baseChangeCoord lam e k (etm lam s m) = s * lam (e.hom m k) := by
  rw [baseChangeCoord, ModuleCat.comp_apply, map_etm]
  exact baseChangeSelf_etm lam s _

/-- A vector all of whose coordinates vanish after extension of scalars gives a vanishing
elementary tensor. -/
theorem etm_one_eq_zero_of_coord {M : ModuleCat.{u} R} {n : ℕ}
    (e : M ≅ ModuleCat.of R (Fin n → R)) (y : M) (hy : ∀ k, lam (e.hom y k) = 0) :
    etm lam 1 y = 0 := by
  classical
  have h1 : e.hom y = ∑ k, (e.hom y k) • (Pi.single k (1 : R) : Fin n → R) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hdec : y = ∑ k, (e.hom y k) • e.inv (Pi.single k (1 : R)) := by
    calc y = e.inv (e.hom y) := (e.hom_inv_id_apply y).symm
      _ = e.inv (∑ k, (e.hom y k) • (Pi.single k (1 : R) : Fin n → R)) := congrArg _ h1
      _ = _ := by rw [map_sum]; simp only [map_smul]
  rw [hdec]
  have hsum : ∀ (T : Finset (Fin n)), etm lam 1 (∑ k ∈ T, (e.hom y k) •
      e.inv (Pi.single k (1 : R))) = 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert k T hk ih =>
      rw [Finset.sum_insert hk, etm_add_right, ih, add_zero, etm_smul_right, hy k, mul_zero,
        etm_zero_left]
  exact hsum Finset.univ

/-- Every element of the extension of scalars of a free module of rank one is a multiple of the
elementary tensor of a fixed generator. -/
theorem exists_eq_smul_etm_of_rank_one {M : ModuleCat.{u} R}
    (e : M ≅ ModuleCat.of R (Fin 1 → R)) (y : (ModuleCat.extendScalars.{u, u, u} lam).obj M) :
    ∃ t : B, y = t • etm lam 1 (e.inv fun _ => 1) := by
  refine extendScalars_induction lam (P := fun y => ∃ t : B, y = t • etm lam 1
    (e.inv fun _ => 1)) ?_ ?_ y
  · rintro x z ⟨t, rfl⟩ ⟨t', rfl⟩
    exact ⟨t + t', by rw [add_smul]⟩
  · intro s m
    refine ⟨s * lam (e.hom m 0), ?_⟩
    have h1 : e.hom m = (e.hom m 0) • (fun _ => (1 : R)) := by
      funext j
      have : j = 0 := Subsingleton.elim _ _
      subst this
      change e.hom m 0 = e.hom m 0 * 1
      rw [mul_one]
    have hm : m = (e.hom m 0) • e.inv (fun _ => 1) := by
      calc m = e.inv (e.hom m) := (e.hom_inv_id_apply m).symm
        _ = e.inv ((e.hom m 0) • (fun _ => (1 : R))) := congrArg _ h1
        _ = _ := map_smul _ _ _
    conv_lhs => rw [hm]
    rw [etm_smul_right, smul_etm, mul_one]

end Coordinates

/-! ### The main statement -/

/-- The composition isomorphism of extension of scalars on `1 ⊗ (1 ⊗ m)`, in the `etm` spelling. -/
theorem extendScalarsComp_inv_app_etm_one_etm_one {B C : Type u} [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (M : ModuleCat.{u} A) (m : M) :
    (ModuleCat.extendScalarsComp φ ψ).inv.app M (etm ψ 1 (etm φ 1 m)) = etm (ψ.comp φ) 1 m := by
  have hhom : (ModuleCat.extendScalarsComp φ ψ).hom.app M (etm1 (ψ.comp φ) m) =
      etm1 ψ (etm1 φ m) := ModuleCat.extendScalarsComp_hom_app_one_tmul φ ψ M m
  simp only [etm, one_smul]
  rw [← hhom, Iso.hom_inv_id_app_apply]

/-- The composition isomorphism of extension of scalars on a twofold elementary tensor. -/
theorem extendScalarsComp_inv_app_etm_etm {B C : Type u} [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (M : ModuleCat.{u} A) (t : C) (s : B) (m : M) :
    (ModuleCat.extendScalarsComp φ ψ).inv.app M (etm ψ t (etm φ s m)) =
      etm (ψ.comp φ) (t * ψ s) m := by
  have h1 : etm φ s m = s • etm φ 1 m := by rw [smul_etm, mul_one]
  rw [h1, etm_smul_right, ← mul_one (t * ψ s), ← smul_etm, map_smul,
    extendScalarsComp_inv_app_etm_one_etm_one, smul_etm, ← smul_etm, smul_etm]

/-- Transport of the injectivity hypothesis along an equality of ring maps. -/
private theorem mono_homologyMap_congr {K : Type u} [Field K] {χ₁ χ₂ : A →+* K} (h : χ₁ = χ₂)
    {P P' : CochainComplex (ModuleCat.{u} A) ℤ} (ψ : P ⟶ P') (i : ℤ)
    (hm : Mono (HomologicalComplex.homologyMap
      (((ModuleCat.extendScalars.{u, u, u} χ₁).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ)
        i)) :
    Mono (HomologicalComplex.homologyMap
      (((ModuleCat.extendScalars.{u, u, u} χ₂).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ)
        i) := by
  subst h
  exact hm

/-- Composition of extension of scalars, at a chain map. -/
private theorem baseChangeComplexCompIso_naturality {B C : Type u} [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {P P' : CochainComplex (ModuleCat.{u} A) ℤ} (f : P ⟶ P') :
    ((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).map f) =
      (baseChangeComplexCompIso φ ψ P).hom ≫
        ((ModuleCat.extendScalars.{u, u, u} (ψ.comp φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f ≫ (baseChangeComplexCompIso φ ψ P').inv := by
  rw [← cancel_mono (baseChangeComplexCompIso φ ψ P').hom, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  exact (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp φ ψ).symm
    (ComplexShape.up ℤ)).hom.naturality f

/-- The standard free module, with or without a universe lift. -/
private def uliftFunIso {R : Type u} [CommRing R] (n : ℕ) :
    ModuleCat.of R (ULift.{u} (Fin n → R)) ≅ ModuleCat.of R (Fin n → R) :=
  ULift.moduleEquiv.toModuleIso

/-- Extension of scalars along `lam` carries a homotopy equivalence with `P ⊗ R` to one with
`P ⊗ B`. -/
private def baseChangeHomotopyEquiv {R B : Type u} [CommRing R] [CommRing B] (αR : A →+* R)
    (lam : R →+* B) {P : CochainComplex (ModuleCat.{u} A) ℤ}
    {Q : CochainComplex (ModuleCat.{u} R) ℤ} (E : HomotopyEquiv Q (baseChangeComplex αR P)) :
    HomotopyEquiv (baseChangeComplex lam Q) (baseChangeComplex (lam.comp αR) P) :=
  ((ModuleCat.extendScalars.{u, u, u} lam).mapHomotopyEquiv E).trans
    (HomotopyEquiv.ofIso (baseChangeComplexCompIso αR lam P))

/-- **The algebraic core of [Stacks, Tag 0BF1].** Let `ψ : P ⟶ P'` be a chain map of bounded
complexes of finite projective `A`-modules and `χ₀ : A → K₀` a ring map to a field, such that the
fibres `P ⊗ K₀` and `P' ⊗ K₀` have no `H⁻¹` and a one-dimensional `H⁰`, and `H¹(ψ ⊗ K₀)` is
injective. Then there are `g` with `χ₀ g ≠ 0` and finitely many `c k` killed by `χ₀` such that,
for every ring map `φ : A → B` inverting `g`:

* if `H⁰(P' ⊗ B)` is free of rank one, every `φ (c k)` vanishes;
* if every `φ (c k)` vanishes, `P ⊗ B` has a degree-zero cycle `σ` whose image in `P ⊗ K` is not
  a boundary, for every field `K` over `B`. -/
theorem exists_vanishing_family_of_mono_homologyMap_one {K₀ : Type u} [Field K₀] (χ₀ : A →+* K₀)
    [(RingHom.ker χ₀).IsPrime]
    (P P' : CochainComplex (ModuleCat.{u} A) ℤ) (a b a' b' : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] [P'.IsStrictlyGE a'] [P'.IsStrictlyLE b']
    (hfin : ∀ i, Module.Finite A (P.X i)) (hproj : ∀ i, Module.Projective A (P.X i))
    (hfin' : ∀ i, Module.Finite A (P'.X i)) (hproj' : ∀ i, Module.Projective A (P'.X i))
    (ψ : P ⟶ P')
    (hm : Module.finrank K₀ ((baseChangeComplex χ₀ P).homology (-1)) = 0)
    (hm' : Module.finrank K₀ ((baseChangeComplex χ₀ P').homology (-1)) = 0)
    (h0 : Module.finrank K₀ ((baseChangeComplex χ₀ P).homology 0) = 1)
    (h0' : Module.finrank K₀ ((baseChangeComplex χ₀ P').homology 0) = 1)
    (h1 : Mono (HomologicalComplex.homologyMap
      (((ModuleCat.extendScalars.{u, u, u} χ₀).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ)
        1)) :
    ∃ g : A, χ₀ g ≠ 0 ∧ ∃ (n : ℕ) (c : Fin n → A), (∀ k, χ₀ (c k) = 0) ∧
      (∀ (B : Type u) [CommRing B] (φ : A →+* B), IsUnit (φ g) →
        Nonempty (((baseChangeComplex φ P').homology 0) ≃ₗ[B] B) → ∀ k, φ (c k) = 0) ∧
      (∀ (B : Type u) [CommRing B] (φ : A →+* B), IsUnit (φ g) → (∀ k, φ (c k) = 0) →
        ∃ σ : (baseChangeComplex φ P).X 0, (baseChangeComplex φ P).d 0 1 σ = 0 ∧
          ∀ (K : Type u) [Field K] (χ : B →+* K) (τ : (baseChangeComplex (χ.comp φ) P).X (-1)),
            (baseChangeComplex (χ.comp φ) P).d (-1) 0 τ ≠
              (ModuleCat.extendScalarsComp φ χ).inv.app (P.X 0) (etm χ 1 σ)) := by
  classical
  obtain ⟨f, hf, hQ⟩ := exists_minimal_model χ₀ P a b hfin hproj
  obtain ⟨f', hf', hQ'⟩ := exists_minimal_model χ₀ P' a' b' hfin' hproj'
  let R := Localization.Away (f * f')
  let αR : A →+* R := algebraMap A R
  have hRu : IsUnit (αR (f * f')) := IsLocalization.Away.algebraMap_isUnit (f * f')
  rw [map_mul] at hRu
  have hRf : IsUnit (αR f) := isUnit_of_mul_isUnit_left hRu
  have hRf' : IsUnit (αR f') := isUnit_of_mul_isUnit_right hRu
  have hχff : IsUnit (χ₀ (f * f')) := by
    rw [map_mul]; exact (isUnit_iff_ne_zero.mpr hf).mul (isUnit_iff_ne_zero.mpr hf')
  have hlift : ∀ {B : Type u} [CommRing B] (φ : A →+* B), IsUnit (φ (f * f')) →
      ∃ lam : R →+* B, lam.comp αR = φ := fun φ h =>
    ⟨IsLocalization.Away.lift (f * f') h, IsLocalization.Away.lift_comp (f * f') h⟩
  obtain ⟨ρR, hρR⟩ := hlift χ₀ hχff
  obtain ⟨Q, -, hQX, hQd, ⟨E⟩⟩ := hQ R αR ρR hRf hρR
  obtain ⟨Q', -, hQX', hQd', ⟨E'⟩⟩ := hQ' R αR ρR hRf' hρR
  set r := fun i => Module.finrank K₀ ((baseChangeComplex χ₀ P).homology i) with hr
  set r' := fun i => Module.finrank K₀ ((baseChangeComplex χ₀ P').homology i) with hr'
  have eX : ∀ i, Q.X i ≅ ModuleCat.of R (Fin (r i) → R) := fun i =>
    (hQX i).some ≪≫ uliftFunIso _
  have eX' : ∀ i, Q'.X i ≅ ModuleCat.of R (Fin (r' i) → R) := fun i =>
    (hQX' i).some ≪≫ uliftFunIso _
  have hr0 : r 0 = 1 := h0
  have hr0' : r' 0 = 1 := h0'
  have hrm : r (-1) = 0 := hm
  have hrm' : r' (-1) = 0 := hm'
  let e0 : Q.X 0 ≅ ModuleCat.of R (Fin 1 → R) := eX 0 ≪≫ eqToIso (by rw [hr0])
  let e0' : Q'.X 0 ≅ ModuleCat.of R (Fin 1 → R) := eX' 0 ≪≫ eqToIso (by rw [hr0'])
  have hzQ : IsZero (Q.X (-1)) := by
    refine IsZero.of_iso ?_ (eX (-1))
    rw [hrm]
    exact ModuleCat.isZero_of_subsingleton _
  have hzQ' : IsZero (Q'.X (-1)) := by
    refine IsZero.of_iso ?_ (eX' (-1))
    rw [hrm']
    exact ModuleCat.isZero_of_subsingleton _
  have hfinQ1 : Module.Finite R (Q.X 1) := Module.Finite.equiv (eX 1).toLinearEquiv.symm
  have hfinQ'1 : Module.Finite R (Q'.X 1) := Module.Finite.equiv (eX' 1).toLinearEquiv.symm
  have hprojQ'1 : Module.Projective R (Q'.X 1) :=
    Module.Projective.of_equiv (eX' 1).toLinearEquiv.symm
  let bcF := fun {S : Type u} [CommRing S] (θ : R →+* S) =>
    (ModuleCat.extendScalars.{u, u, u} θ).mapHomologicalComplex (ComplexShape.up ℤ)
  let χQ : Q ⟶ Q' := E.hom ≫ ((ModuleCat.extendScalars.{u, u, u} αR).mapHomologicalComplex
    (ComplexShape.up ℤ)).map ψ ≫ E'.inv
  have hmono : Mono (HomologicalComplex.homologyMap ((bcF ρR).map χQ) 1) := by
    have hsplit : (bcF ρR).map χQ = (bcF ρR).map E.hom ≫
        ((baseChangeComplexCompIso αR ρR P).hom ≫
          ((ModuleCat.extendScalars.{u, u, u} (ρR.comp αR)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map ψ ≫ (baseChangeComplexCompIso αR ρR P').inv) ≫
        (bcF ρR).map E'.inv := by
      rw [← baseChangeComplexCompIso_naturality]
      simp only [χQ, Functor.map_comp]
      rfl
    rw [hsplit, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
    have i1 : IsIso (HomologicalComplex.homologyMap ((bcF ρR).map E.hom) 1) :=
      (((ModuleCat.extendScalars.{u, u, u} ρR).mapHomotopyEquiv E).toHomologyIso 1).isIso_hom
    have i2 : IsIso (HomologicalComplex.homologyMap ((bcF ρR).map E'.inv) 1) :=
      (((ModuleCat.extendScalars.{u, u, u} ρR).mapHomotopyEquiv E').toHomologyIso 1).isIso_inv
    have m3 := mono_homologyMap_congr hρR.symm ψ 1 h1
    infer_instance
  obtain ⟨δ, hδ0, hδ⟩ := exists_ne_zero_d_eq_zero_of_comp_eq_zero ρR χQ (hQd 0 1 rfl)
    (hQd 1 2 rfl) hmono
  let g0' : Q'.X 0 := e0'.inv (fun _ => 1)
  let c' : Q'.X 1 := Q'.d 0 1 g0'
  have hcoord : ∀ k : Fin (r' 1), ∃ (x : A) (y : Submonoid.powers (f * f')),
      IsLocalization.mk' R x y = (eX' 1).hom c' k := fun k => by
    obtain ⟨⟨x, y⟩, h⟩ := IsLocalization.mk'_surjective (Submonoid.powers (f * f'))
      ((eX' 1).hom c' k)
    exact ⟨x, y, h⟩
  choose num den hnd using hcoord
  obtain ⟨⟨d0, s0⟩, hd0⟩ := IsLocalization.mk'_surjective (Submonoid.powers (f * f')) δ
  have hnum : ∀ k, αR (num k) = (eX' 1).hom c' k * αR (den k) := fun k => by
    rw [← hnd k, IsLocalization.mk'_spec]
  have hd0' : αR d0 = δ * αR s0 := by
    rw [← IsLocalization.mk'_spec R d0 s0]
    exact congrArg (· * αR s0) hd0
  have hunit : ∀ y : Submonoid.powers (f * f'), IsUnit (αR y) := fun y =>
    IsLocalization.map_units R y
  have hdet : ∀ {S : Type u} [CommRing S] (θ : R →+* S),
      ((bcF θ).obj Q').d 0 1 (etm θ 1 g0') = etm θ 1 c' := fun θ => map_etm θ (Q'.d 0 1) 1 g0'
  have hρc : ∀ k, ρR ((eX' 1).hom c' k) = 0 := by
    intro k
    have hd := hdet ρR
    have hz : (baseChangeComplex ρR Q').d 0 1 (etm ρR 1 g0') = 0 := by
      rw [hQd' 0 1 rfl]; rfl
    have := congrArg (baseChangeCoord ρR (eX' 1) k) (hd.symm.trans hz)
    rwa [baseChangeCoord_etm, map_zero, one_mul] at this
  have hρd0 : ρR (αR d0) ≠ 0 := by
    rw [hd0', map_mul]
    exact mul_ne_zero hδ0 ((hunit s0).map ρR).ne_zero
  refine ⟨f * f' * d0, ?_, r' 1, num, ?_, ?_, ?_⟩
  · rw [← hρR, RingHom.comp_apply]
    simp only [map_mul]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) hρd0
    · rw [← RingHom.comp_apply, hρR]; exact hf
    · rw [← RingHom.comp_apply, hρR]; exact hf'
  · intro k
    rw [← hρR, RingHom.comp_apply, hnum k, map_mul, hρc k, zero_mul]
  · intro B _ φ hφ ⟨θ⟩ k
    rw [map_mul] at hφ
    have hφff : IsUnit (φ (f * f')) := isUnit_of_mul_isUnit_left hφ
    obtain ⟨lam, rfl⟩ := hlift φ hφff
    let EB' := baseChangeHomotopyEquiv αR lam E'
    let θ' : ((bcF lam).obj Q').homology 0 ≃ₗ[B] B := (EB'.toHomologyIso 0).toLinearEquiv.trans θ
    have hzB : IsZero (((bcF lam).obj Q').X (-1)) :=
      (ModuleCat.extendScalars.{u, u, u} lam).map_isZero hzQ'
    have hdin : ((bcF lam).obj Q').d (-1) 0 = 0 := hzB.eq_of_src _ _
    have hπ := ((bcF lam).obj Q').isIso_homologyπ (-1) 0 (by simp) hdin
    let w := (inv (((bcF lam).obj Q').homologyπ 0)) (θ'.symm 1)
    let x := ((bcF lam).obj Q').iCycles 0 w
    have hdx : ((bcF lam).obj Q').d 0 1 x = 0 := by
      change (((bcF lam).obj Q').iCycles 0 ≫ ((bcF lam).obj Q').d 0 1) w = 0
      rw [HomologicalComplex.iCycles_d]; rfl
    have hann : ∀ t : B, t • x = 0 → t = 0 := by
      intro t ht
      have h1 : t • w = 0 := by
        apply (ModuleCat.mono_iff_injective (((bcF lam).obj Q').iCycles 0)).1 inferInstance
        rw [map_smul, map_zero]; exact ht
      have h2 : ((bcF lam).obj Q').homologyπ 0 w = θ'.symm 1 := by
        change (inv (((bcF lam).obj Q').homologyπ 0) ≫ ((bcF lam).obj Q').homologyπ 0)
          (θ'.symm 1) = θ'.symm 1
        rw [IsIso.inv_hom_id]; rfl
      calc t = θ' (t • θ'.symm 1) := by rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul,
              mul_one]
        _ = θ' (((bcF lam).obj Q').homologyπ 0 (t • w)) := congrArg θ' (by rw [map_smul, h2])
        _ = 0 := by rw [h1, map_zero, map_zero]
    obtain ⟨t0, ht0⟩ := exists_eq_smul_etm_of_rank_one lam e0' x
    have hdx' : ((bcF lam).obj Q').d 0 1 x = t0 • etm lam 1 c' := by
      rw [ht0, map_smul, hdet]
    have hk : t0 * lam ((eX' 1).hom c' k) = 0 := by
      have := congrArg (baseChangeCoord lam (eX' 1) k) (hdx'.symm.trans hdx)
      rwa [map_smul, baseChangeCoord_etm, map_zero, one_mul, smul_eq_mul] at this
    have hlam : lam ((eX' 1).hom c' k) = 0 :=
      hann _ (by rw [ht0, smul_smul, mul_comm (lam _) t0, hk, zero_smul])
    rw [RingHom.comp_apply, hnum k, map_mul, hlam, zero_mul]
  · intro B _ φ hφ hc
    rw [map_mul] at hφ
    have hφff : IsUnit (φ (f * f')) := isUnit_of_mul_isUnit_left hφ
    have hφd0 : IsUnit (φ d0) := isUnit_of_mul_isUnit_right hφ
    obtain ⟨lam, rfl⟩ := hlift φ hφff
    have hlamc : ∀ k, lam ((eX' 1).hom c' k) = 0 := fun k => by
      have h := hc k
      rw [RingHom.comp_apply, hnum k, map_mul] at h
      exact ((((hunit (den k)).map lam)).mul_left_eq_zero).mp h
    have hzc' : etm lam 1 c' = 0 := etm_one_eq_zero_of_coord lam (eX' 1) c' hlamc
    have hd'B : ((bcF lam).obj Q').d 0 1 = 0 := by
      refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
      obtain ⟨t, rfl⟩ := exists_eq_smul_etm_of_rank_one lam e0' y
      change ((bcF lam).obj Q').d 0 1 (t • etm lam 1 g0') = 0
      rw [map_smul, hdet, hzc', smul_zero]
    have hδu : IsUnit (lam δ) := by
      have h : IsUnit (lam (αR d0)) := hφd0
      rw [hd0', map_mul] at h
      exact isUnit_of_mul_isUnit_left h
    have hdB : ((bcF lam).obj Q).d 0 1 = 0 :=
      hδ B lam hδu (by rw [hd'B, Limits.comp_zero])
    let EB := baseChangeHomotopyEquiv αR lam E
    let g0 : Q.X 0 := e0.inv (fun _ => 1)
    refine ⟨EB.hom.f 0 (etm lam 1 g0), ?_, ?_⟩
    · have h := EB.hom.comm 0 1
      change (EB.hom.f 0 ≫ (baseChangeComplex (lam.comp αR) P).d 0 1) (etm lam 1 g0) = 0
      rw [h, hdB, Limits.zero_comp]
      rfl
    · intro K _ χ τ hτ
      let ν : R →+* K := χ.comp lam
      let EK := baseChangeHomotopyEquiv αR ν E
      let z : ((bcF ν).obj Q).X 0 := etm ν 1 g0
      have hC1 : (ModuleCat.extendScalarsComp (lam.comp αR) χ).inv.app (P.X 0)
          (etm χ 1 (EB.hom.f 0 (etm lam 1 g0))) = EK.hom.f 0 z := by
        change (ModuleCat.extendScalarsComp (lam.comp αR) χ).inv.app (P.X 0)
          (etm χ 1 ((ModuleCat.extendScalarsComp αR lam).inv.app (P.X 0)
            ((ModuleCat.extendScalars.{u, u, u} lam).map (E.hom.f 0) (etm lam 1 g0)))) =
          (ModuleCat.extendScalarsComp αR ν).inv.app (P.X 0)
            ((ModuleCat.extendScalars.{u, u, u} ν).map (E.hom.f 0) (etm ν 1 g0))
        rw [map_etm, map_etm]
        generalize E.hom.f 0 g0 = y
        refine extendScalars_induction αR (P := fun y =>
          (ModuleCat.extendScalarsComp (lam.comp αR) χ).inv.app (P.X 0)
            (etm χ 1 ((ModuleCat.extendScalarsComp αR lam).inv.app (P.X 0) (etm lam 1 y))) =
          (ModuleCat.extendScalarsComp αR ν).inv.app (P.X 0) (etm ν 1 y)) ?_ ?_ y
        · intro y₁ y₂ h₁ h₂
          simp only [etm_add_right, map_add, h₁, h₂]
        · intro s' m
          rw [extendScalarsComp_inv_app_etm_etm, extendScalarsComp_inv_app_etm_etm,
            extendScalarsComp_inv_app_etm_etm]
          simp only [one_mul]
          rfl
      have hzne : z ≠ 0 := by
        intro hz
        have := congrArg (baseChangeCoord ν e0 0) hz
        rw [baseChangeCoord_etm, map_zero, one_mul] at this
        have h1 : e0.hom g0 0 = 1 := by
          change (e0.inv ≫ e0.hom) (fun _ => (1 : R)) 0 = 1
          rw [Iso.inv_hom_id]; rfl
        rw [h1, map_one] at this
        exact one_ne_zero this
      have hdz : ((bcF ν).obj Q).d 0 1 z = 0 := by
        have h1 : ((bcF lam).obj Q).d 0 1 (etm lam 1 g0) = etm lam 1 (Q.d 0 1 g0) :=
          map_etm lam (Q.d 0 1) 1 g0
        rw [hdB] at h1
        have h2 : ((bcF ν).obj Q).d 0 1 z = etm ν 1 (Q.d 0 1 g0) := map_etm ν (Q.d 0 1) 1 g0
        rw [h2, ← extendScalarsComp_inv_app_etm_one_etm_one lam χ (Q.X 1), ← h1]
        change (ModuleCat.extendScalarsComp lam χ).inv.app (Q.X 1) (etm χ 1 0) = 0
        rw [etm_zero_right, map_zero]
      have hsub : Subsingleton (((bcF ν).obj Q).X (-1)) :=
        ModuleCat.subsingleton_of_isZero ((ModuleCat.extendScalars.{u, u, u} ν).map_isZero hzQ)
      have hτ' : (baseChangeComplex (ν.comp αR) P).d (-1) 0 τ = EK.hom.f 0 z := hτ.trans hC1
      let H := EK.homotopyHomInvId
      have hc := H.comm 0
      rw [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel 0 1 from rfl),
        prevD_eq H.hom (show (ComplexShape.up ℤ).Rel (-1) 0 from by simp)] at hc
      have hz := congrArg (fun φ => φ z) hc
      simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, HomologicalComplex.id_f,
        ModuleCat.id_apply, ModuleCat.hom_add, LinearMap.add_apply] at hz
      rw [← hτ', hdz, map_zero, zero_add] at hz
      have h1 : EK.inv.f 0 ((baseChangeComplex (ν.comp αR) P).d (-1) 0 τ) =
          ((bcF ν).obj Q).d (-1) 0 (EK.inv.f (-1) τ) := by
        rw [← ModuleCat.comp_apply, ← EK.inv.comm (-1) 0]; rfl
      rw [h1, Subsingleton.elim (EK.inv.f (-1) τ) 0,
        Subsingleton.elim ((H.hom 0 (-1)) z) 0] at hz
      simp only [map_zero, zero_add] at hz
      exact hzne hz.symm

end StacksDraft.Perfect

end
