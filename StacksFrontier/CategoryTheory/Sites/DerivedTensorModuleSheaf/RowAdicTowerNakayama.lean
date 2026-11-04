module

public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Constant
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.RowAdicTowerChangeOfRings

/-!
# A Nakayama lemma for the tower of termwise reductions

Let `(C, J)` be a site, `R` a commutative ring and `𝔟 ⊆ R` a nilpotent ideal. A morphism
`f : U ⟶ V` between K-flat complexes of sheaves of `R`-modules is a quasi-isomorphism as soon as
its termwise reduction `f ⊗_R \underline{R/𝔟}` is.

## Main results

* `Stacks.ModuleSheaf.kFlat_constantSheaf_mapHomologicalComplex_of_flat`,
  `Stacks.ModuleSheaf.kFlat_constantSheaf_mapHomologicalComplex`: the constant complex of a
  bounded above complex of flat (in particular, projective) `R`-modules is K-flat.
* `Stacks.ModuleSheaf.acyclic_rowComplex_of_kFlat_of_acyclic`: tensoring an acyclic K-flat complex
  termwise with any sheaf gives an acyclic complex.
* `Stacks.ModuleSheaf.quasiIso_rowComplexMap_of_kFlat`: termwise tensoring with a sheaf preserves
  quasi-isomorphisms between K-flat complexes.
* `Stacks.ModuleSheaf.acyclic_rowComplex_X₂_of_shortExact`: for a K-flat complex `K`, the sheaves
  `N` with `p ↦ K^p ⊗ N` acyclic are closed under extensions.
* `Stacks.ModuleSheaf.quasiIso_of_quasiIso_rowAdicTowerMap_app_one`: the Nakayama lemma above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.KFlatBifunctor Opposite

universe w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed
  CochainComplex.braidedCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [UnivLE.{max u v, w}]

section C
variable {R : Type w} [CommRing R]

/-! ### Constant complexes of flat modules -/

/-- The constant sheaf on a flat `R`-module, placed in one degree, is a K-flat complex. -/
theorem kFlat_single_constantSheaf_obj (V : ModuleCat.{w} R) [Module.Flat R V] (q : ℤ) :
    KFlat (curriedTensor (Sheaf J (ModuleCat.{w} R)))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj
        ((constantSheaf J (ModuleCat.{w} R)).obj V)) := by
  have : PreservesFiniteLimits
      (MonoidalCategory.tensorRight ((constantSheaf J (ModuleCat.{w} R)).obj V)) :=
    preservesFiniteLimits_tensorRight_presheafToSheaf_obj J ((Functor.const Cᵒᵖ).obj V)
      (fun _ => inferInstanceAs (Module.Flat R V))
  exact kFlat_single_of_exact (curriedTensor (Sheaf J (ModuleCat.{w} R))) _ q
    (fun G hG => HomologicalComplex.Acyclic.map (MonoidalCategory.tensorRight _) hG)

/-- **The constant complex of a bounded above complex of flat `R`-modules is K-flat.** -/
theorem kFlat_constantSheaf_mapHomologicalComplex_of_flat (M : CochainComplex (ModuleCat.{w} R) ℤ)
    (b : ℤ) [M.IsStrictlyLE b] (hM : ∀ k, Module.Flat R (M.X k)) :
    KFlat (curriedTensor (Sheaf J (ModuleCat.{w} R)))
      (((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) :=
  CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE _ _ b
    (fun _ ↦ inferInstance)
    (acyclic_of_isColimit_nat (J := J) (Λ := R))
    (fun q => have := hM q; kFlat_single_constantSheaf_obj (M.X q) q)

/-- **The constant complex of a bounded above complex of projective `R`-modules is K-flat.** -/
theorem kFlat_constantSheaf_mapHomologicalComplex (M : CochainComplex (ModuleCat.{w} R) ℤ) (b : ℤ)
    [M.IsStrictlyLE b] (hM : ∀ k, Module.Projective R (M.X k)) :
    KFlat (curriedTensor (Sheaf J (ModuleCat.{w} R)))
      (((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) :=
  kFlat_constantSheaf_mapHomologicalComplex_of_flat M b fun k => have := hM k; inferInstance

/-! ### Termwise tensor products with a K-flat complex -/

/-- **An acyclic K-flat complex tensored termwise with any sheaf is acyclic.** -/
theorem acyclic_rowComplex_of_kFlat_of_acyclic {K : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℤ}
    (hK : KFlat (curriedTensor _) K) (hac : K.Acyclic) (N : Sheaf J (ModuleCat.{w} R)) :
    (rowComplex (curriedTensor (Sheaf J (ModuleCat.{w} R))) K N).Acyclic := by
  obtain ⟨P, q, hP, hq⟩ :=
    exists_kFlat_quasiIso ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj N)
  have h := acyclic_totalComplex_of_kFlat_of_acyclic (curriedTensor _) hK hac q hq
    (CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat _ hP)
  exact fun n => ((h n).of_iso (β_ _ K)).of_iso (totalComplexSingleIso K N)

/-- The termwise tensor product with a sheaf commutes with mapping cones. -/
def rowComplexMappingConeIso {K L : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℤ} (f : K ⟶ L)
    (N : Sheaf J (ModuleCat.{w} R)) :
    rowComplex (curriedTensor _) (CochainComplex.mappingCone f) N ≅
      CochainComplex.mappingCone (rowComplexMap (curriedTensor _) f N) :=
  CochainComplex.mappingCone.mapHomologicalComplexIso f (MonoidalCategory.tensorRight N)

/-- The mapping cone of a morphism between K-flat complexes is K-flat. -/
theorem kFlat_mappingCone_of_kFlat {K L : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℤ}
    (f : K ⟶ L) (hK : KFlat (curriedTensor _) K) (hL : KFlat (curriedTensor _) L) :
    KFlat (curriedTensor _) (CochainComplex.mappingCone f) :=
  kFlat_obj₃_of_distTriang _ _ _ _ (HomotopyCategory.mappingCone_triangleh_distinguished f) hK hL

/-- **Termwise tensoring with a sheaf preserves quasi-isomorphisms between K-flat complexes.** -/
theorem quasiIso_rowComplexMap_of_kFlat {U V : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℤ}
    (f : U ⟶ V) (hU : KFlat (curriedTensor _) U) (hV : KFlat (curriedTensor _) V) [QuasiIso f]
    (N : Sheaf J (ModuleCat.{w} R)) :
    QuasiIso (rowComplexMap (curriedTensor (Sheaf J (ModuleCat.{w} R))) f N) :=
  (quasiIso_iff_acyclic_mappingCone _).2 fun n =>
    (acyclic_rowComplex_of_kFlat_of_acyclic (kFlat_mappingCone_of_kFlat f hU hV)
      ((quasiIso_iff_acyclic_mappingCone f).1 inferInstance) N n).of_iso
      (rowComplexMappingConeIso f N)

/-- **Closure under extensions.** For a K-flat complex `K` and a short exact sequence
`0 → N₁ → N₂ → N₃ → 0` of sheaves, if `p ↦ K^p ⊗ N₁` and `p ↦ K^p ⊗ N₃` are acyclic, so is
`p ↦ K^p ⊗ N₂`. -/
theorem acyclic_rowComplex_X₂_of_shortExact {K : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℤ}
    (hK : KFlat (curriedTensor _) K) {S : ShortComplex (Sheaf J (ModuleCat.{w} R))}
    (hS : S.ShortExact) (h₁ : (rowComplex (curriedTensor _) K S.X₁).Acyclic)
    (h₃ : (rowComplex (curriedTensor _) K S.X₃).Acyclic) :
    (rowComplex (curriedTensor _) K S.X₂).Acyclic := by
  let F := curriedTensor (Sheaf J (ModuleCat.{w} R))
  let Ψ := (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).obj K
  let S' := S.map (HomologicalComplex.single _ (ComplexShape.up ℤ) 0)
  have hS' : S'.ShortExact := hS.map_of_exact _
  have hφ := quasiIso_of_kFlatLeft F K (CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat _ hK) _
    (CochainComplex.mappingCone.quasiIso_descShortComplex hS')
  have hc : (Ψ.obj (CochainComplex.mappingCone S'.f)).Acyclic :=
    (HomologicalComplex.acyclic_iff_of_quasiIso _ hφ).2
      (fun n => (h₃ n).of_iso (totalComplexSingleIso K S.X₃).symm)
  have hg : QuasiIso (Ψ.map S'.f) := (quasiIso_iff_acyclic_mappingCone _).2
    (fun n => (hc n).of_iso
      (Stacks.SheafOfModules.Tensor.Reduction.bifunctorMappingConeIso F K S'.f))
  have h₂ := (HomologicalComplex.acyclic_iff_of_quasiIso _ hg).1
    (fun n => (h₁ n).of_iso (totalComplexSingleIso K S.X₁).symm)
  exact fun n => (h₂ n).of_iso (totalComplexSingleIso K S.X₂)

/-! ### Change of rings -/

section ChangeOfRings

variable {S : Type w} [CommRing S] (e : R →+* S)

/-- **Base change of the vanishing.** If `K` is K-flat and `p ↦ K^p ⊗_R \underline{S}` is
acyclic, then `p ↦ K^p ⊗_R \underline{L}` is acyclic for every `S`-module `L` read over `R`. -/
theorem acyclic_rowComplex_restrictScalars {K : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℤ}
    (hK : KFlat (curriedTensor _) K)
    (h : (rowComplex (curriedTensor _) K ((constantSheaf J (ModuleCat.{w} R)).obj
      ((ModuleCat.restrictScalars.{w} e).obj (ModuleCat.of S S)))).Acyclic)
    (L : ModuleCat.{w} S) :
    (rowComplex (curriedTensor _) K ((constantSheaf J (ModuleCat.{w} R)).obj
      ((ModuleCat.restrictScalars.{w} e).obj L))).Acyclic := by
  let E := restrictScalarsConstantSheafRowFunctorIso J e K
  have h₁ : (((extendScalars J e).mapHomologicalComplex _).obj K).Acyclic := by
    rw [← HomologicalComplex.acyclic_map_iff_of_preservesHomology _ (restrictScalars J e)]
    exact fun n => (h n).of_iso (E.app (ModuleCat.of S S) ≪≫
      ((restrictScalars J e).mapHomologicalComplex _).mapIso (rowComplexUnitIso J _))
  have h₂ := acyclic_rowComplex_of_kFlat_of_acyclic (kFlat_extendScalars J e hK) h₁
    ((constantSheaf J (ModuleCat.{w} S)).obj L)
  rw [← HomologicalComplex.acyclic_map_iff_of_preservesHomology _ (restrictScalars J e)] at h₂
  exact fun n => (h₂ n).of_iso (E.app L).symm

end ChangeOfRings

/-! ### The Nakayama lemma -/

/-- Acyclicity of `p ↦ K^p ⊗ \underline{M}` depends only on the isomorphism class of `M`. -/
theorem acyclic_rowComplex_constantSheaf_of_iso {K : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℤ}
    {M M' : ModuleCat.{w} R} (i : M ≅ M')
    (h : (rowComplex (curriedTensor _) K ((constantSheaf J (ModuleCat.{w} R)).obj M)).Acyclic) :
    (rowComplex (curriedTensor _) K ((constantSheaf J (ModuleCat.{w} R)).obj M')).Acyclic :=
  fun n => (h n).of_iso ((rowFunctor (curriedTensor _) K).mapIso
    ((constantSheaf J (ModuleCat.{w} R)).mapIso i))

omit [UnivLE.{max u v, w}] in
/-- The quotient `R/𝔟`, as a ring, read as an `R`-module, is the module quotient `R/𝔟R`. -/
def restrictScalarsQuotientIso (𝔟 : Ideal R) :
    (ModuleCat.restrictScalars.{w} (Ideal.Quotient.mk 𝔟)).obj (ModuleCat.of (R ⧸ 𝔟) (R ⧸ 𝔟)) ≅
      ModuleCat.of R (R ⧸ (𝔟 ^ 1 • ⊤ : Submodule R R)) :=
  LinearEquiv.toModuleIso
    ({ toFun := fun x => x
       invFun := fun x => x
       map_add' := fun _ _ => rfl
       map_smul' := fun r x => by
         obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
         rfl
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl } ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (by rw [pow_one, Ideal.smul_eq_mul, Ideal.mul_top]))

omit [UnivLE.{max u v, w}] in
/-- An `R`-module killed by `𝔟` is the restriction of scalars of an `R/𝔟`-module. -/
def restrictScalarsQuotientModuleIso (𝔟 : Ideal R) (M : ModuleCat.{w} R)
    (hM : Module.IsTorsionBySet R M 𝔟) :
    letI := hM.module
    (ModuleCat.restrictScalars.{w} (Ideal.Quotient.mk 𝔟)).obj (ModuleCat.of (R ⧸ 𝔟) M) ≅ M :=
  letI := hM.module
  LinearEquiv.toModuleIso
    { toFun := fun x => x
      invFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => Module.IsTorsionBySet.mk_smul hM r x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **The modules killed by `𝔟`.** If `K` is K-flat and `p ↦ K^p ⊗ \underline{R/𝔟}` is acyclic,
then `p ↦ K^p ⊗ \underline{M}` is acyclic for every `R`-module `M` killed by `𝔟`. -/
theorem acyclic_rowComplex_constantSheaf_of_smul_eq_zero (𝔟 : Ideal R)
    {K : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℤ} (hK : KFlat (curriedTensor _) K)
    (h : (rowComplex (curriedTensor _) K ((constantSheaf J (ModuleCat.{w} R)).obj
      (ModuleCat.of R (R ⧸ (𝔟 ^ 1 • ⊤ : Submodule R R))))).Acyclic)
    (M : ModuleCat.{w} R) (hM : ∀ r ∈ 𝔟, ∀ x : M, r • x = 0) :
    (rowComplex (curriedTensor _) K ((constantSheaf J (ModuleCat.{w} R)).obj M)).Acyclic := by
  have hM' : Module.IsTorsionBySet R M 𝔟 := fun x a => hM a a.2 x
  let := hM'.module
  exact acyclic_rowComplex_constantSheaf_of_iso (restrictScalarsQuotientModuleIso 𝔟 M hM')
    (acyclic_rowComplex_restrictScalars (Ideal.Quotient.mk 𝔟) hK
      (acyclic_rowComplex_constantSheaf_of_iso (restrictScalarsQuotientIso 𝔟).symm h)
      (ModuleCat.of (R ⧸ 𝔟) M))

/-- For a zero sheaf `N`, the termwise tensor product `p ↦ K^p ⊗ N` is acyclic. -/
theorem acyclic_rowComplex_of_isZero (K : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℤ)
    {N : Sheaf J (ModuleCat.{w} R)} (hN : IsZero N) :
    (rowComplex (curriedTensor _) K N).Acyclic := fun n =>
  ShortComplex.exact_of_isZero_X₂ _ ((MonoidalCategory.tensorLeft (K.X n)).map_isZero hN)

omit [UnivLE.{max u v, w}] in
/-- The short exact sequence `0 → N → M → M/N → 0` of a submodule. -/
theorem shortExact_submodule {M : ModuleCat.{w} R} (N : Submodule R M) :
    (ShortComplex.mk (ModuleCat.ofHom N.subtype) (ModuleCat.ofHom N.mkQ)
      (by ext x; simp)).ShortExact where
  exact := ShortComplex.Exact.moduleCat_of_range_eq_ker _ _
    (N.range_subtype.trans N.ker_mkQ.symm)
  mono_f := (ModuleCat.mono_iff_injective _).2 N.injective_subtype
  epi_g := (ModuleCat.epi_iff_surjective _).2 N.mkQ_surjective

/-- **Dévissage along the powers of `𝔟`.** If `K` is K-flat and `p ↦ K^p ⊗ \underline{M}` is
acyclic for every `R`-module `M` killed by `𝔟`, then the same holds for every `M` killed by a
power of `𝔟`. -/
theorem acyclic_rowComplex_constantSheaf_of_pow_smul_eq_zero (𝔟 : Ideal R)
    {K : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℤ} (hK : KFlat (curriedTensor _) K)
    (h : ∀ M : ModuleCat.{w} R, (∀ r ∈ 𝔟, ∀ x : M, r • x = 0) →
      (rowComplex (curriedTensor _) K ((constantSheaf J (ModuleCat.{w} R)).obj M)).Acyclic) :
    ∀ (k : ℕ) (M : ModuleCat.{w} R), (∀ r ∈ 𝔟 ^ k, ∀ x : M, r • x = 0) →
      (rowComplex (curriedTensor _) K ((constantSheaf J (ModuleCat.{w} R)).obj M)).Acyclic := by
  intro k
  induction k with
  | zero =>
    intro M hM
    refine acyclic_rowComplex_of_isZero K (Functor.map_isZero _ ?_)
    have : Subsingleton M := ⟨fun x y => by
      rw [← one_smul R x, ← one_smul R y, hM 1 (by simp) x, hM 1 (by simp) y]⟩
    exact ModuleCat.isZero_of_subsingleton M
  | succ k ih =>
    intro M hM
    let N : Submodule R M := 𝔟 ^ k • ⊤
    have hS := (shortExact_submodule N).map_of_exact (constantSheaf J (ModuleCat.{w} R))
    refine acyclic_rowComplex_X₂_of_shortExact hK hS (h _ ?_) (ih _ ?_)
    · intro r hr x
      apply Subtype.ext
      change r • (x : M) = 0
      obtain ⟨x, hx⟩ := x
      refine Submodule.smul_induction_on (p := fun y => r • y = 0) hx (fun s hs m _ => ?_)
        (fun x y hx hy => by simp only [smul_add, hx, hy, add_zero])
      rw [smul_smul]
      exact hM _ (by rw [pow_succ']; exact Ideal.mul_mem_mul hr hs) m
    · intro r hr y
      obtain ⟨m, rfl⟩ := N.mkQ_surjective y
      change r • Submodule.Quotient.mk m = (0 : M ⧸ N)
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hr Submodule.mem_top

/-- **Nakayama's lemma for the tower of termwise reductions.** Let `𝔟` be a nilpotent ideal of
`R` and `f : U ⟶ V` a morphism of K-flat complexes of sheaves of `R`-modules. If the termwise
reduction `f ⊗_R \underline{R/𝔟}` is a quasi-isomorphism, so is `f`. -/
theorem quasiIso_of_quasiIso_rowAdicTowerMap_app_one (𝔟 : Ideal R) (h𝔟 : IsNilpotent 𝔟)
    {U V : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℤ} (f : U ⟶ V)
    (hU : KFlat (curriedTensor _) U) (hV : KFlat (curriedTensor _) V)
    (hf : QuasiIso ((rowAdicTowerMap J 𝔟 f).app (op 1))) :
    QuasiIso f := by
  rw [quasiIso_iff_acyclic_mappingCone]
  have hC := kFlat_mappingCone_of_kFlat f hU hV
  have h₀ : (rowComplex (curriedTensor _) (CochainComplex.mappingCone f)
      ((constantSheaf J (ModuleCat.{w} R)).obj
        (ModuleCat.of R (R ⧸ (𝔟 ^ 1 • ⊤ : Submodule R R))))).Acyclic :=
    fun n => (((quasiIso_iff_acyclic_mappingCone _).1 hf) n).of_iso
      (rowComplexMappingConeIso f _).symm
  obtain ⟨m, hm⟩ := h𝔟
  have h₁ := acyclic_rowComplex_constantSheaf_of_pow_smul_eq_zero 𝔟 hC
    (fun M hM => acyclic_rowComplex_constantSheaf_of_smul_eq_zero 𝔟 hC h₀ M hM) m
    (ModuleCat.of R R) (fun r hr x => by
      rw [hm, Ideal.zero_eq_bot, Ideal.mem_bot] at hr
      rw [hr, zero_smul])
  exact fun n => (h₁ n).of_iso (rowComplexUnitIso J _)

end C

end Stacks.ModuleSheaf
