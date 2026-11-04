module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstantComplexAdicTower
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.AdicReductionSections
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.ReductionTower
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.RowAdicTowerChangeOfRings

/-!
# Transferring towers of reductions from the completion to the ring

Let `(C, J)` be a site, `Λ` a Noetherian ring, `I ⊆ Λ` an ideal and `Λ^∧` the `I`-adic completion.
For a K-flat complex `P` of sheaves of `Λ`-modules and a complex `M` of `Λ^∧`-modules, an
isomorphism in `D(C, Λ^∧)` between the towers of termwise reductions
`j ↦ (Λ^∧ ⊗_Λ P) ⊗ \underline{Λ^∧/(IΛ^∧)ʲ}` and `j ↦ \underline{M} ⊗ \underline{Λ^∧/(IΛ^∧)ʲ}`
gives, after restriction of scalars to `Λ`, an isomorphism in `D(C, Λ)` between the tower of
derived reductions `j ↦ P ⊗_Λ^L \underline{Λ/Iʲ}` and the tower of constant complexes
`j ↦ \underline{M/IʲM}`.

The ingredients are:
* for a ring map `f : R → S`, an ideal `𝔞 ⊆ R` and an `S`-module `V`, the isomorphism
  `V/𝔞ʲV ≅ V ⊗_S S/(𝔞S)ʲ` of `R`-modules, natural in `V` and `j`, and its sheafified form
  `\underline{V/𝔞ʲV} ≅ \underline{V} ⊗_S \underline{S/(𝔞S)ʲ}`;
* the isomorphisms `Λ/Iʲ ≅ Λ^∧/(IΛ^∧)ʲ` of `Λ`-modules, for `I` finitely generated;
* the computation of the derived reductions of a K-flat complex by its termwise reductions.

## Main definitions

* `AlgebraicGeometry.ProEtale.adicQuotientRestrictScalarsTensorIso`: `V/𝔞ʲV ≅ V ⊗_S S/(𝔞S)ʲ`,
  as an isomorphism of functors of `V` and `j`.
* `Stacks.ModuleSheaf.constantAdicQuotientComplexTowerRestrictScalarsIso`: for a complex `M` of
  `S`-modules, the tower `j ↦ \underline{M/𝔞ʲM}` is the restriction of scalars of the tower of
  termwise reductions of `\underline{M}` modulo `(𝔞S)ʲ`.
* `AlgebraicGeometry.ProEtale.adicQuotientAdicCompletionIso`: the tower `j ↦ Λ/Iʲ` is the tower
  `j ↦ Λ^∧/(IΛ^∧)ʲ` read over `Λ`.
* `Stacks.ModuleSheaf.derivedReductionTowerIsoRowAdicTower`: for a K-flat complex `P`, the tower
  of derived reductions of `P` is its tower of termwise reductions.

## Main results

* `Stacks.ModuleSheaf.nonempty_derivedReductionTower_iso_of_rowAdicTower_iso`: an isomorphism of
  towers of termwise reductions over `Λ^∧` yields an isomorphism over `Λ` between the tower of
  derived reductions of `P` and the tower `j ↦ \underline{M/IʲM}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.KFlatBifunctor Opposite

universe t t' w v u

namespace AlgebraicGeometry.ProEtale

section TensorQuotient

variable {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S) (𝔞 : Ideal R)

/-- For a ring map `f : R → S`, an ideal `𝔞 ⊆ R` and an `S`-module `V`, an element of `V` lies in
`(𝔞S)ʲV` if and only if it lies in `𝔞ʲV`, with `V` read over `R`. -/
theorem mem_map_pow_smul_top_iff (V : ModuleCat.{w} S) (j : ℕ)
    (v : (ModuleCat.restrictScalars.{w} f).obj V) :
    (v : V) ∈ (((𝔞.map f) ^ j • ⊤ : Ideal S) • ⊤ : Submodule S V) ↔
      v ∈ (𝔞 ^ j • ⊤ : Submodule R ((ModuleCat.restrictScalars.{w} f).obj V)) := by
  have hI : ((𝔞.map f) ^ j • ⊤ : Ideal S) = (𝔞 ^ j).map f := by
    rw [smul_eq_mul, Ideal.mul_top, Ideal.map_pow]
  rw [hI]
  constructor
  · intro hv
    refine Submodule.smul_induction_on (M := V)
      (p := fun x : V => (x : (ModuleCat.restrictScalars.{w} f).obj V) ∈
        (𝔞 ^ j • ⊤ : Submodule R ((ModuleCat.restrictScalars.{w} f).obj V)))
      hv (fun s hs m _ => ?_) (fun _ _ ha hb => add_mem ha hb)
    refine Submodule.span_induction (p := fun s _ => ∀ m : V,
        ((s • m : V) : (ModuleCat.restrictScalars.{w} f).obj V) ∈
          (𝔞 ^ j • ⊤ : Submodule R ((ModuleCat.restrictScalars.{w} f).obj V)))
      (fun s hs m => ?_) (fun m => ?_) (fun s t _ _ hs ht m => ?_) (fun c s _ hs m => ?_) hs m
    · obtain ⟨a, ha, rfl⟩ := hs
      exact Submodule.smul_mem_smul (M := (ModuleCat.restrictScalars.{w} f).obj V) ha
        (Submodule.mem_top (R := R) (M := (ModuleCat.restrictScalars.{w} f).obj V) (x := m))
    · simp only [zero_smul]
      exact zero_mem _
    · simp only [add_smul]
      exact add_mem (hs m) (ht m)
    · simp only [smul_eq_mul, mul_comm c s, mul_smul]
      exact hs (c • m)
  · intro hv
    refine Submodule.smul_induction_on (M := (ModuleCat.restrictScalars.{w} f).obj V)
      (p := fun x : (ModuleCat.restrictScalars.{w} f).obj V =>
        (x : V) ∈ ((𝔞 ^ j).map f • ⊤ : Submodule S V))
      hv (fun a ha m _ => ?_) (fun _ _ ha hb => add_mem ha hb)
    exact Submodule.smul_mem_smul (M := V) (Ideal.mem_map_of_mem f ha)
      (Submodule.mem_top (R := S) (M := V) (x := m))

/-- The `f`-semilinear map `V/𝔞ʲV → V/(𝔞S)ʲV` induced by the identity of `V`. -/
def adicQuotientRestrictScalarsQuotientMap (V : ModuleCat.{w} S) (j : ℕ) :
    ((ModuleCat.restrictScalars.{w} f).obj V) ⧸
        (𝔞 ^ j • ⊤ : Submodule R ((ModuleCat.restrictScalars.{w} f).obj V)) →ₛₗ[f]
      V ⧸ (((𝔞.map f) ^ j • ⊤ : Ideal S) • ⊤ : Submodule S V) :=
  Submodule.mapQ _ _
    ({ toFun := fun v => (v : V), map_add' := fun _ _ => rfl,
       map_smul' := fun _ _ => rfl } : (ModuleCat.restrictScalars.{w} f).obj V →ₛₗ[f] V)
    (fun v hv => (mem_map_pow_smul_top_iff f 𝔞 V j v).2 hv)

/-- The `f`-semilinear map `V/𝔞ʲV → V/(𝔞S)ʲV` induced by the identity of `V` is bijective. -/
theorem bijective_adicQuotientRestrictScalarsQuotientMap (V : ModuleCat.{w} S) (j : ℕ) :
    Function.Bijective (adicQuotientRestrictScalarsQuotientMap f 𝔞 V j) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' := (Submodule.Quotient.mk_eq_zero _).1 hx
    exact (Submodule.Quotient.mk_eq_zero _).2 ((mem_map_pow_smul_top_iff f 𝔞 V j v).1 hx')
  · intro y
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk v, rfl⟩

/-- The identity of `V` induces the `R`-linear map `V/𝔞ʲV → V/(𝔞S)ʲV`, the target read
over `R`. -/
def adicQuotientRestrictScalarsQuotientHom (V : ModuleCat.{w} S) (j : ℕ) :
    (adicQuotientModuleSystem R 𝔞 ((ModuleCat.restrictScalars.{w} f).obj V)).obj (op j) ⟶
      (ModuleCat.restrictScalars.{w} f).obj
        (ModuleCat.of S (V ⧸ (((𝔞.map f) ^ j • ⊤ : Ideal S) • ⊤ : Submodule S V))) :=
  ModuleCat.semilinearMapAddEquiv f _ _ (adicQuotientRestrictScalarsQuotientMap f 𝔞 V j)

/-- The `R`-linear map `V/𝔞ʲV → V/(𝔞S)ʲV` induced by the identity of `V` is an isomorphism. -/
instance (V : ModuleCat.{w} S) (j : ℕ) : IsIso (adicQuotientRestrictScalarsQuotientHom f 𝔞 V j) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_adicQuotientRestrictScalarsQuotientMap f 𝔞 V j)

/-- The `R`-linear isomorphism `V/𝔞ʲV ≅ V ⊗_S S/(𝔞S)ʲ`, `[v] ↦ v ⊗ 1`, for an `S`-module `V`. -/
def adicQuotientRestrictScalarsTensorIsoApp (V : ModuleCat.{w} S) (j : ℕ) :
    (adicQuotientModuleSystem R 𝔞 ((ModuleCat.restrictScalars.{w} f).obj V)).obj (op j) ≅
      (ModuleCat.restrictScalars.{w} f).obj
        (V ⊗ (adicQuotientModuleSystem S (𝔞.map f) (ModuleCat.of S S)).obj (op j)) :=
  asIso (adicQuotientRestrictScalarsQuotientHom f 𝔞 V j) ≪≫
    (ModuleCat.restrictScalars.{w} f).mapIso
      (TensorProduct.tensorQuotEquivQuotSMul V ((𝔞.map f) ^ j • ⊤ : Ideal S)).toModuleIso.symm

/-- The isomorphisms `V/𝔞ʲV ≅ V ⊗_S S/(𝔞S)ʲ` are natural in the `S`-module `V`. -/
theorem adicQuotientRestrictScalarsTensorHom_naturality_left {V V' : ModuleCat.{w} S}
    (g : V ⟶ V') (j : ℕ) :
    ((adicQuotientModuleFunctor.{w, w} R 𝔞).map ((ModuleCat.restrictScalars.{w} f).map g)).app
        (op j) ≫ (adicQuotientRestrictScalarsTensorIsoApp f 𝔞 V' j).hom =
      (adicQuotientRestrictScalarsTensorIsoApp f 𝔞 V j).hom ≫
        (ModuleCat.restrictScalars.{w} f).map (g ▷ _) := by
  ext x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- The isomorphisms `V/𝔞ʲV ≅ V ⊗_S S/(𝔞S)ʲ` are compatible with the transition maps in `j`. -/
theorem adicQuotientRestrictScalarsTensorHom_naturality_right (V : ModuleCat.{w} S) {i j : ℕ}
    (hij : i ≤ j) :
    (adicQuotientModuleSystem R 𝔞 ((ModuleCat.restrictScalars.{w} f).obj V)).map
        (homOfLE hij).op ≫ (adicQuotientRestrictScalarsTensorIsoApp f 𝔞 V i).hom =
      (adicQuotientRestrictScalarsTensorIsoApp f 𝔞 V j).hom ≫
        (ModuleCat.restrictScalars.{w} f).map
          (V ◁ (adicQuotientModuleSystem S (𝔞.map f) (ModuleCat.of S S)).map (homOfLE hij).op) := by
  rw [adicQuotientModuleSystem_map, adicQuotientModuleSystem_map]
  ext x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- **Adic quotients of a module under change of rings.** For a ring map `f : R → S`, an ideal
`𝔞 ⊆ R` and an `S`-module `V`, the adic quotients `V/𝔞ʲV` of `V` read over `R` are the
`R`-modules `V ⊗_S S/(𝔞S)ʲ`, naturally in `V` and `j`. -/
def adicQuotientRestrictScalarsTensorIso :
    ModuleCat.restrictScalars.{w} f ⋙ adicQuotientModuleFunctor.{w, w} R 𝔞 ≅
      curriedTensor (ModuleCat.{w} S) ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (adicQuotientModuleSystem S (𝔞.map f) (ModuleCat.of S S)) ⋙
        (Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars.{w} f) :=
  NatIso.ofComponents (fun V => NatIso.ofComponents (fun j =>
      adicQuotientRestrictScalarsTensorIsoApp f 𝔞 V j.unop)
      (fun {j j'} φ => adicQuotientRestrictScalarsTensorHom_naturality_right f 𝔞 V
        (leOfHom φ.unop)))
    (fun g => by
      ext j : 2
      exact adicQuotientRestrictScalarsTensorHom_naturality_left f 𝔞 g j.unop)

end TensorQuotient

section AdicCompletion

variable {Λ : Type w} [CommRing Λ] (I : Ideal Λ)

/-- For a finitely generated ideal `I ⊆ Λ`, the map `Λ/Iʲ → Λ^∧/(IΛ^∧)ʲ` induced by `Λ → Λ^∧` is
bijective. -/
theorem bijective_adicQuotientRestrictScalarsHom_algebraMap (hI : I.FG) (j : ℕ) :
    Function.Bijective (adicQuotientRestrictScalarsHom (algebraMap Λ (AdicCompletion I Λ)) I
      (I.map (algebraMap Λ (AdicCompletion I Λ))) rfl j).hom := by
  have key : ∀ r : Λ, ∀ a : AdicCompletion I Λ,
      algebraMap Λ (AdicCompletion I Λ) r - a ∈
          ((I.map (algebraMap Λ (AdicCompletion I Λ))) ^ j • ⊤ :
            Submodule (AdicCompletion I Λ) (AdicCompletion I Λ)) ↔
        Ideal.Quotient.mk (I ^ j) r = AdicCompletion.evalₐ I j a := by
    intro r a
    have hker := AdicCompletion.ker_evalₐ I hI j
    have hmem := RingHom.mem_ker (f := (AdicCompletion.evalₐ I j).toRingHom)
      (r := algebraMap Λ (AdicCompletion I Λ) r - a)
    rw [hker] at hmem
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, AlgHom.commutes,
      sub_eq_zero] at hmem
    simpa using hmem
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change (Submodule.Quotient.mk (algebraMap Λ (AdicCompletion I Λ) r) :
      AdicCompletion I Λ ⧸ ((I.map (algebraMap Λ (AdicCompletion I Λ))) ^ j • ⊤ :
        Submodule (AdicCompletion I Λ) (AdicCompletion I Λ))) = 0 at hx
    rw [Submodule.Quotient.mk_eq_zero, ← sub_zero (algebraMap Λ _ r), key, map_zero] at hx
    exact (Submodule.Quotient.mk_eq_zero _).2 (by simpa using Ideal.Quotient.eq_zero_iff_mem.1 hx)
  · intro y
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I j a)
    exact ⟨Submodule.Quotient.mk r, (Submodule.Quotient.eq _).2 ((key r a).2 hr)⟩

/-- The maps `R/𝔞ʲ → S/(𝔞S)ʲ` induced by a ring map `R → S` are compatible with the transition
maps. -/
theorem adicQuotientRestrictScalarsHom_naturality {R S : Type w} [CommRing R] [CommRing S]
    (h : R →+* S) (𝔞 : Ideal R) (𝔟 : Ideal S) (h𝔟 : 𝔞.map h = 𝔟) {i j : ℕ} (hij : i ≤ j) :
    (adicQuotientModuleSystem R 𝔞 (ModuleCat.of R R)).map (homOfLE hij).op ≫
        adicQuotientRestrictScalarsHom h 𝔞 𝔟 h𝔟 i =
      adicQuotientRestrictScalarsHom h 𝔞 𝔟 h𝔟 j ≫ (ModuleCat.restrictScalars h).map
        ((adicQuotientModuleSystem S 𝔟 (ModuleCat.of S S)).map (homOfLE hij).op) := by
  rw [adicQuotientModuleSystem_map, adicQuotientModuleSystem_map]
  ext x
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- For a finitely generated ideal `I ⊆ Λ`, the map `Λ/Iʲ → Λ^∧/(IΛ^∧)ʲ` induced by `Λ → Λ^∧` is
an isomorphism of `Λ`-modules. -/
theorem isIso_adicQuotientRestrictScalarsHom_algebraMap (hI : I.FG) (j : ℕ) :
    IsIso (adicQuotientRestrictScalarsHom
    (algebraMap Λ (AdicCompletion I Λ)) I (I.map (algebraMap Λ (AdicCompletion I Λ))) rfl j) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_adicQuotientRestrictScalarsHom_algebraMap I hI j)

/-- **The adic quotients of the completion.** For a finitely generated ideal `I ⊆ Λ`, the tower
`j ↦ Λ/Iʲ` of `Λ`-modules is the tower `j ↦ Λ^∧/(IΛ^∧)ʲ` read over `Λ`. -/
def adicQuotientAdicCompletionIso (hI : I.FG) :
    adicQuotientModuleSystem Λ I (ModuleCat.of Λ Λ) ≅
      adicQuotientModuleSystem (AdicCompletion I Λ) (I.map (algebraMap Λ (AdicCompletion I Λ)))
          (ModuleCat.of (AdicCompletion I Λ) (AdicCompletion I Λ)) ⋙
        ModuleCat.restrictScalars.{w} (algebraMap Λ (AdicCompletion I Λ)) :=
  NatIso.ofComponents (fun j =>
      @asIso _ _ _ _ (adicQuotientRestrictScalarsHom (algebraMap Λ (AdicCompletion I Λ)) I
          (I.map (algebraMap Λ (AdicCompletion I Λ))) rfl j.unop)
        (isIso_adicQuotientRestrictScalarsHom_algebraMap I hI j.unop))
    (fun φ => adicQuotientRestrictScalarsHom_naturality _ _ _ rfl (leOfHom φ.unop))

end AdicCompletion

end AlgebraicGeometry.ProEtale

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed
  CochainComplex.braidedCategory derivedMonoidal

open AlgebraicGeometry.ProEtale

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [UnivLE.{max u v, w}]

section Restrict

variable {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S) (𝔞 : Ideal R)

variable (J) in
/-- **Constant adic quotients under change of rings, as functors of the module.** For a ring map
`f : R → S`, an ideal `𝔞 ⊆ R` and an `S`-module `V`, the constant sheaf `\underline{V/𝔞ʲV}` of
`R`-modules is the restriction of scalars of `\underline{V} ⊗_S \underline{S/(𝔞S)ʲ}`, naturally in
`V` and `j`. -/
def constantAdicQuotientRestrictScalarsIso :
    ModuleCat.restrictScalars.{w} f ⋙ adicQuotientModuleFunctor.{w, w} R 𝔞 ⋙
        (Functor.whiskeringRight _ _ _).obj (constantSheaf J (ModuleCat.{w} R)) ≅
      constantSheaf J (ModuleCat.{w} S) ⋙ curriedTensor (Sheaf J (ModuleCat.{w} S)) ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (adicQuotientModuleSystem S (𝔞.map f) (ModuleCat.of S S) ⋙
            constantSheaf J (ModuleCat.{w} S)) ⋙
        (Functor.whiskeringRight _ _ _).obj (restrictScalars J f) :=
  let Y := adicQuotientModuleSystem S (𝔞.map f) (ModuleCat.of S S)
  let T := curriedTensor (ModuleCat.{w} S)
  Functor.isoWhiskerRight (adicQuotientRestrictScalarsTensorIso f 𝔞)
      ((Functor.whiskeringRight _ _ _).obj (constantSheaf J (ModuleCat.{w} R))) ≪≫
    (Iso.refl _ : (T ⋙ (Functor.whiskeringLeft _ _ _).obj Y ⋙
        (Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars.{w} f)) ⋙
          (Functor.whiskeringRight _ _ _).obj (constantSheaf J (ModuleCat.{w} R)) ≅
      T ⋙ (Functor.whiskeringLeft _ _ _).obj Y ⋙ (Functor.whiskeringRight _ _ _).obj
        (ModuleCat.restrictScalars.{w} f ⋙ constantSheaf J (ModuleCat.{w} R))) ≪≫
    Functor.isoWhiskerLeft (T ⋙ (Functor.whiskeringLeft _ _ _).obj Y)
      ((Functor.whiskeringRight _ _ _).mapIso (restrictScalarsConstantSheafIso J f).symm) ≪≫
    (Iso.refl _ : T ⋙ (Functor.whiskeringLeft _ _ _).obj Y ⋙ (Functor.whiskeringRight _ _ _).obj
        (constantSheaf J (ModuleCat.{w} S) ⋙ restrictScalars J f) ≅
      (T ⋙ (Functor.whiskeringRight _ _ _).obj (constantSheaf J (ModuleCat.{w} S))) ⋙
        (Functor.whiskeringLeft _ _ _).obj Y ⋙
          (Functor.whiskeringRight _ _ _).obj (restrictScalars J f)) ≪≫
    Functor.isoWhiskerRight (constantSheafTensorIso (J := J) (A := S))
      ((Functor.whiskeringLeft _ _ _).obj Y ⋙
        (Functor.whiskeringRight _ _ _).obj (restrictScalars J f))

variable (J) in
/-- **The tower of constant adic quotients of a complex under change of rings.** For a ring map
`f : R → S`, an ideal `𝔞 ⊆ R` and a complex `M` of `S`-modules, the tower
`j ↦ \underline{M/𝔞ʲM}` of constant complexes of sheaves of `R`-modules (with `M` read over `R`)
is the restriction of scalars of the tower `j ↦ \underline{M} ⊗_S \underline{S/(𝔞S)ʲ}` of
termwise reductions of the constant complex `\underline{M}`. -/
def constantAdicQuotientComplexTowerRestrictScalarsIso (M : CochainComplex (ModuleCat.{w} S) ℤ) :
    constantAdicQuotientComplexTower J R 𝔞
        (((ModuleCat.restrictScalars.{w} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≅
      rowAdicTower J (𝔞.map f) (((constantSheaf J (ModuleCat.{w} S)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ⋙
        (restrictScalars J f).mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.ofComponents (fun j => HomologicalComplex.Hom.isoOfComponents
      (fun p => ((constantAdicQuotientRestrictScalarsIso J f 𝔞).app (M.X p)).app j)
      (fun p q _ => (NatTrans.congr_app
        ((constantAdicQuotientRestrictScalarsIso J f 𝔞).hom.naturality (M.d p q)) j).symm))
    (fun φ => HomologicalComplex.hom_ext _ _ fun p =>
      ((constantAdicQuotientRestrictScalarsIso J f 𝔞).hom.app (M.X p)).naturality φ)

end Restrict

section Derived

variable {Λ : Type w} [CommRing Λ] [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]

variable (J) in
/-- **Derived reductions of a K-flat complex are termwise reductions.** For a left K-flat complex
`P` of sheaves of `Λ`-modules, the tower of derived reductions `j ↦ P ⊗_Λ^L \underline{Λ/Iʲ}` is
the tower `j ↦ P ⊗_Λ \underline{Λ/Iʲ}` of termwise reductions. -/
def derivedReductionTowerIsoRowAdicTower (I : Ideal Λ)
    {P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (hP : KFlatLeft (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) P) :
    derivedReductionTower J Λ I (DerivedCategory.Q.obj P) ≅
      rowAdicTower J I P ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft (constantAdicQuotientTower J Λ I (ModuleCat.of Λ Λ))
    (Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ _ 0)
        (tensorLeft (DerivedCategory.Q.obj P)) ≪≫ derivedTensorSingleIso hP)

end Derived

/-- **Λ-transfer of towers of reductions.** Let `Λ` be Noetherian, `I ⊆ Λ` an ideal, `P` a K-flat
complex of sheaves of `Λ`-modules and `M` a complex of `Λ^∧`-modules. An isomorphism in
`D(C, Λ^∧)` between the towers `j ↦ (Λ^∧ ⊗_Λ P) ⊗ \underline{Λ^∧/(IΛ^∧)ʲ}` and
`j ↦ \underline{M} ⊗ \underline{Λ^∧/(IΛ^∧)ʲ}` of termwise reductions yields an isomorphism in
`D(C, Λ)` between the tower of derived reductions `j ↦ P ⊗_Λ^L \underline{Λ/Iʲ}` and the tower
`j ↦ \underline{M/IʲM}` of constant complexes, `M` being read over `Λ`. -/
theorem nonempty_derivedReductionTower_iso_of_rowAdicTower_iso {Λ : Type w} [CommRing Λ]
    [IsNoetherianRing Λ] (I : Ideal Λ)
    [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]
    [HasDerivedCategory.{t'} (Sheaf J (ModuleCat.{w} (AdicCompletion I Λ)))]
    {P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (hP : KFlat (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) P)
    (M : CochainComplex (ModuleCat.{w} (AdicCompletion I Λ)) ℤ)
    (φ : rowAdicTower J (I.map (algebraMap Λ (AdicCompletion I Λ)))
        (((extendScalars J (algebraMap Λ (AdicCompletion I Λ))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ⋙ DerivedCategory.Q ≅
      rowAdicTower J (I.map (algebraMap Λ (AdicCompletion I Λ)))
        (((constantSheaf J (ModuleCat.{w} (AdicCompletion I Λ))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ⋙ DerivedCategory.Q) :
    Nonempty (derivedReductionTower J Λ I (DerivedCategory.Q.obj P) ≅
      constantAdicQuotientComplexTower J Λ I
        (((ModuleCat.restrictScalars (algebraMap Λ (AdicCompletion I Λ))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ⋙ DerivedCategory.Q) :=
  let ι := algebraMap Λ (AdicCompletion I Λ)
  let resD := (restrictScalars J ι).mapDerivedCategory
  ⟨derivedReductionTowerIsoRowAdicTower J I
      (CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat _ hP) ≪≫
    Functor.isoWhiskerRight (rowAdicTowerIsoRestrictScalars J ι I
      (adicQuotientAdicCompletionIso I (IsNoetherian.noetherian I)) P) DerivedCategory.Q ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (restrictScalars J ι).mapDerivedCategoryFactors.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight φ resD ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (restrictScalars J ι).mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (constantAdicQuotientComplexTowerRestrictScalarsIso J ι I M).symm
      DerivedCategory.Q⟩

end Stacks.ModuleSheaf

end
