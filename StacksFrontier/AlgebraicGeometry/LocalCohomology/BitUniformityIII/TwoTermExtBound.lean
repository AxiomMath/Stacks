module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DivisibleMaps
public import StacksFrontier.Homology.TwoTermComplex.Representative
public import StacksFrontier.Homology.TwoTermComplex.SmulIdZero
import StacksCore.Tactic.StacksAttribute

/-!
# Killing `Ext¹` out of a two-term complex by twisting the coefficients down

This file holds the algebraic ingredients of Stacks Tag 0GAD, the last lemma of the section
*A bit of uniformity, III* of the chapter *Local Cohomology* (Tag 0GA6). Tag 0GAD itself is
`Stacks.LocalCohomology.UniformityIII.ext_one_powQuot_map_eq_zero_blowup`.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace TwoTermComplex

attribute [local instance] HasDerivedCategory.standard

section Coefficients

variable {R : Type u} [CommRing R]

/-- The chain map `N[1] ⟶ N'[1]` induced by a map `u : N ⟶ N'` of modules. -/
noncomputable def shiftSingleMap {N N' : ModuleCat.{v} R} (u : N ⟶ N') :
    TwoTermComplexExt.shiftSingle N 1 ⟶ TwoTermComplexExt.shiftSingle N' 1 :=
  (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{v} R) ℤ) (1 : ℤ)).map
    ((HomologicalComplex.single (ModuleCat.{v} R) (ComplexShape.up ℤ) 0).map u)

/-- The degree `-1` term of `N[1]` is `N`. -/
noncomputable def shiftSingleXNegOne (N : ModuleCat.{v} R) :
    (TwoTermComplexExt.shiftSingle N 1).X (-1) ≅ N :=
  HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N

/-- In the one degree where `N[1]` is nonzero, `N[1] ⟶ N'[1]` is `u`. -/
theorem shiftSingleMap_f_neg_one {N N' : ModuleCat.{v} R} (u : N ⟶ N') :
    (shiftSingleMap u).f (-1) =
      (shiftSingleXNegOne N).hom ≫ u ≫ (shiftSingleXNegOne N').inv := by
  have h : (shiftSingleMap u).f (-1) =
      ((HomologicalComplex.single (ModuleCat.{v} R) (ComplexShape.up ℤ) 0).map u).f 0 := rfl
  rw [h, HomologicalComplex.single_map_f_self]
  rfl

variable [Small.{v} R]

/-- The comparison isomorphism `Q(N[1]) ≅ (N[0])⟦1⟧` between the two ways of placing a module
in degree `-1` of the derived category. -/
noncomputable def singleShiftIso (N : ModuleCat.{v} R) :
    DerivedCategory.Q.obj (TwoTermComplexExt.shiftSingle N 1) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N)⟦(1 : ℤ)⟧ :=
  ((DerivedCategory.Q (C := ModuleCat.{v} R)).commShiftIso (1 : ℤ)).app
    ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj N)

omit [Small.{v} R] in
/-- The comparison isomorphism `Q(N[1]) ≅ (N[0])⟦1⟧` is natural in `N`. -/
theorem singleShiftIso_naturality {N N' : ModuleCat.{v} R} (u : N ⟶ N') :
    (singleShiftIso N).hom ≫
        (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{v} R)) (1 : ℤ)).map
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).map u) =
      DerivedCategory.Q.map (shiftSingleMap u) ≫ (singleShiftIso N').hom :=
  (((DerivedCategory.Q (C := ModuleCat.{v} R)).commShiftIso (1 : ℤ)).hom.naturality
    ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map u)).symm

/-- **The coefficient-twisting criterion.** Let `L = (L⁻¹ → L⁰)` be a two-term complex with
projective degree-zero term representing an object `K` of `D(R)`, and let `u : N ⟶ N'` be a map
of `R`-modules. If every homomorphism `L⁻¹ → N`, composed with `u`, factors through the
differential of `L`, then the map `Ext¹_R(K, N) → Ext¹_R(K, N')` induced by `u` vanishes.

Morphisms out of `L` in `D(R)` are homotopy classes of chain maps because `L⁰` is projective
(Stacks 0ALN part (1)), so a class in `Ext¹_R(K, N)` is a map `L⁻¹ → N`, and its image in
`Ext¹_R(K, N')` vanishes exactly when the composite with `u` is null-homotopic, which is the
assumed factorization. -/
theorem ext_one_map_eq_zero_of_forall_factorization
    {K : DerivedCategory (ModuleCat.{v} R)}
    (L : CochainComplex (ModuleCat.{v} R) ℤ)
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0] [Projective (L.X 0)]
    (e : DerivedCategory.Q.obj L ≅ K)
    {N N' : ModuleCat.{v} R} (u : N ⟶ N')
    (hfac : ∀ φ : L.X (-1) ⟶ N, ∃ ψ : L.X 0 ⟶ N', L.d (-1) 0 ≫ ψ = φ ≫ u)
    (ξ : DerivedCategory.Ext K ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) 1) :
    ξ ≫ (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{v} R)) (1 : ℤ)).map
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).map u) = 0 := by
  have hLpos : ∀ i : ℤ, 0 < i → IsZero (L.X i) := fun i hi =>
    CochainComplex.isZero_of_isStrictlyLE L 0 i hi
  have hTzero : ∀ i ≤ (-2 : ℤ), IsZero ((TwoTermComplexExt.shiftSingle N 1).X i) := by
    intro i hi
    exact TwoTermComplexExt.isZero_shiftSingle_X (by omega)
  -- Represent the class by a chain map `L ⟶ N[1]`.
  set ζ : TwoTermComplexExt.ExtMod L N 1 := e.hom ≫ ξ ≫ (singleShiftIso N).inv with hζ
  obtain ⟨fK, hfK⟩ :=
    (TwoTermComplexExt.toHomD_bijective L (TwoTermComplexExt.shiftSingle N 1) hLpos
      inferInstance hTzero).2 ζ
  obtain ⟨f, hf⟩ :=
    (HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map_surjective fK
  have hζf : ζ = DerivedCategory.Q.map f := by
    have hfK' : TwoTermComplexExt.toHomD fK = ζ := hfK
    rw [← hfK', ← hf, TwoTermComplexExt.toHomD_quotient_map]
  -- The factorization hypothesis, applied to the degree `-1` component.
  obtain ⟨ψ, hψ⟩ := hfac (f.f (-1) ≫ (shiftSingleXNegOne N).hom)
  -- The composite chain map `L ⟶ N'[1]` is null-homotopic.
  have hneg : (f ≫ shiftSingleMap u).f (-1) =
      L.d (-1) 0 ≫ (ψ ≫ (shiftSingleXNegOne N').inv) +
        (0 : L ⟶ TwoTermComplexExt.shiftSingle N' 1).f (-1) := by
    rw [HomologicalComplex.comp_f, shiftSingleMap_f_neg_one, HomologicalComplex.zero_f,
      add_zero, ← Category.assoc (L.d (-1) 0) ψ, hψ]
    simp only [Category.assoc]
  have hzero0 : (f ≫ shiftSingleMap u).f 0 =
      (ψ ≫ (shiftSingleXNegOne N').inv) ≫ (TwoTermComplexExt.shiftSingle N' 1).d (-1) 0 +
        (0 : L ⟶ TwoTermComplexExt.shiftSingle N' 1).f 0 :=
    (TwoTermComplexExt.isZero_shiftSingle_X
      (N := N') (j := (1 : ℤ)) (i := (0 : ℤ)) (by omega)).eq_of_tgt _ _
  have hzero : DerivedCategory.Q.map (f ≫ shiftSingleMap u) = 0 := by
    obtain ⟨H⟩ := nonempty_homotopy_of_twoTerm_components
      (f := f ≫ shiftSingleMap u) (g := 0)
      (ψ ≫ (shiftSingleXNegOne N').inv) hneg hzero0
    simpa using DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{v} R) H
  -- Transport back through the comparison isomorphisms.
  rw [← cancel_epi e.hom]
  have key : e.hom ≫ ξ = ζ ≫ (singleShiftIso N).hom := by
    rw [hζ, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Limits.comp_zero, ← Category.assoc, key, Category.assoc,
    singleShiftIso_naturality u, hζf, ← Category.assoc, ← Functor.map_comp, hzero,
    Limits.zero_comp]

end Coefficients

end TwoTermComplex

namespace Stacks.LocalCohomology.UniformityIII

open CategoryTheory CategoryTheory.Limits

section PowQuotModule

variable {A : Type u} [CommRing A] (I : Ideal A) (q n : ℕ)

/-- `Iⁿ` annihilates the subquotient `I^q/I^{q+n}`. -/
theorem isTorsionBySet_powQuot :
    Module.IsTorsionBySet A (powQuot I q n) ((I ^ n : Ideal A) : Set A) := by
  intro x a
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    change (Submodule.Quotient.mk ((a : A) • y) : powQuot I q n) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    simp only [powSub, Submodule.mem_comap, Submodule.coe_subtype, SetLike.val_smul,
      smul_eq_mul]
    have h : (a : A) * (y : A) ∈ I ^ n * I ^ q := Ideal.mul_mem_mul a.2 y.2
    rw [← pow_add] at h
    exact Ideal.pow_le_pow_right (by omega) h

/-- The subquotient `I^q/I^{q+n}` of `A` as a module over `A/Iⁿ`, which annihilates it. -/
noncomputable instance powQuotModule : Module (A ⧸ I ^ n) (powQuot I q n) :=
  (isTorsionBySet_powQuot I q n).module

@[simp] theorem powQuot_mk_smul (a : A) (x : powQuot I q n) :
    (Ideal.Quotient.mk (I ^ n) a) • x = a • x := rfl

/-- The subquotient `I^q/I^{q+n}` of `A` as an object of the category of `A/Iⁿ`-modules. -/
noncomputable abbrev powQuotObj : ModuleCat.{u} (A ⧸ I ^ n) :=
  ModuleCat.of (A ⧸ I ^ n) (powQuot I q n)

variable {M : ModuleCat.{u} (A ⧸ I ^ n)}

/-- An `A`-linear map out of the underlying `A`-module of an `A/Iⁿ`-module `M` into `I^q/I^{q+n}`
is the same thing as an `A/Iⁿ`-linear map `M ⟶ I^q/I^{q+n}`. -/
noncomputable def ofResHom (φ : resModule I n M →ₗ[A] powQuot I q n) : M ⟶ powQuotObj I q n :=
  ModuleCat.ofHom
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun r x => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        exact φ.map_smul a x }

/-- The `A`-linear map underlying an `A/Iⁿ`-linear map `M ⟶ I^q/I^{q+n}`. -/
noncomputable def toResHom (θ : M ⟶ powQuotObj I q n) : resModule I n M →ₗ[A] powQuot I q n where
  toFun := θ.hom
  map_add' := θ.hom.map_add
  map_smul' a z := by
    have h : θ.hom (a • z) = (Ideal.Quotient.mk (I ^ n) a) • θ.hom z := by
      rw [ModuleCat.restrictScalars.smul_def]
      exact map_smul θ.hom _ z
    rw [h, powQuot_mk_smul, RingHom.id_apply]

@[simp] theorem toResHom_ofResHom (φ : resModule I n M →ₗ[A] powQuot I q n) :
    toResHom I q n (ofResHom I q n φ) = φ := rfl

@[simp] theorem ofResHom_apply (φ : resModule I n M →ₗ[A] powQuot I q n) (x : M) :
    (ofResHom I q n φ).hom x = φ x := rfl

@[simp] theorem toResHom_apply (θ : M ⟶ powQuotObj I q n) (x : M) :
    toResHom I q n θ x = θ.hom x := rfl

/-- The canonical map `I^q/I^{q+n} ⟶ I^{q'}/I^{q'+n}` for `q' ≤ q`, as a map of
`A/Iⁿ`-modules. -/
noncomputable def powQuotLeHom {q q' : ℕ} (h : q' ≤ q) :
    powQuotObj I q n ⟶ powQuotObj I q' n :=
  ofResHom I q' n (powQuotLe I h)

@[simp] theorem powQuotLeHom_apply {q q' : ℕ} (h : q' ≤ q) (x : powQuot I q n) :
    (powQuotLeHom I n h).hom x = powQuotLe I h x := rfl

end PowQuotModule

/-- Multiplying by `a ∈ I^c` from `I^g/I^{g+n}` into `I^f/I^{f+n}` and twisting back down to
`I^g/I^{g+n}` is multiplication by `a`. -/
theorem powQuotLe_powQuotSmul {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ) {a : A} {c g f : ℕ}
    (ha : a ∈ I ^ c) (hgf : g + c = f) (x : powQuot I g n) :
    powQuotLe I (Nat.le.intro hgf) (powQuotSmul I ha hgf x) = a • x := by
  induction x using Submodule.Quotient.induction_on with
  | H y => rfl

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {n c : ℕ}

attribute [local instance] HasDerivedCategory.standard

/-- The `A`-linear map underlying an `A/Iⁿ`-linear map of `A/Iⁿ`-modules. -/
noncomputable def resMap (I : Ideal A) (n : ℕ) {M P : ModuleCat.{u} (A ⧸ I ^ n)} (θ : M ⟶ P) :
    resModule I n M →ₗ[A] resModule I n P :=
  ((ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).map θ).hom

omit [IsNoetherianRing A] in
/-- The degree `-1` term of a two-term complex over `A/Iⁿ` whose degree `0` term is finite free
and for which multiplication by every element of `I^c/Iⁿ` factors through the differential is an
`(A, n, c)`-module: it is finite, and multiplication by `a ∈ I^c` on it factors through the
finite free module in degree `0`. -/
theorem isANCModule_X_neg_one (L : CochainComplex (ModuleCat.{u} (A ⧸ I ^ n)) ℤ)
    (hfin : Module.Finite (A ⧸ I ^ n) (L.X (-1))) (hfree : Module.Free (A ⧸ I ^ n) (L.X 0))
    (hfac : ∀ a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c),
      ∃ h : L.X 0 ⟶ L.X (-1), L.d (-1) 0 ≫ h = a • 𝟙 (L.X (-1))) :
    IsANCModule I n c (L.X (-1)) := by
  refine ⟨hfin, fun a ha => ?_⟩
  obtain ⟨h, hh⟩ := hfac a ha
  have hfree' : Module.Free (A ⧸ I ^ n) (L.X 0) := hfree
  refine ⟨L.X 0, inferInstance, inferInstance, inferInstance,
    (L.d (-1) 0).hom, h.hom, LinearMap.ext fun z => ?_⟩
  have hz : (L.d (-1) 0 ≫ h).hom z = (a • 𝟙 (L.X (-1))).hom z := by rw [hh]
  simpa using hz.symm

end Main

end Stacks.LocalCohomology.UniformityIII

end
