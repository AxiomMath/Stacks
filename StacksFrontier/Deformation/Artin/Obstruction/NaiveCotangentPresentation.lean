module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Obstruction
public import StacksFrontier.Homology.DoubleExtend
public import StacksFrontier.RingTheory.NaiveCotangent.Defs
public import StacksFrontier.RingTheory.NaiveCotangent.TwoTermDoubleQuasiIso

/-!
# Presentation independence of the derived naive cotangent complex

The naive cotangent complex `NL_{A/Λ}` of a ring map may be computed from any presentation
`α : P → A` of `A` as a quotient of a polynomial algebra over `Λ`: a morphism of
presentations exists, induces a chain map of the associated two-term complexes
`I/I² → Ω_{P/Λ} ⊗_P A`, and is unique up to homotopy, so that comparing a presentation with
the canonical one gives a homotopy equivalence. Passing to the derived category, where
homotopic morphisms of complexes become equal, turns that homotopy equivalence into an
isomorphism.

A two-term complex of modules is placed as a cochain complex in degrees `-1` and `0`, and a
homotopy of chain maps of two-term complexes is a `Homotopy` of the associated morphisms of
cochain complexes.

## Main definitions

* `Deformation.Artin.twoTermComplex`: a two-term complex of `A`-modules as a cochain complex
  concentrated in degrees `-1` and `0`.
* `Deformation.Artin.twoTermHom`: the morphism of cochain complexes induced by a chain map of
  two-term complexes.
* `Deformation.Artin.twoTermHomotopy`: a homotopy of chain maps of two-term complexes of
  modules, as a homotopy of the associated morphisms of cochain complexes.
* `Deformation.Artin.twoTermHomotopyEquiv`: the homotopy equivalence of cochain complexes
  induced by a homotopy equivalence of two-term complexes.
* `Deformation.Artin.derivedNaiveCotangentComplexIso`: for any presentation of `A` over `Λ`,
  the isomorphism `NL(α) ≅ NL_{A/Λ}` in the derived category of `A`-modules given by the
  comparison with the canonical presentation.
* `Deformation.Artin.twoTermTriangle` and `Deformation.Artin.twoTermComplexTriangle`: the
  triangle `M[0] ⟶ (N ⟶ M) ⟶ N[-1] ⟶ M[0]⟦1⟧` of a two-term complex `d : N ⟶ M` in the derived
  category of `A`-modules.

## Main results

* `Deformation.Artin.quasiIso_twoTermHom`: a chain map of two-term complexes which is a
  homotopy equivalence induces a quasi-isomorphism of cochain complexes.
* `Deformation.Artin.isIso_Q_map_twoTermHom`: such a chain map becomes an isomorphism in the
  derived category.
* `Deformation.Artin.shortExact_twoTermShortComplex`: for a two-term complex `d : N ⟶ M` the
  sequence `0 → M[0] → (N ⟶ M) → N[-1] → 0` of cochain complexes is short exact.
* `Deformation.Artin.twoTermTriangle_distinguished` and
  `Deformation.Artin.twoTermComplexTriangle_distinguished`: the triangle of a two-term complex
  is distinguished.

## References

* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated NaiveCotangent HomologicalComplex
open ComplexShape (upIntRelNegOneZero)

namespace Deformation.Artin

universe u

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]

/-- A two-term complex of `A`-modules, placed in cohomological degrees `-1` and `0`. -/
public abbrev twoTermComplex (T : TwoTerm.{u, u, u} A) : CochainComplex (ModuleCat.{u} A) ℤ :=
  double (ModuleCat.ofHom T.d) upIntRelNegOneZero

/-- The morphism of two-term complexes induced by a chain map. -/
public def twoTermHom {T T' : TwoTerm.{u, u, u} A} (f : ChainMap T T') :
    twoTermComplex T ⟶ twoTermComplex T' :=
  Stacks.TwoTermDoubleQuasiIso.mapDouble f upIntRelNegOneZero

/-- In degree `-1`, `twoTermHom f` is `f.f₁`, read through the degree isomorphisms `doubleXIso₀`
of the two complexes. -/
@[simp] public theorem twoTermHom_f_neg_one {T T' : TwoTerm.{u, u, u} A} (f : ChainMap T T') :
    (twoTermHom f).f (-1) =
      (doubleXIso₀ (ModuleCat.ofHom T.d) upIntRelNegOneZero).hom ≫ ModuleCat.ofHom f.f₁ ≫
        (doubleXIso₀ (ModuleCat.ofHom T'.d) upIntRelNegOneZero).inv :=
  Stacks.TwoTermDoubleQuasiIso.mapDouble_f_negOne f upIntRelNegOneZero

/-- In degree `0`, `twoTermHom f` is `f.f₀`, read through the degree isomorphisms `doubleXIso₁`
of the two complexes. -/
@[simp] public theorem twoTermHom_f_zero {T T' : TwoTerm.{u, u, u} A} (f : ChainMap T T') :
    (twoTermHom f).f 0 =
      (doubleXIso₁ (ModuleCat.ofHom T.d) upIntRelNegOneZero (by omega)).hom ≫
        ModuleCat.ofHom f.f₀ ≫
        (doubleXIso₁ (ModuleCat.ofHom T'.d) upIntRelNegOneZero (by omega)).inv :=
  Stacks.TwoTermDoubleQuasiIso.mapDouble_f_zero f upIntRelNegOneZero

/-- `twoTermHom` sends the identity chain map to the identity. -/
public theorem twoTermHom_id (T : TwoTerm.{u, u, u} A) :
    twoTermHom (ChainMap.id T) = 𝟙 (twoTermComplex T) := by
  apply from_double_hom_ext <;> simp [ChainMap.id, twoTermComplex]

/-- `twoTermHom` sends a composite of chain maps to the composite of the induced morphisms. -/
public theorem twoTermHom_comp {T T' T'' : TwoTerm.{u, u, u} A} (f : ChainMap T T')
    (g : ChainMap T' T'') :
    twoTermHom (g.comp f) = twoTermHom f ≫ twoTermHom g := by
  apply from_double_hom_ext <;> simp [ChainMap.comp, twoTermComplex]

/-- A homotopy of chain maps of two-term complexes, given by `h` with
`f₁ - g₁ = h ∘ d` and `f₀ - g₀ = d' ∘ h`, is a homotopy of the induced morphisms of cochain
complexes, concentrated in the single component from degree `0` to degree `-1`. -/
public def twoTermHomotopy {T T' : TwoTerm.{u, u, u} A} {f g : ChainMap T T'}
    (h : T.X₀ →ₗ[A] T'.X₁) (h₁ : f.f₁ - g.f₁ = h ∘ₗ T.d) (h₀ : f.f₀ - g.f₀ = T'.d ∘ₗ h) :
    Homotopy (twoTermHom f) (twoTermHom g) where
  hom i j :=
    if hij : i = 0 ∧ j = -1 then
      eqToHom (by rw [hij.1]) ≫
        (doubleXIso₁ (ModuleCat.ofHom T.d) upIntRelNegOneZero (by omega)).hom ≫
        ModuleCat.ofHom h ≫
        (doubleXIso₀ (ModuleCat.ofHom T'.d) upIntRelNegOneZero).inv ≫
        eqToHom (by rw [hij.2])
    else 0
  zero i j hr := by
    rw [dite_eq_right]
    rintro ⟨rfl, rfl⟩
    exact absurd rfl hr
  comm i := by
    have key₁ : ModuleCat.ofHom f.f₁ =
        ModuleCat.ofHom T.d ≫ ModuleCat.ofHom h + ModuleCat.ofHom g.f₁ := by
      apply ModuleCat.hom_ext
      ext x
      have hx := congrArg (fun m => m x) h₁
      simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply] at hx
      simpa using sub_eq_iff_eq_add.mp hx
    have key₀ : ModuleCat.ofHom f.f₀ =
        ModuleCat.ofHom h ≫ ModuleCat.ofHom T'.d + ModuleCat.ofHom g.f₀ := by
      apply ModuleCat.hom_ext
      ext x
      have hx := congrArg (fun m => m x) h₀
      simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply] at hx
      simpa using sub_eq_iff_eq_add.mp hx
    by_cases hi : i = -1
    · subst hi
      rw [dNext_eq _ upIntRelNegOneZero,
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (-2) (-1) by decide), twoTermHom_f_neg_one,
        twoTermHom_f_neg_one, key₁, double_d _ _ (by omega : (-1 : ℤ) ≠ 0)]
      simp [Preadditive.comp_add, Preadditive.add_comp]
    by_cases hi0 : i = 0
    · subst hi0
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by decide),
        prevD_eq _ upIntRelNegOneZero, twoTermHom_f_zero, twoTermHom_f_zero, key₀,
        double_d_eq_zero₀ _ _ 0 1 (by omega),
        double_d (ModuleCat.ofHom T'.d) upIntRelNegOneZero (by omega)]
      simp [Preadditive.comp_add, Preadditive.add_comp]
    exact (isZero_double_X (ModuleCat.ofHom T.d) upIntRelNegOneZero i hi hi0).eq_of_src _ _

/-- A homotopy equivalence of two-term complexes of modules induces one of the associated
cochain complexes. -/
public def twoTermHomotopyEquiv {T T' : TwoTerm.{u, u, u} A} {f : ChainMap T T'}
    (hf : IsHomotopyEquiv f) : HomotopyEquiv (twoTermComplex T) (twoTermComplex T') where
  hom := twoTermHom f
  inv := twoTermHom hf.choose
  homotopyHomInvId := by
    rw [← twoTermHom_comp, ← twoTermHom_id T]
    exact twoTermHomotopy hf.choose_spec.1.choose hf.choose_spec.1.choose_spec.1
      hf.choose_spec.1.choose_spec.2
  homotopyInvHomId := by
    rw [← twoTermHom_comp, ← twoTermHom_id T']
    exact twoTermHomotopy hf.choose_spec.2.choose hf.choose_spec.2.choose_spec.1
      hf.choose_spec.2.choose_spec.2

/-- A chain map of two-term complexes which is a homotopy equivalence is a
quasi-isomorphism of the associated cochain complexes. -/
public theorem quasiIso_twoTermHom {T T' : TwoTerm.{u, u, u} A} {f : ChainMap T T'}
    (hf : IsHomotopyEquiv f) : QuasiIso (twoTermHom f) :=
  show QuasiIso (twoTermHomotopyEquiv hf).hom from inferInstance

/-- A chain map of two-term complexes which is a homotopy equivalence becomes an
isomorphism in the derived category. -/
public theorem isIso_Q_map_twoTermHom {T T' : TwoTerm.{u, u, u} A} {f : ChainMap T T'}
    (hf : IsHomotopyEquiv f) : IsIso (DerivedCategory.Q.map (twoTermHom f)) :=
  have := quasiIso_twoTermHom hf
  inferInstance

/-- Homotopic chain maps of two-term complexes have the same image in the derived category. -/
public theorem Q_map_twoTermHom_eq_of_homotopic {T T' : TwoTerm.{u, u, u} A}
    {f g : ChainMap T T'} (h : Homotopic f g) :
    DerivedCategory.Q.map (twoTermHom f) = DerivedCategory.Q.map (twoTermHom g) := by
  obtain ⟨s, h₁, h₀⟩ := h
  exact DerivedCategory.Q_map_eq_of_homotopy _ (twoTermHomotopy s h₁ h₀)

/-! ### The distinguished triangle of a two-term complex -/

section Triangle

variable {N M : ModuleCat.{u} A}

/-- The inclusion of the degree-zero term `M` of a two-term complex `d : N ⟶ M`, placed in
cohomological degree `0`, into the complex. -/
public def twoTermInclusion (d : N ⟶ M) :
    (single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj M ⟶ double d upIntRelNegOneZero :=
  mkHomFromSingle (doubleXIso₁ d upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero).inv
    (fun k _ => by
      rw [double_d_eq_zero₀ d upIntRelNegOneZero 0 k (by omega), Limits.comp_zero])

/-- The projection of a two-term complex `d : N ⟶ M` onto its degree `-1` term `N`, placed in
cohomological degree `-1`. -/
public def twoTermProjection (d : N ⟶ M) :
    double d upIntRelNegOneZero ⟶
      (single (ModuleCat.{u} A) (ComplexShape.up ℤ) (-1)).obj N :=
  mkHomToSingle (doubleXIso₀ d upIntRelNegOneZero).hom
    (fun i _ => by
      rw [double_d_eq_zero₁ d upIntRelNegOneZero i (-1) NaiveCotangent.TwoTerm.negOne_ne_zero,
        Limits.zero_comp])

/-- In degree `0`, `twoTermInclusion d` is the inverse of the degree isomorphism of the two-term
complex, read through the degree isomorphism of the single complex. -/
@[simp] public theorem twoTermInclusion_f_zero (d : N ⟶ M) :
    (twoTermInclusion d).f 0 = (singleObjXSelf (ComplexShape.up ℤ) 0 M).hom ≫
      (doubleXIso₁ d upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero).inv :=
  mkHomFromSingle_f ..

/-- In degree `-1`, `twoTermProjection d` is the degree isomorphism of the two-term complex,
read through the degree isomorphism of the single complex. -/
@[simp] public theorem twoTermProjection_f_neg_one (d : N ⟶ M) :
    (twoTermProjection d).f (-1) = (doubleXIso₀ d upIntRelNegOneZero).hom ≫
      (singleObjXSelf (ComplexShape.up ℤ) (-1) N).inv :=
  mkHomToSingle_f ..

/-- The inclusion of the degree-zero term followed by the projection onto the degree `-1` term
is zero. -/
public theorem twoTermInclusion_comp_twoTermProjection (d : N ⟶ M) :
    twoTermInclusion d ≫ twoTermProjection d = 0 := by
  apply from_single_hom_ext
  exact (isZero_single_obj_X (ComplexShape.up ℤ) (-1) N 0 (by omega)).eq_of_tgt _ _

/-- The degreewise split short complex `M[0] ⟶ (N ⟶ M) ⟶ N[-1]` of cochain complexes
attached to a two-term complex. -/
public def twoTermShortComplex (d : N ⟶ M) :
    ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ) :=
  ShortComplex.mk (twoTermInclusion d) (twoTermProjection d)
    (twoTermInclusion_comp_twoTermProjection d)

/-- In degree `0` the short complex of a two-term complex is `M → M → 0`. -/
public def twoTermSplitting₀ (d : N ⟶ M) :
    ((twoTermShortComplex d).map (eval (ModuleCat.{u} A) (ComplexShape.up ℤ) 0)).Splitting where
  r := (doubleXIso₁ d upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero).hom ≫
    (singleObjXSelf (ComplexShape.up ℤ) 0 M).inv
  s := 0
  f_r := by simp [twoTermShortComplex]
  s_g := (isZero_single_obj_X (ComplexShape.up ℤ) (-1) N 0 (by omega)).eq_of_src _ _
  id := by
    rw [Limits.comp_zero, add_zero]
    simp [twoTermShortComplex]

/-- In degree `-1` the short complex of a two-term complex is `0 → N → N`. -/
public def twoTermSplitting₁ (d : N ⟶ M) :
    ((twoTermShortComplex d).map
      (eval (ModuleCat.{u} A) (ComplexShape.up ℤ) (-1))).Splitting where
  r := 0
  s := (singleObjXSelf (ComplexShape.up ℤ) (-1) N).hom ≫
    (doubleXIso₀ d upIntRelNegOneZero).inv
  f_r := (isZero_single_obj_X (ComplexShape.up ℤ) 0 M (-1)
    NaiveCotangent.TwoTerm.negOne_ne_zero).eq_of_src _ _
  s_g := by simp [twoTermShortComplex]
  id := by
    rw [Limits.zero_comp, zero_add]
    simp [twoTermShortComplex]

/-- Away from the degrees `-1` and `0` all three terms of the short complex vanish. -/
public def twoTermSplitting₂ (d : N ⟶ M) (i : ℤ) (h₀ : i ≠ 0) (h₁ : i ≠ -1) :
    ((twoTermShortComplex d).map (eval (ModuleCat.{u} A) (ComplexShape.up ℤ) i)).Splitting where
  r := 0
  s := 0
  f_r := (isZero_single_obj_X (ComplexShape.up ℤ) 0 M i h₀).eq_of_src _ _
  s_g := (isZero_single_obj_X (ComplexShape.up ℤ) (-1) N i h₁).eq_of_src _ _
  id := (isZero_double_X d upIntRelNegOneZero i h₁ h₀).eq_of_src _ _

/-- The short complex `M[0] ⟶ (N ⟶ M) ⟶ N[-1]` is short exact. -/
public theorem shortExact_twoTermShortComplex (d : N ⟶ M) :
    (twoTermShortComplex d).ShortExact := by
  refine shortExact_of_degreewise_shortExact _ fun i => ?_
  by_cases h₀ : i = 0
  · subst h₀
    exact (twoTermSplitting₀ d).shortExact
  by_cases h₁ : i = -1
  · subst h₁
    exact (twoTermSplitting₁ d).shortExact
  exact (twoTermSplitting₂ d i h₀ h₁).shortExact

/-- For `d : N ⟶ M` the triangle `M[0] ⟶ (N ⟶ M) ⟶ N[-1] ⟶ M[0]⟦1⟧` in the derived category
of `A`-modules of the short exact sequence `twoTermShortComplex d` of cochain complexes. -/
public def twoTermTriangle (d : N ⟶ M) :
    Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} A)) :=
  DerivedCategory.triangleOfSES (shortExact_twoTermShortComplex d)

/-- The triangle of a two-term complex is distinguished. -/
public theorem twoTermTriangle_distinguished (d : N ⟶ M) :
    twoTermTriangle d ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) :=
  DerivedCategory.triangleOfSES_distinguished _

/-- The first morphism of `twoTermTriangle d` is the image of `twoTermInclusion d`. -/
@[simp] public theorem twoTermTriangle_mor₁ (d : N ⟶ M) :
    (twoTermTriangle d).mor₁ = DerivedCategory.Q.map (twoTermInclusion d) :=
  rfl

/-- The second morphism of `twoTermTriangle d` is the image of `twoTermProjection d`. -/
@[simp] public theorem twoTermTriangle_mor₂ (d : N ⟶ M) :
    (twoTermTriangle d).mor₂ = DerivedCategory.Q.map (twoTermProjection d) :=
  rfl

/-- The triangle `twoTermTriangle` of the differential of a two-term complex of modules; for the
naive cotangent complex of a presentation it is `Ω[0] ⟶ NL(α) ⟶ (J/J²)[-1]`. -/
public def twoTermComplexTriangle (T : TwoTerm.{u, u, u} A) :
    Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} A)) :=
  twoTermTriangle (ModuleCat.ofHom T.d)

/-- The triangle of a two-term complex of modules is distinguished. -/
public theorem twoTermComplexTriangle_distinguished (T : TwoTerm.{u, u, u} A) :
    twoTermComplexTriangle T ∈
      distTriang (DerivedCategory (ModuleCat.{u} A)) :=
  twoTermTriangle_distinguished _

end Triangle

section Presentation

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A] {ι : Type u}

/-- The comparison of any presentation of `A` over `Λ` with the canonical presentation is a
homotopy equivalence of naive cotangent complexes. -/
public theorem nlMap_canonical_isHomotopyEquiv (P : Algebra.Generators Λ A ι)
    (φ : P.Hom (canonicalGenerators Λ A)) :
    IsHomotopyEquiv (nlMap P (canonicalGenerators Λ A) φ) :=
  (nlMap_isHomotopyEquiv_and_isQuasiIso (R' := Λ) (S' := A)
    (by rw [Algebra.algebraMap_self]; exact Function.bijective_id)
    (by rw [Algebra.algebraMap_self]; exact Function.bijective_id)
    P (canonicalGenerators Λ A) φ).left

/-- For any presentation of `A` over `Λ`, the comparison with the canonical presentation is an
isomorphism `NL(α) ≅ NL_{A/Λ}` in the derived category of `A`-modules. -/
@[stacks 00S1 "presentation independence in the derived category: the comparison with the
canonical presentation is an isomorphism in D(A)",
  sga "6 0 4.3" "partial",
  sga "6 0 4.4" "special case",
  sga "6 VIII 2.2" "special case"]
public def derivedNaiveCotangentComplexIso (P : Algebra.Generators Λ A ι)
    (φ : P.Hom (canonicalGenerators Λ A)) :
    DerivedCategory.Q.obj (twoTermComplex (nlRestrict A P)) ≅
      derivedNaiveCotangentComplex Λ A :=
  @asIso _ _ _ _ _ (isIso_Q_map_twoTermHom (nlMap_canonical_isHomotopyEquiv Λ A P φ))

end Presentation

end Deformation.Artin

end
