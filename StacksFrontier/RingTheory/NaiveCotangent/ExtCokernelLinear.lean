module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.Algebra.Homology.DerivedCategory.EssentiallyConstant
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import StacksFrontier.Homology.DoubleExtend
public import StacksFrontier.RingTheory.NaiveCotangent.Defs
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import StacksFrontier.Homology.TwoTermComplex.Ext
public import Mathlib.Algebra.Homology.HomotopyCofiber

/-!
# The Ext-cokernel comparison of a two-term complex, linearly

Let `dl : M₁ →ₗ[B] M₀` be a map of `B`-modules with `M₀` free, and let `[M₁ → M₀]` be the
two-term complex it defines, realized as the mapping cone of the induced map of complexes
concentrated in degree `0`. For a coefficient module `Nc` the first extension group of that
cone is the cokernel of precomposition with `dl` on the dual modules,

`Ext¹([M₁ → M₀], Nc) = (M₁ →ₗ[B] Nc) / (M₀ →ₗ[B] Nc)`,

and the comparison is given by an explicit cocycle: a functional `f : M₁ →ₗ[B] Nc` is sent to
the class of the cochain map which is `f` on the summand `M₁` of the cone, in degree `-1`, and
zero on the summand `M₀`. Instantiating at the naive cotangent complex of a polynomial
presentation gives `NaiveCotangent.presentationCokernelExtOneEquiv`, the comparison computing
`Ext¹(NL_{B/A}, N)`.

The comparison is **linear over `B`**, and it is characterised by what it does to the class of
a functional.

## Main definitions

* `NaiveCotangent.ExtCokernelLinear.coneDesc`: the cochain map `cone(dl) ⟶ Nc[1]` determined by
  a functional on the conormal term.
* `NaiveCotangent.ExtCokernelLinear.extOneClass`, `extOneClassMap`: its class in the derived
  category, as a `B`-linear map in the functional.
* `NaiveCotangent.ExtCokernelLinear.extOneTwoTermLinearEquiv`: the comparison, for an arbitrary
  two-term complex of modules.
* `NaiveCotangent.presentationCokernelExtOneEquiv`: the comparison for the naive cotangent
  complex of a presentation, and `NaiveCotangent.presentationExtOneClass` the explicit class of
  a conormal functional.
* `NaiveCotangent.extOne_naiveCotangentComplex_linearEquiv_cokernel`: the same equivalence,
  stated with the differential of `NaiveCotangent.NL P`.

## Main results

* `NaiveCotangent.ExtCokernelLinear.Q_map_coneDesc_eq_zero_iff`: a functional has zero class
  exactly when it factors through `dl`.
* `NaiveCotangent.ExtCokernelLinear.surjective_extOneClassMap`: every class is the class of a
  functional.
* `NaiveCotangent.presentationCokernelExtOneEquiv_presentationExtOneClass` and
  `NaiveCotangent.presentationCokernelExtOneEquiv_symm_mk`: the comparison carries the class of
  a conormal functional `f` to the residue class of `f`, and conversely.
* `NaiveCotangent.presentationExtOneClass_smul`: the class map is `B`-linear.

## References

* [Stacks Project, Tag 0GPU](https://stacks.math.columbia.edu/tag/0GPU)
* [Stacks Project, Tag 0ALN](https://stacks.math.columbia.edu/tag/0ALN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open ComplexShape (upIntRelNegOneZero)
open HomologicalComplex.homotopyCofiber (inlX inrX sndX fstX desc)

attribute [local instance] HasDerivedCategory.standard

universe w uA uB uι uN

namespace NaiveCotangent.ExtCokernelLinear

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

variable {B : Type uB} [CommRing B] {X Y Z : ModuleCat.{w} B}

/-- `0` precedes its successor in the cochain-complex shape on `ℤ`. -/
lemma upRelNext : (ComplexShape.up ℤ).Rel 0 ((ComplexShape.up ℤ).next 0) := by
  simp [ComplexShape.up_Rel]

/-- The morphism `X[0] ⟶ Y[0]` of complexes concentrated in degree `0` induced by a map
`dd : X ⟶ Y` of modules. Its mapping cone is the two-term complex `[X → Y]`, with `X` in
degree `-1` and `Y` in degree `0`. -/
abbrev singleMap (dd : X ⟶ Y) :
    (CochainComplex.singleFunctor (ModuleCat.{w} B) 0).obj X ⟶
      (CochainComplex.singleFunctor (ModuleCat.{w} B) 0).obj Y :=
  (CochainComplex.singleFunctor (ModuleCat.{w} B) 0).map dd

/-- The null-homotopy of `X[0] → Y[0] → Z[1]` determined by a map `f : X ⟶ Z`: its only
nonzero component is `f` itself, from degree `0` of `X[0]` to degree `-1` of `Z[1]`. -/
def coneHomotopy (dd : X ⟶ Y) (f : X ⟶ Z) :
    Homotopy (singleMap dd ≫
      (0 : (CochainComplex.singleFunctor (ModuleCat.{w} B) 0).obj Y ⟶
        TwoTermComplexExt.shiftSingle Z 1)) 0 where
  hom i j := if h : i = 0 ∧ j = -1 then
      eqToHom (congrArg ((CochainComplex.singleFunctor (ModuleCat.{w} B) 0).obj X).X h.1) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom ≫ f ≫
        (TwoTermComplexExt.shiftSingleXSelf Z 1).inv ≫
        eqToHom (congrArg (TwoTermComplexExt.shiftSingle Z 1).X h.2.symm)
    else 0
  zero i j hij := by
    by_cases h : i = 0 ∧ j = -1
    · exfalso
      apply hij
      rcases h with ⟨rfl, rfl⟩
      simp [ComplexShape.up_Rel]
    · simp [h]
  comm i := by
    rw [dNext_eq _ (i' := i + 1) (by simp [ComplexShape.up_Rel]),
      prevD_eq _ (j' := i - 1) (by simp [ComplexShape.up_Rel])]
    rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
    simp only [comp_zero]
    simp [CochainComplex.singleFunctor, TwoTermComplexExt.shiftSingle]
    all_goals abel

/-- The only nonzero component of `coneHomotopy dd f` is `f` itself. -/
lemma coneHomotopy_hom (dd : X ⟶ Y) (f : X ⟶ Z) :
    (coneHomotopy dd f).hom 0 (-1) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom ≫ f ≫
        (TwoTermComplexExt.shiftSingleXSelf Z 1).inv := by
  simp [coneHomotopy]

/-- The cochain map `cone(dd) ⟶ Z[1]` determined by a map `f : X ⟶ Z` of the conormal term:
it is `f` on the summand `X` of the cone in degree `-1` and zero on the summand `Y`. Its class
in the derived category is the extension class of `f`. -/
def coneDesc (dd : X ⟶ Y) (f : X ⟶ Z) :
    HomologicalComplex.homotopyCofiber (singleMap dd) ⟶ TwoTermComplexExt.shiftSingle Z 1 :=
  desc _ 0 (coneHomotopy dd f)

/-- `Y[0]` vanishes in degree `-1`. -/
lemma isZero_single_X_neg_one (Y : ModuleCat.{w} B) :
    IsZero (((CochainComplex.singleFunctor (ModuleCat.{w} B) 0).obj Y).X (-1)) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 Y (-1) (by norm_num)

/-- `Z[1]` vanishes outside degree `-1`. -/
lemma isZero_shiftSingle (Z : ModuleCat.{w} B) {i : ℤ} (hi : i ≠ -1) :
    IsZero ((TwoTermComplexExt.shiftSingle Z 1).X i) :=
  TwoTermComplexExt.isZero_shiftSingle_X (N := Z) (j := 1) (i := i) (by omega)

/-- Two maps out of the degree `-1` term of `cone(dd)` agree once they agree on the summand
`X`. -/
lemma coneX_ext {dd : X ⟶ Y} {K : ModuleCat.{w} B}
    {a b : (HomologicalComplex.homotopyCofiber (singleMap dd)).X (-1) ⟶ K}
    (h : inlX (singleMap dd) 0 (-1) upIntRelNegOneZero ≫ a =
      inlX (singleMap dd) 0 (-1) upIntRelNegOneZero ≫ b) :
    a = b :=
  HomologicalComplex.homotopyCofiber.ext_from_X (singleMap dd) 0 (-1) upIntRelNegOneZero h
    ((isZero_single_X_neg_one Y).eq_of_src _ _)

/-- Two maps out of `cone(dd)` into a complex concentrated in degree `-1` agree as soon as
they agree on the summand `X` of the cone. -/
lemma coneHom_ext {dd : X ⟶ Y} {K : CochainComplex (ModuleCat.{w} B) ℤ}
    {a b : HomologicalComplex.homotopyCofiber (singleMap dd) ⟶ K}
    (h : ∀ i : ℤ, i ≠ -1 → IsZero (K.X i))
    (h₁ : inlX (singleMap dd) 0 (-1) upIntRelNegOneZero ≫ a.f (-1) =
      inlX (singleMap dd) 0 (-1) upIntRelNegOneZero ≫ b.f (-1)) : a = b := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  obtain rfl | hi := eq_or_ne i (-1)
  · exact coneX_ext h₁
  · exact (h i hi).eq_of_tgt _ _

/-- Restricting `coneDesc dd f` to the summand `X` of the cone in degree `-1` recovers `f`. -/
@[reassoc]
lemma inlX_coneDesc_f (dd : X ⟶ Y) (f : X ⟶ Z) :
    inlX (singleMap dd) 0 (-1) upIntRelNegOneZero ≫ (coneDesc dd f).f (-1) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom ≫ f ≫
        (TwoTermComplexExt.shiftSingleXSelf Z 1).inv := by
  rw [coneDesc, HomologicalComplex.homotopyCofiber.inlX_desc_f _ _ _ 0 (-1) upIntRelNegOneZero,
    coneHomotopy_hom]

/-- `coneDesc dd` is additive in the map `f`. -/
lemma coneDesc_add (dd : X ⟶ Y) (f g : X ⟶ Z) :
    coneDesc dd (f + g) = coneDesc dd f + coneDesc dd g := by
  refine coneHom_ext (fun i hi => isZero_shiftSingle Z hi) ?_
  rw [HomologicalComplex.add_f_apply, Preadditive.comp_add, inlX_coneDesc_f,
    inlX_coneDesc_f, inlX_coneDesc_f]
  simp [Preadditive.comp_add, Preadditive.add_comp]

/-- `coneDesc dd` is compatible with the scalar action of the base ring on the map `f`. -/
lemma coneDesc_smul (dd : X ⟶ Y) (b : B) (f : X ⟶ Z) :
    coneDesc dd (b • f) = b • coneDesc dd f := by
  refine coneHom_ext (fun i hi => isZero_shiftSingle Z hi) ?_
  rw [HomologicalComplex.smul_f_apply, Linear.comp_smul, inlX_coneDesc_f, inlX_coneDesc_f]
  simp [Linear.comp_smul, Linear.smul_comp]

/-- Restricting a cochain map `cone(dd) ⟶ Z[1]` to the summand `X` of the cone. -/
def coneExtract (dd : X ⟶ Y)
    (a : HomologicalComplex.homotopyCofiber (singleMap dd) ⟶
      TwoTermComplexExt.shiftSingle Z 1) : X ⟶ Z :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫
    inlX (singleMap dd) 0 (-1) upIntRelNegOneZero ≫ a.f (-1) ≫
      (TwoTermComplexExt.shiftSingleXSelf Z 1).hom

/-- Every cochain map `cone(dd) ⟶ Z[1]` is `coneDesc dd f` for `f` its restriction to the
summand `X`. -/
lemma coneDesc_coneExtract (dd : X ⟶ Y)
    (a : HomologicalComplex.homotopyCofiber (singleMap dd) ⟶
      TwoTermComplexExt.shiftSingle Z 1) : coneDesc dd (coneExtract dd a) = a := by
  refine coneHom_ext (fun i hi => isZero_shiftSingle Z hi) ?_
  rw [inlX_coneDesc_f, coneExtract]
  simp

/-! ### Vanishing of a class -/

/-- `X[0]` vanishes in the degree following `0`. -/
lemma isZero_single_X_next (X : ModuleCat.{w} B) :
    IsZero (((CochainComplex.singleFunctor (ModuleCat.{w} B) 0).obj X).X
      ((ComplexShape.up ℤ).next 0)) := by
  rw [CochainComplex.next]
  exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 X 1 (by norm_num)

/-- `cone(dd)` vanishes in positive degrees. -/
lemma isZero_cone_X_of_pos (dd : X ⟶ Y) (i : ℤ) (hi : 0 < i) :
    IsZero ((HomologicalComplex.homotopyCofiber (singleMap dd)).X i) := by
  change IsZero ((CochainComplex.mappingCone (singleMap dd)).X i)
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 X (i + 1) (by omega),
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 Y i (by omega)⟩

/-- The degree `0` term of `cone(dd)` is `Y`. -/
def coneXZeroIso (dd : X ⟶ Y) :
    (HomologicalComplex.homotopyCofiber (singleMap dd)).X 0 ≅ Y :=
  (HomologicalComplex.homotopyCofiber.XIsoBiprod (singleMap dd) 0
      ((ComplexShape.up ℤ).next 0) upRelNext).trans
    ((isoZeroBiprod (isZero_single_X_next X)).symm.trans
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y))

/-- `coneXZeroIso` is the projection of the degree `0` term of the cone onto `Y`. -/
@[reassoc]
lemma coneXZeroIso_hom (dd : X ⟶ Y) :
    (coneXZeroIso dd).hom =
      sndX (singleMap dd) 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).hom := by
  apply ModuleCat.hom_ext
  ext x
  simp [coneXZeroIso, HomologicalComplex.homotopyCofiber.sndX,
    HomologicalComplex.homotopyCofiber.XIsoBiprod, ComplexShape.up_Rel, isoZeroBiprod]

/-- The degree `0` term of `cone(dd)` is projective as soon as `Y` is. -/
lemma projective_cone_X_zero (dd : X ⟶ Y) [Projective Y] :
    Projective ((HomologicalComplex.homotopyCofiber (singleMap dd)).X 0) :=
  Projective.of_iso (coneXZeroIso dd).symm inferInstance

/-- The degree `0` term of `Z[1]` is projective. -/
lemma projective_shiftSingle_X_zero (Z : ModuleCat.{w} B) :
    Projective ((TwoTermComplexExt.shiftSingle Z 1).X 0) :=
  Projective.of_iso (IsZero.isoZero (isZero_shiftSingle Z (by norm_num))).symm inferInstance

/-- In degree `0`, `singleMap dd` is `dd` itself. -/
lemma singleObjXSelf_inv_singleMap_f (dd : X ⟶ Y) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ (singleMap dd).f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).hom = dd := by
  change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫
    ((HomologicalComplex.single (ModuleCat.{w} B) (ComplexShape.up ℤ) 0).map dd).f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).hom = _
  rw [HomologicalComplex.single_map_f_self]
  simp

/-- The degree `0` component of `singleMap dd`, read through the identifications of the
degree `0` terms of `X[0]` and `Y[0]` with `X` and `Y`. -/
@[reassoc]
lemma singleMap_f_zero_comp (dd : X ⟶ Y) :
    (singleMap dd).f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).hom =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom ≫ dd := by
  conv_rhs => rw [← singleObjXSelf_inv_singleMap_f dd]
  simp

/-- The composite of the inclusion of the summand `X` with the differential of the cone is the
degree `0` component of `singleMap dd` followed by the inclusion of the summand `Y`. -/
@[reassoc]
lemma inlX_cone_d (dd : X ⟶ Y) :
    inlX (singleMap dd) 0 (-1) upIntRelNegOneZero ≫
        (HomologicalComplex.homotopyCofiber (singleMap dd)).d (-1) 0 =
      (singleMap dd).f 0 ≫ inrX (singleMap dd) 0 := by
  rw [show (HomologicalComplex.homotopyCofiber (singleMap dd)).d (-1) 0 =
    HomologicalComplex.homotopyCofiber.d (singleMap dd) (-1) 0 from rfl,
    HomologicalComplex.homotopyCofiber.inlX_d (singleMap dd) (-1) 0 1 upIntRelNegOneZero
      (by simp [ComplexShape.up_Rel])]
  simp

/-- The inclusion of the summand `Y` into the degree `0` term of the cone, followed by the
projection onto that summand, is the identity. -/
lemma inrX_sndX_comp (dd : X ⟶ Y) {K : ModuleCat.{w} B}
    (k : ((CochainComplex.singleFunctor (ModuleCat.{w} B) 0).obj Y).X 0 ⟶ K) :
    inrX (singleMap dd) 0 ≫ sndX (singleMap dd) 0 ≫ k = k := by
  rw [← Category.assoc, HomologicalComplex.homotopyCofiber.inrX_sndX, Category.id_comp]

/-- The inclusion of the summand `Y` into the degree `0` term of the cone is the inverse of
`coneXZeroIso`, read through the identification of the degree `0` term of `Y[0]` with `Y`. -/
@[reassoc]
lemma inrX_eq (dd : X ⟶ Y) :
    inrX (singleMap dd) 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).hom ≫
        (coneXZeroIso dd).inv := by
  rw [Iso.eq_comp_inv, coneXZeroIso_hom, inrX_sndX_comp]

section Projective

variable [Small.{w} B] [Projective Y]

/-- **The vanishing criterion for a map out of the cone.** A cochain map `cone(dd) ⟶ Z[1]` is
zero in the derived category exactly when its degree `-1` component is cancelled by a
correction term factoring through the differential of the cone. -/
lemma Q_map_coneHom_eq_zero_iff (dd : X ⟶ Y)
    (a : HomologicalComplex.homotopyCofiber (singleMap dd) ⟶
      TwoTermComplexExt.shiftSingle Z 1) :
    DerivedCategory.Q.map a = 0 ↔
      ∃ h0 : (HomologicalComplex.homotopyCofiber (singleMap dd)).X 0 ⟶
          (TwoTermComplexExt.shiftSingle Z 1).X (-1),
        a.f (-1) +
          (HomologicalComplex.homotopyCofiber (singleMap dd)).d (-1) 0 ≫ h0 = 0 := by
  have hcrit := TwoTermComplexExt.forall_Q_map_comp_eq_zero_iff
    (HomologicalComplex.homotopyCofiber (singleMap dd)) (TwoTermComplexExt.shiftSingle Z 1)
    (isZero_cone_X_of_pos dd) (projective_cone_X_zero dd)
    (fun i hi _ => isZero_shiftSingle Z hi) (projective_shiftSingle_X_zero Z) a
  exact ⟨fun ha => hcrit.mp fun _ _ => by simp [ha], fun h => by
    simpa using hcrit.mpr h Z (𝟙 (DerivedCategory.Q.obj (TwoTermComplexExt.shiftSingle Z 1)))⟩

/-- A functional on the conormal term that factors through `dd` has zero class. -/
lemma Q_map_coneDesc_comp (dd : X ⟶ Y) (g : Y ⟶ Z) :
    DerivedCategory.Q.map (coneDesc dd (dd ≫ g)) = 0 := by
  refine (Q_map_coneHom_eq_zero_iff dd _).2 ⟨sndX (singleMap dd) 0 ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).hom ≫ (-g) ≫
      (TwoTermComplexExt.shiftSingleXSelf Z 1).inv, ?_⟩
  refine coneX_ext ?_
  rw [Preadditive.comp_add, inlX_coneDesc_f, comp_zero, inlX_cone_d_assoc,
    inrX_sndX_comp, singleMap_f_zero_comp_assoc]
  simp

/-- The classes of the maps `coneDesc dd f` exhaust `Hom_{D}(cone(dd), Z[1])`. -/
lemma surjective_Q_map_coneDesc (dd : X ⟶ Y) :
    Function.Surjective (fun f : X ⟶ Z => DerivedCategory.Q.map (coneDesc dd f)) := by
  intro y
  obtain ⟨k, hk⟩ := (TwoTermComplexExt.toHomD_bijective
    (HomologicalComplex.homotopyCofiber (singleMap dd)) (TwoTermComplexExt.shiftSingle Z 1)
    (isZero_cone_X_of_pos dd) (projective_cone_X_zero dd)
    (fun i hi => isZero_shiftSingle Z (by omega))).2 y
  obtain ⟨a, ha⟩ := (HomotopyCategory.quotient (ModuleCat.{w} B)
    (ComplexShape.up ℤ)).map_surjective k
  refine ⟨coneExtract dd a, ?_⟩
  change DerivedCategory.Q.map (coneDesc dd (coneExtract dd a)) = y
  rw [coneDesc_coneExtract, ← TwoTermComplexExt.toHomD_quotient_map a, ha]
  exact hk

/-- **The kernel of the class map.** A functional `f : X ⟶ Z` on the conormal term has zero
class exactly when it factors through `dd`. -/
lemma Q_map_coneDesc_eq_zero_iff (dd : X ⟶ Y) (f : X ⟶ Z) :
    DerivedCategory.Q.map (coneDesc dd f) = 0 ↔ ∃ g : Y ⟶ Z, f = dd ≫ g := by
  refine ⟨fun hzero => ?_, fun ⟨g, hg⟩ => by rw [hg]; exact Q_map_coneDesc_comp dd g⟩
  obtain ⟨h0, hh0⟩ := (Q_map_coneHom_eq_zero_iff dd _).mp hzero
  refine ⟨-((coneXZeroIso dd).inv ≫ h0 ≫ (TwoTermComplexExt.shiftSingleXSelf Z 1).hom), ?_⟩
  have key := congrArg
    (fun q => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫
      inlX (singleMap dd) 0 (-1) upIntRelNegOneZero ≫ q ≫
        (TwoTermComplexExt.shiftSingleXSelf Z 1).hom) hh0
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, zero_comp,
    comp_zero] at key
  rw [inlX_coneDesc_f_assoc, inlX_cone_d_assoc, inrX_eq_assoc,
    singleMap_f_zero_comp_assoc] at key
  simp at key
  rwa [Preadditive.comp_neg, eq_neg_iff_add_eq_zero]

end Projective

/-! ### The comparison -/

/-- In the derived category, `Z[1]` is the shift by `1` of `Z[0]`. -/
def shiftSingleQIso (Z : ModuleCat.{w} B) :
    DerivedCategory.Q.obj (TwoTermComplexExt.shiftSingle Z 1) ≅
      (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat.{w} B) 0).obj Z))⟦(1 : ℤ)⟧ :=
  (DerivedCategory.Q.commShiftIso (1 : ℤ)).app
    ((CochainComplex.singleFunctor (ModuleCat.{w} B) 0).obj Z)

/-- The first extension class of the two-term complex `cone(dd)` attached to a functional
`f : X ⟶ Z` on its conormal term: the class of the explicit cochain map `coneDesc dd f`. -/
def extOneClass (dd : X ⟶ Y) (f : X ⟶ Z) :
    DerivedCategory.Ext
      (DerivedCategory.Q.obj (HomologicalComplex.homotopyCofiber (singleMap dd)))
      ((DerivedCategory.singleFunctor (ModuleCat.{w} B) 0).obj Z) 1 :=
  DerivedCategory.Q.map (coneDesc dd f) ≫ (shiftSingleQIso Z).hom

/-- The extension class of a functional on the conormal term, as a `B`-linear map. -/
def extOneClassMap (dd : X ⟶ Y) (Z : ModuleCat.{w} B) :
    (X ⟶ Z) →ₗ[B] DerivedCategory.Ext
      (DerivedCategory.Q.obj (HomologicalComplex.homotopyCofiber (singleMap dd)))
      ((DerivedCategory.singleFunctor (ModuleCat.{w} B) 0).obj Z) 1 where
  toFun := extOneClass dd
  map_add' f g := by
    change extOneClass dd (f + g) = extOneClass dd f + extOneClass dd g
    rw [extOneClass, extOneClass, extOneClass, coneDesc_add, Functor.map_add,
      Preadditive.add_comp]
  map_smul' b f := by
    change extOneClass dd (b • f) = b • extOneClass dd f
    rw [extOneClass, extOneClass, coneDesc_smul, Functor.map_smul, Linear.smul_comp]

/-- `extOneClassMap dd Z` sends `f` to `extOneClass dd f`. -/
@[simp]
lemma extOneClassMap_apply (dd : X ⟶ Y) (f : X ⟶ Z) :
    extOneClassMap dd Z f = extOneClass dd f := rfl

section Projective

variable [Small.{w} B] [Projective Y]

/-- The extension class of `f` vanishes exactly when `f` factors through `dd`. -/
lemma extOneClass_eq_zero_iff (dd : X ⟶ Y) (f : X ⟶ Z) :
    extOneClass dd f = 0 ↔ ∃ g : Y ⟶ Z, f = dd ≫ g := by
  rw [← Q_map_coneDesc_eq_zero_iff dd f, extOneClass]
  refine ⟨fun h => ?_, fun h => by rw [h, zero_comp]⟩
  rw [← cancel_mono (shiftSingleQIso Z).hom, h, zero_comp]

/-- The kernel of the class map is the image of precomposition with `dd`. -/
lemma ker_extOneClassMap (dd : X ⟶ Y) :
    LinearMap.ker (extOneClassMap dd Z) = LinearMap.range (Linear.leftComp B Z dd) := by
  ext f
  rw [LinearMap.mem_ker, extOneClassMap_apply, extOneClass_eq_zero_iff]
  exact ⟨fun ⟨g, hg⟩ => ⟨g, hg.symm⟩, fun ⟨g, hg⟩ => ⟨g, hg.symm⟩⟩

/-- Every first extension class of the two-term complex is the class of a functional on its
conormal term. -/
lemma surjective_extOneClassMap (dd : X ⟶ Y) :
    Function.Surjective (extOneClassMap dd Z) := by
  intro x
  obtain ⟨f, hf⟩ := surjective_Q_map_coneDesc dd (x ≫ (shiftSingleQIso Z).inv)
  replace hf : DerivedCategory.Q.map (coneDesc dd f) = x ≫ (shiftSingleQIso Z).inv := hf
  refine ⟨f, ?_⟩
  rw [extOneClassMap_apply, extOneClass, hf]
  simp

/-- **The Ext-cokernel comparison for a two-term complex of modules.** The first extension
group of the mapping cone of `dd : X ⟶ Y`, with `Y` projective, is the cokernel of
precomposition with `dd` on the dual modules — as an equivalence of `B`-modules, and by an
explicit map: the class of `f` is the class of the cochain map `coneDesc dd f`. -/
def cokernelExtOneEquiv (dd : X ⟶ Y) :
    ((X ⟶ Z) ⧸ LinearMap.range (Linear.leftComp B Z dd)) ≃ₗ[B]
      DerivedCategory.Ext
        (DerivedCategory.Q.obj (HomologicalComplex.homotopyCofiber (singleMap dd)))
        ((DerivedCategory.singleFunctor (ModuleCat.{w} B) 0).obj Z) 1 :=
  LinearEquiv.ofBijective
    ((LinearMap.range (Linear.leftComp B Z dd)).liftQ (extOneClassMap dd Z)
      (ker_extOneClassMap dd).ge)
    ⟨LinearMap.ker_eq_bot.mp
        (Submodule.ker_liftQ_eq_bot' _ _ (ker_extOneClassMap dd).symm),
      fun x => by
        obtain ⟨f, hf⟩ := surjective_extOneClassMap (Z := Z) dd x
        exact ⟨Submodule.Quotient.mk f, hf⟩⟩

/-- `cokernelExtOneEquiv dd` sends the residue class of `f` to `extOneClass dd f`. -/
@[simp]
lemma cokernelExtOneEquiv_mk (dd : X ⟶ Y) (f : X ⟶ Z) :
    cokernelExtOneEquiv dd (Submodule.Quotient.mk f) = extOneClass dd f := rfl

/-- The inverse of `cokernelExtOneEquiv dd` sends `extOneClass dd f` to the residue class of
`f`. -/
@[simp]
lemma cokernelExtOneEquiv_symm_extOneClass (dd : X ⟶ Y) (f : X ⟶ Z) :
    (cokernelExtOneEquiv dd).symm (extOneClass dd f) = Submodule.Quotient.mk f :=
  (cokernelExtOneEquiv dd).symm_apply_eq.2 (cokernelExtOneEquiv_mk dd f).symm

end Projective

/-! ### The cokernel presentation in terms of linear maps -/

section LinearMaps

variable {M₁ M₀ Nc : Type w} [AddCommGroup M₁] [Module B M₁] [AddCommGroup M₀]
  [Module B M₀] [AddCommGroup Nc] [Module B Nc]

/-- Morphisms `M₁ ⟶ Nc` of the module category are linear maps `M₁ →ₗ[B] Nc`. -/
def homEquivLinear (M₁ Nc : Type w) [AddCommGroup M₁] [Module B M₁] [AddCommGroup Nc]
    [Module B Nc] : (ModuleCat.of B M₁ ⟶ ModuleCat.of B Nc) ≃ₗ[B] (M₁ →ₗ[B] Nc) :=
  ModuleCat.homLinearEquiv

/-- Under the identification of morphisms of the module category with linear maps,
precomposition with `ModuleCat.ofHom dl` is precomposition with `dl`. -/
lemma homEquivLinear_comp_leftComp (dl : M₁ →ₗ[B] M₀) :
    (homEquivLinear (B := B) M₁ Nc : _ →ₗ[B] (M₁ →ₗ[B] Nc)).comp
        (Linear.leftComp B (ModuleCat.of B Nc) (ModuleCat.ofHom dl)) =
      (LinearMap.lcomp B Nc dl).comp (homEquivLinear (B := B) M₀ Nc : _ →ₗ[B] (M₀ →ₗ[B] Nc)) :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

/-- The range of precomposition with `ModuleCat.ofHom dl` is carried onto the range of
precomposition with `dl`. -/
lemma map_range_leftComp (dl : M₁ →ₗ[B] M₀) :
    Submodule.map (homEquivLinear (B := B) M₁ Nc : _ →ₗ[B] _)
        (LinearMap.range (Linear.leftComp B (ModuleCat.of B Nc) (ModuleCat.ofHom dl))) =
      LinearMap.range (LinearMap.lcomp B Nc dl) := by
  rw [← LinearMap.range_comp, homEquivLinear_comp_leftComp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top]

/-- **The Ext-cokernel comparison of a two-term complex of modules.** The first extension
group of the mapping cone of `dl : M₁ →ₗ[B] M₀`, with `M₀` free, is the cokernel of
precomposition with `dl` on the dual modules, as an equivalence of `B`-modules. -/
def extOneTwoTermLinearEquiv [Small.{w} B] [Module.Free B M₀] (dl : M₁ →ₗ[B] M₀) :
    DerivedCategory.Ext
        (DerivedCategory.Q.obj (HomologicalComplex.homotopyCofiber
          (singleMap (ModuleCat.ofHom dl))))
        ((DerivedCategory.singleFunctor (ModuleCat.{w} B) 0).obj (ModuleCat.of B Nc)) 1 ≃ₗ[B]
      ((M₁ →ₗ[B] Nc) ⧸ LinearMap.range (LinearMap.lcomp B Nc dl)) :=
  (cokernelExtOneEquiv (Z := ModuleCat.of B Nc) (ModuleCat.ofHom dl)).symm.trans
    (Submodule.Quotient.equiv _ _ (homEquivLinear (B := B) M₁ Nc) (map_range_leftComp dl))

/-- The comparison sends the class of a conormal functional `f` to the residue class of `f`. -/
@[simp]
lemma extOneTwoTermLinearEquiv_extOneClass [Small.{w} B] [Module.Free B M₀]
    (dl : M₁ →ₗ[B] M₀) (f : ModuleCat.of B M₁ ⟶ ModuleCat.of B Nc) :
    extOneTwoTermLinearEquiv (Nc := Nc) dl (extOneClass (ModuleCat.ofHom dl) f) =
      Submodule.Quotient.mk (homEquivLinear (B := B) M₁ Nc f) := by
  rw [extOneTwoTermLinearEquiv, LinearEquiv.trans_apply,
    cokernelExtOneEquiv_symm_extOneClass]
  rfl

end LinearMaps

end NaiveCotangent.ExtCokernelLinear

namespace NaiveCotangent

open ExtCokernelLinear

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

section Presentation

variable {A : Type uA} {B : Type uB} {ι : Type uι} {N : Type uN}
  [CommRing A] [CommRing B] [Algebra A B] (P : Algebra.Generators A B ι)
  [AddCommGroup N] [Module B N]

/-- The conormal differential of the presentation `P`, transported into the common universe
`max uA uB uι uN` in which the comparison with the Ext group takes place. -/
def uliftedCotangentComplex (_N : Type uN) :
    ULift.{max uA uB uι uN} P.toExtension.Cotangent →ₗ[B]
      ULift.{max uA uB uι uN} P.toExtension.CotangentSpace :=
  ULift.moduleEquiv.symm.toLinearMap.comp
    (P.toExtension.cotangentComplex.comp ULift.moduleEquiv.toLinearMap)

/-- Functionals on the lifted conormal module are functionals on the conormal module. -/
def uliftConormalDualEquiv :
    (ULift.{max uA uB uι uN} P.toExtension.Cotangent →ₗ[B]
        ULift.{max uA uB uι uN} N) ≃ₗ[B] (P.toExtension.Cotangent →ₗ[B] N) :=
  LinearEquiv.arrowCongr ULift.moduleEquiv ULift.moduleEquiv

/-- Functionals on the lifted cotangent space are functionals on the cotangent space. -/
def uliftCotangentSpaceDualEquiv :
    (ULift.{max uA uB uι uN} P.toExtension.CotangentSpace →ₗ[B]
        ULift.{max uA uB uι uN} N) ≃ₗ[B] (P.toExtension.CotangentSpace →ₗ[B] N) :=
  LinearEquiv.arrowCongr ULift.moduleEquiv ULift.moduleEquiv

/-- Precomposition with the lifted conormal differential is, under the identifications of the
dual modules, precomposition with the conormal differential itself. -/
lemma uliftConormalDualEquiv_comp_lcomp :
    (uliftConormalDualEquiv (N := N) P : _ →ₗ[B] (P.toExtension.Cotangent →ₗ[B] N)).comp
        (LinearMap.lcomp B (ULift.{max uA uB uι uN} N) (uliftedCotangentComplex P N)) =
      (LinearMap.lcomp B N P.toExtension.cotangentComplex).comp
        (uliftCotangentSpaceDualEquiv (N := N) P :
          _ →ₗ[B] (P.toExtension.CotangentSpace →ₗ[B] N)) :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

/-- The range of precomposition with the lifted conormal differential is carried onto the
range of precomposition with the conormal differential. -/
lemma map_range_lcomp_ulifted :
    Submodule.map (uliftConormalDualEquiv (N := N) P : _ →ₗ[B] _)
        (LinearMap.range (LinearMap.lcomp B (ULift.{max uA uB uι uN} N)
          (uliftedCotangentComplex P N))) =
      LinearMap.range (LinearMap.lcomp B N P.toExtension.cotangentComplex) := by
  rw [← LinearMap.range_comp, uliftConormalDualEquiv_comp_lcomp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top]

/-- **The first Ext group of the naive cotangent complex is the conormal cokernel.** An
equivalence of `B`-modules, given by an explicit map: the class of a conormal functional `f` is
the class of the cochain map `ExtCokernelLinear.coneDesc` of `f`. The source complex is written
with the lifted conormal differential `uliftedCotangentComplex`. -/
def presentationCokernelExtOneEquiv :
    DerivedCategory.Ext
        (DerivedCategory.Q.obj (HomologicalComplex.homotopyCofiber
          (ExtCokernelLinear.singleMap
            (ModuleCat.ofHom (uliftedCotangentComplex P N)))))
        ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB uι uN} B) 0).obj
          (ModuleCat.of B (ULift.{max uA uB uι uN} N))) 1 ≃ₗ[B]
      ((P.toExtension.Cotangent →ₗ[B] N) ⧸
        LinearMap.range (LinearMap.lcomp B N P.toExtension.cotangentComplex)) :=
  (ExtCokernelLinear.extOneTwoTermLinearEquiv (Nc := ULift.{max uA uB uι uN} N)
      (uliftedCotangentComplex P N)).trans
    (Submodule.Quotient.equiv _ _ (uliftConormalDualEquiv P) (map_range_lcomp_ulifted P))

/-- The first extension class of the naive cotangent complex of `P` attached to a conormal
functional `f`: the class of the cochain map which is `f` on the conormal summand of the
mapping cone and zero on the cotangent-space summand. -/
def presentationExtOneClass (f : P.toExtension.Cotangent →ₗ[B] N) :
    DerivedCategory.Ext
      (DerivedCategory.Q.obj (HomologicalComplex.homotopyCofiber
        (ExtCokernelLinear.singleMap
          (ModuleCat.ofHom (uliftedCotangentComplex P N)))))
      ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB uι uN} B) 0).obj
        (ModuleCat.of B (ULift.{max uA uB uι uN} N))) 1 :=
  ExtCokernelLinear.extOneClass (ModuleCat.ofHom (uliftedCotangentComplex P N))
    (ModuleCat.ofHom ((uliftConormalDualEquiv P).symm f))

/-- **The comparison, on an explicit class.** The class of the conormal functional `f` goes to
the residue class of `f`. -/
@[simp]
lemma presentationCokernelExtOneEquiv_presentationExtOneClass
    (f : P.toExtension.Cotangent →ₗ[B] N) :
    presentationCokernelExtOneEquiv P (presentationExtOneClass P f) =
      Submodule.Quotient.mk f := by
  rw [presentationCokernelExtOneEquiv, presentationExtOneClass, LinearEquiv.trans_apply,
    ExtCokernelLinear.extOneTwoTermLinearEquiv_extOneClass,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe]
  exact congrArg Submodule.Quotient.mk ((uliftConormalDualEquiv P).apply_symm_apply f)

/-- The inverse of the comparison is the explicit class map. -/
lemma presentationCokernelExtOneEquiv_symm_mk (f : P.toExtension.Cotangent →ₗ[B] N) :
    (presentationCokernelExtOneEquiv P).symm (Submodule.Quotient.mk f) =
      presentationExtOneClass P f :=
  (presentationCokernelExtOneEquiv P).symm_apply_eq.2
    (presentationCokernelExtOneEquiv_presentationExtOneClass P f).symm

/-- The explicit class map is additive in the conormal functional. -/
lemma presentationExtOneClass_add (f g : P.toExtension.Cotangent →ₗ[B] N) :
    presentationExtOneClass P (f + g) =
      presentationExtOneClass P f + presentationExtOneClass P g := by
  rw [← presentationCokernelExtOneEquiv_symm_mk, ← presentationCokernelExtOneEquiv_symm_mk,
    ← presentationCokernelExtOneEquiv_symm_mk, ← map_add]
  rfl

/-- The explicit class map is `B`-linear in the conormal functional. -/
lemma presentationExtOneClass_smul (b : B) (f : P.toExtension.Cotangent →ₗ[B] N) :
    presentationExtOneClass P (b • f) = b • presentationExtOneClass P f := by
  rw [← presentationCokernelExtOneEquiv_symm_mk, ← presentationCokernelExtOneEquiv_symm_mk,
    ← map_smul]
  rfl

/-- A conormal functional which factors through the conormal differential has zero class. -/
lemma presentationExtOneClass_comp_cotangentComplex
    (g : P.toExtension.CotangentSpace →ₗ[B] N) :
    presentationExtOneClass P (g.comp P.toExtension.cotangentComplex) = 0 := by
  rw [← presentationCokernelExtOneEquiv_symm_mk]
  refine (LinearEquiv.map_eq_zero_iff _).2 ?_
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨g, rfl⟩

/-- Conversely, a conormal functional with zero class factors through the conormal
differential. -/
lemma exists_comp_cotangentComplex_of_presentationExtOneClass_eq_zero
    (f : P.toExtension.Cotangent →ₗ[B] N) (hf : presentationExtOneClass P f = 0) :
    ∃ g : P.toExtension.CotangentSpace →ₗ[B] N,
      f = g.comp P.toExtension.cotangentComplex := by
  rw [← presentationCokernelExtOneEquiv_symm_mk, LinearEquiv.map_eq_zero_iff,
    Submodule.Quotient.mk_eq_zero] at hf
  obtain ⟨g, hg⟩ := hf
  exact ⟨g, hg.symm⟩

/-- Every first extension class of the naive cotangent complex is the class of a conormal
functional. -/
lemma surjective_presentationExtOneClass :
    Function.Surjective (presentationExtOneClass (N := N) P) := by
  intro x
  obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _
    (presentationCokernelExtOneEquiv P x)
  refine ⟨f, ?_⟩
  rw [← presentationCokernelExtOneEquiv_symm_mk, hf, LinearEquiv.symm_apply_apply]

/-- **The first Ext group of the naive cotangent complex, linearly.** The first extension group
of the mapping cone of the differential of `NaiveCotangent.NL P` is the cokernel of
precomposition with that differential on the dual modules, as an equivalence of `B`-modules:
it is `presentationCokernelExtOneEquiv`, which on the class of a conormal functional `f` is the
residue class of `f`. -/
def extOne_naiveCotangentComplex_linearEquiv_cokernel :
    DerivedCategory.Ext
        ((DerivedCategory.Q :
            CochainComplex (ModuleCat.{max uA uB uι uN} B) ℤ ⥤ _).obj
          (CochainComplex.mappingCone
            ((CochainComplex.singleFunctor (ModuleCat.{max uA uB uι uN} B) 0).map
              (ModuleCat.ofHom
                (ULift.moduleEquiv.{uB, max (max uA uB) uι,
                  max uA uB uι uN}.symm.toLinearMap.comp
                  ((NaiveCotangent.NL P).d.comp
                    ULift.moduleEquiv.{uB, max uA uι,
                      max uA uB uι uN}.toLinearMap))))))
        ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB uι uN} B) 0).obj
          (ModuleCat.of B (ULift.{max uA uB uι uN} N))) 1 ≃ₗ[B]
      ((P.toExtension.Cotangent →ₗ[B] N) ⧸ LinearMap.range
        ((LinearMap.lcomp B N (NaiveCotangent.NL P).d) :
          (P.toExtension.CotangentSpace →ₗ[B] N) →ₗ[B]
            (P.toExtension.Cotangent →ₗ[B] N))) :=
  presentationCokernelExtOneEquiv P

end Presentation

end NaiveCotangent

end
