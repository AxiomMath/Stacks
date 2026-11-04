module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The relative de Rham complex as a sheaf of differential graded algebras

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a topological space, with
`𝒪_X` the structure sheaf of a ringed space `X`, let `Ω = Ω_{𝒪_X/A}` be the sheaf of relative
differentials and let `B` also denote a package of the three algebras of Stacks Section 17.21 for
`Ω`. Wedge multiplication makes the relative de Rham complex `Ω^•_{𝒪_X/A}` a sheaf of
differential graded `A`-algebras in the sense of
`SheafOfModules.DifferentialGradedAlgebra`: the multiplication is `A`-bilinear and compatible
with restriction, the unit is the unit of the exterior algebra, and the graded Leibniz rule
`d(ω ∧ η) = dω ∧ η + (-1)^p ω ∧ dη` holds.

A sheaf of differential graded algebras carries a `ℤ`-indexed cochain complex, while the de Rham
complex is indexed by `ℕ`, so the complex used is the extension by zero
`AlgebraicGeometry.SheafOfModules.deRhamComplexInt` and the multiplication is zero as soon as one
of the two degrees is negative.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.deRhamTermInt`: the degree-`i` sheaf of relative differential
  forms for an *integer* degree `i`, as a sheaf of `A`-modules.
* `AlgebraicGeometry.SheafOfModules.deRhamMulInt`: wedge multiplication of homogeneous local
  sections in integer degrees, as an `A`-bilinear map of sheaves of `A`-modules.
* `AlgebraicGeometry.SheafOfModules.deRhamComplexIntMul` and
  `AlgebraicGeometry.SheafOfModules.deRhamComplexIntOne`: that multiplication and the exterior
  unit, transported onto the terms of the extended complex.
* `AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra`: **the relative de Rham
  complex as a sheaf of differential graded `A`-algebras.**
* `AlgebraicGeometry.SheafOfModules.relativeDeRhamDifferentialGradedAlgebra`: the same structure
  for the chosen package of algebras and the unique de Rham differential, so depending on `φ`
  alone.

## Main results

* `AlgebraicGeometry.SheafOfModules.d_formProduct`: **the graded Leibniz rule on local sections**,
  `d(ω ∧ η) = dω ∧ η + (-1)^p ω ∧ dη`, for arbitrary local differential forms.
* `AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra_complex`: its underlying
  complex is the relative de Rham complex, extended by zero to negative degrees.
* `AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra_mul` and
  `AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra_one`: its multiplication and
  its unit are wedge multiplication and the unit of the exterior algebra.

## References

* [Stacks Project, Tag 0FU6](https://stacks.math.columbia.edu/tag/0FU6)
* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory ComplexShape Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.SheafOfModules

/-! ### Transport along equalities of sheaves of modules -/

section Transport

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- A bilinear map of sheaves of modules, transported along equalities of its source and target
sheaves. -/
def bilinearMapOfEq {M M' N N' P P' : _root_.SheafOfModules.{u} R}
    (hM : M = M') (hN : N = N') (hP : P = P')
    (m : _root_.SheafOfModules.BilinearMap M N P) :
    _root_.SheafOfModules.BilinearMap M' N' P' := by
  cases hM; cases hN; cases hP; exact m

/-- A transported bilinear map agrees with the original one on local sections identified by the
transport. -/
private theorem bilinearMapOfEq_app_heq {M M' N N' P P' : _root_.SheafOfModules.{u} R}
    (hM : M = M') (hN : N = N') (hP : P = P')
    (m : _root_.SheafOfModules.BilinearMap M N P) (U : Cᵒᵖ)
    (x : M'.val.obj U) (y : N'.val.obj U) (x' : M.val.obj U) (y' : N.val.obj U)
    (hx : HEq x x') (hy : HEq y y') :
    HEq ((bilinearMapOfEq hM hN hP m).app U x y) (m.app U x' y') := by
  cases hM; cases hN; cases hP
  cases eq_of_heq hx; cases eq_of_heq hy
  rfl

/-- A global section of a sheaf of modules, transported along an equality of sheaves. -/
def sectionsOfEq {M M' : _root_.SheafOfModules.{u} R} (h : M = M') (s : M.sections) :
    M'.sections := by
  cases h; exact s

/-- A transported global section has the same local values as the original one. -/
private theorem sectionsOfEq_eval_heq {M M' : _root_.SheafOfModules.{u} R} (h : M = M')
    (s : M.sections) (U : Cᵒᵖ) : HEq ((sectionsOfEq h s).eval U) (s.eval U) := by
  cases h; rfl

/-- A morphism of sheaves of modules transported along equalities of its source and target acts
on local sections as the original morphism. -/
private theorem hom_app_heq {M M' N N' : _root_.SheafOfModules.{u} R} (hM : M = M') (hN : N = N')
    (f : M ⟶ N) (f' : M' ⟶ N') (hf : HEq f f') (U : Cᵒᵖ)
    (x : M.val.obj U) (x' : M'.val.obj U) (hx : HEq x x') :
    HEq (f.val.app U x) (f'.val.app U x') := by
  cases hM; cases hN
  cases eq_of_heq hf; cases eq_of_heq hx
  rfl

/-- The canonical isomorphism between two terms of a cochain complex of equal degree acts
trivially on local sections. -/
private theorem XIsoOfEq_hom_app_heq {ι : Type*} {c : ComplexShape ι}
    {K : HomologicalComplex (_root_.SheafOfModules.{u} R) c} {p q : ι} (h : p = q) (U : Cᵒᵖ)
    (x : (K.X p).val.obj U) : HEq ((K.XIsoOfEq h).hom.val.app U x) x := by
  subst h
  rw [HomologicalComplex.XIsoOfEq_rfl]
  rfl

/-- Transport along an equality of degrees acts trivially on local sections. -/
private theorem gradedCast_heq {ι : Type*} (Y : ι → Type*) {i j : ι} (h : i = j) (x : Y i) :
    HEq (_root_.SheafOfModules.gradedCast Y h x) x := by
  cases h; rfl

/-- Transport along an equality of degrees sends zero to zero. -/
private theorem gradedCast_zero {ι : Type*} (Y : ι → Type*) [∀ i, Zero (Y i)] {i j : ι}
    (h : i = j) : _root_.SheafOfModules.gradedCast Y h 0 = 0 := by
  cases h; rfl

/-- Two zero sections of terms of equal degree are heterogeneously equal. -/
private theorem zero_heq_zero {Y : ℤ → _root_.SheafOfModules.{u} R} {i j : ℤ} (h : i = j)
    (U : Cᵒᵖ) : HEq (0 : (Y i).val.obj U) (0 : (Y j).val.obj U) := by
  cases h; rfl

end Transport

/-- Adding and scaling respect a heterogeneous equality of elements of equal modules. -/
private theorem add_zsmul_heq {S : Type u} [Ring S] {M N : ModuleCat.{u} S} (hMN : M = N)
    (a b : M) (a' b' : N) (ha : HEq a a') (hb : HEq b b') (z : ℤ) :
    HEq (a + z • b) (a' + z • b') := by
  cases hMN; cases eq_of_heq ha; cases eq_of_heq hb; rfl

/-! ### The graded Leibniz rule on local sections -/

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-- A sum of morphisms of sheaves of `A`-modules whose second summand is scaled by an integer
acts summand-wise on a local section. -/
private theorem add_zsmul_val_app
    {M N : _root_.SheafOfModules.{u} (underlyingRingSheaf A)} (f g : M ⟶ N) (z : ℤ)
    (U : (Opens X.carrier)ᵒᵖ) (x : M.val.obj U) :
    (f + z • g).val.app U x = f.val.app U x + z • g.val.app U x := by
  have hz : (z • g).val = z • g.val := (_root_.SheafOfModules.forget _).map_zsmul
  simp only [_root_.SheafOfModules.add_val, PresheafOfModules.add_app, hz,
    PresheafOfModules.zsmul_app, ModuleCat.hom_add, LinearMap.add_apply]
  rfl

/-- A bilinear map of sheaves of modules vanishes when its first argument does. -/
private theorem bilinear_app_eq_zero_left
    {M N P : _root_.SheafOfModules.{u} (underlyingRingSheaf A)}
    (m : _root_.SheafOfModules.BilinearMap M N P) (U : (Opens X.carrier)ᵒᵖ)
    {x : M.val.obj U} (y : N.val.obj U) (hx : x = 0) : m.app U x y = 0 := by
  rw [hx, map_zero, AddMonoidHom.zero_apply]

/-- A bilinear map of sheaves of modules vanishes when its second argument does. -/
private theorem bilinear_app_eq_zero_right
    {M N P : _root_.SheafOfModules.{u} (underlyingRingSheaf A)}
    (m : _root_.SheafOfModules.BilinearMap M N P) (U : (Opens X.carrier)ᵒᵖ)
    (x : M.val.obj U) {y : N.val.obj U} (hy : y = 0) : m.app U x y = 0 := by
  rw [hy, map_zero]

variable (D : DeRhamDifferential B)

/-- **The graded Leibniz rule on local differential forms**:
`d(ω ∧ η) = dω ∧ η + (-1)^p ω ∧ dη`, for arbitrary local sections `ω` of `Ωᵖ` and `η` of `Ωᵠ`.
The two summands on the right, of degrees `p + 1 + q` and `p + (q + 1)`, are read in degree
`p + q + 1` through the reindexing isomorphisms of the complex. -/
theorem d_formProduct (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower q).val.obj U) :
    ((deRhamComplex B D).d (p + q) (p + q + 1)).val.app U (formProduct B p q U ω η) =
      ((deRhamComplex B D).XIsoOfEq (show p + 1 + q = p + q + 1 by omega)).hom.val.app U
          (formProduct B (p + 1) q U (((deRhamComplex B D).d p (p + 1)).val.app U ω) η) +
        (-1 : ℤ) ^ p •
          ((deRhamComplex B D).XIsoOfEq (show p + (q + 1) = p + q + 1 by omega)).hom.val.app U
            (formProduct B p (q + 1) U ω (((deRhamComplex B D).d q (q + 1)).val.app U η)) := by
  have key := congrArg
    (fun f : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A).obj (deRhamTerm B p)).obj
      (deRhamTerm B q) ⟶
        (deRhamComplex B D).X (p + q + 1) =>
      f.val.app U (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
        (PresheafOfModules.tensorObj ((deRhamTerm B p)).val ((deRhamTerm B q)).val)).app U
          (ω ⊗ₜ[A.obj.obj U] η)))
    (exteriorProductComponent_d B D p q)
  refine Eq.trans ?_ ((key.trans (add_zsmul_val_app _ _ _ U _)).trans ?_)
  · exact congrArg (fun z => ((deRhamComplex B D).d (p + q) (p + q + 1)).val.app U z)
      (exteriorProductComponent_unit_apply B p q U ω η).symm
  · refine congrArg₂ (· + ·) ?_ (congrArg (fun z => (-1 : ℤ) ^ p • z) ?_)
    · refine congrArg (fun z => ((deRhamComplex B D).XIsoOfEq
        (show p + 1 + q = p + q + 1 by omega)).hom.val.app U z) ?_
      exact (congrArg (fun z => (exteriorProductComponent B (p + 1) q).val.app U z)
        (tensorFunctor_map_unit_apply (N := deRhamTerm B q)
          ((deRhamComplex B D).d p (p + 1)) U ω η)).trans
        (exteriorProductComponent_unit_apply B (p + 1) q U
          (((deRhamComplex B D).d p (p + 1)).val.app U ω) η)
    · refine congrArg (fun z => ((deRhamComplex B D).XIsoOfEq
        (show p + (q + 1) = p + q + 1 by omega)).hom.val.app U z) ?_
      exact (congrArg (fun z => (exteriorProductComponent B p (q + 1)).val.app U z)
        (tensorFunctor_obj_map_unit_apply (M := deRhamTerm B p)
          ((deRhamComplex B D).d q (q + 1)) U ω η)).trans
        (exteriorProductComponent_unit_apply B p (q + 1) U ω
          (((deRhamComplex B D).d q (q + 1)).val.app U η))

/-! ### The graded pieces and their multiplication in integer degrees -/

/-- The sheaf `Ω^i_{𝒪_X/A}` of relative differential forms of an **integer** degree `i`, as a
sheaf of `A`-modules: the degree-`i` piece of the exterior algebra of `Ω`, with scalars
restricted along `φ`. For `i = (p : ℕ)` this is `AlgebraicGeometry.SheafOfModules.deRhamTerm`,
and for `i < 0` its local sections all vanish. -/
noncomputable abbrev deRhamTermInt (i : ℤ) : _root_.SheafOfModules.{u} (underlyingRingSheaf A) :=
  (_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).obj (B.exterior.piece i)

/-- **Wedge multiplication of homogeneous local differential forms in integer degrees**, as a
bilinear map of sheaves of `A`-modules. It is the multiplication of the exterior algebra of `Ω`,
which is bilinear over `𝒪_X` and hence over `A`. -/
noncomputable def deRhamMulInt (i j : ℤ) :
    _root_.SheafOfModules.BilinearMap (deRhamTermInt B i) (deRhamTermInt B j)
      (deRhamTermInt B (i + j)) where
  app U := (B.exterior.mul i j).app U
  map_smul_left U r x y := (B.exterior.mul i j).map_smul_left U (φ.hom.app U r) x y
  map_smul_right U r x y := (B.exterior.mul i j).map_smul_right U (φ.hom.app U r) x y
  naturality f x y := (B.exterior.mul i j).naturality f x y

/-- In a nonnegative degree the term of the relative de Rham complex extended by zero is equal,
not merely isomorphic, to the corresponding piece of the exterior algebra of `Ω`. -/
theorem deRhamComplexInt_X_of_nonneg (i : ℤ) (hi : 0 ≤ i) :
    (deRhamComplexInt B D).X i = deRhamTermInt B i := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  show HomologicalComplex.extend.X (deRhamComplex B D)
      (embeddingUpNat.r (embeddingUpNat.f p)) =
    HomologicalComplex.extend.X (deRhamComplex B D) (some p)
  exact congrArg (HomologicalComplex.extend.X (deRhamComplex B D)) (embeddingUpNat.r_f p)

/-- In nonnegative degrees the differential of the extended complex is the de Rham
differential. -/
private theorem deRhamComplexInt_d_heq (p q : ℕ) :
    HEq ((deRhamComplexInt B D).d (p : ℤ) (q : ℤ)) ((deRhamComplex B D).d p q) := by
  show HEq (HomologicalComplex.extend.d (deRhamComplex B D)
    (embeddingUpNat.r (embeddingUpNat.f p)) (embeddingUpNat.r (embeddingUpNat.f q))) _
  rw [embeddingUpNat.r_f p, embeddingUpNat.r_f q]
  rfl

/-- In nonnegative degrees the differential of the extended complex acts on local sections as
the de Rham differential. -/
private theorem deRhamComplexInt_d_app_heq (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((deRhamComplexInt B D).X (p : ℤ)).val.obj U) (x' : (deRhamTerm B p).val.obj U)
    (hx : HEq x x') :
    HEq (((deRhamComplexInt B D).d (p : ℤ) (q : ℤ)).val.app U x)
      (((deRhamComplex B D).d p q).val.app U x') :=
  hom_app_heq (deRhamComplexInt_X_of_nonneg B D (p : ℤ) (Int.natCast_nonneg p))
    (deRhamComplexInt_X_of_nonneg B D (q : ℤ) (Int.natCast_nonneg q)) _ _
    (deRhamComplexInt_d_heq B D p q) U x x' hx

/-- The same statement with the two degrees presented as integers. -/
private theorem deRhamComplexInt_d_app_heq_of_degrees (i j : ℤ) (p q : ℕ)
    (hi : i = (p : ℤ)) (hj : j = (q : ℤ)) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((deRhamComplexInt B D).X i).val.obj U) (x' : (deRhamTerm B p).val.obj U)
    (hx : HEq x x') :
    HEq (((deRhamComplexInt B D).d i j).val.app U x)
      (((deRhamComplex B D).d p q).val.app U x') := by
  subst hi hj
  exact deRhamComplexInt_d_app_heq B D p q U x x' hx

/-- Every local section of a negative-degree term of the extended complex vanishes: that term is
a zero sheaf. -/
private theorem deRhamComplexInt_section_eq_zero (i : ℤ) (hi : i < 0)
    (U : (Opens X.carrier)ᵒᵖ) (x : ((deRhamComplexInt B D).X i).val.obj U) : x = 0 := by
  have hz : Limits.IsZero ((deRhamComplexInt B D).X i) := by
    refine (deRhamComplex B D).isZero_extend_X embeddingUpNat i fun n hn => ?_
    exact absurd hi (not_lt_of_ge (hn ▸ Int.natCast_nonneg n))
  let ev : _root_.SheafOfModules.{u} (underlyingRingSheaf A) ⥤
      ModuleCat.{u} ((underlyingRingSheaf A).obj.obj U) :=
    _root_.SheafOfModules.evaluation (underlyingRingSheaf A) U
  have hev : ev.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  exact (ModuleCat.isZero_iff_subsingleton.mp (Functor.map_isZero ev hz)).elim x 0

/-- Every local section of a nonnegative-degree term of the extended complex is, up to the
transport of `AlgebraicGeometry.SheafOfModules.deRhamComplexInt_X_of_nonneg`, a local section of
the corresponding piece of the exterior algebra. -/
private theorem exists_heq_piece (i : ℤ) (hi : 0 ≤ i) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((deRhamComplexInt B D).X i).val.obj U) :
    ∃ x' : (B.exterior.piece i).val.obj U, HEq x x' :=
  ⟨cast (congrArg (fun M : _root_.SheafOfModules.{u} (underlyingRingSheaf A) =>
    (M.val.obj U : Type u)) (deRhamComplexInt_X_of_nonneg B D i hi)) x, (cast_heq _ x).symm⟩

/-! ### The multiplication and the unit of the differential graded algebra -/

/-- Wedge multiplication on the terms of the relative de Rham complex extended by zero, in a pair
of nonnegative degrees: the multiplication of the exterior algebra, transported along
`AlgebraicGeometry.SheafOfModules.deRhamComplexInt_X_of_nonneg`. -/
noncomputable def deRhamComplexIntMulOfNonneg (i j : ℤ) (hi : 0 ≤ i) (hj : 0 ≤ j) :
    _root_.SheafOfModules.BilinearMap ((deRhamComplexInt B D).X i) ((deRhamComplexInt B D).X j)
      ((deRhamComplexInt B D).X (i + j)) :=
  bilinearMapOfEq (deRhamComplexInt_X_of_nonneg B D i hi).symm
    (deRhamComplexInt_X_of_nonneg B D j hj).symm
    (deRhamComplexInt_X_of_nonneg B D (i + j) (by omega)).symm (deRhamMulInt B i j)

/-- The zero bilinear map from the terms of degrees `i` and `j` of the relative de Rham complex
extended by zero to its term of degree `i + j`. -/
noncomputable def deRhamComplexIntMulZero (i j : ℤ) :
    _root_.SheafOfModules.BilinearMap ((deRhamComplexInt B D).X i) ((deRhamComplexInt B D).X j)
      ((deRhamComplexInt B D).X (i + j)) where
  app _ := 0
  map_smul_left _ r _ _ := (smul_zero r).symm
  map_smul_right _ r _ _ := (smul_zero r).symm
  naturality _ _ _ := map_zero _

/-- **The multiplication of the relative de Rham differential graded algebra**: wedge
multiplication in nonnegative degrees, and zero as soon as one of the two degrees is negative. -/
noncomputable def deRhamComplexIntMul (i j : ℤ) :
    _root_.SheafOfModules.BilinearMap ((deRhamComplexInt B D).X i) ((deRhamComplexInt B D).X j)
      ((deRhamComplexInt B D).X (i + j)) :=
  if hi : 0 ≤ i then
    if hj : 0 ≤ j then deRhamComplexIntMulOfNonneg B D i j hi hj
    else deRhamComplexIntMulZero B D i j
  else deRhamComplexIntMulZero B D i j

/-- In nonnegative degrees the multiplication is the transported exterior multiplication. -/
private theorem deRhamComplexIntMul_of_nonneg (i j : ℤ) (hi : 0 ≤ i) (hj : 0 ≤ j) :
    deRhamComplexIntMul B D i j = deRhamComplexIntMulOfNonneg B D i j hi hj := by
  simp [deRhamComplexIntMul, hi, hj]

/-- In nonnegative degrees the multiplication acts on local sections as the multiplication of the
exterior algebra. -/
private theorem deRhamComplexIntMul_app_heq (i j : ℤ) (hi : 0 ≤ i) (hj : 0 ≤ j)
    (U : (Opens X.carrier)ᵒᵖ) (x : ((deRhamComplexInt B D).X i).val.obj U)
    (y : ((deRhamComplexInt B D).X j).val.obj U)
    (x' : (B.exterior.piece i).val.obj U) (y' : (B.exterior.piece j).val.obj U)
    (hx : HEq x x') (hy : HEq y y') :
    HEq ((deRhamComplexIntMul B D i j).app U x y) ((B.exterior.mul i j).app U x' y') := by
  rw [deRhamComplexIntMul_of_nonneg B D i j hi hj]
  exact bilinearMapOfEq_app_heq _ _ _ (deRhamMulInt B i j) U x y x' y' hx hy

/-- **The unit of the relative de Rham differential graded algebra**: the unit of the exterior
algebra of `Ω`, read as a global section of the degree-zero term of the extended complex. -/
noncomputable def deRhamComplexIntOne : ((deRhamComplexInt B D).X 0).sections :=
  sectionsOfEq (deRhamComplexInt_X_of_nonneg B D 0 le_rfl).symm B.exterior.one

/-- The unit of the differential graded algebra has the same local values as the exterior
unit. -/
private theorem deRhamComplexIntOne_eval_heq (U : (Opens X.carrier)ᵒᵖ) :
    HEq ((deRhamComplexIntOne B D).eval U) (B.exterior.one.eval U) :=
  sectionsOfEq_eval_heq (deRhamComplexInt_X_of_nonneg B D 0 le_rfl).symm B.exterior.one U

/-! ### The Leibniz rule in nonnegative integer degrees -/

/-- The graded Leibniz rule for the transported multiplication, in a pair of nonnegative
degrees. -/
private theorem deRhamComplexIntMul_leibniz_of_nonneg (n m : ℤ) (hn : 0 ≤ n) (hm : 0 ≤ m)
    (U : (Opens X.carrier)ᵒᵖ) (x : ((deRhamComplexInt B D).X n).val.obj U)
    (y : ((deRhamComplexInt B D).X m).val.obj U) :
    ((deRhamComplexInt B D).d (n + m) (n + m + 1)).val.app U
        ((deRhamComplexIntMul B D n m).app U x y) =
      _root_.SheafOfModules.gradedCast
          (fun k => ((deRhamComplexInt B D).X k).val.obj U) (add_right_comm n 1 m)
          ((deRhamComplexIntMul B D (n + 1) m).app U
            (((deRhamComplexInt B D).d n (n + 1)).val.app U x) y) +
        (Int.negOnePow n : ℤ) •
          _root_.SheafOfModules.gradedCast
            (fun k => ((deRhamComplexInt B D).X k).val.obj U) (add_assoc n m 1).symm
            ((deRhamComplexIntMul B D n (m + 1)).app U x
              (((deRhamComplexInt B D).d m (m + 1)).val.app U y)) := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  obtain ⟨x', hx⟩ := exists_heq_piece B D (p : ℤ) hn U x
  obtain ⟨y', hy⟩ := exists_heq_piece B D (q : ℤ) hm U y
  have hmul : HEq ((deRhamComplexIntMul B D (p : ℤ) (q : ℤ)).app U x y)
      (formProduct B p q U x' y') :=
    deRhamComplexIntMul_app_heq B D _ _ hn hm U x y x' y' hx hy
  have hleft := deRhamComplexInt_d_app_heq_of_degrees B D ((p : ℤ) + q) ((p : ℤ) + q + 1)
    (p + q) (p + q + 1) (by simp) (by simp) U _ _ hmul
  have hdx := deRhamComplexInt_d_app_heq_of_degrees B D (p : ℤ) ((p : ℤ) + 1) p (p + 1)
    rfl (by simp) U x x' hx
  have hdy := deRhamComplexInt_d_app_heq_of_degrees B D (q : ℤ) ((q : ℤ) + 1) q (q + 1)
    rfl (by simp) U y y' hy
  have hfirst : HEq ((deRhamComplexIntMul B D ((p : ℤ) + 1) (q : ℤ)).app U
        (((deRhamComplexInt B D).d (p : ℤ) ((p : ℤ) + 1)).val.app U x) y)
      (formProduct B (p + 1) q U (((deRhamComplex B D).d p (p + 1)).val.app U x') y') :=
    deRhamComplexIntMul_app_heq B D _ _ (by omega) hm U _ y _ y' hdx hy
  have hsecond : HEq ((deRhamComplexIntMul B D (p : ℤ) ((q : ℤ) + 1)).app U x
        (((deRhamComplexInt B D).d (q : ℤ) ((q : ℤ) + 1)).val.app U y))
      (formProduct B p (q + 1) U x' (((deRhamComplex B D).d q (q + 1)).val.app U y')) :=
    deRhamComplexIntMul_app_heq B D _ _ hn (by omega) U x _ x' _ hx hdy
  have hcast₁ := (gradedCast_heq (fun k => ((deRhamComplexInt B D).X k).val.obj U)
    (add_right_comm (p : ℤ) 1 (q : ℤ)) _).trans hfirst
  have hcast₂ := (gradedCast_heq (fun k => ((deRhamComplexInt B D).X k).val.obj U)
    (add_assoc (p : ℤ) (q : ℤ) 1).symm _).trans hsecond
  have hXIso₁ := XIsoOfEq_hom_app_heq (K := deRhamComplex B D)
    (show p + 1 + q = p + q + 1 by omega) U
    (formProduct B (p + 1) q U (((deRhamComplex B D).d p (p + 1)).val.app U x') y')
  have hXIso₂ := XIsoOfEq_hom_app_heq (K := deRhamComplex B D)
    (show p + (q + 1) = p + q + 1 by omega) U
    (formProduct B p (q + 1) U x' (((deRhamComplex B D).d q (q + 1)).val.app U y'))
  have hpiece : ((deRhamComplexInt B D).X ((p : ℤ) + q + 1)).val.obj U =
      (deRhamTerm B (p + q + 1)).val.obj U := by
    have hi : (p : ℤ) + q + 1 = ((p + q + 1 : ℕ) : ℤ) := by omega
    rw [hi]
    exact congrArg (fun M : _root_.SheafOfModules.{u} (underlyingRingSheaf A) => M.val.obj U)
      (deRhamComplexInt_X_of_nonneg B D ((p + q + 1 : ℕ) : ℤ) (by omega))
  have hneg : (Int.negOnePow (p : ℤ) : ℤ) = (-1 : ℤ) ^ p := Int.coe_negOnePow_natCast p
  rw [hneg]
  refine eq_of_heq (hleft.trans ((heq_of_eq (d_formProduct B D p q U x' y')).trans ?_))
  exact (add_zsmul_heq hpiece _ _ _ _ (hcast₁.trans hXIso₁.symm)
    (hcast₂.trans hXIso₂.symm) ((-1 : ℤ) ^ p)).symm

/-! ### The differential graded algebra -/

/-- The relative de Rham complex of `φ`, with wedge multiplication and the unit of the exterior
algebra, as a sheaf of differential graded `A`-algebras. -/
@[stacks 0FU6 "relative_de_rham_dga"]
noncomputable def deRhamDifferentialGradedAlgebra :
    _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (underlyingRingSheaf A) where
  complex := deRhamComplexInt B D
  mul := deRhamComplexIntMul B D
  one := deRhamComplexIntOne B D
  mul_assoc n m k U x y z := by
    by_cases hn : 0 ≤ n
    · by_cases hm : 0 ≤ m
      · by_cases hk : 0 ≤ k
        · obtain ⟨x', hx⟩ := exists_heq_piece B D n hn U x
          obtain ⟨y', hy⟩ := exists_heq_piece B D m hm U y
          obtain ⟨z', hz⟩ := exists_heq_piece B D k hk U z
          have hxy := deRhamComplexIntMul_app_heq B D n m hn hm U x y x' y' hx hy
          have hyz := deRhamComplexIntMul_app_heq B D m k hm hk U y z y' z' hy hz
          refine (deRhamComplexIntMul_app_heq B D (n + m) k (by omega) hk U _ z _ z'
            hxy hz).trans (((B.exterior.mul_assoc n m k U x' y' z').trans ?_))
          exact (deRhamComplexIntMul_app_heq B D n (m + k) hn (by omega) U x _ x' _
            hx hyz).symm
        · have hz0 := deRhamComplexInt_section_eq_zero B D k (by omega) U z
          rw [bilinear_app_eq_zero_right _ U _ hz0,
            bilinear_app_eq_zero_right _ U _ (bilinear_app_eq_zero_right _ U y hz0)]
          exact zero_heq_zero (Y := (deRhamComplexInt B D).X) (add_assoc n m k) U
      · have hy0 := deRhamComplexInt_section_eq_zero B D m (by omega) U y
        rw [bilinear_app_eq_zero_left _ U _ (bilinear_app_eq_zero_right _ U x hy0),
          bilinear_app_eq_zero_right _ U _ (bilinear_app_eq_zero_left _ U z hy0)]
        exact zero_heq_zero (Y := (deRhamComplexInt B D).X) (add_assoc n m k) U
    · have hx0 := deRhamComplexInt_section_eq_zero B D n (by omega) U x
      rw [bilinear_app_eq_zero_left _ U _ (bilinear_app_eq_zero_left _ U y hx0),
        bilinear_app_eq_zero_left _ U _ hx0]
      exact zero_heq_zero (Y := (deRhamComplexInt B D).X) (add_assoc n m k) U
  one_mul n U x := by
    by_cases hn : 0 ≤ n
    · obtain ⟨x', hx⟩ := exists_heq_piece B D n hn U x
      refine (deRhamComplexIntMul_app_heq B D 0 n le_rfl hn U _ x _ x'
        (deRhamComplexIntOne_eval_heq B D U) hx).trans ?_
      exact (B.exterior.one_mul n U x').trans hx.symm
    · have hx0 := deRhamComplexInt_section_eq_zero B D n (by omega) U x
      rw [bilinear_app_eq_zero_right _ U _ hx0, hx0]
      exact zero_heq_zero (Y := (deRhamComplexInt B D).X) (zero_add n) U
  mul_one n U x := by
    by_cases hn : 0 ≤ n
    · obtain ⟨x', hx⟩ := exists_heq_piece B D n hn U x
      refine (deRhamComplexIntMul_app_heq B D n 0 hn le_rfl U x _ x' _
        hx (deRhamComplexIntOne_eval_heq B D U)).trans ?_
      exact (B.exterior.mul_one n U x').trans hx.symm
    · have hx0 := deRhamComplexInt_section_eq_zero B D n (by omega) U x
      rw [bilinear_app_eq_zero_left _ U _ hx0, hx0]
      exact zero_heq_zero (Y := (deRhamComplexInt B D).X) (add_zero n) U
  leibniz n m U x y := by
    by_cases hn : 0 ≤ n
    · by_cases hm : 0 ≤ m
      · exact deRhamComplexIntMul_leibniz_of_nonneg B D n m hn hm U x y
      · have hy0 := deRhamComplexInt_section_eq_zero B D m (by omega) U y
        rw [bilinear_app_eq_zero_right _ U x hy0, map_zero,
          bilinear_app_eq_zero_right _ U _ hy0,
          bilinear_app_eq_zero_right _ U x (by rw [hy0, map_zero]),
          gradedCast_zero, gradedCast_zero, smul_zero, add_zero]
    · have hx0 := deRhamComplexInt_section_eq_zero B D n (by omega) U x
      rw [bilinear_app_eq_zero_left _ U y hx0, map_zero,
        bilinear_app_eq_zero_left _ U y (by rw [hx0, map_zero]),
        bilinear_app_eq_zero_left _ U _ hx0,
        gradedCast_zero, gradedCast_zero, smul_zero, add_zero]

/-- The complex underlying the relative de Rham differential graded algebra is the relative de
Rham complex, extended by zero to negative degrees. -/
@[stacks 0FU6 "relative_de_rham_dga"]
theorem deRhamDifferentialGradedAlgebra_complex :
    (deRhamDifferentialGradedAlgebra B D).complex = deRhamComplexInt B D := rfl

/-- Multiplication in the relative de Rham differential graded algebra is wedge multiplication of
differential forms, on every pair of homogeneous local sections. -/
@[stacks 0FU6 "relative_de_rham_dga"]
theorem deRhamDifferentialGradedAlgebra_mul (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : ((deRhamDifferentialGradedAlgebra B D).complex.X (p : ℤ)).val.obj U)
    (η : ((deRhamDifferentialGradedAlgebra B D).complex.X (q : ℤ)).val.obj U)
    (ω' : (B.exteriorPower p).val.obj U) (η' : (B.exteriorPower q).val.obj U)
    (hω : HEq ω ω') (hη : HEq η η') :
    HEq (((deRhamDifferentialGradedAlgebra B D).mul (p : ℤ) (q : ℤ)).app U ω η)
      (formProduct B p q U ω' η') :=
  deRhamComplexIntMul_app_heq B D (p : ℤ) (q : ℤ) (Int.natCast_nonneg p) (Int.natCast_nonneg q)
    U ω η ω' η' hω hη

/-- The unit of the relative de Rham differential graded algebra is the unit of the exterior
algebra of `Ω`. -/
@[stacks 0FU6 "relative_de_rham_dga"]
theorem deRhamDifferentialGradedAlgebra_one (U : (Opens X.carrier)ᵒᵖ) :
    HEq ((deRhamDifferentialGradedAlgebra B D).one.eval U) (B.exterior.one.eval U) :=
  deRhamComplexIntOne_eval_heq B D U

/-- The relative de Rham complex of `φ` with no choices left open: the differential graded algebra
of `AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra` for the chosen package of
algebras `AlgebraicGeometry.SheafOfModules.differentialAlgebras` and the de Rham differential
`AlgebraicGeometry.SheafOfModules.deRhamDifferential`, which by
`AlgebraicGeometry.SheafOfModules.deRhamDifferential_unique` is the only one. -/
noncomputable def relativeDeRhamDifferentialGradedAlgebra (φ : A ⟶ X.sheaf) :
    _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (underlyingRingSheaf A) :=
  deRhamDifferentialGradedAlgebra (differentialAlgebras φ)
    (deRhamDifferential (differentialAlgebras φ))

end AlgebraicGeometry.SheafOfModules

end
