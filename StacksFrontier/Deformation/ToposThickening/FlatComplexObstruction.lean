module

public import StacksFrontier.Deformation.ToposThickening.IdealKernelExistence
public import StacksFrontier.Deformation.ToposThickening.DerivedComplexLift
public import StacksFrontier.Deformation.ToposThickening.SquareZeroReductionTriangle
public import StacksFrontier.Deformation.ToposThickening.FlatTensorAmplitude
import StacksCore.Tactic.StacksAttribute

/-!
# A bounded above complex of flat modules over the thickening has vanishing obstruction

Let `f : O ⟶ O₀` be a locally surjective morphism of sheaves of commutative rings on a site
whose kernel is a square-zero ideal sheaf `I`. A bounded above complex `P` of flat `O`-modules
is in particular a bounded above flat lift, in the sense of Tag 0DIU, of its degreewise
extension of scalars `P₀ = O₀ ⊗_O P`: the graded family is `P` itself, its reduction is the
unit of extension and restriction of scalars, and the reduction of the differential is the
differential of `P₀`. Since the differential of `P` squares to zero, the canonical class
`ω(P₀)` vanishes.

So the implication `(2) ⇒ (1)` of Tag 0DIW holds in the generality of the source: if a bounded
above object `K₀` of `D(O₀)` is `K ⊗^L_O O₀` for some `K ∈ D⁻(O)`, then `ω(K₀) = 0`. Represent
`K` by a bounded above complex `P` of flat `O`-modules; then `K ⊗^L_O O₀` is represented by
`P₀`, whose class vanishes, and `ω` is natural along the identification `P₀ ≅ K₀` in `D(O₀)`.

## Main definitions

* `Deformation.ComplexLift.flatComplexGraded`: the graded family underlying a complex.
* `Deformation.ComplexLift.flatComplexBaseChange`: the reduction of a complex of `O`-modules by
  degreewise extension of scalars, as a base-change datum.
* `Deformation.ComplexLift.FlatLift.ofFlatComplex`: a bounded above complex of flat `O`-modules
  as a flat lift of its reduction.

## Main results

* `Deformation.ComplexLift.isExtensionOfScalars_extendRestrictAdjunction_unit`: the unit of
  extension and restriction of scalars has the universal property of extension of scalars.
* `Deformation.ComplexLift.FlatLift.isFlat_reduction`: the reduction of a flat lift has flat
  terms.
* `Deformation.ComplexLift.omega_eq_zero_of_flatComplex`: `ω(P₀) = 0`.
* `Deformation.ComplexLift.omega_eq_zero_of_nonempty_derivedLift`: **Tag 0DIW, `(2) ⇒ (1)`**.

## References

* [Stacks Project, Tag 0DIW](https://stacks.math.columbia.edu/tag/0DIW)
* [Stacks Project, Tag 0DIU](https://stacks.math.columbia.edu/tag/0DIU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.ComplexLifting (GradedDifferential BaseChangeTo
  IsExtensionOfScalars)

universe v u w d d₀

namespace Deformation.ComplexLift

attribute [-instance] CategoryTheory.catToReflQuiver

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  {O O₀ : Sheaf J CommRingCat.{max u v w}} {f : O ⟶ O₀}

section FlatComplex

variable (f) in
/-- The unit of extension and restriction of scalars has the universal property of extension of
scalars: composing with it is the adjunction bijection. -/
theorem isExtensionOfScalars_extendRestrictAdjunction_unit (M : SheafMod O) :
    IsExtensionOfScalars f M ((extensionOfScalars f).obj M)
      ((extendRestrictAdjunction f).unit.app M) := by
  intro N
  have h := ((extendRestrictAdjunction f).homEquiv M N).bijective
  have e : ⇑((extendRestrictAdjunction f).homEquiv M N) = fun a =>
      (extendRestrictAdjunction f).unit.app M ≫
        (SheafOfModules.restrictScalars (ringSheafMapOf J f)).map a :=
    funext fun a => (extendRestrictAdjunction f).homEquiv_unit M N a
  rw [e] at h
  exact h

/-- Two morphisms with the universal property of extension of scalars out of the same module
have isomorphic targets. -/
def isExtensionOfScalarsIso {M : SheafMod O} {A B : SheafMod O₀}
    {a : M ⟶ (restrict f).obj A} {b : M ⟶ (restrict f).obj B}
    (ha : IsExtensionOfScalars f M A a) (hb : IsExtensionOfScalars f M B b) : A ≅ B where
  hom := IsExtensionOfScalars.desc.{v, u, max u v w, max u v w} f ha b
  inv := IsExtensionOfScalars.desc.{v, u, max u v w, max u v w} f hb a
  hom_inv_id := by
    apply (ha A).injective
    change a ≫ (restrict f).map (_ ≫ _) = a ≫ (restrict f).map (𝟙 _)
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, IsExtensionOfScalars.desc_spec,
      IsExtensionOfScalars.desc_spec, CategoryTheory.Functor.map_id, Category.comp_id]
  inv_hom_id := by
    apply (hb B).injective
    change b ≫ (restrict f).map (_ ≫ _) = b ≫ (restrict f).map (𝟙 _)
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, IsExtensionOfScalars.desc_spec,
      IsExtensionOfScalars.desc_spec, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The graded family underlying a complex of `O`-modules. -/
def flatComplexGraded (P : CochainComplex (SheafMod O) ℤ) : GradedDifferential (SheafMod O) where
  X := P.X
  d n := P.d n (n + 1)

variable (f) in
/-- The unit `P^n ⟶ (O₀ ⊗_O P^n)|_O` of extension and restriction of scalars. -/
def flatComplexUnit (P : CochainComplex (SheafMod O) ℤ) (n : ℤ) :
    P.X n ⟶ (restrict f).obj (((extensionOfScalarsCochainComplex J f).obj P).X n) :=
  (extendRestrictAdjunction f).unit.app (P.X n)

/-- The unit `P^n ⟶ (O₀ ⊗_O P^n)|_O` has the universal property of extension of scalars. -/
theorem flatComplexUnit_isExtension (P : CochainComplex (SheafMod O) ℤ) (n : ℤ) :
    IsExtensionOfScalars f (P.X n) (((extensionOfScalarsCochainComplex J f).obj P).X n)
      (flatComplexUnit f P n) :=
  isExtensionOfScalars_extendRestrictAdjunction_unit f (P.X n)

/-- The units `P^n ⟶ (O₀ ⊗_O P^n)|_O` commute with the differentials of `P` and of
`O₀ ⊗_O P`. -/
@[reassoc]
theorem flatComplexUnit_naturality (P : CochainComplex (SheafMod O) ℤ) (i j : ℤ) :
    P.d i j ≫ flatComplexUnit f P j =
      flatComplexUnit f P i ≫
        (restrict f).map (((extensionOfScalarsCochainComplex J f).obj P).d i j) :=
  (extendRestrictAdjunction f).unit.naturality (P.d i j)

variable (f) in
/-- The reduction of a complex of `O`-modules by degreewise extension of scalars, as the
base-change datum of Stacks 0DIT: the units are those of extension and restriction of scalars,
and the reduction is the identity of `O₀ ⊗_O P`. -/
def flatComplexBaseChange (P : CochainComplex (SheafMod O) ℤ) :
    BaseChangeTo f (flatComplexGraded P) ((extensionOfScalarsCochainComplex J f).obj P)
      (flatComplexUnit f P) where
  complex := (extensionOfScalarsCochainComplex J f).obj P
  unit := flatComplexUnit f P
  isExtension := flatComplexUnit_isExtension P
  differential n := flatComplexUnit_naturality P n (n + 1)
  map := 𝟙 _
  map_unit _n := Category.comp_id _

/-- The map of reductions of `flatComplexBaseChange f P` is the identity of `O₀ ⊗_O P`. -/
theorem flatComplexBaseChange_map (P : CochainComplex (SheafMod O) ℤ) :
    (flatComplexBaseChange f P).map = 𝟙 _ := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The identity of a complex of `O₀`-modules is a quasi-isomorphism. -/
theorem quasiIso_id_of_flatComplex (K : CochainComplex (SheafMod O₀) ℤ) : QuasiIso (𝟙 K) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap, HomologicalComplex.homologyMap_id]
  infer_instance

variable (f) in
/-- **A bounded above complex of flat `O`-modules is a flat lift of its reduction.** The graded
family is the complex itself, its reduction is degreewise extension of scalars, and the induced
map of reductions is the identity. -/
def FlatLift.ofFlatComplex (P : CochainComplex (SheafMod O) ℤ)
    (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (O := O) (P.X n))
    (hbdd : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (P.X n)) :
    FlatLift f ((extensionOfScalarsCochainComplex J f).obj P) where
  F := flatComplexGraded P
  flat := hflat
  boundedAbove := hbdd
  toTarget := flatComplexUnit f P
  baseChange := flatComplexBaseChange f P
  quasiIso := quasiIso_id_of_flatComplex _

/-- The units of the base-change datum of `FlatLift.ofFlatComplex f P hflat hbdd` are the units
`flatComplexUnit f P n` of extension and restriction of scalars. -/
theorem FlatLift.ofFlatComplex_baseChange_unit (P : CochainComplex (SheafMod O) ℤ)
    (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (O := O) (P.X n))
    (hbdd : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (P.X n)) (n : ℤ) :
    (FlatLift.ofFlatComplex f P hflat hbdd).baseChange.unit n = flatComplexUnit f P n := rfl

/-- The reduction of a flat lift has flat terms: each is an extension of scalars of a flat
module. -/
theorem FlatLift.isFlat_reduction {K₀ : CochainComplex (SheafMod O₀) ℤ} (L : FlatLift f K₀)
    (n : ℤ) : AlgebraicGeometry.SheafOfModules.IsFlat (O := O₀) (L.baseChange.complex.X n) :=
  flatObjects_of_iso
    (isExtensionOfScalarsIso (isExtensionOfScalars_extendRestrictAdjunction_unit f (L.F.X n))
      (L.baseChange.isExtension n))
    (flatObjects_extensionOfScalars f (L.flat n))

/-- The reduction of a flat lift vanishes in the degrees in which the lift vanishes. -/
theorem FlatLift.isZero_reduction {K₀ : CochainComplex (SheafMod O₀) ℤ} (L : FlatLift f K₀)
    {n : ℤ} (hn : IsZero (L.F.X n)) : IsZero (L.baseChange.complex.X n) :=
  Stacks.SheafOfModules.ComplexLifting.isZero_of_isExtensionOfScalars f
    (L.baseChange.isExtension n) hn

end FlatComplex

section Forward

variable {I : SheafMod O₀}
  [((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I).Additive]
  [HasDerivedCategory.{d₀} (SheafMod O₀)]

/-- **The canonical class of the reduction of a bounded above complex of flat `O`-modules
vanishes.** The complex is a flat lift of its reduction whose lifted differential squares to
zero. -/
theorem omega_eq_zero_of_flatComplex (hf : Sheaf.IsLocallySurjective f)
    (S : SquareZeroIdeal f I) (D : DerivedIdealTensor I) (P : CochainComplex (SheafMod O) ℤ)
    (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (O := O) (P.X n))
    (hbdd : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (P.X n))
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      IsZero (((extensionOfScalarsCochainComplex J f).obj P).homology n)) :
    omega hf S D ((extensionOfScalarsCochainComplex J f).obj P) hK = 0 := by
  rw [omega_eq hf S D hK (idealKernel hf S (FlatLift.ofFlatComplex f P hflat hbdd))]
  exact obstructionMap_eq_zero_of_dd_eq_zero _ (fun n => P.d_comp_d _ _ _) D

variable [HasDerivedCategory.{d} (SheafMod O)]

/-- **Stacks 0DIW, `(2) ⇒ (1)`.** Let `K₀ ∈ D⁻(O₀)`, represented by a complex `K₀'` of
`O₀`-modules. If there is `K ∈ D⁻(O)` with `K ⊗^L_O O₀ ≅ K₀` in `D(O₀)` (for any derived base
change `T` along `f`), then the canonical class `ω(K₀')` of Tag 0DIU vanishes.

Represent `K` by a bounded above complex `P` of flat `O`-modules. Its derived base change is
then represented by the degreewise reduction `P₀`, whose class vanishes because the
differential of `P` squares to zero; and `ω` is natural along the resulting isomorphism
`P₀ ≅ K₀'` of `D(O₀)`. -/
theorem omega_eq_zero_of_nonempty_derivedLift (hf : Sheaf.IsLocallySurjective f)
    (S : SquareZeroIdeal f I) (D : DerivedIdealTensor I) (T : DerivedExtensionOfScalars f)
    (E : DerivedCategory.Minus (SheafMod O₀)) (K₀ : CochainComplex (SheafMod O₀) ℤ)
    (e : DerivedCategory.Q.obj K₀ ≅ E.obj)
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n))
    (hL : Nonempty (DerivedLift T E)) : omega hf S D K₀ hK = 0 := by
  obtain ⟨L⟩ := hL
  let L' := L.transport (T' := derivedExtensionOfScalarsData.{d, d₀} f)
  obtain ⟨b, P, hflat, hLE, ⟨w⟩⟩ := exists_isFlat_representative O L'.K
  have hcell := isFlatCellular_of_isStrictlyLE O P b hflat
  have := isIso_derivedExtensionOfScalarsCounit_app.{d, d₀} f P hcell
  have hP₀ : CochainComplex.IsStrictlyLE ((extensionOfScalarsCochainComplex J f).obj P) b :=
    isStrictlyLE_map_extensionOfScalars f b P hLE
  let ψ : DerivedCategory.Q.obj ((extensionOfScalarsCochainComplex J f).obj P) ≅
      DerivedCategory.Q.obj K₀ :=
    (asIso ((derivedExtensionOfScalarsCounit.{d, d₀} f).app P)).symm ≪≫
      (derivedExtensionOfScalars.{d, d₀} f).mapIso w ≪≫ L'.identification ≪≫ e.symm
  have hbdd : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (P.X n) :=
    ⟨b + 1, fun n hn => P.isZero_of_isStrictlyLE b n (by omega)⟩
  have hK₀ := homology_boundedAbove ((extensionOfScalarsCochainComplex J f).obj P) b
  have hn := omega_natural_derived hf S D hK₀ hK ψ.hom
  rw [omega_eq_zero_of_flatComplex hf S D P hflat hbdd hK₀, zero_comp] at hn
  rw [← cancel_epi ψ.hom, hn, comp_zero]

end Forward

end Deformation.ComplexLift

end
