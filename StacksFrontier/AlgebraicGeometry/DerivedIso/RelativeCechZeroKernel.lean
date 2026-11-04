module

public import StacksFrontier.AlgebraicGeometry.DerivedIso.RelativeCechZero

/-!
# The relative Čech row is left exact

Let `f : X ⟶ S` be a morphism of schemes, let `𝒰` be the covering given by a finite affine open
cover `T` of `X` and let `ℱ` be a quasi-coherent `𝒪_X`-module.  The relative Čech complex
`Č ⁼(𝒰, f, ℱ)` of [Stacks, Tag 01XL] is concentrated in non-negative degrees and its degree zero
cohomology is `f_* ℱ`, so

`0 ⟶ f_* ℱ ⟶ Č ⁰(𝒰, f, ℱ) ⟶ Č ¹(𝒰, f, ℱ)`

is exact: the augmentation is a kernel of the first differential.

The deduction is pure homological algebra and is carried out in that generality: in a degree into
which no differential enters, the cycles are both the kernel of the outgoing differential and the
homology, so any object identified with the homology is a kernel of the outgoing differential,
naturally in a parameter.

## Main definitions

* `Stacks.HomologicalComplex.natTransICycles`: the inclusion of the cycles into the term, as a
  natural transformation.
* `Stacks.HomologicalComplex.homologyAug`: for a family of complexes into whose degree `j` no
  differential enters, the morphism from the degree `j` homology to the degree `j` term,
  naturally in the parameter.
* `Stacks.AlgebraicGeometry.Tag01XLDerivedIso.relativeCechAugZero`: the augmentation
  `f_* ℱ ⟶ Č ⁰(𝒰, f, ℱ)` of the relative Čech complex, naturally in `ℱ`.

## Main results

* `Stacks.HomologicalComplex.isLimitKernelForkOfHomologyIso` and
  `Stacks.HomologicalComplex.isLimitKernelFork_homologyAug`: **an object identified with the
  degree `j` homology of a complex into whose degree `j` no differential enters is a kernel of
  the differential leaving degree `j`.**
* `Stacks.AlgebraicGeometry.Tag01XLDerivedIso.isLimitKernelFork_relativeCechAugZero`: **the
  augmentation `f_* ℱ ⟶ Č ⁰(𝒰, f, ℱ)` is a kernel of `Č ⁰(𝒰, f, ℱ) ⟶ Č ¹(𝒰, f, ℱ)`**, that is
  the relative Čech row is left exact.
* `Stacks.AlgebraicGeometry.Tag01XLDerivedIso.relativeCechAugZero_comp_dNatTrans`: that row is a
  complex, naturally in the quasi-coherent module.

## Implementation notes

`Stacks.HomologicalComplex.isLimitKernelForkOfHomologyIso` takes the morphism whose kernel
property is asserted as a variable together with an equation identifying it, because the proof
that it kills the differential occurs inside the type of the conclusion and so cannot be
rewritten there.

The identification of the homology with the cycles is natural only where the differential
entering the degree vanishes, which is a hypothesis on each member of the family rather than a
property of the degree; the augmentation is therefore assembled componentwise, its naturality
coming from the naturality of the homology class map and of the inclusion of the cycles.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe v u

/-! ### Homology in a degree into which no differential enters -/

namespace Stacks.HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  [CategoryWithHomology C]

/-- The inclusion of the cycles into the term, as a natural transformation of functors of the
complex. -/
def natTransICycles (j : ι) :
    _root_.HomologicalComplex.cyclesFunctor C c j ⟶ _root_.HomologicalComplex.eval C c j where
  app K := K.iCycles j
  naturality _ _ φ := _root_.HomologicalComplex.cyclesMap_i φ j

/-- **The homology of a complex in a degree into which no differential enters, mapped to the term
of that degree**:  the homology is the cycles there, and the cycles include into the term. -/
def homologyToX (K : _root_.HomologicalComplex C c) (j : ι) (hK : K.d (c.prev j) j = 0) :
    K.homology j ⟶ K.X j :=
  (K.isoHomologyπ (c.prev j) j rfl hK).inv ≫ K.iCycles j

/-- The homology of a degree into which no differential enters maps into the term by a cycle. -/
theorem homologyToX_comp_d (K : _root_.HomologicalComplex C c) (j j' : ι)
    (hK : K.d (c.prev j) j = 0) : homologyToX K j hK ≫ K.d j j' = 0 := by
  rw [homologyToX, Category.assoc, _root_.HomologicalComplex.iCycles_d, comp_zero]

/-- **A morphism of complexes commutes with the passage from the homology to the term**, in a
degree into which no differential enters in either complex. -/
theorem homologyMap_comp_homologyToX {K L : _root_.HomologicalComplex C c} (j : ι) (φ : K ⟶ L)
    (hK : K.d (c.prev j) j = 0) (hL : L.d (c.prev j) j = 0) :
    _root_.HomologicalComplex.homologyMap φ j ≫ homologyToX L j hL =
      homologyToX K j hK ≫ φ.f j := by
  rw [← cancel_epi (K.isoHomologyπ (c.prev j) j rfl hK).hom, homologyToX, homologyToX]
  simp

/-- **An object identified with the degree `j` homology of a complex into whose degree `j` no
differential enters is a kernel of the differential leaving degree `j`**:  that homology is the
cycles, and the cycles are such a kernel. -/
def isLimitKernelForkOfHomologyIso (K : _root_.HomologicalComplex C c) {j j' : ι}
    (hj : c.next j = j') (hK : K.d (c.prev j) j = 0) {A : C} (e : A ≅ K.homology j)
    {w : A ⟶ K.X j} (hw : w = e.hom ≫ homologyToX K j hK) (hwd : w ≫ K.d j j' = 0) :
    IsLimit (KernelFork.ofι w hwd) := by
  subst hw
  exact IsLimit.ofIsoLimit (K.cyclesIsKernel j j' hj)
    (Fork.ext (K.isoHomologyπ (c.prev j) j rfl hK ≪≫ e.symm) (by simp [homologyToX]))

variable {D : Type*} [Category* D] {Φ : D ⥤ _root_.HomologicalComplex C c} {G : D ⥤ C} {j : ι}
  (e : G ≅ Φ ⋙ _root_.HomologicalComplex.homologyFunctor C c j)
  (hΦ : ∀ Z, (Φ.obj Z).d (c.prev j) j = 0)

/-- **The augmentation of a family of complexes by its degree `j` homology**, in a degree into
which no differential enters:  the homology is the cycles there, and the cycles include into the
term. -/
def homologyAug : G ⟶ Φ ⋙ _root_.HomologicalComplex.eval C c j where
  app Z := e.hom.app Z ≫ homologyToX (Φ.obj Z) j (hΦ Z)
  naturality Z Z' φ :=
    calc G.map φ ≫ e.hom.app Z' ≫ homologyToX (Φ.obj Z') j (hΦ Z')
        = (G.map φ ≫ e.hom.app Z') ≫ homologyToX (Φ.obj Z') j (hΦ Z') :=
          (Category.assoc _ _ _).symm
      _ = (e.hom.app Z ≫ _root_.HomologicalComplex.homologyMap (Φ.map φ) j) ≫
            homologyToX (Φ.obj Z') j (hΦ Z') :=
          congrArg (fun z => z ≫ homologyToX (Φ.obj Z') j (hΦ Z')) (e.hom.naturality φ)
      _ = e.hom.app Z ≫ _root_.HomologicalComplex.homologyMap (Φ.map φ) j ≫
            homologyToX (Φ.obj Z') j (hΦ Z') := Category.assoc _ _ _
      _ = e.hom.app Z ≫ homologyToX (Φ.obj Z) j (hΦ Z) ≫ (Φ.map φ).f j :=
          congrArg (fun z => e.hom.app Z ≫ z)
            (homologyMap_comp_homologyToX j (Φ.map φ) (hΦ Z) (hΦ Z'))
      _ = (e.hom.app Z ≫ homologyToX (Φ.obj Z) j (hΦ Z)) ≫ (Φ.map φ).f j :=
          (Category.assoc _ _ _).symm

/-- The components of `Stacks.HomologicalComplex.homologyAug`. -/
theorem homologyAug_app (Z : D) :
    (homologyAug e hΦ).app Z = e.hom.app Z ≫ homologyToX (Φ.obj Z) j (hΦ Z) :=
  rfl

/-- The augmentation followed by the differential leaving degree `j` is zero, at a fixed
parameter. -/
theorem homologyAug_app_comp_d (j' : ι) (Z : D) :
    (homologyAug e hΦ).app Z ≫ (Φ.obj Z).d j j' = 0 :=
  Eq.trans (Category.assoc (e.hom.app Z) (homologyToX (Φ.obj Z) j (hΦ Z)) ((Φ.obj Z).d j j'))
    (Eq.trans
      (congrArg (fun z : (Φ ⋙ _root_.HomologicalComplex.homologyFunctor C c j).obj Z ⟶
            (Φ.obj Z).X j' => e.hom.app Z ≫ z)
        (homologyToX_comp_d (Φ.obj Z) j j' (hΦ Z)))
      comp_zero)

/-- **The augmentation followed by the differential leaving degree `j` is zero**, naturally in the
parameter. -/
theorem homologyAug_comp_dNatTrans (j' : ι) :
    homologyAug e hΦ ≫
        Functor.whiskerLeft Φ (_root_.HomologicalComplex.dNatTrans C c j j') = 0 := by
  ext Z
  exact homologyAug_app_comp_d e hΦ j' Z

/-- **The augmentation of a family of complexes by its degree `j` homology is a kernel of the
differential leaving degree `j`**, at every parameter. -/
def isLimitKernelFork_homologyAug {j' : ι} (hj : c.next j = j') (Z : D) :
    IsLimit (KernelFork.ofι ((homologyAug e hΦ).app Z) (homologyAug_app_comp_d e hΦ j' Z)) :=
  isLimitKernelForkOfHomologyIso (Φ.obj Z) hj (hΦ Z) (e.app Z) rfl
    (homologyAug_app_comp_d e hΦ j' Z)

end Stacks.HomologicalComplex

/-! ### The relative Čech row is left exact -/

namespace Stacks.AlgebraicGeometry.Tag01XLDerivedIso

open Stacks.AlgebraicGeometry.RelativeCech
open Stacks.AlgebraicGeometry.RelativeCechComplex

variable {X S : Scheme.{u}} (f : X ⟶ S) (T : X.AffineOpenCover.{u, u}) [Fintype T.I₀]

/-- The relative Čech complex of [Stacks, Tag 01XL] as a family of `ℤ`-indexed complexes of
`𝒪_S`-modules, the bound being forgotten. -/
def relativeCechComplexZ :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      CochainComplex S.Modules ℤ :=
  relativeCechComplex f T ⋙ CochainComplex.Plus.ι S.Modules

/-- No differential of the relative Čech complex enters degree zero:  the complex is the
extension of an `ℕ`-indexed complex, so its term in the preceding degree is zero. -/
theorem relativeCechComplexZ_d_prev_zero
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    ((relativeCechComplexZ f T).obj F).d ((ComplexShape.up ℤ).prev 0) 0 = 0 := by
  show (((CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))).obj
      ((relativeCechPresheaf f).obj F)).extend ComplexShape.embeddingUpNat).d
      ((ComplexShape.up ℤ).prev 0) 0 = 0
  refine (_root_.HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat
    ((ComplexShape.up ℤ).prev 0) (fun i ↦ ?_)).eq_zero_of_src _
  have h : (ComplexShape.up ℤ).prev 0 = -1 := by simp
  simp only [ComplexShape.embeddingUpNat_f, h]
  omega

/-- `H⁰(Č ⁼(𝒰, f, ℱ)) ≅ f_* ℱ`, read on the `ℤ`-indexed relative Čech complex. -/
def relativeCechHomologyZeroIsoZ :
    ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        Scheme.Modules.pushforward f ≅
      relativeCechComplexZ f T ⋙
        _root_.HomologicalComplex.homologyFunctor S.Modules (ComplexShape.up ℤ) 0 :=
  (relativeCechHomologyZeroIso f T).symm

/-- **The augmentation `f_* ℱ ⟶ Č ⁰(𝒰, f, ℱ)` of the relative Čech complex of
[Stacks, Tag 01XL]**, as a natural transformation in the quasi-coherent `𝒪_X`-module `ℱ`:  the
degree zero cohomology of that complex is `f_* ℱ`, and no differential enters degree zero. -/
def relativeCechAugZero :
    ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        Scheme.Modules.pushforward f ⟶
      relativeCechComplexZ f T ⋙
        _root_.HomologicalComplex.eval S.Modules (ComplexShape.up ℤ) 0 :=
  Stacks.HomologicalComplex.homologyAug (relativeCechHomologyZeroIsoZ f T)
    (relativeCechComplexZ_d_prev_zero f T)

/-- The augmentation followed by the first differential of the relative Čech complex is zero, at
a fixed quasi-coherent `𝒪_X`-module. -/
theorem relativeCechAugZero_app_comp_d
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (relativeCechAugZero f T).app F ≫ ((relativeCechComplexZ f T).obj F).d 0 1 = 0 :=
  Stacks.HomologicalComplex.homologyAug_app_comp_d _ _ 1 F

/-- **`f_* ℱ ⟶ Č ⁰(𝒰, f, ℱ) ⟶ Č ¹(𝒰, f, ℱ)` is a complex**, naturally in the quasi-coherent
`𝒪_X`-module `ℱ`. -/
theorem relativeCechAugZero_comp_dNatTrans :
    relativeCechAugZero f T ≫ Functor.whiskerLeft (relativeCechComplexZ f T)
        (_root_.HomologicalComplex.dNatTrans S.Modules (ComplexShape.up ℤ) 0 1) = 0 :=
  Stacks.HomologicalComplex.homologyAug_comp_dNatTrans _ _ 1

/-- **The relative Čech row of [Stacks, Tag 01XL] is left exact**:  the augmentation
`f_* ℱ ⟶ Č ⁰(𝒰, f, ℱ)` is a kernel of the first differential
`Č ⁰(𝒰, f, ℱ) ⟶ Č ¹(𝒰, f, ℱ)`.  This is the left exactness of the bottom row of the comparison
diagram of [Stacks, Tag 0GPA]. -/
def isLimitKernelFork_relativeCechAugZero
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    IsLimit (KernelFork.ofι ((relativeCechAugZero f T).app F)
      (relativeCechAugZero_app_comp_d f T F)) :=
  Stacks.HomologicalComplex.isLimitKernelFork_homologyAug _ _ (by simp) F

/-- **The augmentation `f_* ℱ ⟶ Č ⁰(𝒰, f, ℱ)` is a monomorphism.** -/
theorem mono_relativeCechAugZero_app
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    Mono ((relativeCechAugZero f T).app F) :=
  mono_of_isLimit_fork (isLimitKernelFork_relativeCechAugZero f T F)

end Stacks.AlgebraicGeometry.Tag01XLDerivedIso

end
