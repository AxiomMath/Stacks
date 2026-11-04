module

public import StacksFrontier.CategoryTheory.Sites.Modules.SquareZeroPullback
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionClassInjective
public import StacksFrontier.Deformation.RingedSpaceThickening.SchemeDeformationExtClassNaturality

/-!
# The pulled-back extension `𝒪_{X'} ×_{𝒪_X} 𝒜` and the criterion of Stacks 0GQ2 on classes

Let `g : (Z, 𝒜) ⟶ (T, 𝒪_T)` be a morphism of ringed spaces and `𝒢` an `𝒜`-module. Suppose given
on the opens of `Z` a sheaf of commutative rings `ℬ`, a ring map `q : 𝒜 ⟶ ℬ`, and a square-zero
extension `0 ⟶ 𝒢 ⟶ ℬ' ⟶ ℬ ⟶ 0` of `g⁻¹𝒪_T`-algebras whose ideal `𝒢` is acted on through `q`.
This is the situation of the second construction of **Stacks 0GQ2**, with `𝒜 = f⁻¹𝒪_Y`,
`ℬ = 𝒪_X`, `ℬ' = 𝒪_{X'}` and `q = f^♯`. Pulling `ℬ'` back along `q` gives an extension

`0 ⟶ 𝒢 ⟶ ℬ' ×_ℬ 𝒜 ⟶ 𝒜 ⟶ 0`

of `g⁻¹𝒪_T`-algebras, `AlgebraicGeometry.RingedSpaceThickening.FibreExtensionData.toExtension`,
whose identification of its ideal with `𝒢` is bijective. The criterion
`FibreExtensionData.extClass_eq_extClass_toExtension_iff` says that an arbitrary square-zero
extension `𝒪'` of `𝒜` by `𝒢` has the same class in `Ext¹_𝒜(𝖭𝖫_{𝒜/T}, 𝒢)` as the pulled-back one
exactly when there is a ring map `𝒪' ⟶ ℬ'` of `g⁻¹𝒪_T`-algebras lying over `q` and restricting on
the square-zero ideal of `𝒪'` to its given map to `𝒢`.

This is the comparison of **Stacks 0GQ2** read on classes: there `𝒪'` is the inverse image of an
extension, and the map `𝒪' ⟶ ℬ'` is a morphism of thickenings compatible with the given map on
ideals. Stated with an arbitrary `𝒪'`, whose ideal map need not be bijective, it needs no
pushout: the class of `𝒪'` already is the class of its pushout along its ideal map.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.FibreExtensionData`: the data `ℬ, ℬ', q, p, ι, v`.
* `AlgebraicGeometry.RingedSpaceThickening.FibreExtensionData.toExtension`: the pulled-back
  extension `ℬ' ×_ℬ 𝒜`.

## Main results

* `FibreExtensionData.toExtension_idealBijective`: its ideal is identified with `𝒢` bijectively.
* `FibreExtensionData.extClass_eq_extClass_toExtension_iff`: **the criterion.**

## References

* [Stacks Project, Tag 0GQ2](https://stacks.math.columbia.edu/tag/0GQ2)
* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal kernelIdeal_le_comap hom_of_comp_eq
  presentationScalar)
open Stacks.Sites.SqZeroPullback
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {Z T : RingedSpace.{u, u}}

/-- The data of the second construction of **Stacks 0GQ2** on the opens of `Z`: a sheaf of rings
`ℬ` with a ring map `q : 𝒜 ⟶ ℬ` out of the structure sheaf `𝒜` of `Z`, and a square-zero
extension `0 ⟶ 𝒢 ⟶ ℬ' ⟶ ℬ ⟶ 0` of `g⁻¹𝒪_T`-algebras in which `𝒢` is acted on through `q`. -/
structure FibreExtensionData (g : Z ⟶ T)
    (G : SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology Z.carrier) Z.sheaf))
    {B : Sheaf (Opens.grothendieckTopology Z.carrier) CommRingCat.{u}} (q : Z.sheaf ⟶ B) where
  /-- The extension `ℬ'`. -/
  B' : Sheaf (Opens.grothendieckTopology Z.carrier) CommRingCat.{u}
  /-- The reduction `ℬ' ⟶ ℬ`. -/
  p : B' ⟶ B
  /-- The reduction is locally surjective. -/
  locallySurjective_p :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Z.carrier) p.hom
  /-- The identification of `𝒢` with the kernel of the reduction. -/
  ι : FibreInrData p G.val.presheaf
  /-- The ideal `𝒢` of `ℬ'` squares to zero. -/
  inr_mul_inr (U : (Opens Z.carrier)ᵒᵖ) (n m : ↥(G.val.obj U)) : ι.app U n * ι.app U m = 0
  /-- `ℬ'` acts on its ideal `𝒢` through `q`. -/
  smul_inr (U : (Opens Z.carrier)ᵒᵖ) (b : ↥(B'.obj.obj U))
    (a : ↥((ringSheaf (J := Opens.grothendieckTopology Z.carrier) Z.sheaf).obj.obj U))
    (n : ↥(G.val.obj U)) (hb : p.hom.app U b = q.hom.app U a) :
    b * ι.app U n = ι.app U (a • n)
  /-- The `g⁻¹𝒪_T`-algebra structure of `ℬ'`. -/
  v : inverseImageBaseRing g ⟶ B'
  /-- The reduction is a morphism of `g⁻¹𝒪_T`-algebras over `q`. -/
  base_comm : v ≫ p = structureRingMap g ≫ q

namespace FibreExtensionData

variable {g : Z ⟶ T}
  {G : SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology Z.carrier) Z.sheaf)}
  {B : Sheaf (Opens.grothendieckTopology Z.carrier) CommRingCat.{u}} {q : Z.sheaf ⟶ B}
  (D : FibreExtensionData g G q)

attribute [instance] FibreExtensionData.locallySurjective_p

/-- The section `n` of `𝒢` with `(ι n, 0)` equal to a given local section of `ℬ' ×_ℬ 𝒜` killed by
the projection to `𝒜`. -/
def idealValue (U : (Opens Z.carrier)ᵒᵖ) (y : ↥(kernelIdeal (fibreSnd D.p q).hom U)) :
    ↥(G.val.obj U) :=
  Classical.choose ((fibreSnd_app_eq_zero_iff_exists_fibreInr D.p q D.ι U y.1).1 y.2)

/-- The section `(ι n, 0)` for `n = idealValue U y` is `y`. -/
theorem fibreInr_idealValue (U : (Opens Z.carrier)ᵒᵖ)
    (y : ↥(kernelIdeal (fibreSnd D.p q).hom U)) :
    fibreInr D.p q D.ι U (D.idealValue U y) = y.1 :=
  Classical.choose_spec ((fibreSnd_app_eq_zero_iff_exists_fibreInr D.p q D.ι U y.1).1 y.2)

/-- `idealValue U y` is the unique `n` with `(ι n, 0) = y`. -/
theorem idealValue_eq (U : (Opens Z.carrier)ᵒᵖ) (y : ↥(kernelIdeal (fibreSnd D.p q).hom U))
    (n : ↥(G.val.obj U)) (hn : fibreInr D.p q D.ι U n = y.1) : D.idealValue U y = n :=
  fibreInr_injective D.p q D.ι U ((D.fibreInr_idealValue U y).trans hn.symm)

/-- The identification of the ideal of `ℬ' ×_ℬ 𝒜` with `𝒢`. -/
def ideal : IdealRestriction.{u, u, u, u} (fibreSnd D.p q) G where
  app U :=
    { toFun := D.idealValue U
      map_zero' := D.idealValue_eq U 0 0 (fibreInr_zero D.p q D.ι U)
      map_add' := fun y y' => D.idealValue_eq U _ _
        ((fibreInr_add D.p q D.ι U _ _).trans (congrArg₂ (· + ·)
          (D.fibreInr_idealValue U y) (D.fibreInr_idealValue U y'))) }
  app_smul U r y := by
    refine D.idealValue_eq U _ _ ?_
    refine (fibreMk_mul_fibreInr D.p q D.ι U r (D.idealValue U y) _
      (D.smul_inr U (fibreVal D.p q U r).1 (presentationScalar (fibreSnd D.p q) U r)
        (D.idealValue U y) ((mem_fibreSubring_iff D.p q U _).1
          (fibreVal_mem D.p q U r)))).symm.trans ?_
    exact congrArg (r * ·) (D.fibreInr_idealValue U y)
  app_map {U V} k y :=
    D.idealValue_eq V _ _ ((fibreInr_map D.p q D.ι k (D.idealValue U y)).symm.trans
      (congrArg (fun z => ((fibrePresheaf D.p q).map k).hom z) (D.fibreInr_idealValue U y)))

/-- The identification `ideal` sends a local section `y` of the ideal to `idealValue U y`. -/
theorem ideal_app (U : (Opens Z.carrier)ᵒᵖ) (y : ↥(kernelIdeal (fibreSnd D.p q).hom U)) :
    D.ideal.app U y = D.idealValue U y := rfl

/-- **The pulled-back extension `ℬ' ×_ℬ 𝒜`** of `𝒜` by `𝒢`, an extension of `g⁻¹𝒪_T`-algebras:
the second construction of **Stacks 0GQ2**. -/
def toExtension : AlgebraSquareZeroExtension g G where
  sheaf := fibreSheaf D.p q
  base := fibreLift D.p q D.v (structureRingMap g) D.base_comm
  reduction := fibreSnd D.p q
  base_comp_reduction := fibreLift_comp_snd D.p q D.v (structureRingMap g) D.base_comm
  reduction_surjective := isLocallySurjective_fibreSnd D.p q
  ideal := D.ideal

/-- The identification of the ideal of `toExtension` with `𝒢` sends `(ι n, 0)` to `n`. -/
theorem toExtension_ideal_fibreInr (U : (Opens Z.carrier)ᵒᵖ) (n : ↥(G.val.obj U))
    (hn : fibreInr D.p q D.ι U n ∈ kernelIdeal (fibreSnd D.p q).hom U) :
    D.toExtension.ideal.app U ⟨fibreInr D.p q D.ι U n, hn⟩ = n :=
  (D.ideal_app U _).trans (D.idealValue_eq U _ n rfl)

/-- The identification of the ideal of the pulled-back extension with `𝒢` is bijective. -/
theorem toExtension_idealBijective (U : (Opens Z.carrier)ᵒᵖ) :
    Function.Bijective (D.toExtension.ideal.app U) :=
  ⟨fun y y' h => Subtype.ext ((D.fibreInr_idealValue U y).symm.trans
    ((congrArg (fibreInr D.p q D.ι U) (((D.ideal_app U y).symm.trans h).trans
      (D.ideal_app U y'))).trans (D.fibreInr_idealValue U y'))),
    fun n => ⟨⟨fibreInr D.p q D.ι U n, fibreSnd_fibreInr D.p q D.ι U n⟩,
      D.toExtension_ideal_fibreInr U n _⟩⟩

/-- A local section `y` of the ideal of `ℬ' ×_ℬ 𝒜` with first component `ι n` is sent to `n`. -/
private theorem ideal_app_eq_of_fst_eq (U : (Opens Z.carrier)ᵒᵖ)
    (y : ↥(kernelIdeal (fibreSnd D.p q).hom U)) (n : ↥(G.val.obj U))
    (h : (fibreVal D.p q U y.1).1 = D.ι.app U n) : D.ideal.app U y = n :=
  (D.ideal_app U y).trans (D.idealValue_eq U y n
    (fibreVal_injective D.p q U (Prod.ext h.symm y.2.symm)))

/-- A morphism into `ℬ' ×_ℬ 𝒜` with the components of the structure map `v` and the structure
map of `𝒜` is the base map of the pulled-back extension. -/
private theorem eq_toExtension_base
    (F : inverseImageBaseRing g ⟶ fibreSheaf D.p q) (h₁ : F ≫ fibreFst D.p q = D.v)
    (h₂ : F ≫ fibreSnd D.p q = structureRingMap g) : F = D.toExtension.base :=
  fibre_hom_ext D.p q (h₁.trans (fibreLift_comp_fst D.p q D.v (structureRingMap g)
    D.base_comm).symm) (h₂.trans (fibreLift_comp_snd D.p q D.v (structureRingMap g)
    D.base_comm).symm)

/-- **The criterion of Stacks 0GQ2, on classes.** A square-zero extension `𝒪'` of `𝒜` by `𝒢` has
the same class in `Ext¹_𝒜(𝖭𝖫_{𝒜/T}, 𝒢)` as the pulled-back extension `ℬ' ×_ℬ 𝒜` exactly when
there is a ring map `φ : 𝒪' ⟶ ℬ'` lying over `q`, of `g⁻¹𝒪_T`-algebras, and restricting on the
square-zero ideal of `𝒪'` to its identification with `𝒢` followed by `ι`.

The identification of the ideal of `𝒪'` with `𝒢` need not be bijective. -/
theorem extClass_eq_extClass_toExtension_iff (P : AlgebraSquareZeroExtension g G) :
    P.toPresented.extClass = D.toExtension.toPresented.extClass ↔
      ∃ φ : P.sheaf ⟶ D.B', φ ≫ D.p = P.reduction ≫ q ∧ P.base ≫ φ = D.v ∧
        ∀ (V : (Opens Z.carrier)ᵒᵖ) (y : ↥(kernelIdeal P.reduction.hom V)),
          φ.hom.app V y = D.ι.app V (P.ideal.app V y) := by
  rw [AlgebraSquareZeroExtension.extClass_eq_iff_exists_hom P D.toExtension
    D.toExtension_idealBijective]
  constructor
  · rintro ⟨θ, hbase, hred, hideal⟩
    refine ⟨θ ≫ fibreFst D.p q, ?_, ?_, fun V y => ?_⟩
    · exact (Category.assoc θ (fibreFst D.p q) D.p).trans
        ((congrArg (θ ≫ ·) (fibreFst_comp_eq D.p q)).trans
          ((Category.assoc θ (fibreSnd D.p q) q).symm.trans (congrArg (· ≫ q) hred)))
    · exact (Category.assoc P.base θ (fibreFst D.p q)).symm.trans
        ((congrArg (· ≫ fibreFst D.p q) hbase).trans
          (fibreLift_comp_fst D.p q D.v (structureRingMap g) D.base_comm))
    · have hv := D.fibreInr_idealValue V ⟨θ.hom.app V y, kernelIdeal_le_comap P.reduction.hom
        D.toExtension.reduction.hom θ.hom (hom_of_comp_eq hred) V y.2⟩
      have h' : D.idealValue V ⟨θ.hom.app V y, kernelIdeal_le_comap P.reduction.hom
          D.toExtension.reduction.hom θ.hom (hom_of_comp_eq hred) V y.2⟩ =
          P.ideal.app V y := hideal V y
      rw [h'] at hv
      have h1 := congrArg (fun z => (fibreVal D.p q V z).1) hv
      simp only at h1
      exact h1.symm
  · rintro ⟨φ, hφ, hbase, hker⟩
    let θ : P.sheaf ⟶ fibreSheaf D.p q := fibreLift D.p q φ P.reduction hφ
    have hred : θ ≫ fibreSnd D.p q = P.reduction := fibreLift_comp_snd D.p q φ _ hφ
    refine ⟨θ, ?_, hred, fun V y => ?_⟩
    · exact (D.eq_toExtension_base _ ((Category.assoc _ _ _).trans
        ((congrArg (P.base ≫ ·) (fibreLift_comp_fst D.p q φ P.reduction hφ)).trans hbase))
        ((Category.assoc _ _ _).trans ((congrArg (P.base ≫ ·) hred).trans
          P.base_comp_reduction)))
    · exact D.ideal_app_eq_of_fst_eq V _ _ (hker V y)

attribute [local instance] HasDerivedCategory.standard

/-- **The class of the pulled-back extension is natural in the coefficient module.** A ring map
`β : ℬ'₁ ⟶ ℬ'₂` of `g⁻¹𝒪_T`-algebras over `ℬ` which on the ideals is `h : 𝒢₁ ⟶ 𝒢₂` carries the
class of `ℬ'₁ ×_ℬ 𝒜` to the class of `ℬ'₂ ×_ℬ 𝒜`: the second is the first pushed forward
along `h`. -/
theorem extClass_toExtension_comp
    {G₂ : SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology Z.carrier) Z.sheaf)}
    (D₂ : FibreExtensionData g G₂ q) (h : G ⟶ G₂) (β : D.B' ⟶ D₂.B') (hp : β ≫ D₂.p = D.p)
    (hv : D.v ≫ β = D₂.v)
    (hι : ∀ (U : (Opens Z.carrier)ᵒᵖ) (n : ↥(G.val.obj U)),
      β.hom.app U (D.ι.app U n) = D₂.ι.app U (h.val.app U n)) :
    D.toExtension.toPresented.extClass ≫
        ((DerivedCategory.singleFunctor _ 0).map h)⟦(1 : ℤ)⟧' =
      D₂.toExtension.toPresented.extClass := by
  have hw : (fibreFst D.p q ≫ β) ≫ D₂.p = fibreSnd D.p q ≫ q :=
    (Category.assoc _ _ _).trans ((congrArg (fibreFst D.p q ≫ ·) hp).trans
      (fibreFst_comp_eq D.p q))
  let θ : fibreSheaf D.p q ⟶ fibreSheaf D₂.p q :=
    fibreLift D₂.p q (fibreFst D.p q ≫ β) (fibreSnd D.p q) hw
  have hred : θ ≫ fibreSnd D₂.p q = fibreSnd D.p q := fibreLift_comp_snd D₂.p q _ _ hw
  refine AlgebraSquareZeroExtension.extClass_comp_eq_extClass_of_hom D.toExtension
    D₂.toExtension h θ ?_ hred (fun V y => ?_)
  · refine D₂.eq_toExtension_base _ ((Category.assoc _ _ _).trans
      ((congrArg (D.toExtension.base ≫ ·) (fibreLift_comp_fst D₂.p q _ _ hw)).trans
        ((Category.assoc _ _ β).symm.trans ((congrArg (· ≫ β)
          (fibreLift_comp_fst D.p q D.v (structureRingMap g) D.base_comm)).trans hv))))
      ((Category.assoc _ _ _).trans ((congrArg (D.toExtension.base ≫ ·) hred).trans
        (fibreLift_comp_snd D.p q D.v (structureRingMap g) D.base_comm)))
  · refine D₂.ideal_app_eq_of_fst_eq V _ _ ?_
    change β.hom.app V (fibreVal D.p q V y.1).1 = D₂.ι.app V (h.val.app V (D.idealValue V y))
    exact (congrArg (β.hom.app V) (congrArg (fun z => (fibreVal D.p q V z).1)
      (D.fibreInr_idealValue V y))).symm.trans (hι V _)

end FibreExtensionData

end AlgebraicGeometry.RingedSpaceThickening

end
