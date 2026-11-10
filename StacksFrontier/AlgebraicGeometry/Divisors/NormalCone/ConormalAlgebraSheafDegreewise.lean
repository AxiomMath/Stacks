module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceUniversal
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeZeroSectionRetraction

/-!
# Maps out of the conormal algebra sheaf, degree by degree

`Stacks.Conormal.conormalAlgebraSheaf` is the ungraded realization of the conormal graded
algebra `𝒞_{Z/X,*}`, that is, the sheafification of the direct sum of its homogeneous pieces.
A morphism of algebra sheaves out of it is determined by its values on the homogeneous local
sections. This file proves that and computes on those sections the two maps out of `𝒞_{D/X,*}`
which [Stacks, Tag 0FEB] compares.

## Main results

* `Stacks.RelativeSpec.ungradedToGradedRight_ungradedAlgebraSheafIncl` and
  `Stacks.RelativeSpec.ungradedAlgebraSheafIsoGradedAlgebraSheaf_inv_ungradedIncl`: **the
  comparison of the two ungraded realizations of a sheaf of graded algebras matches their
  homogeneous inclusions**, in both directions.
* `Stacks.RelativeSpec.gradedAlgebraSheaf_right_hom_ext`: **two morphisms out of the ungraded
  realization of a sheaf of graded algebras agree as soon as they agree on the homogeneous local
  sections of every degree.**
* `Stacks.RelativeSpec.gradedAlgebraSheaf_hom_app`: the structure morphism of the ungraded
  realization is the degree-zero inclusion of a multiple of the graded unit.
* `Stacks.Conormal.conormalSymmetricAlgebraSheafHom_ungradedIncl`: the canonical map
  `Sym(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` of [Stacks, Tag 0632] is the degreewise canonical map on
  homogeneous local sections.
* `Stacks.Conormal.conormalAlgebraSheafRetraction_ungradedIncl`: **the augmentation
  `𝒞_{D/X,*} ⟶ 𝒪_D` of the conormal algebra of an effective Cartier divisor kills every
  homogeneous local section of nonzero degree.**
* `Stacks.Conormal.exists_hom_app_eq_ungradedIncl_zero`: every degree-zero homogeneous local
  section of `𝒞_{D/X,*}` is the image of a function under the structure morphism.
* `Stacks.Conormal.conormalAlgebraSheaf_hom_ext`: **two morphisms of algebra sheaves out of
  `𝒞_{D/X,*}` agree as soon as they agree on the homogeneous local sections of nonzero
  degree.**

## References

* [Stacks Project, Tag 0632](https://stacks.math.columbia.edu/tag/0632)
* [Stacks Project, Tag 0FEB](https://stacks.math.columbia.edu/tag/0FEB)
* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.RelativeSpec

variable (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hA : ∀ (i j : ℤ) (U : (Opens X)ᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
    HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x))

/-- **The comparison of the two ungraded realizations of a sheaf of graded algebras carries a
homogeneous local section to the same one.** -/
theorem ungradedToGradedRight_ungradedAlgebraSheafIncl (n : ℤ) (U : X.Opens)
    (x : (A.piece n).val.obj (op U)) :
    ((ungradedToGradedRight X A hA).hom.app (op U)).hom
        (ungradedAlgebraSheafIncl X A hA n U x) = A.ungradedIncl n x :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (ungradedRingUnit_comp_ringSheafIsoUngradedSheaf_inv X A hA) (op U))
    (A.toPresheafGradedAlgebra.incl n x)

/-- The comparison of the two ungraded realizations cancels against its inverse, read on the
underlying presheaves of rings. -/
theorem ungradedAlgebraSheafIsoGradedAlgebraSheaf_hom_inv_right_hom :
    (ungradedAlgebraSheafIsoGradedAlgebraSheaf X A hA).hom.right.hom ≫
        (ungradedAlgebraSheafIsoGradedAlgebraSheaf X A hA).inv.right.hom =
      𝟙 ((ungradedAlgebraSheaf X A hA).right.obj) :=
  (AlgebraSheaf.comp_right_hom _ _).trans
    (congrArg (fun t => t.right.hom)
      (ungradedAlgebraSheafIsoGradedAlgebraSheaf X A hA).hom_inv_id)

/-- **The inverse comparison of the two ungraded realizations carries a homogeneous local section
to the same one.** -/
theorem ungradedAlgebraSheafIsoGradedAlgebraSheaf_inv_ungradedIncl (n : ℤ) (U : X.Opens)
    (x : (A.piece n).val.obj (op U)) :
    (((ungradedAlgebraSheafIsoGradedAlgebraSheaf X A hA).inv.right.hom).app (op U)).hom
        (A.ungradedIncl n x) = ungradedAlgebraSheafIncl X A hA n U x := by
  rw [← ungradedToGradedRight_ungradedAlgebraSheafIncl X A hA n U x]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (ungradedAlgebraSheafIsoGradedAlgebraSheaf_hom_inv_right_hom X A hA)
      (op U))
    (ungradedAlgebraSheafIncl X A hA n U x)

/-- **Two morphisms out of the ungraded realization of a sheaf of graded algebras agree as soon
as they agree on the homogeneous local sections of every degree.** -/
theorem gradedAlgebraSheaf_right_hom_ext
    {S : Sheaf (Opens.grothendieckTopology (X : TopCat)) CommRingCat.{u}}
    {g h : (gradedAlgebraSheaf X A hA).right ⟶ S}
    (H : ∀ (n : ℤ) (W : (Opens ↥X)ᵒᵖ) (x : (A.piece n).val.obj W),
      (g.hom.app W).hom (A.ungradedIncl n x) = (h.hom.app W).hom (A.ungradedIncl n x)) :
    g = h := by
  have key : ∀ (W : (Opens ↥X)ᵒᵖ) (a : A.toPresheafGradedAlgebra.Total W),
      (((sheafCompose (Opens.grothendieckTopology (X : TopCat))
              (forget₂ CommRingCat.{u} RingCat.{u})).map g).hom.app W).hom
          (A.toPresheafGradedAlgebra.totalUnit (Opens.grothendieckTopology (X : TopCat)) W a) =
        (((sheafCompose (Opens.grothendieckTopology (X : TopCat))
              (forget₂ CommRingCat.{u} RingCat.{u})).map h).hom.app W).hom
          (A.toPresheafGradedAlgebra.totalUnit
            (Opens.grothendieckTopology (X : TopCat)) W a) := by
    intro W a
    induction a using A.toPresheafGradedAlgebra.incl_induction with
    | zero =>
      have h0 : A.toPresheafGradedAlgebra.totalUnit
          (Opens.grothendieckTopology (X : TopCat)) W 0 = 0 := map_zero _
      rw [h0]
      exact (map_zero _).trans (map_zero _).symm
    | incl n x => exact H n W x
    | add a b ha hb =>
      have h1 : A.toPresheafGradedAlgebra.totalUnit
            (Opens.grothendieckTopology (X : TopCat)) W (a + b) =
          A.toPresheafGradedAlgebra.totalUnit (Opens.grothendieckTopology (X : TopCat)) W a +
            A.toPresheafGradedAlgebra.totalUnit (Opens.grothendieckTopology (X : TopCat)) W b :=
        map_add _ _ _
      rw [h1]
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) ha hb).trans (map_add _ _ _).symm)
  refine (sheafCompose (Opens.grothendieckTopology (X : TopCat))
    (forget₂ CommRingCat.{u} RingCat.{u})).map_injective ?_
  refine Stacks.GradedAlgebra.totalSheaf_hom_ext A.toPresheafGradedAlgebra
    (Opens.grothendieckTopology (X : TopCat)) ?_
  exact NatTrans.ext (funext fun W => RingCat.hom_ext (RingHom.ext (key W)))

/-- **The structure morphism of the ungraded realization of a sheaf of graded algebras is the
degree-zero inclusion of the corresponding multiple of the graded unit.** -/
theorem gradedAlgebraSheaf_hom_app (W : (Opens ↥X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj W) :
    ((gradedAlgebraSheaf X A hA).hom.hom.app W).hom r =
      A.ungradedIncl 0 (r • A.one.eval W) :=
  congrArg (A.toPresheafGradedAlgebra.totalUnit (Opens.grothendieckTopology (X : TopCat)) W)
    ((congrArg (r • ·) (A.toPresheafGradedAlgebra.one_eq_incl W)).trans
      (A.toPresheafGradedAlgebra.incl_smul 0 r (A.one.eval W)).symm)

end Stacks.RelativeSpec

namespace Stacks.Conormal

open Stacks.RelativeSpec

variable {Z X : Scheme.{u}}

/-- **The canonical map of algebra sheaves `Sym(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` carries a homogeneous local
section to its image under the degreewise canonical map of [Stacks, Tag 0632].** -/
theorem conormalSymmetricAlgebraSheafHom_ungradedIncl (i : Z ⟶ X) [IsImmersion i] (n : ℤ)
    (U : Z.Opens) (x : ((conormalSymmetricAlgebra i).piece n).val.obj (op U)) :
    (((conormalSymmetricAlgebraSheafHom i).right.hom).app (op U)).hom
        ((conormalSymmetricAlgebra i).ungradedIncl n x) =
      (conormalAlgebra i).algebra.ungradedIncl n
        (((conormalSymmetricHom i).app n).val.app (op U) x) :=
  SheafOfModules.GradedAlgebra.ungradedIncl_ungradedSheafMap (conormalSymmetricHom i) n x

variable (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- **The augmentation `Sym(𝒞_{D/X}) ⟶ 𝒪_D` of the algebra of the normal bundle kills every
homogeneous local section of nonzero degree.** -/
theorem normalBundleAlgebraRetraction_ungradedIncl {n : ℤ} (hn : n ≠ 0) (U : D.subscheme.Opens)
    (y : ((conormalSymmetricAlgebra D.subschemeι).piece n).val.obj (op U)) :
    ((normalBundleAlgebraRetraction D).app (op U)).hom
        ((conormalSymmetricAlgebra D.subschemeι).ungradedIncl n y) = 0 :=
  (congrArg (((conormalSituation D).algebraSheafAugmentation.hom.app (op U)).hom)
      (Stacks.RelativeSpec.ungradedAlgebraSheafIsoGradedAlgebraSheaf_inv_ungradedIncl
        (conormalSituation D).X (conormalSituation D).symmetricAlgebra
        (conormalSituation D).symmetricAlgebra_mul_comm n U y)).trans
    ((conormalSituation D).algebraSheafAugmentation_algebraSheafIncl hn U y)

/-- The canonical map `Sym(𝒞_{D/X}) ⟶ 𝒞_{D/X,*}` cancels against its inverse on the underlying
presheaves of rings. -/
theorem hom_inv_right_hom_conormalSymmetricAlgebraSheafHom :
    (conormalSymmetricAlgebraSheafHom D.subschemeι).right.hom ≫
        (inv (conormalSymmetricAlgebraSheafHom D.subschemeι)).right.hom =
      𝟙 ((normalBundleAlgebra D.subschemeι).right.obj) :=
  (Stacks.RelativeSpec.AlgebraSheaf.comp_right_hom _ _).trans
    (congrArg (fun t => t.right.hom)
      (IsIso.hom_inv_id (conormalSymmetricAlgebraSheafHom D.subschemeι)))

/-- Every homogeneous local section of `𝒞_{D/X,*}` comes from the symmetric algebra. -/
private theorem exists_conormalSymmetricHom_app_preimage (E : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor E] (n : ℤ) (U : E.subscheme.Opens)
    (x : ((conormalAlgebra E.subschemeι).algebra.piece n).val.obj (op U)) :
    ∃ y, ((conormalSymmetricHom E.subschemeι).app n).val.app (op U) y = x := by
  have : IsIso ((conormalSymmetricHom E.subschemeι).app n) :=
    isIso_conormalSymmetricHom_app_of_isEffectiveCartierDivisor E n
  exact ⟨((inv ((conormalSymmetricHom E.subschemeι).app n)).val.app (op U)) x,
    congrArg (fun k : (conormalAlgebra E.subschemeι).algebra.piece n ⟶
        (conormalAlgebra E.subschemeι).algebra.piece n => k.val.app (op U) x)
      (IsIso.inv_hom_id ((conormalSymmetricHom E.subschemeι).app n))⟩

/-- **The augmentation `𝒞_{D/X,*} ⟶ 𝒪_D` of the conormal algebra of an effective Cartier divisor
kills every homogeneous local section of nonzero degree.** -/
theorem conormalAlgebraSheafRetraction_ungradedIncl {n : ℤ} (hn : n ≠ 0)
    (U : D.subscheme.Opens)
    (x : ((conormalAlgebra D.subschemeι).algebra.piece n).val.obj (op U)) :
    ((conormalAlgebraSheafRetraction D).app (op U)).hom
        ((conormalAlgebra D.subschemeι).algebra.ungradedIncl n x) = 0 := by
  obtain ⟨y, hx⟩ := exists_conormalSymmetricHom_app_preimage D n U x
  have hpsi : (((conormalSymmetricAlgebraSheafHom D.subschemeι).right.hom).app (op U)).hom
        ((conormalSymmetricAlgebra D.subschemeι).ungradedIncl n y) =
      (conormalAlgebra D.subschemeι).algebra.ungradedIncl n x :=
    (conormalSymmetricAlgebraSheafHom_ungradedIncl D.subschemeι n U y).trans
      (congrArg ((conormalAlgebra D.subschemeι).algebra.ungradedIncl n) hx)
  have hinv : (((inv (conormalSymmetricAlgebraSheafHom D.subschemeι)).right.hom).app
          (op U)).hom ((conormalAlgebra D.subschemeι).algebra.ungradedIncl n x) =
      (conormalSymmetricAlgebra D.subschemeι).ungradedIncl n y := by
    rw [← hpsi]
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (hom_inv_right_hom_conormalSymmetricAlgebraSheafHom D) (op U))
      ((conormalSymmetricAlgebra D.subschemeι).ungradedIncl n y)
  exact (congrArg (((normalBundleAlgebraRetraction D).app (op U)).hom) hinv).trans
    (normalBundleAlgebraRetraction_ungradedIncl D hn U y)

section DegreeZero

/-- The degree-zero identification `Sym⁰(𝒞_{D/X}) ≅ 𝒪_D`. -/
private abbrev pieceZeroIso :
    (conormalSymmetricAlgebra D.subschemeι).piece 0 ≅
      SheafOfModules.unit D.subscheme.ringCatSheaf :=
  Scheme.Modules.symmetricAlgebraPieceZeroIso D.subscheme (conormalSheafDegreeOne D.subschemeι)

/-- **For an effective Cartier divisor `D`, every degree-zero homogeneous local section of
`𝒞_{D/X,*}` is the image of a function under the structure morphism of the algebra sheaf.** -/
theorem exists_hom_app_eq_ungradedIncl_zero (U : D.subscheme.Opens)
    (x : ((conormalAlgebra D.subschemeι).algebra.piece 0).val.obj (op U)) :
    ∃ r : D.subscheme.ringCatSheaf.obj.obj (op U),
      ((conormalAlgebraSheaf D.subschemeι).hom.hom.app (op U)).hom r =
        (conormalAlgebra D.subschemeι).algebra.ungradedIncl 0 x := by
  obtain ⟨y, hx⟩ := exists_conormalSymmetricHom_app_preimage D 0 U x
  set r : D.subscheme.ringCatSheaf.obj.obj (op U) :=
    (pieceZeroIso D).hom.val.app (op U) y with hr
  refine ⟨r, ?_⟩
  have hroundtrip : ∀ a, ((pieceZeroIso D).inv.val.app (op U))
      (((pieceZeroIso D).hom.val.app (op U)) a) = a := fun a =>
    congrArg (fun k : (conormalSymmetricAlgebra D.subschemeι).piece 0 ⟶
        (conormalSymmetricAlgebra D.subschemeι).piece 0 => k.val.app (op U) a)
      (pieceZeroIso D).hom_inv_id
  have hsmul : ((pieceZeroIso D).hom.val.app (op U))
        (r • (conormalSymmetricAlgebra D.subschemeι).one.eval (op U)) =
      ((pieceZeroIso D).hom.val.app (op U)) y := by
    rw [map_smul (ModuleCat.Hom.hom ((pieceZeroIso D).hom.val.app (op U))) r
      ((conormalSymmetricAlgebra D.subschemeι).one.eval (op U)),
      Scheme.Modules.symmetricAlgebraPieceZeroIso_hom_one D.subscheme
        (conormalSheafDegreeOne D.subschemeι) (op U), hr]
    change r • (1 : D.subscheme.ringCatSheaf.obj.obj (op U)) = r
    exact (smul_eq_mul _ _).trans (mul_one r)
  have hone : r • (conormalSymmetricAlgebra D.subschemeι).one.eval (op U) = y :=
    ((hroundtrip _).symm.trans
      (congrArg ((pieceZeroIso D).inv.val.app (op U)) hsmul)).trans (hroundtrip y)
  refine Eq.trans ?_ ((conormalSymmetricAlgebraSheafHom_ungradedIncl D.subschemeι 0 U y).trans
    (congrArg ((conormalAlgebra D.subschemeι).algebra.ungradedIncl 0) hx))
  refine Eq.trans ?_ (congrArg
    ((((conormalSymmetricAlgebraSheafHom D.subschemeι).right.hom).app (op U)).hom)
    ((Stacks.RelativeSpec.gradedAlgebraSheaf_hom_app D.subscheme
        (conormalSymmetricAlgebra D.subschemeι)
        (Scheme.Modules.symmetricAlgebra_mul_comm D.subscheme
          (conormalSheafDegreeOne D.subschemeι)) (op U) r).trans
      (congrArg ((conormalSymmetricAlgebra D.subschemeι).ungradedIncl 0) hone)))
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app
    (Stacks.RelativeSpec.AlgebraSheaf.hom_comp_right_hom
      (conormalSymmetricAlgebraSheafHom D.subschemeι)) (op U)) r).symm

end DegreeZero

/-- **Two morphisms of algebra sheaves out of the conormal algebra `𝒞_{D/X,*}` of an effective
Cartier divisor agree as soon as they agree on the homogeneous local sections of nonzero
degree.** -/
theorem conormalAlgebraSheaf_hom_ext {S : Stacks.RelativeSpec.AlgebraSheaf D.subscheme}
    {g h : conormalAlgebraSheaf D.subschemeι ⟶ S}
    (H : ∀ (n : ℤ), n ≠ 0 → ∀ (W : (Opens ↥D.subscheme)ᵒᵖ)
      (x : ((conormalAlgebra D.subschemeι).algebra.piece n).val.obj W),
      (g.right.hom.app W).hom ((conormalAlgebra D.subschemeι).algebra.ungradedIncl n x) =
        (h.right.hom.app W).hom ((conormalAlgebra D.subschemeι).algebra.ungradedIncl n x)) :
    g = h := by
  refine Under.UnderMorphism.ext ?_
  refine Stacks.RelativeSpec.gradedAlgebraSheaf_right_hom_ext D.subscheme
    (conormalAlgebra D.subschemeι).algebra (conormalAlgebra D.subschemeι).mul_comm_int
    fun n W x => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · obtain ⟨U⟩ := W
    obtain ⟨r, hr⟩ := exists_hom_app_eq_ungradedIncl_zero D U x
    rw [← hr]
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app
        (Stacks.RelativeSpec.AlgebraSheaf.hom_comp_right_hom g) (op U)) r).trans
      (ConcreteCategory.congr_hom (NatTrans.congr_app
        (Stacks.RelativeSpec.AlgebraSheaf.hom_comp_right_hom h) (op U)) r).symm
  · exact H n hn W x

end Stacks.Conormal

end
