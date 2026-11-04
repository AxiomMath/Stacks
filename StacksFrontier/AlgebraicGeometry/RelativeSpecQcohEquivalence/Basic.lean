module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.AlgebraicGeometry.AffineQcohUnit.Equivalence
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic

/-!
# Quasi-coherent modules on a relative spectrum

Let `S` be a scheme and let `A` be a quasi-coherent sheaf of commutative `𝒪_S`-algebras, with
relative spectrum `π : Spec_S A ⟶ S`. Direct image along `π`, followed by the identification
`π_* 𝒪 ≅ A`, is an equivalence between the quasi-coherent modules on the relative spectrum and
the quasi-coherent `A`-modules. In particular every quasi-coherent `A`-module is the direct image
of a quasi-coherent module on `Spec_S A`, unique up to isomorphism.

## Main definitions

* `Stacks.AffineAlgebraEquivalence.pushforwardRingIso`: the isomorphism of sheaves of rings
  `π_* 𝒪_{Spec_S A} ≅ A`.
* `Stacks.AffineAlgebraEquivalence.relativeSpecQcohEquivalence`: the equivalence between the
  quasi-coherent modules on `Spec_S A` and the quasi-coherent `A`-modules, given by direct
  image along `π` followed by the identification `π_* 𝒪 ≅ A`.
* `Stacks.AlgebraicGeometry.QcohOverAlgebra.qcohRestrictScalarsEquivalence`: restriction of
  scalars along an isomorphism of quasi-coherent `𝒪_S`-algebras, as an equivalence between the
  categories of quasi-coherent modules over them.

## Main results

* `Stacks.AlgebraicGeometry.QcohOverAlgebra.isQuasicoherent_restrictScalars_hom_iff` and
  `isQuasicoherent_restrictScalars_inv_iff`: restriction of scalars along an isomorphism of
  quasi-coherent `𝒪_S`-algebras preserves and reflects quasi-coherence.
* `Stacks.AffineAlgebraEquivalence.relativeSpecQcohEquivalence_functor_obj_obj`: the functor of
  the equivalence is direct image followed by restriction of scalars along `π_* 𝒪 ≅ A`.
* `Stacks.AffineAlgebraEquivalence.exists_iso_relativeSpecQcohPushforward`: every quasi-coherent
  `A`-module is the direct image of a quasi-coherent module on `Spec_S A`.
* `Stacks.AffineAlgebraEquivalence.isoOfRelativeSpecQcohPushforwardIso`: that module is unique
  up to isomorphism.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 0H88](https://stacks.math.columbia.edu/tag/0H88)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.AlgebraicGeometry.QcohOverAlgebra

variable {S : Scheme.{u}}
  {R R' : Sheaf (Opens.grothendieckTopology S) RingCat.{u}}
  {α : S.ringCatSheaf ⟶ R} {α' : S.ringCatSheaf ⟶ R'}

/-- Let `e : R ≅ R'` be an isomorphism of quasi-coherent `𝒪_S`-algebras, that is an isomorphism
of the underlying sheaves of rings compatible with the structure maps `α` and `α'`. An
`R'`-module is quasi-coherent if and only if it is quasi-coherent after restriction of scalars
along `e.hom`. -/
theorem isQuasicoherent_restrictScalars_hom_iff (e : R ≅ R') (he : α ≫ e.hom = α')
    (hR : ((SheafOfModules.restrictScalars.{u} α).obj (SheafOfModules.unit R)).IsQuasicoherent)
    (hR' : ((SheafOfModules.restrictScalars.{u} α').obj (SheafOfModules.unit R')).IsQuasicoherent)
    (M : SheafOfModules.{u} R') :
    ((SheafOfModules.restrictScalars.{u} e.hom).obj M).IsQuasicoherent ↔ M.IsQuasicoherent := by
  subst he
  exact (QcohLimits.isQuasicoherent_restrictScalars_iff α hR
      ((SheafOfModules.restrictScalars.{u} e.hom).obj M)).symm.trans
    (QcohLimits.isQuasicoherent_restrictScalars_iff (α ≫ e.hom) hR' M)

/-- The version of `isQuasicoherent_restrictScalars_hom_iff` for the inverse of `e`: an
`R`-module is quasi-coherent if and only if it is quasi-coherent after restriction of scalars
along `e.inv`. -/
theorem isQuasicoherent_restrictScalars_inv_iff (e : R ≅ R') (he : α ≫ e.hom = α')
    (hR : ((SheafOfModules.restrictScalars.{u} α).obj (SheafOfModules.unit R)).IsQuasicoherent)
    (hR' : ((SheafOfModules.restrictScalars.{u} α').obj (SheafOfModules.unit R')).IsQuasicoherent)
    (M : SheafOfModules.{u} R) :
    ((SheafOfModules.restrictScalars.{u} e.inv).obj M).IsQuasicoherent ↔ M.IsQuasicoherent :=
  isQuasicoherent_restrictScalars_hom_iff e.symm (e.comp_inv_eq.mpr he.symm) hR' hR M

/-- `isQuasicoherent_restrictScalars_inv_iff` as an equality of object properties: the
quasi-coherent `R'`-modules pulled back along restriction of scalars by `e.inv` are the
quasi-coherent `R`-modules. -/
theorem isQuasicoherent_inverseImage_restrictScalars_inv (e : R ≅ R') (he : α ≫ e.hom = α')
    (hR : ((SheafOfModules.restrictScalars.{u} α).obj (SheafOfModules.unit R)).IsQuasicoherent)
    (hR' : ((SheafOfModules.restrictScalars.{u} α').obj (SheafOfModules.unit R')).IsQuasicoherent) :
    (SheafOfModules.isQuasicoherent R').inverseImage
        (SheafOfModules.restrictScalars.{u} e.inv) = SheafOfModules.isQuasicoherent R :=
  funext fun M ↦ propext (isQuasicoherent_restrictScalars_inv_iff e he hR hR' M)

/-- Restriction of scalars along an isomorphism `e : R ≅ R'` of quasi-coherent `𝒪_S`-algebras,
as an equivalence between the category of quasi-coherent `R`-modules and the category of
quasi-coherent `R'`-modules. -/
def qcohRestrictScalarsEquivalence (e : R ≅ R') (he : α ≫ e.hom = α')
    (hR : ((SheafOfModules.restrictScalars.{u} α).obj (SheafOfModules.unit R)).IsQuasicoherent)
    (hR' : ((SheafOfModules.restrictScalars.{u} α').obj (SheafOfModules.unit R')).IsQuasicoherent) :
    (SheafOfModules.isQuasicoherent R).FullSubcategory ≌
      (SheafOfModules.isQuasicoherent R').FullSubcategory :=
  (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso e).congrFullSubcategory
    (isQuasicoherent_inverseImage_restrictScalars_inv e he hR hR')

end Stacks.AlgebraicGeometry.QcohOverAlgebra

namespace Stacks.AffineAlgebraEquivalence

open Stacks.AlgebraicGeometry.AffineQcohEquivalence
open Stacks.AlgebraicGeometry.AffineQcohPushforward

variable {S : Scheme.{u}} (A : Stacks.RelativeSpec.AlgebraSheaf S)
  [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A]

/-- The isomorphism of sheaves of rings `π_* 𝒪_{Spec_S A} ≅ A` underlying
`pushforwardAlgebraIso`, with `π_* 𝒪_{Spec_S A}` in the form
`Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardRing`. -/
def pushforwardRingIso :
    pushforwardRing (relativeSpecToBase A).base (relativeSpec A).ringCatSheaf ≅
      Stacks.RelativeSpec.AlgebraSheaf.ringSheaf A :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).mapIso
    ((Under.forget S.sheaf).mapIso (pushforwardAlgebraIso A))

/-- `pushforwardRingIso` is compatible with the structure maps from `𝒪_S`. -/
theorem structureMap_comp_pushforwardRingIso :
    (relativeSpecToBase A).toRingCatSheafHom ≫ (pushforwardRingIso A).hom =
      Stacks.RelativeSpec.AlgebraSheaf.structureMap A :=
  Sheaf.hom_ext <| NatTrans.ext <| funext fun U ↦ congrArg
    (fun φ : S.sheaf ⟶ A.right ↦ (forget₂ CommRingCat RingCat.{u}).map (φ.hom.app U))
    (Under.w (pushforwardAlgebraIso A).hom)

/-- Restriction of scalars along `pushforwardRingIso`, as an equivalence from the
quasi-coherent `π_* 𝒪_{Spec_S A}`-modules to the quasi-coherent `A`-modules. -/
def qcohPushforwardRingEquivalence :
    (SheafOfModules.isQuasicoherent
        (pushforwardRing (relativeSpecToBase A).base
          (relativeSpec A).ringCatSheaf)).FullSubcategory ≌
      (SheafOfModules.isQuasicoherent
        (Stacks.RelativeSpec.AlgebraSheaf.ringSheaf A)).FullSubcategory :=
  Stacks.AlgebraicGeometry.QcohOverAlgebra.qcohRestrictScalarsEquivalence
    (pushforwardRingIso A) (structureMap_comp_pushforwardRingIso A)
    (isQuasicoherent_restrictScalars_pushforwardRing (relativeSpecToBase A))
    ‹Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A›

/-- For a quasi-coherent `𝒪_S`-algebra `A` with relative spectrum `π : Spec_S A ⟶ S`, direct
image along `π` followed by the identification `π_* 𝒪 ≅ A` is an equivalence from the
quasi-coherent `𝒪_{Spec_S A}`-modules to the quasi-coherent `A`-modules. -/
def relativeSpecQcohEquivalence :
    (SheafOfModules.isQuasicoherent (relativeSpec A).ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherent
        (Stacks.RelativeSpec.AlgebraSheaf.ringSheaf A)).FullSubcategory :=
  haveI := Stacks.AlgebraicGeometry.AffineQcohUnit.isEquivalence_affineQuasicoherentPushforward
    (relativeSpecToBase A)
  (affineQuasicoherentPushforward (relativeSpecToBase A)).asEquivalence.trans
    (qcohPushforwardRingEquivalence A)

/-- The functor of `relativeSpecQcohEquivalence` sends a quasi-coherent module on `Spec_S A` to
its direct image along `π`, with the `π_* 𝒪`-module structure transported to an `A`-module
structure along `pushforwardRingIso`. -/
theorem relativeSpecQcohEquivalence_functor_obj_obj
    (M : (SheafOfModules.isQuasicoherent (relativeSpec A).ringCatSheaf).FullSubcategory) :
    ((relativeSpecQcohEquivalence A).functor.obj M).obj =
      (SheafOfModules.restrictScalars.{u} (pushforwardRingIso A).inv).obj
        ((pushforwardModules.{u} (relativeSpecToBase A).base
          (relativeSpec A).ringCatSheaf).obj M.obj) :=
  rfl

/-- For every quasi-coherent `A`-module `ℱ`
there is a quasi-coherent module `ℱ'` on the relative spectrum of `A` whose direct image is
`ℱ`. -/
theorem exists_iso_relativeSpecQcohPushforward
    (F : (SheafOfModules.isQuasicoherent
      (Stacks.RelativeSpec.AlgebraSheaf.ringSheaf A)).FullSubcategory) :
    ∃ F' : (SheafOfModules.isQuasicoherent (relativeSpec A).ringCatSheaf).FullSubcategory,
      Nonempty ((relativeSpecQcohEquivalence A).functor.obj F' ≅ F) :=
  ⟨(relativeSpecQcohEquivalence A).inverse.obj F,
    ⟨(relativeSpecQcohEquivalence A).counitIso.app F⟩⟩

/-- A quasi-coherent module on the relative
spectrum of `A` is determined up to isomorphism by its direct image. -/
def isoOfRelativeSpecQcohPushforwardIso
    {F₁ F₂ : (SheafOfModules.isQuasicoherent (relativeSpec A).ringCatSheaf).FullSubcategory}
    (φ : (relativeSpecQcohEquivalence A).functor.obj F₁ ≅
      (relativeSpecQcohEquivalence A).functor.obj F₂) :
    F₁ ≅ F₂ :=
  (relativeSpecQcohEquivalence A).functor.preimageIso φ

end Stacks.AffineAlgebraEquivalence

end

end
