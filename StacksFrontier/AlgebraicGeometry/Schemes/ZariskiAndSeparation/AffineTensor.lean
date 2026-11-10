module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TensorProduct
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherentSheaves.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison

/-!
# Tensor products of associated sheaves on an affine scheme

For modules `M` and `N` over a commutative ring `R`, the sheaf associated to their tensor
product is canonically isomorphic to the tensor product of their associated sheaves on `Spec R`.

## Main definitions

* `AlgebraicGeometry.specTensorPresheaf`, `AlgebraicGeometry.specTensorSheaf`: the sectionwise
  tensor product of two sheaves of modules on `Spec R` and its sheafification, read as objects
  over the structure (pre)sheaf of `Spec R`.
* `AlgebraicGeometry.tildeTensorIso`: the canonical isomorphism between these two sheaves of
  modules.

## Main results

* `AlgebraicGeometry.isSheaf_specStructureRingPresheaf`: the structure presheaf of `Spec R` is a
  sheaf of rings.
* `AlgebraicGeometry.tildeTensorIso_hom_tmul`: the isomorphism, read through the
  tilde--global-sections adjunction, sends a pure tensor to the sheafification of the tensor of
  the two canonical global sections.
* `AlgebraicGeometry.tildeTensorIso_natural`: its naturality in both modules.

## Implementation notes

The tensor product of sheaves is `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, the
sheafification of the sectionwise tensor-product presheaf. The affine scheme is presented as
`Spec R`, and Mathlib's `AlgebraicGeometry.tilde` is its associated-sheaf construction. The
induced map on tensor products is `AlgebraicGeometry.tildeTensorSheafMap`.

The comparison is built presheaf-wise from
`TensorProduct.AlgebraTensorModule.distribBaseChange`, sheafified, and then transported to
`tilde` along the natural isomorphism of tag 01I7. The isomorphism is extracted from an
existence statement so that the pure-tensor equation characterizing it is available at the same
time.

Several steps need an identification of two spellings of one object that the elaborator will not
unfold on its own: the structure sheaf of a ringed space as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` and as `structureSheafRing`; the
sheaf of rings of a scheme as `Scheme.ringCatSheaf` and as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of its structure presheaf; and
sheafification applied to a presheaf versus `Stacks.AssociatedSheaf.associatedSheaf`. Rather
than rewrite across them, each identification is absorbed once — into the result type of
`specTensorPresheaf`, `specTensorSheaf` and `isSheaf_specStructureRingPresheaf`, or into its own
`rfl` lemma — so that the statements that use them are type-correct without any transparency
option.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open Stacks.AssociatedSheaf

namespace AlgebraicGeometry

-- `(Spec R).ringCatSheaf` is a `TopCat.Sheaf`, which is a plain `def` for
-- `CategoryTheory.Sheaf`; projecting a sheaf of modules over it is type-correct only once that
-- one abbreviation unfolds, and until it does the rewrites in the proofs below do not fire.
attribute [local implicit_reducible] TopCat.Sheaf AlgebraicGeometry.Scheme.Modules

universe u

/-- The structure sheaf of a ringed space, as indexed for
`Stacks.SheafOfModules.TensorSheafification`, is the one used by the sheafification adjunction
on sheaves of modules. -/
private lemma structureSheaf_eq_ringSheaf (X : RingedSpace.{u, u})
    (h𝒪 : Presheaf.IsSheaf (Opens.grothendieckTopology X.carrier)
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.presheaf)) :
    Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf h𝒪 =
      structureSheafRing X := rfl

/-- The structure presheaf of `Spec R`, as `Stacks.SheafOfModules.TensorSheafification` indexes
it, is a sheaf of rings: it is the underlying presheaf of the scheme's own sheaf of rings. The
sheaf condition is stated at the presheaf `Stacks.SheafOfModules.TensorSheafification` expects,
rather than at `(Spec R).ringCatSheaf`, whose underlying presheaf is only definitionally the
same one. -/
theorem isSheaf_specStructureRingPresheaf (R : CommRingCat.{u}) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(Spec R))
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf (Spec R).presheaf) :=
  (Spec R).ringCatSheaf.2

/-- The sectionwise tensor product of two sheaves of modules on `Spec R`, as a presheaf of
modules over the structure presheaf of `Spec R`. -/
abbrev specTensorPresheaf (R : CommRingCat.{u}) (F G : (Spec R).Modules) :
    PresheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf (Spec
      R).presheaf) :=
  (PresheafOfModules.tensorObj (O := (Spec R).presheaf) (F.val) (G.val))

/-- The tensor product of two sheaves of modules on `Spec R`: the sheafification of their
sectionwise tensor product. -/
@[sga "4 IV 12.7" "special case"]
abbrev specTensorSheaf (R : CommRingCat.{u}) (F G : (Spec R).Modules) : (Spec R).Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(Spec R).presheaf,
    Presheaf.isSheaf_of_isSheaf_comp _ (Spec R).presheaf (forget₂ CommRingCat RingCat)
      (isSheaf_specStructureRingPresheaf R)⟩).obj F).obj G

/-- The sheafification unit is natural: sheafifying a morphism and then taking the unit agrees
with taking the unit and then applying the sheafified morphism. -/
private lemma sheafify_map_apply (X : RingedSpace.{u, u})
    (P Q : PresheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      X.presheaf))
    (f : P ⟶ Q) (U : (Opens X)ᵒᵖ) (x : P.obj U) :
    (((Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf
      (structureSheafRing X).property).map f).val.app U)
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf
          (structureSheafRing X).property P).app U x) =
    (Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf
      (structureSheafRing X).property Q).app U (f.app U x) :=
  congrArg (fun g => g.app U x)
    ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction X.presheaf
      (structureSheafRing X).property).unit.naturality f).symm

/-- The monoidal tensor of two presheaf morphisms acts on a pure tensor factorwise. -/
private lemma tensorHom_tmul (X : RingedSpace.{u, u})
    {F F' G G' : PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.presheaf)}
    (f : F ⟶ F') (g : G ⟶ G') (U : (Opens X)ᵒᵖ) (x : F.obj U) (y : G.obj U) :
    ((PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f g).app U)
      (TensorProduct.tmul (X.presheaf.obj U) x y) =
    TensorProduct.tmul (X.presheaf.obj U) (f.app U x) (g.app U y) := rfl

/-- Through the tilde--global-sections adjunction, a morphism out of `M̃` is determined by its
effect on the canonical global sections. -/
private lemma homEquiv_apply (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    (F : (Spec R).Modules) (f : tilde M ⟶ F) (m : M) :
    (((tilde.adjunction (R := R)).homEquiv M F) f).hom m =
      (f.val.app (op ⊤)) ((tilde.toOpen M ⊤).hom m) := rfl

/-- The canonical global sections of `M̃` are natural in `M`. -/
private lemma tilde_map_toOpen_top (R : CommRingCat.{u}) {M M' : ModuleCat.{u} R} (f : M ⟶ M')
    (m : M) :
    ((tilde.map f).val.app (op ⊤)).hom ((tilde.toOpen M ⊤).hom m) =
      (tilde.toOpen M' ⊤).hom (f.hom m) := by
  change ((modulesSpecToSheaf.map (tilde.map f)).hom.app (op ⊤)).hom _ = _
  exact congrArg (fun k => k.hom m) (tilde.toOpen_map_app f ⊤)

/-- Over a fixed open, the base change of a tensor product of `R`-modules is the tensor product
of their base changes. -/
private noncomputable def associatedPresheafTensorIsoAt (R : CommRingCat.{u})
    (X : RingedSpace.{u, u}) (α : R →+* X.presheaf.obj (op ⊤)) (U : Opens X)
    (M N : ModuleCat.{u} R) :
    (associatedPresheaf X α (M ⊗ N)).obj (op U) ≅
      ((PresheafOfModules.tensorObj (O := X.presheaf) ((associatedPresheaf X α
        M)) ((associatedPresheaf X α N)))).obj (op U) := by
  let S : Type u := R
  let A : Type u := X.presheaf.obj (op U)
  let M₀ := (constantModulePresheaf X M).obj (op U)
  let N₀ := (constantModulePresheaf X N).obj (op U)
  letI : Algebra S A := ((globalSectionsMap X α).app (op U)).hom.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.distribBaseChange S A M₀ N₀).toModuleIso

/-- The presheaf-level comparison: `𝒪 ⊗_R (M ⊗_R N) ≅ (𝒪 ⊗_R M) ⊗_𝒪 (𝒪 ⊗_R N)`. -/
private noncomputable def associatedPresheafTensorIso (R : CommRingCat.{u})
    (M N : ModuleCat.{u} R) :
    associatedPresheaf (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom
        (M ⊗ N) ≅
      PresheafOfModules.tensorObj (O := (Spec R).presheaf)
        (associatedPresheaf (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom M)
        (associatedPresheaf (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom N) := by
  let X := (Spec R).toRingedSpace
  let α := (Scheme.ΓSpecIso R).inv.hom
  refine PresheafOfModules.isoMk (fun U ↦ associatedPresheafTensorIsoAt R X α U.unop M N)
    (fun {U V} i ↦ ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg (fun t ↦ t + _) hx).trans
      ((congrArg (fun t ↦ _ + t) hy).trans (map_add _ x y).symm))
  | tmul a z =>
    let := ((globalSectionsMap X α).app U).hom.toAlgebra
    let : Module ↑((constantRingPresheaf X ↑R).obj U) (TensorProduct ↑R ↑M ↑N) :=
      inferInstanceAs (Module ↑((constantRingPresheaf X ↑R).obj U)
        ↑((constantModulePresheaf X (M ⊗ N)).obj U))
    induction z using TensorProduct.inductionOn with
    | add z w hz hw =>
      exact ((congrArg _ (TensorProduct.tmul_add a z w)).trans ((map_add _ _ _).trans
        ((congrArg (fun t ↦ t + _) hz).trans ((congrArg (fun t ↦ _ + t) hw).trans
          (map_add _ _ _).symm)))).trans (congrArg _ (TensorProduct.tmul_add a z w)).symm
    | tmul m n => with_unfolding_all rfl

/-- The sheaf-level comparison obtained by sheafifying `associatedPresheafTensorIso`. -/
private noncomputable def associatedSheafTensorIso (R : CommRingCat.{u})
    (M N : ModuleCat.{u} R) :
    associatedSheaf (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom (M ⊗ N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(Spec R).toRingedSpace.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (Spec R).toRingedSpace.presheaf
          (forget₂ CommRingCat RingCat) (structureSheafRing (Spec R).toRingedSpace).property⟩).obj
        (associatedSheaf (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom M)).obj
        (associatedSheaf (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom N) := by
  let X := (Spec R).toRingedSpace
  let α := (Scheme.ΓSpecIso R).inv.hom
  let h := associatedPresheafTensorIso R M N
  letI : HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  letI : (Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let h𝒪 := (structureSheafRing X).property
  let η := Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf h𝒪
  exact η.mapIso h ≪≫ Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso X.presheaf
    h𝒪 (associatedPresheaf X α M) (associatedPresheaf X α N)

/-- The sheafified comparison sends the canonical global section of a pure tensor to the tensor
of the two canonical global sections. -/
private lemma associatedSheafTensorIso_tmul_tensorUnitSection
    (R : CommRingCat.{u}) (M N : ModuleCat.{u} R) (m : M) (n : N) :
    ((associatedSheafTensorIso R M N).hom.val.app (op ⊤))
        (tensorUnitSection (X := (Spec R).toRingedSpace)
          (Scheme.ΓSpecIso R).inv.hom (M ⊗ N) (op ⊤)
          (TensorProduct.tmul R m n)) =
      ((Stacks.SheafOfModules.TensorSheafification.toSheafify (Spec R).toRingedSpace.presheaf
          (structureSheafRing (Spec R).toRingedSpace).property
          (PresheafOfModulesOfCommRing.Monoidal.tensorObj
            (associatedSheaf (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom M).val
            (associatedSheaf (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom N).val)).app
        (op ⊤))
        (TensorProduct.tmul ((Spec R).toRingedSpace.presheaf.obj (op ⊤))
          (tensorUnitSection (X := (Spec R).toRingedSpace)
            (Scheme.ΓSpecIso R).inv.hom M (op ⊤) m)
          (tensorUnitSection (X := (Spec R).toRingedSpace)
            (Scheme.ΓSpecIso R).inv.hom N (op ⊤) n)) := by
  let X := (Spec R).toRingedSpace
  let h𝒪 := (structureSheafRing X).property
  let : Module ↑((Spec R).toRingedSpace.presheaf.obj (op ⊤))
      ↑((associatedSheaf (Spec R).toRingedSpace
        (Scheme.ΓSpecIso R).inv.hom M).val.obj (op ⊤)) :=
    ((associatedSheaf (Spec R).toRingedSpace
      (Scheme.ΓSpecIso R).inv.hom M).val.obj (op ⊤)).isModule
  let : Module ↑((Spec R).toRingedSpace.presheaf.obj (op ⊤))
      ↑((associatedSheaf (Spec R).toRingedSpace
        (Scheme.ΓSpecIso R).inv.hom N).val.obj (op ⊤)) :=
    ((associatedSheaf (Spec R).toRingedSpace
      (Scheme.ΓSpecIso R).inv.hom N).val.obj (op ⊤)).isModule
  let P := associatedPresheaf (Spec R).toRingedSpace
    (Scheme.ΓSpecIso R).inv.hom (M ⊗ N)
  let Q := PresheafOfModules.tensorObj (O := X.presheaf)
    (associatedSheaf (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom M).val
    (associatedSheaf (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom N).val
  let h := associatedPresheafTensorIso R M N
  let u := Stacks.SheafOfModules.TensorSheafification.tensorUnitMap X.presheaf h𝒪
    (associatedPresheaf (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom M)
    (associatedPresheaf (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom N)
  let q := h.hom ≫ u
  let x : P.obj (op ⊤) :=
    let : Algebra R ((Spec R).toRingedSpace.presheaf.obj (op ⊤)) :=
      ((globalSectionsMap (Spec R).toRingedSpace
        (Scheme.ΓSpecIso R).inv.hom).app (op ⊤)).hom.toAlgebra
    (1 : (Spec R).toRingedSpace.presheaf.obj (op ⊤)) ⊗ₜ[R] TensorProduct.tmul R m n
  have hq : q.app (op ⊤) x =
      TensorProduct.tmul ((Spec R).toRingedSpace.presheaf.obj (op ⊤))
        (tensorUnitSection (X := (Spec R).toRingedSpace)
          (Scheme.ΓSpecIso R).inv.hom M (op ⊤) m)
        (tensorUnitSection (X := (Spec R).toRingedSpace)
          (Scheme.ΓSpecIso R).inv.hom N (op ⊤) n) := by
    with_unfolding_all rfl
  have hunit := congrArg (fun g => g.app (op ⊤) x)
    ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction X.presheaf h𝒪).unit.naturality
      q).symm
  change (((Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf h𝒪).map q).val.app (op
    ⊤))
      ((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf h𝒪 P).app (op ⊤) x) =
    (Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf h𝒪 Q).app (op ⊤) (q.app (op ⊤)
      x) at hunit
  have hx : (Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf h𝒪 P).app (op ⊤) x =
      tensorUnitSection (X := (Spec R).toRingedSpace)
        (Scheme.ΓSpecIso R).inv.hom (M ⊗ N) (op ⊤)
        (TensorProduct.tmul R m n) := rfl
  rw [hq, hx] at hunit
  have hmap : (associatedSheafTensorIso R M N).hom =
      (Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf h𝒪).map q :=
    ((Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf h𝒪).map_comp h.hom u).symm
  rw [hmap]
  exact hunit

/-- The comparison transported from `associatedSheaf` to `tilde` along the natural isomorphism
of tag 01I7. -/
private noncomputable def tildeTensorComparison (R : CommRingCat.{u})
    (M N : ModuleCat.{u} R) :
    tilde (M ⊗ N) ≅
      specTensorSheaf R (tilde M) (tilde N) := by
  let κ := (tildeAssociatedSheafNatIso R).val
  let X := (Spec R).toRingedSpace
  let h𝒪 := (structureSheafRing X).property
  let η := Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf h𝒪
  letI : MonoidalCategory
      (PresheafOfModules (structureSheafRing X).obj) := by
    change MonoidalCategory (PresheafOfModules
      (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    infer_instance
  let hM := (SheafOfModules.forget (structureSheafRing X)).mapIso
    (κ.app M).symm
  let hN := (SheafOfModules.forget (structureSheafRing X)).mapIso
    (κ.app N).symm
  exact (κ.app (M ⊗ N)) ≪≫ associatedSheafTensorIso R M N ≪≫
    η.mapIso (MonoidalCategory.tensorIso hM hN)

/-- The inverse of the tag 01I7 comparison sends the canonical global section back to the
canonical global section of `M̃`. -/
private lemma tildeAssociatedSheafNatIso_inv_tensorUnitSection
    (R : CommRingCat.{u}) (M : ModuleCat.{u} R) (m : M) :
    (((tildeAssociatedSheafNatIso R).val.inv.app M).val.app (op ⊤))
        (tensorUnitSection (X := (Spec R).toRingedSpace)
          (Scheme.ΓSpecIso R).inv.hom M (op ⊤) m) =
      (tilde.toOpen M ⊤).hom m := by
  have h := (tildeAssociatedSheafNatIso R).property M m
  have hcomp := congrArg (fun f => (f.val.app (op ⊤)))
    (Iso.hom_inv_id ((tildeAssociatedSheafNatIso R).val.app M))
  change ((tildeAssociatedSheafNatIso R).val.hom.app M).val.app (op ⊤) ≫
      ((tildeAssociatedSheafNatIso R).val.inv.app M).val.app (op ⊤) = 𝟙 _ at hcomp
  have hcompapp :
      (((tildeAssociatedSheafNatIso R).val.hom.app M).val.app (op ⊤) ≫
            ((tildeAssociatedSheafNatIso R).val.inv.app M).val.app (op ⊤))
          ((tilde.toOpen M ⊤).hom m) =
        (((tildeAssociatedSheafNatIso R).val.inv.app M).val.app (op ⊤))
          ((((tildeAssociatedSheafNatIso R).val.hom.app M).val.app (op ⊤))
            ((tilde.toOpen M ⊤).hom m)) :=
    CategoryTheory.comp_apply _ _ _
  have heval :
      (((tildeAssociatedSheafNatIso R).val.inv.app M).val.app (op ⊤))
          (((tildeAssociatedSheafNatIso R).val.hom.app M).val.app (op ⊤)
            ((tilde.toOpen M ⊤).hom m)) = (tilde.toOpen M ⊤).hom m := by
    rw [← hcompapp, hcomp]
    exact CategoryTheory.id_apply _
  exact (congrArg
    (fun x => ((tildeAssociatedSheafNatIso R).val.inv.app M).val.app (op ⊤) x)
    h).symm.trans heval

/-- The pure-tensor equation for the transported comparison. -/
private lemma tildeTensorComparison_hom_tmul (R : CommRingCat.{u})
    (M N : ModuleCat.{u} R) (m : M) (n : N) :
    (((tilde.adjunction (R := R)).homEquiv (M ⊗ N)
      (specTensorSheaf R (tilde M) (tilde N))) (tildeTensorComparison R M N).hom).hom
        (TensorProduct.tmul R m n) =
      ((Stacks.SheafOfModules.TensorSheafification.toSheafify (Spec R).presheaf
        (isSheaf_specStructureRingPresheaf R)
        (specTensorPresheaf R (tilde M) (tilde N))).app (.op ⊤)).hom
        (TensorProduct.tmul ((Spec R).presheaf.obj (.op ⊤))
          ((tilde.toOpen M ⊤).hom m) ((tilde.toOpen N ⊤).hom n)) := by
  rw [homEquiv_apply]
  change (((Stacks.SheafOfModules.TensorSheafification.sheafify (Spec R).toRingedSpace.presheaf
      (structureSheafRing (Spec R).toRingedSpace).property).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom
        ((tildeAssociatedSheafNatIso R).val.inv.app M).val
        ((tildeAssociatedSheafNatIso R).val.inv.app N).val)).val.app (op ⊤))
      (((associatedSheafTensorIso R M N).hom.val.app (op ⊤))
        (((tildeAssociatedSheafNatIso R).val.hom.app (M ⊗ N)).val.app (op ⊤)
          ((tilde.toOpen (M ⊗ N) ⊤).hom (TensorProduct.tmul R m n)))) = _
  rw [(tildeAssociatedSheafNatIso R).property,
    associatedSheafTensorIso_tmul_tensorUnitSection]
  refine (sheafify_map_apply (Spec R).toRingedSpace
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (associatedSheaf (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom M).val
      (associatedSheaf (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom N).val)
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (tilde M).val (tilde N).val)
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom
      ((tildeAssociatedSheafNatIso R).val.inv.app M).val
      ((tildeAssociatedSheafNatIso R).val.inv.app N).val)
    (op ⊤)
    (TensorProduct.tmul ((Spec R).toRingedSpace.presheaf.obj (op ⊤))
      (tensorUnitSection (X := (Spec R).toRingedSpace)
        (Scheme.ΓSpecIso R).inv.hom M (op ⊤) m)
      (tensorUnitSection (X := (Spec R).toRingedSpace)
        (Scheme.ΓSpecIso R).inv.hom N (op ⊤) n))).trans ?_
  refine congrArg _ ?_
  refine (tensorHom_tmul (Spec R).toRingedSpace
    ((tildeAssociatedSheafNatIso R).val.inv.app M).val
    ((tildeAssociatedSheafNatIso R).val.inv.app N).val (op ⊤) _ _).trans ?_
  exact congr($(tildeAssociatedSheafNatIso_inv_tensorUnitSection R M m) ⊗ₜ[
    ↑((Spec R).toRingedSpace.presheaf.obj (op ⊤))]
    $(tildeAssociatedSheafNatIso_inv_tensorUnitSection R N n))

private lemma exists_tildeTensorIso (R : CommRingCat.{u})
    (M N : ModuleCat.{u} R) :
    ∃ e : tilde (M ⊗ N) ≅
        specTensorSheaf R (tilde M) (tilde N),
      ∀ (m : M) (n : N),
        (((tilde.adjunction (R := R)).homEquiv (M ⊗ N)
          (specTensorSheaf R (tilde M) (tilde N))) e.hom).hom
            (TensorProduct.tmul R m n) =
          ((Stacks.SheafOfModules.TensorSheafification.toSheafify (Spec R).presheaf
            (isSheaf_specStructureRingPresheaf R)
            (specTensorPresheaf R (tilde M) (tilde N))).app (.op ⊤)).hom
            (TensorProduct.tmul ((Spec R).presheaf.obj (.op ⊤))
              ((tilde.toOpen M ⊤).hom m) ((tilde.toOpen N ⊤).hom n)) :=
  ⟨tildeTensorComparison R M N, tildeTensorComparison_hom_tmul R M N⟩

/-- For modules `M` and `N` over `R`, there is a canonical isomorphism
`(M ⊗[R] N)~ ≅ M~ ⊗_{𝒪_(Spec R)} N~`. -/
@[stacks 01I8 "tensor_product", ega "I 1.3.12" "(i)"]
noncomputable def tildeTensorIso (R : CommRingCat.{u})
    (M N : ModuleCat.{u} R) :
    tilde (M ⊗ N) ≅
      specTensorSheaf R (tilde M) (tilde N) :=
  Classical.choose (private_decl% (exists_tildeTensorIso R M N))

/-- The canonical isomorphism sends a pure tensor, under the
tilde--global-sections adjunction, to the section obtained by tensoring the two
canonical global sections and applying the sheafification unit. -/
@[stacks 01I8 "tensor_product"]
theorem tildeTensorIso_hom_tmul (R : CommRingCat.{u})
    (M N : ModuleCat.{u} R) (m : M) (n : N) :
    (((tilde.adjunction (R := R)).homEquiv (M ⊗ N)
      (specTensorSheaf R (tilde M) (tilde N))) (tildeTensorIso R M N).hom).hom
        (TensorProduct.tmul R m n) =
      ((Stacks.SheafOfModules.TensorSheafification.toSheafify (Spec R).presheaf
        (isSheaf_specStructureRingPresheaf R)
        (specTensorPresheaf R (tilde M) (tilde N))).app (.op ⊤)).hom
        (TensorProduct.tmul ((Spec R).presheaf.obj (.op ⊤))
          ((tilde.toOpen M ⊤).hom m) ((tilde.toOpen N ⊤).hom n)) :=
  Classical.choose_spec (exists_tildeTensorIso R M N) m n

/-- The comparison is canonical: it is the *only* isomorphism `(M ⊗ N)~ ≅ M~ ⊗ N~` satisfying
the pure-tensor equation `tildeTensorIso_hom_tmul`, so `tildeTensorIso` does not depend on the
choice `Classical.choose` makes to produce it. -/
@[stacks 01I8 "tensor_product"]
theorem tildeTensorIso_eq_of_hom_tmul (R : CommRingCat.{u})
    (M N : ModuleCat.{u} R)
    (e : tilde (M ⊗ N) ≅ specTensorSheaf R (tilde M) (tilde N))
    (he : ∀ (m : M) (n : N),
      (((tilde.adjunction (R := R)).homEquiv (M ⊗ N)
        (specTensorSheaf R (tilde M) (tilde N))) e.hom).hom
          (TensorProduct.tmul R m n) =
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify (Spec R).presheaf
          (isSheaf_specStructureRingPresheaf R)
          (specTensorPresheaf R (tilde M) (tilde N))).app (.op ⊤)).hom
          (TensorProduct.tmul ((Spec R).presheaf.obj (.op ⊤))
            ((tilde.toOpen M ⊤).hom m) ((tilde.toOpen N ⊤).hom n))) :
    e = tildeTensorIso R M N := by
  apply Iso.ext
  apply ((tilde.adjunction (R := R)).homEquiv (M ⊗ N)
    (specTensorSheaf R (tilde M) (tilde N))).injective
  apply ModuleCat.hom_ext
  refine TensorProduct.ext' fun m n ↦ ?_
  exact (he m n).trans (tildeTensorIso_hom_tmul R M N m n).symm

/-- The canonical tensor comparison is natural in both modules. -/
@[stacks 01I8 "tensor_product"]
theorem tildeTensorIso_natural (R : CommRingCat.{u})
    {M M' N N' : ModuleCat.{u} R} (f : M ⟶ M') (g : N ⟶ N') :
    tilde.map (f ⊗ₘ g) ≫ (tildeTensorIso R M' N').hom =
      (tildeTensorIso R M N).hom ≫ tildeTensorSheafMap R f g := by
  let adj := tilde.adjunction (R := R)
  apply (adj.homEquiv (M ⊗ N)
    (specTensorSheaf R (tilde M') (tilde N'))).injective
  refine (adj.homEquiv_naturality_left (f ⊗ₘ g) (tildeTensorIso R M' N').hom).trans
    (Eq.trans ?_ (adj.homEquiv_naturality_right (tildeTensorIso R M N).hom
      (tildeTensorSheafMap R f g)).symm)
  apply ModuleCat.hom_ext
  refine TensorProduct.ext' fun m n ↦ ?_
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [show (f ⊗ₘ g).hom (m ⊗ₜ[R] n) = f.hom m ⊗ₜ g.hom n from rfl, tildeTensorIso_hom_tmul,
    tildeTensorIso_hom_tmul]
  have h := sheafify_map_apply (Spec R).toRingedSpace _ _
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (tilde.map f).val (tilde.map g).val)
    (op ⊤) (TensorProduct.tmul ((Spec R).toRingedSpace.presheaf.obj (op ⊤))
      ((tilde.toOpen M ⊤).hom m) ((tilde.toOpen N ⊤).hom n))
  change _ = (Stacks.SheafOfModules.TensorSheafification.toSheafify (Spec R).presheaf
    (isSheaf_specStructureRingPresheaf R)
    (specTensorPresheaf R (tilde M') (tilde N'))).app
      (op ⊤) (TensorProduct.tmul ((Spec R).presheaf.obj (op ⊤))
        (((tilde.map f).val.app (op ⊤)).hom ((tilde.toOpen M ⊤).hom m))
        (((tilde.map g).val.app (op ⊤)).hom ((tilde.toOpen N ⊤).hom n))) at h
  rw [tilde_map_toOpen_top, tilde_map_toOpen_top] at h
  exact h.symm

end AlgebraicGeometry

end
