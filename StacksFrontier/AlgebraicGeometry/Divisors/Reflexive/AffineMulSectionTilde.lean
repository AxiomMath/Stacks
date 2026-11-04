module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRaisedColimits
public import StacksFrontier.AlgebraicGeometry.AffineExteriorPowerCompare.Natural
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowers
public import StacksFrontier.AlgebraicGeometry.Modules.AffineDualSheaf
import all StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalFiniteFreeSummand
import all StacksFrontier.AlgebraicGeometry.Modules.AffineInternalHomNatural

/-!
# Multiplication by a global section, on an affine scheme

Let `R` be a commutative ring and `M`, `N` two `R`-modules.  Multiplication by a global section
`σ : 𝒪_{Spec R} ⟶ M̃` is the morphism `mulSectionHom (Spec R) σ : Ñ ⟶ M̃ ⊗ Ñ` of
`StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowers`.  This file identifies it,
through the affine tensor comparison `AlgebraicGeometry.tensorSheafTildeIso`, with the associated
sheaf of the module-theoretic multiplication `n ↦ s ⊗ n`, where `s ∈ M` is the element
corresponding to `σ`.

## Main results

* `Stacks.AlgebraicGeometry.ReflexivePowers.mulSectionHom_tensorSheafTildeIso`: the affine
  comparison square
  `mulSectionHom (Spec R) σ ≫ tensorSheafTildeIso R M N = tilde.map (TensorProduct.mk R M N s)`,
  for any `σ` whose value on the unit section is `tilde.toOpen M ⊤ s`.
* `Stacks.AlgebraicGeometry.ReflexivePowers.mulSectionHom_unitHomEquiv_symm`: the same square for
  the morphism attached to a section of `M̃` by `SheafOfModules.unitHomEquiv`.
* `Stacks.AlgebraicGeometry.ReflexivePowers.mulSectionHom_whiskerLeft`: multiplication by a
  section is natural in its argument, on an arbitrary ringed space.
* `Stacks.AlgebraicGeometry.ReflexivePowers.tensorSheafIso_hom`: the functoriality isomorphism
  `AlgebraicGeometry.tensorSheafIso` is the canonical induced morphism `tensorSheafMap`, hence
  (`tensorHom_eq_tensorSheafMap`) the monoidal tensor product of the two morphisms.
* `Stacks.AlgebraicGeometry.ReflexivePowers.mulSectionHom_tensorSheafIso`: multiplication by a
  section is natural against `AlgebraicGeometry.tensorSheafIso` in the second argument.

## Implementation notes

**Which tensor product.**  Everything here is stated for the tensor product of the local
instance `Stacks.SheafOfModules.OnSpace.monoidal`, whose tensor is
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` by `rfl`; that is the tensor product
`mulSectionHom` and `AlgebraicGeometry.tensorSheafTildeIso` are both phrased with, so no
identification between competing tensor products is needed.

**How `σ` is pinned down.**  The main theorem quantifies over an arbitrary
`σ : 𝟙_ _ ⟶ M̃` together with a hypothesis giving its value on the unit section, rather than over
the morphism `(tilde M).unitHomEquiv.symm t` attached to a section `t`.  That is the reusable
form: `mulSectionHom_app` computes `mulSectionHom` from exactly that value and nothing else.  The
specialisation to `unitHomEquiv.symm` is `mulSectionHom_unitHomEquiv_symm`, whose hypothesis is
obtained from `SheafOfModules.unitHomEquiv_apply_coe`.

**The route through the two sheafifications.**  Both sides of the main square are morphisms out
of `Ñ`, so `tilde_hom_ext_toOpen` reduces it to the single global section `tilde.toOpen N ⊤ n`.
There `mulSectionHom_app` produces a local pure tensor, and the comparison
`tensorSheafTildeIso = tensorSheafComparison ≪≫ (tildeTensorIso R M N).symm` is evaluated on it in
two steps: `tensorSheafComparison_hom_app_tmul` carries a pure tensor of the sectionwise tensor
product to a pure tensor of the monoidal one — both are sheafification units, and the comparison
is the sheafification of a presheaf map which is the identity on sections — and
`tildeTensorIso_hom_app_toOpen` is `AlgebraicGeometry.tildeTensorIso_hom_tmul` read through the
tilde--global-sections adjunction, whose `homEquiv` evaluates by `rfl`.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace (O sheafifyFunctor sheafifyUnit toTensorSheafSection tensorSheafMap_app_toTensorSheafSection)
open Stacks.SheafOfModules.TensorSheafification (sheafify toSheafify)
open Stacks.SheafOfModules.OnSpace (tensorObjTmul unitSection tensorHom_tmul
  sheaf_comp_app_apply tensor_hom_ext)

universe u

namespace Stacks.AlgebraicGeometry.ReflexivePowers

-- `(Spec R).Modules` and `TopCat.Sheaf` are plain `def`s; the statements below mix them with
-- `SheafOfModules (structureSheafRing _)`, which they unfold to, and a goal mentioning both is
-- not type-correct at `implicit` transparency until they do unfold, so no `rw` fires.
attribute [local implicit_reducible] TopCat.Sheaf TopCat.Presheaf.IsSheaf
  AlgebraicGeometry.Scheme.Modules Stacks.SheafOfModules.Tensor.ringSheaf
  structureSheafRing CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

/-! ### Extensionality and evaluation for associated sheaves -/

/-- An isomorphism of sheaves of modules cancels its hom on sections. -/
theorem iso_inv_hom_app {C : Type*} [Category C] {K : GrothendieckTopology C}
    {Rr : Sheaf K RingCat} {A B : SheafOfModules Rr} (e : A ≅ B) (U : Cᵒᵖ) (x : A.val.obj U) :
    (e.inv.val.app U).hom ((e.hom.val.app U).hom x) = x :=
  congrArg (fun φ : A ⟶ A => (φ.val.app U).hom x) e.hom_inv_id

/-! ### The sheafification unit -/

/-- Naturality of the sheafification unit of
`Stacks.SheafOfModules.TensorStalkRingedSpace`, on a local section. -/
theorem sheafifyUnit_naturality (Y : RingedSpace.{u, u}) {P Q : PresheafOfModules.{u} (O Y)}
    (f : P ⟶ Q) (U : (Opens Y.carrier)ᵒᵖ) (x : P.obj U) :
    (((sheafifyFunctor Y).map f).val.app U).hom (((sheafifyUnit Y P).app U).hom x) =
      ((sheafifyUnit Y Q).app U).hom ((f.app U).hom x) := by
  have hnat := (PresheafOfModules.sheafificationAdjunction (R := structureSheafRing Y)
    (𝟙 (structureSheafRing Y).obj)).unit.naturality f
  exact (congrArg (fun α => (PresheafOfModules.Hom.app α U).hom x) hnat).symm

/-! ### The two tensor-product presheaves -/

/-- `AlgebraicGeometry.tensorSheafComparison` carries a local pure tensor to the corresponding
pure tensor of the monoidal tensor product. -/
theorem tensorSheafComparison_hom_app_tmul (X : Scheme.{u}) (F G : X.Modules)
    (U : (Opens X.carrier)ᵒᵖ) (a : F.val.obj U) (b : G.val.obj U) :
    ((tensorSheafComparison X F G).hom.val.app U).hom
        (toTensorSheafSection X.toRingedSpace F G U (a ⊗ₜ[X.presheaf.obj U] b)) =
      ((toSheafify X.presheaf X.ringCatSheaf.2
          ((PresheafOfModules.tensorObj (O := X.presheaf) (F.val) (G.val)))).app U).hom
        (a ⊗ₜ[X.presheaf.obj U] b) :=
  sheafifyUnit_naturality X.toRingedSpace
    (Stacks.SheafOfModules.TensorRaised.presheafTensorCompare F.val G.val).hom U
    (a ⊗ₜ[X.presheaf.obj U] b)

/-- The inverse of `AlgebraicGeometry.tensorSheafComparison`, on a pure tensor of the monoidal
tensor product coming from the presheaf. -/
theorem tensorSheafComparison_inv_app_tmul (X : Scheme.{u}) (F G : X.Modules)
    (U : (Opens X.carrier)ᵒᵖ) (a : F.val.obj U) (b : G.val.obj U) :
    ((tensorSheafComparison X F G).inv.val.app U).hom
        (((toSheafify X.presheaf X.ringCatSheaf.2
          ((PresheafOfModules.tensorObj (O := X.presheaf) (F.val) (G.val)))).app U).hom (a ⊗ₜ[X.presheaf.obj U] b)) =
      toTensorSheafSection X.toRingedSpace F G U (a ⊗ₜ[X.presheaf.obj U] b) := by
  rw [← tensorSheafComparison_hom_app_tmul, iso_inv_hom_app]

/-- `AlgebraicGeometry.tensorSheafificationIso` acts factorwise on a pure tensor coming from the
presheaf tensor product. -/
theorem tensorSheafificationIso_hom_app_tmul (X : Scheme.{u}) {F F' G G' : X.Modules}
    (e : F ≅ F') (e' : G ≅ G') (U : (Opens X.carrier)ᵒᵖ)
    (a : F.val.obj U) (b : G.val.obj U) :
    ((tensorSheafificationIso X e e').hom.val.app U).hom
        (((toSheafify X.presheaf X.ringCatSheaf.2
          ((PresheafOfModules.tensorObj (O := X.presheaf) (F.val) (G.val)))).app U).hom (a ⊗ₜ[X.presheaf.obj U] b)) =
      ((toSheafify X.presheaf X.ringCatSheaf.2
          ((PresheafOfModules.tensorObj (O := X.presheaf) (F'.val) (G'.val)))).app U).hom
        ((e.hom.val.app U).hom a ⊗ₜ[X.presheaf.obj U] (e'.hom.val.app U).hom b) :=
  Stacks.SheafOfModules.sheafification_map_unit X.presheaf X.ringCatSheaf.2
    (MonoidalCategory.tensorHom
      (C := PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
      ((SheafOfModules.forget X.ringCatSheaf).map e.hom)
      ((SheafOfModules.forget X.ringCatSheaf).map e'.hom)) U
    (a ⊗ₜ[X.presheaf.obj U] b)

/-- **The functoriality isomorphism of the tensor product is the canonical induced morphism.**
Both are determined by their values on local pure tensors, where both act factorwise. -/
theorem tensorSheafIso_hom (X : Scheme.{u}) {F F' G G' : X.Modules} (e : F ≅ F')
    (e' : G ≅ G') :
    (tensorSheafIso X e e').hom = ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩)).map ((e.hom, e'.hom) : (_, _) ⟶ (_, _))) := by
  refine tensor_hom_ext X.toRingedSpace fun U a b => ?_
  rw [tensorSheafIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    sheaf_comp_app_apply, sheaf_comp_app_apply, tensorSheafComparison_hom_app_tmul,
    tensorSheafificationIso_hom_app_tmul, tensorSheafComparison_inv_app_tmul]
  exact (tensorSheafMap_app_toTensorSheafSection X.toRingedSpace F G F' G' e.hom e'.hom U.unop
    a b).symm

/-- The monoidal tensor product of two morphisms of sheaves of modules is the canonical induced
morphism `tensorSheafMap`. -/
theorem tensorHom_eq_tensorSheafMap (Y : RingedSpace.{u, u})
    {A A' B B' : SheafOfModules.{u} (structureSheafRing Y)} (f : A ⟶ A') (g : B ⟶ B') :
    (f ⊗ₘ g) = ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨(Y).presheaf, (Y).IsSheaf⟩)).map ((f, g) : (_, _) ⟶ (_, _))) :=
  tensor_hom_ext Y fun U a b =>
    (tensorHom_tmul Y f g U a b).trans
      (tensorSheafMap_app_toTensorSheafSection Y A B A' B' f g U.unop a b).symm

/-! ### Multiplication by a global section -/

/-- **Multiplication by a global section is natural in its argument.**  The square against the
left whiskering `F ◁ f` commutes on any ringed space. -/
theorem mulSectionHom_whiskerLeft (Y : RingedSpace.{u, u})
    {F G H : SheafOfModules.{u} (structureSheafRing Y)}
    (σ : 𝟙_ (SheafOfModules.{u} (structureSheafRing Y)) ⟶ F) (f : G ⟶ H) :
    mulSectionHom Y σ ≫ (F ◁ f) = f ≫ mulSectionHom Y σ := by
  rw [mulSectionHom, mulSectionHom, Category.assoc, ← whisker_exchange, ← Category.assoc,
    ← MonoidalCategory.leftUnitor_inv_naturality, Category.assoc]

/-- **Multiplication by a global section is natural against the functoriality isomorphism of the
tensor product**, in the second argument. -/
theorem mulSectionHom_tensorSheafIso (X : Scheme.{u})
    {F G H : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (σ : 𝟙_ (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ⟶ F) (e : G ≅ H) :
    mulSectionHom X.toRingedSpace σ ≫ (tensorSheafIso X (Iso.refl F) e).hom =
      e.hom ≫ mulSectionHom X.toRingedSpace σ :=
  have hkey : (tensorSheafIso X (Iso.refl F) e).hom = F ◁ e.hom :=
    (tensorSheafIso_hom X (Iso.refl F) e).trans
      ((tensorHom_eq_tensorSheafMap X.toRingedSpace (𝟙 F) e.hom).symm.trans
        (MonoidalCategory.id_tensorHom F e.hom))
  (congrArg (fun φ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).obj (F)).obj (G)) ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).obj (F)).obj (H)) =>
      mulSectionHom X.toRingedSpace σ ≫ φ) hkey).trans
    (mulSectionHom_whiskerLeft X.toRingedSpace σ e.hom)

/-! ### The affine comparison square -/

/-- `AlgebraicGeometry.tildeTensorIso` on the canonical global section of a pure tensor, read as
a map of sections rather than through the tilde--global-sections adjunction. -/
theorem tildeTensorIso_hom_app_toOpen (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)
    (m : M) (n : N) :
    ((tildeTensorIso R M N).hom.val.app (op ⊤)).hom
        ((tilde.toOpen (M ⊗ N) ⊤).hom (TensorProduct.tmul R m n)) =
      ((toSheafify (Spec R).presheaf (isSheaf_specStructureRingPresheaf R)
          (specTensorPresheaf R (tilde M) (tilde N))).app (op ⊤)).hom
        (TensorProduct.tmul ((Spec R).presheaf.obj (op ⊤))
          ((tilde.toOpen M ⊤).hom m) ((tilde.toOpen N ⊤).hom n)) :=
  tildeTensorIso_hom_tmul R M N m n

/-- **The affine comparison square for multiplication by a global section.**  On `Spec R`,
multiplication by a global section `σ` of `M̃`, followed by the affine tensor comparison
`M̃ ⊗ Ñ ≅ (M ⊗ N)~`, is the associated sheaf of the module-theoretic multiplication
`n ↦ s ⊗ n`, where `s ∈ M` is the element whose canonical global section is the value of `σ` on
the unit section. -/
theorem mulSectionHom_tensorSheafTildeIso (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)
    (σ : 𝟙_ (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace)) ⟶ tilde M) (s : M)
    (hσ : (σ.val.app (op ⊤)).hom (unitSection (Spec R).toRingedSpace (op ⊤) 1) =
      (tilde.toOpen M ⊤).hom s) :
    mulSectionHom (Spec R).toRingedSpace σ ≫ (tensorSheafTildeIso R M N).hom =
      tilde.map (ModuleCat.ofHom (TensorProduct.mk R M N s)) := by
  refine tilde_hom_ext_toOpen fun n => ?_
  -- The value of `mulSectionHom` on the canonical global section of `N`, with `σ` evaluated.
  have h1 : ((mulSectionHom (Spec R).toRingedSpace (G := tilde N) σ).val.app (op ⊤)).hom
        ((tilde.toOpen N ⊤).hom n) =
      tensorObjTmul (Spec R).toRingedSpace (tilde M) (tilde N) (op ⊤)
        ((tilde.toOpen M ⊤).hom s) ((tilde.toOpen N ⊤).hom n) :=
    (mulSectionHom_app (Spec R).toRingedSpace (G := tilde N) σ (op ⊤)
        ((tilde.toOpen N ⊤).hom n)).trans
      (congrArg (fun z => tensorObjTmul (Spec R).toRingedSpace (tilde M) (tilde N) (op ⊤) z
        ((tilde.toOpen N ⊤).hom n)) hσ)
  -- The affine tensor comparison on that pure tensor.
  have h2 : ((tensorSheafTildeIso R M N).hom.val.app (op ⊤)).hom
        (tensorObjTmul (Spec R).toRingedSpace (tilde M) (tilde N) (op ⊤)
          ((tilde.toOpen M ⊤).hom s) ((tilde.toOpen N ⊤).hom n)) =
      (tilde.toOpen (M ⊗ N) ⊤).hom (TensorProduct.tmul R s n) :=
    (sheaf_comp_app_apply (Spec R).toRingedSpace
        (tensorSheafComparison (Spec R) (tilde M) (tilde N)).hom (tildeTensorIso R M N).inv
        (op ⊤) _).trans
      ((congrArg (fun y => ((tildeTensorIso R M N).inv.val.app (op ⊤)).hom y)
          ((tensorSheafComparison_hom_app_tmul (Spec R) (tilde M) (tilde N) (op ⊤)
              ((tilde.toOpen M ⊤).hom s) ((tilde.toOpen N ⊤).hom n)).trans
            (tildeTensorIso_hom_app_toOpen R M N s n).symm)).trans
        (iso_inv_hom_app (tildeTensorIso R M N) (op ⊤) _))
  exact ((sheaf_comp_app_apply (Spec R).toRingedSpace (mulSectionHom (Spec R).toRingedSpace σ)
      (tensorSheafTildeIso R M N).hom (op ⊤) ((tilde.toOpen N ⊤).hom n)).trans
    ((congrArg (fun y => ((tensorSheafTildeIso R M N).hom.val.app (op ⊤)).hom y) h1).trans
      h2)).trans (Stacks.AffineExteriorPower.tilde_map_app_toOpen
    (ModuleCat.ofHom (TensorProduct.mk R M N s)) ⊤ n).symm

/-- The affine comparison square, for the morphism attached to a section of `M̃` by
`SheafOfModules.unitHomEquiv`: this is the shape in which `reflexivePowerTransition` takes its
multiplication morphism. -/
theorem mulSectionHom_unitHomEquiv_symm (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)
    (t : (tilde M : (Spec R).Modules).sections) (s : M)
    (ht : t.val (op ⊤) = (tilde.toOpen M ⊤).hom s) :
    mulSectionHom (Spec R).toRingedSpace
        ((tilde M : (Spec R).Modules).unitHomEquiv.symm t) ≫
          (tensorSheafTildeIso R M N).hom =
      tilde.map (ModuleCat.ofHom (TensorProduct.mk R M N s)) :=
  mulSectionHom_tensorSheafTildeIso R M N _ s
    ((congrArg (fun u : (tilde M : (Spec R).Modules).sections => u.val (op ⊤))
      ((tilde M : (Spec R).Modules).unitHomEquiv.apply_symm_apply t)).trans ht)

end Stacks.AlgebraicGeometry.ReflexivePowers

end
