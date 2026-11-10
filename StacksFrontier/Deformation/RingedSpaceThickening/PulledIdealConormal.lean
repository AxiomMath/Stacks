module

public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionAlgebraExtensionBridge
public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangle
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceFundamentalTriangle
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalInverseImage
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness

/-!
# The pulled-back ideal of a first order thickening is a conormal sheaf

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces and `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` a
first order thickening with ideal `𝒥 = Ker(t^♯)`. On the site of opens of `X` the structure maps
form the tower

`(f ∘ t)⁻¹𝒪_{S'} --g--> f⁻¹𝒪_S --h--> 𝒪_X`

of `Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap` and the structure map of `f`. This file
proves that `g` is locally surjective, with kernel `𝒦 = (f ∘ t)⁻¹𝒥`, and that the pulled-back ideal
`f^* t^* 𝒥` is the extension of scalars along `h` of the conormal sheaf `𝒞 = 𝒦/𝒦²` of `g`, together
with the description of this identification on sections of `𝒥`. This is the input through which
the ideal of the deformation problem of Stacks 08UZ is read in the cotangent complex of the tower.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.idealToPulledKernel`: the map `𝒥 ⟶ (f ∘ t)_* 𝒦`, and
  `AlgebraicGeometry.RingedSpaceThickening.pulledIdealHom`, its transpose `(f ∘ t)⁻¹𝒥 ⟶ 𝒦`.
* `AlgebraicGeometry.RingedSpaceThickening.pulledConormal`: the conormal sheaf `𝒞` of `g`, and
  `AlgebraicGeometry.RingedSpaceThickening.pulledConormalExtended`: `𝒞 ⊗_{f⁻¹𝒪_S} 𝒪_X`.
* `AlgebraicGeometry.RingedSpaceThickening.pulledIdealConormalIso`:
  `f^* t^* 𝒥 ≅ 𝒞 ⊗_{f⁻¹𝒪_S} 𝒪_X`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.isLocallySurjective_baseStructureMap`: `g` is locally
  surjective when `t` is a thickening.
* `AlgebraicGeometry.RingedSpaceThickening.isIso_pulledIdealHom`: `(f ∘ t)⁻¹𝒥 ≅ 𝒦`.
* `AlgebraicGeometry.RingedSpaceThickening.pulledIdealConormalIso_transpose_baseIdealSection`:
  the transpose of `pulledIdealConormalIso` along `(f ∘ t)^* ⊣ (f ∘ t)_*` and `(f ∘ t)^* = f^* t^*`
  sends a section `s` of `𝒪_{S'}` with `t^♯ s = 0` to the unit of extension of scalars applied to
  the conormal class of the image of `s` in `(f ∘ t)⁻¹𝒪_{S'}`.

## Implementation notes

The identification is by Yoneda (`Stacks.Sheaves.RingedToposModules.isoOfNaturalHomEquiv`): maps
out of `𝒞 ⊗ 𝒪_X` into an `𝒪_X`-module `M` are, in turn, `f⁻¹𝒪_S`-linear maps out of `𝒞`,
`(f ∘ t)⁻¹𝒪_{S'}`-linear maps out of `𝒦` (`Stacks.Sites.Conormal.conormalHomEquivOf`: `𝒦` acts
by zero on `M`, so such a map kills `𝒦²`), `(f ∘ t)⁻¹𝒪_{S'}`-linear maps out of `(f ∘ t)⁻¹𝒥`,
`𝒪_{S'}`-linear maps `𝒥 ⟶ (f ∘ t)_* M`, and maps out of `f^* t^* 𝒥`. In particular the square-zero
condition on `𝒥` is not used: the statement holds for any thickening, and is stated for a first
order one only because that is the situation of its consumers.

The one geometric input is `isIso_pulledIdealHom`, proved on stalks: the stalk of
`(f ∘ t)⁻¹𝒥` at `x` is `𝒥_{t f x}`, and a germ of `(f ∘ t)⁻¹𝒪_{S'}` killed by `g` is the germ of a
section of `𝒪_{S'}` whose image under `t^♯` vanishes near `f x`, hence, `t` being a homeomorphism,
the germ of a section of `𝒥`.

## References

* [Stacks Project, Tag 08UZ](https://stacks.math.columbia.edu/tag/08UZ)
* [Stacks Project, Tag 08T4](https://stacks.math.columbia.edu/tag/08T4), the tower.
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), maps out of a conormal
  sheaf.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Sheaves.RingedSpaceDifferentials (sheafAdjunction structureSheafMap inverseImageSheaf)
open Stacks.Sheaves.RingedSpaceCotangent (baseStructureMap baseStructureMap_comp)
open Stacks.Sites.Conormal (kernelIdeal)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S S' : RingedSpace.{u, u}} (f : X ⟶ S) (t : S ⟶ S')

/-- `g` on unit sections: `g (η_{f∘t} s) = η_f (t^♯ s)` for a section `s` of `𝒪_{S'}`, where
`η` denotes the units of the inverse-image adjunctions. This is the defining property of
`baseStructureMap`, read on sections. -/
theorem baseStructureMap_app_unit (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) :
    ((baseStructureMap f t).hom.app (op ((Opens.map (f ≫ t).hom.base).obj V.unop))).hom
        ((((sheafAdjunction (f ≫ t)).unit.app S'.sheaf).hom.app V).hom s) =
      (((sheafAdjunction f).unit.app S.sheaf).hom.app
          (op ((Opens.map t.hom.base).obj V.unop))).hom ((t.hom.c.app V).hom s) := by
  have h : (sheafAdjunction (f ≫ t)).unit.app S'.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ t).hom.base).map (baseStructureMap f t) =
      structureSheafMap t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map
        ((sheafAdjunction f).unit.app S.sheaf) :=
    ((sheafAdjunction (f ≫ t)).homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  exact congrArg (fun k => (k.hom.app V).hom s) h

/-- The kernel `𝒦 = Ker(g)` of `g : (f ∘ t)⁻¹𝒪_{S'} ⟶ f⁻¹𝒪_S`, as a sheaf of
`(f ∘ t)⁻¹𝒪_{S'}`-modules on `X`. -/
abbrev pulledKernel : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
    (J := Opens.grothendieckTopology X.carrier) (inverseImageSheaf (f ≫ t))) :=
  Stacks.Sites.Conormal.idealSheaf.{u, u, u} (Opens.grothendieckTopology X.carrier)
    (Stacks.Sites.Conormal.presentationRingHom.{u, u, u} (Opens.grothendieckTopology X.carrier)
      (baseStructureMap f t))

/-- The ideal `𝒥 = Ker(t^♯)` of `t`, read as a sheaf of modules over the sheaf of rings
underlying `𝒪_{S'}` in the spelling of `AlgebraicGeometry.SheafOfModules.underlyingRingSheaf`, in
which the inverse image of sheaves of modules along a continuous map is stated. -/
abbrev baseIdeal :
    SheafOfModules.{u} (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf S'.sheaf) :=
  AlgebraicGeometry.SheafOfModules.idealSheaf t

/-- The section of `𝒦` given by a section of `(f ∘ t)⁻¹𝒪_{S'}` killed by `g`. -/
def pulledKernelSection (W : (Opens X.carrier)ᵒᵖ) (a : (inverseImageSheaf (f ≫ t)).obj.obj W)
    (ha : ((baseStructureMap f t).hom.app W).hom a = 0) : (pulledKernel f t).val.obj W :=
  ⟨a, ha⟩

/-- The underlying section of `pulledKernelSection f t W a ha` in `(f ∘ t)⁻¹𝒪_{S'}` is `a`. -/
theorem pulledKernelSection_val (W : (Opens X.carrier)ᵒᵖ)
    (a : (inverseImageSheaf (f ≫ t)).obj.obj W)
    (ha : ((baseStructureMap f t).hom.app W).hom a = 0) :
    (pulledKernelSection f t W a ha).1 = a := rfl

/-- A section of `𝒪_{S'}` killed by the ideal-sheaf inclusion's target map: the sections of
`𝒥 = Ker(t^♯)`, read in `𝒪_{S'}`, are killed by `t^♯`. -/
theorem app_idealSheafι_eq_zero (V : (Opens S'.carrier)ᵒᵖ)
    (y : (AlgebraicGeometry.SheafOfModules.idealSheaf t).val.obj V) :
    (t.hom.c.app V).hom ((Stacks.ClosedImmersion.idealSheafι t).val.app V y) = 0 := by
  have h := congrArg (fun k => k.val.app V y)
    (kernel.condition (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom t)))
  exact h

/-- The unit section of a section of `𝒥` is killed by `g`. -/
theorem baseStructureMap_unit_idealSheafι (V : (Opens S'.carrier)ᵒᵖ)
    (y : (AlgebraicGeometry.SheafOfModules.idealSheaf t).val.obj V) :
    ((baseStructureMap f t).hom.app (op ((Opens.map (f ≫ t).hom.base).obj V.unop))).hom
        (AlgebraicGeometry.SheafOfModules.inverseImageRingUnitApp (f ≫ t).hom.base S'.sheaf V
          ((Stacks.ClosedImmersion.idealSheafι t).val.app V y)) = 0 := by
  refine (baseStructureMap_app_unit f t V _).trans ?_
  refine (congrArg _ (app_idealSheafι_eq_zero t V y)).trans ?_
  exact map_zero _

/-- **The map `𝒥 ⟶ (f ∘ t)_* 𝒦`**: a section `y` of `𝒥` goes to the image of `y` in
`(f ∘ t)⁻¹𝒪_{S'}` under the unit of `(f ∘ t)⁻¹ ⊣ (f ∘ t)_*`, which `g` kills. -/
def idealToPulledKernel :
    baseIdeal t ⟶
      (SheafOfModules.pushforward.{u}
        (AlgebraicGeometry.SheafOfModules.inverseImageRingHom (f ≫ t).hom.base S'.sheaf)).obj
        (pulledKernel f t) where
  val :=
    { app := fun V => ModuleCat.ofHom
        (X := (baseIdeal t).val.obj V)
        (Y := ((SheafOfModules.pushforward.{u}
          (AlgebraicGeometry.SheafOfModules.inverseImageRingHom (f ≫ t).hom.base S'.sheaf)).obj
            (pulledKernel f t)).val.obj V)
        { toFun := fun y => pulledKernelSection f t _
            (AlgebraicGeometry.SheafOfModules.inverseImageRingUnitApp (f ≫ t).hom.base S'.sheaf V
              ((Stacks.ClosedImmersion.idealSheafι t).val.app V y))
            (baseStructureMap_unit_idealSheafι f t V y)
          map_add' := fun y y' => Subtype.ext ((congrArg
              (AlgebraicGeometry.SheafOfModules.inverseImageRingUnitApp (f ≫ t).hom.base S'.sheaf V)
              (map_add ((Stacks.ClosedImmersion.idealSheafι t).val.app V).hom y y')).trans
            (map_add _ _ _))
          map_smul' := fun r y => Subtype.ext ((congrArg
              (AlgebraicGeometry.SheafOfModules.inverseImageRingUnitApp (f ≫ t).hom.base S'.sheaf V)
              (((Stacks.ClosedImmersion.idealSheafι t).val.app V).hom.map_smul r y)).trans
            (map_mul _ _ _)) }
      naturality := fun {_V V'} i => ModuleCat.hom_ext (LinearMap.ext fun y => Subtype.ext
        ((congrArg
            (AlgebraicGeometry.SheafOfModules.inverseImageRingUnitApp (f ≫ t).hom.base S'.sheaf V')
            (PresheafOfModules.naturality_apply (Stacks.ClosedImmersion.idealSheafι t).val i
              y)).trans
          (NatTrans.naturality_apply
            ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
              (f ≫ t).hom.base).unit.app S'.sheaf).hom i _))) }

/-- **The comparison `(f ∘ t)⁻¹𝒥 ⟶ 𝒦`**, the transpose of `idealToPulledKernel`. -/
def pulledIdealHom :
    (SheafOfModules.pullback.{u}
        (AlgebraicGeometry.SheafOfModules.inverseImageRingHom (f ≫ t).hom.base S'.sheaf)).obj
        (baseIdeal t) ⟶ pulledKernel f t :=
  ((AlgebraicGeometry.SheafOfModules.inverseImageAdjunction (f ≫ t).hom.base S'.sheaf).homEquiv
    _ _).symm (idealToPulledKernel f t)

/-! ### Germs -/

section Germs

/-- Two successive restrictions of a section of a presheaf of commutative rings are one
restriction. -/
theorem presheaf_map_map {Y : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{u} Y)
    {U V W : Opens Y} (i : V ⟶ U) (j : W ⟶ V) (k : W ⟶ U) (s : F.obj (op U)) :
    (F.map j.op).hom ((F.map i.op).hom s) = (F.map k.op).hom s := by
  rw [show k = j ≫ i from rfl, op_comp, F.map_comp]
  rfl

/-- The underlying homeomorphism of a thickening carries open neighbourhoods to open
neighbourhoods: every open neighbourhood `U` of a point `x` of `S` contains the preimage of an
open neighbourhood of `t x`. -/
theorem exists_preimage_le (ht : IsIso t.hom.base) (U : Opens S.carrier) (x : S.carrier)
    (hx : x ∈ U) :
    ∃ V : Opens S'.carrier, t.hom.base x ∈ V ∧ (Opens.map t.hom.base).obj V ≤ U := by
  have e := (TopCat.isIso_iff_isHomeomorph t.hom.base).mp ht
  refine ⟨⟨t.hom.base '' U, e.isOpenMap _ U.2⟩, ⟨x, hx, rfl⟩, ?_⟩
  rintro z ⟨w, hw, hwz⟩
  exact e.injective hwz ▸ hw

/-- The germ at `y` of the unit section of a section `b` of a sheaf of commutative rings `O`
on `Z` along `φ : Y ⟶ Z` vanishes only if the germ of `b` at `φ y` does. -/
theorem germ_eq_zero_of_germ_unit_eq_zero {Y Z : TopCat.{u}} (φ : Y ⟶ Z)
    (O : TopCat.Sheaf CommRingCat.{u} Z) (y : Y) (V : Opens Z) (hV : φ y ∈ V)
    (b : O.obj.obj (op V))
    (h : (((TopCat.Sheaf.pullback CommRingCat.{u} φ).obj O).presheaf.germ
        ((Opens.map φ).obj V) y hV).hom
        (AlgebraicGeometry.SheafOfModules.inverseImageRingUnitApp φ O (op V) b) = 0) :
    (O.presheaf.germ V (φ y) hV).hom b = 0 := by
  have h' := (Stacks.InverseImageStalk.ringStalkEquiv_germ φ O y V hV b).trans h
  exact (map_eq_zero_iff _ (Stacks.InverseImageStalk.ringStalkEquiv _ _ _).injective).1 h'

end Germs

section LocallySurjective

variable {t}

/-- **The reduction `g : (f ∘ t)⁻¹𝒪_{S'} ⟶ f⁻¹𝒪_S` is surjective on stalks** when `t` is a
thickening. -/
theorem surjective_stalk_baseStructureMap (ht : IsThickening t) (x : X.carrier) :
    Function.Surjective
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map (baseStructureMap f t).hom) := by
  intro w
  obtain ⟨z, rfl⟩ := (Stacks.InverseImageStalk.ringStalkEquiv f.hom.base S.sheaf x).surjective w
  obtain ⟨U, hU, d, rfl⟩ := S.sheaf.presheaf.exists_germ_eq z
  obtain ⟨V₂, hV₂, hle⟩ := exists_preimage_le t ht.1 U (f.hom.base x) hU
  have hloc := (TopCat.Presheaf.isLocallySurjective_iff _).1
    (isLocallySurjective_of_isThickening t ht) V₂
    ((S.sheaf.presheaf.map (homOfLE hle).op).hom d) (t.hom.base (f.hom.base x)) hV₂
  obtain ⟨V₃, hV₃le, ⟨b, hb⟩, hpV₃⟩ := hloc
  have hb' : (t.hom.c.app (op V₃)).hom b =
      (S.sheaf.presheaf.map (homOfLE (((Opens.map t.hom.base).monotone hV₃le).trans hle)).op).hom
        d := by
    refine hb.trans ?_
    exact presheaf_map_map S.sheaf.presheaf (homOfLE hle)
      ((Opens.map t.hom.base).map (homOfLE hV₃le)) _ d
  refine ⟨(((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ t).hom.base).obj S'.sheaf).presheaf.germ
      ((Opens.map (f ≫ t).hom.base).obj V₃) x hpV₃).hom
      (AlgebraicGeometry.SheafOfModules.inverseImageRingUnitApp (f ≫ t).hom.base S'.sheaf
        (op V₃) b), ?_⟩
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply _ x hpV₃ _ _).trans ?_
  refine (congrArg (((inverseImageSheaf f).presheaf.germ
      ((Opens.map (f ≫ t).hom.base).obj V₃) x hpV₃).hom)
    (baseStructureMap_app_unit f t (op V₃) b)).trans ?_
  refine (Stacks.InverseImageStalk.ringStalkEquiv_germ f.hom.base S.sheaf x
    ((Opens.map t.hom.base).obj V₃) hpV₃ _).symm.trans ?_
  refine congrArg (Stacks.InverseImageStalk.ringStalkEquiv f.hom.base S.sheaf x) ?_
  refine (congrArg (S.sheaf.presheaf.germ ((Opens.map t.hom.base).obj V₃) (f.hom.base x)
    hpV₃).hom hb').trans ?_
  exact TopCat.Presheaf.germ_res_apply S.sheaf.presheaf _ (f.hom.base x) hpV₃ d

/-- **The reduction `g : (f ∘ t)⁻¹𝒪_{S'} ⟶ f⁻¹𝒪_S` is locally surjective** when `t` is a
thickening. -/
theorem isLocallySurjective_baseStructureMap (ht : IsThickening t) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (baseStructureMap f t).hom :=
  (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks (baseStructureMap f t).hom).2
    (surjective_stalk_baseStructureMap f ht)

end LocallySurjective

/-! ### `(f ∘ t)⁻¹𝒥 ⟶ 𝒦` is an isomorphism -/

section PulledIdealIso

/-- Restriction of a section of `𝒦` is restriction in `(f ∘ t)⁻¹𝒪_{S'}`. -/
theorem pulledKernel_map_val {W W' : (Opens X.carrier)ᵒᵖ} (i : W ⟶ W')
    (k : (pulledKernel f t).val.obj W) :
    ((pulledKernel f t).val.map i k).1 = ((inverseImageSheaf (f ≫ t)).obj.map i).hom k.1 := rfl

/-- `idealToPulledKernel` on sections. -/
theorem idealToPulledKernel_app_val (V : (Opens S'.carrier)ᵒᵖ) (y : (baseIdeal t).val.obj V) :
    ((idealToPulledKernel f t).val.app V y).1 =
      AlgebraicGeometry.SheafOfModules.inverseImageRingUnitApp (f ≫ t).hom.base S'.sheaf V
        ((Stacks.ClosedImmersion.idealSheafι t).val.app V y) := rfl

/-- **`(f ∘ t)⁻¹𝒥 ⟶ 𝒦` on stalks**: the germ at `f (t x)` of a section `y` of `𝒥` goes to the
germ at `x` of its unit section. -/
theorem stalkMap_pulledIdealHom_germ (x : X.carrier) (V : Opens S'.carrier)
    (hV : (f ≫ t).hom.base x ∈ V) (y : (baseIdeal t).val.obj (op V)) :
    (AlgebraicGeometry.SheafOfModules.stalkMap _ x (pulledIdealHom f t)).hom
        (Stacks.InverseImageStalk.inverseImageModuleStalkEquiv (f ≫ t).hom.base S'.sheaf x
          (baseIdeal t) ((TopCat.Presheaf.germ (baseIdeal t).val.presheaf V
            ((f ≫ t).hom.base x) hV).hom y)) =
      (TopCat.Presheaf.germ (pulledKernel f t).val.presheaf
        ((Opens.map (f ≫ t).hom.base).obj V) x hV).hom
        ((idealToPulledKernel f t).val.app (op V) y) := by
  refine (congrArg (AlgebraicGeometry.SheafOfModules.stalkMap _ x (pulledIdealHom f t)).hom
    (Stacks.InverseImageStalk.inverseImageModuleStalkEquiv_germ (f ≫ t).hom.base S'.sheaf x
      (baseIdeal t) V hV y)).trans ?_
  refine (AlgebraicGeometry.SheafOfModules.stalkMap_germ _ x _ _ hV _).trans ?_
  exact congrArg (TopCat.Presheaf.germ (pulledKernel f t).val.presheaf
      ((Opens.map (f ≫ t).hom.base).obj V) x hV).hom
    (Stacks.SheafOfModules.inverseImageAdjunction_homEquiv_symm_val_app_unit (f ≫ t).hom.base
      S'.sheaf (idealToPulledKernel f t) (op V) y)

/-- `(f ∘ t)⁻¹𝒥 ⟶ 𝒦` is injective on stalks. -/
theorem injective_stalkMap_pulledIdealHom (x : X.carrier) :
    Function.Injective
      (AlgebraicGeometry.SheafOfModules.stalkMap _ x (pulledIdealHom f t)).hom := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  obtain ⟨w, rfl⟩ := (Stacks.InverseImageStalk.inverseImageModuleStalkEquiv (f ≫ t).hom.base
    S'.sheaf x (baseIdeal t)).surjective z
  obtain ⟨V, hV, y, rfl⟩ := TopCat.Presheaf.exists_germ_eq (X := S'.carrier)
    (C := AddCommGrpCat.{u}) (baseIdeal t).val.presheaf w
  replace hz := (stalkMap_pulledIdealHom_germ f t x V hV y).symm.trans hz
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq (X := X.carrier)
    (C := AddCommGrpCat.{u}) (U := (Opens.map (f ≫ t).hom.base).obj V)
    (V := (Opens.map (f ≫ t).hom.base).obj V) (pulledKernel f t).val.presheaf x hV hV _ 0
    (hz.trans (map_zero _).symm)
  have hW' : ((inverseImageSheaf (f ≫ t)).obj.map iU.op).hom
      (AlgebraicGeometry.SheafOfModules.inverseImageRingUnitApp (f ≫ t).hom.base S'.sheaf (op V)
        ((Stacks.ClosedImmersion.idealSheafι t).val.app (op V) y)) = 0 :=
    (congrArg Subtype.val hW).trans (congrArg Subtype.val (map_zero _))
  have hg : (((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ t).hom.base).obj S'.sheaf).presheaf.germ
      ((Opens.map (f ≫ t).hom.base).obj V) x hV).hom
      (AlgebraicGeometry.SheafOfModules.inverseImageRingUnitApp (f ≫ t).hom.base S'.sheaf (op V)
        ((Stacks.ClosedImmersion.idealSheafι t).val.app (op V) y)) = 0 := by
    rw [← TopCat.Presheaf.germ_res_apply _ iU x hxW, hW', map_zero]
  have hs := germ_eq_zero_of_germ_unit_eq_zero (f ≫ t).hom.base S'.sheaf x V hV _ hg
  obtain ⟨V', j₁, hxV', hV'⟩ := S'.exists_res_eq_zero_of_germ_eq_zero V _ ⟨_, hV⟩ hs
  have hy : (baseIdeal t).val.map j₁.op y = 0 := by
    refine Stacks.ClosedImmersion.injective_idealSheafι_val_app t V' ?_
    refine (PresheafOfModules.naturality_apply (Stacks.ClosedImmersion.idealSheafι t).val j₁.op
      y).trans ?_
    exact hV'.trans (map_zero _).symm
  have hgy : (TopCat.Presheaf.germ (baseIdeal t).val.presheaf V ((f ≫ t).hom.base x) hV).hom y
      = 0 := by
    rw [← TopCat.Presheaf.germ_res_apply _ j₁ _ hxV']
    exact (congrArg _ hy).trans (map_zero _)
  exact (congrArg _ hgy).trans (map_zero _)

variable {t} in
/-- `(f ∘ t)⁻¹𝒥 ⟶ 𝒦` is surjective on stalks when `t` is a thickening. -/
theorem surjective_stalkMap_pulledIdealHom (ht : IsThickening t) (x : X.carrier) :
    Function.Surjective
      (AlgebraicGeometry.SheafOfModules.stalkMap _ x (pulledIdealHom f t)).hom := by
  intro k
  obtain ⟨W, hW, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (X := X.carrier)
    (C := AddCommGrpCat.{u}) (pulledKernel f t).val.presheaf k
  let a₁ : (inverseImageSheaf (f ≫ t)).obj.obj (op W) :=
    (a : (pulledKernel f t).val.obj (op W)).1
  have ha : ((baseStructureMap f t).hom.app (op W)).hom a₁ = 0 :=
    (a : (pulledKernel f t).val.obj (op W)).2
  obtain ⟨z, hz⟩ := (Stacks.InverseImageStalk.ringStalkEquiv (f ≫ t).hom.base S'.sheaf x).surjective
    (((inverseImageSheaf (f ≫ t)).presheaf.germ W x hW).hom a₁)
  obtain ⟨V, hV, b, rfl⟩ := S'.sheaf.presheaf.exists_germ_eq z
  obtain ⟨W₁, hxW₁, i₁, i₂, he⟩ := (inverseImageSheaf (f ≫ t)).presheaf.germ_eq x hV hW _ _
    ((Stacks.InverseImageStalk.ringStalkEquiv_germ (f ≫ t).hom.base S'.sheaf x V hV
      b).symm.trans hz)
  have hg1 : ((baseStructureMap f t).hom.app (op W₁)).hom
      (((inverseImageSheaf (f ≫ t)).presheaf.map i₁.op).hom
        (AlgebraicGeometry.SheafOfModules.inverseImageRingUnitApp (f ≫ t).hom.base S'.sheaf
          (op V) b)) = 0 := by
    refine (congrArg _ he).trans ?_
    refine (NatTrans.naturality_apply (baseStructureMap f t).hom i₂.op a₁).trans ?_
    exact (congrArg _ ha).trans (map_zero _)
  have hg2 : ((inverseImageSheaf f).presheaf.germ ((Opens.map (f ≫ t).hom.base).obj V) x hV).hom
      (((baseStructureMap f t).hom.app (op ((Opens.map (f ≫ t).hom.base).obj V))).hom
        (AlgebraicGeometry.SheafOfModules.inverseImageRingUnitApp (f ≫ t).hom.base S'.sheaf
          (op V) b)) = 0 := by
    rw [← TopCat.Presheaf.germ_res_apply _ i₁ x hxW₁]
    refine (congrArg _ (NatTrans.naturality_apply (baseStructureMap f t).hom i₁.op _).symm).trans ?_
    exact (congrArg _ hg1).trans (map_zero _)
  have hg3 : ((inverseImageSheaf f).presheaf.germ
      ((Opens.map f.hom.base).obj ((Opens.map t.hom.base).obj V)) x hV).hom
      (AlgebraicGeometry.SheafOfModules.inverseImageRingUnitApp f.hom.base S.sheaf
        (op ((Opens.map t.hom.base).obj V)) ((t.hom.c.app (op V)).hom b)) = 0 :=
    (congrArg _ (baseStructureMap_app_unit f t (op V) b)).symm.trans hg2
  have hs := germ_eq_zero_of_germ_unit_eq_zero f.hom.base S.sheaf x
    ((Opens.map t.hom.base).obj V) hV _ hg3
  obtain ⟨U, k₁, hxU, hU⟩ := S.exists_res_eq_zero_of_germ_eq_zero _ _ ⟨_, hV⟩ hs
  obtain ⟨V₂, hV₂, hle⟩ := exists_preimage_le t ht.1 U (f.hom.base x) hxU
  have hpV₁ : (f ≫ t).hom.base x ∈ V ⊓ V₂ := ⟨hV, hV₂⟩
  have hle' : (Opens.map t.hom.base).obj (V ⊓ V₂) ≤ U :=
    ((Opens.map t.hom.base).monotone inf_le_right).trans hle
  let b₁ := (S'.sheaf.presheaf.map (homOfLE inf_le_left : V ⊓ V₂ ⟶ V).op).hom b
  have hb₁ : (t.hom.c.app (op (V ⊓ V₂))).hom b₁ = 0 := by
    refine (NatTrans.naturality_apply t.hom.c (homOfLE inf_le_left : V ⊓ V₂ ⟶ V).op b).trans ?_
    refine (presheaf_map_map S.sheaf.presheaf k₁ (homOfLE hle') _ _).symm.trans ?_
    exact (congrArg _ hU).trans (map_zero _)
  let y := baseIdealSection t (op (V ⊓ V₂)) b₁ hb₁
  have hy : (Stacks.ClosedImmersion.idealSheafι t).val.app (op (V ⊓ V₂)) y = b₁ :=
    idealSheafι_baseIdealSection t (op (V ⊓ V₂)) b₁ hb₁
  refine ⟨Stacks.InverseImageStalk.inverseImageModuleStalkEquiv (f ≫ t).hom.base S'.sheaf x
    (baseIdeal t) ((TopCat.Presheaf.germ (baseIdeal t).val.presheaf (V ⊓ V₂)
      ((f ≫ t).hom.base x) hpV₁).hom y), ?_⟩
  refine (stalkMap_pulledIdealHom_germ f t x (V ⊓ V₂) hpV₁ y).trans ?_
  refine TopCat.Presheaf.germ_ext (C := AddCommGrpCat.{u}) (pulledKernel f t).val.presheaf
    (W₁ ⊓ (Opens.map (f ≫ t).hom.base).obj (V ⊓ V₂)) ⟨hxW₁, hpV₁⟩ (homOfLE inf_le_right)
    (homOfLE (inf_le_left.trans i₂.le)) ?_
  refine Subtype.ext ?_
  change ((inverseImageSheaf (f ≫ t)).presheaf.map (homOfLE inf_le_right :
      W₁ ⊓ (Opens.map (f ≫ t).hom.base).obj (V ⊓ V₂) ⟶
        (Opens.map (f ≫ t).hom.base).obj (V ⊓ V₂)).op).hom
      (AlgebraicGeometry.SheafOfModules.inverseImageRingUnitApp (f ≫ t).hom.base S'.sheaf
        (op (V ⊓ V₂)) ((Stacks.ClosedImmersion.idealSheafι t).val.app (op (V ⊓ V₂)) y)) =
    ((inverseImageSheaf (f ≫ t)).presheaf.map (homOfLE (inf_le_left.trans i₂.le) :
      W₁ ⊓ (Opens.map (f ≫ t).hom.base).obj (V ⊓ V₂) ⟶ W).op).hom a₁
  rw [hy]
  refine (congrArg _ (NatTrans.naturality_apply
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (f ≫ t).hom.base).unit.app S'.sheaf).hom (homOfLE inf_le_left : V ⊓ V₂ ⟶ V).op b)).trans ?_
  refine (presheaf_map_map _ _ _ (homOfLE (inf_le_left.trans i₁.le)) _).trans ?_
  refine (presheaf_map_map _ i₁ (homOfLE inf_le_left) _ _).symm.trans ?_
  refine (congrArg _ he).trans ?_
  exact presheaf_map_map _ i₂ (homOfLE inf_le_left) _ _

variable {t} in
/-- **The inverse image of the ideal is the kernel of the reduction**: `(f ∘ t)⁻¹𝒥 ⟶ 𝒦` is an
isomorphism when `t` is a thickening. -/
theorem isIso_pulledIdealHom (ht : IsThickening t) : IsIso (pulledIdealHom f t) :=
  (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap (pulledIdealHom f t)).2
    fun x => ⟨injective_stalkMap_pulledIdealHom f t x, surjective_stalkMap_pulledIdealHom f ht x⟩

end PulledIdealIso

/-! ### The two direct images -/

section DirectImage

/-- The structure map of `f ∘ t` factors through the tower: on sections, `h (g (η r))` is
`(f ∘ t)^♯ r`, where `η` is the unit of `(f ∘ t)⁻¹ ⊣ (f ∘ t)_*`. -/
theorem inverseImageStructureMap_baseStructureMap_unit (V : (Opens S'.carrier)ᵒᵖ)
    (r : S'.presheaf.obj V) :
    ((Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f).hom.app
        (op ((Opens.map (f ≫ t).hom.base).obj V.unop))).hom
        (((baseStructureMap f t).hom.app (op ((Opens.map (f ≫ t).hom.base).obj V.unop))).hom
          (AlgebraicGeometry.SheafOfModules.inverseImageRingUnitApp (f ≫ t).hom.base S'.sheaf
            V r)) =
      ((f ≫ t).hom.c.app V).hom r := by
  have h := Stacks.Sheaves.RingedSpaceDifferentials.homEquiv_inverseImageStructureMap (f ≫ t)
  rw [Adjunction.homEquiv_unit, ← baseStructureMap_comp] at h
  exact congrArg (fun k => (k.hom.app V).hom r) h

/-- `(f ∘ t)_* M`, read as a sheaf of modules over the sheaf of rings underlying `𝒪_{S'}` in the
spelling of `AlgebraicGeometry.SheafOfModules.underlyingRingSheaf`. -/
def pushforwardOnBase (M : SheafOfModules.{u} (structureSheafRing X)) :
    SheafOfModules.{u} (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf S'.sheaf) :=
  (modulePushforward (f ≫ t)).obj M

/-- A sheaf of `𝒪_X`-modules, read as a sheaf of `(f ∘ t)⁻¹𝒪_{S'}`-modules along `h ∘ g` and
pushed forward along the inverse image adjunction, is `(f ∘ t)_*` of it: the two have the same
sections, and the two actions of `𝒪_{S'}` agree by
`inverseImageStructureMap_baseStructureMap_unit`. -/
def pushforwardRestrictIso (M : SheafOfModules.{u} (structureSheafRing X)) :
    @Iso (SheafOfModules.{u} (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf S'.sheaf)) _
    ((SheafOfModules.pushforward.{u}
        (AlgebraicGeometry.SheafOfModules.inverseImageRingHom (f ≫ t).hom.base S'.sheaf)).obj
        ((SheafOfModules.restrictScalars
          (Stacks.Sites.Conormal.presentationRingHom.{u, u, u}
            (Opens.grothendieckTopology X.carrier) (baseStructureMap f t))).obj
          ((CategoryTheory.Sheaf.squareRestrict.{u, u, u} (Opens.grothendieckTopology X.carrier)
            (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)).obj M)))
      (pushforwardOnBase f t M) where
  hom :=
    { val :=
        { app := fun V => ModuleCat.ofHom
            (X := ((SheafOfModules.pushforward.{u}
              (AlgebraicGeometry.SheafOfModules.inverseImageRingHom (f ≫ t).hom.base
                S'.sheaf)).obj
              ((SheafOfModules.restrictScalars
                (Stacks.Sites.Conormal.presentationRingHom.{u, u, u}
                  (Opens.grothendieckTopology X.carrier) (baseStructureMap f t))).obj
                ((CategoryTheory.Sheaf.squareRestrict.{u, u, u}
                  (Opens.grothendieckTopology X.carrier)
                  (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)).obj
                    M))).val.obj V)
            (Y := (pushforwardOnBase f t M).val.obj V)
            { toFun := fun m => m
              map_add' := fun _ _ => rfl
              map_smul' := fun r m =>
                congrArg (fun z : (structureSheafRing X).obj.obj
                  (op ((Opens.map (f ≫ t).hom.base).obj V.unop)) =>
                    z • (@id (M.val.obj (op ((Opens.map (f ≫ t).hom.base).obj
                  V.unop))) m))
                  (inverseImageStructureMap_baseStructureMap_unit f t V r) }
          naturality := fun _ => rfl } }
  inv :=
    { val :=
        { app := fun V => ModuleCat.ofHom
            (R := (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf S'.sheaf).obj.obj V)
            (X := (pushforwardOnBase f t M).val.obj V)
            (Y := ((SheafOfModules.pushforward.{u}
              (AlgebraicGeometry.SheafOfModules.inverseImageRingHom (f ≫ t).hom.base
                S'.sheaf)).obj
              ((SheafOfModules.restrictScalars
                (Stacks.Sites.Conormal.presentationRingHom.{u, u, u}
                  (Opens.grothendieckTopology X.carrier) (baseStructureMap f t))).obj
                ((CategoryTheory.Sheaf.squareRestrict.{u, u, u}
                  (Opens.grothendieckTopology X.carrier)
                  (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)).obj
                    M))).val.obj V)
            { toFun := fun m => m
              map_add' := fun _ _ => rfl
              map_smul' := fun r m =>
                (congrArg (fun z : (structureSheafRing X).obj.obj
                  (op ((Opens.map (f ≫ t).hom.base).obj V.unop)) =>
                    z • (@id (M.val.obj (op ((Opens.map (f ≫ t).hom.base).obj
                  V.unop))) m))
                  (inverseImageStructureMap_baseStructureMap_unit f t V r)).symm }
          naturality := fun _ => rfl } }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- `pushforwardRestrictIso` is natural. -/
theorem pushforwardRestrictIso_hom_naturality {M M' : SheafOfModules.{u} (structureSheafRing X)}
    (γ : M ⟶ M') :
    (SheafOfModules.pushforward.{u}
        (AlgebraicGeometry.SheafOfModules.inverseImageRingHom (f ≫ t).hom.base S'.sheaf)).map
        ((SheafOfModules.restrictScalars
          (Stacks.Sites.Conormal.presentationRingHom.{u, u, u}
            (Opens.grothendieckTopology X.carrier) (baseStructureMap f t))).map
          ((CategoryTheory.Sheaf.squareRestrict.{u, u, u} (Opens.grothendieckTopology X.carrier)
            (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)).map γ)) ≫
        (pushforwardRestrictIso f t M').hom =
      (pushforwardRestrictIso f t M).hom ≫ (modulePushforward (f ≫ t)).map γ :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ =>
    ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

end DirectImage

/-! ### The isomorphism -/

section Iso

variable {t}

/-- **The conormal sheaf `𝒞 = 𝒦/𝒦²` of the reduction `g : (f ∘ t)⁻¹𝒪_{S'} ⟶ f⁻¹𝒪_S`**, a sheaf
of `f⁻¹𝒪_S`-modules on `X`. The reduction is locally surjective because `t` is a thickening
(`isLocallySurjective_baseStructureMap`). -/
abbrev pulledConormal (ht : IsFirstOrderThickening t) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
      (J := Opens.grothendieckTopology X.carrier) (inverseImageSheaf f)) :=
  haveI := isLocallySurjective_baseStructureMap f ht.1
  Stacks.Sites.Conormal.conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
    (inverseImageSheaf (f ≫ t)) (inverseImageSheaf f) (baseStructureMap f t)

/-- The extension of scalars `𝒞 ⊗_{f⁻¹𝒪_S} 𝒪_X` of the conormal sheaf of the reduction along
`f⁻¹𝒪_S ⟶ 𝒪_X`. -/
abbrev pulledConormalExtended (ht : IsFirstOrderThickening t) :
    SheafOfModules.{u} (structureSheafRing X) :=
  (CategoryTheory.Sheaf.towerExtendScalars.{u, u, u} (Opens.grothendieckTopology X.carrier)
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)).obj
    (pulledConormal f ht)

/-- Maps out of `𝒞 ⊗_{f⁻¹𝒪_S} 𝒪_X` are maps out of `f^* t^* 𝒥`: the chain of identifications
`Hom(𝒞 ⊗ 𝒪_X, M) = Hom_{f⁻¹𝒪_S}(𝒞, M) = Hom_{(f∘t)⁻¹𝒪_{S'}}(𝒦, M)
= Hom_{(f∘t)⁻¹𝒪_{S'}}((f ∘ t)⁻¹𝒥, M) = Hom_{𝒪_{S'}}(𝒥, (f ∘ t)_* M) = Hom(f^* t^* 𝒥, M)`. -/
def pulledIdealConormalHomEquiv (ht : IsFirstOrderThickening t)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (pulledConormalExtended f ht ⟶ M) ≃
      ((modulePullback f).obj
        ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ M) :=
  haveI := isLocallySurjective_baseStructureMap f ht.1
  haveI := isIso_pulledIdealHom f ht.1
  ((((((CategoryTheory.Sheaf.towerExtendRestrictAdjunction.{u, u, u}
      (Opens.grothendieckTopology X.carrier)
      (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)).homEquiv
        (pulledConormal f ht) M).trans
    (Stacks.Sites.Conormal.conormalHomEquivOf.{u, u, u} (Opens.grothendieckTopology X.carrier)
      (baseStructureMap f t) _ rfl _)).trans
    (asIso (pulledIdealHom f t)).symm.homFromEquiv).trans
    ((AlgebraicGeometry.SheafOfModules.inverseImageAdjunction (f ≫ t).hom.base
      S'.sheaf).homEquiv _ _)).trans
    (pushforwardRestrictIso f t M).homToEquiv).trans
    (((modulePullbackPushforwardAdjunction (f ≫ t)).homEquiv
      (AlgebraicGeometry.SheafOfModules.idealSheaf t) M).symm.trans
    ((modulePullbackCompUniq f t).app (AlgebraicGeometry.SheafOfModules.idealSheaf t)).homFromEquiv)

/-- `pulledIdealConormalHomEquiv`, unfolded. -/
theorem pulledIdealConormalHomEquiv_apply (ht : IsFirstOrderThickening t)
    (M : SheafOfModules.{u} (structureSheafRing X)) (a : pulledConormalExtended f ht ⟶ M) :
    haveI := isLocallySurjective_baseStructureMap f ht.1
    pulledIdealConormalHomEquiv f ht M a =
      (modulePullbackCompUniq f t).inv.app (AlgebraicGeometry.SheafOfModules.idealSheaf t) ≫
        ((modulePullbackPushforwardAdjunction (f ≫ t)).homEquiv
          (AlgebraicGeometry.SheafOfModules.idealSheaf t) M).symm
          (((AlgebraicGeometry.SheafOfModules.inverseImageAdjunction (f ≫ t).hom.base
              S'.sheaf).homEquiv _ _
            (pulledIdealHom f t ≫
              Stacks.Sites.Conormal.conormalHomEquivOf.{u, u, u}
                (Opens.grothendieckTopology X.carrier) (baseStructureMap f t) _ rfl _
                ((CategoryTheory.Sheaf.towerExtendRestrictAdjunction.{u, u, u}
                  (Opens.grothendieckTopology X.carrier)
                  (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)).homEquiv
                    (pulledConormal f ht) M a))) ≫
            (pushforwardRestrictIso f t M).hom) :=
  rfl

/-- The identification `pulledIdealConormalHomEquiv` is natural in the target. -/
theorem naturalHomEquiv_pulledIdealConormalHomEquiv (ht : IsFirstOrderThickening t) :
    Stacks.Sheaves.RingedToposModules.NaturalHomEquiv (pulledIdealConormalHomEquiv f ht) := by
  intro Z Z' a γ
  have := isLocallySurjective_baseStructureMap f ht.1
  refine (pulledIdealConormalHomEquiv_apply f ht Z' (a ≫ γ)).trans ?_
  refine Eq.trans ?_ (congrArg (· ≫ γ) (pulledIdealConormalHomEquiv_apply f ht Z a)).symm
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg ((modulePullbackCompUniq f t).inv.app
    (AlgebraicGeometry.SheafOfModules.idealSheaf t) ≫ ·) ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_naturality_right_symm _ _ γ)
  refine congrArg ((modulePullbackPushforwardAdjunction (f ≫ t)).homEquiv
    (AlgebraicGeometry.SheafOfModules.idealSheaf t) Z').symm ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun k => _ ≫ k) (pushforwardRestrictIso_hom_naturality f t γ))
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine congrArg (· ≫ (pushforwardRestrictIso f t Z').hom) ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_naturality_right _ _ _)
  refine congrArg ((AlgebraicGeometry.SheafOfModules.inverseImageAdjunction (f ≫ t).hom.base
    S'.sheaf).homEquiv _ _) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (pulledIdealHom f t ≫ ·) ?_
  exact (congrArg (Stacks.Sites.Conormal.conormalHomEquivOf.{u, u, u}
      (Opens.grothendieckTopology X.carrier) (baseStructureMap f t) _ rfl _)
      (Adjunction.homEquiv_naturality_right _ a γ)).trans
    (Stacks.Sites.Conormal.conormalHomEquivOf_comp _ _ _ rfl _ _ _ _)

/-- **The pulled-back ideal of a first order thickening is the conormal sheaf of the inverse-image
surjection.** For morphisms of ringed spaces `f : X ⟶ S` and a first order thickening
`t : S ⟶ S'` with ideal `𝒥`, `f^* t^* 𝒥` is `𝒞 ⊗_{f⁻¹𝒪_S} 𝒪_X`, where `𝒞` is the conormal sheaf of
the reduction `(f ∘ t)⁻¹𝒪_{S'} ⟶ f⁻¹𝒪_S`. -/
def pulledIdealConormalIso (ht : IsFirstOrderThickening t) :
    (modulePullback f).obj ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t))
      ≅ pulledConormalExtended f ht :=
  (Stacks.Sheaves.RingedToposModules.isoOfNaturalHomEquiv (pulledIdealConormalHomEquiv f ht)
    (naturalHomEquiv_pulledIdealConormalHomEquiv f ht)).symm

/-- **The transpose of `pulledIdealConormalIso`**, along `(f ∘ t)^* ⊣ (f ∘ t)_*` and
`(f ∘ t)^* = f^* t^*` (the convention of `prescribedIdealMap`): the map `𝒥 ⟶ (f ∘ t)_*(𝒞 ⊗ 𝒪_X)`
is `𝒥 ⟶ (f ∘ t)_* 𝒦` followed by the conormal class `𝒦 ⟶ 𝒞` and the unit `𝒞 ⟶ 𝒞 ⊗ 𝒪_X`. -/
theorem pulledIdealConormalIso_transpose (ht : IsFirstOrderThickening t) :
    haveI := isLocallySurjective_baseStructureMap f ht.1
    (modulePullbackPushforwardAdjunction (f ≫ t)).homEquiv _ _
        ((modulePullbackCompUniq f t).hom.app (AlgebraicGeometry.SheafOfModules.idealSheaf t) ≫
          (pulledIdealConormalIso f ht).hom) =
      idealToPulledKernel f t ≫
        (SheafOfModules.pushforward.{u}
          (AlgebraicGeometry.SheafOfModules.inverseImageRingHom (f ≫ t).hom.base S'.sheaf)).map
          (Stacks.Sites.Conormal.conormalHomEquivOf.{u, u, u}
            (Opens.grothendieckTopology X.carrier) (baseStructureMap f t) _ rfl _
            ((CategoryTheory.Sheaf.towerExtendRestrictAdjunction.{u, u, u}
              (Opens.grothendieckTopology X.carrier)
              (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)).unit.app
              (pulledConormal f ht))) ≫
        (pushforwardRestrictIso f t (pulledConormalExtended f ht)).hom := by
  have := isLocallySurjective_baseStructureMap f ht.1
  change (modulePullbackPushforwardAdjunction (f ≫ t)).homEquiv _ _
      ((modulePullbackCompUniq f t).hom.app (AlgebraicGeometry.SheafOfModules.idealSheaf t) ≫
        pulledIdealConormalHomEquiv f ht _ (𝟙 _)) = _
  rw [pulledIdealConormalHomEquiv_apply, Iso.hom_inv_id_app_assoc, Equiv.apply_symm_apply]
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine congrArg (· ≫ (pushforwardRestrictIso f t (pulledConormalExtended f ht)).hom) ?_
  refine (Adjunction.homEquiv_naturality_right _ _ _).trans ?_
  refine congrArg₂ (· ≫ ·) (Equiv.apply_symm_apply _ _) ?_
  exact congrArg (fun k => (SheafOfModules.pushforward.{u}
      (AlgebraicGeometry.SheafOfModules.inverseImageRingHom (f ≫ t).hom.base S'.sheaf)).map
      (Stacks.Sites.Conormal.conormalHomEquivOf.{u, u, u}
        (Opens.grothendieckTopology X.carrier) (baseStructureMap f t) _ rfl _ k))
    (Adjunction.homEquiv_id _ _)

/-- A section of `𝒪_{S'}` killed by `t^♯` is carried by the unit of `(f ∘ t)⁻¹ ⊣ (f ∘ t)_*` into
the kernel of the reduction `g`. -/
theorem unit_mem_kernelIdeal (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V)
    (hs : (t.hom.c.app V).hom s = 0) :
    (((sheafAdjunction (f ≫ t)).unit.app S'.sheaf).hom.app V).hom s ∈
      kernelIdeal (baseStructureMap f t).hom (op ((Opens.map (f ≫ t).hom.base).obj V.unop)) :=
  RingHom.mem_ker.2 ((baseStructureMap_app_unit f t V s).trans ((congrArg _ hs).trans (map_zero _)))

/-- **The transpose of `pulledIdealConormalIso` on sections.** A section `s` of `𝒪_{S'}` with
`t^♯ s = 0`, read as a section of `𝒥` by `baseIdealSection`, goes to the image under the unit of
extension of scalars `𝒞 ⟶ 𝒞 ⊗_{f⁻¹𝒪_S} 𝒪_X` of the conormal class of the image of `s` in
`(f ∘ t)⁻¹𝒪_{S'}` under the unit of `(f ∘ t)⁻¹ ⊣ (f ∘ t)_*`. -/
theorem pulledIdealConormalIso_transpose_baseIdealSection (ht : IsFirstOrderThickening t)
    (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0) :
    haveI := isLocallySurjective_baseStructureMap f ht.1
    ((modulePullbackPushforwardAdjunction (f ≫ t)).homEquiv _ _
        ((modulePullbackCompUniq f t).hom.app (AlgebraicGeometry.SheafOfModules.idealSheaf t) ≫
          (pulledIdealConormalIso f ht).hom)).val.app V (baseIdealSection t V s hs) =
      ((CategoryTheory.Sheaf.towerExtendRestrictAdjunction.{u, u, u}
          (Opens.grothendieckTopology X.carrier)
          (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)).unit.app
          (pulledConormal f ht)).val.app (op ((Opens.map (f ≫ t).hom.base).obj V.unop))
        (Stacks.Sites.Conormal.conormalClass.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
          (inverseImageSheaf (f ≫ t)) (inverseImageSheaf (f ≫ t)) (inverseImageSheaf f) (𝟙 _)
          (baseStructureMap f t) (op ((Opens.map (f ≫ t).hom.base).obj V.unop))
          ⟨(((sheafAdjunction (f ≫ t)).unit.app S'.sheaf).hom.app V).hom s,
            unit_mem_kernelIdeal f V s hs⟩) := by
  have := isLocallySurjective_baseStructureMap f ht.1
  rw [pulledIdealConormalIso_transpose]
  exact Stacks.Sites.Conormal.conormalModuleHomEquivOf_app_conormalClass _ _ _ rfl _ (𝟙 _)
    ((CategoryTheory.Sheaf.squareRestrict.{u, u, u} (Opens.grothendieckTopology X.carrier)
      (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)).obj
      (pulledConormalExtended f ht))
    ((CategoryTheory.Sheaf.towerExtendRestrictAdjunction.{u, u, u}
      (Opens.grothendieckTopology X.carrier)
      (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)).unit.app
      (pulledConormal f ht)) _
    ((idealToPulledKernel f t).val.app V (baseIdealSection t V s hs))
    ⟨_, unit_mem_kernelIdeal f V s hs⟩
    ((idealToPulledKernel_app_val f t V _).trans
      (congrArg (AlgebraicGeometry.SheafOfModules.inverseImageRingUnitApp (f ≫ t).hom.base S'.sheaf
        V) (idealSheafι_baseIdealSection t V s hs)))

end Iso

end AlgebraicGeometry.RingedSpaceThickening
