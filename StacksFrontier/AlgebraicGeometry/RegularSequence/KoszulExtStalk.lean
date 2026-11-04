module

public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtComputation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafStalkBasis
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulSheafDifferential
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.FiniteColimits.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InternalHomSheafAsSheafHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Ext sheaves of a Koszul-regular quotient, at a stalk

Let `O♯` be a sheaf of commutative rings on a space `X`, let `f_1, …, f_r` be global sections
generating an ideal `I`, and suppose the Koszul complex `K` on `f` resolves the quotient
`O♯/I`. The Ext sheaves of the quotient are then the internal Hom sheaves out of the exterior
powers of `(O♯)ʳ`,

`Ext^m_{O♯}(O♯/I, O♯/I) ≅ SheafHom_{O♯}(⋀ᵐ((O♯)ʳ), O♯/I)`,

which is `Stacks.RegularSequence.KoszulChainData.extIsoInternalHomExteriorPower`: the Hom complex
out of the Koszul complex into the quotient has vanishing differential, so its cohomology is its
terms.

This file passes to a stalk. At a point `x` the exterior power `⋀ᵐ((O♯)ʳ)` is free of finite
rank, hence of finite presentation, so the stalk of the internal Hom sheaf out of it is the
module of linear maps on stalks; and the stalk of the exterior power is the exterior power of the
free module `(O_x)ʳ`. Composing the three identifications,

`Ext^m_{O♯}(O♯/I, O♯/I)_x ≅ (⋀ᵐ((O_x)ʳ) →ₗ[O_x] (O♯/I)_x)`,

the dual of the `m`-th exterior power of a free module of rank `r`, with values in the stalk of
the quotient. The germ formula records what the identification does to the class of a local
homomorphism evaluated on a basis wedge.

## Main definitions

* `Stacks.SheafOfModules.ringedSpace`: the space and its sheaf of rings, read as a ringed space.
* `Stacks.SheafOfModules.modStalkEquivOfIso`: the linear isomorphism of stalks induced by an
  isomorphism of sheaves of modules.
* `Stacks.RegularSequence.KoszulChainData.extStalkEquiv`: the identification displayed above.
* `Stacks.RegularSequence.KoszulChainData.ext1StalkEquiv`: its degree-one case, which
  presents the stalk of `Ext^1` as the `O_x`-linear maps `(O_x)ʳ → (O♯/I)_x`.

## Main statements

* `Stacks.RegularSequence.KoszulChainData.isFinitePresentation_koszulExteriorPower`: the exterior
  powers of `(O♯)ʳ` are of finite presentation.
* `Stacks.RegularSequence.KoszulChainData.extStalkEquiv_germ`: the identification carries the Ext
  class of a local homomorphism `s`, evaluated on the basis wedge indexed by `i`, to the germ of
  the value of `s` on the corresponding basis section of the exterior power.
* `Stacks.RegularSequence.KoszulChainData.ext1StalkEquiv_germ`: in degree one this carries the
  `j`-th basis section to the `j`-th coordinate functional, so the stalk of `Ext^1` is free of
  rank `r` over the stalk of the quotient with the coordinate functionals as a basis.

## Implementation notes

**Where the stalk of an internal Hom comes from.** The stalk of `SheafHom_{O_X}(F, G)` at `x` is
the module of `O_{X,x}`-linear maps `F_x →ₗ G_x` as soon as `F` is of finite presentation; this is
Tag 01CP, available as
`Stacks.SheafOfModules.SheafHomStalk.sheafHomStalkLinearEquivOfFinitePresentation`, and it is
applied here through `Stacks.SheafOfModules.internalHomSheafStalkEquiv`, which packages the
internal Hom sheaf of the ringed site as the `SheafHom` datum that Tag 01CP consumes. Nothing
about exterior powers is involved in that step: the finiteness hypothesis is the whole input.

**Where the stalk of an exterior power comes from.** Sheaf exterior powers have a *general* stalk
identification `Stacks.SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPowerStalkEquiv`,
valid for any sheaf of modules carrying the exterior algebra datum and equipped with a germ
formula on wedges of local sections; the Koszul-specific
`Stacks.SheafOfModules.exteriorKoszulStalkEquiv` used below is that general equivalence composed
with the trivialisation of the free sheaf, and it is what carries the germ formula on the
*basis* sections. Either is available; the Koszul one is used here because the basis is what the
computation needs.

**Two spellings of the sheaf of rings.** The finite presentation of an exterior power is proved
over `structureSheafRing` of a ringed space, while the Koszul development works
over `CategoryTheory.Sheaf.toRingCat` of the sheaf of commutative rings. The two are
definitionally equal, but `sheafCompose` is not reducible, so an instance standing in context at
one spelling is not found at the other; the finite presentation of the free sheaf is therefore
supplied as an explicit term rather than synthesised, and the exterior-power theorem is applied
rather than searched for.

## References

* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex Stacks.ChainComplex

universe u

namespace Stacks.SheafOfModules

open Stacks.SheafOfModules.SheafHomStalk

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- A sheaf of commutative rings on a topological space, read as a ringed space: the space is the
given one and the structure sheaf is the given sheaf. Its `structureSheafRing` is the sheaf of
rings underlying `Rc`. -/
@[ega "0 4.1.1"]
def ringedSpace : RingedSpace.{u, u} where
  carrier := X
  presheaf := Rc.obj
  IsSheaf := Rc.property

/-- The sheaf of rings of the ringed space attached to `Rc` is the one the site-level development
uses. -/
theorem ringSheaf_ringedSpace :
    structureSheafRing (ringedSpace Rc) =
      toRingCat (Opens.grothendieckTopology ↥X) Rc :=
  rfl

/-- **An isomorphism of sheaves of modules is a linear isomorphism on every stalk.** The
underlying map is the one induced on stalks by the isomorphism, and it is bijective because
isomorphy of sheaves of modules is detected stalkwise. -/
def modStalkEquivOfIso {M N : SheafOfModules.{u} (structureSheaf Rc)} (e : M ≅ N) (x : X) :
    modStalk M x ≃ₗ[ringStalk Rc x] modStalk N x :=
  LinearEquiv.ofBijective (Stacks.RegularSequence.stalkLin e.hom.val x)
    ((AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap e.hom).1 e.isIso_hom x)

/-- The stalk isomorphism induced by an isomorphism of sheaves of modules carries the germ of a
local section to the germ of its image. -/
theorem modStalkEquivOfIso_germ {M N : SheafOfModules.{u} (structureSheaf Rc)} (e : M ≅ N)
    (x : X) (U : Opens X) (hxU : x ∈ U) (s : (commVal (Rc := Rc) M).obj (op U)) :
    modStalkEquivOfIso Rc e x (germAt M U x hxU s)
      = germAt N U x hxU (e.hom.val.app (op U) s) :=
  Stacks.RegularSequence.stalkLin_germAddHom e.hom.val U hxU s

end Stacks.SheafOfModules

namespace Stacks.RegularSequence.KoszulChainData

open Stacks.SheafOfModules Stacks.SheafOfModules.SheafHomStalk

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Rc r)}
  {φ : koszulFreeSheaf Rc r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)}

/-- **The free sheaf on `r` generators is of finite presentation.** It is free on a finite index
type, so it is its own presentation with no relations. -/
theorem isFinitePresentation_koszulFreeSheaf : (koszulFreeSheaf Rc r).IsFinitePresentation :=
  Stacks.Tag01PJFiniteColimits.isFinitePresentation_free
    (R := toRingCat (Opens.grothendieckTopology ↥X) Rc) (ULift.{u} (Fin r))

/-- **The exterior powers of `(O♯)ʳ` are of finite presentation.** The free sheaf on `r`
generators is of finite presentation, and the exterior powers of a sheaf of modules of finite
presentation are again of finite presentation. -/
theorem isFinitePresentation_koszulExteriorPower (m : ℕ) :
    (A.exteriorPower m).IsFinitePresentation :=
  have : _root_.SheafOfModules.IsFinitePresentation.{u, u, u}
      (R := structureSheafRing (ringedSpace Rc)) (koszulFreeSheaf Rc r) :=
    isFinitePresentation_koszulFreeSheaf Rc (r := r)
  Stacks.SheafOfModules.isFinitePresentation_exteriorPower (X := ringedSpace Rc)
    (koszulFreeSheaf Rc r) A m

/-- **The Ext sheaves of a Koszul-regular quotient at a stalk.** For a Koszul complex that
resolves the quotient `O♯/I`, the stalk at `x` of `Ext^m_{O♯}(O♯/I, O♯/I)` is the module of
`O_x`-linear maps from the `m`-th exterior power of the free module `(O_x)ʳ` to the stalk of the
quotient.

This is the composition of three identifications: the Ext sheaf is the internal Hom sheaf out of
`⋀ᵐ((O♯)ʳ)`; the stalk of that internal Hom sheaf is the module of linear maps on stalks, because
the exterior power is of finite presentation; and the stalk of the exterior power is the exterior
power of `(O_x)ʳ`. -/
def extStalkEquiv (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation] (m : ℕ)
    (x : X) :
    modStalk
        (derivedSheafExt Rc
          (DerivedCategory.Q.obj
            ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
              (quotient Rc (φ := φ))))
          (DerivedCategory.Q.obj
            ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
              (quotient Rc (φ := φ)))) ((m : ℕ) : ℤ)) x ≃ₗ[ringStalk Rc x]
      (⋀[↑(TopCat.Presheaf.stalk Rc.obj x)]^m (Fin r → ↑(TopCat.Presheaf.stalk Rc.obj x)) →ₗ[
          ringStalk Rc x] modStalk (quotient Rc (φ := φ)) x) :=
  have : _root_.SheafOfModules.IsFinitePresentation.{u, u, u}
      (R := structureSheaf Rc) (A.exteriorPower m) :=
    isFinitePresentation_koszulExteriorPower Rc (A := A) m
  modStalkEquivOfIso Rc (extIsoInternalHomExteriorPower Rc K m) x ≪≫ₗ
    internalHomSheafStalkEquiv Rc (A.exteriorPower m) (quotient Rc (φ := φ)) x ≪≫ₗ
    LinearEquiv.arrowCongr (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A m x)
      (LinearEquiv.refl (ringStalk Rc x) (modStalk (quotient Rc (φ := φ)) x))

/-- **The stalk identification of the Ext sheaves on germs.** The Ext class at `x` of a local
homomorphism `s : ⋀ᵐ((O♯)ʳ)|_U ⟶ (O♯/I)|_U`, evaluated on the basis wedge indexed by
`i : Fin m → Fin r`, is the germ at `x` of the value of `s` on the corresponding basis section of
the exterior power. -/
theorem extStalkEquiv_germ (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation] (m : ℕ)
    (x : X) (U : Opens X) (hxU : x ∈ U)
    (s : (RingedSite.internalHomSheaf (ringedSite Rc) (A.exteriorPower m)
      (quotient Rc (φ := φ))).val.obj (op U)) (i : Fin m → Fin r) :
    extStalkEquiv Rc K m x
        ((modStalkEquivOfIso Rc (extIsoInternalHomExteriorPower Rc K m) x).symm
          (germAt (RingedSite.internalHomSheaf (ringedSite Rc) (A.exteriorPower m)
            (quotient Rc (φ := φ))) U x hxU s))
        (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Rc.obj x) m fun j => Pi.single (i j) 1)
      = germAt (quotient Rc (φ := φ)) U x hxU
          (s.app (op (Over.mk (𝟙 U))) (exteriorBasisSection A U m i)) := by
  have hfp : _root_.SheafOfModules.IsFinitePresentation.{u, u, u}
      (R := structureSheaf Rc) (A.exteriorPower m) :=
    isFinitePresentation_koszulExteriorPower Rc (A := A) m
  have hbasis : (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A m x).symm
      (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Rc.obj x) m fun j => Pi.single (i j) 1)
      = germAt (A.exteriorPower m) U x hxU (exteriorBasisSection A U m i) :=
    (LinearEquiv.symm_apply_eq _).2
      (Stacks.SheafOfModules.exteriorKoszulStalkEquiv_germ_exteriorBasisSection A m U hxU i).symm
  rw [extStalkEquiv]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.arrowCongr_apply, LinearEquiv.refl_apply]
  rw [hbasis]
  exact internalHomSheafStalkEquiv_germ Rc (A.exteriorPower m) (quotient Rc (φ := φ)) x U hxU s
    (exteriorBasisSection A U m i)

/-- **The first Ext sheaf of a Koszul-regular quotient at a stalk.** The stalk at `x` of
`Ext^1_{O♯}(O♯/I, O♯/I)` is the module of `O_x`-linear maps from the free module `(O_x)ʳ` to the
stalk of the quotient — so it is free of rank `r` over the quotient, with the coordinate
functionals as a basis. This is `extStalkEquiv` in degree one, with the first exterior power of a
module identified with the module itself. -/
def ext1StalkEquiv (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation] (x : X) :
    modStalk
        (derivedSheafExt Rc
          (DerivedCategory.Q.obj
            ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
              (quotient Rc (φ := φ))))
          (DerivedCategory.Q.obj
            ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
              (quotient Rc (φ := φ)))) ((1 : ℕ) : ℤ)) x ≃ₗ[ringStalk Rc x]
      ((Fin r → ↑(TopCat.Presheaf.stalk Rc.obj x)) →ₗ[ringStalk Rc x]
        modStalk (quotient Rc (φ := φ)) x) :=
  extStalkEquiv Rc K 1 x ≪≫ₗ
    LinearEquiv.arrowCongr
      (exteriorPower.oneEquiv ↑(TopCat.Presheaf.stalk Rc.obj x)
        (Fin r → ↑(TopCat.Presheaf.stalk Rc.obj x)))
      (LinearEquiv.refl (ringStalk Rc x) (modStalk (quotient Rc (φ := φ)) x))

/-- **The degree-one stalk identification on the coordinate basis.** The `Ext^1` class at `x` of a
local homomorphism `s`, evaluated on the `j`-th standard basis vector of `(O_x)ʳ`, is the germ of
the value of `s` on the `j`-th generator of the first exterior power. So the identification
carries the `j`-th basis section to the `j`-th coordinate functional. -/
theorem ext1StalkEquiv_germ (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation]
    (x : X) (U : Opens X) (hxU : x ∈ U)
    (s : (RingedSite.internalHomSheaf (ringedSite Rc) (A.exteriorPower 1)
      (quotient Rc (φ := φ))).val.obj (op U)) (j : Fin r) :
    ext1StalkEquiv Rc K x
        ((modStalkEquivOfIso Rc (extIsoInternalHomExteriorPower Rc K 1) x).symm
          (germAt (RingedSite.internalHomSheaf (ringedSite Rc) (A.exteriorPower 1)
            (quotient Rc (φ := φ))) U x hxU s))
        (Pi.single j 1)
      = germAt (quotient Rc (φ := φ)) U x hxU
          (s.app (op (Over.mk (𝟙 U))) (exteriorBasisSection A U 1 fun _ => j)) := by
  have hone : (exteriorPower.oneEquiv ↑(TopCat.Presheaf.stalk Rc.obj x)
        (Fin r → ↑(TopCat.Presheaf.stalk Rc.obj x))).symm (Pi.single j 1)
      = exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Rc.obj x) 1
          fun _ => Pi.single j 1 :=
      by rw [LinearEquiv.symm_apply_eq]; simp only [exteriorPower.oneEquiv_ιMulti]
  rw [ext1StalkEquiv]
  simp only [LinearEquiv.trans_apply, LinearEquiv.arrowCongr_apply, LinearEquiv.refl_apply]
  rw [hone]
  exact extStalkEquiv_germ Rc K 1 x U hxU s fun _ => j

end Stacks.RegularSequence.KoszulChainData

end
