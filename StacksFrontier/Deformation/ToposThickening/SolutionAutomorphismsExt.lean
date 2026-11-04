module

public import Mathlib.CategoryTheory.Abelian.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingInverseImageKernel
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposCotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposHomologyZero
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseSheafification
public import StacksFrontier.Deformation.RingThickening.CotangentAutomorphisms
public import StacksFrontier.Deformation.ToposThickening.SolutionAutomorphisms

/-!
# The automorphisms of a solution are `Ext⁰_O(L_f, G)`

Fix a square-zero extension problem `S` of ringed topoi, the problem of [Stacks Project, Tag 08V4]:
a first order thickening `t : (Sh(B), O_B) ⟶ (Sh(B'), O_{B'})` of the base with ideal `J`, a
morphism of ringed topoi `f : (Sh(C), O) ⟶ (Sh(B), O_B)`, an `O`-module `G` and a map
`c : f⁻¹J ⟶ G`. Let `P` be a solution. [Stacks Project, Tag 08V5], clause (3), says that the set
of automorphisms of `P` fitting into the diagram of Tag 08V4 is canonically isomorphic to
`Ext⁰_O(L_f, G)`.

## Main definitions

* `...CompatibleFirstOrderThickening.descendDerivation`: an `f⁻¹O_B`-derivation of `O` with
  values in `G` obtained from a derivation of a solution by descent along the reduction.
* `...CompatibleFirstOrderThickening.derivationEquivFSharp`: the derivations of a solution are
  the `f⁻¹O_B`-derivations of `O` with values in `G`.
* `AlgebraicGeometry.RingedToposHom.derivationEquivHomDifferentials`: `f⁻¹O_B`-derivations of `O`
  with values in a module are the module maps out of `Ω_f`.
* `AlgebraicGeometry.RingedToposHom.cotangentExt`: `Ext^i_O(L_f, G)`.
* `AlgebraicGeometry.RingedToposHom.homDifferentialsEquivExtZero`:
  `Hom_O(Ω_f, G) ≃+ Ext⁰_O(L_f, G)`.

## Main results

* `...CompatibleFirstOrderThickening.autMulEquivExtZero`: the automorphism group of a solution is
  canonically isomorphic to `Ext⁰_O(L_f, G)`, as a group.

## References

* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
* [Stacks Project, Tag 08V0](https://stacks.math.columbia.edu/tag/08V0)
* [Stacks Project, Tag 04BQ](https://stacks.math.columbia.edu/tag/04BQ)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe t v u w v' u' w'

/-! ## Derivations of `O` into `G` are maps out of `Ω_f`, and those are `Ext⁰_O(L_f, G)` -/

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, max u v w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (f : RingedToposHom X Y) (G : Sheaf.targetModules.{u, v, w} X.J X.O)

/-- The `f⁻¹O_Y`-derivations of `O_X` with values in a sheaf of `O_X`-modules `G` are the module
maps `Ω_f ⟶ G`, a derivation corresponding to the map through which it factors and a map to the
universal derivation followed by it. -/
noncomputable def derivationEquivHomDifferentials :
    f.Derivation G ≃ (f.differentials ⟶ G) where
  toFun D := (f.existsUnique_descDerivation G D).choose
  invFun g := (f.universalDerivation).postcomp g.val
  left_inv D := (f.existsUnique_descDerivation G D).choose_spec.1
  right_inv g := ((f.existsUnique_descDerivation G _).choose_spec.2 g rfl).symm

/-- The map attached to a derivation, composed with the universal derivation, is that
derivation. -/
theorem postcomp_derivationEquivHomDifferentials (D : f.Derivation G) :
    (f.universalDerivation).postcomp (f.derivationEquivHomDifferentials G D).val = D :=
  (f.existsUnique_descDerivation G D).choose_spec.1

/-- The map attached to a derivation is determined by the values of the derivation: on the
universal derivation of a section it is the derivation of that section. -/
theorem derivationEquivHomDifferentials_app (D : f.Derivation G) (U : X.Cᵒᵖ)
    (x : X.O.obj.obj U) :
    (f.derivationEquivHomDifferentials G D).val.app U ((f.universalDerivation).d x) = D.d x :=
  PresheafOfModules.Derivation.congr_d (f.postcomp_derivationEquivHomDifferentials G D) x

variable [HasDerivedCategory.{t} (Sheaf.targetModules.{u, v, w} X.J X.O)]

/-- The module `G`, viewed in `D(O_X)` as a complex concentrated in degree `0`. -/
noncomputable abbrev singleDerived : DerivedCategory (Sheaf.targetModules.{u, v, w} X.J X.O) :=
  (DerivedCategory.singleFunctor (Sheaf.targetModules.{u, v, w} X.J X.O) 0).obj G

/-- `Ext^i_{O_X}(L_f, G)`, formed in the derived category of sheaves of `O_X`-modules. -/
noncomputable abbrev cotangentExt (i : ℤ) : Type _ :=
  DerivedCategory.Ext f.cotangentComplexDerived (singleDerived G) i

/-- The cotangent complex of a morphism of ringed topoi is concentrated in non-positive
degrees. -/
instance cotangentComplexDerived_isLE : (f.cotangentComplexDerived).IsLE 0 :=
  (DerivedCategory.isLE_iff (f.cotangentComplexDerived) 0).2 fun i hi =>
    IsZero.of_iso
      (HomologicalComplex.ExactAt.of_isZero (f.cotangentComplex_isZero_pos i hi)).isZero_homology
      ((DerivedCategory.homologyFunctorFactors (Sheaf.targetModules.{u, v, w} X.J X.O) i).app
        f.cotangentComplex)

/-- The degree-zero homology of `L_f`, formed in the derived category, is `Ω_f`. -/
noncomputable def cotangentComplexDerivedHomologyZeroIso :
    (DerivedCategory.homologyFunctor (Sheaf.targetModules.{u, v, w} X.J X.O) 0).obj
        f.cotangentComplexDerived ≅ f.differentials :=
  (DerivedCategory.homologyFunctorFactors (Sheaf.targetModules.{u, v, w} X.J X.O) 0).app
      f.cotangentComplex ≪≫ f.cotangentComplex_homologyZeroIso

/-- Degree-zero homology of `G` placed in degree `0` is `G`. -/
noncomputable def singleDerivedHomologyIso :
    (DerivedCategory.homologyFunctor (Sheaf.targetModules.{u, v, w} X.J X.O) 0).obj
        (singleDerived G) ≅ G :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (Sheaf.targetModules.{u, v, w} X.J X.O) 0).app G

/-- Taking degree-zero homology sends a class of `Ext⁰_{O_X}(L_f, G)` to a map `Ω_f ⟶ G`. -/
noncomputable def extZeroToHomDifferentials :
    f.cotangentExt G 0 →+ (f.differentials ⟶ G) :=
  AddMonoidHom.mk'
    (fun e => (f.cotangentComplexDerivedHomologyZeroIso).inv ≫
      ((DerivedCategory.homologyFunctor (Sheaf.targetModules.{u, v, w} X.J X.O) 0).shiftMap
          e 0 0 (zero_add 0) :
        (DerivedCategory.homologyFunctor (Sheaf.targetModules.{u, v, w} X.J X.O) 0).obj
            f.cotangentComplexDerived ⟶
          (DerivedCategory.homologyFunctor (Sheaf.targetModules.{u, v, w} X.J X.O) 0).obj
            (singleDerived G)) ≫ (singleDerivedHomologyIso G).hom)
    fun a b => by
      rw [Functor.shiftMap_add]
      exact Preadditive.comp_add_comp_assoc (f.cotangentComplexDerivedHomologyZeroIso).inv _ _
        (singleDerivedHomologyIso G).hom

/-- Taking degree-zero homology identifies `Ext⁰_{O_X}(L_f, G)` with `Hom_{O_X}(Ω_f, G)`. -/
theorem extZeroToHomDifferentials_bijective :
    Function.Bijective (f.extZeroToHomDifferentials G) := by
  have hb := DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
    (f.cotangentComplexDerived) (singleDerived G) 0 0 0 0 (zero_add 0) le_rfl
  exact ((f.cotangentComplexDerivedHomologyZeroIso).homCongr
    (singleDerivedHomologyIso G)).bijective.comp hb

/-- `Hom_{O_X}(Ω_f, G) = Ext⁰_{O_X}(L_f, G)`, the inverse of taking degree-zero homology. -/
noncomputable def homDifferentialsEquivExtZero :
    (f.differentials ⟶ G) ≃+ f.cotangentExt G 0 :=
  (AddEquiv.ofBijective (f.extZeroToHomDifferentials G)
    (f.extZeroToHomDifferentials_bijective G)).symm

end AlgebraicGeometry.RingedToposHom

/-! ## Derivations of a solution descend to derivations of `O` -/

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{v, u, max u v w}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{max u v w})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {S : RingedToposExtensionProblem X B}

variable (S) in
/-- The prescribed module `G` of the problem, read as a sheaf of modules over the structure sheaf
of the source in the spelling of the cotangent complex. -/
noncomputable abbrev targetG : Sheaf.targetModules.{u, v, w} X.J X.O := S.G

namespace CompatibleFirstOrderThickening

variable (P : S.CompatibleFirstOrderThickening)

/-- The underlying sheaf of abelian groups of a sheaf of commutative rings: that of the unit
module. -/
noncomputable abbrev abSheaf (R : Sheaf X.J CommRingCat.{max u v w}) :
    Sheaf X.J AddCommGrpCat.{max u v w} :=
  (SheafOfModules.toSheaf _).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))

/-- The reduction of a solution on underlying sheaves of abelian groups. -/
noncomputable def reductionAb : abSheaf P.extension ⟶ abSheaf X.O :=
  ⟨{ app U := AddCommGrpCat.ofHom (P.reduction.hom.app U).hom.toAddMonoidHom
     naturality {U V} g := by
        ext x
        exact ConcreteCategory.congr_hom (P.reduction.hom.naturality g) x }⟩

/-- On sections, `reductionAb` is the reduction of the solution. -/
theorem reductionAb_app (U : X.Cᵒᵖ) (x : P.extension.obj.obj U) :
    (reductionAb P).hom.app U x = P.reduction.hom.app U x := rfl

/-- The underlying sheaf of abelian groups of `G`. -/
noncomputable abbrev abG : Sheaf X.J AddCommGrpCat.{max u v w} :=
  (SheafOfModules.toSheaf _).obj S.G

/-- The reduction of a solution is an epimorphism of sheaves of abelian groups: it is locally
surjective. -/
theorem epi_reductionAb : Epi (reductionAb P) := by
  have h : Presheaf.IsLocallySurjective X.J (reductionAb P).hom :=
    (Presheaf.isLocallySurjective_iff_whisker_forget X.J (reductionAb P).hom).mpr
      ((Presheaf.isLocallySurjective_iff_whisker_forget X.J P.reduction.hom).mp
        P.locallySurjective : _)
  have : Sheaf.IsLocallySurjective (reductionAb P) := h
  exact Sheaf.epi_of_isLocallySurjective _

/-- A derivation of a solution, as a morphism of sheaves of abelian groups. -/
noncomputable def derivationAb (δ : Derivation P) : abSheaf P.extension ⟶ abG (S := S) :=
  ⟨{ app U := AddCommGrpCat.ofHom
        { toFun := δ.toFun U
          map_zero' := δ.map_zero U
          map_add' := δ.map_add' U }
     naturality {U V} g := by
        ext x
        exact δ.naturality g x }⟩

/-- A derivation of a solution kills the kernel of the reduction. -/
theorem kernel_ι_derivationAb (δ : Derivation P) :
    kernel.ι (reductionAb P) ≫ derivationAb P δ = 0 := by
  ext U x
  have hx : P.reduction.hom.app U ((kernel.ι (reductionAb P)).hom.app U x) = 0 :=
    congrArg (fun k => k.hom.app U x) (kernel.condition (reductionAb P))
  obtain ⟨g, hg⟩ := P.exists_incl _ hx
  change δ.toFun U ((kernel.ι (reductionAb P)).hom.app U x) = 0
  rw [← hg]
  exact δ.map_kernel' U g

/-- The reduction of a solution is the cokernel of its kernel. -/
noncomputable def reductionAbIsCokernel :
    IsColimit (CokernelCofork.ofπ (reductionAb P) (kernel.condition (reductionAb P))) :=
  have := epi_reductionAb P
  Abelian.epiIsCokernelOfKernel (Fork.ofι (kernel.ι (reductionAb P)) (kernel.condition _))
    (kernelIsKernel (reductionAb P))

/-- The descended map of sheaves of abelian groups `O ⟶ G` of a derivation of a solution. -/
noncomputable def descendAb (δ : Derivation P) : abSheaf X.O ⟶ abG (S := S) :=
  (reductionAbIsCokernel P).desc (CokernelCofork.ofπ (derivationAb P δ)
    (kernel_ι_derivationAb P δ))

/-- The descended map composed with the reduction is the derivation of the solution. -/
theorem reductionAb_descendAb (δ : Derivation P) :
    reductionAb P ≫ descendAb P δ = derivationAb P δ :=
  (reductionAbIsCokernel P).fac _ WalkingParallelPair.one

/-- On sections, the descended map applied to a reduced section is the derivation of the
section. -/
theorem descendAb_reduction (δ : Derivation P) (U : X.Cᵒᵖ)
    (x : P.extension.obj.obj U) :
    (descendAb P δ).hom.app U (P.reduction.hom.app U x) = δ.toFun U x :=
  congrArg (fun k : abSheaf P.extension ⟶ abG (S := S) => k.hom.app U x)
    (reductionAb_descendAb P δ)

/-- The descended map of a derivation of a solution is natural in the site variable. -/
theorem descendAb_naturality (δ : Derivation P) {U V : X.Cᵒᵖ} (g : U ⟶ V)
    (x : X.O.obj.obj U) :
    S.G.val.map g ((descendAb P δ).hom.app U x) =
      (descendAb P δ).hom.app V (X.O.obj.map g x) :=
  (ConcreteCategory.congr_hom ((descendAb P δ).hom.naturality g) x).symm

attribute [local instance] Sheaf.moduleOfSections

/-- The `f⁻¹O_B`-derivation `D` of `O` with values in `G` attached to a derivation `δ` of the
thickened structure sheaf `O'` of a solution, determined by `D(x mod G) = δ(x)`. -/
noncomputable def descendDerivation (δ : Derivation P) : S.f.Derivation S.G where
  d {U} := ((descendAb P δ).hom.app U).hom
  d_map g x := (descendAb_naturality P δ g x).symm
  d_mul {U} x y := by
    let MT : Sheaf X.J (Type (max u v w)) := (sheafCompose X.J (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf _).obj S.G)
    let ct := Functor.whiskerRight P.reduction.hom (forget CommRingCat)
    have : Presheaf.IsLocallySurjective X.J ct :=
      (Presheaf.isLocallySurjective_iff_whisker_forget X.J P.reduction.hom).mp
        P.locallySurjective
    refine Sheaf.eq_of_isLocallySurjective_binary X.J ct MT
      (fun U (x y : X.O.obj.obj U) => (descendAb P δ).hom.app U (x * y))
      (fun U (x y : X.O.obj.obj U) =>
        toRingSection X.J x • (show P.toSituation.G.val.obj U from (descendAb P δ).hom.app U y) +
          toRingSection X.J y • (show P.toSituation.G.val.obj U from (descendAb P δ).hom.app U x))
      ?_ ?_ ?_ U x y
    · rintro U V g (x : X.O.obj.obj U) (y : X.O.obj.obj U)
      change S.G.val.map g ((descendAb P δ).hom.app U (x * y)) =
        (descendAb P δ).hom.app V (X.O.obj.map g x * X.O.obj.map g y)
      rw [descendAb_naturality, map_mul]
    · rintro U V g (x : X.O.obj.obj U) (y : X.O.obj.obj U)
      have e₁ := P.toSituation.G.val.map_smul g (toRingSection X.J x)
        ((descendAb P δ).hom.app U y)
      have e₂ := P.toSituation.G.val.map_smul g (toRingSection X.J y)
        ((descendAb P δ).hom.app U x)
      refine ((P.toSituation.G.val.map g).hom.map_add _ _).trans
        (congrArg₂ (· + ·) (e₁.trans ?_) (e₂.trans ?_))
      · exact congrArg (fun m : P.toSituation.G.val.obj V =>
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g (toRingSection X.J x) • m)
          (descendAb_naturality P δ g y)
      · exact congrArg (fun m : P.toSituation.G.val.obj V =>
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g (toRingSection X.J y) • m)
          (descendAb_naturality P δ g x)
    · intro U x' y'
      change (descendAb P δ).hom.app U
          (P.reduction.hom.app U x' * P.reduction.hom.app U y') =
        toRingSection X.J (P.reduction.hom.app U x') •
            (show P.toSituation.G.val.obj U from
              (descendAb P δ).hom.app U (P.reduction.hom.app U y')) +
          toRingSection X.J (P.reduction.hom.app U y') •
            (show P.toSituation.G.val.obj U from
              (descendAb P δ).hom.app U (P.reduction.hom.app U x'))
      rw [← map_mul, descendAb_reduction, descendAb_reduction, descendAb_reduction]
      exact δ.leibniz' U x' y'
  d_app {U} a := by
    let MT : Sheaf X.J (Type (max u v w)) := (sheafCompose X.J (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf _).obj S.G)
    let ct := Functor.whiskerRight
      ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom (forget CommRingCat)
    have : Presheaf.IsLocallySurjective X.J ct :=
      (Presheaf.isLocallySurjective_iff_whisker_forget X.J _).mp
        (Stacks.Sheaves.ToposPushforward.isLocallySurjective_inverseImageCommRingFunctor_map
          S.f.toToposHom S.baseReduction S.baseLocallySurjective)
    refine Sheaf.eq_of_isLocallySurjective_binary X.J ct MT
      (fun U (x _ : ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O).obj.obj U) =>
        (descendAb P δ).hom.app U (S.f.fSharpInverseImage.hom.app U x))
      (fun U _ _ => (0 : S.G.val.obj U)) ?_ ?_ ?_ U a a
    · rintro U V g x -
      change S.G.val.map g ((descendAb P δ).hom.app U (S.f.fSharpInverseImage.hom.app U x)) =
        (descendAb P δ).hom.app V (S.f.fSharpInverseImage.hom.app V
          (((inverseImageCommRingFunctor S.f.toToposHom).obj B.O).obj.map g x))
      rw [descendAb_naturality]
      exact congrArg ((descendAb P δ).hom.app V)
        (ConcreteCategory.congr_hom (S.f.fSharpInverseImage.hom.naturality g) x).symm
    · rintro U V g - -
      exact (S.G.val.map g).hom.map_zero
    · intro U b _
      change (descendAb P δ).hom.app U (S.f.fSharpInverseImage.hom.app U
        (((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U b)) = 0
      have h := ConcreteCategory.congr_hom (NatTrans.congr_app
        (congrArg (fun k => k.hom) P.baseMap_reduction) U) b
      change P.reduction.hom.app U (P.baseMap.hom.app U b) =
        S.f.fSharpInverseImage.hom.app U
          (((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U b) at h
      rw [← h, descendAb_reduction]
      exact δ.map_base' U b

/-- The descended derivation takes the value `δ(x)` on the reduction of a section `x`. -/
theorem descendDerivation_d_reduction (δ : Derivation P) (U : X.Cᵒᵖ)
    (x : P.extension.obj.obj U) :
    (descendDerivation P δ).d (P.reduction.hom.app U x) = δ.toFun U x :=
  descendAb_reduction P δ U x

/-- The derivation of a solution attached to an `f⁻¹O_B`-derivation `D` of `O` with values in
`G`: the composite of `D` with the reduction `O' ⟶ O`. -/
noncomputable def derivationOfFSharp (D : S.f.Derivation S.G) : Derivation P where
  toFun U x := D.d (P.reduction.hom.app U x)
  map_add' U x y := by rw [map_add, map_add]
  naturality {U V} g x :=
    (congrArg D.d (ConcreteCategory.congr_hom (P.reduction.hom.naturality g) x)).trans
      (D.d_map g _)
  leibniz U x y := by
    change D.d (P.reduction.hom.app U (x * y)) = _
    rw [map_mul, D.d_mul]
    rfl
  map_kernel U m := by
    change D.d (P.reduction.hom.app U (P.incl m)) = 0
    rw [P.reduction_incl, map_zero]
  map_base U a := by
    change D.d (P.reduction.hom.app U (P.baseMap.hom.app U a)) = 0
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun k => k.hom) P.baseMap_reduction) U) a
    change P.reduction.hom.app U (P.baseMap.hom.app U a) =
      S.f.fSharpInverseImage.hom.app U
        (((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U a) at h
    rw [h]
    exact D.d_app _

/-- The derivations of a solution are the `f⁻¹O_B`-derivations of `O` with values in `G`:
descending along the reduction `O' ⟶ O` and composing with it are mutually inverse. -/
noncomputable def derivationEquivFSharp : Derivation P ≃ S.f.Derivation S.G where
  toFun := descendDerivation P
  invFun := derivationOfFSharp P
  left_inv δ := Derivation.ext_apply fun U x => descendDerivation_d_reduction P δ U x
  right_inv D := by
    let MT : Sheaf X.J (Type (max u v w)) := (sheafCompose X.J (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf _).obj S.G)
    let ct := Functor.whiskerRight P.reduction.hom (forget CommRingCat)
    have : Presheaf.IsLocallySurjective X.J ct :=
      (Presheaf.isLocallySurjective_iff_whisker_forget X.J P.reduction.hom).mp
        P.locallySurjective
    refine PresheafOfModules.Derivation.ext (funext fun U => AddMonoidHom.ext fun x => ?_)
    refine Sheaf.eq_of_isLocallySurjective_binary X.J ct MT
      (fun U (x _ : X.O.obj.obj U) => (descendDerivation P (derivationOfFSharp P D)).d x)
      (fun U (x _ : X.O.obj.obj U) => D.d x) ?_ ?_ ?_ U x x
    · rintro U V g x -
      exact ((descendDerivation P (derivationOfFSharp P D)).d_map g x).symm
    · rintro U V g x -
      exact (D.d_map g x).symm
    · intro U x' _
      exact descendDerivation_d_reduction P _ U x'

/-- The value of the bijection `derivationEquivFSharp` on the reduction of a section. -/
theorem derivationEquivFSharp_d (δ : Derivation P) (U : X.Cᵒᵖ) (x : P.extension.obj.obj U) :
    (derivationEquivFSharp P δ).d (P.reduction.hom.app U x) = δ.toFun U x :=
  descendDerivation_d_reduction P δ U x


/-- The descended derivation of a sum of derivations of a solution is the sum of the descended
derivations, on every section. -/
theorem derivationEquivFSharp_add_d (δ ε : Derivation P) (U : X.Cᵒᵖ) (x : X.O.obj.obj U) :
    (derivationEquivFSharp P (δ + ε)).d x =
      (derivationEquivFSharp P δ).d x + (derivationEquivFSharp P ε).d x := by
  let MT : Sheaf X.J (Type (max u v w)) := (sheafCompose X.J (forget AddCommGrpCat)).obj
    ((SheafOfModules.toSheaf _).obj S.G)
  let ct := Functor.whiskerRight P.reduction.hom (forget CommRingCat)
  have : Presheaf.IsLocallySurjective X.J ct :=
    (Presheaf.isLocallySurjective_iff_whisker_forget X.J P.reduction.hom).mp
      P.locallySurjective
  refine Sheaf.eq_of_isLocallySurjective_binary X.J ct MT
    (fun U (x _ : X.O.obj.obj U) => (derivationEquivFSharp P (δ + ε)).d x)
    (fun U (x _ : X.O.obj.obj U) =>
      (derivationEquivFSharp P δ).d x + (derivationEquivFSharp P ε).d x) ?_ ?_ ?_ U x x
  · rintro U V g x -
    exact ((derivationEquivFSharp P (δ + ε)).d_map g x).symm
  · rintro U V g x -
    exact ((S.G.val.map g).hom.map_add _ _).trans (congrArg₂ (· + ·)
      ((derivationEquivFSharp P δ).d_map g x).symm ((derivationEquivFSharp P ε).d_map g x).symm)
  · intro U x' _
    change (derivationEquivFSharp P (δ + ε)).d (P.reduction.hom.app U x') =
      (derivationEquivFSharp P δ).d (P.reduction.hom.app U x') +
        (derivationEquivFSharp P ε).d (P.reduction.hom.app U x')
    rw [derivationEquivFSharp_d, derivationEquivFSharp_d, derivationEquivFSharp_d]
    rfl

/-- The map `Ω_f ⟶ G` attached to a derivation of a solution: descend it to an
`f⁻¹O_B`-derivation of `O` and factor that through the universal derivation. -/
noncomputable def derivationToHomDifferentials (δ : Derivation P) :
    S.f.differentials ⟶ targetG S :=
  S.f.derivationEquivHomDifferentials (targetG S) (derivationEquivFSharp P δ)

/-- The map `Ω_f ⟶ G` attached to a derivation of a solution sends the universal derivation of a
section to the descended derivation of that section. -/
private theorem derivationToHomDifferentials_app (δ : Derivation P) (U : X.Cᵒᵖ)
    (x : X.O.obj.obj U) :
    (derivationToHomDifferentials P δ).val.app U ((S.f.universalDerivation).d x) =
      (derivationEquivFSharp P δ).d x :=
  RingedToposHom.derivationEquivHomDifferentials_app _ _ _ U x

/-- The map `Ω_f ⟶ G` attached to a derivation of a solution is additive in the derivation. -/
theorem derivationToHomDifferentials_add (δ ε : Derivation P) :
    derivationToHomDifferentials P (δ + ε) =
      derivationToHomDifferentials P δ + derivationToHomDifferentials P ε := by
  apply (S.f.derivationEquivHomDifferentials (targetG S)).symm.injective
  refine PresheafOfModules.Derivation.ext (funext fun U => AddMonoidHom.ext fun x => ?_)
  change ((S.f.derivationEquivHomDifferentials (targetG S)).symm
      (S.f.derivationEquivHomDifferentials (targetG S) (derivationEquivFSharp P (δ + ε)))).d x =
    (derivationToHomDifferentials P δ + derivationToHomDifferentials P ε).val.app U
      ((S.f.universalDerivation).d x)
  rw [Equiv.symm_apply_apply]
  refine (derivationEquivFSharp_add_d P δ ε U x).trans ?_
  change _ = (derivationToHomDifferentials P δ).val.app U ((S.f.universalDerivation).d x) +
    (derivationToHomDifferentials P ε).val.app U ((S.f.universalDerivation).d x)
  rw [derivationToHomDifferentials_app, derivationToHomDifferentials_app]

/-- The derivations of a solution are the maps `Ω_f ⟶ G`: the composite of
`derivationEquivFSharp` with the universal property of `Ω_f`. -/
noncomputable def derivationEquivHomDifferentials :
    Derivation P ≃ (S.f.differentials ⟶ targetG S) :=
  (derivationEquivFSharp P).trans (S.f.derivationEquivHomDifferentials (targetG S))

variable [X.J.HasSheafCompose (forget CommRingCat.{max u v w})]
  [(forget CommRingCat.{max u v w}).ReflectsIsomorphisms]
  [HasDerivedCategory.{t} (Sheaf.targetModules.{u, v, w} X.J X.O)]

/-- The bijection between the automorphisms of a solution and `Ext⁰_O(L_f, G)`, as a map of sets.
-/
noncomputable def autEquivExtZero : P.AutomorphismGroup ≃ S.f.cotangentExt (targetG S) 0 :=
  ((autEquivDerivation P).trans (derivationEquivHomDifferentials P)).trans
    (S.f.homDifferentialsEquivExtZero (targetG S)).toEquiv

/-- Given a solution `P` of a square-zero extension problem of ringed topoi, the group of
automorphisms of `P` fitting into the diagram of the problem is canonically isomorphic to
`Ext⁰_O(L_f, G)`: an automorphism `a` goes to the class whose degree-zero homology
`Ω_f = H⁰(L_f) ⟶ G` sends `d(x mod G)` to the section of `G` by which `a(x)` differs from `x`;
composition of automorphisms goes to addition of classes. -/
@[stacks 08V5 "clause (3): given a solution, its automorphisms fitting into the diagram of 08V4 \
  form a group canonically isomorphic to Ext⁰_O(L_f, G)"]
noncomputable def autMulEquivExtZero :
    P.AutomorphismGroup ≃* Multiplicative (S.f.cotangentExt (targetG S) 0) where
  toEquiv := (autEquivExtZero P).trans Multiplicative.ofAdd
  map_mul' a b := by
    change Multiplicative.ofAdd (autEquivExtZero P (a * b)) =
      Multiplicative.ofAdd (autEquivExtZero P a) * Multiplicative.ofAdd (autEquivExtZero P b)
    rw [← ofAdd_add]
    congr 1
    change S.f.homDifferentialsEquivExtZero (targetG S)
        (derivationToHomDifferentials P (autEquivDerivation P (a * b))) =
      S.f.homDifferentialsEquivExtZero (targetG S)
          (derivationToHomDifferentials P (autEquivDerivation P a)) +
        S.f.homDifferentialsEquivExtZero (targetG S)
          (derivationToHomDifferentials P (autEquivDerivation P b))
    rw [autEquivDerivation_mul, derivationToHomDifferentials_add, map_add]

/-- The class attached to an automorphism, read in degree-zero homology: the map `Ω_f ⟶ G`
it induces sends `d(x mod G)` to the section `g` of `G` with `a(x) = x + g`. -/
theorem incl_extZeroToHomDifferentials_autMulEquivExtZero (a : P.AutomorphismGroup)
    (U : X.Cᵒᵖ) (x : P.extension.obj.obj U) :
    P.incl ((S.f.extZeroToHomDifferentials (targetG S)
        (Multiplicative.toAdd (autMulEquivExtZero P a))).val.app U
          ((S.f.universalDerivation).d (P.reduction.hom.app U x))) =
      a.hom.hom.hom.hom.app U x - x := by
  change P.incl ((S.f.extZeroToHomDifferentials (targetG S)
      (S.f.homDifferentialsEquivExtZero (targetG S)
      (derivationToHomDifferentials P (autEquivDerivation P a)))).val.app U _) = _
  have h : S.f.extZeroToHomDifferentials (targetG S) (S.f.homDifferentialsEquivExtZero (targetG S)
      (derivationToHomDifferentials P (autEquivDerivation P a))) =
      derivationToHomDifferentials P (autEquivDerivation P a) :=
    (AddEquiv.ofBijective (S.f.extZeroToHomDifferentials (targetG S))
      (S.f.extZeroToHomDifferentials_bijective (targetG S))).apply_symm_apply _
  rw [h, derivationToHomDifferentials_app, derivationEquivFSharp_d,
    incl_autEquivDerivation_toFun]

end CompatibleFirstOrderThickening

end Deformation.ToposThickening.RingedToposExtensionProblem

end
