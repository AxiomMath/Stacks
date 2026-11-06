module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackCategory
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSection
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerConstraints
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRightScalar
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorUnitSmul
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleModuleTriviality
public import StacksFrontier.CategoryTheory.Sites.Modules.ComplexesDGCategoryBaseRing

/-!
# Multiplication by global functions on modules over an algebraic space

For an algebraic space `Z` over a scheme `S` of a big fppf site, a global regular function of `Z`
acts on every `𝒪_Z`-module by multiplication, as an endomorphism of the identity functor. This
file compares these multiplications along morphisms of algebraic spaces, shows that every
endomorphism of an invertible module is multiplication by a unique global function, and attaches
global functions of the base changes `X_T` to the regular functions on test schemes `T`.

## Main definitions

* `AlgebraicGeometry.Space.globalFunctionSMul`: multiplication by a global regular function, as an
  endomorphism of the identity functor of `𝒪_Z`-modules.
* `AlgebraicGeometry.Space.GlobalFunctionsCompatible`: compatibility of global functions on `Y`
  and on `X` along a morphism `f : X ⟶ Y`.
* `AlgebraicGeometry.Space.schemeGlobalFunctions`: a regular function on a scheme of the site, as
  a global function of the algebraic space it represents.
* `AlgebraicGeometry.Space.baseChangeGlobalFunctions`: the global functions of `X_T` attached to
  the regular functions on a test scheme `T`.

## Main results

* `AlgebraicGeometry.Space.modulePushforward_map_globalFunctionSMul` and
  `AlgebraicGeometry.Space.modulePullback_map_globalFunctionSMul`: direct and inverse image carry
  multiplication by a global function to multiplication by a compatible one.
* `AlgebraicGeometry.Space.globalFunctionSMul_injective_of_isInvertibleModule`: on an invertible
  module, multiplication by a global function determines the function.
* `AlgebraicGeometry.Space.exists_eq_globalFunctionSMul_of_isInvertibleModule`: every endomorphism
  of an invertible module is multiplication by a global function.
* `AlgebraicGeometry.Space.globalFunctionsCompatible_baseChangeGlobalFunctions`: the global
  functions attached to a test scheme are compatible along the morphisms of base changes.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback
open scoped IsMulCommutative

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Multiplication by a global regular function of an algebraic space `Z`, as an endomorphism of
the identity functor of the category of `𝒪_Z`-modules. -/
abbrev globalFunctionSMul (Z : AlgebraicSpaces B S hS)
    (a : ((structureRingSheaf B S hS Z).obj ⋙ forget RingCat).sections) :
    End (𝟭 (Modules.{u, u} B S hS Z.1 Z.2)) :=
  haveI : ∀ U, IsMulCommutative ((structureRingSheaf B S hS Z).obj.obj U) := fun U ↦
    RingedSite.ringSheafSectionsIsMulCommutative (smallEtaleRingedSite B S hS Z.1 Z.2) U
  Stacks.SheafOfModules.globalSectionToEnd (structureRingSheaf B S hS Z) a

variable {B S hS} {X Y : AlgebraicSpaces B S hS}

/-- The rings of sections of the structure sheaf of an algebraic space are commutative. -/
private theorem isMulCommutative_structureRingSheaf_obj (Z : AlgebraicSpaces B S hS) :
    ∀ U, IsMulCommutative ((structureRingSheaf B S hS Z).obj.obj U) := fun U ↦
  RingedSite.ringSheafSectionsIsMulCommutative (smallEtaleRingedSite B S hS Z.1 Z.2) U

/-- Two global regular functions `a` on `Y` and `b` on `X` are *compatible along* `f : X ⟶ Y`
when, for every étale chart `V` of `Y` and every étale chart of `X` above `X ×_Y V`, the value of
`b` on the chart of `X` is the pullback of the value of `a` on `V`. -/
def GlobalFunctionsCompatible (f : X ⟶ Y)
    (a : ((structureRingSheaf B S hS Y).obj ⋙ forget RingCat).sections)
    (b : ((structureRingSheaf B S hS X).obj ⋙ forget RingCat).sections) : Prop :=
  ∀ (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op),
    b.val j.right = chartPullback B S hS f V j (a.val (op V))

/-- **Direct image carries multiplication by a global function to multiplication by a
compatible one.**  If `b` on `X` is compatible with `a` on `Y` along `f`, then the direct image
along `f` carries multiplication by `b` to multiplication by `a`. -/
theorem modulePushforward_map_globalFunctionSMul (f : X ⟶ Y)
    (a : ((structureRingSheaf B S hS Y).obj ⋙ forget RingCat).sections)
    (b : ((structureRingSheaf B S hS X).obj ⋙ forget RingCat).sections)
    (h : GlobalFunctionsCompatible f a b) (N : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS f).map ((globalFunctionSMul B S hS X b).asHom.app N) =
      (globalFunctionSMul B S hS Y a).asHom.app ((modulePushforward B S hS f).obj N) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V ↦ ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  have hP : PreservesFiniteProducts (smallEtaleDirectImage B S hS f ⋙
      Sheaf.sectionsFunctor.{u} (SmallEtale.topology B S hS Y.1) (op V.unop)) := inferInstance
  refine moduleChartProjection_ext B S hS f V.unop (moduleSetSheaf B S hS X N) fun j ↦ ?_
  have hQ : PreservesFiniteProducts (Sheaf.sectionsFunctor.{u}
      (SmallEtale.topology B S hS X.1) j.right) := inferInstance
  have hR : (SmallEtale.topology B S hS X.1).HasSheafCompose (forget RingCat.{u}) :=
    inferInstance
  have hA : (SmallEtale.topology B S hS X.1).HasSheafCompose (forget AddCommGrpCat.{u}) :=
    inferInstance
  have e1 := Functor.natTrans_app_map_apply (moduleChartProjection B S hS f V.unop j)
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
      ((globalFunctionSMul B S hS X b).asHom.app N)) x
  have e2 := @Sheaf.moduleSMulObj_naturality _ _ _ hR hA
    (structureRingSheaf B S hS X) N _ hP _ hQ
    (moduleChartProjection B S hS f V.unop j)
    (((structureSharp B S hS f).hom.app V).hom (a.val V) : ((smallEtaleDirectImage B S hS f ⋙
        Sheaf.sectionsFunctor.{u} (SmallEtale.topology B S hS Y.1) (op V.unop)).obj
      (structureSetSheaf B S hS X))) x
  have e3 := (moduleChartProjection_app_structureSharp B S hS f V.unop j (a.val V)).trans
    (h V.unop j).symm
  refine e1.trans (Eq.trans ?_ e2.symm)
  refine Eq.trans ?_ (congrArg (fun r ↦ Sheaf.moduleSMulObj (structureRingSheaf B S hS X) N
    (Sheaf.sectionsFunctor.{u} (SmallEtale.topology B S hS X.1) j.right) r
    ((moduleChartProjection B S hS f V.unop j).app (moduleSetSheaf B S hS X N) x)) e3).symm
  exact (Sheaf.sectionsFunctor_map_moduleSMulHom (structureRingSheaf B S hS X) N j.right _ _).symm

/-- **Inverse image carries multiplication by a global function to multiplication by a
compatible one.**  If `b` on `X` is compatible with `a` on `Y` along `f`, then the inverse image
along `f` carries multiplication by `a` to multiplication by `b`. -/
theorem modulePullback_map_globalFunctionSMul (f : X ⟶ Y)
    (a : ((structureRingSheaf B S hS Y).obj ⋙ forget RingCat).sections)
    (b : ((structureRingSheaf B S hS X).obj ⋙ forget RingCat).sections)
    (h : GlobalFunctionsCompatible f a b) (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS f).map ((globalFunctionSMul B S hS Y a).asHom.app M) =
      (globalFunctionSMul B S hS X b).asHom.app ((modulePullback B S hS f).obj M) :=
  (modulePullbackAdjunction B S hS f).map_endOfId
    (fun N ↦ modulePushforward_map_globalFunctionSMul f a b h N) M

/-! ### Endomorphisms of an invertible module are multiplications by global functions -/

section Invertible

variable (Z : AlgebraicSpaces B S hS)

/-- Tensoring on the right by a module, on the small étale site of an algebraic space. -/
abbrev tensorRightModule (L : Modules.{u, u} B S hS Z.1 Z.2) :
    Modules.{u, u} B S hS Z.1 Z.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2 :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
    (smallEtaleRingedSite B S hS Z.1 Z.2).O).flip.obj L

/-- Tensoring on the right by an invertible module is fully faithful. -/
def tensorRightModuleFullyFaithful (L : Modules.{u, u} B S hS Z.1 Z.2)
    (hL : IsInvertibleModule Z L) : (tensorRightModule Z L).FullyFaithful :=
  haveI := hL
  haveI : (tensorRightModule Z L).IsEquivalence :=
    isEquivalence_tensorRightFunctor B S hS Z.1 Z.2 L
  Functor.FullyFaithful.ofFullyFaithful _

/-- Tensoring on the right by a module commutes with multiplication by a global function. -/
theorem tensorRightModule_map_globalFunctionSMul (L : Modules.{u, u} B S hS Z.1 Z.2)
    (a : ((structureRingSheaf B S hS Z).obj ⋙ forget RingCat).sections)
    (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (tensorRightModule Z L).map ((globalFunctionSMul B S hS Z a).asHom.app M) =
      (globalFunctionSMul B S hS Z a).asHom.app ((tensorRightModule Z L).obj M) :=
  have := isMulCommutative_structureRingSheaf_obj Z
  SheafOfModules.sheafTensorRight_map_globalSectionToEnd (C := SmallEtale B S hS Z.1)
    (J := SmallEtale.topology B S hS Z.1) (smallEtaleRingedSite B S hS Z.1 Z.2).O L a M

/-- The global function that an endomorphism of the structure module is multiplication by: its
value at `1` on every chart. -/
def unitEndGlobalFunction (ψ : structureModule Z ⟶ structureModule Z) :
    ((structureRingSheaf B S hS Z).obj ⋙ forget RingCat).sections :=
  ⟨fun U ↦ ψ.val.app U (1 : (structureRingSheaf B S hS Z).obj.obj U), fun {U V} i ↦ by
    have h := congrArg (fun φ ↦ φ.hom (1 : (structureRingSheaf B S hS Z).obj.obj U))
      (ψ.val.naturality i)
    exact h.symm.trans
      (congrArg (ψ.val.app V).hom (map_one ((structureRingSheaf B S hS Z).obj.map i).hom))⟩

/-- An endomorphism of the structure module is multiplication by its value at `1`. -/
theorem eq_globalFunctionSMul_unitEndGlobalFunction
    (ψ : structureModule Z ⟶ structureModule Z) :
    ψ = (globalFunctionSMul B S hS Z (unitEndGlobalFunction Z ψ)).asHom.app (structureModule Z) := by
  have := isMulCommutative_structureRingSheaf_obj Z
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦ ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  let r : (structureRingSheaf B S hS Z).obj.obj U := (unitEndGlobalFunction Z ψ).val U
  have h : ψ.val.app U x = (show (structureRingSheaf B S hS Z).obj.obj U from x) * r := by
    have h0 := (ψ.val.app U).hom.map_smul (show (structureRingSheaf B S hS Z).obj.obj U from x)
      (1 : (structureRingSheaf B S hS Z).obj.obj U)
    exact (congrArg (ψ.val.app U).hom
      (mul_one (show (structureRingSheaf B S hS Z).obj.obj U from x)).symm).trans h0
  show ψ.val.app U x = r * (show (structureRingSheaf B S hS Z).obj.obj U from x)
  rw [h]
  exact (RingedSite.ringSheafSectionsIsMulCommutative (smallEtaleRingedSite B S hS Z.1 Z.2)
    U).is_comm.comm _ _

/-- Multiplication by a global function on the structure module determines the function. -/
theorem globalFunctionSMul_injective_structureModule
    {b c : ((structureRingSheaf B S hS Z).obj ⋙ forget RingCat).sections}
    (h : (globalFunctionSMul B S hS Z b).asHom.app (structureModule Z) =
      (globalFunctionSMul B S hS Z c).asHom.app (structureModule Z)) : b = c := by
  refine Subtype.ext (funext fun U ↦ ?_)
  have h1 := congrArg (fun φ : structureModule Z ⟶ structureModule Z ↦
    φ.val.app U (1 : (structureRingSheaf B S hS Z).obj.obj U)) h
  change b.val U • (1 : (structureRingSheaf B S hS Z).obj.obj U) =
    c.val U • (1 : (structureRingSheaf B S hS Z).obj.obj U) at h1
  simpa using h1

/-- **On an invertible module, multiplication by a global function determines the function.** -/
theorem globalFunctionSMul_injective_of_isInvertibleModule (L : Modules.{u, u} B S hS Z.1 Z.2)
    (hL : IsInvertibleModule Z L)
    {b c : ((structureRingSheaf B S hS Z).obj ⋙ forget RingCat).sections}
    (h : (globalFunctionSMul B S hS Z b).asHom.app L = (globalFunctionSMul B S hS Z c).asHom.app L) :
    b = c := by
  refine globalFunctionSMul_injective_structureModule Z
    ((tensorRightModuleFullyFaithful Z L hL).map_injective ?_)
  let ι : (tensorRightModule Z L).obj (structureModule Z) ≅ L :=
    SheafOfModules.sheafTensorRightUnitIso (C := SmallEtale B S hS Z.1)
      (J := SmallEtale.topology B S hS Z.1) (smallEtaleRingedSite B S hS Z.1 Z.2).O L
  rw [tensorRightModule_map_globalFunctionSMul, tensorRightModule_map_globalFunctionSMul]
  have hb := (globalFunctionSMul B S hS Z b).asHom.naturality ι.hom
  have hc := (globalFunctionSMul B S hS Z c).asHom.naturality ι.hom
  simp only [Functor.id_map] at hb hc
  rw [← Iso.cancel_iso_hom_right _ _ ι, ← hb, ← hc, h]

/-- **Every endomorphism of an invertible module is multiplication by a global function.** -/
theorem exists_eq_globalFunctionSMul_of_isInvertibleModule (L : Modules.{u, u} B S hS Z.1 Z.2)
    (hL : IsInvertibleModule Z L) (φ : L ⟶ L) :
    ∃ b, φ = (globalFunctionSMul B S hS Z b).asHom.app L := by
  let ι : (tensorRightModule Z L).obj (structureModule Z) ≅ L :=
    SheafOfModules.sheafTensorRightUnitIso (C := SmallEtale B S hS Z.1)
      (J := SmallEtale.topology B S hS Z.1) (smallEtaleRingedSite B S hS Z.1 Z.2).O L
  let ψ := (tensorRightModuleFullyFaithful Z L hL).preimage (ι.hom ≫ φ ≫ ι.inv)
  refine ⟨unitEndGlobalFunction Z ψ, ?_⟩
  have hψ : (tensorRightModule Z L).map ψ = ι.hom ≫ φ ≫ ι.inv :=
    (tensorRightModuleFullyFaithful Z L hL).map_preimage _
  rw [eq_globalFunctionSMul_unitEndGlobalFunction Z ψ,
    tensorRightModule_map_globalFunctionSMul] at hψ
  have hb := (globalFunctionSMul B S hS Z (unitEndGlobalFunction Z ψ)).asHom.naturality ι.hom
  simp only [Functor.id_map] at hb
  rw [← Iso.cancel_iso_hom_left ι, hb, hψ, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

end Invertible

/-! ### Global functions pulled back along a morphism are compatible -/

/-- **Pullback of global functions along `f` is compatible along `f`**: the pullback of a global
function `a` of `Y` along `f` is compatible with `a` along `f`. -/
theorem globalFunctionsCompatible_globalFunctionsMap (f : X ⟶ Y)
    (a : ((structureRingSheaf B S hS Y).obj ⋙ forget RingCat).sections) :
    GlobalFunctionsCompatible f a (globalFunctionsMap B S hS f a) := by
  intro V j
  have h1 := (globalFunctionsChartEquiv B S hS Y).property a
  let k : (CostructuredArrow.map f.hom).obj
      ((SmallEtale.inclusion B S hS X.1).obj j.right.unop) ⟶
        (SmallEtale.inclusion B S hS Y.1).obj V :=
    CostructuredArrow.homMk (chartBaseChangeMap B S hS f V j)
      (chartBaseChangeMap_comm B S hS f j.right.unop V j.hom.unop).symm
  have h2 := ((globalFunctionsChartEquiv B S hS Y).val a).property k.op
  exact h2.symm.trans
    (congrArg (chartPullback B S hS f V j) (congrArg (fun s ↦ s.val (op V)) h1))

/-! ### Regular functions on a test scheme as global functions -/

/-- The all-chart family of regular functions of the algebraic space of a scheme `T` attached to
a regular function on `T`: on a scheme chart it is the pullback along the chart. -/
def schemeChartFunctions (T : BigFppfOver B S hS) :
    Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)) →+*
      chartFunctions B S hS ((schemeSpaceFunctor B S hS).obj T).1 where
  toFun u := ⟨fun j ↦ (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage j.unop.hom)).op).hom u, by
    intro j k g
    have hk : yoneda.preimage k.unop.hom = g.unop.left ≫ yoneda.preimage j.unop.hom :=
      yoneda.map_injective ((yoneda.map_preimage _).trans
        ((CostructuredArrow.w g.unop).symm.trans
          ((congrArg (fun m ↦ yoneda.map g.unop.left ≫ m) (yoneda.map_preimage _).symm).trans
            (yoneda.map_comp _ _).symm)))
    change (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g.unop.left).op).hom
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage j.unop.hom)).op).hom u) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (yoneda.preimage k.unop.hom)).op).hom u
    rw [hk, Functor.map_comp, op_comp, Functor.map_comp, CommRingCat.hom_comp,
      RingHom.comp_apply]⟩
  map_one' := Subtype.ext (funext fun _ ↦ map_one _)
  map_mul' a b := Subtype.ext (funext fun _ ↦ map_mul _ a b)
  map_zero' := Subtype.ext (funext fun _ ↦ map_zero _)
  map_add' a b := Subtype.ext (funext fun _ ↦ map_add _ a b)

/-- A regular function on a scheme `T` of the site, as a global regular function of the
algebraic space that `T` represents. -/
def schemeGlobalFunctions (T : BigFppfOver B S hS) :
    Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)) →+*
      globalFunctions' B S hS ((schemeSpaceFunctor B S hS).obj T).1 :=
  (chartFunctionsToSmall B S hS ((schemeSpaceFunctor B S hS).obj T).1).comp
    (schemeChartFunctions T)

/-- The global function attached to a regular function on `T` takes the value of that function
on the identity chart. -/
theorem schemeGlobalFunctions_idEtaleChart (T : BigFppfOver B S hS)
    (u : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T))) :
    (schemeGlobalFunctions T u).val (op (idEtaleChart B S hS T)) = u := by
  show (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (𝟙 (yoneda.obj T)))).op).hom u = u
  rw [Functor.preimage_id, CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **Regular functions on test schemes and their pullback.**  The global function attached to
the pullback of `u` along `g : T ⟶ T'` is the pullback along the induced morphism of algebraic
spaces of the global function attached to `u`. -/
theorem globalFunctionsMap_schemeGlobalFunctions {T T' : BigFppfOver B S hS} (g : T ⟶ T')
    (u : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T'))) :
    globalFunctionsMap B S hS ((schemeSpaceFunctor B S hS).map g) (schemeGlobalFunctions T' u) =
      schemeGlobalFunctions T ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom u) := by
  have hc : ∀ (Z : BigFppfOver B S hS)
      (c : chartFunctions B S hS ((schemeSpaceFunctor B S hS).obj Z).1),
      (globalFunctionsChartEquiv B S hS ((schemeSpaceFunctor B S hS).obj Z)).val
        (chartFunctionsToSmall B S hS ((schemeSpaceFunctor B S hS).obj Z).1 c) = c := fun Z c ↦
    (RingEquiv.ofBijective _
      (chartFunctionsToSmall_bijective B S hS _
        ((schemeSpaceFunctor B S hS).obj Z).property)).symm_apply_apply c
  refine (globalFunctionsChartEquiv B S hS ((schemeSpaceFunctor B S hS).obj T)).val.injective ?_
  rw [globalFunctionsMap_chart]
  show chartFunctionsMap B S hS (yoneda.map g)
      ((globalFunctionsChartEquiv B S hS ((schemeSpaceFunctor B S hS).obj T')).val
        (chartFunctionsToSmall B S hS ((schemeSpaceFunctor B S hS).obj T').1
          (schemeChartFunctions T' u))) =
    (globalFunctionsChartEquiv B S hS ((schemeSpaceFunctor B S hS).obj T)).val
        (chartFunctionsToSmall B S hS ((schemeSpaceFunctor B S hS).obj T).1
          (schemeChartFunctions T _))
  rw [hc, hc]
  refine Subtype.ext (funext fun j ↦ ?_)
  have hj : yoneda.preimage (j.unop.hom ≫ yoneda.map g) =
      yoneda.preimage j.unop.hom ≫ g :=
    yoneda.map_injective ((yoneda.map_preimage _).trans
      ((congrArg (fun m ↦ m ≫ yoneda.map g) (yoneda.map_preimage _).symm).trans
        (yoneda.map_comp _ _).symm))
  show (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (j.unop.hom ≫ yoneda.map g))).op).hom u =
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (yoneda.preimage j.unop.hom)).op).hom
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom u)
  rw [hj, Functor.map_comp, op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]

/-- The global functions of the base change `X_T` attached to the regular functions on a test
scheme `T`: pullback along the projection `X_T ⟶ T`. -/
def baseChangeGlobalFunctions (f : X ⟶ Y) (T : SchemesOver Y) :
    Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T.left)) →+*
      globalFunctions' B S hS (baseChangeSpace f T).1 :=
  (globalFunctionsMap B S hS (baseChangeInclusion f T)).comp (schemeGlobalFunctions T.left)

/-- **The global functions attached to a test scheme are compatible along the morphisms of base
changes.**  For `g : T ⟶ T'`, the global function of `X_T` attached to the pullback of `u` along
`g` is compatible, along `X_T ⟶ X_{T'}`, with the global function of `X_{T'}` attached to `u`. -/
theorem globalFunctionsCompatible_baseChangeGlobalFunctions (f : X ⟶ Y) {T T' : SchemesOver Y}
    (g : T ⟶ T') (u : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T'.left))) :
    GlobalFunctionsCompatible (baseChangeMap f g) (baseChangeGlobalFunctions f T' u)
      (baseChangeGlobalFunctions f T
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g.left).op).hom u)) := by
  have e : baseChangeGlobalFunctions f T
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g.left).op).hom u) =
      globalFunctionsMap B S hS (baseChangeMap f g) (baseChangeGlobalFunctions f T' u) := by
    show globalFunctionsMap B S hS (baseChangeInclusion f T)
        (schemeGlobalFunctions T.left _) = _
    rw [← globalFunctionsMap_schemeGlobalFunctions, ← RingHom.comp_apply,
      ← globalFunctionsMap_comp, ← baseChangeMap_comp_inclusion, globalFunctionsMap_comp]
    rfl
  rw [e]
  exact globalFunctionsCompatible_globalFunctionsMap _ _

/-- The global functions attached to a test scheme are the pullbacks of regular functions along
the morphisms of schemes from the étale charts of `X_T` to `T`: on each chart they are the
comparison `AlgebraicGeometry.Space.terminalChartPullback` with the identity chart of `T`. -/
theorem baseChangeGlobalFunctions_eq_terminalChartPullback (f : X ⟶ Y) (T : SchemesOver Y)
    (u : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T.left))) :
    (baseChangeGlobalFunctions f T u : globalFunctions B S hS (baseChangeSpace f T).1) =
      terminalChartPullback B S hS (baseChangeInclusion f T) (idEtaleChart B S hS T.left)
        (by change IsIso (𝟙 ((schemeSpaceFunctor B S hS).obj T.left)); infer_instance) u := by
  refine Subtype.ext (funext fun U ↦ ?_)
  have h := globalFunctionsCompatible_globalFunctionsMap (baseChangeInclusion f T)
    (schemeGlobalFunctions T.left u) (idEtaleChart B S hS T.left)
    (terminalChartIndex B S hS (baseChangeInclusion f T) (idEtaleChart B S hS T.left)
      (by change IsIso (𝟙 ((schemeSpaceFunctor B S hS).obj T.left)); infer_instance) U.unop)
  exact h.trans (congrArg _ (schemeGlobalFunctions_idEtaleChart T.left u))

/-! ### Products of multiplications by global functions -/

/-- Multiplication by `b` followed by multiplication by `c` is multiplication by `c * b`. -/
theorem globalFunctionSMul_app_comp (Z : AlgebraicSpaces B S hS)
    (b c d : ((structureRingSheaf B S hS Z).obj ⋙ forget RingCat).sections)
    (h : ∀ U, d.val U = c.val U * b.val U) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (globalFunctionSMul B S hS Z b).asHom.app M ≫ (globalFunctionSMul B S hS Z c).asHom.app M =
      (globalFunctionSMul B S hS Z d).asHom.app M := by
  have := isMulCommutative_structureRingSheaf_obj Z
  exact (congrArg (fun e : End (𝟭 (Modules.{u, u} B S hS Z.1 Z.2)) ↦ e.asHom.app M)
    (Stacks.SheafOfModules.globalSectionToEnd_mul_of_val (structureRingSheaf B S hS Z)
      c b d h)).symm

/-- Multiplication by the global function `1` is the identity. -/
theorem globalFunctionSMul_app_eq_id (Z : AlgebraicSpaces B S hS)
    (b : ((structureRingSheaf B S hS Z).obj ⋙ forget RingCat).sections) (h : ∀ U, b.val U = 1)
    (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (globalFunctionSMul B S hS Z b).asHom.app M = 𝟙 M := by
  have := isMulCommutative_structureRingSheaf_obj Z
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦ ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  refine (Stacks.SheafOfModules.globalSectionToEnd_apply (structureRingSheaf B S hS Z) b M U
    x).trans ?_
  rw [h U]
  exact one_smul ((structureRingSheaf B S hS Z).obj.obj U) _

end AlgebraicGeometry.Space
