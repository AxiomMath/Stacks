module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicPictureChain
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ModuleAlgebraData
public import StacksFrontier.AlgebraicGeometry.EtaleAlgebra.FlatBaseChange.AlgebraComparison
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.ComparisonSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicPictureBridges

/-!
# The canonical algebra-pullback comparison is multiplicative and unital

For a morphism of schemes `g : T ⟶ S` and an algebra sheaf `E` on `S`, an
`AlgebraicGeometry.AlgebraPullbackModuleIso g E` consists of an isomorphism of `𝒪_T`-modules
identifying the module underlying `g⁻¹E ⊗_{g⁻¹𝒪_S} 𝒪_T` with `g^*` of the module underlying `E`,
together with two equations saying that it intertwines the multiplications and the structure
morphisms. This file proves both equations for the canonical comparison
`Stacks.FundamentalGroup.algebraPullbackModuleComparison g E`, the adjoint transpose of the module
underlying the unit of `Stacks.AffineAlgebraEquivalence.algebraPullbackPushforwardAdjunction`, so
that such a datum is produced from the invertibility of that comparison alone.

The unit of an adjunction of algebra sheaves is a morphism of sheaves of commutative rings, so on
sections it is a ring homomorphism (`AlgebraicGeometry.algebraPullbackUnitSection_mulSection`,
`AlgebraicGeometry.algebraPullbackUnitSection_oneSection`). Both equations are reduced to this:
a morphism out of a pullback is determined by its adjoint transpose, and a morphism out of a
sheafified tensor product by its values on pure tensors of local sections, on which the
comparison of [Stacks, Tag 01CD] computes
(`Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso_hom_modulesPullbackUnit`).

## Main definitions

* `AlgebraicGeometry.algebraPullbackUnitSection`: the unit of the base-change adjunction for
  algebra sheaves, read on sections; a homomorphism of commutative rings.
* `AlgebraicGeometry.algebraPullbackModuleIsoOfIsIso`: the datum
  `AlgebraicGeometry.AlgebraPullbackModuleIso g E` from the invertibility of the canonical
  comparison.
* `AlgebraicGeometry.algebraPullbackModuleIso_of_isIso_comparison`: the same for all `g` and all
  quasi-coherent `E` at once.

## Main results

* `AlgebraicGeometry.hom_ext_modulesPullbackUnit`: two morphisms out of a module pullback
  agreeing on the pullback-unit images of local sections are equal.
* `AlgebraicGeometry.schemePullbackTensorIso_comp_multiplication`: the canonical comparison
  intertwines the multiplications.
* `AlgebraicGeometry.pullback_map_unitModuleMap_comp_comparison`: the canonical comparison
  intertwines the structure morphisms.
* `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_isIso_comparison`:
  `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_moduleAlgebraData` with its `hpullback`
  hypothesis replaced by the invertibility of the canonical comparison.

## Implementation notes

The proofs are in term mode wherever a goal mentions `AlgebraicGeometry.Scheme.Modules` or
`SheafOfModules.unit X.ringCatSheaf`: those goals are not type-correct at `implicit`
transparency (`AlgebraicGeometry.Scheme.ringCatSheaf` is a `TopCat.Sheaf RingCat ↑X` where
`CategoryTheory.SheafOfModules` expects a `CategoryTheory.Sheaf (Opens.grothendieckTopology ↥X)
RingCat`), so `rw`, `change` and `simp` cannot build a motive on them, while `Eq.trans`,
`congrArg` and `exact` check at default transparency.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 0A42](https://stacks.math.columbia.edu/tag/0A42)
* [Stacks Project, Tag 0899](https://stacks.math.columbia.edu/tag/0899)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.RelativeSpec (AlgebraSheaf)
open Stacks.AffineAlgebraEquivalence
open Stacks.FundamentalGroup (algebraPullbackModuleComparison)
open Stacks.Tag01VSPullbackTensor (modulesPullbackUnit schemePullbackTensorIso tensorSheafMapIso
  tensorSheafMapIso_hom_toTensorSheafSection schemePullbackTensorIso_hom_modulesPullbackUnit)
open Stacks.SheafOfModules.TensorStalkRingedSpace (hom_ext_toTensorSheafSection
  toTensorSheafSection)

universe u

namespace AlgebraicGeometry

variable {T S : Scheme.{u}} (g : T ⟶ S)

/-! ### Morphisms out of a module pullback, and the unit of the adjunction on sections -/

/-- **Two morphisms out of a module pullback agreeing on the pullback-unit images of local
sections are equal.** A morphism out of `g ^* M` is determined by its adjoint transpose, and the
transpose is read on sections by precomposition with the unit of `g ^* ⊣ g_*`. -/
theorem hom_ext_modulesPullbackUnit {M : S.Modules} {N : T.Modules}
    (a b : (Scheme.Modules.pullback g).obj M ⟶ N)
    (h : ∀ (U : S.Opens) (x : Γ(M, U)),
      Scheme.Modules.Hom.app a (g ⁻¹ᵁ U) (modulesPullbackUnit g M U x) =
        Scheme.Modules.Hom.app b (g ⁻¹ᵁ U) (modulesPullbackUnit g M U x)) :
    a = b := by
  refine ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv M N).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => h U x)

/-- The unit of `g ^* ⊣ g_*` is natural: the pullback of a morphism carries the pullback-unit
image of a section to the pullback-unit image of its image. -/
theorem modulesPullbackUnit_pullback_map {M N : S.Modules} (φ : M ⟶ N) (U : S.Opens)
    (x : Γ(M, U)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullback g).map φ) (g ⁻¹ᵁ U)
        (modulesPullbackUnit g M U x) =
      modulesPullbackUnit g N U (Scheme.Modules.Hom.app φ U x) :=
  congrArg (fun k => Scheme.Modules.Hom.app k U x)
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality φ).symm

/-! ### The comparison on pullback-unit sections is the algebra unit on sections -/

/-- The section of `g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` over `g⁻¹U` attached to a section of `A` over `U`: the
unit of `Stacks.AffineAlgebraEquivalence.algebraPullbackPushforwardAdjunction` read on sections,
which is a homomorphism of commutative rings. -/
def algebraPullbackUnitSection (E : AlgebraSheaf S) (U : S.Opens)
    (x : Γ(AlgebraSheaf.underlyingModule E, U)) :
    Γ(AlgebraSheaf.underlyingModule ((algebraPullback g).obj E), g ⁻¹ᵁ U) :=
  Scheme.Modules.Hom.app (AlgebraSheaf.underlyingModuleMap
    ((algebraPullbackPushforwardAdjunction g).unit.app E)) U x

/-- **The canonical comparison carries the pullback-unit image of a section to the image of that
section under the unit of the base-change adjunction for algebra sheaves.** -/
theorem algebraPullbackModuleComparison_modulesPullbackUnit (E : AlgebraSheaf S) (U : S.Opens)
    (x : Γ(AlgebraSheaf.underlyingModule E, U)) :
    Scheme.Modules.Hom.app (algebraPullbackModuleComparison g E) (g ⁻¹ᵁ U)
        (modulesPullbackUnit g (AlgebraSheaf.underlyingModule E) U x) =
      algebraPullbackUnitSection g E U x :=
  congrArg (fun φ : AlgebraSheaf.underlyingModule E ⟶ (Scheme.Modules.pushforward g).obj
      (AlgebraSheaf.underlyingModule ((algebraPullback g).obj E)) =>
    Scheme.Modules.Hom.app φ U x)
    (Stacks.FundamentalGroup.homEquiv_algebraPullbackModuleComparison g E)

/-- The unit of the base-change adjunction for algebra sheaves is multiplicative on sections. -/
theorem algebraPullbackUnitSection_mulSection (E : AlgebraSheaf S) (U : S.Opens)
    (x y : Γ(AlgebraSheaf.underlyingModule E, U)) :
    algebraPullbackUnitSection g E U (AlgebraSheaf.mulSection E (op U) x y) =
      AlgebraSheaf.mulSection ((algebraPullback g).obj E) (op (g ⁻¹ᵁ U))
        (algebraPullbackUnitSection g E U x) (algebraPullbackUnitSection g E U y) :=
  AlgebraSheaf.underlyingModuleMap_mulSection
    ((algebraPullbackPushforwardAdjunction g).unit.app E) (op U) x y

/-- The unit of the base-change adjunction for algebra sheaves is unital on sections. -/
theorem algebraPullbackUnitSection_oneSection (E : AlgebraSheaf S) (U : S.Opens) :
    algebraPullbackUnitSection g E U (AlgebraSheaf.oneSection E (op U)) =
      AlgebraSheaf.oneSection ((algebraPullback g).obj E) (op (g ⁻¹ᵁ U)) :=
  AlgebraSheaf.underlyingModuleMap_oneSection
    ((algebraPullbackPushforwardAdjunction g).unit.app E) (op U)

/-- The multiplication of an algebra sheaf on a pure tensor of local sections, in the
`AlgebraicGeometry.Scheme.Modules.Hom.app` spelling of the action on sections. -/
theorem multiplication_app_toTensorSheafSection {X : Scheme.{u}} (A : AlgebraSheaf X) (U : X.Opens)
    (x y : Γ(AlgebraSheaf.underlyingModule A, U)) :
    Scheme.Modules.Hom.app (AlgebraSheaf.multiplication A) U
        (toTensorSheafSection X.toRingedSpace (AlgebraSheaf.underlyingModule A)
          (AlgebraSheaf.underlyingModule A) (op U) (x ⊗ₜ[X.presheaf.obj (op U)] y)) =
      AlgebraSheaf.mulSection A (op U) x y :=
  AlgebraSheaf.multiplication_tmul A (op U) x y

/-! ### The multiplication half -/

/-- The pullback of the multiplication of `E`, on the pullback-unit image of a pure tensor of
local sections of the module underlying `E`. -/
theorem pullback_map_multiplication_modulesPullbackUnit (E : AlgebraSheaf S) (U : S.Opens)
    (x y : Γ(AlgebraSheaf.underlyingModule E, U)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullback g).map (AlgebraSheaf.multiplication E))
        (g ⁻¹ᵁ U) (modulesPullbackUnit g _ U
          (toTensorSheafSection S.toRingedSpace (AlgebraSheaf.underlyingModule E)
            (AlgebraSheaf.underlyingModule E) (op U) (x ⊗ₜ[S.presheaf.obj (op U)] y))) =
      modulesPullbackUnit g (AlgebraSheaf.underlyingModule E) U
        (AlgebraSheaf.mulSection E (op U) x y) :=
  (modulesPullbackUnit_pullback_map g (AlgebraSheaf.multiplication E) U _).trans
    (congrArg (modulesPullbackUnit g (AlgebraSheaf.underlyingModule E) U)
      (AlgebraSheaf.multiplication_tmul E (op U) x y))

/-- The two sides of the multiplicativity equation, on the pullback-unit image of a pure tensor
of local sections. -/
theorem comparison_multiplication_section (E : AlgebraSheaf S)
    [IsIso (algebraPullbackModuleComparison g E)] (U : S.Opens)
    (x y : Γ(AlgebraSheaf.underlyingModule E, U)) :
    Scheme.Modules.Hom.app (AlgebraSheaf.multiplication ((algebraPullback g).obj E)) (g ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app (tensorSheafMapIso
            (asIso (algebraPullbackModuleComparison g E))
            (asIso (algebraPullbackModuleComparison g E))).hom (g ⁻¹ᵁ U)
          (Scheme.Modules.Hom.app (schemePullbackTensorIso g
              (AlgebraSheaf.underlyingModule E) (AlgebraSheaf.underlyingModule E)).hom (g ⁻¹ᵁ U)
            (modulesPullbackUnit g _ U
              (toTensorSheafSection S.toRingedSpace (AlgebraSheaf.underlyingModule E)
                (AlgebraSheaf.underlyingModule E) (op U)
                (x ⊗ₜ[S.presheaf.obj (op U)] y))))) =
      Scheme.Modules.Hom.app (algebraPullbackModuleComparison g E) (g ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullback g).map (AlgebraSheaf.multiplication E))
          (g ⁻¹ᵁ U) (modulesPullbackUnit g _ U
            (toTensorSheafSection S.toRingedSpace (AlgebraSheaf.underlyingModule E)
              (AlgebraSheaf.underlyingModule E) (op U)
              (x ⊗ₜ[S.presheaf.obj (op U)] y)))) := by
  rw [schemePullbackTensorIso_hom_modulesPullbackUnit,
    tensorSheafMapIso_hom_toTensorSheafSection]
  simp only [asIso_hom]
  rw [algebraPullbackModuleComparison_modulesPullbackUnit,
    algebraPullbackModuleComparison_modulesPullbackUnit,
    multiplication_app_toTensorSheafSection,
    pullback_map_multiplication_modulesPullbackUnit]
  exact (algebraPullbackUnitSection_mulSection g E U x y).symm.trans
    (algebraPullbackModuleComparison_modulesPullbackUnit g E U
      (AlgebraSheaf.mulSection E (op U) x y)).symm

/-- **The canonical comparison intertwines the multiplication of the algebra pullback with the
pullback of the multiplication of `E`.** -/
theorem schemePullbackTensorIso_comp_multiplication (E : AlgebraSheaf S)
    [IsIso (algebraPullbackModuleComparison g E)] :
    (schemePullbackTensorIso g (AlgebraSheaf.underlyingModule E)
          (AlgebraSheaf.underlyingModule E)).hom ≫
        (tensorSheafMapIso (asIso (algebraPullbackModuleComparison g E))
            (asIso (algebraPullbackModuleComparison g E))).hom ≫
          AlgebraSheaf.multiplication ((algebraPullback g).obj E) =
      (Scheme.Modules.pullback g).map (AlgebraSheaf.multiplication E) ≫
        algebraPullbackModuleComparison g E := by
  refine ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective ?_
  refine hom_ext_toTensorSheafSection S.toRingedSpace _ _ fun U x y => ?_
  exact comparison_multiplication_section g E U.unop x y

/-! ### The unit half -/

/-- The structure morphism of a direct image of algebra sheaves is the structure morphism of `g`
followed by the direct image of the structure morphism. -/
theorem unitModuleMap_algebraPushforward (B : AlgebraSheaf T) :
    AlgebraSheaf.unitModuleMap ((algebraPushforward g).obj B) =
      Stacks.AlgebraicGeometry.AffineBaseChange.structureUnitHom g ≫
        (Scheme.Modules.pushforward g).map (AlgebraSheaf.unitModuleMap B) :=
  rfl

/-- **The canonical comparison intertwines the structure morphism of the algebra pullback with
the pullback of the structure morphism of `E`.** -/
theorem pullback_map_unitModuleMap_comp_comparison (E : AlgebraSheaf S) :
    (Scheme.Modules.pullback g).map (AlgebraSheaf.unitModuleMap E) ≫
        algebraPullbackModuleComparison g E =
      (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g).hom ≫
        AlgebraSheaf.unitModuleMap ((algebraPullback g).obj E) := by
  have hL : (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((Scheme.Modules.pullback g).map (AlgebraSheaf.unitModuleMap E) ≫
          algebraPullbackModuleComparison g E) =
      AlgebraSheaf.unitModuleMap ((algebraPushforward g).obj ((algebraPullback g).obj E)) :=
    Eq.trans
      ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_naturality_left
        (AlgebraSheaf.unitModuleMap E) (algebraPullbackModuleComparison g E))
      (Eq.trans
        (congrArg (fun k : AlgebraSheaf.underlyingModule E ⟶ (Scheme.Modules.pushforward g).obj
              (AlgebraSheaf.underlyingModule ((algebraPullback g).obj E)) =>
            AlgebraSheaf.unitModuleMap E ≫ k)
          (Stacks.FundamentalGroup.homEquiv_algebraPullbackModuleComparison g E))
        (AlgebraSheaf.unitModuleMap_comp ((algebraPullbackPushforwardAdjunction g).unit.app E)))
  have hR : (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g).hom ≫
          AlgebraSheaf.unitModuleMap ((algebraPullback g).obj E)) =
      AlgebraSheaf.unitModuleMap ((algebraPushforward g).obj ((algebraPullback g).obj E)) :=
    Eq.trans
      ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_naturality_right
        (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g).hom
        (AlgebraSheaf.unitModuleMap ((algebraPullback g).obj E)))
      (Eq.trans
        (congrArg (fun k : Stacks.AlgebraicGeometry.AffineBaseChange.unitObj S ⟶
              (Scheme.Modules.pushforward g).obj
                (Stacks.AlgebraicGeometry.AffineBaseChange.unitObj T) =>
            k ≫ (Scheme.Modules.pushforward g).map
              (AlgebraSheaf.unitModuleMap ((algebraPullback g).obj E)))
          (Stacks.AlgebraicGeometry.AffineBaseChange.homEquiv_pullbackUnitIso g))
        (unitModuleMap_algebraPushforward g ((algebraPullback g).obj E)).symm)
  exact ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
    (hL.trans hR.symm)

/-! ### The datum from one invertibility -/

/-- The inverse of the comparison undoes the comparison on sections. -/
theorem comparison_inv_comparison_apply (E : AlgebraSheaf S)
    [IsIso (algebraPullbackModuleComparison g E)] (U : S.Opens)
    (z : Γ((Scheme.Modules.pullback g).obj (AlgebraSheaf.underlyingModule E), g ⁻¹ᵁ U)) :
    Scheme.Modules.Hom.app (inv (algebraPullbackModuleComparison g E)) (g ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app (algebraPullbackModuleComparison g E) (g ⁻¹ᵁ U) z) = z :=
  congrArg (fun k : (Scheme.Modules.pullback g).obj (AlgebraSheaf.underlyingModule E) ⟶
      (Scheme.Modules.pullback g).obj (AlgebraSheaf.underlyingModule E) =>
    Scheme.Modules.Hom.app k (g ⁻¹ᵁ U) z)
    (IsIso.hom_inv_id (algebraPullbackModuleComparison g E))

/-- **The multiplicativity equation of `AlgebraicGeometry.AlgebraPullbackModuleIso`, with the
inverse of the comparison folded in.** -/
theorem schemePullbackTensorIso_comp_multiplication_comp_inv (E : AlgebraSheaf S)
    [IsIso (algebraPullbackModuleComparison g E)] :
    (schemePullbackTensorIso g (AlgebraSheaf.underlyingModule E)
          (AlgebraSheaf.underlyingModule E)).hom ≫
        (tensorSheafMapIso (asIso (algebraPullbackModuleComparison g E))
            (asIso (algebraPullbackModuleComparison g E))).hom ≫
          AlgebraSheaf.multiplication ((algebraPullback g).obj E) ≫
            inv (algebraPullbackModuleComparison g E) =
      (Scheme.Modules.pullback g).map (AlgebraSheaf.multiplication E) := by
  exact (Category.assoc _ _ _).symm.trans ((Category.assoc _ _ _).symm.trans
    ((IsIso.comp_inv_eq _).2
      ((Category.assoc _ _ _).trans (schemePullbackTensorIso_comp_multiplication g E))))

/-- **The unitality equation of `AlgebraicGeometry.AlgebraPullbackModuleIso`, with the inverse of
the comparison folded in.** -/
theorem pullbackUnitIso_comp_unitModuleMap_comp_inv (E : AlgebraSheaf S)
    [IsIso (algebraPullbackModuleComparison g E)] :
    (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g).hom ≫
        AlgebraSheaf.unitModuleMap ((algebraPullback g).obj E) ≫
          inv (algebraPullbackModuleComparison g E) =
      (Scheme.Modules.pullback g).map (AlgebraSheaf.unitModuleMap E) := by
  exact (Category.assoc _ _ _).symm.trans
    ((IsIso.comp_inv_eq _).2 (pullback_map_unitModuleMap_comp_comparison g E).symm)

/-- **The inverse of an isomorphism whose forward direction is a bifunctor applied to a pair of
isomorphisms is that bifunctor applied to the pair of inverses**, read through
`CategoryTheory.Functor.uncurry`. -/
private theorem uncurry_map_inv_eq {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
    (F : C₁ ⥤ C₂ ⥤ D) {A A' : C₁} {B B' : C₂}
    {aFwd : A ⟶ A'} {aBwd : A' ⟶ A} {bFwd : B ⟶ B'} {bBwd : B' ⟶ B}
    (e : (Functor.uncurry.obj F).obj (A, B) ≅ (Functor.uncurry.obj F).obj (A', B'))
    (he : e.hom = (Functor.uncurry.obj F).map ((aFwd, bFwd) : (A, B) ⟶ (A', B')))
    (ha : aFwd ≫ aBwd = 𝟙 A) (hb : bFwd ≫ bBwd = 𝟙 B) :
    e.inv = (Functor.uncurry.obj F).map ((aBwd, bBwd) : (A', B') ⟶ (A, B)) := by
  have h : e.hom ≫ (Functor.uncurry.obj F).map ((aBwd, bBwd) : (A', B') ⟶ (A, B)) =
      𝟙 ((Functor.uncurry.obj F).obj (A, B)) := by
    rw [he, ← Functor.map_comp]
    exact (congrArg ((Functor.uncurry.obj F).map (X := (A, B)) (Y := (A, B)))
        (Prod.ext ha hb)).trans ((Functor.uncurry.obj F).map_id (A, B))
  refine Eq.trans (Category.comp_id e.inv).symm ?_
  refine Eq.trans (congrArg (fun z => e.inv ≫ z) h.symm) ?_
  exact e.inv_hom_id_assoc _

/-- **The multiplicativity equation of `AlgebraicGeometry.AlgebraPullbackModuleIso`**, with the
tensor square of the inverse of the comparison written as the image of the pair under
`CategoryTheory.Functor.uncurry` of `Stacks.SheafOfModules.Tensor.sheafTensor`. -/
theorem multiplication_comp_comparison_symm_hom (E : AlgebraSheaf S)
    [IsIso (algebraPullbackModuleComparison g E)] :
    AlgebraSheaf.multiplication ((algebraPullback g).obj E) ≫
        (asIso (algebraPullbackModuleComparison g E)).symm.hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨T.presheaf, T.IsSheaf⟩)).map
            (((asIso (algebraPullbackModuleComparison g E)).symm.hom,
              (asIso (algebraPullbackModuleComparison g E)).symm.hom) : (_, _) ⟶ (_, _))) ≫
        (schemePullbackTensorIso g (AlgebraSheaf.underlyingModule E)
            (AlgebraSheaf.underlyingModule E)).inv ≫
          (Scheme.Modules.pullback g).map (AlgebraSheaf.multiplication E) := by
  have hinv : (tensorSheafMapIso (asIso (algebraPullbackModuleComparison g E))
        (asIso (algebraPullbackModuleComparison g E))).inv =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨T.presheaf, T.IsSheaf⟩)).map
        (((asIso (algebraPullbackModuleComparison g E)).inv,
          (asIso (algebraPullbackModuleComparison g E)).inv) : (_, _) ⟶ (_, _))) :=
    uncurry_map_inv_eq
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨T.presheaf, T.IsSheaf⟩)
      (aFwd := algebraPullbackModuleComparison g E)
      (bFwd := algebraPullbackModuleComparison g E)
      (tensorSheafMapIso (asIso (algebraPullbackModuleComparison g E))
        (asIso (algebraPullbackModuleComparison g E))) rfl
      (IsIso.hom_inv_id (algebraPullbackModuleComparison g E))
      (IsIso.hom_inv_id (algebraPullbackModuleComparison g E))
  refine Eq.trans
    ((Iso.eq_inv_comp (tensorSheafMapIso (asIso (algebraPullbackModuleComparison g E))
        (asIso (algebraPullbackModuleComparison g E)))).mpr
      ((Iso.eq_inv_comp (schemePullbackTensorIso g (AlgebraSheaf.underlyingModule E)
          (AlgebraSheaf.underlyingModule E))).mpr
        (schemePullbackTensorIso_comp_multiplication_comp_inv g E))) ?_
  exact congrArg
    (fun z => z ≫ (schemePullbackTensorIso g (AlgebraSheaf.underlyingModule E)
          (AlgebraSheaf.underlyingModule E)).inv ≫
        (Scheme.Modules.pullback g).map (AlgebraSheaf.multiplication E))
    hinv

/-- **The datum `AlgebraicGeometry.AlgebraPullbackModuleIso g E` from the invertibility of the
canonical comparison**, with the inverse of the comparison as its isomorphism. -/
def algebraPullbackModuleIsoOfIsIso (E : AlgebraSheaf S)
    [IsIso (algebraPullbackModuleComparison g E)] : AlgebraPullbackModuleIso g E where
  iso := (asIso (algebraPullbackModuleComparison g E)).symm
  multiplication_comp_iso_hom := multiplication_comp_comparison_symm_hom g E
  unitModuleMap_comp_iso_hom :=
    (Iso.eq_inv_comp (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g)).mpr
      (pullbackUnitIso_comp_unitModuleMap_comp_inv g E)

/-! ### All algebra sheaves at once -/

section Chain

open Stacks.Algebraization (HasProperSupport)

/-- An `AlgebraicGeometry.AlgebraPullbackModuleIso g E` for every morphism of schemes `g` and
every quasi-coherent algebra sheaf `E`, given that the canonical comparison
`Stacks.FundamentalGroup.algebraPullbackModuleComparison g E` is invertible for all of them. -/
def algebraPullbackModuleIso_of_isIso_comparison
    (hcomparison : ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
      AlgebraSheaf.IsQuasicoherent E → IsIso (algebraPullbackModuleComparison g E)) :
    ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
      AlgebraSheaf.IsQuasicoherent E → AlgebraPullbackModuleIso g E :=
  fun g E hE => @algebraPullbackModuleIsoOfIsIso _ _ g E (hcomparison g E hE)

/-- `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_moduleAlgebraData` with its
`hpullback` hypothesis replaced by the invertibility of the canonical comparison
`Stacks.FundamentalGroup.algebraPullbackModuleComparison g E` for every quasi-coherent `E`. -/
theorem adicFiniteAlgebraAlgebraization_of_isIso_comparison (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A)
    [IsAdicComplete I A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    (hcomparison : ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
      AlgebraSheaf.IsQuasicoherent E → IsIso (algebraPullbackModuleComparison g E))
    (hdata : ∀ (hpullback : ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
        AlgebraSheaf.IsQuasicoherent E → AlgebraPullbackModuleIso g E)
      (B : ∀ n : ℕ, AlgebraSheaf (adicBaseChange A I f n))
      (hqc : ∀ n, AlgebraSheaf.IsQuasicoherent (B n))
      (hBtrans : ∀ n, Nonempty
        ((algebraPullback (adicBaseChangeSucc A I f n)).obj (B (n + 1)) ≅ B n))
      (hMcoh : ∀ n, _root_.SheafOfModules.IsCoherent.{u} (AlgebraSheaf.underlyingModule (B n)))
      (hM0 : HasProperSupport (pullback.snd f (adicThickeningι A I 0))
        (AlgebraSheaf.underlyingModule (B 0)))
      (P : Stacks.Algebraization.CoherentModulesProperOver f),
      ((adicThickeningCompletionFunctor A I f).obj P ≅
          adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh hM0) →
        ∃ d : Stacks.FundamentalGroup.ModuleAlgebraData P.obj.obj, ∀ n, Nonempty
          ((algebraPullback (pullback.fst f (adicThickeningι A I n))).obj
            (Stacks.FundamentalGroup.algebraSheafOfModule P.obj.obj d) ≅ B n)) :
    AdicFiniteAlgebraAlgebraization A I f :=
  adicFiniteAlgebraAlgebraization_of_moduleAlgebraData A I f h088F
    (algebraPullbackModuleIso_of_isIso_comparison hcomparison) hdata

end Chain

end AlgebraicGeometry

end
