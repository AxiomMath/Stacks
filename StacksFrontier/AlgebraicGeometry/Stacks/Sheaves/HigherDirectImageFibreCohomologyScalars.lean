module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.AffineBasis
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.HigherDirectImageFibreCohomology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images of sheaves of modules on algebraic stacks, as modules

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and `τ` one of the Zariski, étale,
smooth, syntomic and fppf topologies. For an object `y` of `𝒴` lying over a scheme `V`, the
2-fibre product `(Sch/V)_{fppf} ×_{y, 𝒴} 𝒳` carries the structure sheaf `𝒪` restricted from `𝒳`,
and every object `P` of it comes with a comparison arrow `f(pr P) ⟶ y`; pulling functions back
along these arrows is a ring map `𝒪_𝒴(y) ⟶ Γ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, 𝒪)`. Through it, the
cohomology `H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)` of a sheaf `ℱ` of `𝒪_𝒳`-modules, a module
over the global sections of `𝒪` (Stacks 071H), is an `𝒪_𝒴(y)`-module.

This file proves Stacks 075G for sheaves of modules in that form: `Rⁿf_*ℱ` is, as a sheaf of
`𝒪_𝒴`-modules, the sheaf associated to a presheaf of `𝒪_𝒴`-modules whose value at `y` is the
`𝒪_𝒴(y)`-module `H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)`.

The key step is Stacks 06W6 with its module structure: the compatible sections over `y` of the
direct image of presheaves of modules of Stacks 06WD are, as `𝒪_𝒴(y)`-modules, the global
sections over the 2-fibre product of the inverse image, with scalars restricted along the
pullback of functions. The rest is the abelian argument: evaluation at `y` and restriction of
scalars are exact, and `pr⁻¹` preserves injective sheaves of modules (Stacks 06X2).

## Main definitions

* `AlgebraicGeometry.Stack.objectFibreScalarMap`: the pullback of functions
  `𝒪_𝒴(y) ⟶ Γ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, 𝒪)`.
* `AlgebraicGeometry.Stack.objectFibreModuleCohomologyModule`: the `𝒪_𝒴(y)`-module
  `H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)`.
* `AlgebraicGeometry.Stack.objectFibreModuleCohomologyPresheafOfModules`: the presheaf of
  `𝒪_𝒴`-modules `y ↦ H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)`.

## Main results

* `AlgebraicGeometry.Stack.modulePresheafDirectImageEvaluationLinearIso`: Stacks 06W6 for
  sheaves of modules, as an isomorphism of functors to `𝒪_𝒴(y)`-modules.
* `AlgebraicGeometry.Stack.derivedModulePresheafDirectImageEvaluationLinearIso`: the value at
  `y` of the derived presheaf direct image of sheaves of modules is
  `H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)` as an `𝒪_𝒴(y)`-module.
* `AlgebraicGeometry.Stack.moduleHigherDirectImageIsoSheafifyFibreModuleCohomology`:
  **Stacks 075G** for sheaves of modules.

## Implementation notes

The restriction maps of the presheaf of `𝒪_𝒴`-modules are not given by the source; they are those
of the derived presheaf direct image of sheaves of modules, transported to the values along
`derivedModulePresheafDirectImageEvaluationLinearIso`. The 1-morphism `(Sch/V)_{fppf} ⟶ 𝒴`
attached to `y` is the slice functor of a choice of pullbacks, as in
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/HigherDirectImageFibreCohomology.lean`.

## References

* [Stacks Project, Tag 075G](https://stacks.math.columbia.edu/tag/075G)
* [Stacks Project, Tag 06W6](https://stacks.math.columbia.edu/tag/06W6)
* [Stacks Project, Tag 06X2](https://stacks.math.columbia.edu/tag/06X2)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w a

section General

/-- The compatible sections of Stacks 06WD over `y` are the sections of the restriction to the
comma category of arrows `y ⟶ L(x)`. -/
def compatibleSectionsEquivSections {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D)
    (F : C ⥤ AddCommGrpCat.{a}) (d : D) :
    compatibleSections L F d ≃ (StructuredArrow.proj d L ⋙ F ⋙ forget AddCommGrpCat).sections where
  toFun s := ⟨fun A => s.1 A.right A.hom, fun {A A'} k => by
    change F.map k.right (s.1 A.right A.hom) = s.1 A'.right A'.hom
    rw [s.2 A.right A'.right k.right A.hom, StructuredArrow.w k]⟩
  invFun t := ⟨fun x γ => t.1 (StructuredArrow.mk γ), fun x x' k γ =>
    t.2 (StructuredArrow.homMk k rfl : StructuredArrow.mk γ ⟶ StructuredArrow.mk (γ ≫ L.map k))⟩
  left_inv s := rfl
  right_inv t := rfl

/-- The direct image of presheaves of modules of Stacks 06WD is, on the nose after transport of
scalars, the functor of compatible sections. -/
def moduleDirectImageDataFstIso {X Y : Type*} [Category* X] [Category* Y] (F : X ⥤ Y)
    (R : Yᵒᵖ ⥤ RingCat.{u}) (T : Xᵒᵖ ⥤ RingCat.{u}) (h : T = F.op ⋙ R) :
    (moduleDirectImageData.{u, _, _, a} F R T h).1 ≅
      PresheafOfModules.restrictScalars (eqToHom h.symm) ⋙
        moduleSectionsFunctor.{u, _, _, a} F R := by
  subst h
  exact Iso.refl _

/-- Restriction of scalars along a morphism of rings, not necessarily commutative, preserves finite
limits: limits of modules are computed on underlying abelian groups. -/
@[sga "4 IV 11.1.6" "special case"]
instance _root_.ModuleCat.preservesFiniteLimits_restrictScalars_of_ring {R R' : Type*} [Ring R]
    [Ring R'] (φ : R →+* R') : PreservesFiniteLimits (ModuleCat.restrictScalars.{a} φ) :=
  ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩

/-- Restriction of scalars along a morphism of rings, not necessarily commutative, preserves finite
colimits: colimits of modules are computed on underlying abelian groups. -/
@[sga "4 IV 11.1.6" "special case"]
instance _root_.ModuleCat.preservesFiniteColimits_restrictScalars_of_ring {R R' : Type*} [Ring R]
    [Ring R'] (φ : R →+* R') : PreservesFiniteColimits (ModuleCat.restrictScalars.{a} φ) :=
  ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩

end General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section FibreRestriction

variable {X Y : Type (u + 1)} [Category.{u} X] [Category.{u} Y]
  (pX : X ⥤ BigFppfOver B S hS) (pY : Y ⥤ BigFppfOver B S hS) (F : X ⥤ Y)
  (c : pY.ChoiceOfPullbacks) (y : Y) (R : Yᵒᵖ ⥤ RingCat.{u})

/-- The functions on `y`, pulled back to every object `P` of the 2-fibre product
`(Sch/V) ×_{y, 𝒴} 𝒳` along its comparison arrow `F(pr P) ⟶ y`. -/
def twoFibreProductScalarRestriction :
    (Functor.const _).obj (R.obj (op y)) ⟶
      (TwoFibreProductOver.snd (Over.forget (pY.obj y)) pX pY
        (c.sliceFunctor (Functor.Fiber.mk rfl)) F).op ⋙ F.op ⋙ R where
  app P := R.map ((Presheaf.pushforwardIndexFunctor pX pY F (c.sliceDatum y)).obj P.unop).hom.op
  naturality P Q k := by
    have w := Presheaf.pushforwardIndexFunctor_w pX pY F (c.sliceDatum y) k.unop
    exact (Category.id_comp _).trans
      ((congrArg (fun φ => R.map φ.op) w).symm.trans (R.map_comp _ _))

end FibreRestriction


section Modules

open Stacks.Cohomology.SiteModules

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (c : 𝒴.val.val.p.ChoiceOfPullbacks) (τ : SiteKind) (y : 𝒴.val.val.obj)

local notation "g" => CatFiberedInGroupoids.homFunctor f.hom
local notation "pr" => objectFibreProjection B S hS f.hom c y
local notation "OX" => ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
  (B.baseTopology τ) (B.baseTopology_le_topology τ)
local notation "OY" => ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
  (B.baseTopology τ) (B.baseTopology_le_topology τ)
local notation "Of" => ringStructureSheafCore B S hS (objectFibreStructure B S hS f.hom c y)
  (isFiberedInGroupoids_objectFibreStructure B S hS f.hom c y) (B.baseTopology τ)
  (B.baseTopology_le_topology τ)
local notation "E" => Presheaf.pushforwardIndexFunctor 𝒳.val.val.p 𝒴.val.val.p g (c.sliceDatum y)

/-- **Stacks 06W6 for sections of modules.** The compatible sections over `y` of a sheaf of
modules on `𝒳` are the global sections of its inverse image on the 2-fibre product. -/
def objectFibreSectionsEquiv (M : SheafOfModules.{max (u + 1) a} OX) :
    compatibleSections (g).op M.val.presheaf (op y) ≃
      ((objectFibreModuleInverseImage.{u, w, a} B S hS f c τ y).obj M).sections :=
  (compatibleSectionsEquivSections (g).op M.val.presheaf (op y)).trans
    ((Presheaf.pushforwardCostrSectionsEquiv g y (M.val.presheaf ⋙ forget _)).trans
      (Presheaf.pushforwardIndexSectionsEquiv 𝒳.val.val.p 𝒴.val.val.p g (c.sliceDatum y)
        𝒴.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        (M.val.presheaf ⋙ forget _)))

/-- The identification of sections reads a compatible section at the comparison arrow of each
object of the 2-fibre product. -/
lemma objectFibreSectionsEquiv_apply (M : SheafOfModules.{max (u + 1) a} OX)
    (s : compatibleSections (g).op M.val.presheaf (op y)) (P : (ObjectFibre B S hS f.hom c y)ᵒᵖ) :
    (objectFibreSectionsEquiv B S hS f c τ y M s).1 P =
      s.1 (op P.unop.y) ((E).obj P.unop).hom.op := rfl



/-- The functions on `y`, pulled back to the structure sheaf of the 2-fibre product along the
comparison arrows `f(pr P) ⟶ y`: `𝒪_𝒴(y) ⟶ 𝒪_𝒴(f(pr P)) = 𝒪_𝒳(pr P) = 𝒪(P)`. -/
def objectFibreScalarAction :
    (Functor.const _).obj ((OY).obj.obj (op y)) ⟶ (Of).obj :=
  twoFibreProductScalarRestriction B S hS 𝒳.val.val.p 𝒴.val.val.p g c y (OY).obj ≫
    Functor.whiskerLeft (pr).op (eqToHom (ringStructureSheafCore_obj_eq B S hS 𝒳.val.val.p
      𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids g
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (B.baseTopology τ)
      (B.baseTopology_le_topology τ)).symm) ≫
    eqToHom (ringStructureSheafCore_obj_eq B S hS (objectFibreStructure B S hS f.hom c y)
      𝒳.val.val.p (isFiberedInGroupoids_objectFibreStructure B S hS f.hom c y)
      𝒳.val.isFiberedInGroupoids pr TwoFibreProductOver.snd_comp_eq (B.baseTopology τ)
      (B.baseTopology_le_topology τ)).symm

/-- The pullback of functions along the 2-fibre product, the ring map
`𝒪_𝒴(y) ⟶ Γ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, 𝒪)` through which `𝒪_𝒴(y)` acts on the cohomology of the
2-fibre product. -/
def objectFibreScalarMap : (OY).obj.obj (op y) →+* GlobalSectionRing (Of) where
  toFun r := ⟨fun P => (objectFibreScalarAction B S hS f c τ y).app P r, fun {_ _} k =>
    (ConcreteCategory.congr_hom ((objectFibreScalarAction B S hS f c τ y).naturality k) r).symm⟩
  map_one' := Subtype.ext (funext fun _ => map_one _)
  map_mul' r s := Subtype.ext (funext fun _ => map_mul _ r s)
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' r s := Subtype.ext (funext fun _ => map_add _ r s)


/-- **The compatible sections over `y` are the global sections over the 2-fibre product, as
`𝒪_𝒴(y)`-modules**, the global sections being a module over `𝒪_𝒴(y)` through
`objectFibreScalarMap`. -/
def objectFibreSectionsLinearEquiv (M : SheafOfModules.{max (u + 1) a} OX) :
    ((moduleSectionsFunctor.{u, u + 1, u, a} g (OY).obj).obj
      ((PresheafOfModules.restrictScalars (eqToHom (moduleFunctoriality.{u, u + 1, u, a, u + 1, u}
          B S hS 𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids g
          (CatFiberedInGroupoids.homFunctor_comp_p f.hom)).structurePresheaf_eq.symm)).obj
        ((SheafOfModules.forget OX).obj M))).obj (op y) ≃ₗ[(OY).obj.obj (op y)]
      (ModuleCat.restrictScalars.{max (u + 1) a} (objectFibreScalarMap B S hS f c τ y)).obj
        ((globalSectionsFunctor.{u + 1, u, u, max (u + 1) a} Of).obj
          ((objectFibreModuleInverseImage.{u, w, a} B S hS f c τ y).obj M)) where
  toFun := objectFibreSectionsEquiv B S hS f c τ y M
  invFun := (objectFibreSectionsEquiv B S hS f c τ y M).symm
  left_inv := (objectFibreSectionsEquiv B S hS f c τ y M).left_inv
  right_inv := (objectFibreSectionsEquiv B S hS f c τ y M).right_inv
  map_add' s t := rfl
  map_smul' r s := by
    apply Subtype.ext
    funext P
    have key : ∀ z, ((eqToHom (ringStructureSheafCore_obj_eq B S hS
        (objectFibreStructure B S hS f.hom c y) 𝒳.val.val.p
        (isFiberedInGroupoids_objectFibreStructure B S hS f.hom c y)
        𝒳.val.isFiberedInGroupoids pr TwoFibreProductOver.snd_comp_eq (B.baseTopology τ)
        (B.baseTopology_le_topology τ))).app P).hom
        (((eqToHom (ringStructureSheafCore_obj_eq B S hS
        (objectFibreStructure B S hS f.hom c y) 𝒳.val.val.p
        (isFiberedInGroupoids_objectFibreStructure B S hS f.hom c y)
        𝒳.val.isFiberedInGroupoids pr TwoFibreProductOver.snd_comp_eq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)).symm).app P).hom z) = z := by
      intro z
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, eqToHom_trans, eqToHom_refl]
      rfl
    let m : M.val.obj (op P.unop.y) := s.1 (op P.unop.y) ((E).obj P.unop).hom.op
    let A : (OX).obj.obj (op P.unop.y) :=
      ((eqToHom (moduleFunctoriality.{u, u + 1, u, a, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
        𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids g
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom)).structurePresheaf_eq.symm).app
          (op P.unop.y)).hom (((OY).obj.map ((E).obj P.unop).hom.op).hom r)
    let B' : (OX).obj.obj (op P.unop.y) := ((eqToHom (ringStructureSheafCore_obj_eq B S hS
        (objectFibreStructure B S hS f.hom c y) 𝒳.val.val.p
        (isFiberedInGroupoids_objectFibreStructure B S hS f.hom c y)
        𝒳.val.isFiberedInGroupoids pr TwoFibreProductOver.snd_comp_eq (B.baseTopology τ)
        (B.baseTopology_le_topology τ))).app P).hom
        (((eqToHom (ringStructureSheafCore_obj_eq B S hS
        (objectFibreStructure B S hS f.hom c y) 𝒳.val.val.p
        (isFiberedInGroupoids_objectFibreStructure B S hS f.hom c y)
        𝒳.val.isFiberedInGroupoids pr TwoFibreProductOver.snd_comp_eq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)).symm).app P).hom A)
    change A • m = B' • m
    have hB : B' = A := key A
    rw [hB]


/-- **Stacks 06W6 for sheaves of modules, as modules.** The sections over `y` of the presheaf
direct image of a sheaf of modules `ℱ` are, as an `𝒪_𝒴(y)`-module, the global sections of
`pr⁻¹ℱ` on the 2-fibre product with scalars restricted along `objectFibreScalarMap`, naturally
in `ℱ`. -/
def modulePresheafDirectImageEvaluationLinearIso :
    modulePresheafDirectImage.{u, w, a} B S hS f τ ⋙
        PresheafOfModules.evaluation (OY).obj (op y) ≅
      objectFibreModuleInverseImage.{u, w, a} B S hS f c τ y ⋙
        globalSectionsFunctor.{u + 1, u, u, max (u + 1) a} Of ⋙
        ModuleCat.restrictScalars.{max (u + 1) a} (objectFibreScalarMap B S hS f c τ y) :=
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft (SheafOfModules.forget OX)
      (moduleDirectImageDataFstIso.{u, a} g (OY).obj (OX).obj
        (moduleFunctoriality.{u, u + 1, u, a, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
          𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids g
          (CatFiberedInGroupoids.homFunctor_comp_p f.hom)).structurePresheaf_eq))
      (PresheafOfModules.evaluation (OY).obj (op y)) ≪≫
    NatIso.ofComponents (fun M => (objectFibreSectionsLinearEquiv B S hS f c τ y M).toModuleIso)
      (fun {M N} φ => by ext s; rfl)



/-- Global sections over the 2-fibre product of the inverse image, as `𝒪_𝒴(y)`-modules, is
additive. -/
instance additive_objectFibreSectionsModule :
    (objectFibreModuleInverseImage.{u, w, a} B S hS f c τ y ⋙
      globalSectionsFunctor.{u + 1, u, u, max (u + 1) a} Of ⋙
      ModuleCat.restrictScalars.{max (u + 1) a} (objectFibreScalarMap B S hS f c τ y)).Additive :=
  inferInstance

/-- **The values of the derived presheaf direct image of sheaves of modules, as modules.** At an
object `y` of `𝒴` lying over `V`, the `n`-th derived presheaf direct image of a sheaf `ℱ` of
`𝒪_𝒳`-modules is `H^n((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)`, the cohomology of the sheaf of modules
`pr⁻¹ℱ` over the global sections of the structure sheaf of the 2-fibre product (Stacks 071H),
regarded as an `𝒪_𝒴(y)`-module through `objectFibreScalarMap`. -/
def derivedModulePresheafDirectImageEvaluationLinearIso (n : ℕ)
    (F : SheafOfModules.{max (u + 1) a} OX) :
    (PresheafOfModules.evaluation (OY).obj (op y)).obj
        (((modulePresheafDirectImage.{u, w, a} B S hS f τ).rightDerived n).obj F) ≅
      (ModuleCat.restrictScalars.{max (u + 1) a} (objectFibreScalarMap B S hS f c τ y)).obj
        ((globalModuleCohomology.{u + 1, u, u, a} (Of) n).obj
          ((objectFibreModuleInverseImage.{u, w, a} B S hS f c τ y).obj F)) :=
  (Functor.rightDerivedCompIso (modulePresheafDirectImage.{u, w, a} B S hS f τ)
      (PresheafOfModules.evaluation (OY).obj (op y)) n).symm.app F ≪≫
    (Functor.rightDerivedIsoOfNatIso
      (modulePresheafDirectImageEvaluationLinearIso.{u, w, a} B S hS f c τ y) n).app F ≪≫
    Functor.rightDerivedCompIsoOfPreservesInjectiveObjects
      (objectFibreModuleInverseImage.{u, w, a} B S hS f c τ y)
      (globalSectionsFunctor.{u + 1, u, u, max (u + 1) a} Of ⋙
        ModuleCat.restrictScalars.{max (u + 1) a} (objectFibreScalarMap B S hS f c τ y)) F n ≪≫
    (Functor.rightDerivedCompIso (globalSectionsFunctor.{u + 1, u, u, max (u + 1) a} Of)
      (ModuleCat.restrictScalars.{max (u + 1) a} (objectFibreScalarMap B S hS f c τ y)) n).app _


/-- `H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)` for a sheaf `ℱ` of `𝒪_𝒳`-modules, as an
`𝒪_𝒴(y)`-module: the cohomology of the sheaf of modules `pr⁻¹ℱ` on the 2-fibre product over the
global sections of its structure sheaf (Stacks 071H), with scalars restricted along the pullback
of functions `objectFibreScalarMap`. -/
abbrev objectFibreModuleCohomologyModule (n : ℕ) (F : SheafOfModules.{max (u + 1) a} OX) :
    ModuleCat.{max (u + 1) a} ((OY).obj.obj (op y)) :=
  (ModuleCat.restrictScalars.{max (u + 1) a} (objectFibreScalarMap B S hS f c τ y)).obj
    ((globalModuleCohomology.{u + 1, u, u, a} (Of) n).obj
      ((objectFibreModuleInverseImage.{u, w, a} B S hS f c τ y).obj F))

/-- **The presheaf of `𝒪_𝒴`-modules `y ↦ H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)` of
Stacks 075G**, for a sheaf `ℱ` of `𝒪_𝒳`-modules: its value at `y` is the `𝒪_𝒴(y)`-module
`objectFibreModuleCohomologyModule` (`objectFibreModuleCohomologyPresheafOfModules_obj`), and its
restriction maps are those of the derived presheaf direct image of sheaves of modules, read through
the identification of the values (`derivedModulePresheafDirectImageEvaluationLinearIso`). -/
def objectFibreModuleCohomologyPresheafOfModules (n : ℕ) (F : SheafOfModules.{max (u + 1) a} OX) :
    PresheafOfModules.{max (u + 1) a} (OY).obj :=
  (((modulePresheafDirectImage.{u, w, a} B S hS f τ).rightDerived n).obj F).copyObj
    (fun y => objectFibreModuleCohomologyModule.{u, w, a} B S hS f c τ y.unop n F)
    (fun y => derivedModulePresheafDirectImageEvaluationLinearIso.{u, w, a} B S hS f c τ y.unop n F)

/-- The value at `y` of the presheaf of modules of Stacks 075G is
`H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)` as an `𝒪_𝒴(y)`-module. -/
@[simp]
lemma objectFibreModuleCohomologyPresheafOfModules_obj (n : ℕ)
    (F : SheafOfModules.{max (u + 1) a} OX) :
    (objectFibreModuleCohomologyPresheafOfModules.{u, w, a} B S hS f c τ n F).obj (op y) =
      objectFibreModuleCohomologyModule.{u, w, a} B S hS f c τ y n F := rfl

/-- **Stacks 075G, sheaves of modules.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks
over `S` and `τ` one of the Zariski, étale, smooth, syntomic and fppf topologies. For a sheaf `ℱ`
of `𝒪_𝒳`-modules on `𝒳_τ`, the higher direct image `Rⁿf_*ℱ` is, as a sheaf of `𝒪_𝒴`-modules, the
sheaf associated to the presheaf of `𝒪_𝒴`-modules `y ↦ H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)`,
`y` an object of `𝒴` lying over the scheme `V`, the cohomology of the sheaf of modules `pr⁻¹ℱ`
being an `𝒪_𝒴(y)`-module through the pullback of functions `𝒪_𝒴(y) ⟶ Γ(…, 𝒪)`.

The direct image is the presheaf direct image followed by sheafification, which is exact
(`moduleHigherDirectImageIsoSheafify`); evaluation at `y` is exact, and the sections over `y` of
the presheaf direct image are the global sections over the 2-fibre product as `𝒪_𝒴(y)`-modules
(`modulePresheafDirectImageEvaluationLinearIso`, Stacks 06W6), whose derived functors are the
cohomology of the 2-fibre product because `pr⁻¹` preserves injectives (Stacks 06X2). -/
@[stacks 075G "sheaves of modules: R^n f_* F is, as an O_Y-module, the sheafification of the \
presheaf of O_Y-modules y ↦ H^n((Sch/V) ×_{y,Y} X, pr^{-1} F)"]
def moduleHigherDirectImageIsoSheafifyFibreModuleCohomology (n : ℕ)
    (F : SheafOfModules.{max (u + 1) a} OX) :
    ((moduleSheafPushforward.{u, u + 1, u, a, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
        𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids g
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (B.baseTopology τ)
        (B.baseTopology_le_topology τ)).rightDerived n).obj F ≅
      (PresheafOfModules.sheafification.{max (u + 1) a} (𝟙 (OY).obj)).obj
        (objectFibreModuleCohomologyPresheafOfModules.{u, w, a} B S hS f c τ n F) :=
  (moduleHigherDirectImageIsoSheafify.{u, w, a} B S hS f τ n).app F ≪≫
    (PresheafOfModules.sheafification.{max (u + 1) a} (𝟙 (OY).obj)).mapIso
      (PresheafOfModules.isoCopyObj _ _ _)
end Modules

end AlgebraicGeometry.Stack

end
