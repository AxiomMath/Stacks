module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsRingedTopos
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.PointRingedSite
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory

/-!
# The structure morphism of `(X_étale, Λ̲)` to the point, and modules on the point

Let `X` be a scheme and `Λ` a commutative ring. This file adds to the ringed topos
`Stacks.EtaleCohomology.EtaleCoefficients.ringedTopos Λ X` its structure morphism

`π : (X_étale, Λ̲) ⟶ (pt, Λ)`

to the point ringed by `Λ`, as a morphism of ringed topoi. Along `π`, `Rπ_*` is `RΓ(X, -)`
and `Lπ^*K` is the constant complex `K̲`; this is how [Stacks, Tag 0F12] reads the canonical map
`RΓ(X, E) ⊗^L_Λ K ⟶ RΓ(X, E ⊗^L_Λ K̲)` as the map of Cohomology on Sites, Section 0943
([Stacks, Tag 0B56]) for `π`. It also identifies sheaves of modules on the point with modules,
and so `D(pt, Λ)` with `D(Λ)`.

## Main definitions

* `pointRing`, `pointScalars`: the structure sheaf of rings of the one-point ringed site of a
  ring and its ring of sections over the point.
* `pointModuleEquivalence`: modules over that ring are sheaves of modules on the point.
* `pointRingedTopos Λ`: the point ringed by `Λ`.
* `terminal X`: the terminal object `X` of the small model of the small étale site.
* `toPointTopos Λ X`: the morphism of topoi to the point, with inverse image the constant sheaf
  functor and direct image restriction along the functor picking `terminal X`.
* `toPoint Λ X`: **the morphism of ringed topoi `π : (X_étale, Λ̲) ⟶ (pt, Λ)`**. Its structure
  map `Λ ⟶ π_*Λ̲` is the sheafification unit of the constant presheaf at `X`, as for
  `Stacks.EtaleCohomology.EtaleCoefficients.structureMap`.
* `pointDerived Λ`: the equivalence `D(Λ) ⥤ D(pt, Λ)`, with
  `pointDerivedSingleIso` identifying the image of `Λ[0]` with `𝒪_pt[0]`.

## References

* [Stacks Project, Tag 0F12](https://stacks.math.columbia.edu/tag/0F12)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe v u

namespace Stacks.EtaleCohomology.EtaleCoefficients

/-! ### Modules on the point -/

section PointModules

open Stacks.PointRingedSite

variable (A : Type v) [CommRing A]

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

/-- The structure sheaf of rings of the one-point ringed site of `A`. -/
abbrev pointRing := Stacks.SheafOfModules.Tensor.ringSheaf (site A).O

/-- The only endomorphism of the point is the identity. -/
theorem hom_eq_id (f : op (pt A) ⟶ op (pt A)) : f = 𝟙 _ := by
  rcases f with ⟨⟨⟨h⟩⟩⟩
  rfl

/-- The restriction maps of a sheaf of modules on the point are the identity. -/
theorem map_apply_eq_self (M : SheafOfModules.{v} (pointRing A)) (f : op (pt A) ⟶ op (pt A))
    (x : M.val.obj (op (pt A))) : (M.val.map f x : M.val.obj (op (pt A))) = x := by
  obtain rfl := hom_eq_id A f
  rw [M.val.map_id]
  rfl

/-- The ring of the point. -/
abbrev pointScalars := ((pointRing A).obj.obj (op (pt A)))

/-- The sheaf of modules on the point with value a module. -/
def constModule (P : ModuleCat.{v} (pointScalars A)) : SheafOfModules.{v} (pointRing A) where
  val :=
    { obj := fun _ => P
      map := fun _ => ModuleCat.ofHom
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_id := fun _ => by ext; rfl
      map_comp := fun _ _ => by ext; rfl }
  isSheaf := Presheaf.isSheaf_bot _

/-- Taking sections over the point is full. -/
instance : (ev A).Full where
  map_surjective {M N} g := by
    refine ⟨⟨{ app := fun _ => g, naturality := fun {U V} f => ?_ }⟩, rfl⟩
    obtain rfl := eq_op_pt A U
    obtain rfl := eq_op_pt A V
    ext x
    change g (M.val.map f x) = N.val.map f (g x)
    rw [map_apply_eq_self A M]
    exact (map_apply_eq_self A N f (g x)).symm

/-- Every module is the sections over the point of a sheaf of modules. -/
instance : (ev A).EssSurj where
  mem_essImage P := ⟨constModule A P, ⟨Iso.refl _⟩⟩

/-- Taking sections over the point is an equivalence. -/
instance : (ev A).IsEquivalence where

/-- **Sheaves of modules on the point are modules**: the inverse of taking sections over the
point. -/
def pointModuleEquivalence :
    ModuleCat.{v} (pointScalars A) ≌ SheafOfModules.{v} (pointRing A) :=
  (ev A).asEquivalence.symm

/-- The functor from modules to sheaves of modules on the point is additive. -/
instance : (pointModuleEquivalence A).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Taking sections over the point is additive. -/
instance : (pointModuleEquivalence A).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

end PointModules

/-! ### The point ringed by `Λ` and the structure morphism to it -/

section ToPoint

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The point ringed by `Λ`**: the one-point site with the chaotic topology and constant
structure sheaf `Λ`. -/
abbrev pointRingedTopos : RingedTopos.{u + 1, u + 1, u + 1} where
  C := (Stacks.PointRingedSite.site Λ).C
  J := (Stacks.PointRingedSite.site Λ).J
  O := (Stacks.PointRingedSite.site Λ).O

/-- Sheaves of sets on the point are sets. -/
def pointToposEquiv : (pointRingedTopos Λ).Topos ≌ Type (u + 1) :=
  (sheafBotEquivalence (C := Discrete PUnit.{u + 2}) (Type (u + 1))).trans
    ((Discrete.opposite PUnit.{u + 2}).congrLeft.trans Functor.equiv)

variable (X : Scheme.{u})

/-- `X` itself, as an object of the small model of its small étale site. -/
abbrev terminal : Site X := (fromEtale X).obj (Scheme.Etale.mk (𝟙 X))

/-- `X` itself is a terminal object of the small model of its small étale site. -/
def terminalIsTerminal : IsTerminal (terminal X) := by
  have hci : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  have hT : IsTerminal (Scheme.Etale.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal _ _
  exact hT.isTerminalObj (fromEtale X) _

/-- The small model of the small étale site of `X` has a terminal object. -/
instance : HasTerminal (Site X) := (terminalIsTerminal X).hasTerminal

/-- The functor from the point to the small model picking the terminal object `X`. -/
abbrev pointFunctor : (Stacks.PointRingedSite.site Λ).C ⥤ Site X :=
  Functor.fromPUnit (terminal X)

/-- The functor picking `terminal X` is continuous. -/
instance : (pointFunctor Λ X).IsContinuous (pointRingedTopos Λ).J (topology X) :=
  ⟨fun _ => Presieve.isSheaf_bot⟩

/-- Sections over `X`, read on the point, are restriction along the functor picking `X`. -/
def sectionsCompPointIso :
    (sheafSections (topology X) (Type (u + 1))).obj (op (terminal X)) ⋙
        (pointToposEquiv Λ).inverse ≅
      (pointFunctor Λ X).sheafPushforwardContinuous (Type (u + 1)) (pointRingedTopos Λ).J
        (topology X) :=
  NatIso.ofComponents (fun F => (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun {U V} f => by
      obtain rfl := Stacks.PointRingedSite.eq_op_pt Λ U
      obtain rfl := Stacks.PointRingedSite.eq_op_pt Λ V
      obtain rfl := hom_eq_id Λ f
      simp
      rfl)))
    (fun g => by
      ext U x
      rfl)

/-- **The morphism of topoi from the small étale topos of `X` to the point**: the inverse image
is the constant sheaf functor, and the direct image is restriction along the functor picking `X`,
which is global sections. -/
def toPointTopos : MorphismOfTopoi (ringedTopos Λ X).Topos (pointRingedTopos Λ).Topos where
  pushforward := (pointFunctor Λ X).sheafPushforwardContinuous (Type (u + 1))
    (pointRingedTopos Λ).J (topology X)
  inverseImage := (pointToposEquiv Λ).functor ⋙ constantSheaf _ _
  adj := ((pointToposEquiv Λ).toAdjunction.comp
    (constantSheafAdj _ _ (terminalIsTerminal X))).ofNatIsoRight (sectionsCompPointIso Λ X)
  preservesFiniteLimits := by
    have : PreservesFiniteLimits (constantSheaf (topology X) (Type (u + 1))) := by
      unfold constantSheaf
      infer_instance
    infer_instance

/-- The inverse image of `toPointTopos Λ X` preserves finite limits. -/
instance : PreservesFiniteLimits (toPointTopos Λ X).inverseImage :=
  (toPointTopos Λ X).preservesFiniteLimits

/-- The direct image of `toPointTopos Λ X` is a right adjoint. -/
instance : (toPointTopos Λ X).pushforward.IsRightAdjoint :=
  (toPointTopos Λ X).adj.isRightAdjoint

/-- The structure map `Λ ⟶ π_*Λ̲` of the morphism to the point: the sheafification unit
`Λ ⟶ Λ̲(X)` of the constant presheaf, read through the identification of the direct image of a
sheaf of commutative rings along restriction with its restriction. -/
def toPointStructureMap :
    (pointRingedTopos Λ).O ⟶ (pushforwardCommRingFunctor (toPointTopos Λ X)).obj
      (ringedTopos Λ X).O :=
  (fullyFaithfulSheafToPresheaf _ _).preimage
      (Y := ((pointFunctor Λ X).sheafPushforwardContinuous CommRingCat.{u + 1}
        (pointRingedTopos Λ).J (topology X)).obj (ringedTopos Λ X).O)
      ((show (sheafToPresheaf _ _).obj (pointRingedTopos Λ).O ⟶
          (pointFunctor Λ X).op ⋙ (Functor.const _).obj (CommRingCat.of Λ) from
          { app := fun _ => 𝟙 _ }) ≫ Functor.whiskerLeft (pointFunctor Λ X).op
        (toSheafify (topology X) ((Functor.const _).obj (CommRingCat.of Λ)))) ≫
    (restrictionCommRingIso (pointRingedTopos Λ).J (topology X) (pointFunctor Λ X)
      (ringedTopos Λ X).O).inv

/-- **The structure morphism `π : (X_étale, Λ̲) ⟶ (pt, Λ)` of ringed topoi.** -/
def toPoint : RingedToposHom (ringedTopos Λ X) (pointRingedTopos Λ) where
  toToposHom := toPointTopos Λ X
  fSharp := toPointStructureMap Λ X

/-- The pullback along `toPoint Λ X` on the homotopy category has a left derived functor. -/
instance : (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackOnHomotopy
    (toPoint Λ X)).HasLeftDerivedFunctor
      (Stacks.Cohomology.DerivedPullbackOfToposHom.quasiIsoTarget (Y := pointRingedTopos Λ)) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy (toPoint Λ X)

/-- Sheaves of `Λ̲`-modules on the small étale site of `X` form a Grothendieck abelian category. -/
instance : IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O)) :=
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u + 1, u + 1, u + 1, u + 1} _

/-- Sheaves of modules on the point ringed by `Λ` form a Grothendieck abelian category. -/
instance : IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedTopos Λ).O)) :=
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u + 1, u + 1, u + 1, u + 1} _

/-- Sheaves of `Λ̲`-modules on the small étale site of `X` have enough injectives. -/
instance : EnoughInjectives (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O)) :=
  IsGrothendieckAbelian.enoughInjectives

/-- Sheaves of modules on the point ringed by `Λ` have enough injectives. -/
instance : EnoughInjectives (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedTopos Λ).O)) :=
  IsGrothendieckAbelian.enoughInjectives

end ToPoint

/-! ### `D(pt, Λ) = D(Λ)` -/

section Derived

-- `Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap` is stated on the standard
-- model of the derived categories, which is the model used here.
attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **`D(Λ) ⥤ D(pt, Λ)`**: complexes of modules over the ring of the point, read as complexes of
sheaves of modules on the point. It is an equivalence, `pointDerivedEquivalence`. -/
abbrev pointDerived : DerivedCategory (ModuleCat.{u + 1} (pointScalars Λ)) ⥤
    DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedTopos Λ).O)) :=
  (pointModuleEquivalence Λ).functor.mapDerivedCategory

/-- **`D(Λ) ≌ D(pt, Λ)`**, induced by the equivalence of modules with sheaves of modules on the
point. Its functor is `pointDerived`. -/
def pointDerivedEquivalence : DerivedCategory (ModuleCat.{u + 1} (pointScalars Λ)) ≌
    DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedTopos Λ).O)) :=
  Dualizing.mapDerivedCategoryEquivalenceOfEquivalence (pointModuleEquivalence Λ)

/-- `pointDerived Λ` is an equivalence. -/
instance : (pointDerived Λ).IsEquivalence :=
  (pointDerivedEquivalence Λ).isEquivalence_functor

/-- The image of the ring placed in degree zero is the structure sheaf placed in degree zero. -/
def pointDerivedSingleIso : (pointDerived Λ).obj ((DerivedCategory.singleFunctor _ 0).obj
      (ModuleCat.of (pointScalars Λ) (Shrink.{u + 1} (pointScalars Λ)))) ≅
    Stacks.DerivedTensor.RingedSite.unitObject
      ⟨(pointRingedTopos Λ).C, (pointRingedTopos Λ).J, (pointRingedTopos Λ).O⟩ :=
  ((pointModuleEquivalence Λ).functor.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((pointModuleEquivalence Λ).functor.mapIso
          ((Shrink.linearEquiv.{u + 1} (pointScalars Λ) (pointScalars Λ)).toModuleIso ≪≫
            Iso.refl ((Stacks.PointRingedSite.ev Λ).obj (SheafOfModules.unit _))) ≪≫
        ((pointModuleEquivalence Λ).counitIso.app _))

end Derived

end Stacks.EtaleCohomology.EtaleCoefficients
