module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars
public import Mathlib.RepresentationTheory.Basic

/-!
# Sheaves of `A[G]`-modules from group actions

Let `A` be a commutative ring and `G` a group. A sheaf `N₀` of `A`-modules on the small étale
site of a scheme `X` together with an action of `G` on `N₀` by automorphisms is the same as a
sheaf of modules over the group ring `A[G]`: over every étale `W ⟶ X` the module `N₀(W)` is a
representation of `G`, hence an `A[G]`-module, and the restriction maps are `G`-equivariant.

## Main definitions

* `Stacks.EtaleCohomology.groupActionEtaleModule`: the sheaf of `A[G]`-modules attached to `N₀`
  with an action `act : G →* End N₀`.
* `Stacks.EtaleCohomology.groupActionEtaleModuleRestrictScalarsIso`: restricting its scalars
  along `A ⟶ A[G]` gives back `N₀`.

## Main results

* `Stacks.EtaleCohomology.groupActionEtaleModuleRestrictScalarsIso_hom_app_smul`: under that
  identification, multiplication by `g ∈ G` is the action of `g`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable {A : Type} [CommRing A] {G : Type} [Group G] {X : Scheme.{u}}
  (N₀ : EtaleModules.{u, 0} A X) (act : G →* End N₀)

/-- The representation of `G` on the sections of `N₀` over `W`. -/
def groupActionSectionsRep (W : X.Etaleᵒᵖ) : Representation A G (N₀.obj.obj W) where
  toFun g := ((act g).asHom.hom.app W).hom
  map_one' := by
    rw [map_one]
    rfl
  map_mul' g h := by
    rw [map_mul, End.mul_asHom]
    rfl

/-- The element `g ∈ G` acts on a section `x` of `N₀` over `W` as `act g` does. -/
lemma groupActionSectionsRep_apply (W : X.Etaleᵒᵖ) (g : G) (x : N₀.obj.obj W) :
    groupActionSectionsRep N₀ act W g x = (act g).asHom.hom.app W x := rfl

/-- The restriction maps of `N₀` are `G`-equivariant. -/
lemma groupActionSectionsRep_map {W W' : X.Etaleᵒᵖ} (m : W ⟶ W') (g : G) (x : N₀.obj.obj W) :
    N₀.obj.map m (groupActionSectionsRep N₀ act W g x) =
      groupActionSectionsRep N₀ act W' g (N₀.obj.map m x) := by
  simp only [groupActionSectionsRep_apply]
  exact (congrArg (fun φ => φ x) (congrArg ModuleCat.Hom.hom ((act g).asHom.hom.naturality m))).symm

/-- A `G`-equivariant linear map between representations is `A[G]`-linear between the associated
modules. -/
def asModuleMapOfEquivariant {V W : Type*} [AddCommGroup V] [Module A V] [AddCommGroup W]
    [Module A W] {ρ : Representation A G V} {σ : Representation A G W} (φ : V →ₗ[A] W)
    (hφ : ∀ g x, φ (ρ g x) = σ g (φ x)) : ρ.asModule →ₗ[MonoidAlgebra A G] σ.asModule where
  toFun x := σ.asModuleEquiv.symm (φ (ρ.asModuleEquiv x))
  map_add' x y := by simp only [map_add]
  map_smul' r x := by
    simp only [Representation.asModuleEquiv_map_smul, RingHom.id_apply]
    rw [LinearEquiv.symm_apply_eq, Representation.asModuleEquiv_map_smul,
      LinearEquiv.apply_symm_apply]
    induction r using MonoidAlgebra.induction_on with
    | of g =>
      simp only [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one, hφ]
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | smul c a ha => simp only [map_smul, LinearMap.smul_apply, ha]

/-- The presheaf of `A[G]`-modules underlying `groupActionEtaleModule`. -/
def groupActionPresheaf : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (MonoidAlgebra A G) where
  obj W := ModuleCat.of _ (groupActionSectionsRep N₀ act W).asModule
  map m := ModuleCat.ofHom (asModuleMapOfEquivariant (N₀.obj.map m).hom
    (fun g x => groupActionSectionsRep_map N₀ act m g x))
  map_id W := by
    ext x
    change (N₀.obj.map (𝟙 W)).hom x = x
    rw [N₀.obj.map_id]
    rfl
  map_comp m m' := by
    ext x
    change (N₀.obj.map (m ≫ m')).hom x = (N₀.obj.map m').hom ((N₀.obj.map m).hom x)
    rw [N₀.obj.map_comp]
    rfl

/-- Restricting the scalars of `groupActionPresheaf` along `A ⟶ A[G]` gives back `N₀`. -/
def groupActionPresheafRestrictScalarsIso :
    groupActionPresheaf N₀ act ⋙ ModuleCat.restrictScalars.{u + 1}
        (MonoidAlgebra.singleOneRingHom (R := A) (M := G)) ≅ N₀.obj :=
  NatIso.ofComponents
    (fun W =>
      { hom := ModuleCat.ofHom
          (X := (groupActionPresheaf N₀ act ⋙ ModuleCat.restrictScalars.{u + 1}
            (MonoidAlgebra.singleOneRingHom (R := A) (M := G))).obj W) (Y := N₀.obj.obj W)
          { toFun := fun x => (groupActionSectionsRep N₀ act W).asModuleEquiv x
            map_add' := fun x y => map_add _ x y
            map_smul' := fun r x => by
              change (groupActionSectionsRep N₀ act W).asAlgebraHom (MonoidAlgebra.single 1 r) x = _
              rw [Representation.asAlgebraHom_single, map_one]
              rfl }
        inv := ModuleCat.ofHom (X := N₀.obj.obj W)
          (Y := (groupActionPresheaf N₀ act ⋙ ModuleCat.restrictScalars.{u + 1}
            (MonoidAlgebra.singleOneRingHom (R := A) (M := G))).obj W)
          { toFun := fun x => (groupActionSectionsRep N₀ act W).asModuleEquiv.symm x
            map_add' := fun x y => map_add _ x y
            map_smul' := fun r x => by
              change _ = (groupActionSectionsRep N₀ act W).asAlgebraHom (MonoidAlgebra.single 1 r) x
              rw [Representation.asAlgebraHom_single, map_one]
              rfl }
        hom_inv_id := rfl
        inv_hom_id := rfl })
    (fun m => rfl)

/-- **The sheaf of `A[G]`-modules attached to a sheaf of `A`-modules with a `G`-action.** -/
def groupActionEtaleModule : EtaleModules.{u, 0} (MonoidAlgebra A G) X where
  obj := groupActionPresheaf N₀ act
  property := by
    have : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} (MonoidAlgebra A G)) :=
      ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, 0}
    refine (Presheaf.isSheaf_iff_isSheaf_comp (J := X.smallEtaleTopology)
      (P := groupActionPresheaf N₀ act)
      (ModuleCat.restrictScalars.{u + 1} (MonoidAlgebra.singleOneRingHom (R := A) (M := G)))).2 ?_
    exact (Presheaf.isSheaf_of_iso_iff (groupActionPresheafRestrictScalarsIso N₀ act)).2
      N₀.property

/-- **Restricting the scalars of `groupActionEtaleModule` along `A ⟶ A[G]` gives back `N₀`.** -/
def groupActionEtaleModuleRestrictScalarsIso :
    (etaleModuleRestrictScalars (MonoidAlgebra.singleOneRingHom (R := A) (M := G)) X).obj
        (groupActionEtaleModule N₀ act) ≅ N₀ :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (groupActionPresheafRestrictScalarsIso N₀ act)

/-- Under `groupActionEtaleModuleRestrictScalarsIso`, multiplication by `g ∈ G` is the action of
`g`. -/
lemma groupActionEtaleModuleRestrictScalarsIso_hom_app_smul (W : X.Etaleᵒᵖ) (g : G)
    (x : (groupActionEtaleModule N₀ act).obj.obj W) :
    (groupActionEtaleModuleRestrictScalarsIso N₀ act).hom.hom.app W
        (MonoidAlgebra.single g (1 : A) • x) =
      (act g).asHom.hom.app W
        ((groupActionEtaleModuleRestrictScalarsIso N₀ act).hom.hom.app W x) := by
  change (groupActionSectionsRep N₀ act W).asAlgebraHom (MonoidAlgebra.single g 1)
    ((groupActionSectionsRep N₀ act W).asModuleEquiv x) = _
  rw [Representation.asAlgebraHom_single_one]
  rfl

end Stacks.EtaleCohomology

end
