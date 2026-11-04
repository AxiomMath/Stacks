module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkSemilinearComparison

/-!
# Endomorphisms of the unit module on the stalk

Let `O` be a sheaf of commutative rings on a site and `Φ` a point of the site. An endomorphism
`ψ` of `O` as a module over itself acts on the stalk `O_Φ` as multiplication by the germ of
`ψ(1)`, computed on any neighbourhood of `Φ`.

## Main results

* `Stacks.moduleStalkGerm_unit`: the germ of a section of the unit module is the germ of that
  section acting on the germ of `1`.
* `Stacks.sheafModuleFiberOfCommRing_map_unit`: the stalk of an endomorphism `ψ` of the unit
  module is multiplication by the germ of `ψ(1)`.
-/

@[expose] public section

open CategoryTheory Opposite

universe w v u

namespace Stacks

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (Φ : J.Point.{w}) (O : Sheaf J CommRingCat.{w})

/-- The germ of a section of the unit module is the germ of that section of the structure sheaf
acting on the germ of `1`. -/
theorem moduleStalkGerm_unit (W : C) (ζ : Φ.fiber.obj W)
    (m : (commRingSheafToRingSheaf O).obj.obj (op W)) :
    moduleStalkGerm Φ O (SheafOfModules.unit (commRingSheafToRingSheaf O)) W ζ m =
      ringStalkGerm Φ O W ζ m •
        moduleStalkGerm Φ O (SheafOfModules.unit (commRingSheafToRingSheaf O)) W ζ
          (1 : (commRingSheafToRingSheaf O).obj.obj (op W)) :=
  (congrArg (moduleStalkGerm Φ O (SheafOfModules.unit (commRingSheafToRingSheaf O)) W ζ)
    (mul_one m).symm).trans (moduleStalkGerm_smul Φ O _ W ζ m _)

omit [LocallySmall.{w, v, u} C] in
/-- The value at `1` of an endomorphism of the unit module is compatible with restriction. -/
theorem unit_endo_app_one_restrict
    (ψ : SheafOfModules.unit (commRingSheafToRingSheaf O) ⟶
      SheafOfModules.unit (commRingSheafToRingSheaf O)) {Z W : C} (k : Z ⟶ W) :
    (((commRingSheafToRingSheaf O).obj.map k.op).hom
        ((ψ.val.app (op W)).hom (1 : (commRingSheafToRingSheaf O).obj.obj (op W))) :
      (commRingSheafToRingSheaf O).obj.obj (op Z)) =
      (ψ.val.app (op Z)).hom (1 : (commRingSheafToRingSheaf O).obj.obj (op Z)) :=
  (PresheafOfModules.naturality_apply ψ.val k.op
    (1 : (commRingSheafToRingSheaf O).obj.obj (op W))).symm.trans
      (congrArg (ψ.val.app (op Z)).hom (map_one ((commRingSheafToRingSheaf O).obj.map k.op).hom))

/-- **An endomorphism of the unit module acts on the stalk by the germ of its value at `1`.** -/
theorem sheafModuleFiberOfCommRing_map_unit
    (ψ : SheafOfModules.unit (commRingSheafToRingSheaf O) ⟶
      SheafOfModules.unit (commRingSheafToRingSheaf O))
    (V : C) (ξ : Φ.fiber.obj V) :
    (sheafModuleFiberOfCommRing Φ O).map ψ =
      ringStalkGerm Φ O V ξ ((ψ.val.app (op V)).hom
        (1 : (commRingSheafToRingSheaf O).obj.obj (op V))) • 𝟙 _ := by
  ext y
  obtain ⟨W, ζ, s₀, rfl⟩ := moduleStalkGerm_jointly_surjective Φ O _ y
  set s : (commRingSheafToRingSheaf O).obj.obj (op W) := s₀
  obtain ⟨Z, η, g, g', hg, hg'⟩ := exists_common_neighborhood₂ Φ
    (fun _ : Unit ↦ W) (fun _ : Unit ↦ V) (fun _ ↦ ζ) (fun _ ↦ ξ)
  have key : ∀ (U : C) (x : Φ.fiber.obj U) (k : Z ⟶ U), Φ.fiber.map k η = x →
      ringStalkGerm Φ O U x ((ψ.val.app (op U)).hom
        (1 : (commRingSheafToRingSheaf O).obj.obj (op U))) =
      ringStalkGerm Φ O Z η ((ψ.val.app (op Z)).hom
        (1 : (commRingSheafToRingSheaf O).obj.obj (op Z))) := by
    rintro U x k rfl
    exact (ringStalkGerm_restrict Φ O k η _).symm.trans
      (congrArg _ (unit_endo_app_one_restrict O ψ k))
  have hW := (key W ζ (g ()) (hg ())).trans (key V ξ (g' ()) (hg' ())).symm
  have hs : (ψ.val.app (op W)).hom s =
      s •
        (ψ.val.app (op W)).hom (1 : (commRingSheafToRingSheaf O).obj.obj (op W)) :=
    (congrArg (ψ.val.app (op W)).hom (mul_one s).symm).trans
      ((ψ.val.app (op W)).hom.map_smul s _)
  have h1 := moduleStalkGerm_unit Φ O W ζ
    ((ψ.val.app (op W)).hom (1 : (commRingSheafToRingSheaf O).obj.obj (op W)))
  have h2 := moduleStalkGerm_unit Φ O W ζ s
  rw [hW] at h1
  rw [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_apply,
    moduleStalkGerm_naturality, hs, moduleStalkGerm_smul]
  refine (congrArg (ringStalkGerm Φ O W ζ s • ·) h1).trans ?_
  refine Eq.trans ?_ (congrArg (_ • ·) h2.symm)
  rw [smul_smul, smul_smul, mul_comm]

end Stacks

