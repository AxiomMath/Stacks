module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigLevelSections

/-!
# Restriction of global sections of an injective module to a level is surjective

Let `X/S` be a global crystalline situation with affine base, `S_e ⊂ S` its finite divided power
levels and `N` an injective sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)`.  This file proves the
second assertion of the hint of [Stacks, Tag 07MV] at module coefficients on the big crystalline
site: the restriction `Γ(CRIS(X/S), N) ⟶ Γ(CRIS(X/S_e), N_e)`, and hence every transition
`Γ(CRIS(X/S_e), N_e) ⟶ Γ(CRIS(X/S_m), N_m)`, is surjective.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.levelSubmodule` — the presheaf of submodules of
  `𝒪_{X/S}` supported on the objects of `CRIS(X/S)` lying over `S_e`.
* `Crystalline.GlobalCrystallineSituation.levelSubmoduleHom` — the morphism of presheaves of
  modules `a ↦ a · t` from that presheaf to `N` attached to a global section `t` of `N_e`.

## Main results

* `Crystalline.GlobalCrystallineSituation.surjective_levelSectionsTrans` — **`Γ(CRIS(X/S), N) ⟶
  Γ(CRIS(X/S_e), N_e)` is surjective for `N` injective.**
* `Crystalline.GlobalCrystallineSituation.surjective_levelSectionsTransition` — **the
  transitions `Γ(CRIS(X/S_e), N_e) ⟶ Γ(CRIS(X/S_m), N_m)` are surjective for `N` injective.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation

open SmallSite

variable (S : GlobalCrystallineSituation.{u}) [IsAffine S.S.scheme] {e : ℕ} (he : S.IsLevel e)

/-- An object of `CRIS(X/S)` **lies over `S_e`** when its structure morphism to `S` factors
through `S_e`; these are the objects in the image of `CRIS(X/S_e)`, up to isomorphism. -/
abbrev LiesOverLevel (V : Thickening S) : Prop :=
  ∃ φ : V.thickening.target ⟶ (S.levelSituation he).S, φ ≫ S.levelProj he = V.toBase

/-- Lying over `S_e` passes to objects mapping to one lying over `S_e`. -/
theorem LiesOverLevel.of_hom {V W : Thickening S} (k : V ⟶ W) (hW : S.LiesOverLevel he W) :
    S.LiesOverLevel he V := by
  obtain ⟨φ, hφ⟩ := hW
  exact ⟨k.targetHom ≫ φ, by rw [Category.assoc, hφ, k.base_naturality]⟩

/-- **The value of a section of `N_e` along a morphism of objects lying over `S_e`.** -/
theorem map_levelValue (N : BigModuleSheaf S) (t : (S.levelSectionsFunctor he).obj N)
    {V W : Thickening S} (k : V ⟶ W) (φ : W.thickening.target ⟶ (S.levelSituation he).S)
    (hφ : φ ≫ S.levelProj he = W.toBase) :
    (S.bigModuleTypes N).map k.op (S.levelValue he N t W φ hφ) =
      S.levelValue he N t V (k.targetHom ≫ φ)
        (by rw [Category.assoc, hφ, k.base_naturality]) := by
  have h := S.map_val_eq_levelValue he N t (k ≫ (W.levelLiftViaIso S he φ hφ).inv)
  exact ((S.bigModuleTypes N).map_comp_apply _ _ _).symm.trans
    (h.trans (S.levelValue_congr he N t V _ _ _ _))

/-- The structure sheaf of `CRIS(X/S)` with its sections raised to the module universe of this
chapter: the free sheaf of modules of rank one at that universe. -/
abbrev bigUnit : BigModuleSheaf S :=
  Stacks.SheafOfModules.uliftUnit.{u + 1} (crystallineStructureSheaf S)

open Classical in
/-- **The presheaf of submodules of `𝒪_{X/S}` supported on the objects lying over `S_e`**: all of
`𝒪_{X/S}(V)` when `V` lies over `S_e`, and `0` otherwise. -/
def levelSubmodule : (S.bigUnit).val.Submodule where
  obj X :=
    { carrier := {x | S.LiesOverLevel he X.unop ∨ x = 0}
      add_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl ha
        · exact Or.inl ha
        · exact Or.inl hb
        · exact Or.inr (by rw [ha, hb, add_zero])
      zero_mem' := Or.inr rfl
      smul_mem' := by
        rintro c a (ha | ha)
        · exact Or.inl ha
        · exact Or.inr (by rw [ha, smul_zero]) }
  map {X Y} f := by
    rintro a (ha | ha)
    · exact Or.inl (LiesOverLevel.of_hom S he f.unop ha)
    · exact Or.inr (by
        change (S.bigUnit).val.map f a = 0
        rw [ha, map_zero])

/-- `N` as a presheaf of modules over the structure presheaf of `CRIS(X/S)`, through the identity
of the structure presheaf. -/
abbrev bigModuleForget (N : BigModuleSheaf S) :
    PresheafOfModules.{u + 1} (crystallineStructureSheaf S).obj :=
  (PresheafOfModules.restrictScalars (𝟙 (crystallineStructureSheaf S).obj)).obj
    ((SheafOfModules.forget _).obj N)

open Classical in
/-- The value of a section of `N_e` at an object of `CRIS(X/S)`: its value through the lift when
the object lies over `S_e`, and `0` otherwise. -/
def levelValueOrZero (N : BigModuleSheaf S) (t : (S.levelSectionsFunctor he).obj N)
    (X : (Thickening S)ᵒᵖ) : N.val.obj X :=
  if h : S.LiesOverLevel he X.unop then S.levelValue he N t X.unop h.choose h.choose_spec else 0

/-- At an object lying over `S_e`, the value is the value through any factorization. -/
theorem levelValueOrZero_of_liesOver (N : BigModuleSheaf S) (t : (S.levelSectionsFunctor he).obj N)
    {X : (Thickening S)ᵒᵖ} (φ : X.unop.thickening.target ⟶ (S.levelSituation he).S)
    (hφ : φ ≫ S.levelProj he = X.unop.toBase) :
    S.levelValueOrZero he N t X = S.levelValue he N t X.unop φ hφ := by
  unfold levelValueOrZero
  exact (dite_eq_left (⟨φ, hφ⟩ : S.LiesOverLevel he X.unop)).trans
    (S.levelValue_congr he N t _ _ _ _ _)

/-- The values of a section of `N_e` are compatible with the restriction maps out of objects lying
over `S_e`. -/
theorem map_levelValueOrZero (N : BigModuleSheaf S) (t : (S.levelSectionsFunctor he).obj N)
    {X Y : (Thickening S)ᵒᵖ} (g : X ⟶ Y) (hX : S.LiesOverLevel he X.unop) :
    N.val.map g (S.levelValueOrZero he N t X) = S.levelValueOrZero he N t Y := by
  obtain ⟨φ, hφ⟩ := hX
  rw [S.levelValueOrZero_of_liesOver he N t φ hφ,
    S.levelValueOrZero_of_liesOver he N t (g.unop.targetHom ≫ φ)
      (by rw [Category.assoc, hφ, g.unop.base_naturality])]
  exact S.map_levelValue he N t g.unop φ hφ

/-- The components of `levelSubmoduleHom`: a local section `a` of `𝒪_{X/S}` supported over `S_e`
goes to `a` times the value of the section of `N_e`. -/
def levelSubmoduleHomApp (N : BigModuleSheaf S) (t : (S.levelSectionsFunctor he).obj N)
    (X : (Thickening S)ᵒᵖ) :
    (S.levelSubmodule he).toPresheafOfModules.obj X ⟶ (S.bigModuleForget N).obj X :=
  ModuleCat.ofHom
    { toFun := fun a => (@id ((crystallineStructureSheaf S).obj.obj X) a.val.down) •
        S.levelValueOrZero he N t X
      map_add' := fun _ _ => add_smul _ _ _
      map_smul' := fun _ _ => mul_smul _ _ _ }

/-- The components of `levelSubmoduleHom`, pointwise. -/
theorem levelSubmoduleHomApp_apply (N : BigModuleSheaf S) (t : (S.levelSectionsFunctor he).obj N)
    (X : (Thickening S)ᵒᵖ) (a : (S.levelSubmodule he).toPresheafOfModules.obj X) :
    (S.levelSubmoduleHomApp he N t X).hom a =
      (@id ((crystallineStructureSheaf S).obj.obj X) a.val.down) • S.levelValueOrZero he N t X :=
  rfl

/-- **The morphism of presheaves of modules attached to a global section `t` of `N_e`**, from the
presheaf of submodules of `𝒪_{X/S}` supported over `S_e` to `N`. -/
def levelSubmoduleHom (N : BigModuleSheaf S) (t : (S.levelSectionsFunctor he).obj N) :
    (S.levelSubmodule he).toPresheafOfModules ⟶ S.bigModuleForget N where
  app X := S.levelSubmoduleHomApp he N t X
  naturality {X Y} g := by
    ext a
    change (@id ((crystallineStructureSheaf S).obj.obj Y)
        ((S.bigUnit).val.map g a.val).down) • S.levelValueOrZero he N t Y =
      N.val.map g ((@id ((crystallineStructureSheaf S).obj.obj X) a.val.down) •
        S.levelValueOrZero he N t X)
    by_cases hX : S.LiesOverLevel he X.unop
    · rw [PresheafOfModules.map_smul, S.map_levelValueOrZero he N t g hX]
      rfl
    · have ha : a.val = 0 := a.2.resolve_left hX
      have h₁ : (@id ((crystallineStructureSheaf S).obj.obj Y)
          ((S.bigUnit).val.map g a.val).down) = 0 := by
        rw [ha, map_zero]
        rfl
      have h₂ : (@id ((crystallineStructureSheaf S).obj.obj X) a.val.down) = 0 := by
        rw [ha]
        rfl
      rw [h₁, h₂, zero_smul, zero_smul, map_zero]
      rfl

/-- The global section `1` of `bigUnit`. -/
def bigUnitOne : (S.bigUnit).val.sections :=
  PresheafOfModules.sectionsMk (fun X => ULift.up (1 : (crystallineStructureSheaf S).obj.obj X))
    (fun {_ _} g => congrArg ULift.up (map_one ((crystallineStructureSheaf S).obj.map g).hom))

/-- **Global sections of an injective module restrict surjectively to a finite level**: every
global section of `N_e` on `CRIS(X/S_e)` is the restriction of a global section of `N` on
`CRIS(X/S)`, for `N` an injective sheaf of `𝒪_{X/S}`-modules. -/
theorem surjective_levelSectionsTrans (N : BigModuleSheaf S) [Injective N] :
    Function.Surjective ((S.levelSectionsTrans he).app N).hom := by
  intro t
  let shf := PresheafOfModules.sheafification.{u + 1} (𝟙 (crystallineStructureSheaf S).obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 (crystallineStructureSheaf S).obj)
  let a := shf.map (S.levelSubmodule he).ι
  have : Mono a := inferInstance
  let ψ₀ := (adj.homEquiv _ N).symm (S.levelSubmoduleHom he N t)
  let ψ := adj.homEquiv _ N (Injective.factorThru ψ₀ a)
  have hψ : (S.levelSubmodule he).ι ≫ ψ = S.levelSubmoduleHom he N t := by
    rw [← adj.homEquiv_naturality_left, Injective.comp_factorThru, Equiv.apply_symm_apply]
  refine ⟨PresheafOfModules.sectionsMap ψ S.bigUnitOne, Subtype.ext (funext fun B => ?_)⟩
  have hB : S.LiesOverLevel he ((S.levelChangeBase he).obj B.unop) := ⟨B.unop.toBase, rfl⟩
  let one : (S.bigUnit).val.obj (op ((S.levelChangeBase he).obj B.unop)) :=
    ULift.up (1 : (crystallineStructureSheaf S).obj.obj (op ((S.levelChangeBase he).obj B.unop)))
  change ψ.app (op ((S.levelChangeBase he).obj B.unop)) one = t.val B
  refine (congrArg (fun f => f.app (op ((S.levelChangeBase he).obj B.unop)) ⟨one, Or.inl hB⟩)
    hψ).trans ?_
  change (1 : (crystallineStructureSheaf S).obj.obj (op ((S.levelChangeBase he).obj B.unop))) •
      S.levelValueOrZero he N t (op ((S.levelChangeBase he).obj B.unop)) = t.val B
  rw [one_smul]
  refine (S.levelValueOrZero_of_liesOver he N t _ _).trans
    ((S.map_val_eq_levelValue he N t (𝟙 ((S.levelChangeBase he).obj B.unop))).symm.trans ?_)
  exact (S.bigModuleTypes N).map_id_apply _ _

/-- **The transitions of global sections of an injective module along the levels are
surjective** for `N` injective: the second assertion of the hint of [Stacks, Tag 07MV]. -/
theorem surjective_levelSectionsTransition {m e : ℕ} (hm : S.IsLevel m) (he : S.IsLevel e)
    (hme : m ≤ e) (N : BigModuleSheaf S) [Injective N] :
    Function.Surjective ((S.levelSectionsTransition hm he hme).app N).hom := by
  intro y
  obtain ⟨x, rfl⟩ := S.surjective_levelSectionsTrans hm N y
  refine ⟨((S.levelSectionsTrans he).app N).hom x, ?_⟩
  exact congrArg (fun f => f.hom x)
    (NatTrans.congr_app (S.levelSectionsTrans_comp_levelSectionsTransition hm he hme) N)

end Crystalline.GlobalCrystallineSituation
