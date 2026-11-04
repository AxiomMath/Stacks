module

public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IdealFiltration.FiltrationData
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IdealFiltration.GenericStalk

/-!
# Filtration of a coherent module by direct images of integral ideal sheaves

[Stacks, Tag 01YF] says that a coherent module `F` on a Noetherian scheme `X` carries a finite
filtration

`0 = F₀ ⊆ F₁ ⊆ ⋯ ⊆ F_n = F`

by coherent submodules whose successive quotients are direct images `i_* I` of nonzero coherent
sheaves of ideals `I ⊆ 𝒪_Z` along closed immersions `i : Z ⟶ X` with `Z` integral.

The filtration is produced by Noetherian induction on the support. On an irreducible support
with generic point `ξ` the defining ideal `J` of the integral closed subscheme cutting out that
support acts nilpotently on `F`, so `F` is filtered by the subsheaves annihilated by the powers
of `J`; each successive quotient is killed by `J`, hence has its stalk at `ξ` killed by the
maximal ideal there, and [Stacks, Tag 01YE] produces a direct image of a finite sum of copies of
one ideal sheaf mapping into it, isomorphically near `ξ`. A support that is not irreducible is
cut into two strictly smaller pieces by [Stacks, Tag 01YD].

## Main definitions

No new public definitions are introduced.

## Main results

* `Stacks.AlgebraicGeometry.CoherentDevissage.exists_filtration_by_integral_ideal_pushforwards`:
  **[Stacks, Tag 01YF]**, as a monotone chain of subobjects of `F` indexed by `Fin (n + 1)` from
  `⊥` to `⊤`, with coherent terms, each successive quotient being the direct image of a nonzero
  coherent sheaf of ideals on an integral closed subscheme.
* `Stacks.AlgebraicGeometry.CoherentDevissage.hasIdealFiltration`: every coherent module on a
  Noetherian scheme satisfies the predicate `HasIdealFiltration`, which is the form in which the
  dévissage engine of [Stacks, Tag 01YG] consumes the filtration.

## References

* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01YD](https://stacks.math.columbia.edu/tag/01YD)
* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.DevissageNoetherian (isClosed_supp_of_isCoherent
  isZero_of_supp_eq_empty)
open Stacks.AlgebraicGeometry.IrreducibleDevissage (supp_subset_of_epi)
open Stacks.AlgebraicGeometry.RegularIdealSheaf (kernelSubmodule definingIdealOfHom
  mem_definingIdealOfHom)
open Stacks.SheafOfModules.OnSpace (sheafHom)

universe u

namespace Stacks.AlgebraicGeometry.CoherentDevissage

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

/-! ### The powers of an ideal acting on a module -/

/-- A section of the sectionwise kernel is killed by the morphism. -/
private theorem kernelSubmodule_condition {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : _root_.SheafOfModules.{u} R} (f : M ⟶ N) :
    (kernelSubmodule f).ι ≫ f = 0 := by
  ext U x
  exact x.property

/-- A morphism killed by `f` factors through the sectionwise kernel of `f`. -/
private def kernelSubmoduleLift {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N L : _root_.SheafOfModules.{u} R} (f : M ⟶ N) (g : L ⟶ M) (hg : g ≫ f = 0) :
    L ⟶ (kernelSubmodule f).toSheafOfModules where
  val :=
    { app := fun U => ModuleCat.ofHom ((g.val.app U).hom.codRestrict _ (fun x =>
        congrArg (fun k : L ⟶ N => k.val.app U x) hg))
      naturality := fun {U V} h => by
        ext x
        exact Subtype.ext (PresheafOfModules.naturality_apply g.val h x) }

/-- The factorisation through the sectionwise kernel is compatible with its inclusion. -/
private theorem kernelSubmoduleLift_ι {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N L : _root_.SheafOfModules.{u} R} (f : M ⟶ N) (g : L ⟶ M) (hg : g ≫ f = 0) :
    kernelSubmoduleLift f g hg ≫ (kernelSubmodule f).ι = g := rfl

/-- The sectionwise kernel of a morphism is its categorical kernel. -/
private def kernelSubmoduleIso {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : _root_.SheafOfModules.{u} R} (f : M ⟶ N) :
    (kernelSubmodule f).toSheafOfModules ≅ kernel f where
  hom := kernel.lift f (kernelSubmodule f).ι (kernelSubmodule_condition f)
  inv := kernelSubmoduleLift f (kernel.ι f) (kernel.condition f)
  hom_inv_id := by
    apply (cancel_mono (kernelSubmodule f).ι).mp
    simp only [Category.assoc, kernelSubmoduleLift_ι, kernel.lift_ι, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (kernel.ι f)).mp
    simp only [Category.assoc, kernel.lift_ι, kernelSubmoduleLift_ι, Category.id_comp]

section IdealAction

attribute [local implicit_reducible] restrFun ORestr PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ ModuleCat.restrictScalars internalHom

/-- A section of the ideal `J` over an object `V` of the slice site at `U`, read as a section of
the structure presheaf over `V.left`. Naming it fixes one spelling of the ring, which instance
search cannot connect to the module index by itself. -/
private abbrev idealValue {X : RingedSpace.{u, u}}
    (J : (SheafOfModules.unit (structureSheafRing X)).Submodule)
    {U : TopologicalSpace.Opens X} (V : (Over U)ᵒᵖ)
    (r : ((restrFun X.presheaf U).obj J.toSheafOfModules.val).obj V) :
    X.presheaf.obj (op V.unop.left) :=
  r.val

/-- A scalar on the slice site at `U`, read as a section of the structure presheaf. -/
private abbrev restrScalar {X : RingedSpace.{u, u}}
    {U : TopologicalSpace.Opens X} (V : (Over U)ᵒᵖ) (a : (ORestr X.presheaf U).obj V) :
    X.presheaf.obj (op V.unop.left) :=
  a

/-- The local endomorphism `r ↦ r • s` of `J` attached to a section `s` of `F`, as a section of
the sheaf-hom from `J` to `F`. -/
private def idealActionSection {X : RingedSpace.{u, u}}
    (J : (SheafOfModules.unit (structureSheafRing X)).Submodule)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X))
    (U : TopologicalSpace.Opens X) (s : F.val.obj (op U)) :
    (sheafHom X J.toSheafOfModules F).val.obj (op U) where
  app V := ModuleCat.ofHom
    { toFun := fun r => idealValue J V r • Stacks.SheafOfModules.OnSpace.resSection X F V s
      map_add' := fun _ _ => add_smul _ _ _
      map_smul' := fun a r =>
        mul_smul (restrScalar V a) (idealValue J V r)
          (Stacks.SheafOfModules.OnSpace.resSection X F V s) }
  naturality {V W} k := by
    ext r
    have hres : (F.val.map W.unop.hom.op).hom s =
        (F.val.map k.unop.left.op).hom ((F.val.map V.unop.hom.op).hom s) := by
      rw [← Over.w k.unop, op_comp, PresheafOfModules.map_comp]
      rfl
    have hsmul := PresheafOfModules.map_smul F.val k.unop.left.op (idealValue J V r)
      (Stacks.SheafOfModules.OnSpace.resSection X F V s)
    have h : (X.presheaf.map k.unop.left.op).hom (idealValue J V r) •
          Stacks.SheafOfModules.OnSpace.resSection X F W s =
        (F.val.map k.unop.left.op).hom (idealValue J V r •
          Stacks.SheafOfModules.OnSpace.resSection X F V s) := by
      refine Eq.trans ?_ hsmul.symm
      exact congrArg (fun y : F.val.obj (op W.unop.left) =>
        (X.presheaf.map k.unop.left.op).hom (idealValue J V r) • y) hres
    exact h

/-- The action of an ideal `J` on a module `F`, as a morphism `F ⟶ SheafHom(J, F)` sending a
section `s` to the endomorphism `r ↦ r • s`. -/
private def idealAction {X : RingedSpace.{u, u}}
    (J : (SheafOfModules.unit (structureSheafRing X)).Submodule)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    F ⟶ sheafHom X J.toSheafOfModules F where
  val := {
    app U := by
      letI := (F.val.obj U).isModule
      letI := ((sheafHom X J.toSheafOfModules F).val.obj U).isModule
      exact ModuleCat.ofHom (X := F.val.obj U)
        (Y := (sheafHom X J.toSheafOfModules F).val.obj U) {
      toFun := idealActionSection J F U.unop
      map_add' := by
        intro s t
        apply PresheafOfModules.hom_ext
        intro V
        ext r
        have hm : (F.val.map V.unop.hom.op).hom (s + t) =
            (F.val.map V.unop.hom.op).hom s + (F.val.map V.unop.hom.op).hom t :=
          map_add _ _ _
        have h : idealValue J V r •
              Stacks.SheafOfModules.OnSpace.resSection X F V (s + t) =
            idealValue J V r • Stacks.SheafOfModules.OnSpace.resSection X F V s +
              idealValue J V r • Stacks.SheafOfModules.OnSpace.resSection X F V t := by
          rw [show Stacks.SheafOfModules.OnSpace.resSection X F V (s + t) =
            Stacks.SheafOfModules.OnSpace.resSection X F V s +
              Stacks.SheafOfModules.OnSpace.resSection X F V t from hm, smul_add]
        exact h
      map_smul' := by
        intro a s
        apply PresheafOfModules.hom_ext
        intro V
        ext r
        have hm : Stacks.SheafOfModules.OnSpace.resSection X F V (a • s) =
            (X.presheaf.map V.unop.hom.op).hom a •
              Stacks.SheafOfModules.OnSpace.resSection X F V s :=
          PresheafOfModules.map_smul F.val V.unop.hom.op a s
        have h : idealValue J V r •
              Stacks.SheafOfModules.OnSpace.resSection X F V (a • s) =
            (X.presheaf.map V.unop.hom.op).hom a •
              (idealValue J V r • Stacks.SheafOfModules.OnSpace.resSection X F V s) := by
          rw [hm, smul_smul, smul_smul]
          exact congrArg
            (fun c : X.presheaf.obj (op V.unop.left) =>
              c • Stacks.SheafOfModules.OnSpace.resSection X F V s)
            (mul_comm _ _)
        exact h }
    naturality {U V} k := by
      ext s
      apply PresheafOfModules.hom_ext
      intro W
      ext r
      have hm : (F.val.map W.unop.hom.op).hom ((F.val.map k).hom s) =
          (F.val.map (W.unop.hom ≫ k.unop).op).hom s := by
        rw [op_comp, PresheafOfModules.map_comp]
        rfl
      have h : idealValue J W r •
            (F.val.map W.unop.hom.op).hom ((F.val.map k).hom s) =
          idealValue J W r • (F.val.map (W.unop.hom ≫ k.unop).op).hom s :=
        congrArg (fun y : F.val.obj (op W.unop.left) => idealValue J W r • y) hm
      exact h }

/-- The `n`-fold iterated sheaf-hom `SheafHom(J, SheafHom(J, ⋯ SheafHom(J, F)))`. -/
private def iteratedIdealHom {X : RingedSpace.{u, u}}
    (J : (SheafOfModules.unit (structureSheafRing X)).Submodule)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    ℕ → _root_.SheafOfModules.{u} (structureSheafRing X)
  | 0 => F
  | n + 1 => sheafHom X J.toSheafOfModules (iteratedIdealHom J F n)

/-- The `n`-fold iterated action of `J`, whose kernel is the subsheaf of sections annihilated
by `J ^ n`. -/
private def iteratedIdealAction {X : RingedSpace.{u, u}}
    (J : (SheafOfModules.unit (structureSheafRing X)).Submodule)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (n : ℕ) → F ⟶ iteratedIdealHom J F n
  | 0 => 𝟙 F
  | n + 1 => iteratedIdealAction J F n ≫ idealAction J (iteratedIdealHom J F n)

/-- The iterated sheaf-hom of coherent modules is coherent, by [Stacks, Tag 01CQ]: a coherent
module is of finite presentation. -/
private theorem iteratedIdealHom_isCoherent {X : RingedSpace.{u, u}}
    (J : (SheafOfModules.unit (structureSheafRing X)).Submodule)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X))
    (hJ : J.toSheafOfModules.IsCoherent) (hF : F.IsCoherent) (n : ℕ) :
    (iteratedIdealHom J F n).IsCoherent := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    have hfp : J.toSheafOfModules.IsFinitePresentation :=
      @isFinitePresentation_of_isCoherent _ _ _ _ hJ
    exact ProperMapping.isCoherent_of_stacks
      (@Stacks.SheafOfModules.sheafHom_isCoherent X.carrier X.presheaf
        (structureSheafRing X).property J.toSheafOfModules (iteratedIdealHom J F n)
        hfp (ProperMapping.stacksIsCoherent ih))

/-- The subsheaf of sections of `F` annihilated by `J ^ n`. -/
private abbrev idealAnnihilator {X : RingedSpace.{u, u}}
    (J : (SheafOfModules.unit (structureSheafRing X)).Submodule)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) (n : ℕ) :=
  kernelSubmodule (iteratedIdealAction J F n)

/-- The annihilator filtration is increasing. -/
private theorem idealAnnihilator_le_succ {X : RingedSpace.{u, u}}
    (J : (SheafOfModules.unit (structureSheafRing X)).Submodule)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) (n : ℕ) :
    idealAnnihilator J F n ≤ idealAnnihilator J F (n + 1) := by
  intro U s hs
  change (idealAction J (iteratedIdealHom J F n)).val.app U
    ((iteratedIdealAction J F n).val.app U s) = 0
  change (iteratedIdealAction J F n).val.app U s = 0 at hs
  rw [hs, map_zero]

/-- If the action of `J` sends a section `s` of `F` to zero, then `J` kills `s`. -/
private theorem smul_eq_zero_of_idealActionSection_eq_zero {X : RingedSpace.{u, u}}
    (J : (SheafOfModules.unit (structureSheafRing X)).Submodule)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X))
    (U : TopologicalSpace.Opens X) (s : F.val.obj (op U))
    (h : idealActionSection J F U s = 0) (r : X.presheaf.obj (op U)) (hr : r ∈ J.obj (op U)) :
    r • s = 0 := by
  have hz := congrArg (fun t => (t.app (op (Over.mk (𝟙 U)))).hom ⟨r, hr⟩) h
  dsimp [idealActionSection] at hz
  change r • (show F.val.obj (op U) from F.val.map (𝟙 U).op s) = 0 at hz
  have hm : F.val.map (𝟙 U).op s = s := by rw [op_id, F.val.map_id]; rfl
  rwa [hm] at hz

/-- If a morphism `φ` kills the multiples by sections of `J` of the restrictions of `s`, then the
action of `J` kills the image of `s` under `φ`. -/
private theorem idealValue_smul_map_eq_zero {X : RingedSpace.{u, u}}
    (J : (SheafOfModules.unit (structureSheafRing X)).Submodule)
    {F G : _root_.SheafOfModules.{u} (structureSheafRing X)} (φ : F ⟶ G)
    (U : TopologicalSpace.Opens X) (s : F.val.obj (op U)) (V : (Over U)ᵒᵖ)
    (r : ((restrFun X.presheaf U).obj J.toSheafOfModules.val).obj V)
    (h : (φ.val.app (op V.unop.left)).hom
      (idealValue J V r • Stacks.SheafOfModules.OnSpace.resSection X F V s) = 0) :
    idealValue J V r • G.val.map V.unop.hom.op (φ.val.app (op U) s) = 0 := by
  rw [← PresheafOfModules.naturality_apply φ.val V.unop.hom.op s]
  exact (map_smul _ _ _).symm.trans h

/-- Multiplying a section annihilated by `J ^ (n + 1)` by a section of `J` lands in the
subsheaf annihilated by `J ^ n`. -/
private theorem smul_mem_idealAnnihilator {X : RingedSpace.{u, u}}
    (J : (SheafOfModules.unit (structureSheafRing X)).Submodule)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) (n : ℕ)
    (U : TopologicalSpace.Opens X) (r : X.presheaf.obj (op U)) (hr : r ∈ J.obj (op U))
    (s : F.val.obj (op U)) (hs : s ∈ (idealAnnihilator J F (n + 1)).obj (op U)) :
    r • s ∈ (idealAnnihilator J F n).obj (op U) := by
  change (iteratedIdealAction J F n).val.app (op U) (r • s) = 0
  rw [map_smul]
  exact smul_eq_zero_of_idealActionSection_eq_zero J (iteratedIdealHom J F n) U _ hs r hr

/-- A section killed by `J ^ n` on every smaller open is killed by the `n`-fold iterated
action. -/
private theorem iteratedIdealAction_eq_zero_of_pow_annihilation {X : RingedSpace.{u, u}}
    (J : (SheafOfModules.unit (structureSheafRing X)).Submodule)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) (n : ℕ)
    (U : TopologicalSpace.Opens X) (s : F.val.obj (op U))
    (h : ∀ (V : TopologicalSpace.Opens X) (i : V ⟶ U) (r : X.presheaf.obj (op V)),
      r ∈ (show Ideal (X.presheaf.obj (op V)) from J.obj (op V)) ^ n →
      r • F.val.map i.op s = 0) :
    (iteratedIdealAction J F n).val.app (op U) s = 0 := by
  induction n generalizing U s with
  | zero =>
    have hz := h U (𝟙 U) 1 (by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)
    have hm : (F.val.map (𝟙 U).op).hom s = s := by
      rw [op_id, F.val.map_id]; rfl
    rw [hm] at hz
    have h1 : (1 : X.presheaf.obj (op U)) • s = s := one_smul _ s
    have hgoal : s = 0 := h1.symm.trans hz
    exact hgoal
  | succ n ih =>
    apply PresheafOfModules.hom_ext
    intro V
    ext r
    have hkey : ((iteratedIdealAction J F n).val.app (op V.unop.left)).hom
        (idealValue J V r • Stacks.SheafOfModules.OnSpace.resSection X F V s) = 0 := by
      apply ih
      intro W k a ha
      rw [PresheafOfModules.map_smul, smul_smul]
      have hr : (X.presheaf.map k.op).hom (idealValue J V r) ∈ J.obj (op W) :=
        J.map k.op r.property
      have hp : a * (X.presheaf.map k.op).hom (idealValue J V r) ∈
          (show Ideal (X.presheaf.obj (op W)) from J.obj (op W)) ^ (n + 1) := by
        rw [pow_succ]
        exact Ideal.mul_mem_mul ha hr
      have hz := h W (k ≫ V.unop.hom) _ hp
      rwa [op_comp, PresheafOfModules.map_comp_apply] at hz
    exact idealValue_smul_map_eq_zero J (iteratedIdealAction J F n) U s V r hkey

/-- **`J` annihilates `F`**: every section of `J` kills every section of `F`. -/
private def IdealAnnihilates {X : RingedSpace.{u, u}}
    (J : (SheafOfModules.unit (structureSheafRing X)).Submodule)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) : Prop :=
  ∀ (U : TopologicalSpace.Opens X) (r : X.presheaf.obj (op U)), r ∈ J.obj (op U) →
    ∀ s : F.val.obj (op U), r • s = 0

/-- If the action of `J` on `F` vanishes then `J` annihilates `F`. -/
private theorem idealAnnihilates_of_idealAction_eq_zero {X : RingedSpace.{u, u}}
    (J : (SheafOfModules.unit (structureSheafRing X)).Submodule)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) (h : idealAction J F = 0) :
    IdealAnnihilates J F := by
  intro U r hr s
  exact smul_eq_zero_of_idealActionSection_eq_zero J F U s
    (congrArg (fun f => (f.val.app (op U)).hom s) h) r hr

/-- **`J` annihilates a cokernel** as soon as every multiple by a section of `J` of a section of
the target lifts to the source. -/
private theorem idealAnnihilates_cokernel {X : RingedSpace.{u, u}}
    (J : (SheafOfModules.unit (structureSheafRing X)).Submodule)
    {A B : _root_.SheafOfModules.{u} (structureSheafRing X)} (f : A ⟶ B)
    (h : ∀ (U : TopologicalSpace.Opens X) (r : X.presheaf.obj (op U)),
      r ∈ J.obj (op U) → ∀ b : B.val.obj (op U),
      ∃ a : A.val.obj (op U), (f.val.app (op U)).hom a = r • b) :
    IdealAnnihilates J (cokernel f) := by
  refine idealAnnihilates_of_idealAction_eq_zero J (cokernel f) ?_
  apply (cancel_epi (cokernel.π f)).mp
  rw [comp_zero]
  ext U b
  apply PresheafOfModules.hom_ext
  intro V
  ext r
  have hkey : ((cokernel.π f).val.app (op V.unop.left)).hom
      (idealValue J V r • Stacks.SheafOfModules.OnSpace.resSection X B V b) = 0 := by
    obtain ⟨a, ha⟩ := h V.unop.left (idealValue J V r) r.property
      (Stacks.SheafOfModules.OnSpace.resSection X B V b)
    rw [← ha]
    exact congrArg (fun q : A ⟶ cokernel f => (q.val.app (op V.unop.left)).hom a)
      (cokernel.condition f)
  exact idealValue_smul_map_eq_zero J (cokernel.π f) U.unop b V r hkey

/-- The subsheaf of sections annihilated by `J ^ 0` is zero: the zeroth iterated action is the
identity. -/
private theorem isZero_idealAnnihilator_zero {X : RingedSpace.{u, u}}
    (J : (SheafOfModules.unit (structureSheafRing X)).Submodule)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    IsZero (idealAnnihilator J F 0).toSheafOfModules := by
  apply IsZero.of_mono_eq_zero (idealAnnihilator J F 0).ι
  ext U s
  exact s.property

/-- If the `n`-fold iterated action of `J` kills every section of `F` then the subsheaf of
sections annihilated by `J ^ n` is all of `F`. -/
private def idealAnnihilatorIso {X : RingedSpace.{u, u}}
    (J : (SheafOfModules.unit (structureSheafRing X)).Submodule)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) (n : ℕ)
    (hn : ∀ (U : (TopologicalSpace.Opens X)ᵒᵖ) (s : F.val.obj U),
      (iteratedIdealAction J F n).val.app U s = 0) :
    (idealAnnihilator J F n).toSheafOfModules ≅ F := by
  have hzero : iteratedIdealAction J F n = 0 := by
    ext U s
    exact hn U s
  haveI : IsIso (kernel.ι (iteratedIdealAction J F n)) := by
    rw [hzero]
    infer_instance
  exact kernelSubmoduleIso (iteratedIdealAction J F n) ≪≫ asIso (kernel.ι _)

end IdealAction

/-- A section of the zero submodule vanishes. -/
private theorem eq_zero_of_mem_bot {X : Scheme.{u}} (F : X.Modules)
    (U : X.Opens) (s : Γ(F, U)) (hs : s ∈ (⊥ : F.Submodule).obj (op U)) : s = 0 :=
  (show (⊥ : F.Submodule) ≤ kernelSubmodule (𝟙 F) from bot_le) (op U) hs

/-- If `I ^ n • F` vanishes then, for a closed subscheme cut out by `I`, every section of the
`n`-th power of its defining ideal kills every section of `F`. -/
private theorem definingIdeal_pow_kills_of_idealPowerMultiple_eq_bot {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : X.Modules) (n : ℕ)
    (h : Stacks.Algebraization.idealPowerMultiple I n F = ⊥)
    (U : X.Opens) (r : Γ(X, U))
    (hr : r ∈ (show Ideal Γ(X, U) from
      (definingIdealOfHom I.subschemeι).obj (op U)) ^ n)
    (s : Γ(F, U)) : r • s = 0 := by
  let J := definingIdealOfHom I.subschemeι
  apply (Scheme.Modules.isSheaf F).section_ext
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  refine ⟨V, hVU, hxV, ?_⟩
  let k : V ⟶ U := homOfLE hVU
  have hJV : (show Ideal Γ(X, V) from J.obj (op V)) = I.ideal ⟨V, hV⟩ :=
    I.ker_subschemeι_app ⟨V, hV⟩
  have hm : Ideal.map (X.presheaf.map k.op).hom (show Ideal Γ(X, U) from J.obj (op U)) ≤
      (show Ideal Γ(X, V) from J.obj (op V)) :=
    Ideal.map_le_iff_le_comap.mpr (fun a ha => J.map k.op ha)
  have hrV : X.presheaf.map k.op r ∈ I.ideal ⟨V, hV⟩ ^ n := by
    rw [← hJV]
    apply pow_le_pow_left' hm n
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hr
  have hp := (Stacks.Algebraization.idealPowerMultiple_le_iff I n F ⊥).mp (le_of_eq h) ⟨V, hV⟩
  have hz := eq_zero_of_mem_bot F V
    ((show Γ(X, V) from X.presheaf.map k.op r) • (show Γ(F, V) from F.val.map k.op s))
    (hp (Submodule.smul_mem_smul hrV Submodule.mem_top))
  have hgoal : (show Γ(F, V) from F.presheaf.map k.op (r • s)) =
      (show Γ(F, V) from F.presheaf.map k.op 0) := by
    rwa [Scheme.Modules.map_smul, map_zero]
  exact hgoal

/-- The defining ideal of a closed immersion into a locally Noetherian scheme is coherent: it is
the kernel of the map from the structure sheaf to the direct image of the structure sheaf of the
subscheme, both of which are coherent. -/
private theorem definingIdeal_isCoherent {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (definingIdealOfHom i).toSheafOfModules.IsCoherent := by
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  let : (SheafOfModules.unit Z.ringCatSheaf).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  let f := SheafOfModules.unitToPushforwardObjUnit
    (RingedSpaceModuleAdjunction.structureSheafHom i.toLRSHom.toShHom)
  exact @isCoherent_of_iso _ _ _ _ _ (kernelSubmoduleIso f)
    (ProperMapping.isCoherent_kernel
      (CoherenceCriteria.structureSheaf_isCoherent X)
      (PushforwardCoherent.pushforward_isCoherent_of_isFinite i
        (SheafOfModules.unit Z.ringCatSheaf)) f)

/-- Each step of the annihilator filtration of a coherent module by a coherent ideal is
coherent, being the kernel of a morphism of coherent modules. -/
private theorem idealAnnihilator_isCoherent {X : Scheme.{u}}
    (J : (SheafOfModules.unit X.ringCatSheaf).Submodule) (F : X.Modules)
    (hJ : J.toSheafOfModules.IsCoherent) (hF : F.IsCoherent) (n : ℕ) :
    (idealAnnihilator (X := X.toRingedSpace) J F n).toSheafOfModules.IsCoherent :=
  @isCoherent_of_iso _ _ _ _ _ (kernelSubmoduleIso (iteratedIdealAction J F n))
    (ProperMapping.isCoherent_kernel hF (iteratedIdealHom_isCoherent J F hJ hF n) _)

/-! ### Noetherian induction on the support -/

/-- **A monomorphism of modules does not enlarge the support.** A monomorphism is detected on
stalks, so its stalk maps are injective and a nonzero element of a stalk upstairs produces one
downstairs. -/
theorem supp_subset_of_mono {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) [Mono f] :
    SheafOfModules.supp F ⊆ SheafOfModules.supp G := by
  have hm : @Mono (_root_.SheafOfModules.{u} X.ringCatSheaf) inferInstance F G f :=
    ⟨fun g h hcomp => (‹Mono f›).right_cancellation g h hcomp⟩
  have hms : Mono ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map f) :=
    CategoryTheory.preserves_mono_of_preservesLimit
      (_root_.SheafOfModules.toSheaf X.ringCatSheaf) f
  have hst := (TopCat.Presheaf.mono_iff_stalk_mono
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map f)).mp hms
  intro x hx
  obtain ⟨a, ha⟩ := hx
  refine ⟨((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map f).hom) a, fun hz => ha ?_⟩
  exact ((AddCommGrpCat.mono_iff_injective _).mp (hst x)) (hz.trans (map_zero _).symm)

/-- **An ideal acting nilpotently reduces the problem to modules it kills.** If `J ^ n` kills
`F` then `F` is filtered by the subsheaves annihilated by the powers of `J`, each successive
quotient is killed by `J`, and the hypothesis `hgood` filters those. -/
private theorem exists_integralFiltrationData_of_nilpotent
    {X : Scheme.{u}} [IsNoetherian X]
    (J : (SheafOfModules.unit X.ringCatSheaf).Submodule)
    (hJ : J.toSheafOfModules.IsCoherent)
    (T : Set X)
    (hgood : ∀ (G : X.Modules), G.IsCoherent → SheafOfModules.supp G ⊆ T →
      IdealAnnihilates (X := X.toRingedSpace) J G → Nonempty (IntegralFiltrationData G))
    (F : X.Modules) [hFc : F.IsCoherent] (hF : SheafOfModules.supp F ⊆ T)
    (n : ℕ)
    (hn : ∀ (U : (TopologicalSpace.Opens X.toRingedSpace)ᵒᵖ) (s : F.val.obj U),
      (iteratedIdealAction (X := X.toRingedSpace) J F n).val.app U s = 0) :
    Nonempty (IntegralFiltrationData F) := by
  classical
  let A (k : ℕ) := idealAnnihilator (X := X.toRingedSpace) J F k
  have hA (k : ℕ) : (A k).toSheafOfModules.IsCoherent :=
    idealAnnihilator_isCoherent J F hJ hFc k
  have hD (k : ℕ) : Nonempty (IntegralFiltrationData (A k).toSheafOfModules) := by
    induction k with
    | zero =>
      exact ⟨integralFiltrationData_of_isZero (isZero_idealAnnihilator_zero J F)⟩
    | succ k ih =>
      let f : (A k).toSheafOfModules ⟶ (A (k + 1)).toSheafOfModules :=
        ⟨PresheafOfModules.Submodule.homOfLE (idealAnnihilator_le_succ J F k)⟩
      have hmono : Mono f := (_root_.SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
        (inferInstanceAs (Mono (PresheafOfModules.Submodule.homOfLE
          (idealAnnihilator_le_succ J F k))))
      have hepi : Epi (cokernel.π f) := inferInstance
      have hQ : (cokernel f).IsCoherent :=
        ProperMapping.isCoherent_cokernel (hA k) (hA (k + 1)) f
      have hQT : SheafOfModules.supp (cokernel f) ⊆ T :=
        (supp_subset_of_epi (cokernel.π f) hepi).trans
          ((@supp_subset_of_mono X (A (k + 1)).toSheafOfModules F (A (k + 1)).ι
            (SheafOfModules.Submodule.instMonoι (A (k + 1)))).trans hF)
      have hzero : IdealAnnihilates (X := X.toRingedSpace) J (cokernel f) := by
        apply idealAnnihilates_cokernel
        intro U r hr b
        refine ⟨⟨r • b.val, smul_mem_idealAnnihilator J F k U r hr b.val b.property⟩, ?_⟩
        exact Subtype.ext rfl
      exact ⟨integralFiltrationData_of_mono_cokernel f hmono (hA k) (hA (k + 1))
        ih.some (hgood (cokernel f) hQ hQT hzero).some⟩
  exact ⟨integralFiltrationData_of_iso (idealAnnihilatorIso J F n hn) (hD n).some⟩

/-- **The irreducible case of the Noetherian induction.** A coherent module whose support is an
irreducible closed set `T` is filtered: the defining ideal of the reduced induced subscheme on
`T` is coherent and acts nilpotently on the module by [Stacks, Tag 01Y9], and the modules it
kills are handled by `integralFiltrationData_of_generic_annihilation`. -/
private theorem exists_integralFiltrationData_of_irreducible_support
    {X : Scheme.{u}} [IsNoetherian X] (T : TopologicalSpace.Closeds X)
    (hT : IsIrreducible (T : Set X))
    (ih : ∀ (G : X.Modules), G.IsCoherent → SheafOfModules.supp G ⊂ (T : Set X) →
      Nonempty (IntegralFiltrationData G))
    (F : X.Modules) [F.IsCoherent] (hF : SheafOfModules.supp F = (T : Set X)) :
    Nonempty (IntegralFiltrationData F) := by
  classical
  let I := Scheme.IdealSheafData.vanishingIdeal T
  let i := I.subschemeι
  have hi : Set.range i = (T : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have : IrreducibleSpace I.subscheme := by
    have : IrreducibleSpace (Set.range i) := Subtype.irreducibleSpace (hi.symm ▸ hT)
    exact i.isClosedEmbedding.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr inferInstance
  have : IsIntegral I.subscheme :=
    (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩
  let ξ := genericPoint I.subscheme
  have hξ := genericPoint_spec I.subscheme
  let J := definingIdealOfHom i
  have hJ : J.toSheafOfModules.IsCoherent := definingIdeal_isCoherent i
  obtain ⟨n, hn⟩ :=
    (Stacks.IdealPowerSupport.exists_idealPowerMultiple_eq_bot_iff_supp_subset F I).mpr
      (by simp [I, hF])
  refine exists_integralFiltrationData_of_nilpotent J hJ T ?_ F hF.le n ?_
  · intro G hG hs hzero
    exact ⟨integralFiltrationData_of_generic_annihilation i ξ hξ T hi ih G hs
      (stalkKilledByMaximalIdeal_of_definingIdeal_kills_sections i ξ hξ G
        fun U _ r s hr => hzero U r hr s)⟩
  · intro U s
    apply iteratedIdealAction_eq_zero_of_pow_annihilation
    intro V k r hr
    exact definingIdeal_pow_kills_of_idealPowerMultiple_eq_bot I F n hn V r hr
      (F.val.map k.op s)

/-- **The Noetherian induction of [Stacks, Tag 01YF].** Every coherent module on a Noetherian
scheme has a filtration: an empty support means the module vanishes, an irreducible support is
the previous step, and a reducible support is split into two strictly smaller closed pieces by
[Stacks, Tag 01YD]. -/
private theorem exists_integralFiltrationData {X : Scheme.{u}} [IsNoetherian X]
    (F : X.Modules) [F.IsCoherent] : Nonempty (IntegralFiltrationData F) := by
  classical
  have hAll : ∀ T : TopologicalSpace.Closeds X, ∀ G : X.Modules,
      G.IsCoherent → SheafOfModules.supp G = (T : Set X) →
      Nonempty (IntegralFiltrationData G) := by
    intro T
    refine (wellFounded_lt : WellFounded ((· < ·) :
      TopologicalSpace.Closeds X → TopologicalSpace.Closeds X → Prop)).induction
        (C := fun T => ∀ G : X.Modules, G.IsCoherent →
          SheafOfModules.supp G = (T : Set X) → Nonempty (IntegralFiltrationData G)) T ?_
    intro T ih G hG hs
    have hsmall : ∀ H : X.Modules, H.IsCoherent →
        SheafOfModules.supp H ⊂ (T : Set X) → Nonempty (IntegralFiltrationData H) := by
      intro H hH hsub
      exact ih ⟨SheafOfModules.supp H, isClosed_supp_of_isCoherent H hH⟩ hsub H hH rfl
    by_cases he : (T : Set X) = ∅
    · exact ⟨integralFiltrationData_of_isZero (isZero_of_supp_eq_empty G (hs.trans he))⟩
    by_cases hp : IsPreirreducible (T : Set X)
    · exact exists_integralFiltrationData_of_irreducible_support T
        ⟨Set.nonempty_iff_ne_empty.mpr he, hp⟩ hsmall G hs
    · rw [isPreirreducible_iff_isClosed_union_isClosed] at hp
      push Not at hp
      obtain ⟨Z₁, Z₂, hZ₁, hZ₂, hcover, hn₁, hn₂⟩ := hp
      have h₁ : (T : Set X) ∩ Z₁ ⊂ T :=
        ⟨Set.inter_subset_left, fun h => hn₁ (fun x hx => (h hx).2)⟩
      have h₂ : (T : Set X) ∩ Z₂ ⊂ T :=
        ⟨Set.inter_subset_left, fun h => hn₂ (fun x hx => (h hx).2)⟩
      have hcover' : SheafOfModules.supp G = ((T : Set X) ∩ Z₁) ∪ ((T : Set X) ∩ Z₂) := by
        rw [hs, ← Set.inter_union_distrib_left, Set.inter_eq_left.mpr hcover]
      obtain ⟨A, B, f, g, w, hex, hA, hB, hsA, hsB⟩ :=
        HigherDirectImageCoherent.exists_shortExact_coherent_of_supp_eq_union X G
          ((T : Set X) ∩ Z₁) ((T : Set X) ∩ Z₂)
          (T.isClosed.inter hZ₁) (T.isClosed.inter hZ₂) hcover'
      exact ⟨integralFiltrationData_of_shortExact_any (ShortComplex.mk f g w) hex hG hB
        (hsmall A hA (hsA.trans_ssubset h₂)).some
        (hsmall B hB (hsB.trans_ssubset h₁)).some⟩
  exact hAll ⟨SheafOfModules.supp F, isClosed_supp_of_isCoherent F inferInstance⟩ F inferInstance
    rfl

/-! ### The filtration -/

/-- **[Stacks, Tag 01YF].** A coherent module on a Noetherian scheme has a finite filtration by
coherent submodules, starting at `⊥` and ending at `⊤`, whose successive quotients are direct
images of nonzero coherent sheaves of ideals on integral closed subschemes. -/
@[stacks 01YF]
public theorem exists_filtration_by_integral_ideal_pushforwards
    (X : Scheme.{u}) [IsNoetherian X] (F : X.Modules) [F.IsCoherent] :
    ∃ (n : ℕ) (G : Fin (n + 1) → Subobject F) (hG : Monotone G),
      G 0 = ⊥ ∧ G (Fin.last n) = ⊤ ∧
      (∀ j : Fin (n + 1), (G j : X.Modules).IsCoherent) ∧
      ∀ j : Fin n,
        ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (_ : IsClosedImmersion i) (_ : IsIntegral Z)
          (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
          I.toSheafOfModules.IsCoherent ∧ ¬ IsZero I.toSheafOfModules ∧
          Nonempty (cokernel (Subobject.ofLE (G j.castSucc) (G j.succ)
            (hG j.castSucc_le_succ)) ≅
            (Scheme.Modules.pushforward i).obj I.toSheafOfModules) := by
  obtain ⟨D⟩ := exists_integralFiltrationData F
  exact ⟨D.length, D.step, D.monotone, D.start, D.finish, D.coherent, D.factor⟩

/-- **Every coherent module on a Noetherian scheme has a dévissage filtration.** This is
[Stacks, Tag 01YF] in the form the dévissage engine of [Stacks, Tag 01YG] consumes: the chain of
subobjects produced above is reindexed by `ℕ` and the coherence of its successive quotients,
which `HasIdealFiltration` carries, is derived from the coherence of its terms. -/
public theorem hasIdealFiltration (X : Scheme.{u}) [IsNoetherian X] (F : X.Modules)
    [F.IsCoherent] : HasIdealFiltration F := by
  obtain ⟨n, G, hG, hbot, htop, hcoh, hquot⟩ :=
    exists_filtration_by_integral_ideal_pushforwards X F
  exact hasIdealFiltration_of_subobjectFiltration n G hG hbot htop hcoh hquot

end Stacks.AlgebraicGeometry.CoherentDevissage

end

end
