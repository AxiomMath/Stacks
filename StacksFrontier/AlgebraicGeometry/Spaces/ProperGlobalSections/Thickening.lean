module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsSquareComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsRingHomSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.FormalFunctions

/-!
# The infinitesimal thickenings of an algebraic space over `Spec A`

For an algebraic space `X` over `Spec A` and an ideal `I ⊆ A`, the quotient
`𝒪_X / (I 𝒪_X)ⁿ⁺¹` is the direct image of the structure sheaf of a closed subspace of `X`, and its
global sections are the global functions of that closed subspace.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules
open Stacks.Sheaves.RingedToposModules (fSharpSet pushforwardModules)
open CategoryTheory.Sheaf (terminalHomEquivSections)

section StructureProjection

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)

/-- **Global sections of the structure projection of a closed subspace are restriction of
functions**: the structure projection `𝒪_X ⟶ i_*𝒪_Z` on global sections, followed by the
identification `Γ(X, i_*𝒪_Z) = Γ(Z, 𝒪_Z)` of Stacks 0732, is the ring map
`Γ(X, 𝒪_X) ⟶ Γ(Z, 𝒪_Z)` induced by the inclusion. -/
theorem globalSectionsPushforwardIsoSite_hom_structureProjection
    (s : (SheafOfModules.unit (structureRingSheaf B S hS X)).sections) :
    (((globalSectionsPushforwardIsoSite B S hS (subspaceInclusion B S hS X Z)).hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS ⟨Z.1.toFunctor, Z.2.1⟩))).hom
      (SheafOfModules.sectionsMap (structureProjection B S hS X Z) s)).1 =
      (globalSectionsRingHomSite B S hS (subspaceInclusion B S hS X Z) ⟨s.1, s.2⟩).1 := by
  refine (congrArg Subtype.val (globalSectionsPushforwardIsoSite_hom_app_apply
    (subspaceInclusion B S hS X Z) (SheafOfModules.unit _)
    (SheafOfModules.sectionsMap (structureProjection B S hS X Z) s))).trans ?_
  have key : (terminalHomEquivSections _).symm
        (modulePushforwardSectionsEquivToposPushforward (subspaceInclusion B S hS X Z)
          (SheafOfModules.unit (structureRingSheaf B S hS ⟨Z.1.toFunctor, Z.2.1⟩))
          (SheafOfModules.sectionsMap (structureProjection B S hS X Z) s)) =
      Sheaf.ringSectionHom
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)
          ⟨s.1, s.2⟩ ≫
        fSharpSet (smallEtaleRingedToposModulesHom B S hS (subspaceInclusion B S hS X Z)) := by
    refine CategoryTheory.Sheaf.hom_ext_sections fun V p => ?_
    exact (congrArg (fun φ => (CategoryTheory.Sheaf.sectionsFunctor _ V).map
      (Sheaf.ringSectionHom
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)
        ⟨s.1, s.2⟩ ≫ φ) p)
      (fSharpSet_smallEtaleRingedToposModulesHom B S hS (subspaceInclusion B S hS X Z))).symm
  have h := ringSectionHom_globalSectionsRingHom
    (smallEtaleRingedToposModulesHom B S hS (subspaceInclusion B S hS X Z)) ⟨s.1, s.2⟩
  refine (congrArg (fun φ => (terminalHomEquivSections _
    ((smallEtaleRingedToposModulesHom B S hS
        (subspaceInclusion B S hS X Z)).toToposHom.pushforwardTerminalHomEquiv
      _ φ)).1) key).trans ?_
  change (terminalHomEquivSections (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS ⟨Z.1.toFunctor, Z.2.1⟩).O))
    ((smallEtaleRingedToposModulesHom B S hS
        (subspaceInclusion B S hS X Z)).toToposHom.pushforwardTerminalHomEquiv
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS ⟨Z.1.toFunctor, Z.2.1⟩).O))
      (Sheaf.ringSectionHom
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)
          ⟨s.1, s.2⟩ ≫
        fSharpSet (smallEtaleRingedToposModulesHom B S hS (subspaceInclusion B S hS X Z))))).1 =
      (globalSectionsRingHom (smallEtaleRingedToposModulesHom B S hS (subspaceInclusion B S hS X Z))
        ⟨s.1, s.2⟩).1
  exact (congrArg (fun φ => (terminalHomEquivSections (Sheaf.ringSheaf
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS ⟨Z.1.toFunctor, Z.2.1⟩).O))
    φ).1) h).symm

/-- **The structure projection `𝒪_X ⟶ i_*𝒪_Z` of a closed subspace is the canonical morphism
`1 ⟶ i_*1` of the morphism of small étale ringed topoi**, read through the comparison of the two
spellings of the direct image. -/
theorem pushforwardUnitSection_comp_modulePushforwardIso_hom :
    pushforwardUnitSection (smallEtaleRingedToposModulesHom B S hS (subspaceInclusion B S hS X Z)) ≫
        (modulePushforwardIso B S hS (subspaceInclusion B S hS X Z)).hom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS ⟨Z.1.toFunctor, Z.2.1⟩).O)) =
      structureProjection B S hS X Z := by
  have h := moduleSheafFunctor_map_pushforwardUnitSection
    (smallEtaleRingedToposModulesHom B S hS (subspaceInclusion B S hS X Z))
  have h2 := fSharpSet_smallEtaleRingedToposModulesHom B S hS (subspaceInclusion B S hS X Z)
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine (modulePushforwardIso_hom_app_val_app B S hS (subspaceInclusion B S hS X Z)
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS ⟨Z.1.toFunctor, Z.2.1⟩).O)) U
    ((pushforwardUnitSection (smallEtaleRingedToposModulesHom B S hS
      (subspaceInclusion B S hS X Z))).val.app U x)).trans ?_
  exact (congrArg (fun φ => φ.hom.app U x) h).trans (congrArg (fun φ => φ.hom.app U x) h2)

end StructureProjection

end AlgebraicGeometry.Space

namespace Stacks.Cohomology.SiteModules

open Stacks.Sheaves.RingedToposModules (pushforwardModules)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe w w' w'' v v' v'' u₁ u' u''

section TransitionComparison

variable {X : AlgebraicGeometry.RingedTopos.{v, u₁, w}}
    {Y : AlgebraicGeometry.RingedTopos.{v', u', w'}}
    {Z : AlgebraicGeometry.RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (φ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom Y Z)
  (χ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Z)
  (τ₀ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ⟶ χ.toToposHom.pushforward)
  (τ : pushforwardModules φ ⋙ pushforwardModules ψ ⟶ pushforwardModules χ)
  (hτ : ∀ N : SheafOfModules.{w} (ringSheaf X.O),
    (Sheaf.moduleSheafFunctor (ringSheaf Z.O)).map (τ.app N) =
      τ₀.app (Sheaf.moduleSheaf (ringSheaf X.O) N))

include hτ

/-- **A map `ψ_*1 ⟶ χ_*1` under the canonical morphisms from `1` is restriction along `φ` on
global sections**, for `χ` presented as the composite of `φ` and `ψ` and the canonical morphism of
`ψ` an epimorphism. -/
theorem globalSectionsPushforwardEquiv_comp_eq_globalSectionsRingHom
    (t : (pushforwardModules ψ).obj (SheafOfModules.unit (ringSheaf Y.O)) ⟶
      (pushforwardModules χ).obj (SheafOfModules.unit (ringSheaf X.O)))
    [hψ : Epi (pushforwardUnitSection ψ)]
    (ht : pushforwardUnitSection ψ ≫ t = pushforwardUnitSection χ)
    (b : SheafOfModules.unit (ringSheaf Z.O) ⟶
      (pushforwardModules ψ).obj (SheafOfModules.unit (ringSheaf Y.O))) :
    (globalSectionsPushforwardEquiv χ _ (SheafOfModules.unitHomEquiv _ (b ≫ t))).1 =
      (globalSectionsRingHom φ
        ⟨(globalSectionsPushforwardEquiv ψ _ (SheafOfModules.unitHomEquiv _ b)).1,
          (globalSectionsPushforwardEquiv ψ _ (SheafOfModules.unitHomEquiv _ b)).2⟩).1 := by
  have htt : t = (pushforwardModules ψ).map (pushforwardUnitSection φ) ≫
      τ.app (SheafOfModules.unit (ringSheaf X.O)) :=
    (cancel_epi (pushforwardUnitSection ψ)).1
      (ht.trans (pushforwardUnitSection_natTrans φ ψ χ τ₀ τ hτ).symm)
  subst htt
  rw [globalSectionsPushforwardEquiv_apply, globalSectionsPushforwardEquiv_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← Category.assoc,
    pushforwardUnitHomEquiv_natTrans φ ψ χ τ₀ τ hτ, pushforwardUnitHomEquiv_comp,
    ← unitEnd_unitEndSection (ringSheaf Y.O) (pushforwardUnitHomEquiv ψ _ b),
    ← pushforwardUnitEndMap_eq, ← unitEnd_globalSectionsRingHom]
  funext U
  exact (one_mul (M := (ringSheaf X.O).obj.obj U) _).trans
    (congrArg (fun a => (globalSectionsRingHom φ a).1 U)
      (Subtype.ext (funext fun V => (one_mul (M := (ringSheaf Y.O).obj.obj V) _).symm)))

/-- **Transitions between direct images of unit modules are restriction along `φ`.** Let
`q : Q' ⟶ Q` be compatible with morphisms `p' : 1 ⟶ Q'` (an epimorphism) and `p : 1 ⟶ Q` which are
identified with the canonical morphisms `1 ⟶ ψ_*1` and `1 ⟶ χ_*1`. On global sections `q` is
restriction along `φ`. -/
theorem globalSectionsPushforwardEquiv_transition
    {Q Q' : SheafOfModules.{w''} (ringSheaf Z.O)} (p' : SheafOfModules.unit (ringSheaf Z.O) ⟶ Q')
    (p : SheafOfModules.unit (ringSheaf Z.O) ⟶ Q) (q : Q' ⟶ Q) (hq : p' ≫ q = p)
    [hψ : Epi (pushforwardUnitSection ψ)]
    (c' : Q' ≅ (pushforwardModules ψ).obj (SheafOfModules.unit (ringSheaf Y.O)))
    (c : Q ≅ (pushforwardModules χ).obj (SheafOfModules.unit (ringSheaf X.O)))
    (hc' : p' ≫ c'.hom = pushforwardUnitSection ψ) (hc : p ≫ c.hom = pushforwardUnitSection χ)
    (b : SheafOfModules.unit (ringSheaf Z.O) ⟶ Q') :
    (globalSectionsPushforwardEquiv χ _ (SheafOfModules.unitHomEquiv _ (b ≫ q ≫ c.hom))).1 =
      (globalSectionsRingHom φ
        ⟨(globalSectionsPushforwardEquiv ψ _ (SheafOfModules.unitHomEquiv _ (b ≫ c'.hom))).1,
          (globalSectionsPushforwardEquiv ψ _
            (SheafOfModules.unitHomEquiv _ (b ≫ c'.hom))).2⟩).1 := by
  have ht : pushforwardUnitSection ψ ≫ c'.inv ≫ q ≫ c.hom = pushforwardUnitSection χ := by
    rw [← hc', Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% hq, hc]
  have key := globalSectionsPushforwardEquiv_comp_eq_globalSectionsRingHom φ ψ χ τ₀ τ hτ
    (c'.inv ≫ q ≫ c.hom) ht (b ≫ c'.hom)
  rwa [Category.assoc, Iso.hom_inv_id_assoc] at key

end TransitionComparison

end Stacks.Cohomology.SiteModules

namespace AlgebraicGeometry.Space

open Stacks.Cohomology.SiteModules
open Stacks.Sheaves.RingedToposModules (fSharpSet pushforwardModules)

section TransitionsSpaces

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The unit module of the small étale ringed topos of an algebraic space. -/
abbrev toposUnit (Y : AlgebraicSpaces B S hS) :=
  SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O)

/-- The identification of global sections of a direct image, on a section given by a morphism out
of the free module of rank one, is the comparison of Stacks 0732 for the morphism of ringed topoi.
-/
theorem globalSectionsPushforwardIsoSite_hom_unitHomEquiv {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (N : Modules.{u, u} B S hS Y.1 Y.2) (Q : Modules.{u, u} B S hS X.1 X.2)
    (c : SheafOfModules.unit _ ⟶ Q) (d : Q ⟶ (modulePushforward B S hS f).obj N) :
    ((globalSectionsPushforwardIsoSite B S hS f).hom.app N).hom
        (SheafOfModules.sectionsMap d (SheafOfModules.unitHomEquiv Q c)) =
      globalSectionsPushforwardEquiv (smallEtaleRingedToposModulesHom B S hS f) N
        (SheafOfModules.unitHomEquiv _ (c ≫ d ≫ (modulePushforwardIso B S hS f).inv.app N)) :=
  rfl

/-- A bookkeeping identity in a category: moving an isomorphism across an equation. -/
theorem comp_comp_eq_of_comp_eq {C : Type*} [Category C] {a q m n : C} (p : a ⟶ q) (c : q ⟶ m)
    (P : a ⟶ n) (e : n ⟶ m) (einv : m ⟶ n) (he : e ≫ einv = 𝟙 _) (h : p ≫ c = P ≫ e) :
    p ≫ c ≫ einv = P := by
  rw [← Category.assoc, h, Category.assoc, he, Category.comp_id]

/-- A bookkeeping identity in a category: cancelling two isomorphisms inside a composite. -/
theorem comp_cancel_two_isos {C : Type*} [Category C] {a q' _q m' m n' n : C} (b : a ⟶ q')
    (c' : q' ⟶ m') (c'inv : m' ⟶ q') (hc' : c' ≫ c'inv = 𝟙 _) (e' : m' ⟶ n') (e'inv : n' ⟶ m')
    (he' : e' ≫ e'inv = 𝟙 _) (x : q' ⟶ m) (y : m ⟶ n) :
    (b ≫ c' ≫ e') ≫ e'inv ≫ c'inv ≫ x ≫ y = b ≫ x ≫ y := by
  simp only [Category.assoc, reassoc_of% he', reassoc_of% hc']

/-- A bookkeeping identity in a category: the transition condition, from its factors. -/
theorem comp_transition_eq {C : Type*} [Category C] {a q' q m' m n' n : C} (P' : a ⟶ n')
    (P : a ⟶ n) (p' : a ⟶ q') (p : a ⟶ q) (qq : q' ⟶ q) (hq : p' ≫ qq = p)
    (c' : q' ⟶ m') (c'inv : m' ⟶ q') (hc'i : c' ≫ c'inv = 𝟙 _) (c : q ⟶ m)
    (e' : n' ⟶ m') (e'inv : m' ⟶ n') (_he'i : e'inv ≫ e' = 𝟙 _) (e : n ⟶ m) (einv : m ⟶ n)
    (hei : e ≫ einv = 𝟙 _)
    (hc' : p' ≫ c' = P' ≫ e') (hc : p ≫ c = P ≫ e) :
    P' ≫ e' ≫ c'inv ≫ qq ≫ c ≫ einv = P := by
  rw [← reassoc_of% hc', reassoc_of% hc'i, reassoc_of% hq, reassoc_of% hc, hei, Category.comp_id]

end TransitionsSpaces

section Thickening

variable (A : Type u) [CommRing A] {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))}
  (X : AlgebraicSpaces B (Spec (.of A)) hA) (I : Ideal A)

/-- The ideal `(I · 𝒪_X)ⁿ⁺¹` of `𝒪_X`. -/
abbrev thickeningIdeal (n : ℕ) :
    (SheafOfModules.unit (structureRingSheaf B (Spec (.of A)) hA X)).Submodule :=
  idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) (n + 1)
    (SheafOfModules.unit _)

/-- The ideal `(I · 𝒪_X)ⁿ⁺¹` is quasi-coherent. -/
theorem isQuasicoherentOnSite_thickeningIdeal (n : ℕ) :
    (thickeningIdeal A X I n).toSheafOfModules.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 _ (SheafOfModules.unit _)
    inferInstance
    (isQuasicoherentOnSite_baseIdealSheaf A X I) (n + 1)

/-- **The `n`-th infinitesimal thickening** `X ×_{Spec A} Spec(A/Iⁿ⁺¹)`, as the closed subspace of
`X` cut out by `(I · 𝒪_X)ⁿ⁺¹` (Stacks 03MB). -/
noncomputable def thickening (n : ℕ) : ClosedSubspaces B (Spec (.of A)) hA X.1 :=
  (exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B (Spec (.of A)) hA X _
    (isQuasicoherentOnSite_thickeningIdeal A X I n)).choose

/-- The defining ideal of the `n`-th thickening is `(I · 𝒪_X)ⁿ⁺¹`. -/
theorem definingIdealSheaf_thickening (n : ℕ) :
    definingIdealSheaf B (Spec (.of A)) hA X (thickening A X I n) = thickeningIdeal A X I n :=
  (exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B (Spec (.of A)) hA X _
    (isQuasicoherentOnSite_thickeningIdeal A X I n)).choose_spec

/-- For `m ≤ n`, the `m`-th thickening is contained in the `n`-th. -/
theorem thickening_le {m n : ℕ} (h : m ≤ n) : (thickening A X I m).1 ≤ (thickening A X I n).1 :=
  le_of_forall_definingIdealAt_le B (Spec (.of A)) hA X _ _ fun U _ => by
    rw [← definingIdealSheaf_obj, ← definingIdealSheaf_obj, definingIdealSheaf_thickening,
      definingIdealSheaf_thickening]
    exact idealPowerMultiple_antitone B (Spec (.of A)) hA X.1 X.2 _ (Nat.succ_le_succ h) _ (op U)

attribute [local instance 5000] SheafOfModules.instAbelian

/-- The cokernel of the inclusion of an ideal equal to the defining ideal of a closed subspace is
the direct image of the structure sheaf of the subspace. -/
noncomputable def cokernelIsoOfDefiningIdealSheafEq {Y : AlgebraicSpaces B (Spec (.of A)) hA}
    (Z : ClosedSubspaces B (Spec (.of A)) hA Y.1)
    (N : (SheafOfModules.unit (structureRingSheaf B (Spec (.of A)) hA Y)).Submodule)
    (h : definingIdealSheaf B (Spec (.of A)) hA Y Z = N) :
    cokernel (C := Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2) N.ι ≅
      pushforwardStructureSheaf B (Spec (.of A)) hA Y Z := by
  subst h
  exact conormalAlgebraDegreeZeroIso B (Spec (.of A)) hA Y Z

/-- The quotient map onto the cokernel, followed by `cokernelIsoOfDefiningIdealSheafEq`, is the
structure projection of the closed subspace. -/
theorem π_comp_cokernelIsoOfDefiningIdealSheafEq_hom {Y : AlgebraicSpaces B (Spec (.of A)) hA}
    (Z : ClosedSubspaces B (Spec (.of A)) hA Y.1)
    (N : (SheafOfModules.unit (structureRingSheaf B (Spec (.of A)) hA Y)).Submodule)
    (h : definingIdealSheaf B (Spec (.of A)) hA Y Z = N) :
    cokernel.π (C := Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2) N.ι ≫
        (cokernelIsoOfDefiningIdealSheafEq A Z N h).hom =
      structureProjection B (Spec (.of A)) hA Y Z := by
  subst h
  exact cokernel_π_comp_conormalAlgebraDegreeZeroIso_hom B (Spec (.of A)) hA Y Z

/-- A map out of `𝒪_Y` that composes with `c` to the structure projection of a closed subspace is,
after `c` and the inverse of the direct image comparison, the canonical morphism `1 ⟶ i_*1`. -/
private theorem comp_comp_inv_app_eq_pushforwardUnitSection
    {Y : AlgebraicSpaces B (Spec (.of A)) hA}
    (Z : ClosedSubspaces B (Spec (.of A)) hA Y.1) {Q : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2}
    (p : SheafOfModules.unit _ ⟶ Q) (c : Q ⟶ pushforwardStructureSheaf B (Spec (.of A)) hA Y Z)
    (hc : p ≫ c = structureProjection B (Spec (.of A)) hA Y Z) :
    p ≫ c ≫ (modulePushforwardIso B (Spec (.of A)) hA
      (subspaceInclusion B (Spec (.of A)) hA Y Z)).inv.app
      (toposUnit B (Spec (.of A)) hA ⟨Z.1.toFunctor, Z.2.1⟩) =
      pushforwardUnitSection (smallEtaleRingedToposModulesHom B (Spec (.of A)) hA
        (subspaceInclusion B (Spec (.of A)) hA Y Z)) :=
  comp_comp_eq_of_comp_eq _ _ _ _ _
    (Iso.hom_inv_id_app (modulePushforwardIso B (Spec (.of A)) hA
      (subspaceInclusion B (Spec (.of A)) hA Y Z))
      (toposUnit B (Spec (.of A)) hA ⟨Z.1.toFunctor, Z.2.1⟩))
    (hc.trans (pushforwardUnitSection_comp_modulePushforwardIso_hom B (Spec (.of A)) hA Y Z).symm)

/-- The quotient map onto `𝒪_X / 𝓘_Z`, followed by the identification with the direct image at the
topos spelling, is the canonical morphism `1 ⟶ i_*1`. -/
theorem π_comp_cokernelIsoOfDefiningIdealSheafEq_hom_comp_inv
    {Y : AlgebraicSpaces B (Spec (.of A)) hA}
    (Z : ClosedSubspaces B (Spec (.of A)) hA Y.1)
    (N : (SheafOfModules.unit (structureRingSheaf B (Spec (.of A)) hA Y)).Submodule)
    (h : definingIdealSheaf B (Spec (.of A)) hA Y Z = N) :
    cokernel.π (C := Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2) N.ι ≫
        (cokernelIsoOfDefiningIdealSheafEq A Z N h).hom ≫
          (modulePushforwardIso B (Spec (.of A)) hA
            (subspaceInclusion B (Spec (.of A)) hA Y Z)).inv.app
            (toposUnit B (Spec (.of A)) hA ⟨Z.1.toFunctor, Z.2.1⟩) =
      pushforwardUnitSection (smallEtaleRingedToposModulesHom B (Spec (.of A)) hA
        (subspaceInclusion B (Spec (.of A)) hA Y Z)) := by
  subst h
  exact comp_comp_inv_app_eq_pushforwardUnitSection A Z _ _
    (cokernel_π_comp_conormalAlgebraDegreeZeroIso_hom B (Spec (.of A)) hA Y Z)

/-- `𝒪_X / (I 𝒪_X)ⁿ⁺¹` is the direct image of the structure sheaf of the `n`-th thickening. -/
noncomputable def thickeningQuotientIso (n : ℕ) :
    idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) (n + 1)
        (SheafOfModules.unit _) ≅
      pushforwardStructureSheaf B (Spec (.of A)) hA X (thickening A X I n) :=
  cokernelIsoOfDefiningIdealSheafEq A (thickening A X I n) _ (definingIdealSheaf_thickening A X I n)

/-- The quotient map onto `𝒪_X / (I 𝒪_X)ⁿ⁺¹`, followed by `thickeningQuotientIso`, is the
structure projection of the `n`-th thickening. -/
theorem π_comp_thickeningQuotientIso_hom (n : ℕ) :
    cokernel.π (C := Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (thickeningIdeal A X I n).ι ≫
        (thickeningQuotientIso A X I n).hom =
      structureProjection B (Spec (.of A)) hA X (thickening A X I n) :=
  π_comp_cokernelIsoOfDefiningIdealSheafEq_hom A _ _ _

/-- Global sections of a module identified with the direct image of the structure sheaf of a
closed subspace `Z` are the global sections of the structure sheaf of `Z`. -/
noncomputable def subspaceSectionsEquiv (Y : AlgebraicSpaces B (Spec (.of A)) hA)
    (Z : ClosedSubspaces B (Spec (.of A)) hA Y.1) {Q : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2}
    (c : Q ≅ pushforwardStructureSheaf B (Spec (.of A)) hA Y Z) :
    (sectionsOverBase A B hA Y.1 Y.2).obj Q ≅
      (sectionsOverBase A B hA (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B (Spec (.of A)) hA).1
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B (Spec (.of A)) hA).2).obj
        (SheafOfModules.unit (structureRingSheaf B (Spec (.of A)) hA ⟨Z.1.toFunctor, Z.2.1⟩)) :=
  (sectionsOverBase A B hA Y.1 Y.2).mapIso c ≪≫
    sectionsOverBasePushforwardIso A (subspaceInclusion B (Spec (.of A)) hA Y Z)
      (SheafOfModules.unit (structureRingSheaf B (Spec (.of A)) hA ⟨Z.1.toFunctor, Z.2.1⟩))

/-- `subspaceSectionsEquiv` applied to a global section `x` of `Q` is the image of `x` under `c`,
followed by the identification of global sections of the direct image. -/
theorem subspaceSectionsEquiv_apply (Y : AlgebraicSpaces B (Spec (.of A)) hA)
    (Z : ClosedSubspaces B (Spec (.of A)) hA Y.1) {Q : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2}
    (c : Q ≅ pushforwardStructureSheaf B (Spec (.of A)) hA Y Z)
    (x : (sectionsOverBase A B hA Y.1 Y.2).obj Q) :
    (subspaceSectionsEquiv A Y Z c).hom x =
      (sectionsOverBasePushforwardIso A (subspaceInclusion B (Spec (.of A)) hA Y Z)
        (SheafOfModules.unit (structureRingSheaf B (Spec (.of A)) hA ⟨Z.1.toFunctor, Z.2.1⟩))).hom
        (((sectionsOverBase A B hA Y.1 Y.2).map c.hom).hom x) := by
  rw [subspaceSectionsEquiv, Iso.trans_hom, ModuleCat.comp_apply, Functor.mapIso_hom]

/-- On global sections, a quotient map `𝒪_Y ⟶ Q` identified with the structure projection of a
closed subspace `Z`, followed by `Γ(Y, i_*𝒪_Z) = Γ(Z, 𝒪_Z)`, is restriction of functions. -/
theorem subspaceSectionsEquiv_map_eq_globalSectionsRingHomSite
    (Y : AlgebraicSpaces B (Spec (.of A)) hA) (Z : ClosedSubspaces B (Spec (.of A)) hA Y.1)
    {Q : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2}
    (p : SheafOfModules.unit _ ⟶ Q) (c : Q ≅ pushforwardStructureSheaf B (Spec (.of A)) hA Y Z)
    (hc : p ≫ c.hom = structureProjection B (Spec (.of A)) hA Y Z)
    (s : (sectionsOverBase A B hA Y.1 Y.2).obj (SheafOfModules.unit _)) :
    ((subspaceSectionsEquiv A Y Z c).hom (((sectionsOverBase A B hA Y.1 Y.2).map p).hom s)).1 =
      (globalSectionsRingHomSite B (Spec (.of A)) hA (subspaceInclusion B (Spec (.of A)) hA Y Z)
        ⟨s.1, s.2⟩).1 := by
  have h : ((sectionsOverBase A B hA Y.1 Y.2).map c.hom).hom
      (((sectionsOverBase A B hA Y.1 Y.2).map p).hom s) =
      SheafOfModules.sectionsMap (structureProjection B (Spec (.of A)) hA Y Z) s := by
    rw [← hc]
    rfl
  rw [subspaceSectionsEquiv_apply]
  exact (congrArg (fun z => ((sectionsOverBasePushforwardIso A
    (subspaceInclusion B (Spec (.of A)) hA Y Z)
    (SheafOfModules.unit (structureRingSheaf B (Spec (.of A)) hA ⟨Z.1.toFunctor, Z.2.1⟩))).hom
      z).1) h).trans
    (globalSectionsPushforwardIsoSite_hom_structureProjection B (Spec (.of A)) hA Y Z s)

/-- `subspaceSectionsEquiv` is the comparison of Stacks 0732 for the morphism of ringed topoi,
after the identification `c`. -/
theorem subspaceSectionsEquiv_hom_eq (Y : AlgebraicSpaces B (Spec (.of A)) hA)
    (Z : ClosedSubspaces B (Spec (.of A)) hA Y.1) {Q : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2}
    (c : Q ≅ pushforwardStructureSheaf B (Spec (.of A)) hA Y Z)
    (x : (sectionsOverBase A B hA Y.1 Y.2).obj Q) :
    (subspaceSectionsEquiv A Y Z c).hom x =
      globalSectionsPushforwardEquiv (smallEtaleRingedToposModulesHom B (Spec (.of A)) hA
          (subspaceInclusion B (Spec (.of A)) hA Y Z)) _
        (SheafOfModules.sectionsMap
          ((modulePushforwardIso B (Spec (.of A)) hA
            (subspaceInclusion B (Spec (.of A)) hA Y Z)).inv.app
            (SheafOfModules.unit (structureRingSheaf B (Spec (.of A)) hA ⟨Z.1.toFunctor, Z.2.1⟩)))
          (SheafOfModules.sectionsMap c.hom x)) :=
  (subspaceSectionsEquiv_apply A Y Z c x).trans rfl

/-- The `n`-th thickening, as an algebraic space. -/
abbrev thickeningSpace (n : ℕ) : AlgebraicSpaces B (Spec (.of A)) hA :=
  ⟨(thickening A X I n).1.toFunctor, (thickening A X I n).2.1⟩

/-- The inclusion of the `n`-th thickening. -/
abbrev baseThickeningInclusion (n : ℕ) : thickeningSpace A X I n ⟶ X :=
  subspaceInclusion B (Spec (.of A)) hA X (thickening A X I n)

/-- **Global sections of `𝒪_X / (I 𝒪_X)ⁿ⁺¹` are global sections of the structure sheaf of the
`n`-th thickening.** -/
noncomputable def thickeningSectionsEquiv (n : ℕ) :
    formalTower A X I (SheafOfModules.unit _) n ≃ₗ[A]
      (sectionsOverBase A B hA (thickeningSpace A X I n).1 (thickeningSpace A X I n).2).obj
        (SheafOfModules.unit _) :=
  (subspaceSectionsEquiv A X (thickening A X I n) (thickeningQuotientIso A X I n)).toLinearEquiv

/-- **The identification is compatible with the projections**: the image of a global function of
`X` in `Γ(X, 𝒪_X / (I 𝒪_X)ⁿ⁺¹)` corresponds to its restriction to the `n`-th thickening. -/
theorem thickeningSectionsEquiv_formalTowerProj (n : ℕ)
    (s : (sectionsOverBase A B hA X.1 X.2).obj (SheafOfModules.unit _)) :
    (thickeningSectionsEquiv A X I n (formalTowerProj A X I (SheafOfModules.unit _) n s)).1 =
      (globalSectionsRingHomSite B (Spec (.of A)) hA (baseThickeningInclusion A X I n)
        ⟨s.1, s.2⟩).1 :=
  subspaceSectionsEquiv_map_eq_globalSectionsRingHomSite A X (thickening A X I n)
    _ _ (π_comp_thickeningQuotientIso_hom A X I n) s

/-- The quotient map onto `𝒪_X / (I 𝒪_X)ⁿ⁺¹`, followed by the identification with the direct
image of the structure sheaf of the `n`-th thickening at the topos spelling, is the canonical
morphism. -/
theorem π_comp_thickeningQuotientIso_trans_hom (n : ℕ) :
    cokernel.π (C := Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (thickeningIdeal A X I n).ι ≫
        (thickeningQuotientIso A X I n ≪≫
          ((modulePushforwardIso B (Spec (.of A)) hA (baseThickeningInclusion A X I n)).app
            (toposUnit B (Spec (.of A)) hA (thickeningSpace A X I n))).symm).hom =
      pushforwardUnitSection (smallEtaleRingedToposModulesHom B (Spec (.of A)) hA
        (baseThickeningInclusion A X I n)) :=
  π_comp_cokernelIsoOfDefiningIdealSheafEq_hom_comp_inv A (thickening A X I n) _
    (definingIdealSheaf_thickening A X I n)

/-- The inclusion of the `n`-th thickening into the `(n + 1)`-st. -/
abbrev thickeningTransition (n : ℕ) : thickeningSpace A X I n ⟶ thickeningSpace A X I (n + 1) :=
  ObjectProperty.homMk (Subfunctor.homOfLe
    (show (thickening A X I n).1 ≤ (thickening A X I (n + 1)).1 from
      thickening_le A X I (Nat.le_succ n)))

/-- The inclusion of the `n`-th thickening into the `(n + 1)`-st, followed by the inclusion of the
`(n + 1)`-st thickening into `X`, is the inclusion of the `n`-th thickening. -/
theorem thickeningTransition_comp_inclusion (n : ℕ) :
    thickeningTransition A X I n ≫ baseThickeningInclusion A X I (n + 1) =
      baseThickeningInclusion A X I n :=
  ObjectProperty.hom_ext _ (Subfunctor.homOfLe_ι (thickening_le A X I (Nat.le_succ n)))

/-- **Transitions between direct images of structure sheaves are restriction of functions**, for
morphisms of algebraic spaces `j ≫ i' = i`, at the topos spelling of the direct images. -/
theorem globalSectionsPushforwardEquiv_transition_of_comp_eq {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S}
    {W W' Y : AlgebraicSpaces B S hS} (j : W ⟶ W') (i' : W' ⟶ Y) (i : W ⟶ Y) (h : j ≫ i' = i)
    {Q Q' : Modules.{u, u} B S hS Y.1 Y.2}
    (p' : SheafOfModules.unit _ ⟶ Q') (p : SheafOfModules.unit _ ⟶ Q)
    (q : Q' ⟶ Q) (hq : p' ≫ q = p)
    [hp' : Epi p']
    (c' : Q' ≅
      (pushforwardModules (smallEtaleRingedToposModulesHom B S hS i')).obj (toposUnit B S hS W'))
    (c : Q ≅
      (pushforwardModules (smallEtaleRingedToposModulesHom B S hS i)).obj (toposUnit B S hS W))
    (hc' : p' ≫ c'.hom = pushforwardUnitSection (smallEtaleRingedToposModulesHom B S hS i'))
    (hc : p ≫ c.hom = pushforwardUnitSection (smallEtaleRingedToposModulesHom B S hS i))
    (b : SheafOfModules.unit _ ⟶ Q') :
    (globalSectionsPushforwardEquiv (smallEtaleRingedToposModulesHom B S hS i) _
        (SheafOfModules.unitHomEquiv _ (b ≫ q ≫ c.hom))).1 =
      (globalSectionsRingHom (smallEtaleRingedToposModulesHom B S hS j)
        ⟨(globalSectionsPushforwardEquiv (smallEtaleRingedToposModulesHom B S hS i') _
            (SheafOfModules.unitHomEquiv _ (b ≫ c'.hom))).1,
          (globalSectionsPushforwardEquiv (smallEtaleRingedToposModulesHom B S hS i') _
            (SheafOfModules.unitHomEquiv _ (b ≫ c'.hom))).2⟩).1 := by
  subst h
  have hψ : Epi (pushforwardUnitSection (smallEtaleRingedToposModulesHom B S hS i')) :=
    hc' ▸ (@epi_comp _ _ _ _ _ p' ‹Epi p'› c'.hom (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom c')))
  have key := globalSectionsPushforwardEquiv_transition (hψ := hψ) (Q := Q) (Q' := Q')
    (smallEtaleRingedToposModulesHom B S hS j)
    (smallEtaleRingedToposModulesHom B S hS i') (smallEtaleRingedToposModulesHom B S hS (j ≫ i'))
    (pushforwardSetCompNatIso B S hS j i').hom (pushforwardModulesCompNatIso B S hS j i').hom
    (fun N =>
      Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_pushforwardModulesCompIso_hom_app
        (smallEtaleRingedToposModulesHom B S hS j) (smallEtaleRingedToposModulesHom B S hS i')
        (smallEtaleRingedToposModulesHom B S hS (j ≫ i')) (pushforwardSetCompNatIso B S hS j i')
        (fSharpSetComp_smallEtaleRingedToposModulesHom B S hS j i') N)
    p' p q hq c' c hc' hc b
  refine Eq.trans ?_ (key.trans ?_)
  · rfl
  · rfl

/-- A quotient map identified with the structure projection of a closed subspace is, at the topos
spelling of the direct image, the canonical morphism `1 ⟶ i_*1`. -/
theorem comp_trans_symm_hom_eq_pushforwardUnitSection {Y : AlgebraicSpaces B (Spec (.of A)) hA}
    (Z : ClosedSubspaces B (Spec (.of A)) hA Y.1) {Q : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2}
    (p : SheafOfModules.unit _ ⟶ Q) (c : Q ≅ pushforwardStructureSheaf B (Spec (.of A)) hA Y Z)
    (hc : p ≫ c.hom = structureProjection B (Spec (.of A)) hA Y Z) :
    p ≫ (c ≪≫ ((modulePushforwardIso B (Spec (.of A)) hA
      (subspaceInclusion B (Spec (.of A)) hA Y Z)).app
      (toposUnit B (Spec (.of A)) hA ⟨Z.1.toFunctor, Z.2.1⟩)).symm).hom =
      pushforwardUnitSection (smallEtaleRingedToposModulesHom B (Spec (.of A)) hA
        (subspaceInclusion B (Spec (.of A)) hA Y Z)) :=
  comp_comp_inv_app_eq_pushforwardUnitSection A Z _ _ hc

end Thickening

end AlgebraicGeometry.Space
