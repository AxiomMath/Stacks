module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRingHomChartFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperReducedGlobalFunctionsFiniteOverSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global functions of an algebraic space proper over a Noetherian affine object of the site

Let `T` be an object of the big fppf site of `S` whose scheme is affine with Noetherian ring of
functions `R = Γ(T, 𝒪_T)`, and let `q : W ⟶ T` be a proper morphism of algebraic spaces.  Then
`Γ(W, 𝒪_W)` is a Noetherian, that is finite, `R`-module.  This is the degree-zero case of
Stacks 08AR for the structure sheaf of `W` over an affine base, proved without cohomology.

The proof is the coherent dévissage of Stacks 07US
(`AlgebraicGeometry.Space.property_of_ideal_pushforward_and_extensions`) on the Noetherian
algebraic space `W`, applied to the property of an `𝒪_W`-module that its global sections form a
Noetherian `R`-module:

* the property is closed under extensions because global sections are left exact and `R` is
  Noetherian;
* it holds for zero modules;
* for a reduced closed subspace `i : Z ⟶ W` and a quasi-coherent sheaf of ideals `I ⊆ 𝒪_Z`, the
  global sections of `i_* I` are those of `I` (Stacks 0732 in degree zero,
  `Stacks.Cohomology.SiteModules.globalSectionsPushforwardEquiv`), which embed into
  `Γ(Z, 𝒪_Z)`, a Noetherian `R`-module because `Z` is reduced and proper over `T`
  (`AlgebraicGeometry.Space.isNoetherian_globalFunctions_of_isProper_of_isReduced`).

The ring map along which global sections of `i_* I` and of `I` are compared is identified with
the pullback of global functions by
`AlgebraicGeometry.Space.globalSectionsRingHom_eq_globalFunctionsMap`, which is what makes the
comparison `R`-linear.

## Main definitions

* `AlgebraicGeometry.Space.sectionsModuleOfHom`: the global sections of an `𝒪_W`-module as an
  `R`-module, through pullback of functions along `q`.
* `AlgebraicGeometry.Space.HasNoetherianSectionsOverBase`: the property of an `𝒪_W`-module
  that its global sections form a Noetherian `R`-module.

## Main results

* `AlgebraicGeometry.Space.isNoetherian_of_isProper_of_isAffine`: `W` is a Noetherian algebraic
  space.
* `AlgebraicGeometry.Space.isNoetherian_globalFunctions_of_isProper`: `Γ(W, 𝒪_W)` is a
  Noetherian `R`-module.

## References

* [Stacks Project, Tag 07US](https://stacks.math.columbia.edu/tag/07US)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 04ZL](https://stacks.math.columbia.edu/tag/04ZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {W : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS} (q : W ⟶ schemeSpace T)

/-- The ring of global regular functions of `W`, read as the ring of global sections of its
structure sheaf of rings (the two are the same compatible families). -/
def globalFunctionsToSectionRing (W : AlgebraicSpaces B S hS) :
    globalFunctions B S hS W.1 →+* RingCat.sectionsSubring
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O).obj where
  toFun x := ⟨x.1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The global sections of an `𝒪_W`-module, as a module over the functions of `T` through
pullback of functions along `q : W ⟶ T`. -/
abbrev sectionsModuleOfHom (M : Modules.{u, u} B S hS W.1 W.2) :
    Module Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) M.sections :=
  letI := Stacks.Cohomology.SiteModules.sectionsModule
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O) M
  Module.compHom M.sections
    ((globalFunctionsToSectionRing B S hS W).comp (pullbackToGlobalFunctions B S hS W T q))

/-- A morphism of `𝒪_W`-modules induces an `R`-linear map on global sections. -/
def sectionsLinearMapOfHom {M N : Modules.{u, u} B S hS W.1 W.2} (φ : M ⟶ N) :
    letI := sectionsModuleOfHom B S hS q M
    letI := sectionsModuleOfHom B S hS q N
    M.sections →ₗ[Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] N.sections :=
  letI := sectionsModuleOfHom B S hS q M
  letI := sectionsModuleOfHom B S hS q N
  { toFun := SheafOfModules.sectionsMap φ
    map_add' := fun _ _ => Subtype.ext (funext fun X => (φ.val.app X).hom.map_add _ _)
    map_smul' := fun _ _ => Subtype.ext (funext fun X => (φ.val.app X).hom.map_smul _ _) }

/-- The linear map on global sections is evaluation of the morphism on every chart. -/
theorem sectionsLinearMapOfHom_apply {M N : Modules.{u, u} B S hS W.1 W.2} (φ : M ⟶ N)
    (s : M.sections) (X : (SmallEtale B S hS W.1)ᵒᵖ) :
    (sectionsLinearMapOfHom B S hS q φ s).val X = φ.val.app X (s.val X) := rfl

variable [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]

/-- The property of an `𝒪_W`-module that its global sections form a Noetherian module over the
functions of `T`. -/
def HasNoetherianSectionsOverBase (M : Modules.{u, u} B S hS W.1 W.2) : Prop :=
  @_root_.IsNoetherian Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) M.sections _ _
    (sectionsModuleOfHom B S hS q M)

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] in
/-- **Hypothesis (1) of Stacks 07US for the property**: global sections are left exact, so
the global sections of the middle term of a short exact sequence are an extension of a submodule
of those of the third term by those of the first. -/
theorem closedUnderCoherentExtensions_hasNoetherianSectionsOverBase :
    ClosedUnderCoherentExtensions B S hS W (HasNoetherianSectionsOverBase B S hS q) := by
  intro E hE _ _ _ h₁ h₃
  let := sectionsModuleOfHom B S hS q E.X₁
  let := sectionsModuleOfHom B S hS q E.X₂
  let := sectionsModuleOfHom B S hS q E.X₃
  have : _root_.IsNoetherian _ E.X₁.sections := h₁
  have : _root_.IsNoetherian _ E.X₃.sections := h₃
  let a := sectionsLinearMapOfHom B S hS q E.f
  let b := sectionsLinearMapOfHom B S hS q E.g
  have hker : LinearMap.ker b ≤ LinearMap.range a := by
    intro s hs
    have hs' : ∀ X, E.g.val.app X (s.val X) = 0 := fun X =>
      congrArg (fun t : E.X₃.sections => t.val X) (LinearMap.mem_ker.mp hs)
    have hex : ∀ X, ∃ x : E.X₁.val.obj X, E.f.val.app X x = s.val X := fun X =>
      SheafOfModules.exists_of_shortExact_sections hE X (s.val X) (hs' X)
    choose t ht using hex
    refine ⟨⟨t, fun {X Y} g => ?_⟩, Subtype.ext (funext fun X => ht X)⟩
    apply SheafOfModules.injective_of_mono_sections E.f hE.mono_f Y
    change E.f.val.app Y (E.X₁.val.map g (t X)) = E.f.val.app Y (t Y)
    rw [ht Y]
    refine (PresheafOfModules.naturality_apply E.f.val g (t X)).trans ?_
    rw [ht X]
    exact s.property g
  refine isNoetherian_of_range_eq_ker a b (le_antisymm ?_ hker)
  rintro _ ⟨s, rfl⟩
  refine LinearMap.mem_ker.mpr (Subtype.ext (funext fun X => ?_))
  change (E.f ≫ E.g).val.app X (s.val X) = 0
  rw [E.zero]
  rfl

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] in
/-- The property is invariant under isomorphism. -/
theorem hasNoetherianSectionsOverBase_of_iso {M N : Modules.{u, u} B S hS W.1 W.2} (e : M ≅ N)
    (h : HasNoetherianSectionsOverBase B S hS q M) : HasNoetherianSectionsOverBase B S hS q N := by
  let := sectionsModuleOfHom B S hS q M
  let := sectionsModuleOfHom B S hS q N
  have : _root_.IsNoetherian _ M.sections := h
  let l : M.sections ≃ₗ[Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] N.sections :=
    { sectionsLinearMapOfHom B S hS q e.hom with
      invFun := sectionsLinearMapOfHom B S hS q e.inv
      left_inv := fun s => Subtype.ext (funext fun X => by
        change (e.hom ≫ e.inv).val.app X (s.val X) = s.val X
        rw [e.hom_inv_id]
        rfl)
      right_inv := fun s => Subtype.ext (funext fun X => by
        change (e.inv ≫ e.hom).val.app X (s.val X) = s.val X
        rw [e.inv_hom_id]
        rfl) }
  exact isNoetherian_of_linearEquiv l

/-- Global sections of the unit module are the global functions, linearly over the functions
of `T`. -/
private def unitSectionsLinearEquiv :
    letI := sectionsModuleOfHom B S hS q
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS W.1 W.2).O))
    letI := globalFunctionsModuleOfHom B S hS W T q
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS W.1 W.2).O)).sections ≃ₗ[
          Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]
        globalFunctions B S hS W.1 :=
  letI := sectionsModuleOfHom B S hS q
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS W.1 W.2).O))
  letI := globalFunctionsModuleOfHom B S hS W T q
  { toFun := fun s => ⟨s.1, s.2⟩
    invFun := fun s => ⟨s.1, s.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- **The structure sheaf of a reduced algebraic space proper over `T` has the property.**  Its
global sections are the global regular functions, to which
`AlgebraicGeometry.Space.isNoetherian_globalFunctions_of_isProper_of_isReduced` applies. -/
theorem hasNoetherianSectionsOverBase_unit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (hq : IsProper B S hS q.hom)
    (hred : HasEtaleLocalProperty B S hS W.obj
      (fun X : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced X)) :
    HasNoetherianSectionsOverBase B S hS q
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS W.1 W.2).O)) := by
  let := sectionsModuleOfHom B S hS q
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS W.1 W.2).O))
  let := globalFunctionsModuleOfHom B S hS W T q
  have := isNoetherian_globalFunctions_of_isProper_of_isReduced B S hS W T q hq hred
  exact isNoetherian_of_linearEquiv (unitSectionsLinearEquiv B S hS q).symm

/-- The comparison of global sections of Stacks 0732 along a morphism `i` of algebraic spaces
carries the action of a global function `a` to the action of its pullback along `i`. -/
theorem globalSectionsPushforwardEquiv_smul_globalFunctions {Z : AlgebraicSpaces B S hS}
    (i : Z ⟶ W) (N : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Z).O))
    (a : globalFunctions B S hS W.1)
    (s : ((Stacks.Sheaves.RingedToposModules.pushforwardModules
        (smallEtaleRingedToposModulesHom B S hS i)).obj N).sections) :
    letI := Stacks.Cohomology.SiteModules.sectionsModule
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Z).O) N
    letI := Stacks.Cohomology.SiteModules.sectionsModule
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS W).O)
      ((Stacks.Sheaves.RingedToposModules.pushforwardModules
        (smallEtaleRingedToposModulesHom B S hS i)).obj N)
    Stacks.Cohomology.SiteModules.globalSectionsPushforwardEquiv
      (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS W)
      (smallEtaleRingedToposModulesHom B S hS i) N ((⟨a.1, a.2⟩ : RingCat.sectionsSubring
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS W).O).obj) • s) =
      (⟨(globalFunctionsMap B S hS i a).1, (globalFunctionsMap B S hS i a).2⟩ :
        RingCat.sectionsSubring
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Z).O).obj) •
        Stacks.Cohomology.SiteModules.globalSectionsPushforwardEquiv
          (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS W)
          (smallEtaleRingedToposModulesHom B S hS i) N s := by
  refine (Stacks.Cohomology.SiteModules.globalSectionsPushforwardEquiv_smul _ N _ s).trans ?_
  congr 1
  exact Subtype.ext (globalSectionsRingHom_eq_globalFunctionsMap B S hS i a)

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] in
/-- **The property passes to direct images**: global sections of `i_* N` are those of `N`, and
the comparison is linear over the functions of `T`. -/
theorem hasNoetherianSectionsOverBase_pushforwardModules {Z : AlgebraicSpaces B S hS} (i : Z ⟶ W)
    (N : Modules.{u, u} B S hS Z.1 Z.2) (h : HasNoetherianSectionsOverBase B S hS (i ≫ q) N) :
    HasNoetherianSectionsOverBase B S hS q
      ((Stacks.Sheaves.RingedToposModules.pushforwardModules
        (smallEtaleRingedToposModulesHom B S hS i)).obj N) := by
  let P : Modules.{u, u} B S hS W.1 W.2 := (Stacks.Sheaves.RingedToposModules.pushforwardModules
        (smallEtaleRingedToposModulesHom B S hS i)).obj N
  change HasNoetherianSectionsOverBase B S hS q P
  let := sectionsModuleOfHom B S hS (i ≫ q) N
  let := sectionsModuleOfHom B S hS q P
  have : _root_.IsNoetherian _ N.sections := h
  let e := Stacks.Cohomology.SiteModules.globalSectionsPushforwardEquiv
    (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS W)
    (smallEtaleRingedToposModulesHom B S hS i) N
  let l : P.sections ≃ₗ[Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] N.sections :=
    { e with
      map_add' := Stacks.Cohomology.SiteModules.globalSectionsPushforwardEquiv_add
        (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS W)
        (smallEtaleRingedToposModulesHom B S hS i) N
      map_smul' := fun r s => by
        refine (globalSectionsPushforwardEquiv_smul_globalFunctions B S hS i N
          (pullbackToGlobalFunctions B S hS W T q r) s).trans ?_
        rw [← RingHom.comp_apply, ← pullbackToGlobalFunctions_comp_left]
        rfl }
  exact isNoetherian_of_linearEquiv l.symm

/-- **Hypothesis (2) of Stacks 07US for the property**: for a reduced closed subspace
`i : Z ⟶ W` and a quasi-coherent sheaf of ideals `I ⊆ 𝒪_Z`, the global sections of `i_* I` form
a Noetherian module over the functions of `T`. -/
theorem hasNoetherianSectionsOverBase_idealPushforward
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (hq : IsProper B S hS q.hom) (Z : Subfunctor W.1) (closed : IsClosedSubspace B S hS Z)
    (hZ : IsReducedIrreducible B S hS Z)
    (I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS closed)) :
    HasNoetherianSectionsOverBase B S hS q
      ((modulePushforward B S hS (closedSubfunctorι B S hS closed)).obj I.1.toSheafOfModules) := by
  let i := closedSubfunctorι B S hS closed
  have hi : IsProper B S hS (i ≫ q).hom :=
    isProper_comp B S hS closed.1 W.2 (schemeSpace T).2 i.hom q.hom
      (isProper_of_isClosedImmersion B S hS closed.1 W.2 i.hom closed.2) hq
  let U : Modules.{u, u} B S hS (closedSubfunctorSpace B S hS closed).1
      (closedSubfunctorSpace B S hS closed).2 := SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (closedSubfunctorSpace B S hS closed).1
        (closedSubfunctorSpace B S hS closed).2).O)
  let N : Modules.{u, u} B S hS (closedSubfunctorSpace B S hS closed).1
      (closedSubfunctorSpace B S hS closed).2 := I.1.toSheafOfModules
  let ι : N ⟶ U := I.1.ι
  have hN : HasNoetherianSectionsOverBase B S hS (i ≫ q) N := by
    let := sectionsModuleOfHom B S hS (i ≫ q) N
    let := sectionsModuleOfHom B S hS (i ≫ q) U
    have := hasNoetherianSectionsOverBase_unit B S hS (i ≫ q) hi hZ.1
    change _root_.IsNoetherian _ U.sections at this
    exact isNoetherian_of_injective (sectionsLinearMapOfHom B S hS (i ≫ q) ι)
      fun s t hst => Subtype.ext (funext fun X => Subtype.ext
        (congrArg (fun z : U.sections => z.val X) hst))
  exact hasNoetherianSectionsOverBase_of_iso B S hS q ((modulePushforwardIso B S hS i).app _)
    (hasNoetherianSectionsOverBase_pushforwardModules B S hS q i _ hN)

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] in
/-- A zero module has the property. -/
theorem hasNoetherianSectionsOverBase_of_isZero (M : Modules.{u, u} B S hS W.1 W.2)
    (hM : IsZero M) :
    HasNoetherianSectionsOverBase B S hS q M := by
  let := sectionsModuleOfHom B S hS q M
  have : Subsingleton M.sections := ⟨fun s t => Subtype.ext (funext fun X => by
    have hs : s.val X = (𝟙 M : M ⟶ M).val.app X (s.val X) := rfl
    have ht : t.val X = (𝟙 M : M ⟶ M).val.app X (t.val X) := rfl
    rw [hs, ht, hM.eq_of_src (𝟙 M) 0]
    rfl)⟩
  change _root_.IsNoetherian _ M.sections
  infer_instance

/-- A Noetherian affine scheme of the site is a Noetherian algebraic space. -/
theorem isNoetherian_yoneda_of_isAffine (hZ : B.Contains (⊤_ Scheme.{u}))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] :
    IsNoetherian B S hS hZ (yoneda.obj T) :=
  ⟨isQuasiCompactSpace_yoneda_of_isAffine B S hS T inferInstance,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (yoneda.obj T) hZ
      ⟨T, inferInstance, ⟨Functor.RepresentableBy.yoneda T⟩⟩,
    (exists_atlas_iff_of_representable B S hS (yoneda.obj T)
      (fun X : Scheme.{u} => IsLocallyNoetherian X) T (Iso.refl _)).2
      (isLocallyNoetherian_of_affine_cover
        (S := fun _ : Unit ↦ ⟨⊤, isAffineOpen_top ((BigFppfOver.toScheme B S hS).obj T)⟩)
        (by simp) fun _ ↦ inferInstance)⟩

/-- An algebraic space proper over a Noetherian affine scheme of the site is Noetherian. -/
theorem isNoetherian_of_isProper_of_isAffine (hZ : B.Contains (⊤_ Scheme.{u}))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (hq : IsProper B S hS q.hom) :
    IsNoetherian B S hS hZ W.1 := by
  have hT := isNoetherian_yoneda_of_isAffine B S hS (T := T) hZ
  exact isNoetherian_of_isFinitePresentation B S hS hZ q.hom W.2 (schemeSpace T).2
    (isFinitePresentation_of_isFiniteType B S hS W.2 (schemeSpace T).2 q.hom hT.2.2 hq.2.1
      (isQuasiSeparated_of_isSeparated B S hS hq.1)) hT

/-- **The global functions of an algebraic space proper over a Noetherian affine object of the
site form a Noetherian module.**  Let `T` be an object of the big fppf site of `S` whose scheme
is affine with Noetherian ring `R` of functions and let `q : W ⟶ T` be proper.  Then
`Γ(W, 𝒪_W)` is a Noetherian (equivalently, finite) `R`-module: this is Stacks 07US for the
property `AlgebraicGeometry.Space.HasNoetherianSectionsOverBase`, applied to the structure
sheaf, which is coherent on the Noetherian algebraic space `W`. -/
@[ega "II 7.3.12" "more general"]
theorem isNoetherian_globalFunctions_of_isProper [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (hq : IsProper B S hS q.hom) :
    @_root_.IsNoetherian (↑Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u)
      (globalFunctions B S hS W.obj) _ _ (globalFunctionsModuleOfHom B S hS W T q) := by
  have hW := isNoetherian_of_isProper_of_isAffine B S hS q B.contains_terminal hq
  have : Fact (HasEtaleLocalProperty B S hS W.1
    (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) := ⟨hW.2.2⟩
  have h := property_of_ideal_pushforward_and_extensions B S hS W hW
    (HasNoetherianSectionsOverBase B S hS q)
    (Or.inr (hasNoetherianSectionsOverBase_of_isZero B S hS q))
    (closedUnderCoherentExtensions_hasNoetherianSectionsOverBase B S hS q)
    (hasNoetherianSectionsOverBase_idealPushforward B S hS q hq)
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS W.1 W.2).O)) inferInstance
  let := sectionsModuleOfHom B S hS q
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS W.1 W.2).O))
  let := globalFunctionsModuleOfHom B S hS W T q
  change _root_.IsNoetherian _ _ at h
  exact isNoetherian_of_linearEquiv (unitSectionsLinearEquiv B S hS q)

end AlgebraicGeometry.Space

end
