module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# Coherent adic systems on an affine scheme

Let `X` be an affine Noetherian scheme and `I ⊆ Γ(X, ⊤)` an ideal. This file proves Stacks 087W:
the category `Coh(X, I)` of coherent adic systems along `I` is equivalent to the category of
finite modules over the `I`-adic completion of `Γ(X, ⊤)`, and the equivalence is computed by the
inverse limit of global sections.

In one direction, a coherent adic system `(F_n)` has finite global sections at each level, the
transitions are surjective with kernel `I ^ (n+1)` times the sections, so by Stacks 09B8 the
inverse limit `lim Γ(F_n, ⊤)` is `I`-adically complete with surjective projections and kernels the
ideal-power multiples; its completion is therefore a finite module over the completed ring. That
assignment is fully faithful because global sections are fully faithful on quasi-coherent modules
and a morphism of limits is induced by a morphism of the towers.

In the other direction, a finite module `N` over the completion gives the tower
`n ↦ N / I ^ (n+1) N` of finite `Γ(X, ⊤)`-modules, and applying `affineTilde` termwise produces a
coherent adic system whose limit of global sections is `N` again.

## Main definitions

* `Stacks.Coherent.globalSectionsSystem` — the inverse system of global sections of a coherent
  adic system.
* `Stacks.Coherent.coherentAdicSystemsEquivFGModuleCat` — the equivalence of Stacks 087W.
* `Stacks.Coherent.completedModuleAsBase` — the corresponding completed module, as a module over
  the original ring.
* `Stacks.Coherent.globalSectionsComparison` — its identification with the inverse limit of
  global sections.

## Main results

* `Stacks.Coherent.globalSectionsComparison_naturality` — the comparison is natural.
* `Stacks.Coherent.globalSectionsComparison_projection_surjective` and
  `Stacks.Coherent.globalSectionsComparison_projection_ker` — the projection onto level `n` is
  surjective with kernel `I ^ (n+1)` times the completed module, so the induced map from the
  quotient is an isomorphism.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed: term `n` represents the Stacks source's
`F_{n+1}`. The ideal sheaf attached to `I` is `Scheme.IdealSheafData.ofIdealTop I`, whose ideal of
sections over an affine open `U` is the image of `I` under restriction; on `U = ⊤` that image is
`I` itself, which is the only place the affineness of `X` enters the kernel computation.

An affine scheme is used rather than a chosen presentation as a spectrum, so the quasi-inverse of
global sections is `affineTilde`, built in `AffineComparison` from restriction along
`X.isoSpec.hom`.

The auxiliary results are public, since the body of `coherentAdicSystemsEquivFGModuleCat` is
exposed and mentions them. No heartbeat limit is raised: the construction of the system attached
to a finite module fits inside the default budget as written, and fullness does once the identification of the functor's action
on a morphism is split off as `coherentSystemToFGModuleFunctor_map_hom_hom` and the remaining
rewrites are replaced by explicit `congrArg` steps, which avoids re-checking a rewrite motive
against the functor's unfolded body.

## References

* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

/-- A coherent adic system on an affine scheme, as an adic inverse system of quasi-coherent
modules. -/
public noncomputable def coherentSystemAdicData
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    (F : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)) :
    Stacks.Algebraization.AdicInverseSystem.{u} where
  X := X
  I := Scheme.IdealSheafData.ofIdealTop I
  system := F.obj
  isQuasicoherent := fun n => by
    have hloc : IsLocallyNoetherian X := isLocallyNoetherian_of_isNoetherianRing_top X
    have htfae := @Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X hloc (F.obj.obj n)
    exact ((htfae.out 1 2 (h₁ := rfl) (h₂ := rfl)).mp (F.property.1 n.unop)).1
  quotientIso := fun n => (F.property.2.2 n).choose
  quotientIso_hom_comp := fun n => (F.property.2.2 n).choose_spec

/-- The inverse system of global sections underlying a coherent adic system. -/
public abbrev globalSectionsSystem
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) :
    ℕᵒᵖ ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  F.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op ⊤)

/-- The transitions of a coherent adic system are surjective on global sections. -/
public theorem coherentSystem_globalSectionsTransition_surjective
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    (F : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)) (n : ℕ) :
    Function.Surjective
      (((globalSectionsSystem F).map (homOfLE (Nat.le_succ n)).op).hom) := by
  have hφ : Epi (F.obj.map (homOfLE (Nat.le_succ n)).op) := by
    rw [← (F.property.2.2 n).choose_spec]
    let g := (Stacks.Algebraization.idealPowerMultiple
      (Scheme.IdealSheafData.ofIdealTop I) (n + 1) (F.obj.obj (op (n + 1)))).ι
    exact epi_comp' (epi_of_isColimit_cofork (c := Cofork.ofπ (cokernel.π g)
      ((cokernel.condition g).trans zero_comp.symm)) (cokernelIsCokernel g))
      (IsIso.epi_of_iso (F.property.2.2 n).choose.hom)
  have hq1 : (F.obj.obj (op n)).IsQuasicoherent :=
    (coherentSystemAdicData X I F).isQuasicoherent (op n)
  have hq2 : (F.obj.obj (op (n + 1))).IsQuasicoherent :=
    (coherentSystemAdicData X I F).isQuasicoherent (op (n + 1))
  exact Stacks.Algebraization.surjective_app_of_epi_of_isAffineOpen
    (F.obj.map (homOfLE (Nat.le_succ n)).op) ⟨⊤, isAffineOpen_top X⟩

/-- Taking global sections of a coherent adic system, as a functor. -/
public noncomputable def globalSectionsFunctor
    (X : Scheme.{u}) (I : X.IdealSheafData) :
    CoherentAdicSystems I ⥤ (ℕᵒᵖ ⥤ ModuleCat.{u} Γ(X, ⊤)) where
  obj := globalSectionsSystem
  map f := Functor.whiskerRight f.hom
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
  map_id F := by
    apply Functor.whiskerRight_id'
  map_comp f g := Functor.whiskerRight_comp f.hom g.hom _

/-- On an affine Noetherian scheme, global sections are fully faithful on coherent adic
systems. -/
public noncomputable def globalSectionsFullyFaithful
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤)) :
    (globalSectionsFunctor X (Scheme.IdealSheafData.ofIdealTop I)).FullyFaithful := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  have hqc (F : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)) (n : ℕᵒᵖ) :
      (F.obj.obj n).IsQuasicoherent := (coherentSystemAdicData X I F).isQuasicoherent n
  refine {
    preimage := fun {F G} τ => ⟨{
      app := fun n => affineQuasicoherentHomLift (τ.app n)
      naturality := ?_ }⟩
    map_preimage := ?_
    preimage_map := ?_ }
  · intro i j a
    apply affineQuasicoherentHom_ext
    refine (Functor.map_comp E _ _).trans ?_
    refine Eq.trans ?_ (Functor.map_comp E _ _).symm
    refine (congrArg (fun k => E.map (F.obj.map a) ≫ k)
      (affineQuasicoherentHomLift_map (τ.app j))).trans ?_
    refine (τ.naturality a).trans ?_
    exact (congrArg (fun k => k ≫ E.map (G.obj.map a))
      (affineQuasicoherentHomLift_map (τ.app i))).symm
  · intro F G τ
    apply NatTrans.ext
    funext n
    exact affineQuasicoherentHomLift_map (τ.app n)
  · intro F G f
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext n
    apply affineQuasicoherentHom_ext
    exact affineQuasicoherentHomLift_map (E.map (f.hom.app n))

/-- A transition of an adic inverse system, as a map of modules of sections over an affine
open. -/
public def adicInverseSystemTransitionLinearMap
    (S : Stacks.Algebraization.AdicInverseSystem.{u}) (U : S.X.affineOpens) (n : ℕ) :
    Γ(S.system.obj (op (n + 1)), U.1) →ₗ[Γ(S.X, U.1)]
      Γ(S.system.obj (op n), U.1) where
  toAddHom := ((S.system.map (homOfLE (Nat.le_succ n)).op).app U.1).hom
  map_smul' r x := Scheme.Modules.Hom.app_smul (S.system.map (homOfLE (Nat.le_succ n)).op) r x

/-- The kernel of a transition of an adic inverse system on affine sections is the corresponding
ideal-power multiple. -/
public theorem adicInverseSystem_transition_ker
    (S : Stacks.Algebraization.AdicInverseSystem.{u}) (U : S.X.affineOpens) (n : ℕ) :
    LinearMap.ker
      (adicInverseSystemTransitionLinearMap S U n) =
      S.I.ideal U ^ (n + 1) •
        (⊤ : Submodule Γ(S.X, U.1)
          Γ(S.system.obj (op (n + 1)), U.1)) := by
  obtain ⟨e, he⟩ := Stacks.Algebraization.AdicInverseSystem.sectionsQuotientEquiv S U n
  have hcomp : e.toLinearMap.comp
      (Submodule.mkQ (S.I.ideal U ^ (n + 1) •
        (⊤ : Submodule Γ(S.X, U.1)
          Γ(S.system.obj (op (n + 1)), U.1)))) =
      adicInverseSystemTransitionLinearMap S U n := by
    ext x
    exact he x
  rw [← hcomp, LinearEquiv.ker_comp, Submodule.ker_mkQ]

/-- On the whole of an affine scheme the ideal of `Scheme.IdealSheafData.ofIdealTop I` is `I`. -/
public theorem ofIdealTop_ideal_top (X : Scheme.{u}) [IsAffine X] (I : Ideal Γ(X, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop I).ideal ⟨⊤, isAffineOpen_top X⟩ = I := by
  rw [Scheme.IdealSheafData.ofIdealTop_ideal]
  have hmap : (X.presheaf.map (homOfLE (le_top (a := (⊤ : X.Opens)))).op).hom =
      RingHom.id _ := by
    rw [show (homOfLE (le_top (a := (⊤ : X.Opens)))).op = 𝟙 (op (⊤ : X.Opens)) from
      Subsingleton.elim _ _]
    ext a
    exact congrArg (fun f => f a) (X.presheaf.map_id (op (⊤ : X.Opens)))
  rw [hmap, Ideal.map_id]

/-- The transitions of the system of global sections of a coherent adic system have kernel the
ideal-power multiple. -/
public theorem coherentSystem_globalSectionsTransition_ker
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    (F : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)) (k : ℕ) :
    LinearMap.ker (((globalSectionsSystem F).map (homOfLE (Nat.le_succ k)).op).hom) =
      I ^ (k + 1) • (⊤ : Submodule Γ(X, ⊤) ((globalSectionsSystem F).obj (op (k + 1)))) := by
  let S := coherentSystemAdicData X I F
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have h := adicInverseSystem_transition_ker S U k
  rwa [show S.I.ideal U = I from ofIdealTop_ideal_top X I] at h

/-- The completion of the inverse limit of global sections is a finite module over the completed
ring. -/
public theorem coherentSystem_completedGlobalSections_finite
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    (F : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)) :
    Module.Finite (AdicCompletion I Γ(X, ⊤))
      (AdicCompletion I (limit (globalSectionsSystem F) : ModuleCat Γ(X, ⊤))) := by
  let G := globalSectionsSystem F
  have hI : I.FG := I.fg_of_isNoetherianRing
  have hcoh : (F.obj.obj (op 0)).IsCoherent := F.property.1 0
  have hfin : Module.Finite Γ(X, ⊤) (G.obj (op 0)) :=
    coherentAdicTerm_finiteSections X (F.obj.obj (op 0))
  exact finite_adicCompletion_of_finite_reduction hI (limit G : ModuleCat Γ(X, ⊤))
    (moduleLimit_zeroQuotient_finite G
      (coherentSystem_globalSectionsTransition_surjective X I F)
      (coherentSystem_globalSectionsTransition_ker X I F) hI hfin)

/-- The inverse limit of global sections of a coherent adic system is `I`-adically complete. -/
public theorem coherentSystem_globalSectionsLimit_isAdicComplete
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    (F : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)) :
    IsAdicComplete I (limit (globalSectionsSystem F) : ModuleCat Γ(X, ⊤)) :=
  moduleLimit_isAdicComplete (globalSectionsSystem F)
    (coherentSystem_globalSectionsTransition_surjective X I F)
    (coherentSystem_globalSectionsTransition_ker X I F) I.fg_of_isNoetherianRing

/-- The kernel of the projection from the inverse limit of global sections onto level `n`. -/
public theorem coherentSystem_limitProjection_ker
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    (F : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)) :
    ∀ n, LinearMap.ker (limit.π (globalSectionsSystem F) (op n)).hom =
      I ^ (n + 1) •
        (⊤ : Submodule Γ(X, ⊤) (limit (globalSectionsSystem F) : ModuleCat Γ(X, ⊤))) :=
  moduleLimit_projection_ker (globalSectionsSystem F)
    (coherentSystem_globalSectionsTransition_surjective X I F)
    (coherentSystem_globalSectionsTransition_ker X I F) I.fg_of_isNoetherianRing

/-- The projection from the inverse limit of global sections onto level `n` is surjective. -/
public theorem coherentSystem_limitProjection_surjective
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    (F : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (n : ℕ) :
    Function.Surjective (limit.π (globalSectionsSystem F) (op n)).hom :=
  moduleLimit_projection_surjective (globalSectionsSystem F)
    (coherentSystem_globalSectionsTransition_surjective X I F) n

/-- The functor from coherent adic systems to finite modules over the completion: the completion
of the inverse limit of global sections. -/
public noncomputable def coherentSystemToFGModuleFunctor
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤)) :
    CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I) ⥤
      FGModuleCat.{u} (AdicCompletion I Γ(X, ⊤)) where
  obj F := by
    have : Module.Finite (AdicCompletion I Γ(X, ⊤))
        (AdicCompletion I (limit (globalSectionsSystem F) : ModuleCat Γ(X, ⊤))) :=
      coherentSystem_completedGlobalSections_finite X I F
    exact FGModuleCat.of (AdicCompletion I Γ(X, ⊤))
      (AdicCompletion I (limit (globalSectionsSystem F) : ModuleCat Γ(X, ⊤)))
  map {F G} f := by
    have : Module.Finite (AdicCompletion I Γ(X, ⊤))
        (AdicCompletion I (limit (globalSectionsSystem F) : ModuleCat Γ(X, ⊤))) :=
      coherentSystem_completedGlobalSections_finite X I F
    have : Module.Finite (AdicCompletion I Γ(X, ⊤))
        (AdicCompletion I (limit (globalSectionsSystem G) : ModuleCat Γ(X, ⊤))) :=
      coherentSystem_completedGlobalSections_finite X I G
    let τ := Functor.whiskerRight f.hom
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
    let l := limMap (F := globalSectionsSystem F) (G := globalSectionsSystem G) τ
    exact FGModuleCat.ofHom (AdicCompletion.map I l.hom)
  map_id F := by
    have : Module.Finite (AdicCompletion I Γ(X, ⊤))
        (AdicCompletion I (limit (globalSectionsSystem F) : ModuleCat Γ(X, ⊤))) :=
      coherentSystem_completedGlobalSections_finite X I F
    let L : ModuleCat Γ(X, ⊤) := limit (globalSectionsSystem F)
    let τ := Functor.whiskerRight (𝟙 F.obj)
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
    let l : L ⟶ L := limMap (F := globalSectionsSystem F)
      (G := globalSectionsSystem F) τ
    have hτ : τ = 𝟙 (globalSectionsSystem F) := by
      dsimp [τ, globalSectionsSystem]
      exact Functor.whiskerRight_id'
        (F := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)) (G := F.obj)
    have hlim : l = 𝟙 L := by
      change limMap τ = 𝟙 L
      rw [hτ]
      change (lim (J := ℕᵒᵖ) (C := ModuleCat (Γ(X, ⊤)))).map
        (𝟙 (globalSectionsSystem F)) = 𝟙 L
      exact CategoryTheory.Functor.map_id
        (lim (J := ℕᵒᵖ) (C := ModuleCat (Γ(X, ⊤)))) (globalSectionsSystem F)
    apply FGModuleCat.hom_ext
    change AdicCompletion.map I l.hom = LinearMap.id
    rw [hlim]
    change AdicCompletion.map I (LinearMap.id (M := L)) = LinearMap.id
    exact AdicCompletion.map_id I L
  map_comp := by
    intro F G H f g
    have : Module.Finite (AdicCompletion I Γ(X, ⊤))
        (AdicCompletion I (limit (globalSectionsSystem F) : ModuleCat Γ(X, ⊤))) :=
      coherentSystem_completedGlobalSections_finite X I F
    have : Module.Finite (AdicCompletion I Γ(X, ⊤))
        (AdicCompletion I (limit (globalSectionsSystem G) : ModuleCat Γ(X, ⊤))) :=
      coherentSystem_completedGlobalSections_finite X I G
    have : Module.Finite (AdicCompletion I Γ(X, ⊤))
        (AdicCompletion I (limit (globalSectionsSystem H) : ModuleCat Γ(X, ⊤))) :=
      coherentSystem_completedGlobalSections_finite X I H
    let LF : ModuleCat Γ(X, ⊤) := limit (globalSectionsSystem F)
    let LG : ModuleCat Γ(X, ⊤) := limit (globalSectionsSystem G)
    let LH : ModuleCat Γ(X, ⊤) := limit (globalSectionsSystem H)
    let τf := Functor.whiskerRight f.hom
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
    let τg := Functor.whiskerRight g.hom
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
    let τfg := Functor.whiskerRight (f ≫ g).hom
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
    let lf : LF ⟶ LG := limMap τf
    let lg : LG ⟶ LH := limMap τg
    let lfg : LF ⟶ LH := limMap τfg
    have hτ : τfg = τf ≫ τg := by
      change Functor.whiskerRight (f.hom ≫ g.hom)
        (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)) = _
      exact Functor.whiskerRight_comp f.hom g.hom
        (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
    have hlim : lfg = lf ≫ lg := by
      change limMap τfg = limMap τf ≫ limMap τg
      rw [hτ]
      change (lim (J := ℕᵒᵖ) (C := ModuleCat (Γ(X, ⊤)))).map (τf ≫ τg) =
        (lim (J := ℕᵒᵖ) (C := ModuleCat (Γ(X, ⊤)))).map τf ≫
          (lim (J := ℕᵒᵖ) (C := ModuleCat (Γ(X, ⊤)))).map τg
      exact CategoryTheory.Functor.map_comp
        (lim (J := ℕᵒᵖ) (C := ModuleCat (Γ(X, ⊤)))) τf τg
    apply FGModuleCat.hom_ext
    change AdicCompletion.map I lfg.hom =
      (AdicCompletion.map I lg.hom).comp (AdicCompletion.map I lf.hom)
    rw [hlim]
    change AdicCompletion.map I (lg.hom.comp lf.hom) = _
    exact (AdicCompletion.map_comp I lf.hom lg.hom).symm

/-- The comparison functor sends a morphism to the completion of the induced map of limits. -/
public theorem coherentSystemToFGModuleFunctor_map_hom_hom
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    {F G : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)} (f : F ⟶ G)
    (x : AdicCompletion I (limit (globalSectionsSystem F) : ModuleCat Γ(X, ⊤))) :
    ((coherentSystemToFGModuleFunctor X I).map f).hom.hom x =
      AdicCompletion.map I (limMap (F := globalSectionsSystem F) (G := globalSectionsSystem G)
        (Functor.whiskerRight f.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)))).hom x := rfl

/-- The comparison functor is faithful. -/
public theorem coherentSystemToFGModuleFunctor_faithful
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤)) : (coherentSystemToFGModuleFunctor X I).Faithful := by
  constructor
  intro F G f g h
  let LF := limit (globalSectionsSystem F)
  let LG := limit (globalSectionsSystem G)
  have hGcomplete : IsAdicComplete I LG :=
    coherentSystem_globalSectionsLimit_isAdicComplete X I G
  let E := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  have hl : limMap (F := globalSectionsSystem F) (G := globalSectionsSystem G)
        (Functor.whiskerRight f.hom E) =
      limMap (F := globalSectionsSystem F) (G := globalSectionsSystem G)
        (Functor.whiskerRight g.hom E) := by
    ext x
    apply (AdicCompletion.of_bijective I LG).1
    have hx := congrArg (fun k => k.hom.hom (AdicCompletion.of I LF x)) h
    simp only [coherentSystemToFGModuleFunctor_map_hom_hom] at hx
    exact hx
  apply (globalSectionsFullyFaithful X I).map_injective
  apply NatTrans.ext
  funext n
  have hepi : Epi (limit.π (globalSectionsSystem F) n) :=
    (ModuleCat.epi_iff_surjective _).mpr (coherentSystem_limitProjection_surjective X I F n.unop)
  apply (cancel_epi (limit.π (globalSectionsSystem F) n)).mp
  have hh := congrArg (fun k => k ≫ limit.π (globalSectionsSystem G) n) hl
  exact (limMap_π (F := globalSectionsSystem F) (G := globalSectionsSystem G)
      (Functor.whiskerRight f.hom E) n).symm.trans
    (hh.trans (limMap_π (F := globalSectionsSystem F) (G := globalSectionsSystem G)
      (Functor.whiskerRight g.hom E) n))

/-- The comparison functor is full. -/
public theorem coherentSystemToFGModuleFunctor_full
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤)) : (coherentSystemToFGModuleFunctor X I).Full := by
  constructor
  intro F G d
  let A := Γ(X, ⊤)
  let LF : ModuleCat A := limit (globalSectionsSystem F)
  let LG : ModuleCat A := limit (globalSectionsSystem G)
  have hFcomplete : IsAdicComplete I LF :=
    coherentSystem_globalSectionsLimit_isAdicComplete X I F
  have hGcomplete : IsAdicComplete I LG :=
    coherentSystem_globalSectionsLimit_isAdicComplete X I G
  let eF : LF ≃ₗ[A] AdicCompletion I LF := completeModuleEquivAdicCompletion I
  let eG : LG ≃ₗ[A] AdicCompletion I LG := completeModuleEquivAdicCompletion I
  let δ : AdicCompletion I LF →ₗ[AdicCompletion I A] AdicCompletion I LG := d.hom.hom
  let l : LF ⟶ LG := ModuleCat.ofHom
    (eG.symm.toLinearMap.comp ((δ.restrictScalars A).comp eF.toLinearMap))
  obtain ⟨τ, hτ⟩ := exists_natTrans_of_limitHom I
    (globalSectionsSystem F) (globalSectionsSystem G)
    (coherentSystem_limitProjection_surjective X I F)
    (coherentSystem_limitProjection_ker X I F)
    (coherentSystem_limitProjection_ker X I G) l
  let f : F ⟶ G := (globalSectionsFullyFaithful X I).preimage τ
  have hf : Functor.whiskerRight f.hom
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)) = τ :=
    (globalSectionsFullyFaithful X I).map_preimage τ
  refine ⟨f, ?_⟩
  apply FGModuleCat.hom_ext
  ext x
  obtain ⟨y, rfl⟩ := (AdicCompletion.of_bijective I LF).2 x
  rw [coherentSystemToFGModuleFunctor_map_hom_hom]
  have hcomp : (limMap (F := globalSectionsSystem F) (G := globalSectionsSystem G)
      (Functor.whiskerRight f.hom
        (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)))) = l :=
    (congrArg (fun σ => limMap (F := globalSectionsSystem F)
      (G := globalSectionsSystem G) σ) hf).trans hτ
  exact (congrArg (fun k : LF ⟶ LG =>
      AdicCompletion.map I k.hom (AdicCompletion.of I LF y)) hcomp).trans
    (eG.apply_symm_apply (δ (eF y)))

/-- A finite module over the completion gives a coherent adic system: apply `affineTilde` to the
tower of its reductions modulo the powers of `I`. -/
public noncomputable def completionModuleSheafSystem (X : Scheme.{u}) [IsAffine X]
    [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (N : FGModuleCat.{u} (AdicCompletion I Γ(X, ⊤))) :
    CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I) := by
  let A := Γ(X, ⊤)
  let M := (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj N.obj
  have : Module.Finite (AdicCompletion I A) M := N.property
  have : IsScalarTower A (AdicCompletion I A) M := ⟨fun a r x => by
    change (algebraMap A (AdicCompletion I A) a * r) • x =
      algebraMap A (AdicCompletion I A) a • (r • x)
    exact mul_smul _ _ _⟩
  let T := completionModuleReductionTower I N
  refine ⟨T ⋙ affineTilde X, ?_, ?_, ?_⟩
  · intro n
    have hfin : Module.Finite A (T.obj (op n)) :=
      completion_quotient_finite I I.fg_of_isNoetherianRing M (n + 1)
    exact affineTilde_coherent X (T.obj (op n))
  · intro n
    have hqc : ((affineTilde X).obj (T.obj (op n))).IsQuasicoherent :=
      affineTilde_quasicoherent X _
    change Stacks.Algebraization.idealPowerMultiple (Scheme.IdealSheafData.ofIdealTop I)
      (n + 1) ((affineTilde X).obj (T.obj (op n))) = ⊥
    apply affine_idealPowerMultiple_eq_bot
    apply affineTilde_power_annihilates
    let J : Submodule A M := I ^ (n + 1) • ⊤
    have hzero : I ^ (n + 1) • (⊤ : Submodule A (M ⧸ J)) = ⊥ := by
      rw [← map_smul_top_local (I ^ (n + 1)) J.mkQ J.mkQ_surjective]
      exact Submodule.mkQ_map_self J
    exact hzero
  · intro n
    obtain ⟨e, he⟩ := affineTildeQuotientIso X I (n + 1)
      (completionModuleReductionMap I N n)
      (completionModuleReductionMap_surjective I N n)
      (completionModuleReductionMap_ker I N n)
    refine ⟨e, ?_⟩
    have hmap : (T ⋙ affineTilde X).map (homOfLE (Nat.le_succ n)).op =
        (affineTilde X).map (completionModuleReductionMap I N n) := by
      simp only [Functor.comp_map, T, completionModuleReductionTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      rfl
    rwa [hmap]

/-- The global sections of `completionModuleSheafSystem` recover the reduction tower. -/
public noncomputable def completionModuleSheafSystemSectionsIso
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (N : FGModuleCat.{u} (AdicCompletion I Γ(X, ⊤))) :
    completionModuleReductionTower I N ≅
      globalSectionsSystem (completionModuleSheafSystem X I N) :=
  NatIso.ofComponents (fun n => affineTildeSectionsIso X
    ((completionModuleReductionTower I N).obj n)) (fun f =>
      (affineTildeAdjunction X).unit.naturality ((completionModuleReductionTower I N).map f))

/-- The comparison functor is essentially surjective. -/
public theorem coherentSystemToFGModuleFunctor_essSurj
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤)) : (coherentSystemToFGModuleFunctor X I).EssSurj := by
  constructor
  intro N
  let A := Γ(X, ⊤)
  let M := (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj N.obj
  let F := completionModuleSheafSystem X I N
  let e : (limit (globalSectionsSystem F) : ModuleCat A) ≃ₗ[A] M :=
    ((lim.mapIso (completionModuleSheafSystemSectionsIso X I N)).symm.toLinearEquiv).trans
      (completionModuleReductionLimitEquiv I N)
  have : Module.Finite (AdicCompletion I A) M := N.property
  have : IsScalarTower A (AdicCompletion I A) M := ⟨fun a r x => by
    show (algebraMap A (AdicCompletion I A) a * r) • x =
      algebraMap A (AdicCompletion I A) a • (r • x)
    exact mul_smul _ _ _⟩
  have hMcomplete : IsAdicComplete I M := finiteCompletionModule_isAdicComplete I
    I.fg_of_isNoetherianRing M
  let eM := (completeModuleEquivAdicCompletion (M := M) I).symm
  let c : AdicCompletion I (limit (globalSectionsSystem F) : ModuleCat A) ≃ₗ[A] M :=
    ((AdicCompletion.congr I e).restrictScalars A).trans eM
  let c' : AdicCompletion I (limit (globalSectionsSystem F) : ModuleCat A) ≃ₗ[AdicCompletion I A]
      M := {
    c.toAddEquiv with
    map_smul' := completion_linearMap_smul I I.fg_of_isNoetherianRing c.toLinearMap }
  exact ⟨F, ⟨ObjectProperty.isoMk _ c'.toModuleIso⟩⟩

/-- The comparison functor is an equivalence. -/
public theorem coherentSystemToFGModuleFunctor_isEquivalence
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤)) :
    (coherentSystemToFGModuleFunctor X I).IsEquivalence where
  faithful := coherentSystemToFGModuleFunctor_faithful X I
  full := coherentSystemToFGModuleFunctor_full X I
  essSurj := coherentSystemToFGModuleFunctor_essSurj X I

/-- **Stacks 087W.** Coherent inverse systems on an affine Noetherian scheme are equivalent to
finite modules over the completion of its ring of global sections. -/
@[stacks 087W]
public noncomputable def coherentAdicSystemsEquivFGModuleCat
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤)) :
    CoherentAdicSystems
      (Scheme.IdealSheafData.ofIdealTop I) ≌
        FGModuleCat.{u} (AdicCompletion I Γ(X, ⊤)) := by
  have : (coherentSystemToFGModuleFunctor X I).IsEquivalence :=
    coherentSystemToFGModuleFunctor_isEquivalence X I
  exact (coherentSystemToFGModuleFunctor X I).asEquivalence

/-- The completed module corresponding to a system, regarded as a module over the original
ring. -/
public abbrev completedModuleAsBase
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    (F : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)) :
    ModuleCat.{u} Γ(X, ⊤) :=
  (ModuleCat.restrictScalars (algebraMap Γ(X, ⊤)
    (AdicCompletion I Γ(X, ⊤)))).obj
      ((coherentAdicSystemsEquivFGModuleCat X I).functor.obj F).obj

/-- **Stacks 087W.** The canonical comparison with the inverse limit of global sections. -/
@[stacks 087W "inverse-limit object"]
public noncomputable def globalSectionsComparison
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    (F : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)) :
    completedModuleAsBase X I F ≅ limit (globalSectionsSystem F) := by
  let A := Γ(X, ⊤)
  let G := globalSectionsSystem F
  have : IsAdicComplete I (limit G : ModuleCat A) :=
    coherentSystem_globalSectionsLimit_isAdicComplete X I F
  let e : (limit G : ModuleCat A) ≃ₗ[A]
      AdicCompletion I (limit G : ModuleCat A) :=
    LinearEquiv.ofBijective (AdicCompletion.of I (limit G : ModuleCat A))
      (AdicCompletion.of_bijective I (limit G : ModuleCat A))
  exact e.toModuleIso.symm

/-- **Stacks 087W.** The comparison is natural in morphisms of coherent adic systems. -/
@[stacks 087W "naturality"]
public theorem globalSectionsComparison_naturality
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    {F G : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)}
    (f : F ⟶ G) :
    (ModuleCat.restrictScalars (algebraMap Γ(X, ⊤)
      (AdicCompletion I Γ(X, ⊤)))).map
        ((coherentAdicSystemsEquivFGModuleCat X I).functor.map f).hom ≫
      (globalSectionsComparison X I G).hom =
    (globalSectionsComparison X I F).hom ≫
      limMap (F := globalSectionsSystem F) (G := globalSectionsSystem G)
        (Functor.whiskerRight f.hom
        (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))) := by
  let A := Γ(X, ⊤)
  let LF : ModuleCat A := limit (globalSectionsSystem F)
  let LG : ModuleCat A := limit (globalSectionsSystem G)
  let τ := Functor.whiskerRight f.hom
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
  let l : LF ⟶ LG := limMap τ
  have hF : IsAdicComplete I LF := coherentSystem_globalSectionsLimit_isAdicComplete X I F
  have hG : IsAdicComplete I LG := coherentSystem_globalSectionsLimit_isAdicComplete X I G
  let eF : LF ≃ₗ[A] AdicCompletion I LF := completeModuleEquivAdicCompletion I
  let eG : LG ≃ₗ[A] AdicCompletion I LG := completeModuleEquivAdicCompletion I
  have hsecF (x : LF) : eF.symm (AdicCompletion.of I LF x) = x := eF.symm_apply_apply x
  have hsecG (x : LG) : eG.symm (AdicCompletion.of I LG x) = x := eG.symm_apply_apply x
  apply ModuleCat.hom_ext
  ext x
  obtain ⟨y, rfl⟩ := (AdicCompletion.of_bijective I LF).2 x
  show eG.symm (AdicCompletion.map I l.hom (AdicCompletion.of I LF y)) =
    l.hom (eF.symm (AdicCompletion.of I LF y))
  rw [AdicCompletion.map_of, hsecG, hsecF]

/-- **Stacks 087W.** Projection from the corresponding completed module onto any term is
surjective. -/
@[stacks 087W "surjective projections"]
public theorem globalSectionsComparison_projection_surjective
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    (F : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (n : ℕ) :
    Function.Surjective
      (((globalSectionsComparison X I F).hom ≫
        limit.π (globalSectionsSystem F) (op n)).hom) := by
  rw [ModuleCat.hom_comp, LinearMap.coe_comp]
  exact (coherentSystem_limitProjection_surjective X I F n).comp
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- **Stacks 087W.** The kernel of the projection is exactly the `(n+1)`-st ideal power multiple,
so the induced map from the quotient is an isomorphism. -/
@[stacks 087W "canonical quotient"]
public theorem globalSectionsComparison_projection_ker
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    (F : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (n : ℕ) :
    LinearMap.ker
      (((globalSectionsComparison X I F).hom ≫
        limit.π (globalSectionsSystem F) (op n)).hom) =
      I ^ (n + 1) • (⊤ : Submodule Γ(X, ⊤) (completedModuleAsBase X I F)) := by
  let A := Γ(X, ⊤)
  let G := globalSectionsSystem F
  let p := (limit.π G (op n)).hom
  let e : completedModuleAsBase X I F ≃ₗ[A] (limit G : ModuleCat A) :=
    (globalSectionsComparison X I F).toLinearEquiv
  have hcomp :
      ((globalSectionsComparison X I F).hom ≫ limit.π G (op n)).hom = p.comp e.toLinearMap :=
    rfl
  rw [hcomp]
  exact ker_comp_linearEquiv_pow_smul_top (I ^ (n + 1)) e p
    (coherentSystem_limitProjection_ker X I F n)

end Stacks.Coherent

end
