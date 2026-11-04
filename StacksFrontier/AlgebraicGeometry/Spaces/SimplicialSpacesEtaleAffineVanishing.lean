module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLowerShriek
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialBigFppfTotalAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleAffineVanishing

/-!
# Quasi-coherent modules on a simplicial algebraic space have no higher cohomology on affines

Let `U` be a simplicial algebraic space and `𝓖` a quasi-coherent `𝒪_U`-module on
`U_{spaces,étale}`. For an object `V/U_n` of `U_{spaces,étale}` with `V` represented by an
affine scheme, `Hᵖ(V/U_n, 𝓖) = 0` for `p > 0`.

The inclusion `d_n` of `(U_n)_{spaces,étale}` into `U_{spaces,étale}` is continuous and preserves
fibre products, so restriction along it is exact and carries injective modules to modules with
no higher cohomology over any object (Stacks 0D6X). Hence `Hᵖ(V/U_n, 𝓖) = Hᵖ(V, 𝓖_n)` (the
shape of Stacks 0DH2), and `𝓖_n` is a quasi-coherent module on `(U_n)_{spaces,étale}`, whose
higher cohomology on affine objects vanishes.

## Main results

In the namespace `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite`:

* `degreeInclusion_preservesPullbacks`: the inclusion of a degree preserves fibre products.
* `isZero_rightDerived_evaluation_of_isAffineScheme_spacesEtaleAffineVanishing`: the vanishing.

## References

* [Stacks Project, Tag 0DHF](https://stacks.math.columbia.edu/tag/0DHF)
* [Stacks Project, Tag 0DH2](https://stacks.math.columbia.edu/tag/0DH2)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

section Pullbacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : SimplicialObject (AlgebraicSpaces B S hS)) (n : SimplexCategory)

/-- A fibre product of `(X_n)_{spaces,étale}` is a fibre product of `X_{spaces,étale}`: a cone
over the cospan in `X_{spaces,étale}` has both legs over one simplex map, and its underlying
algebraic spaces factor through the fibre product of the underlying algebraic spaces. -/
def isLimitDegreeInclusionMapPullbackCone {A C V : SpacesEtale B S hS (X.obj (op n))}
    (f : A ⟶ V) (g : C ⟶ V) :
    IsLimit (PullbackCone.mk (f := (degreeInclusion X n).map f) (g := (degreeInclusion X n).map g)
      ((degreeInclusion X n).map (pullback.fst f g))
      ((degreeInclusion X n).map (pullback.snd f g))
      (by rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition])) := by
  have hP := (IsPullback.of_hasPullback f g).map (SpacesEtale.toSpaces B S hS (X.obj (op n)))
  refine PullbackCone.IsLimit.mk _ (fun s ↦ ?_) (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_)
  · have hb : s.snd.base = s.fst.base := by
      have h := congrArg Hom.base s.condition
      simp only [comp_base, degreeInclusion_map_base] at h
      exact (Category.id_comp _).symm.trans (h.symm.trans (Category.id_comp _))
    have e : s.fst.hom ≫ (SpacesEtale.toSpaces B S hS _).map f =
        s.snd.hom ≫ (SpacesEtale.toSpaces B S hS _).map g := congrArg Hom.hom s.condition
    refine ⟨s.fst.base, hP.lift s.fst.hom s.snd.hom e, ?_⟩
    have h₁ : hP.lift s.fst.hom s.snd.hom e ≫ (pullback.fst f g).hom.left = s.fst.hom :=
      hP.lift_fst _ _ _
    change hP.lift s.fst.hom s.snd.hom e ≫ (pullback f g).obj.hom = _
    rw [← Over.w (pullback.fst f g).hom, ← Category.assoc, h₁]
    exact s.fst.w
  · exact Hom.ext (Category.id_comp _) (hP.lift_fst _ _ _)
  · refine Hom.ext ?_ (hP.lift_snd _ _ _)
    have h := congrArg Hom.base s.condition
    simp only [comp_base, degreeInclusion_map_base] at h
    exact (Category.id_comp _).trans ((Category.id_comp _).symm.trans (h.symm.trans
      (Category.id_comp _))).symm
  · refine Hom.ext ?_ (hP.hom_ext ?_ ?_)
    · have h := congrArg Hom.base h₁
      simp only [comp_base, degreeInclusion_map_base] at h
      exact (Category.id_comp _).symm.trans h
    · exact (congrArg Hom.hom h₁).trans (hP.lift_fst _ _ _).symm
    · exact (congrArg Hom.hom h₂).trans (hP.lift_snd _ _ _).symm

/-- **The inclusion of a degree preserves fibre products.** -/
instance degreeInclusion_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (degreeInclusion X n) where
  preservesLimit {K} := by
    have : PreservesLimit (cospan (K.map WalkingCospan.Hom.inl) (K.map WalkingCospan.Hom.inr))
        (degreeInclusion X n) :=
      preservesLimit_of_preserves_limit_cone (pullbackIsPullback _ _)
        ((isLimitMapConePullbackConeEquiv _ _).symm
          (isLimitDegreeInclusionMapPullbackCone X n _ _))
    exact preservesLimit_of_iso_diagram _ (diagramIsoCospan K).symm

end Pullbacks

section Vanishing

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} (U : SimplicialObject T.Spaces)

/-- Sheaves of modules on `U_{spaces,étale}` form an abelian category. -/
noncomputable local instance abelian_ringSheafRingedSiteModules :
    Abelian (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (ringedSite U).O)) :=
  inferInstance

/-- Sheaves of modules on `U_{spaces,étale}` have enough injectives. -/
local instance enoughInjectives_ringSheafRingedSiteModules :
    EnoughInjectives (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (ringedSite U).O)) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

variable (n : SimplexCategory)

/-- Abelian sheaves on `(U_n)_{spaces,étale}` have `Ext` groups in the universe of its
morphisms. -/
local instance hasExt_degreeSheaf :
    HasExt.{u + 1} (Sheaf (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
      AddCommGrpCat.{u + 1}) :=
  Stacks.Cohomology.ModuleDirectImageOnACover.hasExt_morphismUniverse _

/-- Sheaves of modules over the restriction of `𝒪_U` to degree `n` form an abelian category. -/
noncomputable local instance abelian_degreeRestrictedModules :
    Abelian (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((ringedSite U).restrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
        (degreeInclusion U n)).O)) :=
  inferInstance

/-- Sheaves of modules over the restriction of `𝒪_U` to degree `n` have enough injectives. -/
local instance enoughInjectives_degreeRestrictedModules :
    EnoughInjectives (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((ringedSite U).restrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
        (degreeInclusion U n)).O)) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

/-- Sheaves of modules on `(U_n)_{spaces,étale}` have `Ext` groups in the universe of its
morphisms. -/
local instance hasExt_degreeModules :
    HasExt.{u + 1} (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((ringedSite U).restrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
        (degreeInclusion U n)).O)) :=
  Stacks.Cohomology.ModuleDirectImageOnACover.hasExt_morphismUniverse _

/-- Restriction of modules to degree `n` is additive. -/
local instance additive_degreeRestrictModules : (degreeRestrictModules (U := U) n).Additive where
  map_add := by intros; rfl

/-- Restriction of modules to degree `n` is left exact: it is a right adjoint. -/
local instance preservesFiniteLimits_degreeRestrictModules :
    PreservesFiniteLimits (degreeRestrictModules (U := U) n) :=
  haveI : (degreeRestrictModules (U := U) n).IsRightAdjoint :=
    Stacks.Sheaves.ToposPullback.isRightAdjoint_restrictionModules _ _ _ _
  inferInstance

/-- Restriction of modules to degree `n` is right exact: the inclusion of the degree is
cocontinuous, so restriction is a left adjoint. -/
local instance preservesFiniteColimits_degreeRestrictModules :
    PreservesFiniteColimits (degreeRestrictModules (U := U) n) :=
  haveI : (degreeRestrictModules (U := U) n).IsLeftAdjoint :=
    ((ringedSite U).restrictModulesAdjunctionRestrictionSquarePullbackMate
      (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
      (degreeInclusion U n)).isLeftAdjoint
  inferInstance

/-- **The restriction to degree `n` of an injective `𝒪_U`-module has no higher cohomology over
any object of `(U_n)_{spaces,étale}`** (Stacks 0D6X for the inclusion of the degree, which is
continuous and preserves fibre products). -/
theorem isZero_rightDerived_evaluation_degreeRestrictModules_of_injective
    (Z : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (ringedSite U).O)) [Injective Z]
    (V : SpacesEtale T.schemeSite S T.scheme_mem (U.obj (op n))) (p : ℕ) (hp : 0 < p) :
    IsZero (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
      ((ringedSite U).restrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
        (degreeInclusion U n)).O) (op V)).rightDerived p).obj
        ((degreeRestrictModules n).obj Z)) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  open Stacks.Cohomology.ModuleDirectImageOnACover in
  refine isZero_rightDerived_evaluation_of_isZero_H'_chgUniv.{u + 1, u + 1, u + 1} _ _ _ m _ ?_
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  have h := Stacks.CechSite.injective_module_subsingleton_ext_of_continuous.{u + 1, 0, u + 1,
    u + 1, u + 1, u + 1, u + 1} (ringedSite U)
    (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n))) (degreeInclusion U n) Z V
    (m + 1) (Nat.succ_pos m)
  exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source
    ((presheafToSheaf _ _).mapIso (Functor.isoWhiskerRight
      (uliftYonedaIsoYoneda.{u + 1, u + 1}.app V) AddCommGrpCat.free)) (m + 1) h

/-- **Higher cohomology of a quasi-coherent `𝒪_U`-module over `V/U_n`, with `V` represented by
an affine scheme, vanishes.** Restriction to degree `n` is exact and carries injectives to
modules acyclic for the sections over `V`, so `Hᵖ(V/U_n, 𝓖) = Hᵖ(V, 𝓖_n)` (the shape of
Stacks 0DH2), and `𝓖_n` is quasi-coherent on `(U_n)_{spaces,étale}`. -/
theorem isZero_rightDerived_evaluation_of_isAffineScheme_spacesEtaleAffineVanishing
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (ringedSite U).O))
    [G.IsQuasicoherentOnSite] (V : SpacesEtale T.schemeSite S T.scheme_mem (U.obj (op n)))
    (hV : SpacesEtale.IsAffineScheme T.schemeSite S T.scheme_mem (U.obj (op n)) V) (p : ℕ)
    (hp : 0 < p) :
    IsZero (((SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (ringedSite U).O)
        (op ((degreeInclusion U n).obj V))).rightDerived p).obj G) := by
  have hcomp := Stacks.RightDerivedComp.objIsoOfAcyclicImage (degreeRestrictModules n)
    (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
      ((ringedSite U).restrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
        (degreeInclusion U n)).O) (op V))
    (fun m hm ↦ Functor.isZero_rightDerived_of_exact _ G m hm)
    (fun Z hZ m hm ↦
      @isZero_rightDerived_evaluation_degreeRestrictModules_of_injective _ _ U n Z hZ V m hm) p
  have h₁ : IsZero (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
      ((ringedSite U).restrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
        (degreeInclusion U n)).O) (op V)).rightDerived p).obj ((degreeRestrictModules n).obj G)) :=
    @BigFppfSpaceSite.isZero_rightDerived_evaluation_of_isAffineScheme_spacesEtaleAffineVanishing
      _ T (U.obj (op n)) ((degreeRestrictModules n).obj G)
      (isQuasicoherentOnSite_degreeRestrictModules_obj n G) V hV p hp
  have h₂ := h₁.of_iso hcomp
  exact Functor.isZero_rightDerived_of_iso_comp_forget₂_spacesEtaleAffineVanishing
    (SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (ringedSite U).O)
        (op ((degreeInclusion U n).obj V)))
    (degreeRestrictModules n ⋙ SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
      ((ringedSite U).restrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
        (degreeInclusion U n)).O) (op V))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)) p G h₂

/-- The objects `V/U_n` of `U_{spaces,étale}` with `V` represented by an affine scheme. -/
def IsAffineScheme : ObjectProperty (SimplicialSpacesEtaleSite T.schemeSite S T.scheme_mem U) :=
  fun x ↦ SpacesEtale.IsAffineScheme T.schemeSite S T.scheme_mem (U.obj (op x.degree)) x.obj

/-- **Every object of `U_{spaces,étale}` has a covering family by objects represented by affine
schemes**, in its own degree. -/
theorem exists_preZeroHypercover_isAffineScheme_spacesEtaleAffineVanishing
    (x : SimplicialSpacesEtaleSite T.schemeSite S T.scheme_mem U) :
    ∃ 𝒰 : PreZeroHypercover.{u + 1} x, 𝒰.sieve₀ ∈ topology U x ∧
      ∀ i, IsAffineScheme U (𝒰.X i) := by
  obtain ⟨E, hE, hA⟩ :=
    BigFppfSpaceSite.exists_preZeroHypercover_isAffineScheme_spacesEtaleAffineVanishing T
      (U.obj (op x.degree)) x.obj
  have h := functorPushforward_degreeInclusion_mem hE
  rw [← PreZeroHypercover.sieve₀_map] at h
  exact ⟨E.map (degreeInclusion U x.degree), h, fun i ↦ hA i⟩

/-- **The Olsson--Laszlo vanishing on `U_{spaces,étale}`** (the condition of Stacks 0D6R checked in
the proof of Stacks 0DHF, with `B` the objects `V/U_n`, `V` affine, and `d = 0`):
`Hᵖ(V/U_n, 𝓖) = 0` for `p > 0` and `𝓖` quasi-coherent. -/
theorem isZero_moduleCohomology_of_isAffineScheme_spacesEtaleAffineVanishing
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (ringedSite U).O))
    (hG : G.IsQuasicoherentOnSite) (x : SimplicialSpacesEtaleSite T.schemeSite S T.scheme_mem U)
    (hx : IsAffineScheme U x) (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.Cohomology.moduleCohomology.{u + 1, u + 1, u + 1, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (ringedSite U).O) x p G) :=
  isZero_rightDerived_evaluation_of_isAffineScheme_spacesEtaleAffineVanishing U x.degree G x.obj
    hx p hp

end Vanishing

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
