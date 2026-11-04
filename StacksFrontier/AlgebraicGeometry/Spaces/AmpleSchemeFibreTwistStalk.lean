module

public import StacksFrontier.AlgebraicGeometry.Spaces.StalkPointFibreSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiTwistReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesTensorQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyFiniteOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCoverTwistVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleProjOpenImmersion

/-!
# The stalk vanishing of Stacks 0D39 from the vanishing over the local ring

The first conclusion of Stacks 0D39, `(Rᵖf_*(ℱ ⊗ ℒ^{⊗ d}))_y = 0` for `p > 0`, read from the
vanishing of `Hᵖ(X', ℱ' ⊗ ℒ'^{⊗ d})` on the base change `X' = X ×_Y Spec 𝒪_{Y,y}`, where `ℱ'`
and `ℒ'` are the pullbacks.  This is the reduction "hence we may assume that `Y = Spec(A)` is the
spectrum of a Noetherian local ring" of the proof, in the direction it is used.

## Main results

* `AlgebraicGeometry.Space.modulePullbackTensorPowIso`: `q^*(ℱ ⊗ ℒ^{⊗ d}) ≅ q^*ℱ ⊗ (q^*ℒ)^{⊗ d}`,
  in the iterated-twist spelling.
* `AlgebraicGeometry.Space.isZero_stalk_rightDerived_tensorPow_of_isZero`: the reduction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Inverse image of a twist.** `q^*(ℱ ⊗ ℒ^{⊗ d}) ≅ (q^*ℱ) ⊗ (q^*ℒ)^{⊗ d}`, the right side in
the spelling of the iterated twist. -/
def modulePullbackTensorPowIso {X X' : AlgebraicSpaces B S hS} (q : X' ⟶ X)
    (F L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L] (d : ℕ) :
    (modulePullback B S hS q).obj (F ⊗ tensorPow B S hS L d) ≅
      (twistPowFunctor ((modulePullback B S hS q).obj L) d).obj ((modulePullback B S hS q).obj F) :=
  (modulePullback B S hS q).mapIso (twistPowFunctorObjIso L F d).symm ≪≫
    modulePullbackTwistPowIso q L F d

/-- **The twists of a quasi-coherent module by an invertible module are quasi-coherent.** -/
theorem isQuasicoherentOnSite_tensor_tensorPow {X : AlgebraicSpaces B S hS}
    (F L : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L] (d : ℕ) :
    (F ⊗ tensorPow B S hS L d).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (twistPowFunctorObjIso L F d)
    (isQuasicoherentOnSite_twistPowFunctor_obj F L hF
      (isQuasicoherentOnSite_of_isInvertible B S hS X L
        (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L ‹_›)) d)

/-- **The stalk vanishing of Stacks 0D39 from the vanishing over the local ring.**  If
`Hⁱ(X', q^*ℱ ⊗ (q^*ℒ)^{⊗ d}) = 0` on the base change `X' = X ×_Y Spec 𝒪_{Y,y}`, then the stalk
at `y` of `Rⁱf_*(ℱ ⊗ ℒ^{⊗ d})` vanishes. -/
theorem isZero_stalk_rightDerived_tensorPow_of_isZero (Y : BigFppfOver B S hS)
    [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
    (y : (BigFppfOver.toScheme B S hS).obj Y) {X : AlgebraicSpaces B S hS}
    (f : X ⟶ representedAlgebraicSpace B S hS Y) (hf : IsProper B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L]
    {X' : AlgebraicSpaces B S hS} (q' : X' ⟶ X)
    (f' : X' ⟶ representedAlgebraicSpace B S hS (stalkPointObject Y y))
    (sq : IsPullback q' f' f (representedSpaceMap B S hS (stalkPointHom Y y))) (d i : ℕ)
    (hvan : have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)).rightDerived i).obj
          ((twistPowFunctor ((modulePullback B S hS q').obj L) d).obj
            ((modulePullback B S hS q').obj F)))) :
    letI := modulePushforward_additive B S hS f
    IsZero ((zariskiModule Y (((modulePushforward B S hS f).rightDerived i).obj
      (F ⊗ tensorPow B S hS L d))).presheaf.stalk y) := by
  have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
  exact isZero_zariskiModule_stalk_of_isZero_cohomology Y y f hf.2.1.2
    (isQuasiSeparated_of_isSeparated B S hS hf.1) _
    (isQuasicoherentOnSite_tensor_tensorPow F L hF d)
    q' f' sq i (hvan.of_iso (((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)).rightDerived i).mapIso
        (modulePullbackTensorPowIso q' F L d)))

/-! ### The local situation over `Spec 𝒪_{Y,y}` -/

section Local

variable {Y : BigFppfOver B S hS}
  [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
  {y : (BigFppfOver.toScheme B S hS).obj Y} {X : AlgebraicSpaces B S hS}
  {f : X ⟶ representedAlgebraicSpace B S hS Y} (hf : IsProper B S hS f.hom)
  {X' : AlgebraicSpaces B S hS} {q' : X' ⟶ X}
  {f' : X' ⟶ representedAlgebraicSpace B S hS (stalkPointObject Y y)}
  (sq : IsPullback q' f' f (representedSpaceMap B S hS (stalkPointHom Y y)))

include hf sq in
/-- The base change to `Spec 𝒪_{Y,y}` of a proper morphism is proper. -/
theorem isProper_stalkBaseChange : IsProper B S hS f'.hom :=
  (isProper_isStableUnderBaseChange B S hS).of_isPullback sq hf

/-- The spectrum `Spec 𝒪_{Y,y}` of a local ring of a Noetherian scheme is locally
Noetherian. -/
instance isLocallyNoetherian_stalkPointObject :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (stalkPointObject Y y)) :=
  inferInstanceAs (IsLocallyNoetherian
    (Spec (.of (((BigFppfOver.toScheme B S hS).obj Y).presheaf.stalk y))))

include hf sq in
/-- The base change to `Spec 𝒪_{Y,y}` is locally Noetherian. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_stalkBaseChange :
    HasEtaleLocalProperty B S hS X'.1 (fun V : Scheme.{u} => IsLocallyNoetherian V) :=
  (isNoetherian_of_isProper_schemeSpace B S hS B.contains_terminal inferInstance inferInstance
    f' (isProper_stalkBaseChange hf sq)).2.2

variable {U : BigFppfOver B S hS} {p : yoneda.obj U ⟶ X.1} {q : U ⟶ residuePointObject Y y}
  (hsq : IsPullback p (yoneda.map q) f.hom (yoneda.map (residuePointHom Y y)))

include hf sq hsq in
/-- The fibre `U ⟶ Spec κ(y)` is proper. -/
theorem isProper_fibreMap :
    _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map q) := by
  have hsqA := isPullback_homMk B S hS X'.2 (isAlgebraicSpace_yoneda B S hS _)
    (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
    (isPullback_fibreToStalkBaseChange hsq sq)
  exact isProper_toScheme_map_of_isProper B S hS q
    ((isProper_isStableUnderBaseChange B S hS).of_isPullback hsqA (isProper_stalkBaseChange hf sq))

include hf sq in
/-- The pullback of a coherent module to the base change over `Spec 𝒪_{Y,y}` is coherent. -/
theorem isCoherent_stalkBaseChange (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : IsCoherent B S hS X.1 X.2 F) :
    IsCoherent B S hS X'.1 X'.2 ((modulePullback B S hS q').obj F) :=
  have : Fact (HasEtaleLocalProperty B S hS X'.1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_stalkBaseChange hf sq⟩
  isCoherent_modulePullback B S hS q' F hF

/-- The inverse image of an invertible module is invertible. -/
theorem isInvertible_modulePullback_stacks {X₁ X₂ : AlgebraicSpaces B S hS} (g : X₁ ⟶ X₂)
    (L : Modules.{u, u} B S hS X₂.1 X₂.2)
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X₂.1 X₂.2).obj
      (structureRingPresheaf_isSheaf B S hS X₂.1 X₂.2) L] :
    Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X₁.1 X₁.2).obj
      (structureRingPresheaf_isSheaf B S hS X₁.1 X₁.2) ((modulePullback B S hS g).obj L) :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (isInvertible_modulePullback_obj B S hS g L
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L ‹_›))

include hsq in
/-- The restriction to the fibre of the pullback to `X'` is the restriction to the fibre. -/
def baseChangeModuleStalkIso (L : Modules.{u, u} B S hS X.1 X.2) :
    baseChangeModule B S hS ((modulePullback B S hS q').obj L) U (fibreToStalkBaseChange hsq sq) ≅
      baseChangeModule B S hS L U p :=
  have hcomp : (ObjectProperty.homMk (fibreToStalkBaseChange hsq sq) :
      representedAlgebraicSpace B S hS U ⟶ X') ≫ q' = ObjectProperty.homMk p :=
    ObjectProperty.hom_ext _ (fibreToStalkBaseChange_comp hsq sq)
  (zariskiFunctor U).mapIso ((modulePullbackCompIso B S hS _ q').app L ≪≫
    eqToIso (congrArg (fun g => (modulePullback B S hS g).obj L) hcomp))

end Local

/-- The kernel of `Γ(T, 𝒪_T) ⟶ Γ(P, 𝒪_P)` along a morphism `ι : P ⟶ T` to an affine locally
Noetherian object is finitely generated: it has a finite family of generators. -/
theorem exists_fin_span_eq_ker {P T : BigFppfOver B S hS} (ι : P ⟶ T)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)] :
    ∃ (r : ℕ) (x : Fin r → Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)),
      Ideal.span (Set.range x) = RingHom.ker ((BigFppfOver.toScheme B S hS).map ι).appTop.hom := by
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  exact Submodule.fg_iff_exists_fin_generating_family.1
    (IsNoetherian.noetherian (RingHom.ker ((BigFppfOver.toScheme B S hS).map ι).appTop.hom))

/-- The ring of global functions of `Spec κ(y)` is Noetherian. -/
instance isNoetherianRing_residuePointObject (Y : BigFppfOver B S hS)
    (y : (BigFppfOver.toScheme B S hS).obj Y) :
    IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj (residuePointObject Y y), ⊤) :=
  haveI : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (residuePointObject Y y)) :=
    inferInstanceAs (IsLocallyNoetherian
      (Spec (.of (((BigFppfOver.toScheme B S hS).obj Y).residueField y))))
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

end AlgebraicGeometry.Space

end
