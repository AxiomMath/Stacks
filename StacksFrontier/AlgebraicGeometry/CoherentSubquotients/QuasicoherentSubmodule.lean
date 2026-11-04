module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.FiniteTildeTFAE
public import StacksFrontier.Topology.Sheaves.Modules.Coherent
import all StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic

/-! # Quasi-coherent submodules (Stacks Tag 01Y1)
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace StacksDraft.AlgebraicGeometry.CoherentSubquotients.QuasicoherentSubmodule

private alias mono_as_sheaf := Stacks.AlgebraicGeometry.CoherentSubquotients.mono_as_sheaf

private alias restrictMap_mono := Stacks.AlgebraicGeometry.CoherentSubquotients.restrictMap_mono

/-- Restricting along `b` and then along `a` is the identity when `a ≫ b = 𝟙 X`. -/
private noncomputable def restrictFunctorRestrictIso {X Y : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion b] (h : a ≫ b = 𝟙 X) (M : X.Modules) :
    (Scheme.Modules.restrictFunctor a).obj ((Scheme.Modules.restrictFunctor b).obj M) ≅ M :=
  ((Scheme.Modules.restrictFunctorComp a b).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr h).app M ≪≫
    (Scheme.Modules.restrictFunctorId (X := X)).app M

private theorem mono_quasicoherent_isFiniteTildeOn {X : Scheme.{u}}
    [IsLocallyNoetherian X] {F G : X.Modules} [F.IsCoherent]
    [G.IsQuasicoherent] (f : G ⟶ F) [Mono f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    StacksDraft.AlgebraicGeometry.CoherenceCriteria.FiniteTildeTFAE.IsFiniteTildeOn G U hU := by
  let A := Γ(X, U)
  let R := CommRingCat.of A
  let e := hU.isoSpec
  let G₀ := (Scheme.Modules.restrictFunctor U.ι).obj G
  let F₀ := (Scheme.Modules.restrictFunctor U.ι).obj F
  let G₁ := (Scheme.Modules.restrictFunctor e.inv).obj G₀
  let F₁ := (Scheme.Modules.restrictFunctor e.inv).obj F₀
  let g : G₁ ⟶ F₁ := (Scheme.Modules.restrictFunctor e.inv).map
    ((Scheme.Modules.restrictFunctor U.ι).map f)
  have hFtildeAll :=
    ((StacksDraft.AlgebraicGeometry.CoherenceCriteria.FiniteTildeTFAE.coherent_tfae X F).out 1 4).mp
      ‹F.IsCoherent›
  obtain ⟨M, hM, ⟨eM⟩⟩ := hFtildeAll U hU
  have : Module.Finite A M := hM
  have eM' : F₀ ≅ (Scheme.Modules.restrictFunctor e.hom).obj (tilde M) :=
    eM ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback e.hom).app (tilde M)).symm
  let eF : F₁ ≅ tilde M :=
    (Scheme.Modules.restrictFunctor e.inv).mapIso eM' ≪≫
      restrictFunctorRestrictIso e.inv e.hom e.inv_hom_id (tilde M)
  have : G₁.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor e.inv G₀
  have hfrom : IsIso G₁.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G₁
  let N := moduleSpecΓFunctor.obj G₁
  let eN : M ≅ moduleSpecΓFunctor.obj F₁ :=
    (AlgebraicGeometry.tilde.toTildeΓNatIso.app M) ≪≫
      (moduleSpecΓFunctor.mapIso eF).symm
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hFsec : Module.Finite A (moduleSpecΓFunctor.obj F₁) :=
    Module.Finite.of_surjective eN.hom.hom
      (ConcreteCategory.bijective_of_isIso eN.hom).2
  have : Mono g := by
    have : Mono ((Scheme.Modules.restrictFunctor U.ι).map f) := restrictMap_mono U.ι f
    exact restrictMap_mono e.inv ((Scheme.Modules.restrictFunctor U.ι).map f)
  let L : (↑N) →ₗ[A] ↑(moduleSpecΓFunctor.obj F₁) :=
    (moduleSpecΓFunctor.map g).hom
  have hLinj : Function.Injective L := by
    let : @Mono (SheafOfModules (Spec R).ringCatSheaf) (inferInstance) G₁ F₁ g :=
      mono_as_sheaf g
    let : (moduleSpecΓFunctor (R := R)).IsRightAdjoint :=
      (tilde.adjunction (R := R)).isRightAdjoint
    let : CategoryTheory.Limits.PreservesLimitsOfShape
        CategoryTheory.Limits.WalkingCospan (moduleSpecΓFunctor (R := R)) := inferInstance
    have hEm : (moduleSpecΓFunctor (R := R)).PreservesMonomorphisms :=
      CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
    have hNmap : Mono (moduleSpecΓFunctor.map g) := hEm.preserves g
    have hAppInj := (ModuleCat.mono_iff_injective (moduleSpecΓFunctor.map g)).mp hNmap
    intro x y hxy
    change (ConcreteCategory.hom (moduleSpecΓFunctor.map g)) x =
      (ConcreteCategory.hom (moduleSpecΓFunctor.map g)) y at hxy
    exact hAppInj hxy
  have hN : Module.Finite A (↑N) := Module.Finite.of_injective L hLinj
  let eG : tilde N ≅ G₁ := @CategoryTheory.asIso _ _ _ _ G₁.fromTildeΓ hfrom
  exact ⟨N, hN, ⟨(restrictFunctorRestrictIso e.hom e.inv e.hom_inv_id G₀).symm ≪≫
    (Scheme.Modules.restrictFunctor e.hom).mapIso eG.symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback e.hom).app (tilde N)⟩⟩

/-- A quasi-coherent submodule of a coherent module on a locally Noetherian
scheme is coherent. -/
theorem isCoherent_of_mono {X : Scheme.{u}} [IsLocallyNoetherian X]
    {F G : X.Modules} [F.IsCoherent] [G.IsQuasicoherent]
    (f : G ⟶ F) [Mono f] : G.IsCoherent :=
  ((StacksDraft.AlgebraicGeometry.CoherenceCriteria.FiniteTildeTFAE.coherent_tfae X G).out 1 4).mpr
    (mono_quasicoherent_isFiniteTildeOn f)

end StacksDraft.AlgebraicGeometry.CoherentSubquotients.QuasicoherentSubmodule

end
