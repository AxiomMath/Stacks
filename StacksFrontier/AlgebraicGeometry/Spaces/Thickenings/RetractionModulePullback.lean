module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionStructureSheafSquareZero
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.Deformation.ToposThickening.DerivedExtensionOfScalarsExists

/-!
# Pullback of modules along `X ⟶ X'` as extension of scalars along `𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X`

Let `X ⟶ X' ⟶ X` be the base change of `Spec k ⟶ Spec k[V] ⟶ Spec k`, so that
`AlgebraicGeometry.Space.squareZeroModuleEquivalence` identifies the
`𝒪_X[𝒪_X ⊗_k V]`-modules on the small étale site of `X` with the `𝒪_{X'}`-modules. Through this
identification the direct image of modules along `i : X ⟶ X'` is restriction of scalars along
the projection `𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X`
(`AlgebraicGeometry.Space.squareZeroPushforwardIso`), and so the pullback of modules along `i` is
extension of scalars along it (`AlgebraicGeometry.Space.squareZeroPullbackIso`).

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift
  Stacks.TensorByBaseModule

universe u

namespace AlgebraicGeometry.Space

variable {k : Type u} [CommRing k] {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of k) ⟶ S} {hk : B.Contains (Spec (.of k))} {V : SiteModule k B}
  {X X' : AlgebraicSpaces B S hS} {i : X ⟶ X'} (hi : IsThickeningHom B S hS i)
  {q : X' ⟶ X} (h : i ≫ q = 𝟙 X) {hq : yoneda.relativelyRepresentable q.hom}
  {p : X.1 ⟶ yoneda.obj (algebraOver k B S hS toS hk)}
  {p' : X'.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS V)}
  {τ : squareZeroOver k B S hS toS V ⟶ algebraOver k B S hS toS hk}
  (hip : i.hom ≫ p' = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk V))
  (hpb : IsPullback q.hom p' p (yoneda.map τ))
  (hβτ : squareZeroArrow k B S hS toS hk V ≫ τ = 𝟙 _)

/-- **The direct image of modules along `i : X ⟶ X'` is restriction of scalars along the
projection `𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X`**, read through
`AlgebraicGeometry.Space.squareZeroModuleEquivalence`. -/
def squareZeroPushforwardIso :
    smallBaseChangeModulePushforward.{u, u} B S hS i hi.isClosedImmersion.rep ≅
      SheafOfModules.restrictScalars
          ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
            (sqZeroExtSheafAnySiteProj ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
              (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
              (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj))) ⋙
        (squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).functor :=
  letI := smallBaseChange_isDenseSubsite_of_isThickeningHom B S hS hi
  SheafOfModules.pushforwardCongr (φ := smallBaseChangeSharp B S hS i hi.isClosedImmersion.rep)
    (ψ := (sheafCompose (SmallEtale.topology B S hS X'.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((squareZeroStructureSheafIso (hq := hq) hi h hip hpb hβτ).hom ≫
          (thickeningRetractionEquivalence B S hS hi h hq CommRingCat.{u}).functor.map
            (sqZeroExtSheafAnySiteProj _)))
    (congrArg (sheafCompose (SmallEtale.topology B S hS X'.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).map
        (squareZeroStructureSheafIso_hom_comp (hq := hq) hi h hip hpb hβτ).symm) ≪≫
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **The pullback of modules along `i : X ⟶ X'` is extension of scalars along the projection
`𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X`**, read through `AlgebraicGeometry.Space.squareZeroModuleEquivalence`. -/
def squareZeroPullbackIso :
    (squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).functor ⋙
        (smallEtaleRingedToposHom B S hS i).toModulesHom.pullbackModules ≅
      extensionOfScalars (sqZeroExtSheafAnySiteProj ((tensorByBaseModuleOfHom k
          (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)) :=
  ((squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).toAdjunction.comp
      (RingedToposHom.pullbackAdjPushforwardModules
        (smallEtaleRingedToposHom B S hS i))).ofNatIsoRight
    (Functor.isoWhiskerRight (pushforwardModulesIsoModulePushforward B S hS i ≪≫
        modulePushforwardChartIso B S hS i hi.isClosedImmersion.rep ≪≫
        squareZeroPushforwardIso hi h hip hpb hβτ) _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).unitIso.symm ≪≫
      Functor.rightUnitor _) |>.leftAdjointUniq
    (Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction _ _ _ _)

end AlgebraicGeometry.Space

end
