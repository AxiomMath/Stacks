module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsDerivations
public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsGlobalSmulPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapSections
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRightExact

/-!
# A self-map of a family over a rescaling of the base, on the multiplication by `ε`

Let `X'` be the total space of a flat family over an object `A` of `𝒞_Λ`, `G ⊆ X'` its special
fibre and `ε ∈ A` a generator of the kernel of `A ⟶ k`, so that multiplication by the pullback `t`
of `ε` is a map `ε· : 𝒪_{X'} ⟶ 𝓘_G` (`Deformation.Examples.specialEpsilonMul`).  Let `J : X' ⟶ X'`
be a self-map lying over the morphism of spectra of an endomorphism `σ` of `A` which multiplies
`ε` by `c`, and which preserves `G`.  Then the map of defining ideals of `J`, after the inverse
image of `ε·`, is multiplication by the function `c` followed by `ε·`:

`J^*(ε·) ≫ (J^*𝓘_G ⟶ 𝓘_G) = (J^*𝒪_{X'} ≅ 𝒪_{X'}) ≫ c· ≫ ε·`.

On a chart diagram `U ⟶ V` over `J` both sides send a function `s` on `V` to a function on `U`:
the left-hand side to the pullback of `t·s`, the right-hand side to `t·c·s|_U`; and the pullback of
`t` along `U ⟶ V` is the pullback of `σ(ε) = c·ε` along `U ⟶ X' ⟶ Spec A`, because `J` lies over
`Spec σ`.

## Main definitions

* `Deformation.Examples.familyBaseFunction`: an element of `A`, as a global function on `X'`.

## Main results

* `Deformation.Examples.chartDiagramPullback_familyChartScalar`: the pullback of `t` along a chart
  diagram over `J` is the pullback of `σ(ε)`.
* `Deformation.Examples.modulePullback_map_specialEpsilonMul_comp_idealSheafMap`: the displayed
  equation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Space Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

universe u

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (P : FlatAlgebraicSpaceFamily B hΛ hSpec)

/-- **An element of the base ring, as a global function on the total space**: its pullback along
the structure morphism `X' ⟶ Spec A`. -/
def familyBaseFunction (a : P.base) :
    GlobalSectionRing (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)) :=
  pullbackToGlobalFunctions B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
    (spaceBaseOver B hΛ hSpec P.base) (spaceTotalToBase B hΛ hSpec P)
    ((Scheme.ΓSpecIso (CommRingCat.of P.base)).inv.hom a)

/-- The value of the global function of `a` on an étale chart is the pullback of `a` there. -/
theorem familyBaseFunction_apply (a : P.base) (U : SmallEtale B (Spec (.of Λ)) hΛ P.space) :
    (familyBaseFunction B hΛ hSpec P a).1 (op U) = familyChartScalar B hΛ hSpec P U a :=
  rfl

variable {σ : P.base ⟶ P.base}
  {J : spaceTotalSpace B hΛ hSpec P ⟶ spaceTotalSpace B hΛ hSpec P}
  (hJ : J ≫ spaceTotalToBase B hΛ hSpec P =
    spaceTotalToBase B hΛ hSpec P ≫ schemeSpaceMap (spaceBaseOverMap B hΛ hSpec σ))

include hJ in
/-- **The pullback of an element of the base along a chart diagram over `J` is the pullback of
its image under `σ`.** -/
theorem chartDiagramPullback_familyChartScalar
    (d : ChartDiagram B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P).1
      (spaceTotalSpace B hΛ hSpec P).1 J.hom) (a : P.base) :
    chartDiagramPullback B (Spec (.of Λ)) hΛ J d (familyChartScalar B hΛ hSpec P d.V a) =
      familyChartScalar B hΛ hSpec P d.U (σ.hom a) := by
  refine (chartDiagramPullback_pullbackToGlobalFunctions B (Spec (.of Λ)) hΛ J
    (spaceBaseOver B hΛ hSpec P.base) (spaceTotalToBase B hΛ hSpec P)
    ((Scheme.ΓSpecIso (CommRingCat.of P.base)).inv.hom a) d).trans ?_
  rw [hJ, pullbackToGlobalFunctions_comp_schemeSpaceMap, toScheme_map_spaceBaseOverMap]
  have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ.hom.toRingHom)
  have h := congrArg (fun φ => φ.hom a) hnat
  change (Scheme.ΓSpecIso (CommRingCat.of P.base)).inv.hom (σ.hom a) =
    (Spec.map (CommRingCat.ofHom σ.hom.toRingHom)).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of P.base)).inv.hom a) at h
  show _ = (pullbackToGlobalFunctions B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
    (spaceBaseOver B hΛ hSpec P.base) (spaceTotalToBase B hΛ hSpec P)
    ((Scheme.ΓSpecIso (CommRingCat.of P.base)).inv.hom (σ.hom a))).1 (op d.U)
  rw [h]
  rfl

/-- **The identification `J^*𝒪_{X'} ≅ 𝒪_{X'}` on the chart section of a function** is the pullback
of the function along the chart diagram: the chart section of `s = s · 1` is the pullback of `s`
times the chart section of `1`, which the identification carries to `1`. -/
theorem modulePullbackUnitIso_hom_val_app_modulePullbackChartSection_eq
    {Y Z : AlgebraicSpaces B (Spec (.of Λ)) hΛ} (h : Y ⟶ Z)
    (d : ChartDiagram B (Spec (.of Λ)) hΛ Y.1 Z.1 h.hom)
    (s : (structureRingSheaf B (Spec (.of Λ)) hΛ Z).obj.obj (op d.V)) :
    (modulePullbackUnitIso B (Spec (.of Λ)) hΛ h).hom.val.app (op d.U)
        (modulePullbackChartSection B (Spec (.of Λ)) hΛ h
          (SheafOfModules.unit (structureRingSheaf B (Spec (.of Λ)) hΛ Z)) d s) =
      chartDiagramPullback B (Spec (.of Λ)) hΛ h d s := by
  let one : (SheafOfModules.unit (structureRingSheaf B (Spec (.of Λ)) hΛ Z)).val.obj (op d.V) :=
    (1 : (structureRingSheaf B (Spec (.of Λ)) hΛ Z).obj.obj (op d.V))
  refine (congrArg (fun x => (modulePullbackUnitIso B (Spec (.of Λ)) hΛ h).hom.val.app (op d.U) x)
    ((congrArg (modulePullbackChartSection B (Spec (.of Λ)) hΛ h
      (SheafOfModules.unit (structureRingSheaf B (Spec (.of Λ)) hΛ Z)) d)
        (mul_one s : s • one = s)).symm.trans
      (modulePullbackChartSection_smul B (Spec (.of Λ)) hΛ h
        (SheafOfModules.unit (structureRingSheaf B (Spec (.of Λ)) hΛ Z)) d s one))).trans ?_
  refine (((modulePullbackUnitIso B (Spec (.of Λ)) hΛ h).hom.val.app (op d.U)).hom.map_smul _
    _).trans ?_
  refine (congrArg (fun x => chartDiagramRestrict B (Spec (.of Λ)) hΛ h d s • x)
    (modulePullbackUnitIso_hom_val_app_modulePullbackChartSection B (Spec (.of Λ)) hΛ h d)).trans ?_
  exact mul_one (chartDiagramRestrict B (Spec (.of Λ)) hΛ h d s)

variable (f : P.base ⟶ residueFieldBase Λ k) (εA : P.base)
  (hk : RingHom.ker f.hom.toRingHom = Ideal.span {εA})

/-- The sections of the structure sheaf of the total space commute, in the unbundled form
`Stacks.Cohomology.SiteModules.globalSmul` takes. -/
instance familyStructureRingSheaf_isMulCommutative
    (U : (SmallEtale B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P).1)ᵒᵖ) :
    IsMulCommutative
      ((structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)).obj.obj U) :=
  structureRingSheaf_isMulCommutative B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P) U

include hJ in
/-- **A self-map of the total space over a rescaling `ε ↦ c ε` of the base, on the multiplication
by `ε`.**  `J^*(ε·) ≫ (J^*𝓘_G ⟶ 𝓘_G) = (J^*𝒪_{X'} ≅ 𝒪_{X'}) ≫ c· ≫ ε·`. -/
theorem modulePullback_map_specialEpsilonMul_comp_idealSheafMap (c : P.base)
    (hσ : σ.hom εA = c * εA)
    (f₀ : (⟨(spaceSpecialSubspace B hΛ hSpec P f).1.toFunctor,
        (spaceSpecialSubspace B hΛ hSpec P f).2.1⟩ : AlgebraicSpaces B (Spec (.of Λ)) hΛ) ⟶
      ⟨(spaceSpecialSubspace B hΛ hSpec P f).1.toFunctor,
        (spaceSpecialSubspace B hΛ hSpec P f).2.1⟩)
    (hsq : subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (spaceSpecialSubspace B hΛ hSpec P f) ≫ J =
      f₀ ≫ subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (spaceSpecialSubspace B hΛ hSpec P f)) :
    (modulePullback B (Spec (.of Λ)) hΛ J).map (specialEpsilonMul B hΛ hSpec P f εA hk) ≫
        idealSheafMap B (Spec (.of Λ)) hΛ (spaceSpecialSubspace B hΛ hSpec P f)
          (spaceSpecialSubspace B hΛ hSpec P f) J f₀ hsq =
      (modulePullbackUnitIso B (Spec (.of Λ)) hΛ J).hom ≫
        globalSmul _ (familyBaseFunction B hΛ hSpec P c) _ ≫
          specialEpsilonMul B hΛ hSpec P f εA hk := by
  refine ((modulePullbackAdjunction B (Spec (.of Λ)) hΛ J).homEquiv _ _).injective ?_
  refine (modulePushforwardHomEquiv B (Spec (.of Λ)) hΛ J _ _).injective ?_
  refine ModuleFMap.ext B (Spec (.of Λ)) hΛ (funext fun d => funext fun s => ?_)
  show (modulePullbackHomFMap B (Spec (.of Λ)) hΛ J _ _ _).app d s =
    (modulePullbackHomFMap B (Spec (.of Λ)) hΛ J _ _ _).app d s
  refine (modulePullbackHomFMap_app B (Spec (.of Λ)) hΛ J _ _ _ d s).trans
    (Eq.trans ?_ (modulePullbackHomFMap_app B (Spec (.of Λ)) hΛ J _ _ _ d s).symm)
  apply Subtype.ext
  have hA : ((modulePullback B (Spec (.of Λ)) hΛ J).map
        (specialEpsilonMul B hΛ hSpec P f εA hk)).val.app (op d.U)
        (modulePullbackUnitSection B (Spec (.of Λ)) hΛ J _ d s) =
      modulePullbackUnitSection B (Spec (.of Λ)) hΛ J _ d
        ((specialEpsilonMul B hΛ hSpec P f εA hk).val.app (op d.V) s) :=
    (congrArg (fun x => ((modulePullback B (Spec (.of Λ)) hΛ J).map
        (specialEpsilonMul B hΛ hSpec P f εA hk)).val.app (op d.U) x)
      (modulePullbackUnitSection_eq_modulePullbackChartSection B (Spec (.of Λ)) hΛ J _ d s)).trans
      ((modulePullbackChartSection_map B (Spec (.of Λ)) hΛ J _ _ d s).trans
        (modulePullbackUnitSection_eq_modulePullbackChartSection B (Spec (.of Λ)) hΛ J _ d
          _).symm)
  have hL := idealSheafMap_unitSection_coe B (Spec (.of Λ)) hΛ (spaceSpecialSubspace B hΛ hSpec P f)
    (spaceSpecialSubspace B hΛ hSpec P f) J f₀ hsq d
    ((specialEpsilonMul B hΛ hSpec P f εA hk).val.app (op d.V) s)
  have hu : (modulePullbackUnitIso B (Spec (.of Λ)) hΛ J).hom.val.app (op d.U)
      (modulePullbackUnitSection B (Spec (.of Λ)) hΛ J _ d s) =
      chartDiagramPullback B (Spec (.of Λ)) hΛ J d s :=
    (congrArg (fun x => (modulePullbackUnitIso B (Spec (.of Λ)) hΛ J).hom.val.app (op d.U) x)
      (modulePullbackUnitSection_eq_modulePullbackChartSection B (Spec (.of Λ)) hΛ J _ d s)).trans
      (modulePullbackUnitIso_hom_val_app_modulePullbackChartSection_eq B hΛ J d s)
  have ht := chartDiagramPullback_familyChartScalar B hΛ hSpec P hJ d εA
  rw [hσ] at ht
  let : CommRing ↑((structureRingSheaf B (Spec (.of Λ)) hΛ
      (spaceTotalSpace B hΛ hSpec P)).obj.obj (op d.U)) :=
    inferInstanceAs (CommRing ((smallEtaleRingedSite B (Spec (.of Λ)) hΛ P.space
      P.algebraic).O.obj.obj (op d.U)))
  have hc : familyChartScalar B hΛ hSpec P d.U (c * εA) =
      familyChartScalar B hΛ hSpec P d.U c * familyChartScalar B hΛ hSpec P d.U εA :=
    map_mul (familyChartRingHom B hΛ hSpec P d.U) c εA
  let pbs : ToType ((structureRingSheaf B (Spec (.of Λ)) hΛ
      (spaceTotalSpace B hΛ hSpec P)).obj.obj (op d.U)) :=
    chartDiagramPullback B (Spec (.of Λ)) hΛ J d s
  let s' : ToType ((structureRingSheaf B (Spec (.of Λ)) hΛ
      (spaceTotalSpace B hΛ hSpec P)).obj.obj (op d.V)) := s
  have key : chartDiagramPullback B (Spec (.of Λ)) hΛ J d
      ((specialEpsilonMul B hΛ hSpec P f εA hk).val.app (op d.V) s).1 =
      familyChartScalar B hΛ hSpec P d.U εA *
        ((familyBaseFunction B hΛ hSpec P c).1 (op d.U) * pbs) := by
    show chartDiagramPullback B (Spec (.of Λ)) hΛ J d
      (familyChartScalar B hΛ hSpec P d.V εA * s') = _
    let tU : ToType ((structureRingSheaf B (Spec (.of Λ)) hΛ
      (spaceTotalSpace B hΛ hSpec P)).obj.obj (op d.U)) := familyChartScalar B hΛ hSpec P d.U εA
    let cU : ToType ((structureRingSheaf B (Spec (.of Λ)) hΛ
      (spaceTotalSpace B hΛ hSpec P)).obj.obj (op d.U)) := familyChartScalar B hΛ hSpec P d.U c
    let tV' : ToType ((structureRingSheaf B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec P)).obj.obj (op d.U)) :=
      chartDiagramPullback B (Spec (.of Λ)) hΛ J d (familyChartScalar B hΛ hSpec P d.V εA)
    have m1 : chartDiagramPullback B (Spec (.of Λ)) hΛ J d
        (familyChartScalar B hΛ hSpec P d.V εA * s') = tV' * pbs :=
      map_mul (chartDiagramRestrict B (Spec (.of Λ)) hΛ J d) _ _
    have m3 : (cU * tU) * pbs = tU * (cU * pbs) := by ring
    exact (m1.trans (congrArg (· * pbs) (ht.trans hc : tV' = cU * tU))).trans m3
  exact ((congrArg (fun x => ((idealSheafMap B (Spec (.of Λ)) hΛ
      (spaceSpecialSubspace B hΛ hSpec P f) (spaceSpecialSubspace B hΛ hSpec P f) J f₀
      hsq).val.app (op d.U) x).1) hA).trans hL).trans
    (key.trans (congrArg (fun y => familyChartScalar B hΛ hSpec P d.U εA *
      ((familyBaseFunction B hΛ hSpec P c).1 (op d.U) * y)) hu.symm))

end Deformation.Examples

end
