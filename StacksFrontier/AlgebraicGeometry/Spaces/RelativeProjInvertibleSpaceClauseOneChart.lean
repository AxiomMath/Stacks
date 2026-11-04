module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOne
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackSectionCalculus
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaUniqueClauseOne
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaSection
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSchemeTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiAdjoint

/-! # scratch -/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules (pullbackSection)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.ModuleLimits (pullbackComp_inv_val_app_pullbackSection canHom
  canHom_val_app_pullbackSection doublePullbackSection hom_ext_of_doublePullbackSection)
open AlgebraicGeometry.Space (pullbackAdjointPsi)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

namespace GradedPowerMap

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f) (g : T ⟶ P.coveringOpen.toScheme) (hg : g ≫ P.coveringOpen.ι = 𝟙 T)

include hg in
/-- A right inverse of the inclusion `ι : U(ψ) ⟶ T` is a right inverse on points. -/
theorem base_apply_base_of_section (x : T) : P.coveringOpen.ι.base (g.base x) = x := by
  have h := congrArg (fun k : T ⟶ T => k.base x) hg
  simpa using h

include hg in
/-- When the inclusion `ι : U(ψ) ⟶ T` has a right inverse, every open of `T` is the image of
its preimage. -/
theorem le_image_preimage_of_section (W : T.Opens) :
    W ≤ P.coveringOpen.ι ''ᵁ (P.coveringOpen.ι ⁻¹ᵁ W) := by
  intro x hx
  refine ⟨g.base x, ?_, base_apply_base_of_section P g hg x⟩
  show P.coveringOpen.ι.base (g.base x) ∈ W
  rw [base_apply_base_of_section P g hg x]
  exact hx

/-- **`θ` read along a right inverse `g` of the inclusion, on a pulled-back section**: it carries
the section of `r_w^*𝒪(n)` pulled back from a section `z` of `𝒪(n)` over an open `O` of
`Proj_S(𝒜)` to the restriction of the value of `θ` on the section of `r^*𝒪(n)` pulled back from
`z`. -/
theorem thetaOnSection_val_app_pullbackSection (n : ℤ) (O : (relativeProj A).scheme.Opens)
    (O' : P.coveringOpen.toScheme.Opens) (W : T.Opens)
    (hO' : O' ≤ P.globalMorphism (relativeProj A) ⁻¹ᵁ O) (hW : W ≤ g ⁻¹ᵁ O')
    (h : W ≤ (g ≫ P.globalMorphism (relativeProj A)) ⁻¹ᵁ O)
    (hV : W ≤ P.coveringOpen.ι ''ᵁ O') (z : ((twD A).algebra.piece n).val.obj (op O)) :
    (P.thetaOnSection g hg n).val.app (op W)
        (pullbackSection (g ≫ P.globalMorphism (relativeProj A))
          ((twD A).algebra.piece n) O W h z) =
      (tensorPowerModule T P.L n).val.map (homOfLE hV).op
        ((P.theta.app n).val.app (op O')
          (pullbackSection (P.globalMorphism (relativeProj A))
            ((twD A).algebra.piece n) O O' hO' z)) := by
  have e1 : ((Scheme.Modules.pullbackComp g (P.globalMorphism (relativeProj A))).inv.app
        ((twD A).algebra.piece n)).val.app (op W)
        (pullbackSection (g ≫ P.globalMorphism (relativeProj A))
          ((twD A).algebra.piece n) O W h z) =
      pullbackSection g ((Stacks.Conormal.gradedPullback
          (P.globalMorphism (relativeProj A)) (twD A).algebra).piece n) O' W hW
        (pullbackSection (P.globalMorphism (relativeProj A))
          ((twD A).algebra.piece n) O O' hO' z) :=
    pullbackComp_inv_val_app_pullbackSection g (P.globalMorphism (relativeProj A))
      ((twD A).algebra.piece n) O O' W hO' hW h z
  have e2 := Scheme.Modules.pullbackSection_naturality g (P.theta.app n) O' W hW
    (pullbackSection (P.globalMorphism (relativeProj A)) ((twD A).algebra.piece n) O O' hO' z)
  have e3 : ((Scheme.Modules.pullback g).map
        ((Scheme.Modules.restrictFunctorIsoPullback P.coveringOpen.ι).hom.app
          (tensorPowerModule T P.L n)) ≫
      (Scheme.Modules.pullbackComp g P.coveringOpen.ι).hom.app (tensorPowerModule T P.L n) ≫
      (Scheme.Modules.pullbackCongr hg).hom.app (tensorPowerModule T P.L n) ≫
      (Scheme.Modules.pullbackId T).hom.app (tensorPowerModule T P.L n)).val.app (op W)
        (pullbackSection g
          ((Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn P.L P.coveringOpen).piece n)
          O' W hW
          ((P.theta.app n).val.app (op O')
            (pullbackSection (P.globalMorphism (relativeProj A))
              ((twD A).algebra.piece n) O O' hO' z))) =
      (tensorPowerModule T P.L n).val.map (homOfLE hV).op
        ((P.theta.app n).val.app (op O')
          (pullbackSection (P.globalMorphism (relativeProj A))
            ((twD A).algebra.piece n) O O' hO' z)) :=
    AlgebraicGeometry.Space.sectionPieceChain_val_app_pullbackSection g hg
      (tensorPowerModule T P.L n) O' W hW hV
      ((P.theta.app n).val.app (op O')
        (pullbackSection (P.globalMorphism (relativeProj A))
          ((twD A).algebra.piece n) O O' hO' z))
  show ((Scheme.Modules.pullback g).map
        ((Scheme.Modules.restrictFunctorIsoPullback P.coveringOpen.ι).hom.app
          (tensorPowerModule T P.L n)) ≫
      (Scheme.Modules.pullbackComp g P.coveringOpen.ι).hom.app (tensorPowerModule T P.L n) ≫
      (Scheme.Modules.pullbackCongr hg).hom.app (tensorPowerModule T P.L n) ≫
      (Scheme.Modules.pullbackId T).hom.app (tensorPowerModule T P.L n)).val.app (op W)
      (((Scheme.Modules.pullback g).map (P.theta.app n)).val.app (op W)
        (((Scheme.Modules.pullbackComp g (P.globalMorphism (relativeProj A))).inv.app
            ((twD A).algebra.piece n)).val.app (op W)
          (pullbackSection (g ≫ P.globalMorphism (relativeProj A))
            ((twD A).algebra.piece n) O W h z))) = _
  rw [e1, e2]
  exact e3

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism


namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

/-- **Tag 01NR's `ψ` in adjoint form on a pulled-back section**: for `ι : X ⟶ Proj_Y(A)` and
`f = ι ≫ π`, the morphism `f^*A_n ⟶ ι^*𝒪(n)` carries the section pulled back along `f` from a
section `a` of `A_n` over `V` to the section pulled back along `ι` from `ψ(a)`. -/
theorem pullbackAdjointPsi_val_app_pullbackSection {X Y : Scheme.{u}} (A : SheafGradedAlgebra.{u} Y)
    (ι : X ⟶ (relativeProj A).scheme) (f : X ⟶ Y) (hf : f = ι ≫ (relativeProj A).toBase) (n : ℕ)
    (V : Y.Opens) (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ V)
    (hW' : W ≤ ι ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
    (a : (A.piece (n : ℤ)).val.obj (op V)) :
    (AlgebraicGeometry.Space.pullbackAdjointPsi A ι f hf n).val.app (op W)
        (pullbackSection f (A.piece (n : ℤ)) V W hW a) =
      pullbackSection ι ((GradedPowerMap.twD A).algebra.piece (n : ℤ))
        ((relativeProj A).toBase ⁻¹ᵁ V) W hW' (GradedPowerMap.psiU A n V a) := by
  have e1 := Scheme.Modules.pullbackSection_congr hf (A.piece (n : ℤ)) V W hW hW' a
  have e2 : ((Scheme.Modules.pullbackComp ι (relativeProj A).toBase).inv.app
        (A.piece (n : ℤ))).val.app (op W)
        (pullbackSection (ι ≫ (relativeProj A).toBase) (A.piece (n : ℤ)) V W hW' a) =
      pullbackSection ι ((Scheme.Modules.pullback (relativeProj A).toBase).obj
          (A.piece (n : ℤ))) ((relativeProj A).toBase ⁻¹ᵁ V) W hW'
        (pullbackSection (relativeProj A).toBase (A.piece (n : ℤ)) V
          ((relativeProj A).toBase ⁻¹ᵁ V) le_rfl a) :=
    pullbackComp_inv_val_app_pullbackSection ι (relativeProj A).toBase (A.piece (n : ℤ)) V
      ((relativeProj A).toBase ⁻¹ᵁ V) W le_rfl hW' hW' a
  have e3 := Scheme.Modules.pullbackSection_naturality ι
    (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).homEquiv _ _).symm
      ((GradedPowerMap.twD A).ψ n)) ((relativeProj A).toBase ⁻¹ᵁ V) W hW'
    (pullbackSection (relativeProj A).toBase (A.piece (n : ℤ)) V
      ((relativeProj A).toBase ⁻¹ᵁ V) le_rfl a)
  have e4 : (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).homEquiv _
          _).symm ((GradedPowerMap.twD A).ψ n)).val.app (op ((relativeProj A).toBase ⁻¹ᵁ V))
        (pullbackSection (relativeProj A).toBase (A.piece (n : ℤ)) V
          ((relativeProj A).toBase ⁻¹ᵁ V) le_rfl a) =
      GradedPowerMap.psiU A n V a := by
    have h := Stacks.AlgebraicGeometry.ModuleLimits.homEquiv_val_app (relativeProj A).toBase
      (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).homEquiv _ _).symm
        ((GradedPowerMap.twD A).ψ n)) V a
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  show ((Scheme.Modules.pullback ι).map
      (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).homEquiv _ _).symm
        ((GradedPowerMap.twD A).ψ n))).val.app (op W)
      (((Scheme.Modules.pullbackComp ι (relativeProj A).toBase).inv.app
          (A.piece (n : ℤ))).val.app (op W)
        (((Scheme.Modules.pullbackCongr hf).hom.app (A.piece (n : ℤ))).val.app (op W)
          (pullbackSection f (A.piece (n : ℤ)) V W hW a))) = _
  rw [e1, e2, e3, e4]

namespace GradedPowerMap

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f) (g : T ⟶ P.coveringOpen.toScheme) (hg : g ≫ P.coveringOpen.ι = 𝟙 T)

include hg in
/-- **Clause (1) of [Stacks, Tag 01O9] in morphism form, when `U(ψ)` is everything.**  For a
right inverse `g` of the inclusion `ι : U(ψ) ⟶ T`, the inverse image along `r_w = g ≫ r` of
`ψ_P` of Tag 01NR, in the adjoint form `f^*𝒜_d ⟶ r_w^*𝒪(d)`
(`AlgebraicGeometry.Space.pullbackAdjointPsi`), followed by `θ` read on `T` along `g`
(`…GradedPowerMap.thetaOnSection`), is the adjoint transpose of `ψ`.

This is the sections statement `…GradedPowerMap.theta_clauseOne` read as an identity of
morphisms: both sides are maps out of the inverse image `f^*𝒜_d`, so they agree as soon as they
agree on the pulled-back sections. -/
theorem pullbackAdjointPsi_comp_thetaOnSection (d : ℕ)
    (hf : f = (g ≫ P.globalMorphism (relativeProj A)) ≫ (relativeProj A).toBase) :
    AlgebraicGeometry.Space.pullbackAdjointPsi A (g ≫ P.globalMorphism (relativeProj A)) f hf d ≫
        P.thetaOnSection g hg (d : ℤ) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (P.ψ d) ≫
        (powCompare P.L d).hom := by
  refine Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_pullbackSection f fun V a => ?_
  have hW' : f ⁻¹ᵁ V ≤ (g ≫ P.globalMorphism (relativeProj A)) ⁻¹ᵁ
      ((relativeProj A).toBase ⁻¹ᵁ V) := by
    show f ⁻¹ᵁ V ≤
      ((g ≫ P.globalMorphism (relativeProj A)) ≫ (relativeProj A).toBase) ⁻¹ᵁ V
    rw [← hf]
  have hO' : P.toBase ⁻¹ᵁ V ≤ P.globalMorphism (relativeProj A) ⁻¹ᵁ
      ((relativeProj A).toBase ⁻¹ᵁ V) := (P.toBase_preimage_eq V).le
  have hgV : f ⁻¹ᵁ V ≤ g ⁻¹ᵁ (P.toBase ⁻¹ᵁ V) := by
    intro x hx
    show g.base x ∈ P.toBase ⁻¹ᵁ V
    show P.coveringOpen.ι.base (g.base x) ∈ f ⁻¹ᵁ V
    rw [base_apply_base_of_section P g hg x]
    exact hx
  have hV : f ⁻¹ᵁ V ≤ P.coveringOpen.ι ''ᵁ (P.toBase ⁻¹ᵁ V) :=
    le_image_preimage_of_section P g hg (f ⁻¹ᵁ V)
  -- the two legs on a pulled-back section
  have hA1 := pullbackAdjointPsi_val_app_pullbackSection A
    (g ≫ P.globalMorphism (relativeProj A)) f hf d V (f ⁻¹ᵁ V) le_rfl hW' a
  have hA2 := P.thetaOnSection_val_app_pullbackSection g hg (d : ℤ)
    ((relativeProj A).toBase ⁻¹ᵁ V) (P.toBase ⁻¹ᵁ V) (f ⁻¹ᵁ V) hO' hgV hW' hV
    (GradedPowerMap.psiU A d V a)
  -- two restrictions in a row, and a restriction along an endomorphism of an open
  have hres : ∀ {M : T.Modules} {U₁ U₂ : T.Opens} (i : U₂ ⟶ U₁) (j : U₁ ⟶ U₂)
      (x : M.val.obj (op U₁)), M.val.map j.op (M.val.map i.op x) = x := by
    intro M U₁ U₂ i j x
    have h1 := (PresheafOfModules.map_comp_apply M.val i.op j.op x).symm
    rw [show i.op ≫ j.op = 𝟙 (op U₁) from Subsingleton.elim _ _] at h1
    rw [h1]
    simp
    rfl
  -- the value of `θ` on the pullback-unit section, from clause (1) on sections
  have hsh : ((Stacks.Conormal.gradedPullback (P.globalMorphism (relativeProj A))
          (twD A).algebra).piece (d : ℤ)).val.map (homOfLE hO').op
        (pullbackSection (P.globalMorphism (relativeProj A)) ((twD A).algebra.piece (d : ℤ))
          ((relativeProj A).toBase ⁻¹ᵁ V)
          (P.globalMorphism (relativeProj A) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)) le_rfl
          (GradedPowerMap.psiU A d V a)) =
      pullbackSection (P.globalMorphism (relativeProj A)) ((twD A).algebra.piece (d : ℤ))
        ((relativeProj A).toBase ⁻¹ᵁ V) (P.toBase ⁻¹ᵁ V) hO' (GradedPowerMap.psiU A d V a) :=
    Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_shrink
      (P.globalMorphism (relativeProj A)) ((twD A).algebra.piece (d : ℤ))
      ((relativeProj A).toBase ⁻¹ᵁ V)
      (P.globalMorphism (relativeProj A) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
      (P.toBase ⁻¹ᵁ V) le_rfl hO' hO' (GradedPowerMap.psiU A d V a)
  have hnat := PresheafOfModules.naturality_apply (P.theta.app (d : ℤ)).val (homOfLE hO').op
    (pullbackSection (P.globalMorphism (relativeProj A)) ((twD A).algebra.piece (d : ℤ))
      ((relativeProj A).toBase ⁻¹ᵁ V)
      (P.globalMorphism (relativeProj A) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)) le_rfl
      (GradedPowerMap.psiU A d V a))
  have hself : pullbackSection (P.globalMorphism (relativeProj A))
        ((twD A).algebra.piece (d : ℤ)) ((relativeProj A).toBase ⁻¹ᵁ V)
        (P.globalMorphism (relativeProj A) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)) le_rfl
        (GradedPowerMap.psiU A d V a) =
      Stacks.RingedSpace.pullbackUnit
        (P.globalMorphism (relativeProj A)).toLRSHom.toShHom ((twD A).algebra.piece (d : ℤ))
        (op ((relativeProj A).toBase ⁻¹ᵁ V)) (GradedPowerMap.psiU A d V a) :=
    Stacks.Conormal.pullbackSection_self (P.globalMorphism (relativeProj A))
      ((twD A).algebra.piece (d : ℤ)) ((relativeProj A).toBase ⁻¹ᵁ V)
      (GradedPowerMap.psiU A d V a)
  have hcl1 : (tensorPowerModule T P.L (d : ℤ)).val.map
        (P.coveringOpen.ι.opensFunctor.map (homOfLE hO')).op
        ((P.theta.app (d : ℤ)).val.app
          (op (P.globalMorphism (relativeProj A) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
          (Stacks.RingedSpace.pullbackUnit
            (P.globalMorphism (relativeProj A)).toLRSHom.toShHom
            ((twD A).algebra.piece (d : ℤ)) (op ((relativeProj A).toBase ⁻¹ᵁ V))
            (GradedPowerMap.psiU A d V a))) =
      (tensorPowerModule T P.L (d : ℤ)).val.map
        (homOfLE (P.coveringOpen.ι.image_preimage_le (f ⁻¹ᵁ V))).op
        ((powCompare P.L d).hom.val.app (op (f ⁻¹ᵁ V)) (P.value d V a)) := by
    rw [show (P.coveringOpen.ι.opensFunctor.map (homOfLE hO')) =
      P.coveringOpen.ι.opensFunctor.map (eqToHom (P.toBase_preimage_eq V)) from
        Subsingleton.elim _ _]
    exact P.theta_clauseOne V d a
  -- assemble
  have hR : (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
        (P.ψ d)).val.app (op (f ⁻¹ᵁ V))
        (pullbackSection f (A.piece (d : ℤ)) V (f ⁻¹ᵁ V) le_rfl a) = P.value d V a := by
    have h := Stacks.AlgebraicGeometry.ModuleLimits.homEquiv_val_app f
      (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (P.ψ d)) V a
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  show (P.thetaOnSection g hg (d : ℤ)).val.app (op (f ⁻¹ᵁ V))
        ((AlgebraicGeometry.Space.pullbackAdjointPsi A
            (g ≫ P.globalMorphism (relativeProj A)) f hf d).val.app (op (f ⁻¹ᵁ V))
          (pullbackSection f (A.piece (d : ℤ)) V (f ⁻¹ᵁ V) le_rfl a)) =
      (powCompare P.L d).hom.val.app (op (f ⁻¹ᵁ V))
        ((((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
            (P.ψ d)).val.app (op (f ⁻¹ᵁ V))
          (pullbackSection f (A.piece (d : ℤ)) V (f ⁻¹ᵁ V) le_rfl a))
  rw [hA1, hA2, hR, ← hsh, hnat, hself]
  show (tensorPowerModule T P.L (d : ℤ)).val.map (homOfLE hV).op
      ((tensorPowerModule T P.L (d : ℤ)).val.map
        (P.coveringOpen.ι.opensFunctor.map (homOfLE hO')).op
        ((P.theta.app (d : ℤ)).val.app
          (op (P.globalMorphism (relativeProj A) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
          (Stacks.RingedSpace.pullbackUnit
            (P.globalMorphism (relativeProj A)).toLRSHom.toShHom
            ((twD A).algebra.piece (d : ℤ)) (op ((relativeProj A).toBase ⁻¹ᵁ V))
            (GradedPowerMap.psiU A d V a)))) = _
  rw [hcl1]
  exact hres (homOfLE (P.coveringOpen.ι.image_preimage_le (f ⁻¹ᵁ V))) (homOfLE hV) _

end GradedPowerMap

/-- **Tag 01NR's `ψ` in adjoint form is compatible with a further inverse image**: for
`c : Z ⟶ X`, `ι' = c ≫ ι` and `f' = c ≫ f`, the inverse image along `c` of `f^*A_n ⟶ ι^*𝒪(n)`,
followed by the contraction `c^*(ι^*𝒪(n)) ≅ ι'^*𝒪(n)`, is the contraction
`c^*(f^*A_n) ≅ f'^*A_n` followed by `ψ` in adjoint form along `ι'`. -/
theorem pullback_map_pullbackAdjointPsi_comp_canHom {X Y Z : Scheme.{u}}
    (A : SheafGradedAlgebra.{u} Y) (ι : X ⟶ (relativeProj A).scheme) (fX : X ⟶ Y)
    (hfX : fX = ι ≫ (relativeProj A).toBase) (c : Z ⟶ X) (ι' : Z ⟶ (relativeProj A).scheme)
    (hι' : c ≫ ι = ι') (fZ : Z ⟶ Y) (hfZ : c ≫ fX = fZ)
    (hfZ' : fZ = ι' ≫ (relativeProj A).toBase) (n : ℕ) :
    (Scheme.Modules.pullback c).map (pullbackAdjointPsi A ι fX hfX n) ≫
        canHom c ι ι' hι' ((GradedPowerMap.twD A).algebra.piece (n : ℤ)) =
      canHom c fX fZ hfZ (A.piece (n : ℤ)) ≫ pullbackAdjointPsi A ι' fZ hfZ' n := by
  refine hom_ext_of_doublePullbackSection c fX (F := A.piece (n : ℤ)) fun V a => ?_
  have hw : fX ⁻¹ᵁ V ≤ ι ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) := by
    show fX ⁻¹ᵁ V ≤ (ι ≫ (relativeProj A).toBase) ⁻¹ᵁ V
    rw [← hfX]
  have h2 : c ⁻¹ᵁ (fX ⁻¹ᵁ V) ≤ fZ ⁻¹ᵁ V := by
    rw [← hfZ]
    exact le_rfl
  have h3 : c ⁻¹ᵁ (fX ⁻¹ᵁ V) ≤ ι' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) := by
    show c ⁻¹ᵁ (fX ⁻¹ᵁ V) ≤ (ι' ≫ (relativeProj A).toBase) ⁻¹ᵁ V
    rw [← hfZ']
    exact h2
  have hL1 := Scheme.Modules.pullbackSection_naturality c (pullbackAdjointPsi A ι fX hfX n)
    (fX ⁻¹ᵁ V) (c ⁻¹ᵁ (fX ⁻¹ᵁ V)) le_rfl
    (pullbackSection fX (A.piece (n : ℤ)) V (fX ⁻¹ᵁ V) le_rfl a)
  have hL2 := pullbackAdjointPsi_val_app_pullbackSection A ι fX hfX n V (fX ⁻¹ᵁ V) le_rfl hw a
  have hL3 : (canHom c ι ι' hι' ((GradedPowerMap.twD A).algebra.piece (n : ℤ))).val.app
        (op (c ⁻¹ᵁ (fX ⁻¹ᵁ V)))
        (pullbackSection c ((Scheme.Modules.pullback ι).obj
            ((GradedPowerMap.twD A).algebra.piece (n : ℤ))) (fX ⁻¹ᵁ V) (c ⁻¹ᵁ (fX ⁻¹ᵁ V)) le_rfl
          (pullbackSection ι ((GradedPowerMap.twD A).algebra.piece (n : ℤ))
            ((relativeProj A).toBase ⁻¹ᵁ V) (fX ⁻¹ᵁ V) hw (GradedPowerMap.psiU A n V a))) =
      pullbackSection ι' ((GradedPowerMap.twD A).algebra.piece (n : ℤ))
        ((relativeProj A).toBase ⁻¹ᵁ V) (c ⁻¹ᵁ (fX ⁻¹ᵁ V)) h3 (GradedPowerMap.psiU A n V a) :=
    canHom_val_app_pullbackSection c ι ι' hι'
      ((GradedPowerMap.twD A).algebra.piece (n : ℤ)) ((relativeProj A).toBase ⁻¹ᵁ V)
      (fX ⁻¹ᵁ V) (c ⁻¹ᵁ (fX ⁻¹ᵁ V)) hw le_rfl h3 (GradedPowerMap.psiU A n V a)
  have hR1 : (canHom c fX fZ hfZ (A.piece (n : ℤ))).val.app (op (c ⁻¹ᵁ (fX ⁻¹ᵁ V)))
        (doublePullbackSection c fX (A.piece (n : ℤ)) V a) =
      pullbackSection fZ (A.piece (n : ℤ)) V (c ⁻¹ᵁ (fX ⁻¹ᵁ V)) h2 a :=
    canHom_val_app_pullbackSection c fX fZ hfZ (A.piece (n : ℤ)) V (fX ⁻¹ᵁ V)
      (c ⁻¹ᵁ (fX ⁻¹ᵁ V)) le_rfl le_rfl h2 a
  have hR2 := pullbackAdjointPsi_val_app_pullbackSection A ι' fZ hfZ' n V
    (c ⁻¹ᵁ (fX ⁻¹ᵁ V)) h2 h3 a
  show (canHom c ι ι' hι' ((GradedPowerMap.twD A).algebra.piece (n : ℤ))).val.app
        (op (c ⁻¹ᵁ (fX ⁻¹ᵁ V)))
        (((Scheme.Modules.pullback c).map (pullbackAdjointPsi A ι fX hfX n)).val.app
          (op (c ⁻¹ᵁ (fX ⁻¹ᵁ V))) (doublePullbackSection c fX (A.piece (n : ℤ)) V a)) =
      (pullbackAdjointPsi A ι' fZ hfZ' n).val.app (op (c ⁻¹ᵁ (fX ⁻¹ᵁ V)))
        ((canHom c fX fZ hfZ (A.piece (n : ℤ))).val.app (op (c ⁻¹ᵁ (fX ⁻¹ᵁ V)))
          (doublePullbackSection c fX (A.piece (n : ℤ)) V a))
  rw [hR1, hR2, doublePullbackSection, hL1, hL2, hL3]

/-- `…pullback_map_pullbackAdjointPsi_comp_canHom` with a further morphism `Θ'` out of `ι'^*𝒪(n)`
and the composite `Θ = ψ_{ι'} ≫ Θ'` as variables: this is the shape in which the inverse image
along `c` of `ψ` of Tag 01NR followed by a reading of `θ` is compared with `θ` read at `ι'`. -/
theorem pullback_map_pullbackAdjointPsi_comp_canHom_comp {X Y Z : Scheme.{u}}
    (A : SheafGradedAlgebra.{u} Y) (ι : X ⟶ (relativeProj A).scheme) (fX : X ⟶ Y)
    (hfX : fX = ι ≫ (relativeProj A).toBase) (c : Z ⟶ X) (ι' : Z ⟶ (relativeProj A).scheme)
    (hι' : c ≫ ι = ι') (fZ : Z ⟶ Y) (hfZ : c ≫ fX = fZ)
    (hfZ' : fZ = ι' ≫ (relativeProj A).toBase) (n : ℕ) {N : Z.Modules}
    (Θ' : (Scheme.Modules.pullback ι').obj ((GradedPowerMap.twD A).algebra.piece (n : ℤ)) ⟶ N)
    (Θ : (Scheme.Modules.pullback fZ).obj (A.piece (n : ℤ)) ⟶ N)
    (hΘ : pullbackAdjointPsi A ι' fZ hfZ' n ≫ Θ' = Θ) :
    (Scheme.Modules.pullback c).map (pullbackAdjointPsi A ι fX hfX n) ≫
        canHom c ι ι' hι' ((GradedPowerMap.twD A).algebra.piece (n : ℤ)) ≫ Θ' =
      canHom c fX fZ hfZ (A.piece (n : ℤ)) ≫ Θ := by
  subst hΘ
  have key := reassoc_of%
    pullback_map_pullbackAdjointPsi_comp_canHom A ι fX hfX c ι' hι' fZ hfZ hfZ' n
  exact key _

namespace GradedPowerMap

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f) (g : T ⟶ P.coveringOpen.toScheme) (hg : g ≫ P.coveringOpen.ι = 𝟙 T)

include hg in
/-- The base morphism factors through `r_w = g ≫ r` for a right inverse `g` of the inclusion
`ι : U(ψ) ⟶ T`. -/
theorem eq_comp_globalMorphism_comp_toBase :
    f = (g ≫ P.globalMorphism (relativeProj A)) ≫ (relativeProj A).toBase := by
  rw [Category.assoc, P.globalMorphism_comp_toBase]
  show f = g ≫ P.coveringOpen.ι ≫ f
  rw [← Category.assoc, hg, Category.id_comp]

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
