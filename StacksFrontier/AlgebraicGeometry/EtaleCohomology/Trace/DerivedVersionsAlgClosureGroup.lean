module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DerivedVersionsAlgClosureComparison
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricGaloisProjectionAlgClosure
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.UniversalHomeomorphismEquivalence
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.PurelyInseparableField
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.KernelInvariantsGroupIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationStalkReduction
public import Mathlib.RingTheory.Etale.Field
import StacksCore.Tactic.StacksAttribute

/-!
# The group side of the derived versions of Tag 03VM over an arbitrary field

Let `k` be a field, `k̄` an algebraic closure, `k'` the perfect closure of `k` in `k̄`,
`X` a geometrically connected smooth curve over `k` and `X' = X ×_k k'`. This file shows that the
group-theoretic objects of the derived versions of [Stacks, Tag 03VM], computed on `X'` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/DerivedVersionsAlgClosure.lean`, are the ones
defined directly from `X` over `k`:

* `π₁(X', η̄') ⟶ π₁(X, η̄)` is an isomorphism of topological groups (topological invariance of
  the fundamental group, Tag 0BQN, `X' ⟶ X` being a universal homeomorphism);
* under it and `Aut(k̄/k') = Aut(k̄/k)`, the projection `π₁(X') ⟶ Aut(k̄/k')` of the fundamental
  exact sequence of `X'` over `k'` is the projection `π₁(X) ⟶ Aut(k̄/k)` of `X` over `k`
  (`AlgebraicGeometry.perfectClosureAlgEquiv_geometricGaloisProjection`): both are read off the
  action on the `k̄`-points of the finite étale `k`-schemes `Spec k(a)`, `a` separable;
* hence `RH⁰(π₁(X_{k̄}), M)` with its residual `Aut(k̄/k)`-action, for the extension
  `π₁(X) ⟶ Aut(k̄/k)` of `X` over `k`, is the object computed on `X'`
  (`AlgebraicGeometry.geometricGaloisDerivedInvariantsOfAlgClosureIso`).

The sixth assertion of 03VM with its Galois action is then stated with this group side
(`AlgebraicGeometry.geometricGaloisDerivedKernelInvariantsIsoOfAlgClosure`).

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
* [Stacks Project, Tag 0BQN](https://stacks.math.columbia.edu/tag/0BQN)
* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IntermediateField
open Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- **The maps of fundamental groups along a commutative square act compatibly on fibres.** For
`g ≫ f = f' ≫ s`, a point `x'` of `X'`, `γ' ∈ π₁(X', x')` and a finite étale cover `V` of `S`, the
image of `γ'` in `π₁(S, f(g(x')))` acts on the fibre of `V` as the image of `γ'` in
`π₁(S', f'(x'))` acts on the fibre of `V ×_S S'`, followed by the projection to `V`. -/
theorem etaleFundamentalGroupMap_app_fst_of_comm {X X' S S' : Scheme.{u}} [ConnectedSpace X]
    [ConnectedSpace X'] [ConnectedSpace S] [ConnectedSpace S'] (f : X ⟶ S) (g : X' ⟶ X)
    (f' : X' ⟶ S') (s : S' ⟶ S) (w : g ≫ f = f' ≫ s) (x' : GeometricPoint X')
    (γ' : EtaleFundamentalGroup X' x') (V : FiniteEtaleOver S)
    (q : finiteEtaleFiber ((x'.map g).map f) V)
    (q' : finiteEtaleFiber (x'.map f') ((finiteEtaleBaseChange s).obj V))
    (hq : q'.1 ≫ pullback.fst V.hom s = q.1) :
    (((etaleFundamentalGroupMap f (x'.map g) (etaleFundamentalGroupMap g x' γ')).asIso.app V).hom
        q).1 =
      (((etaleFundamentalGroupMap f' x' γ').asIso.app ((finiteEtaleBaseChange s).obj V)).hom q').1 ≫
        pullback.fst V.hom s := by
  let W := (finiteEtaleBaseChange f).obj V
  let W' := (finiteEtaleBaseChange s).obj V
  have h1 : pullback.fst V.hom f ≫ V.hom = W.hom ≫ f := pullback.condition
  have h2 : pullback.fst W.hom g ≫ W.hom = pullback.snd W.hom g ≫ g := pullback.condition
  have hc : (pullback.fst W.hom g ≫ pullback.fst V.hom f) ≫ V.hom =
      (pullback.snd W.hom g ≫ f') ≫ s :=
    calc (pullback.fst W.hom g ≫ pullback.fst V.hom f) ≫ V.hom
        = pullback.fst W.hom g ≫ (pullback.fst V.hom f ≫ V.hom) := Category.assoc _ _ _
      _ = pullback.fst W.hom g ≫ (W.hom ≫ f) := congrArg (pullback.fst W.hom g ≫ ·) h1
      _ = (pullback.fst W.hom g ≫ W.hom) ≫ f := (Category.assoc _ _ _).symm
      _ = (pullback.snd W.hom g ≫ g) ≫ f := congrArg (· ≫ f) h2
      _ = pullback.snd W.hom g ≫ (g ≫ f) := Category.assoc _ _ _
      _ = pullback.snd W.hom g ≫ (f' ≫ s) := congrArg (pullback.snd W.hom g ≫ ·) w
      _ = (pullback.snd W.hom g ≫ f') ≫ s := (Category.assoc _ _ _).symm
  let inner : pullback W.hom g ⟶ W'.left := pullback.lift _ _ hc
  have hinner₁ : inner ≫ pullback.fst V.hom s = pullback.fst W.hom g ≫ pullback.fst V.hom f :=
    pullback.lift_fst _ _ _
  have hinner₂ : inner ≫ W'.hom = pullback.snd W.hom g ≫ f' := pullback.lift_snd _ _ _
  let cl : pullback W.hom g ⟶ pullback W'.hom f' :=
    pullback.lift inner (pullback.snd W.hom g) hinner₂
  have hcl₁ : cl ≫ pullback.fst W'.hom f' = inner := pullback.lift_fst _ _ _
  let c : (finiteEtaleBaseChange g).obj W ⟶ (finiteEtaleBaseChange f').obj W' :=
    MorphismProperty.Over.homMk cl (pullback.lift_snd _ _ _)
  have hcl : cl ≫ pullback.fst W'.hom f' ≫ pullback.fst V.hom s =
      pullback.fst W.hom g ≫ pullback.fst V.hom f :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst V.hom s) hcl₁).trans hinner₁)
  have hcl' : cl ≫ pullback.fst W'.hom f' ≫ W'.hom = pullback.snd W.hom g ≫ f' :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ W'.hom) hcl₁).trans hinner₂)
  let r₀ := (finiteEtaleFiberProjectionEquiv g x' W).symm
    ((finiteEtaleFiberProjectionEquiv f (x'.map g) V).symm q)
  let r₁ := (finiteEtaleFiberProjectionEquiv f' x' W').symm q'
  have hr₀₁ : r₀.1 ≫ pullback.fst W.hom g =
      ((finiteEtaleFiberProjectionEquiv f (x'.map g) V).symm q).1 :=
    pullback.lift_fst _ _ _
  have hr₀₂ : r₀.1 ≫ pullback.snd W.hom g = x'.hom := pullback.lift_snd _ _ _
  have hq₁ : ((finiteEtaleFiberProjectionEquiv f (x'.map g) V).symm q).1 ≫ pullback.fst V.hom f =
      q.1 := pullback.lift_fst _ _ _
  have hr : (finiteEtaleFiberFunctor x').map c r₀ = r₁ := by
    apply (finiteEtaleFiberProjectionEquiv f' x' W').injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    change (r₀.1 ≫ cl) ≫ pullback.fst W'.hom f' = q'.1
    refine pullback.hom_ext ?_ ?_
    · calc ((r₀.1 ≫ cl) ≫ pullback.fst W'.hom f') ≫ pullback.fst V.hom s
          = r₀.1 ≫ (cl ≫ pullback.fst W'.hom f' ≫ pullback.fst V.hom s) :=
            (Category.assoc _ _ _).trans (Category.assoc _ _ _)
        _ = r₀.1 ≫ (pullback.fst W.hom g ≫ pullback.fst V.hom f) := congrArg (r₀.1 ≫ ·) hcl
        _ = (r₀.1 ≫ pullback.fst W.hom g) ≫ pullback.fst V.hom f := (Category.assoc _ _ _).symm
        _ = q.1 := (congrArg (· ≫ pullback.fst V.hom f) hr₀₁).trans hq₁
        _ = q'.1 ≫ pullback.fst V.hom s := hq.symm
    · calc ((r₀.1 ≫ cl) ≫ pullback.fst W'.hom f') ≫ W'.hom
          = r₀.1 ≫ (cl ≫ pullback.fst W'.hom f' ≫ W'.hom) :=
            (Category.assoc _ _ _).trans (Category.assoc _ _ _)
        _ = r₀.1 ≫ (pullback.snd W.hom g ≫ f') := congrArg (r₀.1 ≫ ·) hcl'
        _ = (r₀.1 ≫ pullback.snd W.hom g) ≫ f' := (Category.assoc _ _ _).symm
        _ = x'.hom ≫ f' := congrArg (· ≫ f') hr₀₂
        _ = q'.1 ≫ W'.hom := q'.2.symm
  have hnat : (finiteEtaleFiberFunctor x').map c ((γ'.asIso.app _).hom r₀) =
      (γ'.asIso.app _).hom ((finiteEtaleFiberFunctor x').map c r₀) :=
    (congrArg (fun k ↦ k r₀) (γ'.asIso.hom.naturality c)).symm
  calc (((etaleFundamentalGroupMap f (x'.map g) (etaleFundamentalGroupMap g x' γ')).asIso.app V).hom
        q).1
      = (((γ'.asIso.app _).hom r₀).1 ≫ pullback.fst W.hom g) ≫ pullback.fst V.hom f := rfl
    _ = ((γ'.asIso.app _).hom r₀).1 ≫ cl ≫ pullback.fst W'.hom f' ≫ pullback.fst V.hom s :=
      (Category.assoc _ _ _).trans (congrArg (((γ'.asIso.app _).hom r₀).1 ≫ ·) hcl.symm)
    _ = ((finiteEtaleFiberFunctor x').map c ((γ'.asIso.app _).hom r₀)).1 ≫
          pullback.fst W'.hom f' ≫ pullback.fst V.hom s := (Category.assoc _ _ _).symm
    _ = ((γ'.asIso.app _).hom r₁).1 ≫ pullback.fst W'.hom f' ≫ pullback.fst V.hom s :=
      congrArg (fun z ↦ z.1 ≫ pullback.fst W'.hom f' ≫ pullback.fst V.hom s)
        (hnat.trans (congrArg _ hr))
    _ = (((etaleFundamentalGroupMap f' x' γ').asIso.app W').hom q').1 ≫ pullback.fst V.hom s :=
      (Category.assoc _ _ _).symm

/-- The same, with the base point `x = (residue field of x', h₀)` of `X` equal to `g(x')`. -/
theorem etaleFundamentalGroupMap_app_fst_of_comm_of_eq {X X' S S' : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace X'] [ConnectedSpace S] [ConnectedSpace S'] (f : X ⟶ S)
    (g : X' ⟶ X) (f' : X' ⟶ S') (s : S' ⟶ S) (w : g ≫ f = f' ≫ s) (x' : GeometricPoint X')
    (h₀ : x'.source ⟶ X) (h : x'.hom ≫ g = h₀)
    (hx : x'.map g = GeometricPoint.mk x'.residueField h₀) (γ' : EtaleFundamentalGroup X' x')
    (V : FiniteEtaleOver S) (q : finiteEtaleFiber ((GeometricPoint.mk x'.residueField h₀).map f) V)
    (q' : finiteEtaleFiber (x'.map f') ((finiteEtaleBaseChange s).obj V))
    (hq : q'.1 ≫ pullback.fst V.hom s = q.1) :
    (((etaleFundamentalGroupMap f (GeometricPoint.mk x'.residueField h₀)
        ((ContinuousMonoidHom.toContinuousMonoidHom
          (etaleFundamentalGroupContinuousMulEquivOfEq hx)).comp
          (etaleFundamentalGroupMap g x') γ')).asIso.app V).hom q).1 =
      (((etaleFundamentalGroupMap f' x' γ').asIso.app ((finiteEtaleBaseChange s).obj V)).hom q').1 ≫
        pullback.fst V.hom s := by
  subst h
  exact etaleFundamentalGroupMap_app_fst_of_comm f g f' s w x' γ' V q q' hq

section Cover

variable (k : Type u) [Field k] (L : Type u) [Field L] [Algebra k L] [Module.Finite k L]
  [Algebra.IsSeparable k L]

/-- The spectrum of a finite separable extension `L / k` as a finite étale cover of `Spec k`. -/
def finiteSeparableExtensionCover : FiniteEtaleOver (Spec (.of k)) :=
  MorphismProperty.Over.mk ⊤ (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    ⟨by
      rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
      exact RingHom.finite_algebraMap.mpr inferInstance,
    by
      rw [HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom]
      have : Algebra.FormallyEtale k L := Algebra.FormallyEtale.of_isSeparable k L
      have : Algebra.FinitePresentation k L := Algebra.FinitePresentation.of_finiteType.mp
        inferInstance
      exact RingHom.etale_algebraMap.mpr ⟨inferInstance, inferInstance⟩⟩

end Cover

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (K : Type u) [Field K] [Algebra k K]
  [IsAlgClosure k K] (y : GeometricPoint (fieldBaseChange (Over.mk f) K))

/-- `X' = X ×_k k' ⟶ X` is a universal homeomorphism, `k'/k` being purely inseparable. -/
instance universalHomeomorphism_perfectClosureModelProj :
    UniversalHomeomorphism (perfectClosureModelProj B X f K).hom :=
  ⟨(MorphismProperty.universally_isStableUnderBaseChange
      (topologically @IsHomeomorph)).of_isPullback
    (IsPullback.of_hasPullback (Over.mk f).hom
      (specAlgebraMap k (perfectClosure k K))).flip
    (universalHomeomorphism_specMap_algebraMap k (perfectClosure k K)).universally_isHomeomorph⟩

/-- **`π₁(X', η̄') ≅ π₁(X, η̄)`**, by topological invariance of the fundamental group (Tag 0BQN);
its underlying map is `AlgebraicGeometry.perfectClosureModelFundamentalGroupMap`. -/
def perfectClosureModelFundamentalGroupEquiv :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
      (perfectClosureModelHom B X f K)
    letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
    EtaleFundamentalGroup (perfectClosureModel B X f K).1
        ((perfectClosureModelPoint B X f K y).map
          (fieldBaseChangeObjProj B (perfectClosureModel B X f K) (perfectClosureModelHom B X f K)
            K (contains_fieldBaseChange_of_isCurve B _ _ K)).hom) ≃ₜ*
      EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f K
  letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
    (perfectClosureModelHom B X f K)
  letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
  (fundamentalGroupContinuousMulEquivOfUniversalHomeomorphism
      (perfectClosureModelProj B X f K).hom _).1.trans
    (etaleFundamentalGroupContinuousMulEquivOfEq (perfectClosureModelPoint_map_map B X f K y))

theorem perfectClosureModelFundamentalGroupEquiv_apply
    (γ' : letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
              (perfectClosureModelHom B X f K)
          letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
          EtaleFundamentalGroup (perfectClosureModel B X f K).1
        ((perfectClosureModelPoint B X f K y).map
          (fieldBaseChangeObjProj B (perfectClosureModel B X f K) (perfectClosureModelHom B X f K)
            K (contains_fieldBaseChange_of_isCurve B _ _ K)).hom)) :
    perfectClosureModelFundamentalGroupEquiv B X f K y γ' =
      perfectClosureModelFundamentalGroupMap B X f K y γ' := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f K
  let := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
    (perfectClosureModelHom B X f K)
  let := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
  change etaleFundamentalGroupContinuousMulEquivOfEq (perfectClosureModelPoint_map_map B X f K y)
      ((fundamentalGroupContinuousMulEquivOfUniversalHomeomorphism
        (perfectClosureModelProj B X f K).hom _).1 γ') =
    etaleFundamentalGroupContinuousMulEquivOfEq (perfectClosureModelPoint_map_map B X f K y)
      (etaleFundamentalGroupMap (perfectClosureModelProj B X f K).hom _ γ')
  rw [(fundamentalGroupContinuousMulEquivOfUniversalHomeomorphism
    (perfectClosureModelProj B X f K).hom _).2]

/-- `η̄' ⟶ X'_{k̄} ⟶ X' ⟶ X` is `η̄ ⟶ X_{k̄} ⟶ X`. -/
theorem perfectClosureModelPoint_hom_comp :
    ((perfectClosureModelPoint B X f K y).map
        (fieldBaseChangeObjProj B (perfectClosureModel B X f K) (perfectClosureModelHom B X f K)
          K (contains_fieldBaseChange_of_isCurve B _ _ K)).hom).hom ≫
        (perfectClosureModelProj B X f K).hom =
      y.hom ≫
        (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom := by
  change ((y.hom ≫ (fieldBaseChangeExtensionIso (Over.mk f) (perfectClosure k K) K).inv) ≫
      pullback.fst (extensionOver (Over.mk f) (perfectClosure k K)).hom
        (specAlgebraMap (perfectClosure k K) K)) ≫
      extensionProj (Over.mk f) (perfectClosure k K) =
    y.hom ≫ pullback.fst (Over.mk f).hom (specAlgebraMap k K)
  rw [Category.assoc, Category.assoc,
    ← fieldBaseChangeExtensionIso_hom_fst (Over.mk f) (perfectClosure k K) K, Iso.inv_hom_id_assoc]

omit [Smooth f] [GeometricallyConnected f] [IsAlgClosure k K] in
/-- The point `Spec Ω ⟶ Spec k̄` of `η̄'` is that of `η̄`. -/
theorem perfectClosureModel_geometricPointToSpec :
    geometricPointToSpec B (perfectClosureModel B X f K) (perfectClosureModelHom B X f K) K
        (perfectClosureModelPoint B X f K y) = geometricPointToSpec B X f K y := by
  change (y.hom ≫ (perfectClosureModelFibreIso B X f K).inv) ≫
      pullback.snd (Over.mk (perfectClosureModelHom B X f K)).hom
        (specAlgebraMap (perfectClosure k K) K) =
    y.hom ≫ pullback.snd (Over.mk f).hom (specAlgebraMap k K)
  rw [Category.assoc, ← fieldBaseChangeExtensionIso_hom_snd (Over.mk f) (perfectClosure k K) K,
    Iso.inv_hom_id_assoc]

/-- **The two projections act alike on the `k̄`-points of `Spec L`**, `L / k` finite separable
inside `k̄`: composed with `Spec L ⟵ Spec k̄`, the image of `γ'` in `Aut(k̄/k')` and the image of
the corresponding element of `π₁(X)` in `Aut(k̄/k)` give the same `Ω`-point of `Spec L`. -/
theorem perfectClosureModel_spec_comp_eq (L : IntermediateField k K) [FiniteDimensional k L]
    [Algebra.IsSeparable k L]
    (γ' : letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
              (perfectClosureModelHom B X f K)
          letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
          EtaleFundamentalGroup (perfectClosureModel B X f K).1
        ((perfectClosureModelPoint B X f K y).map
          (fieldBaseChangeObjProj B (perfectClosureModel B X f K) (perfectClosureModelHom B X f K)
            K (contains_fieldBaseChange_of_isCurve B _ _ K)).hom)) :
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    geometricPointToSpec B X f K y ≫
        Spec.map (CommRingCat.ofHom (geometricGaloisProjectionOfAlgClosure B X f K y
          (perfectClosureModelFundamentalGroupMap B X f K y γ')).toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap L K)) =
      geometricPointToSpec B X f K y ≫
        Spec.map (CommRingCat.ofHom (geometricGaloisProjection B (perfectClosureModel B X f K)
          (perfectClosureModelHom B X f K) K (perfectClosureModelPoint B X f K y)
            γ').toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap L K)) := by
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f K
  let := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
    (perfectClosureModelHom B X f K)
  let := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
  let Y := finiteSeparableExtensionCover k L
  let eY : Spec (.of K) ⟶ Y.left := Spec.map (CommRingCat.ofHom (algebraMap L K))
  have he : eY ≫ Y.hom = specAlgebraMap k K := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let s := specAlgebraMap k (perfectClosure k K)
  have hs : specAlgebraMap (perfectClosure k K) K ≫ s = specAlgebraMap k K :=
    specAlgebraMap_comp_specAlgebraMap (perfectClosure k K) K
  let eY' : Spec (.of K) ⟶ ((finiteEtaleBaseChange s).obj Y).left :=
    pullback.lift eY (specAlgebraMap (perfectClosure k K) K) (by rw [he, hs])
  let ζ := geometricPointToSpec B X f K y
  let ζ' := geometricPointToSpec B (perfectClosureModel B X f K)
    (perfectClosureModelHom B X f K) K (perfectClosureModelPoint B X f K y)
  have hζ : ζ' = ζ := perfectClosureModel_geometricPointToSpec B X f K y
  let p : finiteEtaleFiber ((y.map (fieldBaseChangeObjProj B X f K
      (contains_fieldBaseChange_of_isCurve B X f K)).hom).map f) Y :=
    ⟨ζ ≫ eY, (Category.assoc _ _ _).trans ((congrArg (ζ ≫ ·) he).trans
      (geometricPointToSpec_comp_specAlgebraMap B X f K y))⟩
  have hX := geometricQuotientGaloisEquiv_spec B X f K y
    (perfectClosureModelFundamentalGroupMap B X f K y γ') Y eY he p rfl
  let p' : finiteEtaleFiber ((perfectClosureModelPoint B X f K y).map
      ((fieldBaseChangeObjProj B (perfectClosureModel B X f K) (perfectClosureModelHom B X f K)
        K (contains_fieldBaseChange_of_isCurve B _ _ K)).hom) |>.map
        (perfectClosureModelHom B X f K)) ((finiteEtaleBaseChange s).obj Y) :=
    ⟨ζ' ≫ eY', (Category.assoc _ _ _).trans ((congrArg (ζ' ≫ ·)
      (pullback.lift_snd _ _ _ : eY' ≫ pullback.snd Y.hom s = _)).trans
      (geometricPointToSpec_comp_specAlgebraMap B (perfectClosureModel B X f K)
        (perfectClosureModelHom B X f K) K (perfectClosureModelPoint B X f K y)))⟩
  have hX' := geometricQuotientGaloisEquiv_spec B (perfectClosureModel B X f K)
    (perfectClosureModelHom B X f K) K (perfectClosureModelPoint B X f K y) γ'
    ((finiteEtaleBaseChange s).obj Y) eY' (pullback.lift_snd _ _ _) p' rfl
  have hw : (perfectClosureModelProj B X f K).hom ≫ f = perfectClosureModelHom B X f K ≫ s :=
    pullback.condition
  have hcomp := etaleFundamentalGroupMap_app_fst_of_comm_of_eq f
    (perfectClosureModelProj B X f K).hom (perfectClosureModelHom B X f K) s hw
    ((perfectClosureModelPoint B X f K y).map
      (fieldBaseChangeObjProj B (perfectClosureModel B X f K) (perfectClosureModelHom B X f K)
        K (contains_fieldBaseChange_of_isCurve B _ _ K)).hom)
    (y.hom ≫ (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)
    (perfectClosureModelPoint_hom_comp B X f K y)
    (perfectClosureModelPoint_map_map B X f K y) γ' Y p p'
    ((Category.assoc _ _ _).trans ((congrArg (ζ' ≫ ·)
      (pullback.lift_fst _ _ _ : eY' ≫ pullback.fst Y.hom s = eY)).trans
      (congrArg (· ≫ eY) hζ)))
  refine hX.symm.trans (hcomp.trans ?_)
  rw [hX']
  refine (Category.assoc _ _ _).trans ((congrArg (ζ' ≫ ·) (Category.assoc _ _ _)).trans ?_)
  rw [hζ]
  exact congrArg (fun t ↦ ζ ≫ Spec.map (CommRingCat.ofHom (geometricGaloisProjection B
      (perfectClosureModel B X f K) (perfectClosureModelHom B X f K) K
      (perfectClosureModelPoint B X f K y) γ').toAlgHom.toRingHom) ≫ t)
    (pullback.lift_fst _ _ _ : eY' ≫ pullback.fst Y.hom s = eY)

/-- Two ring endomorphisms of a field `K` agree on an intermediate field `L` as soon as they give
the same `Ω`-point of `Spec L` after a point `Spec Ω ⟶ Spec K`. -/
theorem eq_of_spec_comp_eq {k K Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k K]
    (L : IntermediateField k K) (ζ : CommRingCat.of K ⟶ CommRingCat.of Ω) (τ σ : K →+* K)
    (h : Spec.map ζ ≫ Spec.map (CommRingCat.ofHom τ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap L K)) =
      Spec.map ζ ≫ Spec.map (CommRingCat.ofHom σ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap L K)))
    {a : K} (ha : a ∈ L) : τ a = σ a := by
  have h' : Spec.map (CommRingCat.ofHom (algebraMap L K) ≫ CommRingCat.ofHom τ ≫ ζ) =
      Spec.map (CommRingCat.ofHom (algebraMap L K) ≫ CommRingCat.ofHom σ ≫ ζ) := by
    simpa only [Spec.map_comp, Category.assoc] using h
  have hring := congrArg (fun φ ↦ φ.hom ⟨a, ha⟩) (Spec.map_injective h')
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at hring
  exact ζ.hom.injective hring

/-- **The projection of `X'` over `k'` is the projection of `X` over `k`**: for
`γ' ∈ π₁(X', η̄')`, its image in `Aut(k̄/k') = Aut(k̄/k)` is the image in `Aut(k̄/k)` of the
corresponding element of `π₁(X, η̄)`. Both are determined by the action on the `k̄`-points of the
finite étale `k`-schemes `Spec k(a)`, `a ∈ k^{sep}`, and the maps of fundamental groups along
`X' ⟶ X` and `Spec k' ⟶ Spec k` act compatibly on fibres. -/
theorem perfectClosureAlgEquiv_geometricGaloisProjection
    (γ' : letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
              (perfectClosureModelHom B X f K)
          letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
          EtaleFundamentalGroup (perfectClosureModel B X f K).1
        ((perfectClosureModelPoint B X f K y).map
          (fieldBaseChangeObjProj B (perfectClosureModel B X f K) (perfectClosureModelHom B X f K)
            K (contains_fieldBaseChange_of_isCurve B _ _ K)).hom)) :
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    perfectClosureAlgEquivContinuousMulEquiv k K
        (geometricGaloisProjection B (perfectClosureModel B X f K)
          (perfectClosureModelHom B X f K) K (perfectClosureModelPoint B X f K y) γ') =
      geometricGaloisProjectionOfAlgClosure B X f K y
        (perfectClosureModelFundamentalGroupMap B X f K y γ') := by
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f K
  let := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
    (perfectClosureModelHom B X f K)
  let := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
  apply (separableClosureRestrictMulEquiv k K).injective
  refine AlgEquiv.ext fun a ↦ Subtype.ext ?_
  rw [separableClosureRestrictMulEquiv_apply_coe, separableClosureRestrictMulEquiv_apply_coe]
  let L := k⟮(a : K)⟯
  have : FiniteDimensional k L :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := k) (a : K))
  have : Algebra.IsSeparable k L := (isSeparable_adjoin_simple_iff_isSeparable k K).mpr a.2
  obtain ⟨ζr, hζr⟩ := Spec.map_surjective (geometricPointToSpec B X f K y)
  have h := perfectClosureModel_spec_comp_eq B X f K y L γ'
  rw [← hζr] at h
  exact (eq_of_spec_comp_eq L ζr _ _ h (mem_adjoin_simple_self k (a : K))).symm

variable (Λ : Type) [Ring Λ] [Finite Λ]

/-- **`M ↦ RH⁰(π₁(X_{k̄}, η̄), M)` over `k`**, in the bounded below derived category of discrete
`Λ`-modules with a continuous action of `Aut(k̄/k)`: the right derived functor of the invariants
under the kernel of the projection `π₁(X, η̄) ⟶ Aut(k̄/k)` of `X` over `k`
(`AlgebraicGeometry.geometricGaloisProjectionOfAlgClosure`), which is the image of
`π₁(X_{k̄}, η̄)`, with its residual action of `Aut(k̄/k)`. -/
def geometricGaloisDerivedInvariantsOfAlgClosure :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom)) ⥤
      DerivedCategory.Plus (GaloisModules Λ k K) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f K
  haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom)) ⋙
    DerivedCategory.Plus.singleFunctor _ 0 ⋙
    derivedKernelInvariants.{0, u + 1, u, 0} Λ (geometricGaloisProjectionOfAlgClosure B X f K y)
      (surjective_geometricGaloisProjectionOfAlgClosure B X f K y)

/-- **`RH⁰(π₁(X_{k̄}), M)` over `k` is the object computed on `X' = X ×_k k'`**, naturally in `M`:
`π₁(X') ≅ π₁(X)` and `Aut(k̄/k') = Aut(k̄/k)` carry the projection of `X'` to that of `X`
(`AlgebraicGeometry.perfectClosureAlgEquiv_geometricGaloisProjection`). -/
def geometricGaloisDerivedInvariantsOfAlgClosureIso :
    geometricGaloisDerivedInvariantsOfAlgClosure B X f K y Λ ≅
      perfectClosureGaloisDerivedInvariants B X f K y Λ :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f K
  letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
    (perfectClosureModelHom B X f K)
  letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
  haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  haveI := Stacks.ContinuousCohomology.additive_continuousModuleRes.{0, u + 1, 0} Λ
    (perfectClosureModelFundamentalGroupMap B X f K y)
  haveI := Stacks.ContinuousCohomology.preservesFiniteLimits_continuousModuleRes.{0, u + 1, 0} Λ
    (perfectClosureModelFundamentalGroupMap B X f K y)
  haveI := Stacks.ContinuousCohomology.preservesFiniteColimits_continuousModuleRes.{0, u + 1, 0} Λ
    (perfectClosureModelFundamentalGroupMap B X f K y)
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (derivedKernelInvariantsResIso Λ (perfectClosureModelFundamentalGroupMap B X f K y)
        (perfectClosureModelFundamentalGroupEquiv B X f K y)
        (perfectClosureModelFundamentalGroupEquiv_apply B X f K y)
        (perfectClosureAlgEquivContinuousMulEquiv k K).symm
        (geometricGaloisProjectionOfAlgClosure B X f K y)
        (geometricGaloisProjection B (perfectClosureModel B X f K)
          (perfectClosureModelHom B X f K) K (perfectClosureModelPoint B X f K y))
        (surjective_geometricGaloisProjectionOfAlgClosure B X f K y)
        (surjective_geometricGaloisProjection B (perfectClosureModel B X f K)
          (perfectClosureModelHom B X f K) K (perfectClosureModelPoint B X f K y))
        (fun γ' ↦ by
          rw [← perfectClosureAlgEquiv_geometricGaloisProjection B X f K y γ',
            ContinuousMulEquiv.symm_apply_apply]))) ≪≫
    Functor.isoWhiskerLeft _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.mapDerivedCategoryPlusSingleFunctorIso (continuousModuleRes.{0, u + 1, u + 1} Λ
            (perfectClosureModelFundamentalGroupMap B X f K y)) 0) _ ≪≫
        Functor.associator _ _ _)

/-- **Tag 03VM, the derived version of the cohomological half with its Galois action, over any
field, with the group side defined from `X` over `k`**: for a geometrically connected smooth curve
`X` over a field `k`, `k̄` an algebraic closure of `k`, `Λ` a finite ring with `#Λ` invertible in
`k`, and `X_{k̄} ≇ 𝐏¹_{k̄}`,

`RH⁰(π₁(X_{k̄}), M) ≅ RΓ^{Gal}(X_{k̄}, ℱ_ρ)`

in the bounded below derived category of discrete `Λ`-modules with a continuous action of
`Aut(k̄/k) = Gal(k^{sep}/k)`, naturally in the finite `Λ`-module `M` with continuous action `ρ`
of `π₁(X)`. The left side is the derived invariants under the kernel of the projection
`π₁(X, η̄) ⟶ Aut(k̄/k)` of `X` over `k`, i.e. under the image of `π₁(X_{k̄}, η̄)`. The right side
is computed on `X' = X ×_k k'`, `k'` the perfect closure of `k` in `k̄`; forgetting the action it
is `RΓ(X_{k̄}, ℱ_ρ|_{X_{k̄}})` of `X` itself
(`AlgebraicGeometry.perfectClosureGaloisDerivedSectionsForgetIso`). -/
@[stacks 03VM "sixth assertion (the derived version of the cohomological half) with the Galois \
action: `RH⁰(π₁(X_k̄, η̄), M) ≅ RΓ^{Gal}(X_k̄, ℱ_ρ)` in the derived category of discrete \
`Λ`-modules with continuous `Aut(k̄/k)`-action, natural in `(M, ρ)`, for an arbitrary base \
field `k`"]
def geometricGaloisDerivedKernelInvariantsIsoOfAlgClosure (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hP : ¬ ∃ e : fieldBaseChange (Over.mk f) K ≅ projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.snd (Over.mk f).hom (specAlgebraMap k K)) :
    geometricGaloisDerivedInvariantsOfAlgClosure B X f K y Λ ≅
      perfectClosureGaloisDerivedSections B X f K y Λ :=
  geometricGaloisDerivedInvariantsOfAlgClosureIso B X f K y Λ ≪≫
    geometricGaloisDerivedInvariantsIsoOfAlgClosure B X f K y Λ hΛ hP

end AlgebraicGeometry

end
