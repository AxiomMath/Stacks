module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDiagramCone
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsom
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ModuleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleCompFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupportFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses

/-!
# A descent diagram for `Coh_{X/Y}` over an fpqc covering has a cocone

Let `Δ` be a descent diagram for `Coh_{X/Y}` over a family `{fP l : P_l ⟶ U}`
(`AlgebraicGeometry.Space.CoherentDescentDiagram`) whose members form an fpqc covering.  This
file proves the effectivity step of the proof of Stacks 08KC.

The morphisms `X_{P l} ⟶ X_U` of base changes form an fpqc covering, so the descent datum of
modules of the diagram is effective (Stacks 04W8): it is isomorphic to the canonical descent
datum of a quasi-coherent `𝒪_{X_U}`-module `M`.  The three properties of an object of
`Coh_{X/Y}` descend to `M`:

* finite presentation, by Stacks 060V;
* flatness over `U`, pointwise, because each `X_{P l} ⟶ X_U` is flat and the points of `X_U` are
  covered by the points of the `X_{P l}` (Stacks 05VY), while flatness of the inverse images over
  `P l` gives flatness over `U` along the flat morphisms `P l ⟶ U` (Stacks 05VX);
* properness of the support over `U`, because the inverse image of the support is the support
  of the inverse image (Stacks 07TZ) and properness of a closed subset descends along an fpqc
  covering of the base (Stacks 0422).

So `(U, g, M)` is an object of `Coh_{X/Y}` receiving morphisms from the `P l` over the `fP l`,
and these form a cocone (`AlgebraicGeometry.Space.CoherentDescentDiagram.coneMap_comm`).

## Main results

* `AlgebraicGeometry.Space.CoherentDescentDiagram.isFpqcCovering_memberMap`: the morphisms of base
  changes form an fpqc covering.
* `AlgebraicGeometry.Space.CoherentDescentDiagram.isFinitePresentationOnSite_of_iso`,
  `.isFlatOver_of_iso`, `.properSupport_of_iso`: descent of the three properties.
* `AlgebraicGeometry.Space.CoherentDescentDiagram.exists_cocone`: **the cocone.**

## References

* [Stacks Project, Tag 08KC](https://stacks.math.columbia.edu/tag/08KC)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 060V](https://stacks.math.columbia.edu/tag/060V)
* [Stacks Project, Tag 05VY](https://stacks.math.columbia.edu/tag/05VY)
* [Stacks Project, Tag 0422](https://stacks.math.columbia.edu/tag/0422)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

attribute [local instance] AlgebraicGeometry.Space.pointTopology

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CoherentDescentDiagram

variable {D : CoherentSituation B S hS} {U : BigFppfOver B S hS} {L : Type v}
  (Δ : CoherentDescentDiagram D U L)
  (g : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y)
  (hg : ∀ l, (schemeSpaceFunctor B S hS).map (Δ.fP l) ≫ g = (Δ.P l).T.hom)
  (hcov : IsFpqcCovering B S hS fun l => ((schemeSpaceFunctor B S hS).map (Δ.fP l)).hom)

include hcov in
/-- **The morphisms `X_{P l} ⟶ X_U` of base changes form an fpqc covering.** -/
theorem isFpqcCovering_memberMap :
    IsFpqcCovering B S hS fun l => (Δ.memberMap g hg l).hom :=
  isFpqcCovering_baseChangeMap D.f (Δ.toBase g hg) hcov

variable (M : Modules.{u, u} B S hS (D.space (baseObject g)).1 (D.space (baseObject g)).2)
  (hM : M.IsQuasicoherentOnSite)
  (e : ∀ l, (modulePullback B S hS (Δ.memberMap g hg l)).obj M ≅ (Δ.P l).F)

include hcov hM e in
/-- **Finite presentation descends** (Stacks 060V). -/
theorem isFinitePresentationOnSite_of_iso : M.IsFinitePresentationOnSite := by
  have hfp : ∀ l, ((modulePullback B S hS (Δ.memberMap g hg l)).obj M).IsFinitePresentation :=
    fun l => Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso (e l).symm
      (SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' _
        (Δ.P l).finitePresentation)
  have := isFinitePresentation_of_pullback_fpqc B S hS Δ.member (Δ.memberMap g hg) M hM
    (Δ.isFpqcCovering_memberMap g hg hcov) hfp
  exact SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation M

include hcov hM e in
/-- **Flatness over the base descends** (Stacks 05VY, 05VX). -/
theorem isFlatOver_of_iso :
    IsFlatOver B S hS (D.space (baseObject g)).2 (D.projection (baseObject g)).hom M := by
  have := hM
  have hc := Δ.isFpqcCovering_memberMap g hg hcov
  refine isFlatOver_of_flat_covering B S hS Δ.member (Δ.memberMap g hg)
    (D.projection (baseObject g)) M (fun l => isFpqcCovering_flat B S hS hc l) ?_
    (fun l => (Δ.P l).F) e (fun l => ?_)
  · exact (isJointlySurjective_iff B S hS _ _).1
      (isJointlySurjective_of_isFpqcCovering B S hS _ hc)
  · have := (Δ.P l).quasicoherent
    have hw : Δ.memberMap g hg l ≫ D.projection (baseObject g) =
        D.projection (Δ.P l).T ≫ (schemeSpaceFunctor B S hS).map (Δ.fP l) :=
      baseChangeMap_comp_inclusion D.f (Δ.toBase g hg l)
    rw [hw]
    exact isFlatOver_comp_of_isFlat B S hS _ _ _ (Δ.P l).flat (isFpqcCovering_flat B S hS hcov l)

include hcov hM e in
/-- **Properness of the support over the base descends** (Stacks 07TZ, 0422). -/
theorem properSupport_of_iso (hfp : M.IsFinitePresentationOnSite) :
    ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection (baseObject g)).hom)
      (hU : IsClosed (D.support (baseObject g) M)),
      IsProperOver B S hS (D.space (baseObject g)).2
        ((schemeSpaceFunctor B S hS).obj (baseObject g).left).2
        (D.projection (baseObject g)).hom hp (D.support (baseObject g) M) hU := by
  have := hfp
  have hU : IsClosed (D.support (baseObject g) M) :=
    isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS _ (D.space (baseObject g)).2 M
  refine ⟨isLocallyOfFiniteType_projection D _, hU, ?_⟩
  refine isProperOver_of_isFpqcCovering B S hS (D.projection (baseObject g)) _
    (g' := Δ.memberMap g hg) (f' := fun l => D.projection (Δ.P l).T)
    (g := fun l => (schemeSpaceFunctor B S hS).map (Δ.fP l))
    (fun l => isPullback_baseChangeMap D.f (Δ.toBase g hg l)) hcov _ hU (fun l => ?_)
  have hset : pointsMap B S hS (Δ.member l).1 (Δ.memberMap g hg l).hom ⁻¹'
      D.support (baseObject g) M = D.support (Δ.P l).T (Δ.P l).F := by
    rw [← supportOfSheaf_modulePullback_eq B S hS _ M hM inferInstance]
    exact supportOfSheaf_eq_of_iso B S hS _ (e l)
  obtain ⟨hp, hUl, hpr⟩ := (Δ.P l).properSupport
  have key : ∀ (T : Set (points B S hS (Δ.member l).1)) (hT : IsClosed T),
      T = D.support (Δ.P l).T (Δ.P l).F →
        IsProperOver B S hS (Δ.member l).2
          ((schemeSpaceFunctor B S hS).obj (Δ.P l).T.left).2 (D.projection (Δ.P l).T).hom hp
          T hT := by
    rintro T hT rfl
    exact hpr
  exact key _ _ hset

/-- **A descent diagram over an fpqc covering has a cocone** in `Coh_{X/Y}`: an object `A` over
`U`, with morphisms `P l ⟶ A` over the members `fP l`, whose two composites out of each object
over a pairwise fibre product agree. -/
theorem exists_cocone
    (hsieve : Sieve.ofArrows (fun l => (Δ.P l).T.left) Δ.fP ∈ BigFppfOver.topology B S hS U)
    (hcov : IsFpqcCovering B S hS fun l => ((schemeSpaceFunctor B S hS).map (Δ.fP l)).hom) :
    ∃ (A : CoherentObject D) (hA : A.T.left = U) (ζ : ∀ l, CoherentHom (Δ.P l) A),
      (∀ l, (ζ l).base.left = Δ.fP l ≫ eqToHom hA.symm) ∧
        ∀ l m, (Δ.c l m).comp (ζ l) = (Δ.e l m).comp (ζ m) := by
  obtain ⟨g, hg⟩ := Δ.exists_baseMap hsieve
  obtain ⟨M, hM, ⟨E⟩⟩ := QuasiCoherentDescent.forall_isEffective_of_isFpqcCovering B S hS
    Δ.member (Δ.memberMap g hg) (Δ.isFpqcCovering_memberMap g hg hcov) (Δ.moduleDatum g hg)
  let e : ∀ l, (modulePullback B S hS (Δ.memberMap g hg l)).obj M ≅ (Δ.P l).F :=
    fun l => (QuasiCoherentDescent.DescentDatum.appIso B S hS E l).symm
  have hfp := Δ.isFinitePresentationOnSite_of_iso g hg hcov M hM e
  have hflat := Δ.isFlatOver_of_iso g hg hcov M hM e
  have hprop := Δ.properSupport_of_iso g hg hcov M hM e hfp
  refine ⟨descended g M hM hfp hflat hprop, rfl,
    fun l => Δ.coneMap g hg M hM E hfp hflat hprop l, fun l => ?_,
    fun l m => Δ.coneMap_comm g hg M hM E hfp hflat hprop l m⟩
  simp

end CoherentDescentDiagram

end AlgebraicGeometry.Space
