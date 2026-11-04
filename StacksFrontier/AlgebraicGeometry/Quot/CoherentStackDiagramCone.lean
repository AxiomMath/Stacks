module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDiagram
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcDescentTransitivity

/-!
# The descended object of a descent diagram for `Coh_{X/Y}`, and its cocone

Let `Δ` be a descent diagram for `Coh_{X/Y}` over a family `{fP l : P_l ⟶ U}`
(`AlgebraicGeometry.Space.CoherentDescentDiagram`), with its glued morphism `g : U ⟶ Y` and its
descent datum of modules relative to `{X_{P l} ⟶ X_U}`.  If that datum is isomorphic to the
canonical descent datum of a quasi-coherent `𝒪_{X_U}`-module `M` (Stacks 04W5) — which is what
Stacks 04W8 provides when the family is an fpqc covering — and `M` has the three properties of an
object of `Coh_{X/Y}`, then `(U, g, M)` is an object of `Coh_{X/Y}`, the components of the
isomorphism make morphisms `P l ⟶ (U, g, M)` over `fP l`, and these form a cocone: the two
composites out of the object over each pairwise fibre product agree.

## Main definitions

* `AlgebraicGeometry.Space.CoherentDescentDiagram.descended`: the object `(U, g, M)`.
* `AlgebraicGeometry.Space.CoherentDescentDiagram.coneMap`: the morphisms `P l ⟶ (U, g, M)`.

## Main results

* `AlgebraicGeometry.Space.CoherentDescentDiagram.coneMap_comm`: **the cocone condition.**

## References

* [Stacks Project, Tag 08KC](https://stacks.math.columbia.edu/tag/08KC)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

attribute [local instance] AlgebraicGeometry.Space.pointTopology

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent (pullbackComparison pair pairFst pairSnd pair_condition DescentDatum
  canonicalDescentDatum canonicalComparison)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CoherentDescentDiagram

variable {D : CoherentSituation B S hS} {U : BigFppfOver B S hS} {L : Type v}
  (Δ : CoherentDescentDiagram D U L)
  (g : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y)
  (hg : ∀ l, (schemeSpaceFunctor B S hS).map (Δ.fP l) ≫ g = (Δ.P l).T.hom)

/-- The identification of the pairwise fibre product of the base changes with the base change of
the object over the pairwise fibre product is an isomorphism: both are fibre products of the same
cospan. -/
instance isIso_pairLift (l m : L) : IsIso (Δ.pairLift g hg l m) := by
  let e := (AlgebraicSpaces.isPullback_fiberProduct B S hS (Δ.memberMap g hg l)
    (Δ.memberMap g hg m)).isoIsPullback _ _ (Δ.isPullback_pair g hg l m)
  have he : Δ.pairLift g hg l m = e.hom := by
    refine (Δ.isPullback_pair g hg l m).hom_ext ?_ ?_
    · rw [Δ.pairLift_fst g hg l m]
      simp [e]
    · rw [Δ.pairLift_snd g hg l m]
      simp [e]
  rw [he]
  infer_instance

variable (M : Modules.{u, u} B S hS (D.space (baseObject g)).1 (D.space (baseObject g)).2)
  (hM : M.IsQuasicoherentOnSite)
  (E : Δ.moduleDatum g hg ≅ canonicalDescentDatum B S hS Δ.member (Δ.memberMap g hg) M hM)

/-- **The descended object `(U, g, M)` of `Coh_{X/Y}`.** -/
abbrev descended (hfp : M.IsFinitePresentationOnSite)
    (hflat : IsFlatOver B S hS (D.space (baseObject g)).2 (D.projection (baseObject g)).hom M)
    (hprop : ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection (baseObject g)).hom)
      (hU : IsClosed (D.support (baseObject g) M)),
      IsProperOver B S hS (D.space (baseObject g)).2
        ((schemeSpaceFunctor B S hS).obj (baseObject g).left).2
        (D.projection (baseObject g)).hom hp (D.support (baseObject g) M) hU) :
    CoherentObject D where
  T := baseObject g
  F := M
  quasicoherent := hM
  finitePresentation := hfp
  flat := hflat
  properSupport := hprop

variable (hfp : M.IsFinitePresentationOnSite)
  (hflat : IsFlatOver B S hS (D.space (baseObject g)).2 (D.projection (baseObject g)).hom M)
  (hprop : ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection (baseObject g)).hom)
      (hU : IsClosed (D.support (baseObject g) M)),
      IsProperOver B S hS (D.space (baseObject g)).2
        ((schemeSpaceFunctor B S hS).obj (baseObject g).left).2
        (D.projection (baseObject g)).hom hp (D.support (baseObject g) M) hU)

/-- **The morphisms of the cocone**: `P l ⟶ (U, g, M)`, over `fP l`, with the inverse of the
component of the isomorphism of descent data as their module comparison. -/
def coneMap (l : L) : CoherentHom (Δ.P l) (descended g M hM hfp hflat hprop) where
  base := Δ.toBase g hg l
  fibre := (QuasiCoherentDescent.DescentDatum.appIso B S hS E l).inv
  isIso_fibre := Iso.isIso_inv _

/-- The base map of the morphism of the cocone `P l ⟶ (U, g, M)` is `Δ.toBase g hg l`. -/
@[simp]
theorem coneMap_base (l : L) : (Δ.coneMap g hg M hM E hfp hflat hprop l).base = Δ.toBase g hg l :=
  rfl

/-- The module comparison of a morphism of the cocone, as an isomorphism. -/
theorem asIso_coneMap_fibre (l : L) :
    asIso (Δ.coneMap g hg M hM E hfp hflat hprop l).fibre =
      (QuasiCoherentDescent.DescentDatum.appIso B S hS E l).symm :=
  Iso.ext rfl

/-- **The cocone condition.**  The two composites `Q l m ⟶ P l ⟶ (U, g, M)` and
`Q l m ⟶ P m ⟶ (U, g, M)` agree. -/
theorem coneMap_comm (l m : L) :
    (Δ.c l m).comp (Δ.coneMap g hg M hM E hfp hflat hprop l) =
      (Δ.e l m).comp (Δ.coneMap g hg M hM E hfp hflat hprop m) := by
  have hb : ((Δ.c l m).comp (Δ.coneMap g hg M hM E hfp hflat hprop l)).base =
      ((Δ.e l m).comp (Δ.coneMap g hg M hM E hfp hflat hprop m)).base :=
    Δ.c_comp_toBase g hg l m
  have hrx' : pairSnd B S hS Δ.member (Δ.memberMap g hg) l m ≫ Δ.memberMap g hg m =
      pairFst B S hS Δ.member (Δ.memberMap g hg) l m ≫ Δ.memberMap g hg l :=
    (pair_condition B S hS Δ.member (Δ.memberMap g hg) l m).symm
  have hk₁ : D.relativeMap (Δ.c l m).base ≫ Δ.memberMap g hg l =
      D.relativeMap ((Δ.c l m).comp (Δ.coneMap g hg M hM E hfp hflat hprop l)).base :=
    (CoherentSituation.relativeMap_comp D _ _).symm
  have hk₂ : D.relativeMap (Δ.e l m).base ≫ Δ.memberMap g hg m =
      D.relativeMap ((Δ.e l m).comp (Δ.coneMap g hg M hM E hfp hflat hprop m)).base :=
    (CoherentSituation.relativeMap_comp D _ _).symm
  have h₁ : Δ.pairLift g hg l m ≫
      D.relativeMap ((Δ.c l m).comp (Δ.coneMap g hg M hM E hfp hflat hprop l)).base =
        pairFst B S hS Δ.member (Δ.memberMap g hg) l m ≫ Δ.memberMap g hg l := by
    rw [← hk₁, ← Category.assoc, pairLift_fst]
  have h₂ : Δ.pairLift g hg l m ≫
      D.relativeMap ((Δ.e l m).comp (Δ.coneMap g hg M hM E hfp hflat hprop m)).base =
        pairFst B S hS Δ.member (Δ.memberMap g hg) l m ≫ Δ.memberMap g hg l := by
    rw [← hk₂, ← Category.assoc, pairLift_snd, hrx']
  refine CoherentHom.eq_of_spanIso_eq_refl _ _ hb (Δ.pairLift g hg l m) _ h₁ h₂ ?_
  rw [CoherentHom.spanIso_eq_spanIsoOf]
  have hnat := QuasiCoherentDescent.appIso_naturality B S hS E l m
  rw [QuasiCoherentDescent.canonicalDescentDatum_transition,
    QuasiCoherentDescent.canonicalComparison_eq_pullbackComparison B S hS _ _ _ _ _ _ rfl hrx'
      M] at hnat
  refine spanIsoOf_comp_eq_refl (D.relativeMap (Δ.c l m).base) (D.relativeMap (Δ.e l m).base)
    (asIso (Δ.c l m).fibre) (asIso (Δ.e l m).fibre) (Δ.memberMap g hg l) (Δ.memberMap g hg m)
    (QuasiCoherentDescent.DescentDatum.appIso B S hS E l).symm
    (QuasiCoherentDescent.DescentDatum.appIso B S hS E m).symm _ _ hk₁ hk₂ _ _ ?_ ?_
    (Δ.pairLift g hg l m) _ _ (Δ.pairLift_fst g hg l m) (Δ.pairLift_snd g hg l m) _ rfl hrx'
    h₁ h₂ ?_
  rotate_right
  · exact Iso.ext (congrArg Iso.hom hnat)
  all_goals
    rw [CoherentHom.asIso_comp_fibre, D.compComparison_app, asIso_coneMap_fibre]
    rfl

end CoherentDescentDiagram

end AlgebraicGeometry.Space

end
