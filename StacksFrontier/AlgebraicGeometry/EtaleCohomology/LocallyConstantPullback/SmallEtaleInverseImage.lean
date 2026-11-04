module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SimultaneousStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.InverseImageFiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.BaseChangeFiber
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
import StacksCore.Tactic.StacksAttribute

/-!
# Finite local constancy is stable under small étale inverse image

Let `B` be a big étale site and `f : T ⟶ S` a morphism in it. Base change along `f` is a continuous
functor `S_ét ⥤ T_ét` of small étale sites, and the induced inverse image on sheaves is
`Functor.sheafPullback`. This file specializes
`Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafPullback_of_coverPreserving` — Tag 093R for
a morphism of sites, with arbitrary coefficients — to that functor, and feeds the result into
`AlgebraicGeometry.exists_stratification_isStratifiedSheaf_pair`, whose hypothesis `hPImmersion`
it discharges for `P` finite local constancy.

The specialization needs base change to be left exact and cover preserving. Left exactness is
`AlgebraicGeometry.preservesFiniteLimits_smallEtaleBaseChange`, which gives every finite limit
shape, and cover preservation is `AlgebraicGeometry.smallEtaleBaseChange_coverPreserving`; the
finality of `T / T` over `S / S` that left exactness gives is recorded below.

## Main results

* `AlgebraicGeometry.isFiniteLocallyConstant_smallEtaleSheafPullback_of_overPost` — **Tag 093R
  for small étale sites**: the inverse image of a finite locally constant sheaf along a morphism
  of small étale sites is finite locally constant, given that the pushforward along the slice of
  the base change is a right adjoint. Taken at `AddCommGrpCat` this is the statement about
  abelian sheaves that Tag 03RZ (2) needs.
  `AlgebraicGeometry.isFiniteLocallyConstant_smallEtaleSheafPullback` is the same conclusion
  reached through the slice equivalence instead, which asks nothing of the slice pushforward.
* `AlgebraicGeometry.isLocallyConstant_smallEtaleSheafPullback` — the same for local constancy.
* `AlgebraicGeometry.exists_stratification_isFiniteLocallyConstant_pair` — the simultaneous
  stratification of Tag 03RW for two finite locally constant sheaves, now unconditional: the
  hypothesis `hPImmersion` of
  `AlgebraicGeometry.exists_stratification_isStratifiedSheaf_pair` is supplied by the previous
  result, and the immersion hypothesis on the morphism is not needed.

## Implementation notes

Two instance arguments are carried rather than discharged, and both are *existence of an inverse
image*, not mathematics about local constancy:

* `(smallEtaleBaseChange B f).sheafPushforwardContinuous A _ _` is a right adjoint — this is the
  same hypothesis `AlgebraicGeometry.exists_stratification_isStratifiedSheaf_pair` already carries,
  at the same coefficient category;
* the pushforward along the slice `Over.post (smallEtaleBaseChange B f)` is a right adjoint — the
  same statement one slice down, which is where the localization square of Tag 093R lives.

For sheaves of sets both are theorems, by `AlgebraicGeometry.smallEtaleBaseChange_isMorphismOfSites`
and the small model of the site; for a general coefficient category the left adjoint is built from a
left Kan extension along the opposite functor, which needs the site to be literally small and not
merely essentially small, so the two are hypotheses here.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 021I](https://stacks.math.columbia.edu/tag/021I)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe wc w' w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-! ### Continuity on slices and finality of base change -/

/-- The slice of small étale base change at an object of the source site is continuous for the
two localized topologies. -/
public instance isContinuous_overPost_smallEtaleBaseChange {S T : B.Scheme} (f : T ⟶ S)
    (X : SmallEtale B S.obj S.property) :
    (Over.post (X := X) (smallEtaleBaseChange B f)).IsContinuous
      ((SmallEtale.topology B S.obj S.property).over X)
      ((SmallEtale.topology B T.obj T.property).over ((smallEtaleBaseChange B f).obj X)) :=
  Stacks.ConstantSheaf.isContinuous_overPost _ _ _ (smallEtaleBaseChange_coverPreserving B f) X

/-- Small étale base change carries the final object `S / S` to the final object `T / T`. -/
public def isTerminal_smallEtaleBaseChange_final {S T : B.Scheme} (f : T ⟶ S) :
    IsTerminal ((smallEtaleBaseChange B f).obj (SmallEtale.final B S.obj S.property)) :=
  (SmallEtale.finalIsTerminal B S.obj S.property).isTerminalObj _

/-! ### Sheafification on a localized small étale site -/

/-- Abelian-group-valued presheaves can be sheafified on the localization of the small étale site
of `S` at one of its objects, because that localization is again essentially small. This is
`AlgebraicGeometry.SmallEtale.hasSheafify` one slice down, and it is what the definition of (finite)
local constancy asks for.

It is stated for `AddCommGrpCat` rather than for an arbitrary concrete coefficient category: at the
latter generality the instances behind
`CategoryTheory.hasSheafifyEssentiallySmallSite` are not found inside the heartbeat budget, which is
the same obstruction recorded for the unsliced site in
`StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian`. -/
public noncomputable instance hasSheafifyOverSmallEtale (S : Scheme.{u}) (hS : B.Contains S)
    (U : SmallEtale B S hS) :
    HasSheafify ((SmallEtale.topology B S hS).over U) AddCommGrpCat.{u} :=
  letI : EssentiallySmall.{u} (Over U) := inferInstance
  hasSheafifyEssentiallySmallSite ((SmallEtale.topology B S hS).over U) AddCommGrpCat.{u}

/-! ### Tag 093R for small étale sites -/

section Pullback

variable {A : Type w} [Category.{w'} A] {S T : B.Scheme} (f : T ⟶ S)
  [∀ U : SmallEtale B S.obj S.property,
    HasWeakSheafify ((SmallEtale.topology B S.obj S.property).over U) A]
  [∀ V : SmallEtale B T.obj T.property,
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) A]
  [((smallEtaleBaseChange B f).sheafPushforwardContinuous A
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ X : SmallEtale B S.obj S.property,
    ((Over.post (X := X) (smallEtaleBaseChange B f)).sheafPushforwardContinuous A
      ((SmallEtale.topology B S.obj S.property).over X)
      ((SmallEtale.topology B T.obj T.property).over
        ((smallEtaleBaseChange B f).obj X))).IsRightAdjoint]

/-- **Tag 093R for small étale sites.** The inverse image of a locally constant sheaf along a
morphism of small étale sites is locally constant, for arbitrary coefficients. -/
@[stacks 095A "small étale inverse image"]
public theorem isLocallyConstant_smallEtaleSheafPullback
    (F : Sheaf (SmallEtale.topology B S.obj S.property) A)
    [Stacks.ConstantSheaf.IsLocallyConstant (SmallEtale.topology B S.obj S.property) F] :
    Stacks.ConstantSheaf.IsLocallyConstant (SmallEtale.topology B T.obj T.property)
      (((smallEtaleBaseChange B f).sheafPullback A
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).obj F) :=
  Stacks.ConstantSheaf.isLocallyConstant_sheafPullback _ _ A _
    (smallEtaleBaseChange_coverPreserving B f) F

/-- **Tag 093R for small étale sites.** The inverse image of a *finite* locally constant sheaf
along a morphism of small étale sites is finite locally constant, for arbitrary concrete
coefficients.

Taken at `AddCommGrpCat` this is the statement about abelian sheaves on which
`AlgebraicGeometry.exists_stratification_isStratifiedSheaf_pair` was conditional, and hence the
input that Tag 03RZ (2) needs. -/
public theorem isFiniteLocallyConstant_smallEtaleSheafPullback_of_overPost
    {FA : A → A → Type*} {CA : A → Type wc} [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)]
    [ConcreteCategory.{wc} A FA]
    (F : Sheaf (SmallEtale.topology B S.obj S.property) A)
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FA) (CD := CA)
      (SmallEtale.topology B S.obj S.property) F] :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FA) (CD := CA)
      (SmallEtale.topology B T.obj T.property)
      (((smallEtaleBaseChange B f).sheafPullback A
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).obj F) :=
  Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafPullback_of_coverPreserving _ _ A _
    (smallEtaleBaseChange_coverPreserving B f) F

/-- **Tag 093R for abelian sheaves on small étale sites.** The inverse image of a finite locally
constant sheaf of abelian groups along a morphism of small étale sites is finite locally constant.

This is the specialization of
`AlgebraicGeometry.isFiniteLocallyConstant_smallEtaleSheafPullback_of_overPost` at which the
sheafification hypotheses are discharged by `AlgebraicGeometry.hasSheafifyOverSmallEtale`, leaving
only the
existence of the two inverse images. It is the statement on which
`AlgebraicGeometry.exists_stratification_isStratifiedSheaf_pair` was conditional for abelian
coefficients, and hence the input Tag 03RZ (2) needs. -/
public theorem isFiniteLocallyConstant_smallEtaleSheafPullback_addCommGrp
    {S T : B.Scheme} (f : T ⟶ S)
    [((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ X : SmallEtale B S.obj S.property,
      ((Over.post (X := X) (smallEtaleBaseChange B f)).sheafPushforwardContinuous
        AddCommGrpCat.{u}
        ((SmallEtale.topology B S.obj S.property).over X)
        ((SmallEtale.topology B T.obj T.property).over
          ((smallEtaleBaseChange B f).obj X))).IsRightAdjoint]
    (F : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u})
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant
      (SmallEtale.topology B S.obj S.property) F] :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B T.obj T.property)
      (((smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{u}
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).obj F) :=
  isFiniteLocallyConstant_smallEtaleSheafPullback_of_overPost B f F

end Pullback

/-! ### The simultaneous stratification of Tag 03RW, unconditionally -/

section Stratification

variable {A : Type w} [Category.{w'} A] {FA : A → A → Type*} {CA : A → Type wc}
  [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{wc} A FA]
  [∀ (S : B.Scheme) (U : SmallEtale B S.obj S.property),
    HasWeakSheafify ((SmallEtale.topology B S.obj S.property).over U) A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S T : B.Scheme) (f : T ⟶ S) (X : SmallEtale B S.obj S.property),
    ((Over.post (X := X) (smallEtaleBaseChange B f)).sheafPushforwardContinuous A
      ((SmallEtale.topology B S.obj S.property).over X)
      ((SmallEtale.topology B T.obj T.property).over
        ((smallEtaleBaseChange B f).obj X))).IsRightAdjoint]

/-- Finite local constancy, as a condition on sheaves on the small étale site of each scheme of
the big étale site. This is the `P` of
`AlgebraicGeometry.exists_stratification_isStratifiedSheaf_pair` for which Tag 03RW asserts the
first part. -/
public abbrev isFiniteLocallyConstantSmallEtale :
    ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) A → Prop :=
  fun T => Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FA) (CD := CA)
    (SmallEtale.topology B T.obj T.property)

/-- **Two finite locally constant stratified sheaves are stratified on one stratification**, with
no further hypothesis.

`AlgebraicGeometry.exists_stratification_isStratifiedSheaf_pair` is conditional on the stability of
the stratum condition under inverse image along an immersion; for finite local constancy that is
`AlgebraicGeometry.isFiniteLocallyConstant_smallEtaleSheafPullback_of_overPost`, which holds for
an arbitrary morphism and so in particular for an immersion. This is the input with which every
comparison of two constructible sheaves of Tag 03RZ begins. -/
public theorem exists_stratification_isFiniteLocallyConstant_pair (X : B.Scheme)
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) A}
    (hF : IsStratifiedSheaf B X (isFiniteLocallyConstantSmallEtale B (FA := FA) (CA := CA)) F)
    (hG : IsStratifiedSheaf B X (isFiniteLocallyConstantSmallEtale B (FA := FA) (CA := CA)) G)
    (V : X.obj.affineOpens) :
    ∃ r : ConstructibleStratification B X V.1, ∀ k,
      isFiniteLocallyConstantSmallEtale B (FA := FA) (CA := CA) (r.piece k)
          (((smallEtaleBaseChange B (r.inclusion k)).sheafPullback A
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B (r.piece k).obj (r.piece k).property)).obj F) ∧
        isFiniteLocallyConstantSmallEtale B (FA := FA) (CA := CA) (r.piece k)
          (((smallEtaleBaseChange B (r.inclusion k)).sheafPullback A
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B (r.piece k).obj (r.piece k).property)).obj G) := by
  refine exists_stratification_isStratifiedSheaf_pair B X _ ?_ ?_ hF hG V
  · intro T F' G' e h
    have := h
    exact Stacks.ConstantSheaf.isFiniteLocallyConstant_congr
      (SmallEtale.topology B T.obj T.property) e
  · intro _ _ g _ G' h
    have := h
    exact isFiniteLocallyConstant_smallEtaleSheafPullback_of_overPost B g G'

end Stratification

end AlgebraicGeometry

end
