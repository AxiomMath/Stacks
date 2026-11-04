module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite

/-!
# The direct image along an affine quasi-finite morphism as a morphism of Quot functors

Let `B` be an algebraic space, let `π : X ⟶ Y` be an affine quasi-finite morphism of algebraic
spaces which are separated and of finite presentation over `B`, and let `F` be a quasi-coherent
`𝒪_X`-module.  Stacks 0DP1 asserts that `π_*` induces a morphism
`Quot_{F/X/B} ⟶ Quot_{π_*F/Y/B}`.

Write `G = π_*F`.  Over a test scheme `T` of `B` the base change `π_T : X_T ⟶ Y_T` is again
affine, so `G_T = π_{T,*}F_T` by Stacks 07U8 and `π_{T,*}` is exact; a quotient `F_T ⟶ Q` is
therefore carried to a quotient `G_T ⟶ π_{T,*}Q` of `G_T`.  The four conditions of Stacks 09TR
hold for `π_{T,*}Q` because they hold for `Q`, which is the morphism of stacks
`Coh_{X/B} ⟶ Coh_{Y/B}` of Stacks 0DN9.  Recording quotients by their kernels turns this into a
map `Quot_{F/X/B}(T) ⟶ Quot_{G/Y/B}(T)`, and its compatibility with pullback along a morphism of
test schemes makes the family of these maps a morphism of the Quot functors.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.IsQuotModule`: the four conditions of Stacks 09TR read
  on a module rather than on the subobject recording a quotient.
* `AlgebraicGeometry.Space.QuotPushforwardSituation`: **Stacks 0DP1, the standing data** — the
  affine quasi-finite morphism, the two structure morphisms to the base and the module.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.baseChangeOfMap`: the base change
  `π_T : X_T ⟶ Y_T`.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.sourceSituation` and
  `AlgebraicGeometry.Space.QuotPushforwardSituation.targetSituation`: the two quotient situations
  of Stacks 09TR, for `F/X/B` and for `G/Y/B`.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.PushforwardComparison`: the comparison
  `G_T ≅ π_{T,*}F_T` of Stacks 07U8, together with the exactness of `π_{T,*}`.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.pushforwardQuotient`: **the direct image of a
  quotient**, recorded — as the quotients themselves are — by its kernel.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.AffinePushforwardQuotInputs`: the inputs the
  morphism of Quot functors is built from, those of Stacks 07U8 and Stacks 0DN9.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.quotFunctorMap`: **Stacks 0DP1**, the induced
  morphism `Quot_{F/X/B} ⟶ Quot_{G/Y/B}`.

## Main results

* `AlgebraicGeometry.Space.QuotPushforwardSituation.isPullback_baseChangeOfMap`: `X_T` is the
  fibre product of `Y_T` and `X` over `Y`, so `π_T` really is a base change of `π`.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.pushforwardQuotientCokernelIso`: the quotient
  of `G_T` by the direct image of a quotient is the direct image `π_{T,*}(F_T/K)` of that
  quotient.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.pushforwardQuotient_mem`: **Stacks 0DP1**, the
  direct image of a member of `Quot_{F/X/B}(T)` is a member of `Quot_{G/Y/B}(T)`.

## Implementation notes

**The direct image of a quotient is a conjugation.**  `π_{T,*}` does not act on subobjects — it
need not preserve monomorphisms — but it does act on quotients, and the kernel of the image
quotient is read back off it.  That is exactly
`CategoryTheory.Functor.conjSubobject` for the comparison `G_T ≅ π_{T,*}F_T`, which is the shape
`AlgebraicGeometry.Space.QuotientSituation.quotientPullback` already uses for the inverse images.

**Four inputs are carried as hypotheses.**  The source's proof uses the base-change assertion of
Stacks 07U8, the exactness of the direct image along an affine morphism, and the morphism of
stacks `Coh_{X/B} ⟶ Coh_{Y/B}` of Stacks 0DN9; the fourth, the compatibility of `π_{T,*}` with
base change of the test scheme, is part (b) of the proof of Stacks 0DN9.  They are bundled as
`AlgebraicGeometry.Space.QuotPushforwardSituation.AffinePushforwardQuotInputs`, each field
naming the result it stands for.  The quasi-coherence of `G = π_*F`, which the target situation
needs, is *not* among them: it is Stacks 07U8 as proved here, from the affineness of `π`.

**The quotients live one universe up.**  A quotient is recorded by a subobject of `F_T`, so the
Quot functor takes values in `Type (u + 1)`, as in
`StacksFrontier/AlgebraicGeometry/Quot/QuotFunctorPresheaf.lean`; the morphism below is a morphism
of those functors on the test schemes over `B`.

## References

* [Stacks Project, Tag 0DP1](https://stacks.math.columbia.edu/tag/0DP1)
* [Stacks Project, Tag 0DN9](https://stacks.math.columbia.edu/tag/0DN9)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Quotients read on their quotient module -/

/-- The four conditions of Stacks 09TR on an `𝒪_{X_T}`-module itself, rather than on the
subobject of `F_T` recording a quotient: quasi-coherence, flatness over the test scheme, finite
presentation, and support proper over the test scheme. -/
def QuotSituation.IsQuotModule (D : QuotSituation B S hS) (T : SchemesOver D.Y)
    (Q : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) : Prop :=
  Q.IsQuasicoherentOnSite ∧
    IsFlatOver B S hS (D.space T).2 (D.projection T).hom Q ∧
      Q.IsFinitePresentationOnSite ∧ D.IsProperlySupportedOver T Q

/-- A subobject of `F_T` lies in `Quot_{F/X/B}(T)` exactly when the quotient of `F_T` by it
satisfies the four conditions of Stacks 09TR. -/
theorem QuotSituation.mem_properlySupportedQuotients_iff (D : QuotSituation B S hS)
    (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)) :
    K ∈ D.properlySupportedQuotients T ↔ D.IsQuotModule T (D.quotientModule T K) :=
  ⟨fun h => ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩, fun h => ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩⟩

/-- The four conditions of Stacks 09TR are invariant under an isomorphism of modules. -/
theorem QuotSituation.IsQuotModule.of_iso {D : QuotSituation B S hS} {T : SchemesOver D.Y}
    {Q Q' : Modules.{u, u} B S hS (D.space T).1 (D.space T).2} (e : Q ≅ Q')
    (h : D.IsQuotModule T Q) : D.IsQuotModule T Q' :=
  ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso e h.1,
    IsFlatOver.of_iso B S hS (D.space T).2 e h.2.1,
    SheafOfModules.IsFinitePresentationOnSite.of_iso e h.2.2.1,
    D.isProperlySupportedOver_of_iso e h.2.2.2⟩

/-! ### The standing data -/

/-- **Stacks 0DP1, the standing data.**  An affine quasi-finite morphism `π : X ⟶ Y` of algebraic
spaces which are separated and of finite presentation over an algebraic space `B`, together with
a quasi-coherent `𝒪_X`-module `F`: the data along which the direct image induces a morphism
`Quot_{F/X/B} ⟶ Quot_{π_*F/Y/B}`. -/
@[stacks 0DP1 "the standing data"]
structure QuotPushforwardSituation (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) where
  /-- The base algebraic space over which the two spaces live. -/
  base : AlgebraicSpaces B S hS
  /-- The source of the morphism, the space the module lives on. -/
  X : AlgebraicSpaces B S hS
  /-- The target of the morphism, the space the direct image lives on. -/
  Y : AlgebraicSpaces B S hS
  /-- The morphism `π : X ⟶ Y` along which the module is pushed forward. -/
  π : X ⟶ Y
  /-- The structure morphism of the source over the base. -/
  structureX : X ⟶ base
  /-- The structure morphism of the target over the base. -/
  structureY : Y ⟶ base
  /-- The morphism is a morphism over the base. -/
  comp : π ≫ structureY = structureX
  /-- The module on the source. -/
  F : Modules.{u, u} B S hS X.1 X.2
  /-- It is quasi-coherent (Stacks 03G9). -/
  quasicoherent : F.IsQuasicoherentOnSite
  /-- The morphism is affine. -/
  affine : IsAffineHom B S hS π.hom
  /-- The morphism is quasi-finite. -/
  quasiFinite : IsQuasiFinite B S hS π.hom
  /-- The source is separated over the base. -/
  separatedX : IsSeparated B S hS structureX.hom
  /-- The target is separated over the base. -/
  separatedY : IsSeparated B S hS structureY.hom
  /-- The source is of finite presentation over the base (Stacks 03XP). -/
  finitePresentationX : IsFinitePresentation B S hS structureX.hom
  /-- The target is of finite presentation over the base (Stacks 03XP). -/
  finitePresentationY : IsFinitePresentation B S hS structureY.hom

namespace QuotPushforwardSituation

variable (D : QuotPushforwardSituation B S hS)

/-! ### The two quotient situations -/

/-- The quotient situation `F/X/B` of Stacks 09TR, whose Quot functor is the source of the
morphism of Stacks 0DP1. -/
def sourceSituation : QuotSituation B S hS where
  X := D.X
  Y := D.base
  f := D.structureX
  F := D.F
  quasicoherent := D.quasicoherent
  finitePresentation := D.finitePresentationX

/-- The direct image `G = π_*F`, the module whose Quot functor is the target of the morphism of
Stacks 0DP1. -/
def pushforwardModule : Modules.{u, u} B S hS D.Y.1 D.Y.2 :=
  (modulePushforward B S hS D.π).obj D.F

/-- **Stacks 07U8 for the morphism of the situation**: the direct image `G = π_*F` along the
affine morphism `π` is quasi-coherent.

The hypothesis is the scheme-target case of that tag, which is what
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom` reduces it to. -/
theorem isQuasicoherentOnSite_pushforwardModule
    (h : SchemeTargetAffinePushforwardQuasicoherent B S hS) :
    D.pushforwardModule.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePushforward_of_isAffineHom B S hS h D.π D.affine D.F D.quasicoherent

/-- The quotient situation `G/Y/B` of Stacks 09TR for the direct image `G = π_*F`, whose Quot
functor is the target of the morphism of Stacks 0DP1. -/
def targetSituation (h : SchemeTargetAffinePushforwardQuasicoherent B S hS) :
    QuotSituation B S hS where
  X := D.Y
  Y := D.base
  f := D.structureY
  F := D.pushforwardModule
  quasicoherent := D.isQuasicoherentOnSite_pushforwardModule h
  finitePresentation := D.finitePresentationY

/-! ### The base change of the morphism -/

/-- The base change `π_T : X_T ⟶ Y_T` of the morphism of the situation to a test scheme `T` over
the base. -/
def baseChangeOfMap (T : SchemesOver D.base) :
    baseChangeSpace D.structureX T ⟶ baseChangeSpace D.structureY T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.structureY T.hom).lift
    (baseChangeProjection D.structureX T ≫ D.π) (baseChangeInclusion D.structureX T) (by
      rw [Category.assoc, D.comp]
      exact (AlgebraicSpaces.isPullback_fiberProduct B S hS D.structureX T.hom).w)

/-- The base change `π_T` followed by the projection `Y_T ⟶ Y` is the projection `X_T ⟶ X`
followed by `π`. -/
@[reassoc (attr := simp)]
theorem baseChangeOfMap_comp_projection (T : SchemesOver D.base) :
    D.baseChangeOfMap T ≫ baseChangeProjection D.structureY T =
      baseChangeProjection D.structureX T ≫ D.π :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.structureY T.hom).lift_fst _ _ _

/-- The base change `π_T` followed by the morphism `Y_T ⟶ T` is the morphism `X_T ⟶ T`. -/
@[reassoc (attr := simp)]
theorem baseChangeOfMap_comp_inclusion (T : SchemesOver D.base) :
    D.baseChangeOfMap T ≫ baseChangeInclusion D.structureY T =
      baseChangeInclusion D.structureX T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.structureY T.hom).lift_snd _ _ _

/-- The base change of the morphism over the base is a base change in the strict sense: `X_T` is
the fibre product of `Y_T` and `X` over `Y`. -/
theorem isPullback_baseChangeOfMap (T : SchemesOver D.base) :
    IsPullback (D.baseChangeOfMap T) (baseChangeProjection D.structureX T)
      (baseChangeProjection D.structureY T) D.π := by
  have outer : IsPullback (D.baseChangeOfMap T ≫ baseChangeInclusion D.structureY T)
      (baseChangeProjection D.structureX T) T.hom (D.π ≫ D.structureY) := by
    rw [D.baseChangeOfMap_comp_inclusion T, D.comp]
    exact (AlgebraicSpaces.isPullback_fiberProduct B S hS D.structureX T.hom).flip
  exact outer.of_right (D.baseChangeOfMap_comp_projection T)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.structureY T.hom).flip

/-! ### The comparison of the direct image with its base change -/

/-- **The base-change assertion of Stacks 07U8 for the situation, together with the exactness of
the direct image along an affine morphism**, carried as hypotheses.

The first field is the comparison `G_T ≅ π_{T,*}F_T` of the source's first step, stated at the
level of the functors `𝒪_X`-modules `⥤` `𝒪_{Y_T}`-modules so that it can be conjugated with.  The
second is the source's second step: `π_T` is affine, being a base change of the affine morphism
`π` by `AlgebraicGeometry.Space.QuotPushforwardSituation.isPullback_baseChangeOfMap`, hence
`π_{T,*}` is exact, and all that is used of that exactness is the preservation of
epimorphisms — which is what makes the direct image of a quotient a quotient. -/
structure PushforwardComparison (D : QuotPushforwardSituation B S hS) where
  /-- The comparison `G_T ≅ π_{T,*}F_T` of Stacks 07U8, as an isomorphism of functors. -/
  iso : ∀ T : SchemesOver D.base,
    modulePushforward B S hS D.π ⋙ modulePullback B S hS (baseChangeProjection D.structureY T) ≅
      modulePullback B S hS (baseChangeProjection D.structureX T) ⋙
        modulePushforward B S hS (D.baseChangeOfMap T)
  /-- The direct image along the affine morphism `π_T` preserves epimorphisms. -/
  preservesEpimorphisms : ∀ T : SchemesOver D.base,
    (modulePushforward B S hS (D.baseChangeOfMap T)).PreservesEpimorphisms

/-- **Stacks 0DP1, the direct image of a quotient.**  The quotient `G_T ⟶ π_{T,*}(F_T/K)` of
`G_T` obtained from a quotient `F_T ⟶ F_T/K` by applying `π_{T,*}` and reading the result through
the comparison `G_T ≅ π_{T,*}F_T`, recorded — as the quotients themselves are — by its kernel. -/
@[stacks 0DP1 "the direct image of a quotient, recorded by its kernel"]
def pushforwardQuotient (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (c : PushforwardComparison D) (T : SchemesOver D.base)
    (K : Subobject (D.sourceSituation.baseChangeModule T)) :
    Subobject ((D.targetSituation h).baseChangeModule T) :=
  Functor.conjSubobject (c.iso T) K

/-- The projection of `G_T` onto the direct image of a quotient of `F_T` is an epimorphism, so
the direct image of a quotient really is a quotient. -/
instance epi_conjQuotientProjection_pushforward (c : PushforwardComparison D)
    (T : SchemesOver D.base) (K : Subobject (D.sourceSituation.baseChangeModule T)) :
    Epi (Functor.conjQuotientProjection (c.iso T) K) :=
  have := c.preservesEpimorphisms T
  Functor.epi_conjQuotientProjection _ _

/-- **The quotient of `G_T` by the direct image of a quotient is the direct image of that
quotient**: the quotient of `G_T` by `pushforwardQuotient h c T K` is `π_{T,*}(F_T/K)`. -/
def pushforwardQuotientCokernelIso (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (c : PushforwardComparison D) (T : SchemesOver D.base)
    (K : Subobject (D.sourceSituation.baseChangeModule T)) :
    (D.targetSituation h).quotientModule T (D.pushforwardQuotient h c T K) ≅
      (modulePushforward B S hS (D.baseChangeOfMap T)).obj
        (D.sourceSituation.quotientModule T K) :=
  have := c.preservesEpimorphisms T
  Functor.conjSubobjectCokernelIso (c.iso T) K

/-! ### The inputs the morphism of Quot functors is built from -/

/-- **The inputs the morphism of Stacks 0DP1 is built from**, bundled: the base-change assertion
of Stacks 07U8 with the exactness of the direct image along an affine morphism, the morphism of
stacks `Coh_{X/B} ⟶ Coh_{Y/B}` of Stacks 0DN9, and the compatibility of the direct image with
base change of the test scheme, which is part (b) of the proof of Stacks 0DN9. -/
structure AffinePushforwardQuotInputs (D : QuotPushforwardSituation B S hS)
    (h : SchemeTargetAffinePushforwardQuasicoherent B S hS) where
  /-- The comparison of the direct image with its base change, and its exactness. -/
  comparison : PushforwardComparison D
  /-- **Stacks 0DN9 for the situation**: the direct image along `π_T` of a module satisfying the
  four conditions of Stacks 09TR over `T` again satisfies them.  This is the content of the
  morphism of stacks `Coh_{X/B} ⟶ Coh_{Y/B}` on objects. -/
  pushforwardMem : ∀ (T : SchemesOver D.base)
      (Q : Modules.{u, u} B S hS (D.sourceSituation.space T).1 (D.sourceSituation.space T).2),
    D.sourceSituation.IsQuotModule T Q →
      (D.targetSituation h).IsQuotModule T
        ((modulePushforward B S hS (D.baseChangeOfMap T)).obj Q)
  /-- **Part (b) of the proof of Stacks 0DN9 for the situation**: forming the direct image
  commutes with pullback along a morphism of test schemes, read on the kernels of the
  quotients. -/
  pushforwardQuotient_quotientPullback : ∀ {T' T : SchemesOver D.base} (m : T' ⟶ T)
      (K : Subobject (D.sourceSituation.baseChangeModule T)),
    D.pushforwardQuotient h comparison T' (D.sourceSituation.quotientPullback m K) =
      (D.targetSituation h).quotientPullback m (D.pushforwardQuotient h comparison T K)

/-! ### The morphism of Quot functors -/

/-- **Stacks 0DP1.**  The direct image of a quotient in `Quot_{F/X/B}(T)` lies in
`Quot_{G/Y/B}(T)`: the quotient of `G_T` by it is `π_{T,*}(F_T/K)`, which is quasi-coherent, of
finite presentation, flat over `T` and has support proper over `T` because `F_T/K` is, this being
the morphism of stacks `Coh_{X/B} ⟶ Coh_{Y/B}` of Stacks 0DN9. -/
@[stacks 0DP1 "the direct image of a quotient of the Quot functor is one"]
theorem pushforwardQuotient_mem (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (I : AffinePushforwardQuotInputs D h) (T : SchemesOver D.base)
    (K : Subobject (D.sourceSituation.baseChangeModule T))
    (hK : K ∈ D.sourceSituation.properlySupportedQuotients T) :
    D.pushforwardQuotient h I.comparison T K ∈
      (D.targetSituation h).properlySupportedQuotients T :=
  ((D.targetSituation h).mem_properlySupportedQuotients_iff T
      (D.pushforwardQuotient h I.comparison T K)).mpr
    (QuotSituation.IsQuotModule.of_iso
      (D.pushforwardQuotientCokernelIso h I.comparison T K).symm
      (I.pushforwardMem T (D.sourceSituation.quotientModule T K)
        ((D.sourceSituation.mem_properlySupportedQuotients_iff T K).mp hK)))

/-- **Stacks 0DP1.**  The morphism of Quot functors `Quot_{F/X/B} ⟶ Quot_{π_*F/Y/B}` induced by
the direct image: over a test scheme it sends a quotient `F_T ⟶ Q` to `G_T ⟶ π_{T,*}Q`.

Naturality is the compatibility of the direct image with pullback along a morphism of test
schemes, part (b) of the proof of Stacks 0DN9. -/
@[stacks 0DP1 "the induced morphism of Quot functors"]
def quotFunctorMap (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (I : AffinePushforwardQuotInputs D h) :
    D.sourceSituation.quotFunctor ⟶ (D.targetSituation h).quotFunctor where
  app T := ↾fun K ↦
    ⟨D.pushforwardQuotient h I.comparison T.unop K.1,
      D.pushforwardQuotient_mem h I T.unop K.1 K.2⟩
  naturality _ _ m := ConcreteCategory.hom_ext _ _ fun K ↦
    Subtype.ext (I.pushforwardQuotient_quotientPullback m.unop K.1)

end QuotPushforwardSituation

end AlgebraicGeometry.Space

end
