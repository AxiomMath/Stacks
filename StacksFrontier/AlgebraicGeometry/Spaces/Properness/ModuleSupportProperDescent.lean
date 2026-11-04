module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ProperMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismsClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismsModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType

/-!
# Descending properness of the support of a module along a limit of bases

Stacks 08K2 says: in the situation of Stacks 084W, for `F₀` a quasi-coherent `𝒪_{X₀}`-module of
finite type and `f₀` locally of finite type, if the scheme-theoretic support of the pullback `F`
of `F₀` to the limit `X` is proper over `Y`, then the scheme-theoretic support of the pullback
`F_i` to `X_i` is proper over `Y_i` for some `i`. It is proved here.

The source's proof replaces `X₀` by the support of `F₀` and then transfers properness between the
replaced source and the support of the module on it, in both directions. Between the two
transfers stands Stacks 08K1 for the replaced situation,
`MorphismDescentSituation.exists_isProper_mapAt_of_siteContainsBaseChangeLimits`.

Write `W ⊂ X₀` for the reduced closed subspace on the support of `F₀` and `D'` for the situation
of Stacks 084W with `X₀` replaced by `W`, which is
`AlgebraicGeometry.Space.MorphismDescentSituation.restrictSource`. Then the point set of the
comparison morphism `W ×_{B₀} B_i ⟶ X_i` is the support of `F_i`, and likewise at the limit,
because the support of a pullback is the inverse image of the support (Stacks 07TZ part (3)) and
the comparison morphism is a base change of `W ⟶ X₀`. So `W ×_{B₀} B_i` is one of the closed
subspaces of `X_i` with set of points the support of `F_i`, and properness over `Y_i` of such a
subspace is equivalent to properness over `Y_i` of that set of points. That equivalence is
Stacks 0CZC, already available as
`AlgebraicGeometry.Space.isProper_reducedClosedSubspace_iff_exists` and
`AlgebraicGeometry.Space.exists_isProper_closedSubspace_iff_forall`, and it runs in both
directions with no separatedness or finite-type hypothesis.

The source speaks of the scheme-theoretic supports `Z ⊂ X` and `Z_i ⊂ X_i` of `F` and `F_i`
(Stacks 07U1). Their sets of points are the supports of `F` and `F_i` (Stacks 07U0, part (4)),
so by Stacks 0CZI properness over the target of each is properness of the support in the sense
of Stacks 0CZD; the argument above is run in the latter form.

## Main results

* `exists_isProper_schemeTheoreticSupport_moduleAt_of_siteContainsBaseChangeLimits`:
  **Stacks 08K2**, under the convention of Section 70.2 (tag 07SD) and no other condition on
  the system of bases.
* `exists_isProperOver_supportOfSheaf_moduleAt_of_siteContainsBaseChangeLimits`
  and `MorphismDescentSituation.exists_isProperOver_supportOfSheaf_moduleAt`:
  the same with the scheme-theoretic supports replaced by the supports, in the sense of
  Stacks 0CZD, under the convention and under a bound on the index respectively.
* `AlgebraicGeometry.Space.isProper_schemeTheoreticSupport_iff_isProperOver`: Stacks 0CZI,
  (1) ⟺ (2), which passes between the two forms.
* `AlgebraicGeometry.Space.isProperOver_of_isProper_comp` and
  `AlgebraicGeometry.Space.isProper_comp_of_isProperOver`: Stacks 0CZC in the form where the
  closed subspace carrying the closed set is presented by a closed immersion into `X` rather
  than by a subfunctor.
* `AlgebraicGeometry.Space.MorphismDescentSituation.range_pointsMap_restrictSourceAtHom_support`
  and `…_restrictSourceLimitHom_support`: the point sets of the two comparison morphisms are the
  supports of `F_i` and of `F`.
* `AlgebraicGeometry.Space.MorphismDescentSituation.isProper_restrictSupport_mapLimit`: the
  hypothesis of Stacks 08K1, from the hypothesis of Stacks 08K2.
* `AlgebraicGeometry.Space.MorphismDescentSituation.isProperOver_supportOfSheaf_moduleAt`: the
  conclusion of Stacks 08K2 at a stage, from the conclusion of Stacks 08K1 at that stage.

Stacks 08K2 is the last two composed with Stacks 08K1 for the restricted situation
`AlgebraicGeometry.Space.MorphismDescentSituation.restrictSupport`, whose morphism over the
distinguished stage stays locally of finite type by
`AlgebraicGeometry.Space.MorphismDescentSituation.isLocallyOfFiniteType_restrictSupport_map₀`.

## Implementation notes

The closed subspace is presented by a morphism `g : V ⟶ X` which is a closed immersion with
`Set.range |g| = T`, rather than by a subfunctor of `X`, because that is the form in which the
comparison morphisms of
`AlgebraicGeometry.Space.MorphismDescentSituation.restrictSource` arrive — they are base changes
of `W ⟶ X₀`, not inclusions of subfunctors. Internally the subfunctor is
`CategoryTheory.Subfunctor.range g`, which is a closed subspace by
`AlgebraicGeometry.Space.isClosedSubspace_range_of_isClosedImmersion` and has the same point set
by `AlgebraicGeometry.Space.range_pointsMap_ι_range`, and `V` is identified with it by
`AlgebraicGeometry.Space.rangeIsoOfMono`; an isomorphism is proper, so properness transfers both
ways.

The intermediate lemmas carry the hypotheses that the morphisms to the targets are locally of
finite type explicitly rather than deriving them from `f₀`: they are part of the data of
Stacks 0CZD, which is only defined for a morphism locally of finite type, not extra
assumptions. Stacks 08K2 itself assumes only that `f₀` is locally of finite type, as its source
does, and supplies those data from it through
`AlgebraicGeometry.Space.MorphismDescentSituation.isLocallyOfFiniteType_mapLimit` and
`AlgebraicGeometry.Space.MorphismDescentSituation.isLocallyOfFiniteType_mapAt`, both base changes
of `f₀` being locally of finite type by Stacks 03XH.

The situation is `AlgebraicGeometry.Space.MorphismDescentSituation`, which places no condition
on the index. Section 70.2 of the source (tag 07SD) assumes throughout that every ring it
considers has its spectrum in the big fppf site; for the system of bases this is
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, the one hypothesis Stacks 08K2 takes
beyond those of its statement. The restricted situation has the same system of bases, so it
inherits the convention.

## References

* [Stacks Project, Tag 08K2](https://stacks.math.columbia.edu/tag/08K2)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 03XG](https://stacks.math.columbia.edu/tag/03XG)
* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
* [Stacks Project, Tag 0CZC](https://stacks.math.columbia.edu/tag/0CZC)
* [Stacks Project, Tag 0CZI](https://stacks.math.columbia.edu/tag/0CZI)
* [Stacks Project, Tag 07U0](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Tag 07U1](https://stacks.math.columbia.edu/tag/07U1)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Stacks 0CZC for a closed subspace presented by a closed immersion -/

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0CZC, from a closed immersion to the closed set.** A closed subset of `X` is proper
over `Y` as soon as it is the point set of a closed immersion `g : V ⟶ X` whose composite with
`X ⟶ Y` is proper. -/
theorem isProperOver_of_isProper_comp (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (T : Set (points B S hS X)) (hT : _root_.IsClosed T)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : V ⟶ X)
    (hV : IsAlgebraicSpace B S hS V) (hg : IsClosedImmersion B S hS g)
    (hrange : Set.range (pointsMap B S hS V g) = T)
    (hgproper : IsProper B S hS (g ≫ f)) :
    IsProperOver B S hS hX hY f hf T hT := by
  have _ : Mono g := mono_of_isClosedImmersion B S hS g hg
  refine (isProper_reducedClosedSubspace_iff_exists B S hS hX hY f hf T hT).2
    ⟨Subfunctor.range g, isClosedSubspace_range_of_isClosedImmersion B S hS g hV hg,
      (range_pointsMap_ι_range B S hS g).trans hrange, ?_⟩
  have he : (Subfunctor.range g).ι ≫ f = (rangeIsoOfMono B S hS g).inv ≫ g ≫ f := by
    rw [← Category.assoc, rangeIsoOfMono_inv_comp]
  rw [he]
  exact isProper_comp' B S hS _ _ hV hY (isProper_of_isIso B S hS _) hgproper

/-- **Stacks 0CZC, from the closed set to a closed immersion.** If a closed subset `T` of `X` is
proper over `Y` and `g : V ⟶ X` is a closed immersion with point set `T`, then `g ≫ f` is
proper.

Separatedness and finite type of `g ≫ f` are *not* hypotheses: Stacks 0CZC derives them, through
`AlgebraicGeometry.Space.isProper_ι_comp_of_isProper_ι_comp`, from surjectivity on points of the
factorization of the reduced subspace through `V`. -/
theorem isProper_comp_of_isProperOver (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (T : Set (points B S hS X)) (hT : _root_.IsClosed T)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : V ⟶ X)
    (hV : IsAlgebraicSpace B S hS V) (hg : IsClosedImmersion B S hS g)
    (hrange : Set.range (pointsMap B S hS V g) = T)
    (hproper : IsProperOver B S hS hX hY f hf T hT) :
    IsProper B S hS (g ≫ f) := by
  have _ : Mono g := mono_of_isClosedImmersion B S hS g hg
  have hZ : IsClosedSubspace B S hS (Subfunctor.range g) :=
    isClosedSubspace_range_of_isClosedImmersion B S hS g hV hg
  have hι : IsProper B S hS ((Subfunctor.range g).ι ≫ f) :=
    (exists_isProper_closedSubspace_iff_forall B S hS hX hY f hf T hT).1
      ((isProper_reducedClosedSubspace_iff_exists B S hS hX hY f hf T hT).1 hproper)
      (Subfunctor.range g) hZ ((range_pointsMap_ι_range B S hS g).trans hrange)
  have he : g ≫ f = (rangeIsoOfMono B S hS g).hom ≫ (Subfunctor.range g).ι ≫ f := by
    rw [← Category.assoc, rangeIsoOfMono_hom_ι]
  rw [he]
  exact isProper_comp' B S hS _ _ hZ.1 hY (isProper_of_isIso B S hS _) hι

end General

/-! ### Properness of the scheme-theoretic support -/

section SchemeTheoreticSupport

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CZI, (1) ⟺ (2).** For a quasi-coherent `𝒪_X`-module `F` of finite type and a
morphism `f : X ⟶ Y` locally of finite type, the scheme-theoretic support of `F` is proper over
`Y` exactly when the support of `F` is proper over `Y` in the sense of Stacks 0CZD.

The scheme-theoretic support is a closed subspace whose set of points is the support of `F`
(Stacks 07U0, part (4)), so this is Stacks 0CZC in the form above. -/
theorem isProper_schemeTheoreticSupport_iff_isProperOver (X Y : AlgebraicSpaces B S hS)
    (f : X.1 ⟶ Y.1) (hf : IsLocallyOfFiniteType B S hS f)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hFft : SheafOfModules.IsFiniteTypeOnSite F)
    (hcl : _root_.IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F))) :
    IsProper B S hS ((schemeTheoreticSupport B S hS X F).ι ≫ f) ↔
      IsProperOver B S hS X.2 Y.2 f hf
        (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)) hcl := by
  obtain ⟨hZ, -⟩ := exists_isClosedSubspace_schemeTheoreticSupport B S hS X F hF
    (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite F hFft)
  have hrange :=
    (supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B S hS X F hF hFft).symm
  exact ⟨isProperOver_of_isProper_comp B S hS X.2 Y.2 f hf _ hcl _ hZ.1 hZ.2 hrange,
    isProper_comp_of_isProperOver B S hS X.2 Y.2 f hf _ hcl _ hZ.1 hZ.2 hrange⟩

end SchemeTheoreticSupport

/-! ### The support of a module along a morphism descent system -/

/-- The point set of a base change of a map `g` is the inverse image of the point set of `g`. -/
private theorem range_pointsMap_eq_preimage_of_isPullback (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {P V A X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : P ⟶ A} {b : P ⟶ V}
    {f : A ⟶ X} {g : V ⟶ X} (sq : IsPullback a b f g) :
    Set.range (pointsMap B S hS P a) =
      pointsMap B S hS A f ⁻¹' Set.range (pointsMap B S hS V g) := by
  simpa only [Set.image_univ, Set.preimage_univ] using
    (preimage_image_pointsMap_of_isPullback B S hS sq.flip Set.univ).symm

namespace MorphismDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSituation B S hS hZ I)
  (F₀ : Modules.{u, u} B S hS D.source₀Space.1 D.source₀Space.2)

/-- **Stacks 07TZ, support_closed, for `F₀`.** The support of `F₀` is closed. -/
theorem isClosed_supportOfSheaf₀ (hft : SheafOfModules.IsFiniteTypeOnSite F₀) :
    _root_.IsClosed (supportOfSheaf B S hS D.source₀ ((SheafOfModules.toSheaf _).obj F₀)) := by
  have hft' : SheafOfModules.IsFiniteTypeOnSite
      (show Modules.{u, u} B S hS D.source₀ D.source₀_isAlgebraicSpace from F₀) := hft
  let := hft'
  exact isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS D.source₀
    D.source₀_isAlgebraicSpace
    (show Modules.{u, u} B S hS D.source₀ D.source₀_isAlgebraicSpace from F₀)

/-- The reduced closed subspace of `X₀` on the support of `F₀`. -/
def supportSubspace₀ (hft : SheafOfModules.IsFiniteTypeOnSite F₀) : Subfunctor D.source₀ :=
  reducedClosedSubspace B S hS D.source₀ D.source₀_isAlgebraicSpace
    (supportOfSheaf B S hS D.source₀ ((SheafOfModules.toSheaf _).obj F₀))
    (D.isClosed_supportOfSheaf₀ F₀ hft)

/-- The support subspace `W` is a closed subspace of `X₀`. -/
theorem isClosedSubspace_supportSubspace₀ (hft : SheafOfModules.IsFiniteTypeOnSite F₀) :
    IsClosedSubspace B S hS (D.supportSubspace₀ F₀ hft) :=
  isClosedSubspace_reducedClosedSubspace B S hS D.source₀ D.source₀_isAlgebraicSpace _ _

/-- The support subspace `W` is an algebraic space. -/
theorem supportSubspace₀_isAlgebraicSpace (hft : SheafOfModules.IsFiniteTypeOnSite F₀) :
    IsAlgebraicSpace B S hS (D.supportSubspace₀ F₀ hft).toFunctor :=
  (D.isClosedSubspace_supportSubspace₀ F₀ hft).1

/-- The inclusion `W ⟶ X₀` of the support subspace is a closed immersion. -/
theorem isClosedImmersion_supportSubspace₀_ι
    (hft : SheafOfModules.IsFiniteTypeOnSite F₀) :
    IsClosedImmersion B S hS (D.supportSubspace₀ F₀ hft).ι :=
  (D.isClosedSubspace_supportSubspace₀ F₀ hft).2

/-- The point set of the inclusion `W ⟶ X₀` is the support of `F₀`. -/
theorem range_pointsMap_supportSubspace₀_ι
    (hft : SheafOfModules.IsFiniteTypeOnSite F₀) :
    Set.range (pointsMap B S hS (D.supportSubspace₀ F₀ hft).toFunctor
        (D.supportSubspace₀ F₀ hft).ι) =
      supportOfSheaf B S hS D.source₀ ((SheafOfModules.toSheaf _).obj F₀) :=
  range_pointsMap_ι_reducedClosedSubspace B S hS D.source₀ D.source₀_isAlgebraicSpace _ _

/-- **The situation of Stacks 084W with `X₀` replaced by the support of `F₀`.** This is the
replacement with which the proof of Stacks 08K2 opens. -/
def restrictSupport (hft : SheafOfModules.IsFiniteTypeOnSite F₀) :
    MorphismDescentSituation B S hS hZ I :=
  D.restrictSource (D.supportSubspace₀ F₀ hft) (D.supportSubspace₀_isAlgebraicSpace F₀ hft)
    (D.isClosedImmersion_supportSubspace₀_ι F₀ hft)

/-- The comparison morphism `W ×_{B₀} B_i ⟶ X_i` of the replacement, at a stage. -/
def supportAtHom (hft : SheafOfModules.IsFiniteTypeOnSite F₀) (i : I) (hi : D.initial ≤ i) :
    (D.restrictSupport F₀ hft).sourceAt i hi ⟶ D.sourceAt i hi :=
  D.restrictSourceAtHom (D.supportSubspace₀ F₀ hft)
    (D.supportSubspace₀_isAlgebraicSpace F₀ hft)
    (D.isClosedImmersion_supportSubspace₀_ι F₀ hft) i hi

/-- The comparison morphism `W ×_{B₀} B ⟶ X` of the replacement, at the limit. -/
def supportLimitHom (hft : SheafOfModules.IsFiniteTypeOnSite F₀) :
    (D.restrictSupport F₀ hft).sourceLimit ⟶ D.sourceLimit :=
  D.restrictSourceLimitHom (D.supportSubspace₀ F₀ hft)
    (D.supportSubspace₀_isAlgebraicSpace F₀ hft)
    (D.isClosedImmersion_supportSubspace₀_ι F₀ hft)

/-- The comparison morphism `W ×_{B₀} B_i ⟶ X_i` is a closed immersion. -/
theorem isClosedImmersion_supportAtHom (hft : SheafOfModules.IsFiniteTypeOnSite F₀)
    (i : I) (hi : D.initial ≤ i) :
    IsClosedImmersion B S hS (D.supportAtHom F₀ hft i hi) :=
  D.isClosedImmersion_restrictSourceAtHom _ _ _ i hi

/-- The comparison morphism `W ×_{B₀} B ⟶ X` is a closed immersion. -/
theorem isClosedImmersion_supportLimitHom (hft : SheafOfModules.IsFiniteTypeOnSite F₀) :
    IsClosedImmersion B S hS (D.supportLimitHom F₀ hft) :=
  D.isClosedImmersion_restrictSourceLimitHom _ _ _

/-- The morphism of the restricted situation at a stage is the comparison morphism
`W ×_{B₀} B_i ⟶ X_i` followed by `f_i`. -/
theorem restrictSupport_mapAt (hft : SheafOfModules.IsFiniteTypeOnSite F₀)
    (i : I) (hi : D.initial ≤ i) :
    (D.restrictSupport F₀ hft).mapAt i hi = D.supportAtHom F₀ hft i hi ≫ D.mapAt i hi :=
  D.restrictSource_mapAt _ _ _ i hi

/-- The morphism of the restricted situation at the limit is the comparison morphism
`W ×_{B₀} B ⟶ X` followed by `f`. -/
theorem restrictSupport_mapLimit (hft : SheafOfModules.IsFiniteTypeOnSite F₀) :
    (D.restrictSupport F₀ hft).mapLimit = D.supportLimitHom F₀ hft ≫ D.mapLimit :=
  D.restrictSource_mapLimit _ _ _

/-- **The point set of the comparison morphism at a stage is the support of `F_i`.**

The comparison morphism is a base change of `W ⟶ X₀`, so its point set is the inverse image of
the point set of `W ⟶ X₀`, which is the support of `F₀`; and the inverse image of the support of
`F₀` is the support of `F_i` by part (3) of Stacks 07TZ. -/
theorem range_pointsMap_supportAtHom (hqc : F₀.IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite F₀) (i : I) (hi : D.initial ≤ i) :
    Set.range (pointsMap B S hS ((D.restrictSupport F₀ hft).sourceAt i hi)
        (D.supportAtHom F₀ hft i hi)) =
      supportOfSheaf B S hS (D.sourceAt i hi)
        ((SheafOfModules.toSheaf _).obj (D.moduleAt F₀ i hi)) := by
  rw [D.supportOfSheaf_moduleAt F₀ hqc hft i hi,
    ← D.range_pointsMap_supportSubspace₀_ι F₀ hft]
  exact range_pointsMap_eq_preimage_of_isPullback B S hS
    (D.restrictSourceAtHom_isPullback (D.supportSubspace₀ F₀ hft)
      (D.supportSubspace₀_isAlgebraicSpace F₀ hft)
      (D.isClosedImmersion_supportSubspace₀_ι F₀ hft) i hi)

/-- **The point set of the comparison morphism at the limit is the support of `F`.** -/
theorem range_pointsMap_supportLimitHom (hqc : F₀.IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite F₀) :
    Set.range (pointsMap B S hS (D.restrictSupport F₀ hft).sourceLimit
        (D.supportLimitHom F₀ hft)) =
      supportOfSheaf B S hS D.sourceLimit
        ((SheafOfModules.toSheaf _).obj (D.moduleLimit F₀)) := by
  rw [D.supportOfSheaf_moduleLimit F₀ hqc hft,
    ← D.range_pointsMap_supportSubspace₀_ι F₀ hft]
  exact range_pointsMap_eq_preimage_of_isPullback B S hS
    (D.restrictSourceLimitHom_isPullback (D.supportSubspace₀ F₀ hft)
      (D.supportSubspace₀_isAlgebraicSpace F₀ hft)
      (D.isClosedImmersion_supportSubspace₀_ι F₀ hft))

/-- **The hypothesis of Stacks 08K1 for the replaced situation, from the hypothesis of
Stacks 08K2.** If the support of `F` is proper over `Y`, then the restricted limit morphism
`W ×_{B₀} B ⟶ Y` is proper.

This is Stacks 0CZC: that morphism is a closed immersion with point set the support of `F`,
followed by `f`, and properness over `Y` of a closed subspace with a given point set depends only
on that point set. -/
theorem isProper_restrictSupport_mapLimit (hqc : F₀.IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite F₀)
    (hlft : IsLocallyOfFiniteType B S hS D.mapLimit)
    (hproper : IsProperOver B S hS D.sourceLimit_isAlgebraicSpace
      D.targetLimit_isAlgebraicSpace D.mapLimit hlft
      (supportOfSheaf B S hS D.sourceLimit
        ((SheafOfModules.toSheaf _).obj (D.moduleLimit F₀)))
      (D.isClosed_supportOfSheaf_moduleLimit F₀ hft)) :
    IsProper B S hS ((D.restrictSupport F₀ hft).mapLimit) := by
  rw [D.restrictSupport_mapLimit F₀ hft]
  exact isProper_comp_of_isProperOver B S hS D.sourceLimit_isAlgebraicSpace
    D.targetLimit_isAlgebraicSpace D.mapLimit hlft _ _ _
    ((D.restrictSupport F₀ hft).sourceLimit_isAlgebraicSpace)
    (D.isClosedImmersion_supportLimitHom F₀ hft)
    (D.range_pointsMap_supportLimitHom F₀ hqc hft) hproper

/-- **The conclusion of Stacks 08K2 at a stage, from the conclusion of Stacks 08K1 there.** If
the restricted morphism `W ×_{B₀} B_i ⟶ Y_i` is proper, then the support of `F_i` is proper over
`Y_i`. -/
theorem isProperOver_supportOfSheaf_moduleAt (hqc : F₀.IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite F₀) (i : I) (hi : D.initial ≤ i)
    (hlfti : IsLocallyOfFiniteType B S hS (D.mapAt i hi))
    (hproper : IsProper B S hS ((D.restrictSupport F₀ hft).mapAt i hi)) :
    IsProperOver B S hS (D.sourceAt_isAlgebraicSpace i hi)
      (D.targetAt_isAlgebraicSpace i hi) (D.mapAt i hi) hlfti
      (supportOfSheaf B S hS (D.sourceAt i hi)
        ((SheafOfModules.toSheaf _).obj (D.moduleAt F₀ i hi)))
      (D.isClosed_supportOfSheaf_moduleAt F₀ hft i hi) := by
  rw [D.restrictSupport_mapAt F₀ hft i hi] at hproper
  exact isProperOver_of_isProper_comp B S hS (D.sourceAt_isAlgebraicSpace i hi)
    (D.targetAt_isAlgebraicSpace i hi) (D.mapAt i hi) hlfti _ _ _
    ((D.restrictSupport F₀ hft).sourceAt_isAlgebraicSpace i hi)
    (D.isClosedImmersion_supportAtHom F₀ hft i hi)
    (D.range_pointsMap_supportAtHom F₀ hqc hft i hi) hproper

/-- A stage where the restricted morphism is proper is a stage where the support of `F_i` is proper
over `Y_i`. -/
private theorem exists_isProperOver_supportOfSheaf_moduleAt_of_exists_isProper
    (hqc : F₀.IsQuasicoherentOnSite) (hf₀ : IsLocallyOfFiniteType B S hS D.map₀)
    (hft : SheafOfModules.IsFiniteTypeOnSite F₀)
    (h : ∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS ((D.restrictSupport F₀ hft).mapAt i hi)) :
    ∃ (i : I) (hi : D.initial ≤ i),
      IsProperOver B S hS (D.sourceAt_isAlgebraicSpace i hi)
        (D.targetAt_isAlgebraicSpace i hi) (D.mapAt i hi)
        (D.isLocallyOfFiniteType_mapAt hf₀ i hi)
        (supportOfSheaf B S hS (D.sourceAt i hi)
          ((SheafOfModules.toSheaf _).obj (D.moduleAt F₀ i hi)))
        (D.isClosed_supportOfSheaf_moduleAt F₀ hft i hi) :=
  h.imp fun i hi => hi.imp fun hi hiproper => D.isProperOver_supportOfSheaf_moduleAt F₀ hqc hft i hi
    (D.isLocallyOfFiniteType_mapAt hf₀ i hi) hiproper

/-- **Stacks 03XG for the restricted morphism over the distinguished stage.** The inclusion of
the support of `F₀` is a closed immersion, hence locally of finite type, so composing it with
`f₀` leaves a morphism locally of finite type. -/
theorem isLocallyOfFiniteType_restrictSupport_map₀
    (hft : SheafOfModules.IsFiniteTypeOnSite F₀)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) :
    IsLocallyOfFiniteType B S hS (D.restrictSupport F₀ hft).map₀ :=
  D.isLocallyOfFiniteType_restrictSource_map₀ (D.supportSubspace₀ F₀ hft)
    (D.supportSubspace₀_isAlgebraicSpace F₀ hft)
    (D.isClosedImmersion_supportSubspace₀_ι F₀ hft) hf₀

/-- **Stacks 08K2.** In the situation of Stacks 084W, let `F₀` be a quasi-coherent
`𝒪_{X₀}`-module and let `F` and `F_i` be its pullbacks to `X` and to `X_i`. If `f₀` is locally
of finite type, `F₀` is of finite type and the scheme-theoretic support of `F` is proper over
`Y`, then the scheme-theoretic support of `F_i` is proper over `Y_i` for some stage `i`.

Replacing `X₀` by the support of `F₀` turns the hypothesis into properness of the restricted
morphism at the limit and the conclusion into properness over `Y_i` of the support of `F_i`,
both by Stacks 0CZC; Stacks 08K1 for the restricted situation produces the stage in between.

This form bounds the index by `hb : IsSiteSmall B S hS D.base`; the form
`exists_isProperOver_supportOfSheaf_moduleAt_of_siteContainsBaseChangeLimits` below asks only
the convention of Section 70.2 (tag 07SD) instead. -/
theorem exists_isProperOver_supportOfSheaf_moduleAt (hb : IsSiteSmall B S hS D.base)
    (hqc : F₀.IsQuasicoherentOnSite)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀)
    (hft : SheafOfModules.IsFiniteTypeOnSite F₀)
    (hproper : IsProperOver B S hS D.sourceLimit_isAlgebraicSpace
      D.targetLimit_isAlgebraicSpace D.mapLimit (D.isLocallyOfFiniteType_mapLimit hf₀)
      (supportOfSheaf B S hS D.sourceLimit
        ((SheafOfModules.toSheaf _).obj (D.moduleLimit F₀)))
      (D.isClosed_supportOfSheaf_moduleLimit F₀ hft)) :
    ∃ (i : I) (hi : D.initial ≤ i),
      IsProperOver B S hS (D.sourceAt_isAlgebraicSpace i hi)
        (D.targetAt_isAlgebraicSpace i hi) (D.mapAt i hi)
        (D.isLocallyOfFiniteType_mapAt hf₀ i hi)
        (supportOfSheaf B S hS (D.sourceAt i hi)
          ((SheafOfModules.toSheaf _).obj (D.moduleAt F₀ i hi)))
        (D.isClosed_supportOfSheaf_moduleAt F₀ hft i hi) := by
  exact D.exists_isProperOver_supportOfSheaf_moduleAt_of_exists_isProper F₀ hqc hf₀ hft
    ((D.restrictSupport F₀ hft).exists_isProper_mapAt hb
      (D.isProper_restrictSupport_mapLimit F₀ hqc hft
        (D.isLocallyOfFiniteType_mapLimit hf₀) hproper)
      (D.isLocallyOfFiniteType_restrictSupport_map₀ F₀ hft hf₀))

/-- **Stacks 08K2 for the support, under the chapter's convention.** In the situation of
Stacks 084W, if `f₀` is locally of finite type, `F₀` is quasi-coherent of finite type and the
support of `F` is proper over `Y`, then the support of `F_i` is proper over `Y_i` for some
stage `i`.

The proof is that of
`AlgebraicGeometry.Space.MorphismDescentSituation.exists_isProperOver_supportOfSheaf_moduleAt`,
with Stacks 08K1 for the restricted situation taken under the convention of Section 70.2
(tag 07SD), which the restricted situation inherits since its system of bases is that of `D`. -/
theorem exists_isProperOver_supportOfSheaf_moduleAt_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.base)
    (hqc : F₀.IsQuasicoherentOnSite)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀)
    (hft : SheafOfModules.IsFiniteTypeOnSite F₀)
    (hproper : IsProperOver B S hS D.sourceLimit_isAlgebraicSpace
      D.targetLimit_isAlgebraicSpace D.mapLimit (D.isLocallyOfFiniteType_mapLimit hf₀)
      (supportOfSheaf B S hS D.sourceLimit
        ((SheafOfModules.toSheaf _).obj (D.moduleLimit F₀)))
      (D.isClosed_supportOfSheaf_moduleLimit F₀ hft)) :
    ∃ (i : I) (hi : D.initial ≤ i),
      IsProperOver B S hS (D.sourceAt_isAlgebraicSpace i hi)
        (D.targetAt_isAlgebraicSpace i hi) (D.mapAt i hi)
        (D.isLocallyOfFiniteType_mapAt hf₀ i hi)
        (supportOfSheaf B S hS (D.sourceAt i hi)
          ((SheafOfModules.toSheaf _).obj (D.moduleAt F₀ i hi)))
        (D.isClosed_supportOfSheaf_moduleAt F₀ hft i hi) := by
  exact D.exists_isProperOver_supportOfSheaf_moduleAt_of_exists_isProper F₀ hqc hf₀ hft
    ((D.restrictSupport F₀ hft).exists_isProper_mapAt_of_siteContainsBaseChangeLimits hconv
      (D.isProper_restrictSupport_mapLimit F₀ hqc hft
        (D.isLocallyOfFiniteType_mapLimit hf₀) hproper)
      (D.isLocallyOfFiniteType_restrictSupport_map₀ F₀ hft hf₀))

/-- **Stacks 08K2.** In the situation of Stacks 084W, let `F₀` be a quasi-coherent
`𝒪_{X₀}`-module and let `F` and `F_i` be its pullbacks to `X` and to `X_i`. If `f₀` is locally
of finite type, `F₀` is of finite type and the scheme-theoretic support of `F` is proper over
`Y`, then the scheme-theoretic support of `F_i` is proper over `Y_i` for some stage `i`.

By Stacks 0CZI properness over the target of the scheme-theoretic support of a module of finite
type is properness of its support in the sense of Stacks 0CZD, which reduces the statement to
`exists_isProperOver_supportOfSheaf_moduleAt_of_siteContainsBaseChangeLimits`. The pullbacks
are quasi-coherent by Stacks 03GA and of finite type by Stacks 03DO. The hypothesis `hconv` is
the chapter's convention of Section 70.2 (tag 07SD); that it is a genuine hypothesis of the
chapter is witnessed, for Stacks 07SQ, by
`AlgebraicGeometry.Space.DescentSituation.not_forall_exists_isAffineSpace_system_obj`. -/
theorem exists_isProper_schemeTheoreticSupport_moduleAt_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.base)
    (hqc : F₀.IsQuasicoherentOnSite)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀)
    (hft : SheafOfModules.IsFiniteTypeOnSite F₀)
    (hproper : IsProper B S hS
      ((schemeTheoreticSupport B S hS D.sourceLimitSpace (D.moduleLimit F₀)).ι ≫ D.mapLimit)) :
    ∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS
      ((schemeTheoreticSupport B S hS (D.sourceAtSpace i hi) (D.moduleAt F₀ i hi)).ι ≫
        D.mapAt i hi) := by
  obtain ⟨i, hi, hiproper⟩ :=
    D.exists_isProperOver_supportOfSheaf_moduleAt_of_siteContainsBaseChangeLimits F₀ hconv hqc
      hf₀ hft ((isProper_schemeTheoreticSupport_iff_isProperOver B S hS D.sourceLimitSpace
        ⟨D.targetLimit, D.targetLimit_isAlgebraicSpace⟩ D.mapLimit
        (D.isLocallyOfFiniteType_mapLimit hf₀) (D.moduleLimit F₀)
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ F₀ hqc)
        (isFiniteTypeOnSite_modulePullback B S hS _ F₀ hft)
        (D.isClosed_supportOfSheaf_moduleLimit F₀ hft)).1 hproper)
  exact ⟨i, hi, (isProper_schemeTheoreticSupport_iff_isProperOver B S hS (D.sourceAtSpace i hi)
    ⟨D.targetAt i hi, D.targetAt_isAlgebraicSpace i hi⟩ (D.mapAt i hi)
    (D.isLocallyOfFiniteType_mapAt hf₀ i hi) (D.moduleAt F₀ i hi)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ F₀ hqc)
    (isFiniteTypeOnSite_modulePullback B S hS _ F₀ hft)
    (D.isClosed_supportOfSheaf_moduleAt F₀ hft i hi)).2 hiproper⟩

end MorphismDescentSituation

end AlgebraicGeometry.Space

end
