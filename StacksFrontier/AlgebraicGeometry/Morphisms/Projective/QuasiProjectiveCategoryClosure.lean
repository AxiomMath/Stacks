module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.Basic
public import StacksFrontier.AlgebraicGeometry.HProjective.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.BaseChange

/-!
# The category of quasi-projective schemes over a base with an ample invertible sheaf

For a scheme `S` carrying an ample invertible sheaf, `QP_S` is the full subcategory of the
category of schemes over `S` whose structure morphism satisfies the equivalent conditions of
[Stacks, Tag 0B42]. This file carries the closure properties of that category: base change,
composition, fibre products, and the criteria that put a quasi-affine of finite type, a
quasi-finite separated, or a quasi-compact immersion morphism into it. Clauses (4) and (5) are
proved in modules that this one does not contain; the sections below say where and why.

## Main definitions

* `AlgebraicGeometry.quasiProjectiveOver` and
  `AlgebraicGeometry.QuasiProjectiveSchemesOver`: the property, of a scheme over `S`, of being
  quasi-projective over `S`, and the full subcategory `QP_S` it cuts out.
* `AlgebraicGeometry.isLimitOverBinaryFan`: a binary product in `Over S` is a fibre product of
  the sources over `S`. This is what makes clause (3) a statement about the category.

## Main results

* `AlgebraicGeometry.QuasiProjectiveSchemesOver.baseChange`: **clause (1)**, base change along
  `S' ⟶ S` is a functor `QP_S ⥤ QP_{S'}`.
* `AlgebraicGeometry.isQuasiProjective_comp_of_exists_isAmple`: **clause (2)**, if `X ∈ QP_S` and
  `Y ∈ QP_X` then `Y ∈ QP_S`.
* `AlgebraicGeometry.isQuasiProjective_pullback_snd_comp` and
  `AlgebraicGeometry.quasiProjectiveOver_isClosedUnderBinaryProducts`: **clause (3)**, `QP_S` is
  closed under fibre products over `S`, as a statement about the structure morphism of the fibre
  product and as closure of the full subcategory under binary products.
* **Clause (4)**, closure under finite disjoint unions, is
  `AlgebraicGeometry.isQuasiProjective_sigmaDesc` in
  `StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveDisjointUnion`, which this
  file does not import; see the section "Clause (4)" below.
* **Clause (5)**, a projective morphism is in `QP_S`, is
  `AlgebraicGeometry.IsProjective.isQuasiProjective` in
  `StacksFrontier.AlgebraicGeometry.ProjectiveBundleProperFiniteType.Basic`, which carries the
  attribute for this clause as well as for [Stacks, Tag 07RL]; see the section "Clause (5)"
  below.
* `AlgebraicGeometry.isQuasiProjective_of_isQuasiAffineHom`: **clause (6)**, a quasi-affine
  morphism of finite type is in `QP_S`.
* `AlgebraicGeometry.isQuasiProjective_of_locallyQuasiFinite_of_isSeparated`: **clause (7)**, a
  quasi-finite separated morphism is in `QP_S`.
* `AlgebraicGeometry.isQuasiProjective_of_isImmersion`: **clause (8)**, a quasi-compact immersion
  is in `QP_S`.

## Membership in `QP_S`

Membership of `X` in `QP_S` is `AlgebraicGeometry.IsQuasiProjective X.hom`, which is condition
(1) of [Stacks, Tag 0B42] and the predicate of [Stacks, Tag 01VW] that this repository carries;
over a base with an ample invertible sheaf the other four conditions of Tag 0B42 are equivalent
to it, which is
`AlgebraicGeometry.isQuasiProjective_tfae_of_exists_isAmple`.

## Which clauses carry what

The source's hypothesis on `S` is that it carries an ample invertible sheaf, and it is written
out as the existential `hS` below rather than abbreviated, matching
`StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveOverAmpleBase`, which states
Tag 0B42 itself at exactly this shape.

* Clauses (1), (5), (6), (7) and (8) need **no hypothesis on the base at all** — the base change
  of a quasi-projective morphism is quasi-projective unconditionally by [Stacks, Tag 0B3G],
  a projective morphism is quasi-projective unconditionally by [Stacks, Tag 07RL], and
  quasi-affineness of finite type gives relative ampleness of `𝒪_X` unconditionally by
  [Stacks, Tag 0B3H]. In particular clause (1) does not use the hypothesis that `S'` carries an
  ample invertible sheaf either; it is kept out of the statement rather than assumed and
  discarded.
* Clauses (2) and (3) use exactly `CompactSpace S`, which an ample invertible sheaf on `S`
  provides. The source routes clause (2) through condition (4) of Tag 0B42; this file routes it
  instead through [Stacks, Tag 0C4M], `AlgebraicGeometry.IsQuasiProjective.comp`, which is
  already proved over a quasi-compact base and so costs nothing beyond the hypothesis, and
  clause (3) through clause (1) and clause (2) as the source does.
* Clause (5) needs **no hypothesis on the base** either, and is not in this file; see the
  section "Clause (5)" below.
* Clause (4), closure under finite disjoint unions, is proved in a module **above** this one,
  `StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveDisjointUnion`, because its
  proof consumes clauses (2) and (6) from this file; see the section "Clause (4)" below. It uses
  exactly the same hypothesis on the base as clauses (2) and (3), and for the same reason.

## Clause (5)

Clause (5), that a projective morphism is in `QP_S`, is
`AlgebraicGeometry.IsProjective.isQuasiProjective`, which is Morphisms [Stacks, Tag 07RL] for
`AlgebraicGeometry.IsProjective` — clause (1) of Definition 01W8, a closed immersion over `S`
into the projective bundle `𝐏(ℰ)` of a quasi-coherent module of finite type — with no hypothesis
on the base, as the source states it. Membership of `X` in `QP_S` is
`AlgebraicGeometry.IsQuasiProjective X.hom`, so that theorem is the clause and it carries the
attribute. It lives in
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleProperFiniteType.Basic`, which does not import
this file.

Nothing is assumed for it. In particular clause (1) of [Stacks, Tag 0BCL],
`AlgebraicGeometry.isProjective_iff_isQuasiProjective_and_isProper`, is **not** used, and the
base need not be quasi-compact and quasi-separated: the forward half of that equivalence is the
pair `AlgebraicGeometry.IsProjective.isProper` and
`AlgebraicGeometry.IsProjective.isQuasiProjective`, both in the library. The two further inputs
for Tag 07RL at this notion of projectivity are in the library as well — properness of
`𝐏(ℰ) ⟶ S` for `ℰ` quasi-coherent of finite type
(`AlgebraicGeometry.isProper_schemeProjectiveBundleToBase`, through the presentation comparison
`AlgebraicGeometry.projectiveBundlePresentationsAgree`) and the finite type of a projective
morphism (`AlgebraicGeometry.IsProjective.locallyOfFiniteType`,
`AlgebraicGeometry.IsProjective.quasiCompact`) — so clause (5) is stated unconditionally, with no
assumption of Tag 0BCL or of quasi-compactness and quasi-separatedness of the base.

## Clause (4)

Clause (4), closure of `QP_S` under finite disjoint unions, is
`AlgebraicGeometry.isQuasiProjective_sigmaDesc`: for a finite family of quasi-projective
morphisms `f i : Z i ⟶ S` the structure morphism `Sigma.desc f : ∐ Z ⟶ S` of the disjoint union
is quasi-projective. It lives in
`StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveDisjointUnion`, which imports
this file, and is proved from clause (6) and clause (2) above rather than by the source's route.

**The source's route is still not available, and is not used.** The source reads clause (4) off
condition (4) of Tag 0B42 together with the assertion whose proof it omits — that an invertible
module on `Y ⨿ Z` whose restrictions to `Y` and to `Z` are ample is itself ample. The *module* is
available: gluing sheaves of modules along a finite coproduct of schemes is
`StacksTag09NE.moduleOnSchemeSigma`, with `StacksTag09NE.pullback_moduleOnSchemeSigma` for its
restriction to each summand and, for its invertibility,
`AlgebraicGeometry.isInvertibleModule_moduleOnSchemeSigma` (from
`StacksTag09NE.moduleOnSchemeSigma_exists_local_free`). The *absolute ampleness* is not: no
declaration in either Lean tree relates `Stacks.Ample.IsAmple` or
`AlgebraicGeometry.Scheme.Modules.IsAmple` to a coproduct, a sigma or a disjoint union of
schemes, so

> a module on a finite coproduct of schemes whose restriction to every summand is ample is
> ample

remains unproved here. What the proof of clause (4) shows is that the clause does not need it:
relative ampleness of the glued module is proved over the base `∐_i S`, one copy of `S` per
summand, where the preimage of a small enough open of the base meets a single summand and no
disjoint union is formed, and the collapsing morphism `∐_i S ⟶ S` is quasi-affine of finite type,
hence quasi-projective by clause (6). Clause (2) composes the two.

**The route through projective schemes is not used either.** Condition (3) of Tag 0B42 presents
`X` as a quasi-compact open subscheme over `S` of a scheme projective over `S`; a coproduct of
two such presentations is one for `X ⨿ Y`, provided a coproduct of two schemes projective over
`S` is projective over `S`, which is clause (4) of [Stacks, Tag 0B46]. In this repository that
route costs two named hypotheses that are not discharged here — `ProjectiveCriteriaOverAmpleBase`
(Tag 0B45) and `Stacks.FiniteMorphismProjective.PushforwardIsRelativeProj`, which Tag 0B46's
clause (4) carries. A clause standing on unproved inputs is worth less than a located gap, so it
is not stated.

## References

* [Stacks Project, Tag 0B43](https://stacks.math.columbia.edu/tag/0B43)
* [Stacks Project, Tag 0B42](https://stacks.math.columbia.edu/tag/0B42)
* [Stacks Project, Tag 0B3G](https://stacks.math.columbia.edu/tag/0B3G)
* [Stacks Project, Tag 0B3H](https://stacks.math.columbia.edu/tag/0B3H)
* [Stacks Project, Tag 07RL](https://stacks.math.columbia.edu/tag/07RL)
* [Stacks Project, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR)
* [Stacks Project, Tag 01TN](https://stacks.math.columbia.edu/tag/01TN)
* [Stacks Project, Tag 0C4M](https://stacks.math.columbia.edu/tag/0C4M)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The category `QP_S` -/

/-- The property, of a scheme over `S`, of being quasi-projective over `S`. This is condition
(1) of [Stacks, Tag 0B42]. -/
def quasiProjectiveOver (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun X => IsQuasiProjective X.hom

/-- **`QP_S` of [Stacks, Tag 0B43]**: the full subcategory of the category of schemes over `S`
whose objects are quasi-projective over `S`. -/
abbrev QuasiProjectiveSchemesOver (S : Scheme.{u}) :=
  (quasiProjectiveOver S).FullSubcategory

/-- Quasi-projectivity over the base is invariant under isomorphism of schemes over the base: an
isomorphism in `Over S` identifies the two structure morphisms, and an isomorphism is a base
change of the identity, so [Stacks, Tag 0B3G] applies. -/
instance quasiProjectiveOver_isClosedUnderIsomorphisms (S : Scheme.{u}) :
    (quasiProjectiveOver S).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    have hiso := show IsIso e.inv.left from
      inferInstanceAs (IsIso ((Over.forget S).map e.inv))
    rw [show (quasiProjectiveOver S) Y = IsQuasiProjective Y.hom from rfl, ← Over.w e.inv]
    exact IsQuasiProjective.of_isPullback
      (IsPullback.of_horiz_isIso (fst := e.inv.left) (snd := e.inv.left ≫ X.hom)
        (f := X.hom) (g := 𝟙 S) ⟨by simp⟩) hX

/-- A scheme carrying an ample invertible module is quasi-compact. This is the only consequence
of the hypothesis on the base that clauses (2) and (3) use. -/
theorem compactSpace_of_exists_isAmple (S : Scheme.{u})
    (hS : ∃ (M : S.Modules) (hM : Stacks.Ample.IsInvertibleModule S M),
      letI : Stacks.Ample.IsInvertibleModule S M := hM
      Stacks.Ample.IsAmple S M) :
    CompactSpace S := by
  obtain ⟨M, hM, hample⟩ := hS
  have := show Stacks.Ample.IsInvertibleModule S M from hM
  exact hample.compactSpace

/-- A scheme carrying an ample invertible module is quasi-separated, by [Stacks, Tag 01PV]. -/
theorem quasiSeparatedSpace_of_exists_isAmple (S : Scheme.{u})
    (hS : ∃ (M : S.Modules) (hM : Stacks.Ample.IsInvertibleModule S M),
      letI : Stacks.Ample.IsInvertibleModule S M := hM
      Stacks.Ample.IsAmple S M) :
    QuasiSeparatedSpace S := by
  obtain ⟨M, hM, hample⟩ := hS
  have := show Stacks.Ample.IsInvertibleModule S M from hM
  exact Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple M hample

/-! ### Clause (1): base change -/

/-- **Stacks Project, Tag 0B43, clause (1).** For a morphism of bases `g : S' ⟶ S`, base change
along `g` is a functor `QP_S ⥤ QP_{S'}`: the fibre product `X ×_S S'` of a scheme `X`
quasi-projective over `S` is quasi-projective over `S'`.

The object part is [Stacks, Tag 0B3G], `AlgebraicGeometry.IsQuasiProjective.of_isPullback`,
applied to the fibre-product square. That result is unconditional, so the hypothesis of the
source that `S'` carries an ample invertible sheaf is not needed and is not assumed. -/
@[stacks 0B43 "part (1), base change; the source's hypothesis that `S'` has an ample invertible \
sheaf is not needed, Tag 0B3G needing no such hypothesis", ega "II 5.3.4"]
def QuasiProjectiveSchemesOver.baseChange {S S' : Scheme.{u}} (g : S' ⟶ S) :
    QuasiProjectiveSchemesOver S ⥤ QuasiProjectiveSchemesOver S' :=
  ObjectProperty.lift (quasiProjectiveOver S') ((quasiProjectiveOver S).ι ⋙ Over.pullback g)
    fun X => IsQuasiProjective.of_isPullback (IsPullback.of_hasPullback X.obj.hom g) X.property

/-! ### Clause (2): composition -/

/-- **Stacks Project, Tag 0B43, clause (2).** Let `S` carry an ample invertible sheaf. If
`X ∈ QP_S` and `Y ∈ QP_X`, then `Y ∈ QP_S`: for `f : Y ⟶ X` and `g : X ⟶ S` quasi-projective,
`f ≫ g` is quasi-projective.

The source reads this off condition (4) of [Stacks, Tag 0B42]. It is taken here from
[Stacks, Tag 0C4M], `AlgebraicGeometry.IsQuasiProjective.comp`, which is already proved over a
quasi-compact base; the ample invertible sheaf on `S` supplies that quasi-compactness and nothing
else is used. -/
@[stacks 0B43 "part (2), composition"]
theorem isQuasiProjective_comp_of_exists_isAmple {X Y S : Scheme.{u}} (f : Y ⟶ X) (g : X ⟶ S)
    (hS : ∃ (M : S.Modules) (hM : Stacks.Ample.IsInvertibleModule S M),
      letI : Stacks.Ample.IsInvertibleModule S M := hM
      Stacks.Ample.IsAmple S M)
    (hf : IsQuasiProjective f) (hg : IsQuasiProjective g) : IsQuasiProjective (f ≫ g) := by
  have := compactSpace_of_exists_isAmple S hS
  exact IsQuasiProjective.comp f g hf hg

/-! ### Clause (3): fibre products -/

/-- **Stacks Project, Tag 0B43, clause (3). `QP_S` is closed under fibre products over `S`.** For
`f : X ⟶ S` and `g : Y ⟶ S` quasi-projective and `S` carrying an ample invertible sheaf, the
structure morphism `X ×_S Y ⟶ S` is quasi-projective.

This is the source's proof: the projection `X ×_S Y ⟶ Y` is a base change of `f`, hence
quasi-projective by clause (1), and clause (2) composes it with `g`. -/
@[stacks 0B43 "part (3), fibre products"]
theorem isQuasiProjective_pullback_snd_comp {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (hS : ∃ (M : S.Modules) (hM : Stacks.Ample.IsInvertibleModule S M),
      letI : Stacks.Ample.IsInvertibleModule S M := hM
      Stacks.Ample.IsAmple S M)
    (hf : IsQuasiProjective f) (hg : IsQuasiProjective g) :
    IsQuasiProjective (pullback.snd f g ≫ g) :=
  isQuasiProjective_comp_of_exists_isAmple _ _ hS (IsQuasiProjective.pullback_snd f g hf) hg

/-- **Binary products of schemes over `S` are the fibre products of the sources.** The fibre
product of the two sources, with the structure morphism factoring through the second projection,
is the product in the category of schemes over `S`. -/
def isLimitOverBinaryFan {S : Scheme.{u}} (A B : Over S) :
    IsLimit (BinaryFan.mk
      (Over.homMk (U := Over.mk (pullback.snd A.hom B.hom ≫ B.hom)) (V := A)
        (pullback.fst A.hom B.hom) pullback.condition)
      (Over.homMk (U := Over.mk (pullback.snd A.hom B.hom ≫ B.hom)) (V := B)
        (pullback.snd A.hom B.hom) rfl)) :=
  BinaryFan.isLimitMk
    (fun s => Over.homMk
      (pullback.lift s.fst.left s.snd.left ((Over.w s.fst).trans (Over.w s.snd).symm))
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ B.hom) (pullback.lift_snd _ _ _)).trans (Over.w s.snd))))
    (fun _ => Over.OverMorphism.ext (pullback.lift_fst _ _ _))
    (fun _ => Over.OverMorphism.ext (pullback.lift_snd _ _ _))
    (fun _ _ h₁ h₂ => Over.OverMorphism.ext (pullback.hom_ext
      ((congrArg Over.Hom.left h₁).trans (pullback.lift_fst _ _ _).symm)
      ((congrArg Over.Hom.left h₂).trans (pullback.lift_snd _ _ _).symm)))

/-- **Stacks Project, Tag 0B43, clause (3), as a closure property of the category `QP_S`.** For
`S` carrying an ample invertible sheaf, the full subcategory of schemes quasi-projective over `S`
is closed under binary products in the category of schemes over `S` — that is, under fibre
products over `S`.

A binary product in `Over S` is a fibre product of the sources over `S`, by
`AlgebraicGeometry.isLimitOverBinaryFan`, so this is
`AlgebraicGeometry.isQuasiProjective_pullback_snd_comp` transported along the comparison
isomorphism. -/
@[stacks 0B43 "part (3), fibre products, as closure of the category under binary products",
  ega "II 5.3.4" "(iv)"]
theorem quasiProjectiveOver_isClosedUnderBinaryProducts (S : Scheme.{u})
    (hS : ∃ (M : S.Modules) (hM : Stacks.Ample.IsInvertibleModule S M),
      letI : Stacks.Ample.IsInvertibleModule S M := hM
      Stacks.Ample.IsAmple S M) :
    (quasiProjectiveOver S).IsClosedUnderBinaryProducts := by
  refine ⟨?_⟩
  rintro T ⟨p⟩
  have hdiag := p.hasLimit
  have hpair := hasLimit_of_iso (diagramIsoPair p.diag)
  have e := show T ≅ Over.mk (pullback.snd (p.diag.obj ⟨WalkingPair.left⟩).hom
      (p.diag.obj ⟨WalkingPair.right⟩).hom ≫ (p.diag.obj ⟨WalkingPair.right⟩).hom) from
    (p.isLimit.conePointUniqueUpToIso (limit.isLimit p.diag)).trans
      ((HasLimit.isoOfNatIso (diagramIsoPair p.diag)).trans
        ((limit.isLimit _).conePointUniqueUpToIso (isLimitOverBinaryFan _ _)))
  exact ObjectProperty.prop_of_iso _ e.symm
    (isQuasiProjective_pullback_snd_comp _ _ hS (p.prop_diag_obj _) (p.prop_diag_obj _))

/-! ### Clause (6): quasi-affine morphisms of finite type -/

/-- **Stacks Project, Tag 0B43, clause (6).** If `f : X ⟶ S` is quasi-affine of finite type then
`X ∈ QP_S`.

This is Morphisms [Stacks, Tag 0B3H],
`Stacks.HProjective.isQuasiProjective_of_isQuasiAffineHom`: the structure sheaf `𝒪_X` is ample
relative to a quasi-affine morphism. It needs no hypothesis on the base. Finite type is the
conjunction of local finite type and quasi-compactness as in [Stacks, Tag 01T1], and
quasi-compactness already follows from quasi-affineness, so only the local finite type half
appears. -/
@[stacks 0B43 "part (6), quasi-affine of finite type; no hypothesis on the base is used"]
theorem isQuasiProjective_of_isQuasiAffineHom {X S : Scheme.{u}} (f : X ⟶ S)
    [IsQuasiAffineHom f] (hf : LocallyOfFiniteType f) : IsQuasiProjective f :=
  (isQuasiProjective_iff_hProjectiveIsQuasiProjective f).mpr
    (Stacks.HProjective.isQuasiProjective_of_isQuasiAffineHom f hf)

/-! ### Clause (7): quasi-finite separated morphisms -/

/-- **Stacks Project, Tag 0B43, clause (7).** If `f : X ⟶ S` is quasi-finite and separated then
`X ∈ QP_S`.

This is the source's proof: a quasi-finite separated morphism is quasi-affine by
[Stacks, Tag 02LR], `AlgebraicGeometry.isQuasiAffineHom_of_locallyQuasiFinite`, and clause (6)
applies. Quasi-finiteness is local quasi-finiteness together with finite type, as in
[Stacks, Tag 02NG]. No hypothesis on the base is used. -/
@[stacks 0B43 "part (7), quasi-finite and separated; no hypothesis on the base is used",
  ega "III 4.4.12" "more general"]
theorem isQuasiProjective_of_locallyQuasiFinite_of_isSeparated {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] [QuasiCompact f] :
    IsQuasiProjective f :=
  have := isQuasiAffineHom_of_locallyQuasiFinite f
  isQuasiProjective_of_isQuasiAffineHom f ‹LocallyOfFiniteType f›

/-! ### Clause (8): quasi-compact immersions -/

/-- **Stacks Project, Tag 0B43, clause (8).** If `f : X ⟶ S` is a quasi-compact immersion then
`X ∈ QP_S`.

The source goes through clause (7) and Morphisms [Stacks, Tag 01TN], an immersion being locally
quasi-finite; here that tag is Mathlib's `LocallyQuasiFinite` instance for an immersion, and an
immersion is locally of finite type as well, so clause (7) applies directly. No hypothesis on the
base is used. -/
@[stacks 0B43 "part (8), quasi-compact immersion; no hypothesis on the base is used"]
theorem isQuasiProjective_of_isImmersion {X S : Scheme.{u}} (f : X ⟶ S) [IsImmersion f]
    [QuasiCompact f] : IsQuasiProjective f :=
  isQuasiProjective_of_locallyQuasiFinite_of_isSeparated f

end AlgebraicGeometry

end
