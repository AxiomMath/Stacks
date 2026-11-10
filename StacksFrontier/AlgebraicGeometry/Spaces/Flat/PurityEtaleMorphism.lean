module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceEtaleTargetDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleTargetModuleFMapRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PuritySchemeBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PuritySpecialization
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Purity along an étale morphism over the base

In the standing situation of Stacks 0CV6 — a finite type decent morphism `f : X ⟶ Y` of
algebraic spaces over a scheme `S`, a finite type quasi-coherent `𝒪_X`-module `ℱ` and a point
`y` of `Y` — let `g : X' ⟶ X` be an étale morphism over `Y` whose structure morphism
`X' ⟶ Y` is again decent and of finite type. Then `g^*ℱ` on `X'` carries a situation of its
own, and the two purity conditions above `y` are related in both directions:

* if the relative assassin `Ass_{X/Y}(ℱ)` lies in the image of `|X'| → |X|`, then purity —
  respectively universal purity — of `g^*ℱ` above `y` descends to `ℱ`;
* conversely, purity of `ℱ` above `y` forces `Ass_{X/Y}(ℱ)` into that image as soon as the
  image contains the fibre `F = f^{-1}(\{y\})`, because the image of an étale morphism is open
  and purity specializes the relative assassin into the fibre;
* and when `ℱ` is moreover flat along `F`, the image need only contain `Ass_{X/Y}(ℱ) ∩ F`,
  because Stacks 0CW1 then specializes the relative assassin into that smaller set.

The relative assassin is the relative weak assassin
`AlgebraicGeometry.Space.IsRelativeWeaklyAssociatedPoint` of Stacks 0CV0: the morphism of the
situation is of finite type, so its fibres are locally Noetherian by Stacks 0CUY and that set
is the one the source writes `Ass_{X/Y}(ℱ)`.

## Main definitions

* `AlgebraicGeometry.Space.PrePureSituation.structureSpaceMorphism`: the morphism of a
  pre-pure situation, read as a morphism in the category of algebraic spaces.
* `AlgebraicGeometry.Space.EtaleOverSource`: the hypothesis of Stacks 0CW3, an étale morphism
  `g : X' ⟶ X` into the source of a pre-pure situation whose composite to the base is decent
  and of finite type.
* `AlgebraicGeometry.Space.EtaleOverSource.situation`: the pre-pure situation it induces on
  `X'`, carrying the module `g^*ℱ`.
* `AlgebraicGeometry.Space.EtaleOverSource.baseChangeMap`: the induced morphism
  `X'_T ⟶ X_T` of base changes.
* `AlgebraicGeometry.Space.EtaleOverSource.alongEtale`: an impurity diagram of the situation,
  lifted to the situation on `X'` along a prescribed lift of its distinguished point.
* `AlgebraicGeometry.Space.PrePureSituation.IsAffineLocalAt`: the base of the situation is
  affine local with closed point `y`.
* `AlgebraicGeometry.Space.PurityFibreSpecialization`: the specialization step of clause (2)
  of Stacks 0CW3.

## Main results

* `AlgebraicGeometry.Space.EtaleOverSource.isEtale_baseChangeMap`: **Stacks 03FU** for the
  induced morphism of base changes.
* `AlgebraicGeometry.Space.EtaleOverSource.isRelativeWeaklyAssociatedPoint_baseChangeMap_iff`:
  **Stacks 0CUZ** on the base changes, the relative assassin of `g^*ℱ` restricted to `X'_T`
  being the preimage of that of `ℱ` restricted to `X_T`.
* `AlgebraicGeometry.Space.EtaleOverSource.isPureAbove_of_isPureAbove_situation`:
  **Stacks 0CW3, clause (1)** for purity above `y`, and
  `isUniversallyPureAbove_of_isUniversallyPureAbove_situation` in the same namespace for
  universal purity above `y`.
* `AlgebraicGeometry.Space.purityFibreSpecialization`: the specialization step itself, proved
  from purity above `y` over an affine local base.
* `relativeWeaklyAssociatedPoints_subset_range_of_isAffineLocalAt`, in
  `AlgebraicGeometry.Space.EtaleOverSource`:
  **Stacks 0CW3, clause (2)**, carrying only the hypotheses of the source;
  `relativeWeaklyAssociatedPoints_subset_range` is the auxiliary form that grants the
  specialization step instead of proving it.
* `relativeWeaklyAssociatedPoints_subset_range_of_isFlatAt_fibre` and
  `..._of_isFlatAt_fibre_of_isAffineLocalAt`: the analogue of clause (2) for a morphism flat
  along the fibre. These are **not** clause (3) and carry no `@[stacks 0CW3]` attribute:
  clause (3) asks for the module `ℱ` to be flat over `Y` at the points of the fibre, and that
  condition is incomparable with flatness of the morphism, so neither statement implies the
  other.
* `relativeWeaklyAssociatedPoints_subset_range_of_isFlatOver_fibre_of_isAffineLocalAt`, in
  `AlgebraicGeometry.Space.EtaleOverSource`: **Stacks 0CW3, clause (3)**, with the source's own
  flatness hypothesis — flatness of the module `ℱ` over `Y` at the points of the fibre, which
  is `AlgebraicGeometry.Space.IsFlatOverAtPoint` — and carrying only the hypotheses of the
  source; `relativeWeaklyAssociatedPoints_subset_range_of_isFlatOver_fibre` is the auxiliary
  form that grants the specialization step instead of proving it.
* `exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_isoSchemeSpace`, in
  `AlgebraicGeometry.Space`: **Stacks 0CW1** over a base isomorphic to the algebraic space of
  a scheme of the site, which is what the affine local base of clauses (2) and (3) supplies;
  and `AlgebraicGeometry.Space.isFlatOverAtPoint_comp_of_isEtale`, the transport of flatness
  over the target along an étale — here invertible — morphism of the target that it
  consumes.

Of Stacks 0CW3 this file therefore delivers clauses (1), (2) and (3); clause (4) of the source
is "Add more here" and has no content.

## Implementation notes

The induced morphism `X'_T ⟶ X_T` of base changes is built from
`CategoryTheory.Limits.pullbackLeftPullbackSndIso` exactly as
`AlgebraicGeometry.Space.ClosedSubspaceModule.baseChangeImmersion` is, the construction using
nothing about the morphism into the source; the two are instances of one comparison, kept
separate only because neither file is a dependency of the other. Its cartesian square over
`g` is what makes it étale, by Stacks 03FU, and is also the square `sq'` that Stacks 0CW2
needs.

Clause (1) is proved from two inputs the library already has. Stacks 0CW2, in the form
`AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints_baseChange_subset_range`, carries the
containment `Ass_{X/Y}(ℱ) ⊆ g(|X'|)` to every base change, which produces the lift `ξ'` of the
distinguished point of an impurity diagram; Stacks 0CUZ, in the form
`AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_modulePullback_iff`, identifies the
relative assassin on `X'_T` with the preimage of the one on `X_T`, which is what makes the
lifted diagram an impurity. The second half of the impurity condition only needs continuity of
the map on points: a specialization of `ξ'` over `t` would push to a specialization of `ξ`
over `t`. Since the structure morphism and the two points of `T` are unchanged by the lift,
one argument serves both purity above `y` — where the structure morphism is required to be
quasi-finite at `t` — and universal purity above `y`.

Clause (2) is proved from the openness of `g(|X'|)`, which is Stacks 03IR, together with the
fact that an open set contains every generalization of each of its points. The other half of
the source's proof of clause (2) — that purity above `y` specializes every point of
`Ass_{X/Y}(ℱ)` to a point of the fibre — is the condition
`AlgebraicGeometry.Space.PurityFibreSpecialization`, which takes both of the source's
hypotheses, `AlgebraicGeometry.Space.PrePureSituation.IsAffineLocalAt` and purity above `y`, so
that both remain hypotheses of the statements using it. It is carried by the statement of
clause (2) below and proved separately, as the source proves it: the impurity diagram whose
own structure morphism is the base itself, with `t = y` and `t'` the image of the given point,
the specialization `t' ⤳ t` being supplied by the affine local base with closed point `y`. An
affine local base is read as the source's own, a base represented by a scheme of the site
isomorphic to the spectrum of a local ring, with the chosen point closed for the point topology
of Stacks 03BY; the structure morphism of the diagram is then the representing isomorphism,
which is étale and so locally quasi-finite, and the distinguished point of the base change
comes from part (2) of Stacks 0CV2,
`AlgebraicGeometry.Space.exists_isRelativeWeaklyAssociatedPoint_baseChange`. The clause (2)
statement with that condition discharged is stated alongside the one carrying it, so that both
interfaces remain available.

Clause (3) is the variant of clause (2) for a module flat along the fibre, which replaces the
fibre by its intersection with the relative assassin in the containment hypothesis. It is
proved from clause (2)'s specialization step followed by Stacks 0CW1, whose own
hypothesis of flatness along the fibre is clause (3)'s extra hypothesis and whose conclusion
places the specialized point in the relative assassin.

Nothing is granted there either. Stacks 0CW1 is available unconditionally for a base which is a
scheme of the site, as
`AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_schemeBase`,
and an affine local base is by definition isomorphic to the algebraic space of such a scheme.
Transporting the lemma across that isomorphism is
`Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_isoSchemeSpace` of this file:
the morphism becomes `f ≫ e⁻¹`, locally of finite type by Stacks 06LT and Stacks 03XG; the point of
the base becomes its image, the map on points of an isomorphism being injective, so the fibre is
the same set; flatness over the base moves by
`AlgebraicGeometry.Space.isFlatOverAtPoint_comp_of_isEtale`, which reads
`AlgebraicGeometry.Space.IsFlatOverAtPoint` on the chart diagram postcomposed with `e⁻¹` and so
on the very same vertical morphism of schemes; and the relative assassin does not move at all,
by Stacks 0CUZ in the form
`AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_comp_iff_of_isEtale`. So the two
statements of clause (3) carry exactly the specialization step of clause (2), respectively
nothing. The chart criterion
`AlgebraicGeometry.Space.ChartPurityCriterionFlatOver`, which the algebraic-space-base form
`AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_isFlatOver`
carries, is not needed: the base here is not an arbitrary algebraic space.

The morphism-flat analogue of the clause uses the morphism-flat form,
`AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre`, and the
criterion on an étale scheme chart is carried as a hypothesis there, so it is carried by those
two statements; the scheme-base lemma cannot discharge it, since it is stated at the source's
module flatness and the two flatness conditions are incomparable. Decency of `X` as an algebraic
space, which Stacks 0CW1 asks for, is not carried: the affine local base is represented by a
scheme of the site, hence a decent space by condition (4) of Stacks 03JV, and decency of the
morphism of the situation carries that to `X` by Stacks 0ABY. Clause (4) of the source is the
placeholder "Add more here" and has no content.

Finiteness of type and quasi-coherence of `ℱ` are hypotheses of the situation, and for `g^*ℱ`
both are derived rather than assumed: finiteness of type is
`AlgebraicGeometry.Space.isFiniteTypeOnSite_modulePullback` and quasi-coherence is Stacks 03GA
along an étale morphism,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isEtale`. Decency and
finiteness of type of `X' ⟶ Y` are fields of the hypothesis structure, the source assuming them
outright.

## References

* [Stacks Project, Lemma 77.6.3 (Tag 0CW3)](https://stacks.math.columbia.edu/tag/0CW3)
* [Stacks Project, Tag 0CW2](https://stacks.math.columbia.edu/tag/0CW2)
* [Stacks Project, Tag 0CW1](https://stacks.math.columbia.edu/tag/0CW1)
* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 0CVD](https://stacks.math.columbia.edu/tag/0CVD)
* [Stacks Project, Tag 0CV2](https://stacks.math.columbia.edu/tag/0CV2)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03XU](https://stacks.math.columbia.edu/tag/03XU)
* [Stacks Project, Tag 03XG](https://stacks.math.columbia.edu/tag/03XG)
* [Stacks Project, Tag 06LT](https://stacks.math.columbia.edu/tag/06LT)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03IR](https://stacks.math.columbia.edu/tag/03IR)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 0ABY](https://stacks.math.columbia.edu/tag/0ABY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/- Instance search for pullbacks of presheaves on `BigFppfOver B S hS` times out under Lean
v4.35.0; supply the functor-category instances (file-unique names). -/
local instance (priority := high) hasPullbacks_presheaf_PurityEtaleMorphism :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_PurityEtaleMorphism
    {Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ W) (g : Z ⟶ W) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

/-- The morphism `f : X ⟶ Y` of a pre-pure situation, read as a morphism in the category of
algebraic spaces over `S`. This is the morphism along which the relative weak assassin
`WeakAss_{X/Y}(ℱ)` of Stacks 0CV0 is taken. -/
@[reducible] noncomputable def PrePureSituation.structureSpaceMorphism
    (P : PrePureSituation.{u, u} B S hS) :
    (⟨P.X, P.hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P.Y, P.hY⟩ :=
  ObjectProperty.homMk P.f

/-! ### An étale morphism into the source -/

/-- **The hypothesis of Stacks 0CW3**: an étale morphism `g : X' ⟶ X` into the source of a
pre-pure situation whose composite `X' ⟶ Y` to the base is decent and of finite type, as the
source assumes for both structure morphisms.

Nothing beyond the source's hypotheses is asked. Quasi-coherence of the pullback `g^*ℱ` is
Stacks 03GA along an étale morphism,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isEtale`, and finiteness of its
type is `AlgebraicGeometry.Space.isFiniteTypeOnSite_modulePullback`. -/
structure EtaleOverSource (P : PrePureSituation.{u, u} B S hS) where
  /-- The source of the étale morphism. -/
  X' : AlgebraicSpaces B S hS
  /-- The morphism to the source of the situation. -/
  g : X' ⟶ (⟨P.X, P.hX⟩ : AlgebraicSpaces B S hS)
  /-- It is étale. -/
  isEtale : IsEtale B S hS g.hom
  /-- The composite `X' ⟶ Y` is of finite type. -/
  finiteType : IsFiniteType B S hS (g.hom ≫ P.f)
  /-- The composite `X' ⟶ Y` is decent. -/
  decent : IsDecent B S hS (g.hom ≫ P.f)

namespace EtaleOverSource

variable {P : PrePureSituation.{u, u} B S hS} (c : EtaleOverSource P)

/-- **The pre-pure situation on the étale cover**: the composite `X' ⟶ X ⟶ Y`, which is of
finite type and decent by hypothesis, the pullback `g^*ℱ` of the module of the situation, and
the same point of the base.

Finiteness of type of `g^*ℱ` is Stacks 03DO for the clause 03DL(5); its quasi-coherence is
Stacks 03GA along an étale morphism. -/
@[reducible] noncomputable def situation : PrePureSituation.{u, u} B S hS where
  X := c.X'.1
  hX := c.X'.2
  Y := P.Y
  hY := P.hY
  f := c.g.hom ≫ P.f
  finiteType := c.finiteType
  decent := c.decent
  F := (modulePullback B S hS c.g).obj P.F
  moduleFiniteType := isFiniteTypeOnSite_modulePullback B S hS c.g P.F P.moduleFiniteType
  moduleQuasicoherent :=
    isQuasicoherentOnSite_modulePullback_of_isEtale B S hS c.g c.isEtale P.F P.moduleQuasicoherent
  y := P.y

/-! ### The induced morphism of base changes -/

variable (T : BigFppfOver B S hS) (q : yoneda.obj T ⟶ P.Y)

/-- The induced morphism `X'_T ⟶ X_T` of base changes, read off the comparison of
`(T ×_Y X) ×_X X'` with `T ×_Y X'`. -/
noncomputable def baseChangeMap :
    c.situation.baseChangeSpace T q ⟶ P.baseChangeSpace T q :=
  ObjectProperty.homMk ((pullbackLeftPullbackSndIso q P.f c.g.hom).inv ≫
    pullback.fst (pullback.snd q P.f) c.g.hom)

/-- The induced morphism of base changes is compatible with the projections to `T`. -/
theorem baseChangeMap_hom_comp_fst :
    (c.baseChangeMap T q).hom ≫ pullback.fst q P.f =
      pullback.fst q (c.g.hom ≫ P.f) := by
  change ((pullbackLeftPullbackSndIso q P.f c.g.hom).inv ≫
    pullback.fst (pullback.snd q P.f) c.g.hom) ≫ pullback.fst q P.f = _
  rw [Category.assoc]
  exact pullbackLeftPullbackSndIso_inv_fst q P.f c.g.hom

/-- The induced morphism of base changes is compatible with the projections to the source of
the situation and the étale morphism. -/
theorem baseChangeMap_hom_comp_snd :
    (c.baseChangeMap T q).hom ≫ pullback.snd q P.f =
      pullback.snd q (c.g.hom ≫ P.f) ≫ c.g.hom := by
  change ((pullbackLeftPullbackSndIso q P.f c.g.hom).inv ≫
    pullback.fst (pullback.snd q P.f) c.g.hom) ≫ pullback.snd q P.f = _
  rw [Category.assoc]
  exact pullbackLeftPullbackSndIso_inv_fst_snd q P.f c.g.hom

/-- The induced morphism of base changes is compatible with the projections to `T`, as a
morphism of algebraic spaces. -/
theorem baseChangeMap_comp_toBase :
    c.baseChangeMap T q ≫ P.baseChangeToBase T q = c.situation.baseChangeToBase T q :=
  ObjectProperty.hom_ext _ (c.baseChangeMap_hom_comp_fst T q)

/-- The induced morphism of base changes is compatible with the projections to the source of
the situation, as a morphism of algebraic spaces. -/
theorem baseChangeMap_comp_toSource :
    c.baseChangeMap T q ≫ P.baseChangeToSource T q =
      c.situation.baseChangeToSource T q ≫ c.g :=
  ObjectProperty.hom_ext _ (c.baseChangeMap_hom_comp_snd T q)

/-- The square exhibiting `X'_T ⟶ X_T` as a base change of the étale morphism `g`. -/
theorem isPullback_baseChangeMap :
    IsPullback (c.baseChangeMap T q).hom (pullback.snd q (c.g.hom ≫ P.f))
      (pullback.snd q P.f) c.g.hom :=
  IsPullback.of_iso_pullback ⟨c.baseChangeMap_hom_comp_snd T q⟩
    (pullbackLeftPullbackSndIso q P.f c.g.hom).symm rfl
    (pullbackLeftPullbackSndIso_inv_snd_snd q P.f c.g.hom)

/-- **Stacks 03FU.** The induced morphism `X'_T ⟶ X_T` of base changes is étale, being the
composite of an isomorphism with a base change of `g` along `X_T ⟶ X`. -/
theorem isEtale_baseChangeMap : IsEtale B S hS (c.baseChangeMap T q).hom := by
  have hiso : IsEtale B S hS (pullbackLeftPullbackSndIso q P.f c.g.hom).inv :=
    isEtale_of_isIso B S hS _
  have hbc : IsEtale B S hS (pullback.fst (pullback.snd q P.f) c.g.hom) :=
    isEtale_pullback_fst B S hS (P.baseChangeSpace T q).2 P.hX c.X'.2
      (pullback.snd q P.f) c.g.hom c.isEtale
  exact isEtale_comp B S hS hiso hbc

/-! ### The module on the base changes -/

/-- The restriction of `ℱ_T` to `X'_T` is the restriction `(g^*ℱ)_T` of `g^*ℱ`: both are the
pullback of `ℱ` along `X'_T ⟶ X`, by the comparison of inverse images of Stacks 03LU and the
compatibility of the induced morphism of base changes with the projections to `X`. -/
noncomputable def baseChangeModuleIso :
    (modulePullback B S hS (c.baseChangeMap T q)).obj (P.baseChangeModule T q) ≅
      c.situation.baseChangeModule T q := by
  refine (modulePullbackCompIso B S hS (c.baseChangeMap T q) (P.baseChangeToSource T q)).app P.F
    ≪≫ ?_ ≪≫
    ((modulePullbackCompIso B S hS (c.situation.baseChangeToSource T q) c.g).app P.F).symm
  exact eqToIso (by rw [c.baseChangeMap_comp_toSource T q])

/-- **Stacks 0CUZ on the base changes.** A point of `X'_T` lies in the relative assassin
`Ass_{X'_T/T}((g^*ℱ)_T)` exactly when its image in `X_T` lies in `Ass_{X_T/T}(ℱ_T)`: the
induced morphism of base changes is étale, and it carries the one module to the other. -/
theorem isRelativeWeaklyAssociatedPoint_baseChangeMap_iff
    (ζ : points B S hS (c.situation.baseChangeSpace T q).1) :
    IsRelativeWeaklyAssociatedPoint B S hS (c.situation.baseChangeToBase T q)
        (c.situation.baseChangeModule T q) ζ ↔
      IsRelativeWeaklyAssociatedPoint B S hS (P.baseChangeToBase T q) (P.baseChangeModule T q)
        (pointsMap B S hS (c.situation.baseChangeSpace T q).1
          (c.baseChangeMap T q).hom ζ) := by
  rw [← c.baseChangeMap_comp_toBase T q,
    isRelativeWeaklyAssociatedPoint_congr (c.baseChangeMap T q ≫ P.baseChangeToBase T q)
      (c.baseChangeModuleIso T q).symm ζ]
  exact isRelativeWeaklyAssociatedPoint_modulePullback_iff B S hS (c.baseChangeMap T q)
    (c.isEtale_baseChangeMap T q) (P.baseChangeToBase T q) (P.baseChangeModule T q) ζ

/-- **Stacks 0CW2 for the étale morphism.** If the relative assassin `Ass_{X/Y}(ℱ)` lies in
the image of `|X'| → |X|`, then on any base change `T ⟶ Y` the relative assassin
`Ass_{X_T/T}(ℱ_T)` lies in the image of `|X'_T| → |X_T|`. -/
theorem relativeWeaklyAssociatedPoints_baseChangeModule_subset_range
    (hass : relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom)) :
    relativeWeaklyAssociatedPoints B S hS (P.baseChangeToBase T q)
        (P.baseChangeModule T q) ⊆
      Set.range (pointsMap B S hS (c.situation.baseChangeSpace T q).1
        (c.baseChangeMap T q).hom) :=
  relativeWeaklyAssociatedPoints_baseChange_subset_range B S hS
    (IsPullback.of_hasPullback q P.f).flip (c.isPullback_baseChangeMap T q) P.F hass

/-! ### Impurities -/

section Impurity

attribute [local instance] pointTopology

/-- An impurity diagram of the situation, read as an impurity diagram of the situation on the
étale cover: the structure morphism and the points of `T` are unchanged, and the distinguished
point of `X'_T` is a prescribed lift of the one of `X_T`. -/
@[reducible] noncomputable def alongEtale (D : ImpurityDiagram P)
    (ζ : points B S hS (c.situation.baseChangeSpace D.T D.g).1)
    (hζ : pointsMap B S hS (c.situation.baseChangeSpace D.T D.g).1
      (c.baseChangeMap D.T D.g).hom ζ = D.xi) :
    ImpurityDiagram c.situation where
  T := D.T
  g := D.g
  t' := D.t'
  t := D.t
  specializes := D.specializes
  mapsToChosenPoint := D.mapsToChosenPoint
  xi := ζ
  xi_liesOver := by
    rw [← c.baseChangeMap_hom_comp_fst D.T D.g, pointsMap_comp_apply, hζ]
    exact D.xi_liesOver

/-- **A lift of an impurity of `ℱ` above `y` is an impurity of `g^*ℱ` above `y`.** The lifted
point lies in the relative assassin of `(g^*ℱ)_T` because its image does, by Stacks 0CUZ on
the base changes; and no specialization of it lies over `t`, because the map on points is
continuous, so such a specialization would push to a specialization of `ξ` over `t`. -/
theorem isImpurity_alongEtale (D : ImpurityDiagram P) (hD : D.IsImpurity)
    (ζ : points B S hS (c.situation.baseChangeSpace D.T D.g).1)
    (hζ : pointsMap B S hS (c.situation.baseChangeSpace D.T D.g).1
      (c.baseChangeMap D.T D.g).hom ζ = D.xi) :
    (c.alongEtale D ζ hζ).IsImpurity := by
  rw [ImpurityDiagram.isImpurity_iff] at hD ⊢
  refine ⟨(c.isRelativeWeaklyAssociatedPoint_baseChangeMap_iff D.T D.g ζ).2 ?_, ?_⟩
  · rw [hζ]
    exact (D.isRelativeWeakAssassinPoint_iff D.xi).1 hD.1
  · intro θ hθ hmap
    refine hD.2 (pointsMap B S hS (c.situation.baseChangeSpace D.T D.g).1
      (c.baseChangeMap D.T D.g).hom θ) ?_ ?_
    · rw [← hζ]
      exact hθ.map (continuous_pointsMap B S hS (c.baseChangeMap D.T D.g).hom)
    · rw [← pointsMap_comp_apply, c.baseChangeMap_hom_comp_fst D.T D.g]
      exact hmap

/-- **Stacks 0CW3, clause (1), on impurity diagrams.** If the relative assassin
`Ass_{X/Y}(ℱ)` lies in the image of `|X'| → |X|`, then every impurity of `ℱ` above `y` lifts
to an impurity of `g^*ℱ` above `y` with the same structure morphism and the same two points of
`T`.

The property `Q` of the structure morphism and the point is arbitrary, so this covers both
purity above `y` — where the structure morphism is required to be quasi-finite at the point —
and universal purity above `y`. -/
theorem exists_isImpurity_situation
    (hass : relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom))
    (Q : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ P.Y) → points B S hS (yoneda.obj T) → Prop)
    (h : ∃ D : ImpurityDiagram P, Q D.T D.g D.t ∧ D.IsImpurity) :
    ∃ E : ImpurityDiagram c.situation, Q E.T E.g E.t ∧ E.IsImpurity := by
  obtain ⟨D, hQ, hD⟩ := h
  obtain ⟨ζ, hζ⟩ := c.relativeWeaklyAssociatedPoints_baseChangeModule_subset_range D.T D.g hass
    ((D.isRelativeWeakAssassinPoint_iff D.xi).1 hD.1)
  exact ⟨c.alongEtale D ζ hζ, hQ, c.isImpurity_alongEtale D hD ζ hζ⟩

/-! ### Stacks 0CW3, clause (1) -/

/-- **Stacks 0CW3, clause (1), for purity above `y`.** In the situation of Stacks 0CV6, let
`g : X' ⟶ X` be étale over `Y` with `X' ⟶ Y` decent and of finite type. If the relative
assassin `Ass_{X/Y}(ℱ)` lies in the image of `|X'| → |X|` and `g^*ℱ` is pure above `y`, then
`ℱ` is pure above `y`.

An impurity of `ℱ` above `y` whose structure morphism is quasi-finite at `t` lifts to such an
impurity of `g^*ℱ` above `y`: the containment passes to the base change by Stacks 0CW2, which
lifts the distinguished point, and Stacks 0CUZ makes the lift relatively associated.

The containment of the assassin and purity of `g^*ℱ` are the two assumptions the source's own
clause (1) makes, and nothing further is assumed.  In particular the containment is not obtained
from clause (2) of the same tag: clause (2) produces it from purity of `ℱ` above `y` — which is
the conclusion here — over an affine local base whose fibre is met by the image, so none of its
three inputs is available at clause (1). -/
@[stacks 0CW3 "clause (1) for purity above y: the source's own two assumptions on the etale \
morphism g, that Ass_{X/Y}(F) lies in the image of |X'| and that g^*F is pure above y, give \
purity of F above y. Nothing beyond the source's own assumptions is used"]
theorem isPureAbove_of_isPureAbove_situation
    (hass : relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom))
    (h : IsPureAbove c.situation) : IsPureAbove P := by
  intro D hqf hD
  obtain ⟨E, hqfE, hE⟩ := c.exists_isImpurity_situation hass
    (fun _ b t ↦ IsQuasiFiniteAt B S hS b t) ⟨D, hqf, hD⟩
  exact h E hqfE hE

/-- **Stacks 0CW3, clause (1), for universal purity above `y`.** In the situation of
Stacks 0CV6, let `g : X' ⟶ X` be étale over `Y` with `X' ⟶ Y` decent and of finite type. If
the relative assassin `Ass_{X/Y}(ℱ)` lies in the image of `|X'| → |X|` and `g^*ℱ` is
universally pure above `y`, then `ℱ` is universally pure above `y`.

Any impurity of `ℱ` above `y` lifts to an impurity of `g^*ℱ` above `y`.

The containment of the assassin and universal purity of `g^*ℱ` are the two assumptions the
source's own clause (1) makes, and nothing further is assumed. -/
@[stacks 0CW3 "clause (1) for universal purity above y: the source's own two assumptions on the \
etale morphism g, that Ass_{X/Y}(F) lies in the image of |X'| and that g^*F is universally pure \
above y, give universal purity of F above y. Nothing beyond the source's own assumptions is \
used"]
theorem isUniversallyPureAbove_of_isUniversallyPureAbove_situation
    (hass : relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom))
    (h : IsUniversallyPureAbove c.situation) : IsUniversallyPureAbove P := by
  intro D hD
  obtain ⟨E, -, hE⟩ := c.exists_isImpurity_situation hass (fun _ _ _ ↦ True)
    ⟨D, trivial, hD⟩
  exact h E hE

end Impurity

end EtaleOverSource

/-! ### The specialization step of clause (2) -/

section Specialization

attribute [local instance] pointTopology

/-- **The base of a pre-pure situation is affine local with closed point `y`**: it is
represented by a scheme of the site isomorphic to the spectrum of a local ring, and the chosen
point is closed for the point topology of Stacks 03BY. -/
def PrePureSituation.IsAffineLocalAt (P : PrePureSituation.{u, u} B S hS) : Prop :=
  (∃ (T : BigFppfOver B S hS) (A : CommRingCat.{u}), IsLocalRing A ∧
      Nonempty (Spec A ≅ (BigFppfOver.toScheme B S hS).obj T) ∧
      Nonempty (yoneda.obj T ≅ P.Y)) ∧
    IsClosed ({P.y} : Set (points B S hS P.Y))

/-- **The specialization step of Stacks 0CW3, clause (2).** Over a base which is affine local
with closed point `y`, purity of `ℱ` above `y` makes every point of the relative assassin
`Ass_{X/Y}(ℱ)` specialize to a point of the fibre `F = f^{-1}(\{y\})`.

The source obtains this from the definition of purity by taking the impurity diagram
whose structure morphism is the base itself, with `t = y` and `t'` the image of the given
point; the specialization `t' ⤳ t` is what the affine local base with closed point `y` gives.
Carrying the statement in this form keeps both of the source's hypotheses visible in the
statements that use it. -/
def PurityFibreSpecialization (P : PrePureSituation.{u, u} B S hS) : Prop :=
  P.IsAffineLocalAt → IsPureAbove P →
    ∀ x ∈ relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F,
      ∃ θ : points B S hS P.X, x ⤳ θ ∧ pointsMap B S hS P.X P.f θ = P.y

/-- If `g` is a left inverse of a continuous `f` and `q` is a closed point with `f (g q) = q`,
then `g q` is a closed point. -/
private theorem isClosed_singleton_of_inverse {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} {g : β → α} (hf : Continuous f) (hgf : ∀ a, g (f a) = a)
    {q : β} (hfg : f (g q) = q) (hq : IsClosed ({q} : Set β)) : IsClosed ({g q} : Set α) := by
  have : ({g q} : Set α) = f ⁻¹' {q} := by
    ext z
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨by rintro rfl; exact hfg, fun h ↦ by rw [← h, hgf]⟩
  rw [this]
  exact hq.preimage hf

/-- **In a scheme isomorphic to the spectrum of a local ring every point specializes to every
closed point.** Every point of the spectrum of a local ring specializes to
`IsLocalRing.closedPoint`, so a point whose singleton is closed has that point in its own
closure and is therefore equal to it; and every point specializes to it. -/
@[ega "I 2.4.1"]
theorem specializes_of_isClosed_isoSpec_isLocalRing {W : Scheme.{u}} {A : CommRingCat.{u}}
    (hA : IsLocalRing A) (φ : Spec A ≅ W) (p q : W)
    (hq : IsClosed ({q} : Set W)) : p ⤳ q := by
  have hinv : ∀ w : W, φ.hom (φ.inv w) = w := fun w => by
    rw [← Scheme.Hom.comp_apply, φ.inv_hom_id]
    rfl
  have hcl : IsClosed ({φ.inv q} : Set (Spec A)) :=
    isClosed_singleton_of_inverse φ.hom.continuous (fun z => by
      rw [← Scheme.Hom.comp_apply, φ.hom_inv_id]
      rfl) (hinv q) hq
  have hpspec : φ.inv p ⤳ IsLocalRing.closedPoint A := IsLocalRing.specializes_closedPoint _
  have hqspec : φ.inv q ⤳ IsLocalRing.closedPoint A := IsLocalRing.specializes_closedPoint _
  have heq : IsLocalRing.closedPoint A = φ.inv q := by
    have h := specializes_iff_mem_closure.1 hqspec
    rwa [hcl.closure_eq] at h
  rw [heq] at hpspec
  have h2 := hpspec.map φ.hom.continuous
  rwa [hinv, hinv] at h2

/-- **The specialization step of Stacks 0CW3, clause (2).** Over a base which is affine local
with closed point `y`, purity of `ℱ` above `y` does make every point of the relative assassin
`Ass_{X/Y}(ℱ)` specialize to a point of the fibre `F = f^{-1}(\{y\})`: the condition
`AlgebraicGeometry.Space.PurityFibreSpecialization` holds.

The diagram is the source's. Its scheme is the one representing the base and its structure
morphism the representing isomorphism, which is étale and hence locally quasi-finite by
Stacks 03XU, so the diagram is one of those that purity above `y` excludes; the point `t` is
the one of that scheme above `y` and `t'` the field-valued representative that the image of the
given point carries over to it. The specialization `t' ⤳ t` holds because `t` is a closed point
of a scheme isomorphic to the spectrum of a local ring, to which every point specializes. The
distinguished point of the base change `X_T = T ×_Y X` and its membership of
`Ass_{X_T/T}(ℱ_T)` are part (2) of Stacks 0CV2 at that representative. A specialization of it
lying over `t` would push down along `X_T ⟶ X` to a specialization of the given point lying
over `y`, so in the absence of the conclusion the diagram is an impurity. -/
theorem purityFibreSpecialization (P : PrePureSituation.{u, u} B S hS) :
    PurityFibreSpecialization P := by
  intro hlocal hpure x hx
  obtain ⟨⟨T, A, hA, ⟨φ⟩, ⟨e⟩⟩, hyclosed⟩ := hlocal
  by_contra hcon
  obtain ⟨p, hp, hfib⟩ := (isRelativeWeaklyAssociatedPoint_iff_exists B S hS
    P.structureSpaceMorphism P.F x).1 hx
  have ht : pointsMap B S hS (yoneda.obj T) e.hom
      (pointsMap B S hS P.Y e.inv P.y) = P.y := by
    rw [← pointsMap_comp_apply, e.inv_hom_id, pointsMap_id, id_eq]
  have hqmap : FieldValuedPoint.map B S hS (yoneda.obj T) e.hom
      (FieldValuedPoint.map B S hS P.Y e.inv p) = p := by
    rw [← FieldValuedPoint.map_comp, e.inv_hom_id, FieldValuedPoint.map_id]
  have hsq : IsPullback (P.baseChangeToSource T e.hom).hom (P.baseChangeToBase T e.hom).hom
      P.structureSpaceMorphism.hom
      (ObjectProperty.homMk (P := IsAlgebraicSpace B S hS) e.hom
        (X := (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS))
        (Y := (⟨P.Y, P.hY⟩ : AlgebraicSpaces B S hS))).hom :=
    (IsPullback.of_hasPullback e.hom P.f).flip
  obtain ⟨xi, hxiass, hxix, hxit⟩ :=
    exists_isRelativeWeaklyAssociatedPoint_baseChange B S hS
      (f := P.structureSpaceMorphism)
      (f' := P.baseChangeToBase T e.hom) (g' := P.baseChangeToSource T e.hom)
      hsq P.F (FieldValuedPoint.map B S hS P.Y e.inv p)
      (show IsWeaklyAssociatedOnFibre B S hS P.structureSpaceMorphism P.F
          (FieldValuedPoint.map B S hS (yoneda.obj T) e.hom
            (FieldValuedPoint.map B S hS P.Y e.inv p)) x from by rw [hqmap]; exact hfib)
  have htclosed : IsClosed ({pointsMap B S hS P.Y e.inv P.y} :
      Set (points B S hS (yoneda.obj T))) :=
    isClosed_singleton_of_inverse (continuous_pointsMap B S hS e.hom)
      (fun z ↦ by rw [← pointsMap_comp_apply, e.hom_inv_id, pointsMap_id, id_eq]) ht hyclosed
  have htscheme : IsClosed ({pointsToScheme B S hS T (pointsMap B S hS P.Y e.inv P.y)} :
      Set ((BigFppfOver.toScheme B S hS).obj T)) := by
    have h := (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS T
      {pointsMap B S hS P.Y e.inv P.y}).1 htclosed
    rwa [Set.image_singleton] at h
  have hnotD : ∀ θ : points B S hS (pullback e.hom P.f),
      xi ⤳ θ → pointsMap B S hS (pullback e.hom P.f) (pullback.fst e.hom P.f) θ ≠
        pointsMap B S hS P.Y e.inv P.y := by
    intro θ hθ hmapθ
    refine hcon ⟨pointsMap B S hS (pullback e.hom P.f) (pullback.snd e.hom P.f) θ, ?_, ?_⟩
    · rw [← hxix]
      exact hθ.map (continuous_pointsMap B S hS (pullback.snd e.hom P.f))
    · rw [← pointsMap_comp_apply, ← pullback.condition, pointsMap_comp_apply, hmapθ]
      exact ht
  refine hpure ⟨T, e.hom,
    FieldValuedPoint.class B S hS (yoneda.obj T) (FieldValuedPoint.map B S hS P.Y e.inv p),
    pointsMap B S hS P.Y e.inv P.y,
    specializes_of_isClosed_isoSpec_isLocalRing hA φ _ _ htscheme, ht, xi, hxit⟩ ?_ ?_
  · exact isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS
      (isAlgebraicSpace_yoneda B S hS T)
      (isLocallyQuasiFinite_of_isEtale' B S hS (isEtale_of_isIso B S hS e.hom)) _
  · rw [ImpurityDiagram.isImpurity_iff]
    exact ⟨hxiass, hnotD⟩

/-! ### Stacks 0CW1 over a base isomorphic to a scheme of the site -/

/-- **Flatness of a module over the target is unchanged by an étale morphism of the target.** If
`ℱ` on `X` is flat over `Y` at `x` along `a : X ⟶ Y` and `p : Y ⟶ Z` is étale, then `ℱ` is flat
over `Z` at `x` along `a ≫ p`.

A diagram of étale scheme charts over `a` becomes one over `a ≫ p` by postcomposing its chart of
`Y` with `p`, `AlgebraicGeometry.Space.ChartDiagram.postcompTarget`, and that leaves both the
chart of `X` and the vertical morphism of schemes untouched. So the ringed-space flatness
condition of Stacks 08KT part (1) which `AlgebraicGeometry.Space.IsFlatOverAtPoint` asks on one
such diagram is the very same condition on the very same data. -/
theorem isFlatOverAtPoint_comp_of_isEtale {X Y Z : AlgebraicSpaces B S hS} (a : X ⟶ Y)
    (p : Y ⟶ Z) (hp : IsEtale B S hS p.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    {x : points B S hS X.1} (h : IsFlatOverAtPoint B S hS X.2 a.hom F x) :
    IsFlatOverAtPoint B S hS X.2 (a ≫ p).hom F x := by
  obtain ⟨d, u, hu, hd⟩ := h
  exact ⟨d.postcompTarget B S hS a p hp, u, hu, hd⟩

/-- **Stacks 0CW1 over a base isomorphic to a scheme of the site.** Let `f : X ⟶ Y` be a
morphism of algebraic spaces over `S` with `X` decent and `f` locally of finite type, let `ℱ` be
a finite type quasi-coherent `𝒪_X`-module, let `s` be a point of `Y` at which `ℱ` is flat over
`Y` at every point of the fibre `X_s`, and let `Y` be isomorphic to the algebraic space of a
scheme `T` of the site. Then a point of the relative assassin `Ass_{X/Y}(ℱ)` which specializes
to a point of `X_s` specializes to a point of `Ass_{X/Y}(ℱ)` lying over `s`.

This is `exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_schemeBase` of
`AlgebraicGeometry.Space`, the unconditional Stacks 0CW1 for a base which *is* a scheme of the
site, transported across the isomorphism `e`. Every datum of the statement moves: the morphism
becomes `f ≫ e⁻¹` into `h_T`, which is locally of finite type by Stacks 06LT and
Stacks 03XG; the point of the base
becomes its image under `|e⁻¹|`, and the map on points of `e⁻¹` is injective, so the fibre is
the same set; flatness over the base moves by
`AlgebraicGeometry.Space.isFlatOverAtPoint_comp_of_isEtale`, an isomorphism being étale; and the
relative assassin does not move at all, by Stacks 0CUZ in the form
`AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_comp_iff_of_isEtale`, since
`(f ≫ e⁻¹) ≫ e = f`.

It carries no chart criterion: that hypothesis of
`AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_isFlatOver`
is what the generalization to an arbitrary algebraic-space base needs, and a base isomorphic to
a scheme of the site is not such a generalization. The tag 0CW1 is registered on the
scheme-base statement and is not repeated here. -/
theorem exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_isoSchemeSpace
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (T : BigFppfOver B S hS)
    (e : yoneda.obj T ≅ Y.1) (hXdec : IsDecentSpace B S hS X.1)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] [SheafOfModules.IsFiniteTypeOnSite F]
    (s : points B S hS Y.1)
    (hflat : ∀ t : points B S hS X.1, pointsMap B S hS X.1 f.hom t = s →
      IsFlatOverAtPoint B S hS X.2 f.hom F t)
    {x' : points B S hS X.1} (hx' : IsRelativeWeaklyAssociatedPoint B S hS f F x')
    (hmeets : ∃ t : points B S hS X.1, x' ⤳ t ∧ pointsMap B S hS X.1 f.hom t = s) :
    ∃ x : points B S hS X.1, x' ⤳ x ∧ pointsMap B S hS X.1 f.hom x = s ∧
      IsRelativeWeaklyAssociatedPoint B S hS f F x := by
  have : IsIso e.hom := Iso.isIso_hom e
  have : IsIso e.inv := Iso.isIso_inv e
  -- the base read as the algebraic space of the scheme `T`, in both directions
  let ψ : schemeSpace T ⟶ Y := ObjectProperty.homMk e.hom
  let ψ' : Y ⟶ schemeSpace T := ObjectProperty.homMk e.inv
  have hψhom : ψ.hom = e.hom := rfl
  have hψ'hom : ψ'.hom = e.inv := rfl
  have hψet : IsEtale B S hS ψ.hom := hψhom ▸ isEtale_of_isIso B S hS e.hom
  have hψ'et : IsEtale B S hS ψ'.hom := hψ'hom ▸ isEtale_of_isIso B S hS e.inv
  have hcancel' : ψ'.hom ≫ ψ.hom = 𝟙 Y.1 := by
    rw [hψhom, hψ'hom]; exact e.inv_hom_id
  have hcancel : ψ' ≫ ψ = 𝟙 Y := ObjectProperty.hom_ext _ hcancel'
  have hfψ : (f ≫ ψ') ≫ ψ = f := by rw [Category.assoc, hcancel, Category.comp_id]
  -- the map on points of an isomorphism is injective, so the two fibres are the same set
  have hinj : Function.Injective (pointsMap B S hS Y.1 ψ'.hom) := by
    intro p q hpq
    have h1 : pointsMap B S hS Y.1 (ψ'.hom ≫ ψ.hom) p =
        pointsMap B S hS Y.1 (ψ'.hom ≫ ψ.hom) q := by
      rw [pointsMap_comp_apply, pointsMap_comp_apply, hpq]
    rwa [hcancel', pointsMap_id, id_eq, id_eq] at h1
  have hpt : ∀ t : points B S hS X.1,
      pointsMap B S hS X.1 (f ≫ ψ').hom t = pointsMap B S hS Y.1 ψ'.hom s ↔
        pointsMap B S hS X.1 f.hom t = s := by
    intro t
    have hA : pointsMap B S hS X.1 (f ≫ ψ').hom t =
        pointsMap B S hS Y.1 ψ'.hom (pointsMap B S hS X.1 f.hom t) :=
      pointsMap_comp_apply B S hS f.hom ψ'.hom t
    rw [hA]
    exact hinj.eq_iff
  -- the relative assassin is the same, by Stacks 0CUZ at the isomorphism
  have hass : ∀ z : points B S hS X.1,
      IsRelativeWeaklyAssociatedPoint B S hS f F z ↔
        IsRelativeWeaklyAssociatedPoint B S hS (f ≫ ψ') F z := by
    intro z
    have h := isRelativeWeaklyAssociatedPoint_comp_iff_of_isEtale B S hS (f ≫ ψ') ψ hψet F z
    rwa [hfψ] at h
  obtain ⟨t, hts, htmap⟩ := hmeets
  obtain ⟨x, hspec, hxmap, hxass⟩ :=
    exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_schemeBase B S hS T (f ≫ ψ')
      hXdec
      (isLocallyOfFiniteType_comp B S hS X.2 Y.2 (isAlgebraicSpace_yoneda B S hS T)
        f.hom ψ'.hom hf (isLocallyOfFiniteType_of_isEtale B S hS
          (isAlgebraicSpace_yoneda B S hS T) hψ'et))
      F (pointsMap B S hS Y.1 ψ'.hom s)
      (fun z hz ↦ isFlatOverAtPoint_comp_of_isEtale f ψ' hψ'et F
        (hflat z ((hpt z).1 hz)))
      ((hass x').1 hx') ⟨t, hts, (hpt t).2 htmap⟩
  exact ⟨x, hspec, (hpt x).1 hxmap, (hass x).2 hxass⟩

namespace EtaleOverSource

variable {P : PrePureSituation.{u, u} B S hS} (c : EtaleOverSource P)

/-- A generalization of a point in the image of `|X'| → |X|` lies in that image, the image of an
étale morphism being open (Stacks 03IR). -/
private theorem mem_range_of_specializes {x θ : points B S hS P.X} (hspec : x ⤳ θ)
    (hθ : θ ∈ Set.range (pointsMap B S hS c.X'.1 c.g.hom)) :
    x ∈ Set.range (pointsMap B S hS c.X'.1 c.g.hom) :=
  hspec.mem_open (isOpen_range_pointsMap_of_isEtale B S hS c.g.hom c.X'.2 P.hX c.isEtale) hθ

/-- The source of a situation over a base isomorphic to a scheme of the site is decent. -/
private theorem isDecentSpace_source (T : BigFppfOver B S hS) (e : yoneda.obj T ≅ P.Y) :
    IsDecentSpace B S hS P.X :=
  isDecentSpace_of_isDecent B S hS P.hX P.hY P.f
    (isDecentSpace_of_iso B S hS e (isDecentSpace_yoneda B S hS T)) P.decent

/-- **Stacks 0CW3, clause (2).** In the situation of Stacks 0CV6, let `g : X' ⟶ X` be étale
over `Y` with `X' ⟶ Y` decent and of finite type. If `ℱ` is pure above `y`, the image of
`|X'| → |X|` contains the fibre `F = f^{-1}(\{y\})`, and `Y` is affine local with closed point
`y`, then that image contains the whole relative assassin `Ass_{X/Y}(ℱ)`.

The image of an étale morphism is open on points by Stacks 03IR, and an open set contains
every generalization of each of its points; so it is enough that every point of
`Ass_{X/Y}(ℱ)` specialize to a point of the fibre, which is what purity above `y` gives over
an affine local base, taken here as `hinto`.  This is the auxiliary form: the tag sits on
`relativeWeaklyAssociatedPoints_subset_range_of_isAffineLocalAt`, which discharges `hinto` by
`AlgebraicGeometry.Space.purityFibreSpecialization` and so carries only the source's own
hypotheses. -/
theorem relativeWeaklyAssociatedPoints_subset_range
    (hlocal : P.IsAffineLocalAt) (hpure : IsPureAbove P)
    (hinto : PurityFibreSpecialization P)
    (hfibre : pointsMap B S hS P.X P.f ⁻¹' {P.y} ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom)) :
    relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom) := by
  intro x hx
  obtain ⟨θ, hspec, hθ⟩ := hinto hlocal hpure x hx
  exact c.mem_range_of_specializes hspec (hfibre hθ)

/-- **Stacks 0CW3, clause (2), with nothing granted.** In the situation of Stacks 0CV6, let
`g : X' ⟶ X` be étale over `Y` with `X' ⟶ Y` decent and of finite type. If `ℱ` is pure above
`y`, the image of `|X'| → |X|` contains the fibre `F = f^{-1}(\{y\})`, and `Y` is affine local
with closed point `y`, then that image contains the whole relative assassin `Ass_{X/Y}(ℱ)`.

This is `AlgebraicGeometry.Space.EtaleOverSource.relativeWeaklyAssociatedPoints_subset_range`
with its specialization step discharged by
`AlgebraicGeometry.Space.purityFibreSpecialization`, so that only the source's own hypotheses
remain. -/
@[stacks 0CW3 "clause (2): purity of F above y, the image of |X'| meeting the whole fibre and an \
affine local base with closed point y give the containment of Ass_{X/Y}(F) in that image. Those \
are the source's own three assumptions, and nothing beyond them is used"]
theorem relativeWeaklyAssociatedPoints_subset_range_of_isAffineLocalAt
    (hlocal : P.IsAffineLocalAt) (hpure : IsPureAbove P)
    (hfibre : pointsMap B S hS P.X P.f ⁻¹' {P.y} ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom)) :
    relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom) :=
  c.relativeWeaklyAssociatedPoints_subset_range hlocal hpure
    (purityFibreSpecialization P) hfibre

/-! ### Stacks 0CW3, clause (3), and its morphism-flat analogue -/

/-- **The morphism-flat analogue of Stacks 0CW3, clause (3).** In the situation of
Stacks 0CV6, let `g : X' ⟶ X` be étale over `Y` with `X' ⟶ Y` decent and of finite type. If
`ℱ` is pure above `y`, the morphism `f` is flat at every point of the fibre
`F = f^{-1}(\{y\})`, the image of `|X'| → |X|` contains `Ass_{X/Y}(ℱ) ∩ F`, and `Y` is affine
local with closed point `y`, then that image contains the whole relative assassin
`Ass_{X/Y}(ℱ)`.

This refines clause (2), whose containment hypothesis asks for the whole fibre: here only the
relatively associated part of the fibre has to be met, at the price of flatness along the
fibre. That flatness is exactly what lets Stacks 0CW1,
`AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre`, upgrade a
specialization of a point of `Ass_{X/Y}(ℱ)` into the fibre to a specialization into
`Ass_{X/Y}(ℱ) ∩ F`. The specialization into the fibre is the one purity supplies over an
affine local base, so it is granted here as `hinto`, exactly as in clause (2); the criterion
on an étale scheme chart which is the hypothesis of Stacks 0CW1 is granted as `hchart`. See
`AlgebraicGeometry.Space.PurityFibreSpecialization` and
`AlgebraicGeometry.Space.ChartPurityCriterion`. From the upgraded specialization the
conclusion is reached as in clause (2): the image of an étale morphism is open on points by
Stacks 03IR, and an open set contains every generalization of each of its points.

Decency of `X` as an algebraic space, which Stacks 0CW1 asks for, is not carried. The affine
local base is represented by a scheme of the site, so it is a decent space, and decency of the
morphism of the situation carries that to `X` by Stacks 0ABY. -/
theorem relativeWeaklyAssociatedPoints_subset_range_of_isFlatAt_fibre
    (hlocal : P.IsAffineLocalAt) (hpure : IsPureAbove P)
    (hinto : PurityFibreSpecialization P)
    (hflat : ∀ t : points B S hS P.X, pointsMap B S hS P.X P.f t = P.y →
      IsFlatAt B S hS P.f t)
    (hchart : ChartPurityCriterion B S hS P.structureSpaceMorphism P.F P.y)
    (hfibre : relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F ∩
        pointsMap B S hS P.X P.f ⁻¹' {P.y} ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom)) :
    relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom) := by
  obtain ⟨T, -, -, -, ⟨e⟩⟩ := hlocal.1
  have hXdec := isDecentSpace_source (P := P) T e
  intro x hx
  obtain ⟨θ, hspec, hθy, hθass⟩ :=
    exists_specializes_isRelativeWeaklyAssociatedPoint_fibre B S hS
      P.structureSpaceMorphism hXdec P.finiteType.1 P.F P.y hflat hchart hx
      (hinto hlocal hpure x hx)
  exact c.mem_range_of_specializes hspec (hfibre ⟨hθass, hθy⟩)

/-- **The morphism-flat analogue of Stacks 0CW3, clause (3), with the specialization step
discharged.** In the situation of Stacks 0CV6, let `g : X' ⟶ X` be étale over `Y` with
`X' ⟶ Y` decent and of finite type. If `ℱ` is pure above `y`, the morphism `f` is flat at
every point of the fibre
`F = f^{-1}(\{y\})`, the image of `|X'| → |X|` contains `Ass_{X/Y}(ℱ) ∩ F`, and `Y` is affine
local with closed point `y`, then that image contains the whole relative assassin
`Ass_{X/Y}(ℱ)`.

This is `relativeWeaklyAssociatedPoints_subset_range_of_isFlatAt_fibre` in this namespace
with its specialization step discharged by
`AlgebraicGeometry.Space.purityFibreSpecialization`. The criterion on an étale scheme chart
which is the hypothesis of the library's Stacks 0CW1 is still granted as `hchart`, and the
flatness hypothesis is still flatness of the morphism, Stacks 03ML(2), rather than of the
module `ℱ` over `Y` along the fibre, which the source asks for; the two agree for `ℱ = 𝒪_X`
and are incomparable in general.

Because those two flatness conditions are incomparable, this statement does **not** imply
clause (3) of [Stacks, Tag 0CW3], and it deliberately carries no `@[stacks 0CW3]` attribute: it
is the morphism-flat analogue of that clause, not that clause. Tagging it would assert a
statement of the source that is not proved. Clause (3) itself, with the source's own flatness
hypothesis, is
`relativeWeaklyAssociatedPoints_subset_range_of_isFlatOver_fibre_of_isAffineLocalAt` in this
namespace, stated through `AlgebraicGeometry.Space.IsFlatOverAtPoint`. -/
theorem relativeWeaklyAssociatedPoints_subset_range_of_isFlatAt_fibre_of_isAffineLocalAt
    (hlocal : P.IsAffineLocalAt) (hpure : IsPureAbove P)
    (hflat : ∀ t : points B S hS P.X, pointsMap B S hS P.X P.f t = P.y →
      IsFlatAt B S hS P.f t)
    (hchart : ChartPurityCriterion B S hS P.structureSpaceMorphism P.F P.y)
    (hfibre : relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F ∩
        pointsMap B S hS P.X P.f ⁻¹' {P.y} ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom)) :
    relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom) :=
  c.relativeWeaklyAssociatedPoints_subset_range_of_isFlatAt_fibre hlocal hpure
    (purityFibreSpecialization P) hflat hchart hfibre

/-- **Stacks 0CW3, clause (3).** In the situation of Stacks 0CV6, let `g : X' ⟶ X` be étale
over `Y` with `X' ⟶ Y` decent and of finite type. If `ℱ` is pure above `y`, `ℱ` is flat over
`Y` at every point of the fibre `F = f^{-1}(\{y\})`, the image of `|X'| → |X|` contains
`Ass_{X/Y}(ℱ) ∩ F`, and `Y` is affine local with closed point `y`, then that image contains
the whole relative assassin `Ass_{X/Y}(ℱ)`.

This is the source's clause (3): its flatness hypothesis is flatness of the *module* `ℱ` over
`Y` at the points of the fibre — `AlgebraicGeometry.Space.IsFlatOverAtPoint`, Stacks 05VV at a
point in the some-chart form which is condition (1) of Stacks 05VU — which is what the source
asks for, and not flatness of the morphism `f`.

The clause refines clause (2), whose containment hypothesis asks for the whole fibre: here only
the relatively associated part of the fibre has to be met, at the price of flatness along the
fibre. That flatness is exactly what lets Stacks 0CW1 upgrade a specialization of a point of
`Ass_{X/Y}(ℱ)` into the fibre to a specialization into `Ass_{X/Y}(ℱ) ∩ F`. The form of
Stacks 0CW1 used is
`exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_isoSchemeSpace` of
`AlgebraicGeometry.Space`, the unconditional scheme-base lemma transported across the
isomorphism which exhibits the base as the algebraic space of a scheme of the site; being
affine local, the base supplies exactly that isomorphism, so nothing is granted. The
specialization into the fibre is the one purity supplies over an affine local base, so it is
granted here as `hinto`, exactly as in clause (2);
see `AlgebraicGeometry.Space.PurityFibreSpecialization`. From the upgraded specialization the
conclusion is reached as in clause (2): the image of an étale morphism is open on points by
Stacks 03IR, and an open set contains every generalization of each of its points.

Decency of `X` as an algebraic space, which Stacks 0CW1 asks for, is not carried. The affine
local base is represented by a scheme of the site, so it is a decent space, and decency of the
morphism of the situation carries that to `X` by Stacks 0ABY.

This is the auxiliary form: the tag sits on
`relativeWeaklyAssociatedPoints_subset_range_of_isFlatOver_fibre_of_isAffineLocalAt`, which
discharges `hinto` and so carries only the source's own hypotheses. -/
theorem relativeWeaklyAssociatedPoints_subset_range_of_isFlatOver_fibre
    (hlocal : P.IsAffineLocalAt) (hpure : IsPureAbove P)
    (hinto : PurityFibreSpecialization P)
    (hflat : ∀ t : points B S hS P.X, pointsMap B S hS P.X P.f t = P.y →
      IsFlatOverAtPoint B S hS P.hX P.f P.F t)
    (hfibre : relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F ∩
        pointsMap B S hS P.X P.f ⁻¹' {P.y} ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom)) :
    relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom) := by
  obtain ⟨T, -, -, -, ⟨e⟩⟩ := hlocal.1
  have hXdec := isDecentSpace_source (P := P) T e
  intro x hx
  obtain ⟨θ, hspec, hθy, hθass⟩ :=
    exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_isoSchemeSpace
      P.structureSpaceMorphism T e hXdec P.finiteType.1 P.F P.y hflat hx
      (hinto hlocal hpure x hx)
  exact c.mem_range_of_specializes hspec (hfibre ⟨hθass, hθy⟩)

/-- **Stacks 0CW3, clause (3), with nothing granted.** In the situation of Stacks 0CV6, let
`g : X' ⟶ X` be étale over `Y` with `X' ⟶ Y` decent and of finite type. If `ℱ` is pure above
`y`, `ℱ` is flat over `Y` at every point of the fibre `F = f^{-1}(\{y\})`, the image of
`|X'| → |X|` contains `Ass_{X/Y}(ℱ) ∩ F`, and `Y` is affine local with closed point `y`, then
that image contains the whole relative assassin `Ass_{X/Y}(ℱ)`.

The flatness hypothesis is the source's own: flatness of the *module* `ℱ` over `Y` at the
points of the fibre, `AlgebraicGeometry.Space.IsFlatOverAtPoint`, Stacks 05VV at a point in the
some-chart form which is condition (1) of Stacks 05VU — and not flatness of the morphism `f`,
which is the incomparable condition of
`relativeWeaklyAssociatedPoints_subset_range_of_isFlatAt_fibre_of_isAffineLocalAt` in this
namespace.

This is `relativeWeaklyAssociatedPoints_subset_range_of_isFlatOver_fibre` in this namespace
with its specialization step discharged by
`AlgebraicGeometry.Space.purityFibreSpecialization`, so that nothing beyond the source's own
hypotheses is assumed. -/
@[stacks 0CW3 "clause (3): purity of F above y, flatness of the module F over Y at the points of \
the fibre, the image of |X'| meeting Ass_{X/Y}(F) cap F and an affine local base with closed \
point y give the containment of Ass_{X/Y}(F) in that image. Those are the source's own four \
assumptions, and nothing beyond them is used"]
theorem relativeWeaklyAssociatedPoints_subset_range_of_isFlatOver_fibre_of_isAffineLocalAt
    (hlocal : P.IsAffineLocalAt) (hpure : IsPureAbove P)
    (hflat : ∀ t : points B S hS P.X, pointsMap B S hS P.X P.f t = P.y →
      IsFlatOverAtPoint B S hS P.hX P.f P.F t)
    (hfibre : relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F ∩
        pointsMap B S hS P.X P.f ⁻¹' {P.y} ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom)) :
    relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom) :=
  c.relativeWeaklyAssociatedPoints_subset_range_of_isFlatOver_fibre hlocal hpure
    (purityFibreSpecialization P) hflat hfibre

end EtaleOverSource

end Specialization

end AlgebraicGeometry.Space

end
