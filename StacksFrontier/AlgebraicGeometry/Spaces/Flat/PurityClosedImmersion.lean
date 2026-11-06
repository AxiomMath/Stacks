module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceFiniteDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.RelativelyPureModules
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperComposition

/-!
# Purity of a module supported on a closed subspace

In the standing situation of Stacks 0CV6 — a finite type decent morphism `f : X ⟶ Y` of
algebraic spaces, a finite type quasi-coherent `𝒪_X`-module `ℱ` and a point `y` of `Y` — let
`i : Z ⟶ X` be a closed immersion and suppose `ℱ = i_*𝒢` for a finite type quasi-coherent
`𝒪_Z`-module `𝒢`. Then `𝒢` is pure above `y` exactly when `ℱ` is, and `𝒢` is universally pure
above `y` exactly when `ℱ` is.

The reason is that an impurity of `𝒢` above `y` and an impurity of `ℱ` above `y` carry the same
data. On the base change along a morphism `T ⟶ Y` the closed immersion becomes a closed
immersion `Z_T ⟶ X_T` whose relative weak assassin carries over: the relative weak assassin of
`ℱ_T = (i_T)_*𝒢_T` is the image of that of `𝒢_T` by Stacks 0CV4, and the image under `Z_T ⟶ X_T`
of the closure of a point is the closure of its image, that morphism being a closed embedding on
points.

## Main definitions

* `AlgebraicGeometry.Space.PrePureSituation.baseChangeSpace`, its two projections
  `AlgebraicGeometry.Space.PrePureSituation.baseChangeToBase` and
  `AlgebraicGeometry.Space.PrePureSituation.baseChangeToSource`, and
  `AlgebraicGeometry.Space.PrePureSituation.baseChangeModule`: the base change `X_T = T ×_Y X`
  of a situation along a morphism from a scheme of the site, and the restriction of its module.
* `AlgebraicGeometry.Space.ClosedSubspaceModule`: the hypothesis of Stacks 0CVH, a closed
  immersion into the source of a situation together with a finite type quasi-coherent module
  whose direct image is the module of the situation.
* `AlgebraicGeometry.Space.ClosedSubspaceModule.situation`: the pre-pure situation it induces
  on the closed subspace.
* `AlgebraicGeometry.Space.ClosedSubspaceModule.baseChangeImmersion`: the induced closed
  immersion `Z_T ⟶ X_T` of base changes.
* `AlgebraicGeometry.Space.ClosedSubspaceModule.BaseChangeInput`: the input on those base
  changes that the source's one-line appeal to Stacks 0CV4 hides.

## Main results

* `AlgebraicGeometry.Space.isDecent_of_isClosedImmersion`: a closed immersion of algebraic
  spaces is a decent morphism.
* `AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_congr` and
  `AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints_congr`: isomorphic modules have the
  same relative weak assassin.
* `AlgebraicGeometry.Space.ImpurityDiagram.isRelativeWeakAssassinPoint_iff`: the relative weak
  assassin condition of an impurity diagram is the relative weak assassin of Stacks 0CV0 for
  the projection `X_T ⟶ T`.
* `AlgebraicGeometry.Space.ClosedSubspaceModule.relativeWeaklyAssociatedPoints_baseChangeModule`:
  **Stacks 0CV4 on the base changes of the situation**, the heart of the proof.
* `AlgebraicGeometry.Space.ClosedSubspaceModule.isImpurity_alongClosedImmersion_iff` and
  `AlgebraicGeometry.Space.ClosedSubspaceModule.exists_isImpurity_iff`: an impurity of `𝒢`
  above `y` and an impurity of `ℱ` above `y` are the same thing, with the same structure
  morphism and the same point of `T`.
* `AlgebraicGeometry.Space.ClosedSubspaceModule.isPureAbove_situation_iff` and
  `AlgebraicGeometry.Space.ClosedSubspaceModule.isUniversallyPureAbove_situation_iff`:
  **Stacks 0CVH**, for purity above `y` and for universal purity above `y`.

## Implementation notes

The situation on the closed subspace is the composite `Z ⟶ X ⟶ Y`, which is of finite type by
Stacks 03XG because a closed immersion is of finite type, and decent by Stacks 03L1 because a
closed immersion is a decent morphism — the latter is
`AlgebraicGeometry.Space.isDecent_of_isClosedImmersion` below, Stacks 03KF for the represented
base changes of a representable morphism.

The base changes are taken on the chosen fibre products, matching
`AlgebraicGeometry.Space.ImpurityDiagram.baseChange`, so that the base change of a situation
along the structure morphism of an impurity diagram is the total space of that diagram on the
nose. The induced morphism `Z_T ⟶ X_T` is read off the comparison
`CategoryTheory.Limits.pullbackLeftPullbackSndIso` of `(T ×_Y X) ×_X Z` with `T ×_Y Z`, which
also exhibits it as a base change of `i` and hence as a closed immersion by Stacks 02YW.

The single input collected in
`AlgebraicGeometry.Space.ClosedSubspaceModule.BaseChangeInput` is affine base change for
`X_T ⟶ X`, which identifies the restriction of `i_*𝒢` to `X_T` with the direct image along
`Z_T ⟶ X_T` of the restriction of `𝒢`; the library has that comparison, as an isomorphism of
modules, only for an étale base change. Stacks 0CV4 itself is unconditional, and so is the
affine case of Stacks 0CU9 it rests on. Quasi-coherence of the restrictions of `𝒢` is
Stacks 03GA, in the form
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`, and so
is no longer an input either.

## References

* [Stacks Project, Tag 0CVH](https://stacks.math.columbia.edu/tag/0CVH)
* [Stacks Project, Tag 0CV6](https://stacks.math.columbia.edu/tag/0CV6)
* [Stacks Project, Tag 0CVD](https://stacks.math.columbia.edu/tag/0CVD)
* [Stacks Project, Tag 0CV4](https://stacks.math.columbia.edu/tag/0CV4)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/- Instance search for pullbacks of presheaves on `BigFppfOver B S hS` times out under Lean
v4.35.0; supply the functor-category instance. -/
local instance (priority := high) : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

local instance (priority := high) {Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ W)
    (g : Z ⟶ W) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

local instance (priority := high) {J : Type} :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

/-! ### A closed immersion is a decent morphism -/

/-- A base change of a closed immersion of algebraic spaces over `S` is a closed immersion
(Stacks 02YW). -/
private theorem isClosedImmersion_fst_of_isPullback
    {W X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {fst : W ⟶ X} {snd : W ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (h : IsPullback fst snd f g) (hg : IsClosedImmersion B S hS g) :
    IsClosedImmersion B S hS fst :=
  (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback h.flip hg

/-- **A closed immersion of algebraic spaces over `S` is a decent morphism.** Every base change
of it along a morphism from a scheme of the site is again a closed immersion by Stacks 02YW,
hence representable, so its source is a decent algebraic space by Stacks 03KF because the
scheme is one. -/
theorem isDecent_of_isClosedImmersion {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X) (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i) :
    IsDecent B S hS i := by
  intro T g
  exact isDecentSpace_of_relativelyRepresentable B S hS
    (isAlgebraicSpace_pullback B S hS g i (isAlgebraicSpace_yoneda B S hS T) hZ hX)
    (pullback.fst g i)
    (isClosedImmersion_fst_of_isPullback B S hS (IsPullback.of_hasPullback g i) hi).1
    (isDecentSpace_yoneda B S hS T)

/-! ### The relative weak assassin and isomorphisms of modules -/

variable {B S hS}

/-- Isomorphic `𝒪_X`-modules have the same relative weak assassin: the two restrictions to a
fibre of `f` are isomorphic, and weak association only depends on the isomorphism class. -/
theorem isRelativeWeaklyAssociatedPoint_congr {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {F F' : Modules.{u, u} B S hS X.1 X.2} (e : F ≅ F') (x : points B S hS X.1) :
    IsRelativeWeaklyAssociatedPoint B S hS f F x ↔
      IsRelativeWeaklyAssociatedPoint B S hS f F' x := by
  unfold IsRelativeWeaklyAssociatedPoint
  exact exists_congr fun p => and_congr_right fun _ => exists_congr fun θ =>
    and_congr_right fun _ => isWeaklyAssociatedPoint_congr B S hS
      ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f p)).mapIso e) θ

/-- Isomorphic `𝒪_X`-modules have the same relative weak assassin `WeakAss_{X/Y}(-)`. -/
theorem relativeWeaklyAssociatedPoints_congr {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {F F' : Modules.{u, u} B S hS X.1 X.2} (e : F ≅ F') :
    relativeWeaklyAssociatedPoints B S hS f F = relativeWeaklyAssociatedPoints B S hS f F' :=
  Set.ext fun x => isRelativeWeaklyAssociatedPoint_congr f e x

/-! ### Base changes of a pre-pure situation -/

namespace PrePureSituation

variable (P : PrePureSituation.{u, u} B S hS)

/-- The base change `X_T = T ×_Y X` of the source of a pre-pure situation along a morphism from
a scheme of the site, as an algebraic space. This is the total space of an impurity diagram
with structure morphism `g`. -/
noncomputable abbrev baseChangeSpace (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ P.Y) :
    AlgebraicSpaces B S hS :=
  ⟨pullback g P.f,
    isAlgebraicSpace_pullback B S hS g P.f (isAlgebraicSpace_yoneda B S hS T) P.hX P.hY⟩

/-- The projection `X_T ⟶ T`, a base change of the morphism of the situation. -/
noncomputable abbrev baseChangeToBase (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ P.Y) :
    P.baseChangeSpace T g ⟶ (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ :
      AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (pullback.fst g P.f)

/-- The projection `X_T ⟶ X` onto the source of the situation. -/
noncomputable abbrev baseChangeToSource (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ P.Y) :
    P.baseChangeSpace T g ⟶ (⟨P.X, P.hX⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (pullback.snd g P.f)

/-- The restriction `ℱ_T` to `X_T` of the module of the situation. -/
noncomputable abbrev baseChangeModule (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ P.Y) :
    Modules.{u, u} B S hS (P.baseChangeSpace T g).1 (P.baseChangeSpace T g).2 :=
  (modulePullback B S hS (P.baseChangeToSource T g)).obj P.F

end PrePureSituation

/-- The relative weak assassin condition of an impurity diagram is the relative weak assassin
of Stacks 0CV0 for the projection `X_T ⟶ T`. -/
theorem ImpurityDiagram.isRelativeWeakAssassinPoint_iff {P : PrePureSituation.{u, u} B S hS}
    (D : ImpurityDiagram P) (x : points B S hS D.baseChange) :
    D.IsRelativeWeakAssassinPoint x ↔
      IsRelativeWeaklyAssociatedPoint B S hS (P.baseChangeToBase D.T D.g)
        (P.baseChangeModule D.T D.g) x :=
  Iff.rfl

/-! ### A module pushed forward along a closed immersion -/

/-- **The hypothesis of Stacks 0CVH**: a closed immersion `i : Z ⟶ X` into the source of a
pre-pure situation, together with a finite type quasi-coherent `𝒪_Z`-module `𝒢` whose direct
image `i_*𝒢` is the module `ℱ` of the situation. -/
structure ClosedSubspaceModule (P : PrePureSituation.{u, u} B S hS) where
  /-- The closed subspace of the source. -/
  Z : AlgebraicSpaces B S hS
  /-- The morphism to the source of the situation. -/
  i : Z ⟶ (⟨P.X, P.hX⟩ : AlgebraicSpaces B S hS)
  /-- It is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion B S hS i.hom
  /-- The module on the closed subspace. -/
  G : Modules.{u, u} B S hS Z.1 Z.2
  /-- It is of finite type. -/
  moduleFiniteType : SheafOfModules.IsFiniteTypeOnSite G
  /-- It is quasi-coherent. -/
  moduleQuasicoherent : G.IsQuasicoherentOnSite
  /-- The module of the situation is the direct image of `G`. -/
  iso : P.F ≅ (modulePushforward B S hS i).obj G

namespace ClosedSubspaceModule

variable {P : PrePureSituation.{u, u} B S hS} (c : ClosedSubspaceModule P)

/-- **The pre-pure situation on the closed subspace**: the composite `Z ⟶ X ⟶ Y`, which is of
finite type by Stacks 03XG and decent by Stacks 03L1 because a closed immersion is both, with
the module `𝒢` and the same point of the target. -/
@[reducible] noncomputable def situation : PrePureSituation.{u, u} B S hS where
  X := c.Z.1
  hX := c.Z.2
  Y := P.Y
  hY := P.hY
  f := c.i.hom ≫ P.f
  finiteType := isFiniteType_comp B S hS c.Z.2 P.hX P.hY c.i.hom P.f
    (isFiniteType_of_isClosedImmersion B S hS c.i.hom c.isClosedImmersion) P.finiteType
  decent := isDecent_comp B S hS c.Z.2 P.hX P.hY c.i.hom P.f
    (isDecent_of_isClosedImmersion B S hS c.Z.2 P.hX c.i.hom c.isClosedImmersion) P.decent
  F := c.G
  moduleFiniteType := c.moduleFiniteType
  moduleQuasicoherent := c.moduleQuasicoherent
  y := P.y

/-! ### The induced closed immersion of base changes -/

/-- The induced morphism `Z_T ⟶ X_T` of base changes, read off the comparison of
`(T ×_Y X) ×_X Z` with `T ×_Y Z`. -/
noncomputable def baseChangeImmersion (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ P.Y) :
    c.situation.baseChangeSpace T g ⟶ P.baseChangeSpace T g :=
  ObjectProperty.homMk ((pullbackLeftPullbackSndIso g P.f c.i.hom).inv ≫
    pullback.fst (pullback.snd g P.f) c.i.hom)

variable (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ P.Y)

/-- The induced morphism of base changes is compatible with the projections to `T`. -/
theorem baseChangeImmersion_hom_comp_fst :
    (c.baseChangeImmersion T g).hom ≫ pullback.fst g P.f =
      pullback.fst g (c.i.hom ≫ P.f) := by
  change ((pullbackLeftPullbackSndIso g P.f c.i.hom).inv ≫
    pullback.fst (pullback.snd g P.f) c.i.hom) ≫ pullback.fst g P.f = _
  rw [Category.assoc]
  exact pullbackLeftPullbackSndIso_inv_fst g P.f c.i.hom

/-- The induced morphism of base changes is compatible with the projections to the source of
the situation and the closed immersion. -/
theorem baseChangeImmersion_hom_comp_snd :
    (c.baseChangeImmersion T g).hom ≫ pullback.snd g P.f =
      pullback.snd g (c.i.hom ≫ P.f) ≫ c.i.hom := by
  change ((pullbackLeftPullbackSndIso g P.f c.i.hom).inv ≫
    pullback.fst (pullback.snd g P.f) c.i.hom) ≫ pullback.snd g P.f = _
  rw [Category.assoc]
  exact pullbackLeftPullbackSndIso_inv_fst_snd g P.f c.i.hom

/-- The induced morphism of base changes is compatible with the projections to `T`, as a
morphism of algebraic spaces. -/
theorem baseChangeImmersion_comp_toBase :
    c.baseChangeImmersion T g ≫ P.baseChangeToBase T g =
      c.situation.baseChangeToBase T g :=
  ObjectProperty.hom_ext _ (c.baseChangeImmersion_hom_comp_fst T g)

/-- The square exhibiting `Z_T ⟶ X_T` as a base change of the closed immersion. -/
theorem isPullback_baseChangeImmersion :
    IsPullback (c.baseChangeImmersion T g).hom (pullback.snd g (c.i.hom ≫ P.f))
      (pullback.snd g P.f) c.i.hom :=
  IsPullback.of_iso_pullback ⟨c.baseChangeImmersion_hom_comp_snd T g⟩
    (pullbackLeftPullbackSndIso g P.f c.i.hom).symm rfl
    (pullbackLeftPullbackSndIso_inv_snd_snd g P.f c.i.hom)

/-- **Stacks 02YW.** The induced morphism `Z_T ⟶ X_T` of base changes is a closed immersion,
being a base change of `i`. -/
theorem isClosedImmersion_baseChangeImmersion :
    IsClosedImmersion B S hS (c.baseChangeImmersion T g).hom :=
  isClosedImmersion_fst_of_isPullback B S hS (c.isPullback_baseChangeImmersion T g)
    c.isClosedImmersion

/-- **Stacks 081Y.** The induced morphism `Z_T ⟶ X_T` of base changes is finite. -/
theorem isFinite_baseChangeImmersion :
    IsFinite B S hS (c.baseChangeImmersion T g).hom :=
  isFinite_of_isClosedImmersion B S hS _ (c.isClosedImmersion_baseChangeImmersion T g)

/-- The induced morphism `Z_T ⟶ X_T` of base changes is injective on points. -/
theorem injective_pointsMap_baseChangeImmersion :
    Function.Injective (pointsMap B S hS (c.situation.baseChangeSpace T g).1
      (c.baseChangeImmersion T g).hom) :=
  injective_pointsMap_of_isImmersion B S hS (P.baseChangeSpace T g).2 _
    (isImmersion_of_isClosedImmersion B S hS (c.isClosedImmersion_baseChangeImmersion T g))

section Topology

attribute [local instance] pointTopology

/-- The induced morphism `Z_T ⟶ X_T` of base changes is a closed embedding on points: it is an
embedding because it is an immersion, and its image is closed because it is a closed
immersion. -/
theorem isClosedEmbedding_pointsMap_baseChangeImmersion :
    Topology.IsClosedEmbedding (pointsMap B S hS (c.situation.baseChangeSpace T g).1
      (c.baseChangeImmersion T g).hom) := by
  have hi := c.isClosedImmersion_baseChangeImmersion T g
  have him := isImmersion_of_isClosedImmersion B S hS hi
  exact
    { toIsEmbedding := isEmbedding_pointsMap_of_isImmersion B S hS (P.baseChangeSpace T g).2 _ him
      isClosed_range :=
        (isClosedImmersion_iff_isClosed_range_pointsMap B S hS (P.baseChangeSpace T g).2 _
          him).1 hi }

/-- The image in `T` of the closure of a point of `Z_T` is the image in `T` of the closure of
its image in `X_T`: the induced morphism of base changes is a closed embedding on points, so it
carries the closure of a point to the closure of its image. -/
theorem image_closure_singleton_baseChangeImmersion
    (ζ : points B S hS (c.situation.baseChangeSpace T g).1) :
    pointsMap B S hS (pullback g P.f) (pullback.fst g P.f) ''
        closure {pointsMap B S hS (c.situation.baseChangeSpace T g).1
                  (c.baseChangeImmersion T g).hom ζ} =
      pointsMap B S hS (pullback g (c.i.hom ≫ P.f)) (pullback.fst g (c.i.hom ≫ P.f)) ''
        closure {ζ} := by
  have hclosure : closure {pointsMap B S hS (c.situation.baseChangeSpace T g).1
                            (c.baseChangeImmersion T g).hom ζ} =
      pointsMap B S hS (c.situation.baseChangeSpace T g).1
        (c.baseChangeImmersion T g).hom '' closure {ζ} := by
    rw [← Set.image_singleton (f := pointsMap B S hS (c.situation.baseChangeSpace T g).1
      (c.baseChangeImmersion T g).hom)]
    exact (c.isClosedEmbedding_pointsMap_baseChangeImmersion T g).closure_image_eq _
  rw [hclosure, ← Set.image_comp, ← pointsMap_comp,
    c.baseChangeImmersion_hom_comp_fst T g]

end Topology

/-! ### The inputs on the base changes -/

/-- The input on the base changes of the situation that the source's one-line appeal to
Stacks 0CV4 hides in this library: affine base change for `X_T ⟶ X`, identifying the
restriction of `i_*𝒢` to `X_T` with the direct image along `Z_T ⟶ X_T` of `𝒢_T`. The library has
that comparison, as an isomorphism of modules, only for an étale base change. -/
structure BaseChangeInput : Prop where
  /-- **Affine base change, Stacks 02KG**, for `X_T ⟶ X`: the restriction of `i_*𝒢` to `X_T`
  is the direct image along `Z_T ⟶ X_T` of the restriction of `𝒢` to `Z_T`. -/
  directImage : ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ P.Y),
    Nonempty
      ((modulePullback B S hS (P.baseChangeToSource T g)).obj
          ((modulePushforward B S hS c.i).obj c.G) ≅
        (modulePushforward B S hS (c.baseChangeImmersion T g)).obj
          (c.situation.baseChangeModule T g))

/-! ### The relative weak assassin on the base changes -/

/-- **Stacks 0CV4 on the base changes of the situation.** The relative weak assassin
`WeakAss_{X_T/T}(ℱ_T)` is the image under `Z_T ⟶ X_T` of `WeakAss_{Z_T/T}(𝒢_T)`.

The module `ℱ_T` is the direct image along `Z_T ⟶ X_T` of `𝒢_T`, by the hypothesis `ℱ = i_*𝒢`
and affine base change, and `Z_T ⟶ X_T` is a closed immersion, hence finite. -/
theorem relativeWeaklyAssociatedPoints_baseChangeModule
    (hin : c.BaseChangeInput) :
    relativeWeaklyAssociatedPoints B S hS (P.baseChangeToBase T g) (P.baseChangeModule T g) =
      pointsMap B S hS (c.situation.baseChangeSpace T g).1 (c.baseChangeImmersion T g).hom ''
        relativeWeaklyAssociatedPoints B S hS (c.situation.baseChangeToBase T g)
          (c.situation.baseChangeModule T g) := by
  have hqc : (c.situation.baseChangeModule T g).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ c.G
      c.moduleQuasicoherent
  have key := relativeWeaklyAssociatedPoints_modulePushforward_eq_image_of_isFinite B S hS
    (P.baseChangeToBase T g) (c.baseChangeImmersion T g) (c.isFinite_baseChangeImmersion T g)
    (c.situation.baseChangeModule T g) hqc
  have α : P.baseChangeModule T g ≅
      (modulePushforward B S hS (c.baseChangeImmersion T g)).obj
        (c.situation.baseChangeModule T g) :=
    (modulePullback B S hS (P.baseChangeToSource T g)).mapIso c.iso ≪≫
      (hin.directImage T g).some
  rw [relativeWeaklyAssociatedPoints_congr (P.baseChangeToBase T g) α, key,
    c.baseChangeImmersion_comp_toBase T g]

/-- A relative weak assassin point of `ℱ_T` is the image of a relative weak assassin point of
`𝒢_T`, and conversely. -/
theorem isRelativeWeaklyAssociatedPoint_baseChangeImmersion_iff
    (hin : c.BaseChangeInput)
    (ζ : points B S hS (c.situation.baseChangeSpace T g).1) :
    IsRelativeWeaklyAssociatedPoint B S hS (P.baseChangeToBase T g) (P.baseChangeModule T g)
        (pointsMap B S hS (c.situation.baseChangeSpace T g).1
          (c.baseChangeImmersion T g).hom ζ) ↔
      IsRelativeWeaklyAssociatedPoint B S hS (c.situation.baseChangeToBase T g)
        (c.situation.baseChangeModule T g) ζ := by
  have hset := c.relativeWeaklyAssociatedPoints_baseChangeModule T g hin
  constructor
  · intro hx
    have hmem : pointsMap B S hS (c.situation.baseChangeSpace T g).1
        (c.baseChangeImmersion T g).hom ζ ∈
        relativeWeaklyAssociatedPoints B S hS (P.baseChangeToBase T g)
          (P.baseChangeModule T g) := hx
    rw [hset] at hmem
    obtain ⟨ζ', hζ', hζ'eq⟩ := hmem
    exact c.injective_pointsMap_baseChangeImmersion T g hζ'eq ▸ hζ'
  · intro hζ
    have hmem : pointsMap B S hS (c.situation.baseChangeSpace T g).1
        (c.baseChangeImmersion T g).hom ζ ∈
        pointsMap B S hS (c.situation.baseChangeSpace T g).1
            (c.baseChangeImmersion T g).hom ''
          relativeWeaklyAssociatedPoints B S hS (c.situation.baseChangeToBase T g)
            (c.situation.baseChangeModule T g) := ⟨ζ, hζ, rfl⟩
    rwa [← hset] at hmem

/-- Every relative weak assassin point of `ℱ_T` comes from one of `𝒢_T`. -/
theorem exists_isRelativeWeaklyAssociatedPoint
    (hin : c.BaseChangeInput)
    (x : points B S hS (P.baseChangeSpace T g).1)
    (hx : IsRelativeWeaklyAssociatedPoint B S hS (P.baseChangeToBase T g)
      (P.baseChangeModule T g) x) :
    ∃ ζ : points B S hS (c.situation.baseChangeSpace T g).1,
      pointsMap B S hS (c.situation.baseChangeSpace T g).1
          (c.baseChangeImmersion T g).hom ζ = x ∧
        IsRelativeWeaklyAssociatedPoint B S hS (c.situation.baseChangeToBase T g)
          (c.situation.baseChangeModule T g) ζ := by
  have hmem : x ∈ relativeWeaklyAssociatedPoints B S hS (P.baseChangeToBase T g)
      (P.baseChangeModule T g) := hx
  rw [c.relativeWeaklyAssociatedPoints_baseChangeModule T g hin] at hmem
  obtain ⟨ζ, hζ, hζeq⟩ := hmem
  exact ⟨ζ, hζeq, hζ⟩

/-! ### Impurities -/

section Impurity

attribute [local instance] pointTopology

/-- An impurity diagram of the situation on the closed subspace, read as an impurity diagram of
the original situation: the structure morphism and the points of `T` are unchanged, and the
distinguished point of `Z_T` is carried to `X_T` along the induced closed immersion. -/
@[reducible] noncomputable def alongClosedImmersion (E : ImpurityDiagram c.situation) :
    ImpurityDiagram P where
  T := E.T
  g := E.g
  t' := E.t'
  t := E.t
  specializes := E.specializes
  mapsToChosenPoint := E.mapsToChosenPoint
  xi := pointsMap B S hS (c.situation.baseChangeSpace E.T E.g).1
    (c.baseChangeImmersion E.T E.g).hom E.xi
  xi_liesOver := by
    rw [← pointsMap_comp_apply, c.baseChangeImmersion_hom_comp_fst E.T E.g]
    exact E.xi_liesOver

/-- **An impurity of `𝒢` above `y` is exactly an impurity of `ℱ = i_*𝒢` above `y`.** The
relative weak assassin of `ℱ_T` is the image of that of `𝒢_T` by Stacks 0CV4, and the image in
`T` of the closure of the distinguished point is unchanged because `Z_T ⟶ X_T` is a closed
embedding on points. -/
theorem isImpurity_alongClosedImmersion_iff
    (hin : c.BaseChangeInput)
    (E : ImpurityDiagram c.situation) :
    (c.alongClosedImmersion E).IsImpurity ↔ E.IsImpurity := by
  have hass : (c.alongClosedImmersion E).IsRelativeWeakAssassinPoint
      (c.alongClosedImmersion E).xi ↔ E.IsRelativeWeakAssassinPoint E.xi :=
    ((c.alongClosedImmersion E).isRelativeWeakAssassinPoint_iff _).trans
      ((c.isRelativeWeaklyAssociatedPoint_baseChangeImmersion_iff E.T E.g hin E.xi).trans
        (E.isRelativeWeakAssassinPoint_iff E.xi).symm)
  have himg := c.image_closure_singleton_baseChangeImmersion E.T E.g E.xi
  unfold ImpurityDiagram.IsImpurity
  exact and_congr hass (by rw [himg])

/-- **An impurity of `𝒢` above `y` with a prescribed structure morphism and point of `T` is
exactly such an impurity of `ℱ = i_*𝒢`.** The property of the structure morphism and the point
is arbitrary, so this covers both purity above `y` — where the structure morphism is required to
be quasi-finite at the point — and universal purity above `y`. -/
theorem exists_isImpurity_iff
    (hin : c.BaseChangeInput)
    (Q : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ P.Y) → points B S hS (yoneda.obj T) → Prop) :
    (∃ E : ImpurityDiagram c.situation, Q E.T E.g E.t ∧ E.IsImpurity) ↔
      ∃ D : ImpurityDiagram P, Q D.T D.g D.t ∧ D.IsImpurity := by
  constructor
  · rintro ⟨E, hQ, hE⟩
    exact ⟨c.alongClosedImmersion E, hQ,
      (c.isImpurity_alongClosedImmersion_iff hin E).2 hE⟩
  · rintro ⟨D, hQ, hD⟩
    obtain ⟨ζ, hζeq, hζ⟩ := c.exists_isRelativeWeaklyAssociatedPoint D.T D.g hin D.xi
      ((D.isRelativeWeakAssassinPoint_iff D.xi).1 hD.1)
    have hxi : pointsMap B S hS (pullback D.g (c.i.hom ≫ P.f))
        (pullback.fst D.g (c.i.hom ≫ P.f)) ζ = D.t' := by
      rw [← c.baseChangeImmersion_hom_comp_fst D.T D.g, pointsMap_comp_apply, hζeq]
      exact D.xi_liesOver
    have himg := c.image_closure_singleton_baseChangeImmersion D.T D.g ζ
    rw [hζeq] at himg
    refine ⟨{ T := D.T
              g := D.g
              t' := D.t'
              t := D.t
              specializes := D.specializes
              mapsToChosenPoint := D.mapsToChosenPoint
              xi := ζ
              xi_liesOver := hxi }, hQ, hζ, fun hmem => hD.2 ?_⟩
    rw [himg]
    exact hmem

/-! ### Stacks 0CVH -/

/-- **Stacks 0CVH, purity above `y`.** In the situation of Stacks 0CV6, let `i : Z ⟶ X` be a
closed immersion and suppose `ℱ = i_*𝒢` for a finite type quasi-coherent `𝒪_Z`-module `𝒢`.
Then `𝒢` is pure above `y` exactly when `ℱ` is.

An impurity of `𝒢` above `y` whose structure morphism is quasi-finite at `t` is such an impurity
of `ℱ` above `y`, and conversely; this is Stacks 0CV4 on the base changes, together with the
fact that `Z_T ⟶ X_T` is a closed embedding on points.

The inputs of `AlgebraicGeometry.Space.ClosedSubspaceModule.BaseChangeInput` — affine base
change on the base changes — are hypotheses. -/
@[stacks 0CVH "pure above y, granting as hin affine base change (Stacks 02KG) on the base \
changes of the situation"]
theorem isPureAbove_situation_iff
    (hin : c.BaseChangeInput) :
    IsPureAbove c.situation ↔ IsPureAbove P := by
  have key := c.exists_isImpurity_iff hin
    (fun _ g t => IsQuasiFiniteAt B S hS g t)
  constructor
  · intro h D hqf hD
    obtain ⟨E, hqfE, hE⟩ := key.2 ⟨D, hqf, hD⟩
    exact h E hqfE hE
  · intro h E hqf hE
    obtain ⟨D, hqfD, hD⟩ := key.1 ⟨E, hqf, hE⟩
    exact h D hqfD hD

/-- **Stacks 0CVH, universal purity above `y`.** In the situation of Stacks 0CV6, let
`i : Z ⟶ X` be a closed immersion and suppose `ℱ = i_*𝒢` for a finite type quasi-coherent
`𝒪_Z`-module `𝒢`. Then `𝒢` is universally pure above `y` exactly when `ℱ` is.

An impurity of `𝒢` above `y` is an impurity of `ℱ` above `y`, and conversely.

The inputs of `AlgebraicGeometry.Space.ClosedSubspaceModule.BaseChangeInput` — affine base
change on the base changes — are hypotheses. -/
@[stacks 0CVH "universally pure above y, granting as hin affine base change (Stacks 02KG) on \
the base changes of the situation"]
theorem isUniversallyPureAbove_situation_iff
    (hin : c.BaseChangeInput) :
    IsUniversallyPureAbove c.situation ↔ IsUniversallyPureAbove P := by
  have key := c.exists_isImpurity_iff hin (fun _ _ _ => True)
  constructor
  · intro h D hD
    obtain ⟨E, -, hE⟩ := key.2 ⟨D, trivial, hD⟩
    exact h E hE
  · intro h E hE
    obtain ⟨D, -, hD⟩ := key.1 ⟨E, trivial, hE⟩
    exact h D hD

end Impurity

end ClosedSubspaceModule

end AlgebraicGeometry.Space

end
