module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFactorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Recompletion
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPointsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonalProperties

/-!
# Equality of two morphisms from the open complement and the completion

Let `S` be a scheme contained in a big fppf site `B`, let `X` and `W` be algebraic spaces over
`S` with `X` locally Noetherian and let `T ⊆ |X|` be a closed subset. **Stacks 0GI1** says that
two morphisms `a, b : X ⟶ W` over `S` which agree on the open subspace `X ∖ T` and whose
completions `a_{/T}, b_{/T} : X_{/T} ⟶ W` agree are equal.

The proof is two steps. The *equalizer* `E` of `a` and `b` — the fibre product of
`(a, b) : X ⟶ W ×_S W` and the relative diagonal `Δ : W ⟶ W ×_S W` — is an algebraic space,
and `g : E ⟶ X` is a monomorphism and locally of finite type by **Stacks 03HK**. The two
hypotheses say exactly that `X ∖ T ⟶ X` and `X_{/T} ⟶ X` factor through `g`, so
**Stacks 0AR6** applies to `f = 𝟙 X` and `g` and factors `𝟙 X` through `g`; composing that
factorisation with `g ≫ a = g ≫ b` gives `a = b`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.upliftedMap` is a morphism of algebraic spaces over `S`,
  regarded as a morphism of fppf sheaves of large sets.
* `AlgebraicGeometry.FormalSpace.completionOfAlgebraicSpace` is the completion `X_{/T}` of an
  algebraic space `X` over `S` along a subset `T ⊆ |X|`, and
  `AlgebraicGeometry.FormalSpace.completionOfAlgebraicSpaceInclusion` its inclusion into `X`.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_equalizerProj` and
  `AlgebraicGeometry.FormalSpace.mono_equalizerProj`: the projection `E ⟶ X` from the
  equalizer of two morphisms of algebraic spaces over `S` is locally of finite type and a
  monomorphism. This is **Stacks 03HK**, parts (2) and (3), transported to the equalizer.
* `AlgebraicGeometry.FormalSpace.exists_factorization_openSubspace_equalizer` and
  `AlgebraicGeometry.FormalSpace.exists_factorization_completion_equalizer`: the two
  hypotheses of Stacks 0GI1 give the factorisations of `X ∖ T ⟶ X` and of `X_{/T} ⟶ X`
  through the equalizer.
* `AlgebraicGeometry.FormalSpace.eq_of_eq_on_openComplement_of_eq_on_completion`: **Stacks
  0GI1**.

## Implementation notes

*The completion hypothesis of Stacks 0AR6.* The completion of an algebraic space is the
sheafification of the subfunctor
`AlgebraicGeometry.Space.completionSubfunctor` of sections of the universe lift of `X` with
point-set image in `T`, and
`AlgebraicGeometry.FormalSpace.exists_factorization_of_openComplement_and_completion` takes
its completion hypothesis on that subfunctor. A morphism out of the completion restricts along
the unit of the sheafification to a morphism out of the subfunctor, which is what
`AlgebraicGeometry.FormalSpace.exists_factorization_completionSubfunctor_of_completion`
records.

*The open complement.* Stacks 0AR6 names it through the correspondence of **Stacks 03BZ**,
whereas the factorisation produced here is on the subfunctor
`AlgebraicGeometry.Space.openSubspaceOfPoints` cut out by `Tᶜ`; the two agree because the
correspondence is injective and both have point set `Tᶜ`.

*The equalizer.* It is formed as the fibre product of `(a, b)` and the relative diagonal of
`t : W ⟶ *` over the final sheaf, rather than as a fibre product over a binary product
`W ⨯ W`; this is the shape in which
`AlgebraicGeometry.presheaf_locallyOfFiniteType_pullbackDiagonal` — part (2) of Stacks 03HK —
is stated, and it keeps the final object of the site in one place.
Note that the diagonal is *not* assumed to be a closed immersion: 0GI1 does not assume `W`
separated, and none of what follows does either. That the projection is a monomorphism is free,
the relative diagonal being a split monomorphism; it is local finite type that needs 03HK.

*Universes.* An algebraic space over `S` is a sheaf of `Type u` while a formal algebraic space
is a sheaf of `Type (u + 1)`, so the completion of `X` is formed from the universe lift
`AlgebraicGeometry.FormalSpace.upliftedSheaf` of `X` and the closed subset is carried across
`AlgebraicGeometry.Space.pointsULiftEquiv`, the identification of the two point spaces. The
completion hypothesis and the conclusion of 0GI1 are therefore stated in two different
categories, exactly as in the source, where `X_{/T} ⟶ W` is a morphism of formal algebraic
spaces and `a, b : X ⟶ W` are morphisms of algebraic spaces.

## References

* [Stacks Project, Tag 0GI1](https://stacks.math.columbia.edu/tag/0GI1)
* [Stacks Project, Tag 0AR6](https://stacks.math.columbia.edu/tag/0AR6)
* [Stacks Project, Tag 03HK](https://stacks.math.columbia.edu/tag/03HK)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Algebraic spaces as sheaves of large sets -/

/-- The universe lift functor on presheaves over the big fppf site of `S`: postcomposition
with `CategoryTheory.uliftFunctor`. -/
abbrev upliftFunctor :
    ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) :=
  (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1}

/-- The universe lift of a cartesian square of presheaves over the big fppf site of `S` is
cartesian: a cartesian square of presheaves is cartesian on sections over each object of the
site, and the universe lift preserves limits of types. -/
theorem isPullback_upliftFunctor_map {Z P Q R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f₁ : Z ⟶ P} {f₂ : Z ⟶ Q} {f₃ : P ⟶ R} {f₄ : Q ⟶ R} (h : IsPullback f₁ f₂ f₃ f₄) :
    IsPullback ((upliftFunctor B S hS).map f₁) ((upliftFunctor B S hS).map f₂)
      ((upliftFunctor B S hS).map f₃) ((upliftFunctor B S hS).map f₄) :=
  IsPullback.of_forall_isPullback_app fun U => (h.app U).map uliftFunctor.{u + 1}

/-- The universe lift of a cartesian square of presheaves over the big fppf site of `S` is
cartesian: a cartesian square of presheaves is cartesian on sections over each object of the
site, and the universe lift preserves limits of types. -/
alias isPullback_uliftPresheaf_map := AlgebraicGeometry.FormalSpace.isPullback_upliftFunctor_map

/-- A morphism of algebraic spaces over `S`, regarded as a morphism of fppf sheaves of
`Type (u + 1)`: the universe lift of the morphism, which is a morphism of the universe lifts
`AlgebraicGeometry.FormalSpace.upliftedSheaf`. -/
def upliftedMap {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    upliftedSheaf X hX ⟶ upliftedSheaf Y hY :=
  ObjectProperty.homMk ((upliftFunctor B S hS).map f)

/-- The morphism of sheaves of large sets underlying the universe lift of a morphism of
algebraic spaces is the universe lift of that morphism. -/
@[simp]
theorem upliftedMap_hom {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    (upliftedMap B S hS hX hY f).hom = (upliftFunctor B S hS).map f :=
  rfl

/-- The morphism of sheaves of large sets underlying the universe lift of a morphism of
algebraic spaces is the universe lift of that morphism. -/
@[simp]
alias upliftedMap_hom' := AlgebraicGeometry.FormalSpace.upliftedMap_hom

/-- The universe lift of an identity morphism is the identity. -/
@[simp]
theorem upliftedMap_id {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) :
    upliftedMap B S hS hX hX (𝟙 X) = 𝟙 (upliftedSheaf X hX) :=
  Sheaf.hom_ext rfl

/-! ### The completion of an algebraic space along a closed subset of its points -/

/-- The completion `X_{/T}` of an algebraic space `X` over `S` along a subset `T` of its point
space: the completion of Stacks 0AIN of the universe lift of `X` along the image of `T` under
the identification of the two point spaces. -/
def completionOfAlgebraicSpace {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (T : Set (Space.points B S hS X)) : FppfSheaf B S hS :=
  Space.completionSheafULift B S hS (upliftedSheaf X hX)
    (Space.pointsULiftEquiv.{u + 1} B S hS X '' T)

/-- The inclusion `X_{/T} ⟶ X` of the completion of an algebraic space along a subset of its
point space, read in the universe lift of `X`. -/
def completionOfAlgebraicSpaceInclusion {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (T : Set (Space.points B S hS X)) :
    completionOfAlgebraicSpace B S hS hX T ⟶ upliftedSheaf X hX :=
  Space.completionSheafULiftInclusion B S hS (upliftedSheaf X hX)
    (Space.pointsULiftEquiv.{u + 1} B S hS X '' T)

/-! ### Restricting to the completion subfunctor and to the open complement -/

/-- A section of the universe lift of `X` with point-set image in `T` has point-set image in
the image of `T` under the identification of the points of `X` with those of its universe
lift: the two conditions are tested on the same field-valued points, which correspond. -/
theorem completionSubfunctor_le_completionSubfunctorULift
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Set (Space.points B S hS X)) :
    Space.completionSubfunctor B S hS X T ≤
      Space.completionSubfunctorULift B S hS (X ⋙ uliftFunctor.{u + 1})
        (Space.pointsULiftEquiv.{u + 1} B S hS X '' T) := by
  intro U x hx p
  exact ⟨_, hx p, rfl⟩

/-- The unit of the sheafification presenting the completion `X_{/T}` of an algebraic space:
the morphism from the subfunctor of sections of the universe lift of `X` with point-set image
in `T` into the completion. -/
def toCompletionOfAlgebraicSpace {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (T : Set (Space.points B S hS X)) :
    (Space.completionSubfunctorULift B S hS (X ⋙ uliftFunctor.{u + 1})
        (Space.pointsULiftEquiv.{u + 1} B S hS X '' T)).toFunctor ⟶
      (completionOfAlgebraicSpace B S hS hX T).obj :=
  (BigFppfOver.topology B S hS).toSheafify _

/-- The inclusion `X_{/T} ⟶ X` of the completion of an algebraic space restricts along the
unit of the sheafification to the inclusion of the subfunctor which that completion
sheafifies. -/
theorem toCompletionOfAlgebraicSpace_comp_inclusion
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X)) :
    toCompletionOfAlgebraicSpace B S hS hX T ≫
        (completionOfAlgebraicSpaceInclusion B S hS hX T).hom =
      (Space.completionSubfunctorULift B S hS (X ⋙ uliftFunctor.{u + 1})
        (Space.pointsULiftEquiv.{u + 1} B S hS X '' T)).ι := by
  rw [show (completionOfAlgebraicSpaceInclusion B S hS hX T).hom =
      (BigFppfOver.topology B S hS).sheafifyLift
        (Space.completionSubfunctorULift B S hS (X ⋙ uliftFunctor.{u + 1})
          (Space.pointsULiftEquiv.{u + 1} B S hS X '' T)).ι (upliftedSheaf X hX).property from
    Space.completionSheafULiftInclusion_hom B S hS (upliftedSheaf X hX) _]
  exact (BigFppfOver.topology B S hS).toSheafify_sheafifyLift _ _

/-- A factorisation of `f_{/T} : X_{/T} ⟶ Y` through `g : Z ⟶ Y` restricts along the unit of
the sheafification to a factorisation on the subfunctor of sections of the universe lift of
`X` with point-set image in `T`. -/
theorem exists_factorization_completionSubfunctor_of_completion
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Z ⟶ Y)
    (T : Set (Space.points B S hS X))
    (h : ∃ v : completionOfAlgebraicSpace B S hS hX T ⟶ upliftedSheaf Z hZ,
      v ≫ upliftedMap B S hS hZ hY g =
        completionOfAlgebraicSpaceInclusion B S hS hX T ≫ upliftedMap B S hS hX hY f) :
    ∃ v : (Space.completionSubfunctor B S hS X T).toFunctor ⟶ Z ⋙ uliftFunctor.{u + 1},
      v ≫ Functor.whiskerRight g uliftFunctor.{u + 1} =
        (Space.completionSubfunctor B S hS X T).ι ≫
          Functor.whiskerRight f uliftFunctor.{u + 1} := by
  obtain ⟨v, hv⟩ := h
  let vh : (completionOfAlgebraicSpace B S hS hX T).obj ⟶ Z ⋙ uliftFunctor.{u + 1} := v.hom
  let ih : (completionOfAlgebraicSpace B S hS hX T).obj ⟶ X ⋙ uliftFunctor.{u + 1} :=
    (completionOfAlgebraicSpaceInclusion B S hS hX T).hom
  have hv' : vh ≫ Functor.whiskerRight g uliftFunctor.{u + 1} =
      ih ≫ Functor.whiskerRight f uliftFunctor.{u + 1} :=
    congrArg (fun φ : completionOfAlgebraicSpace B S hS hX T ⟶ upliftedSheaf Y hY => φ.hom) hv
  have hi0 : toCompletionOfAlgebraicSpace B S hS hX T ≫ ih =
      (Space.completionSubfunctorULift B S hS (X ⋙ uliftFunctor.{u + 1})
        (Space.pointsULiftEquiv.{u + 1} B S hS X '' T)).ι :=
    toCompletionOfAlgebraicSpace_comp_inclusion B S hS hX T
  have hi : toCompletionOfAlgebraicSpace B S hS hX T ≫ ih ≫
        Functor.whiskerRight f uliftFunctor.{u + 1} =
      (Space.completionSubfunctorULift B S hS (X ⋙ uliftFunctor.{u + 1})
          (Space.pointsULiftEquiv.{u + 1} B S hS X '' T)).ι ≫
        Functor.whiskerRight f uliftFunctor.{u + 1} := by
    rw [← Category.assoc, hi0]
  refine ⟨Subfunctor.homOfLe
      (completionSubfunctor_le_completionSubfunctorULift B S hS (X := X) T) ≫
    toCompletionOfAlgebraicSpace B S hS hX T ≫ vh, ?_⟩
  rw [Category.assoc, Category.assoc, hv', hi, ← Category.assoc, Subfunctor.homOfLe_ι]

/-- The open subspace of Stacks 03BZ with point set `Tᶜ` is the subfunctor cut out by `Tᶜ`:
the correspondence of that tag is injective and both have point set `Tᶜ`. -/
theorem openSubspacesOrderIso_symm_compl {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (T : Set (Space.points B S hS X)) (hT : IsClosed T) :
    (Space.openSubspacesOrderIso B S hS X hX).symm ⟨Tᶜ, hT.isOpen_compl⟩ =
      ⟨Space.openSubspaceOfPoints B S hS X Tᶜ,
        Space.isOpenSubspace_openSubspaceOfPoints B S hS hX Tᶜ hT.isOpen_compl⟩ := by
  rw [OrderIso.symm_apply_eq]
  exact TopologicalSpace.Opens.ext
    (Space.range_pointsMap_ι_openSubspaceOfPoints B S hS Tᶜ).symm

/-! ### Stacks 0AR6 in the vocabulary of this library -/

/-- **Stacks 0AR6**, stated in the vocabulary of this library.

Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of algebraic spaces over `S` and let
`T ⊆ |X|` be closed, with `X` locally Noetherian and `g` a monomorphism locally of finite
type. If the restriction of `f` to the open subspace `X ∖ T` factors through `g`, and if the
completion `f_{/T} : X_{/T} ⟶ Y` factors through `g`, then `f` factors through `g`.

The form proved in this library is
`AlgebraicGeometry.FormalSpace.exists_factorization_of_openComplement_and_completion`, which
states the completion hypothesis on the unsheafified subfunctor of sections with point-set
image in `T`. -/
def FactorizationGluingAcrossClosedSubset : Prop :=
  ∀ {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
      (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Z ⟶ Y)
      (T : Set (Space.points B S hS X)),
    IsClosed T →
    Space.HasEtaleLocalProperty B S hS X (fun V : Scheme.{u} => IsLocallyNoetherian V) →
    Mono g →
    Space.IsLocallyOfFiniteType B S hS g →
    (∃ v : (Space.openSubspaceOfPoints B S hS X Tᶜ).toFunctor ⟶ Z,
      v ≫ g = (Space.openSubspaceOfPoints B S hS X Tᶜ).ι ≫ f) →
    (∃ v : completionOfAlgebraicSpace B S hS hX T ⟶ upliftedSheaf Z hZ,
      v ≫ upliftedMap B S hS hZ hY g =
        completionOfAlgebraicSpaceInclusion B S hS hX T ≫ upliftedMap B S hS hX hY f) →
    ∃ v : X ⟶ Z, v ≫ g = f

/-! ### The equalizer of two morphisms of algebraic spaces -/

section Equalizer

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_MorphismEqualityFromCompletion :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_MorphismEqualityFromCompletion
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_MorphismEqualityFromCompletion B S hS).has_limit _

variable {X W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The final object of the big fppf category over `S`: the base `S`, presented as an object
of the category over itself by the identity. -/
def finalSiteObject : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))

/-- The final object of the big fppf category over `S` is final. -/
def isTerminalFinalSiteObject : IsTerminal (finalSiteObject B S hS) :=
  Over.mkIdTerminal

/-- The sheaf represented by the final object of the site is a final sheaf. -/
def isTerminalYonedaFinalSiteObject :
    IsTerminal (yoneda.obj (finalSiteObject B S hS)) :=
  IsTerminal.isTerminalObj yoneda _ (isTerminalFinalSiteObject B S hS)

/-- The structure morphism of an algebraic space over `S` to the final sheaf. -/
def toFinalSheaf (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    W ⟶ yoneda.obj (finalSiteObject B S hS) :=
  (isTerminalYonedaFinalSiteObject B S hS).from W

/-- The product `W ×_S W` of an algebraic space over `S` with itself. -/
abbrev selfProduct (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (toFinalSheaf B S hS W) (toFinalSheaf B S hS W)

/-- The product of an algebraic space over `S` with itself is an algebraic space. -/
theorem isAlgebraicSpace_selfProduct (hW : IsAlgebraicSpace B S hS W) :
    IsAlgebraicSpace B S hS (selfProduct B S hS W) :=
  isAlgebraicSpace_pullback B S hS _ _ hW hW
    (isAlgebraicSpace_yoneda B S hS (finalSiteObject B S hS))

/-- The relative diagonal `Δ : W ⟶ W ×_S W` of an algebraic space over `S`. -/
abbrev selfDiagonal (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : W ⟶ selfProduct B S hS W :=
  pullback.diagonal (toFinalSheaf B S hS W)

/-- The morphism `(a, b) : X ⟶ W ×_S W` attached to a pair of morphisms of algebraic spaces
over `S` with the same source and target. -/
abbrev pairMap (a b : X ⟶ W) : X ⟶ selfProduct B S hS W :=
  pullback.lift a b ((isTerminalYonedaFinalSiteObject B S hS).hom_ext _ _)

/-- The first projection of `(a, b) : X ⟶ W ×_S W` is `a`. -/
@[simp]
theorem pairMap_fst (a b : X ⟶ W) :
    pairMap B S hS a b ≫ pullback.fst (toFinalSheaf B S hS W) (toFinalSheaf B S hS W) = a :=
  pullback.lift_fst _ _ _

/-- The second projection of `(a, b) : X ⟶ W ×_S W` is `b`. -/
@[simp]
theorem pairMap_snd (a b : X ⟶ W) :
    pairMap B S hS a b ≫ pullback.snd (toFinalSheaf B S hS W) (toFinalSheaf B S hS W) = b :=
  pullback.lift_snd _ _ _

/-- The *equalizer* of two morphisms `a, b : X ⟶ W` of algebraic spaces over `S`: the fibre
product of `(a, b) : X ⟶ W ×_S W` and the relative diagonal of `W`. A morphism into it over
an algebraic space `X'` is a morphism `X' ⟶ X` equalizing `a` and `b`. -/
abbrev equalizer (a b : X ⟶ W) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (pairMap B S hS a b) (selfDiagonal B S hS W)

/-- The projection `E ⟶ X` from the equalizer of two morphisms of algebraic spaces over `S`. -/
abbrev equalizerProj (a b : X ⟶ W) : equalizer B S hS a b ⟶ X :=
  pullback.fst (pairMap B S hS a b) (selfDiagonal B S hS W)

/-- The equalizer of two morphisms of algebraic spaces over `S` is cartesian over the pair
`(a, b)` and the relative diagonal of `W`. -/
theorem isPullback_equalizer (a b : X ⟶ W) :
    IsPullback (equalizerProj B S hS a b)
      (pullback.snd (pairMap B S hS a b) (selfDiagonal B S hS W))
      (pairMap B S hS a b) (selfDiagonal B S hS W) :=
  IsPullback.of_hasPullback _ _

/-- The equalizer of two morphisms of algebraic spaces over `S` is an algebraic space. -/
theorem isAlgebraicSpace_equalizer (hX : IsAlgebraicSpace B S hS X)
    (hW : IsAlgebraicSpace B S hS W) (a b : X ⟶ W) :
    IsAlgebraicSpace B S hS (equalizer B S hS a b) :=
  isAlgebraicSpace_pullback B S hS _ _ hX hW (isAlgebraicSpace_selfProduct B S hS hW)

/-- The two morphisms agree after composing with the projection from their equalizer. -/
theorem equalizerProj_comp_eq (a b : X ⟶ W) :
    equalizerProj B S hS a b ≫ a = equalizerProj B S hS a b ≫ b := by
  have key : ∀ q : selfProduct B S hS W ⟶ W,
      selfDiagonal B S hS W ≫ q = 𝟙 W →
      equalizerProj B S hS a b ≫ pairMap B S hS a b ≫ q =
        pullback.snd (pairMap B S hS a b) (selfDiagonal B S hS W) := by
    intro q hq
    rw [← Category.assoc, (isPullback_equalizer B S hS a b).w, Category.assoc, hq,
      Category.comp_id]
  have ha := key (pullback.fst (toFinalSheaf B S hS W) (toFinalSheaf B S hS W))
    (pullback.diagonal_fst _)
  have hb := key (pullback.snd (toFinalSheaf B S hS W) (toFinalSheaf B S hS W))
    (pullback.diagonal_snd _)
  simp only [pullback.lift_fst, pullback.lift_snd] at ha hb
  exact ha.trans hb.symm

/-- The projection from the equalizer of two morphisms of algebraic spaces over `S` is a
monomorphism: it is a base change of the relative diagonal of `W`, which is a split
monomorphism. No separatedness of `W` is involved. -/
theorem mono_equalizerProj (a b : X ⟶ W) : Mono (equalizerProj B S hS a b) :=
  (isPullback_equalizer B S hS a b).mono_fst_of_mono
    (SplitMono.mono ⟨pullback.fst (toFinalSheaf B S hS W) (toFinalSheaf B S hS W),
      pullback.diagonal_fst _⟩)

/-- **Stacks 03HK, part (2), for the equalizer.** The projection from the equalizer of two
morphisms of algebraic spaces over `S` is locally of finite type, being a base change of the
relative diagonal of `W`. -/
theorem isLocallyOfFiniteType_equalizerProj (hW : IsAlgebraicSpace B S hS W) (a b : X ⟶ W) :
    Space.IsLocallyOfFiniteType B S hS (equalizerProj B S hS a b) := by
  have hdiag : Space.IsLocallyOfFiniteType B S hS (selfDiagonal B S hS W) :=
    Space.presheafImpliesHoldsOnEveryEtaleChart_locallyOfFiniteType B S hS _
      (presheaf_locallyOfFiniteType_pullbackDiagonal B S hS (toFinalSheaf B S hS W) hW)
  exact Space.IsLocallyOfFiniteType.of_isPullback B S hS
    (isPullback_equalizer B S hS a b) hW (isAlgebraicSpace_selfProduct B S hS hW) hdiag

/-- A morphism into `X` which equalizes `a` and `b` factors through their equalizer. -/
theorem exists_factorization_equalizer {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a b : X ⟶ W)
    (p : X' ⟶ X) (hp : p ≫ a = p ≫ b) :
    ∃ v : X' ⟶ equalizer B S hS a b, v ≫ equalizerProj B S hS a b = p := by
  refine ⟨pullback.lift p (p ≫ a) (pullback.hom_ext ?_ ?_), pullback.lift_fst _ _ _⟩
  · simp only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
  · simp only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id]
    exact hp.symm

end Equalizer

/-! ### Stacks 0GI1 -/

section Main

variable {X W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The two morphisms agreeing on the open subspace `X ∖ T` factors its inclusion through the
equalizer of `a` and `b`. -/
theorem exists_factorization_openSubspace_equalizer (a b : X ⟶ W)
    (T : Set (Space.points B S hS X))
    (hopen : (Space.openSubspaceOfPoints B S hS X Tᶜ).ι ≫ a =
      (Space.openSubspaceOfPoints B S hS X Tᶜ).ι ≫ b) :
    ∃ v : (Space.openSubspaceOfPoints B S hS X Tᶜ).toFunctor ⟶ equalizer B S hS a b,
      v ≫ equalizerProj B S hS a b =
        (Space.openSubspaceOfPoints B S hS X Tᶜ).ι ≫ 𝟙 X := by
  obtain ⟨v, hv⟩ := exists_factorization_equalizer B S hS a b
    (Space.openSubspaceOfPoints B S hS X Tᶜ).ι hopen
  exact ⟨v, by rw [hv, Category.comp_id]⟩

/-- A morphism into the universe lift of `X` which equalizes the universe lifts of `a` and `b`
factors through the universe lift of their equalizer. The source is an arbitrary presheaf of
`Type (u + 1)`, so this is the statement needed for the completion of `X`, which lives in that
universe. -/
theorem exists_factorization_upliftFunctor_equalizer
    {C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (a b : X ⟶ W)
    (ι : C ⟶ (upliftFunctor B S hS).obj X)
    (hab : ι ≫ (upliftFunctor B S hS).map a = ι ≫ (upliftFunctor B S hS).map b) :
    ∃ v : C ⟶ (upliftFunctor B S hS).obj (equalizer B S hS a b),
      v ≫ (upliftFunctor B S hS).map (equalizerProj B S hS a b) = ι := by
  have hPpb := isPullback_upliftFunctor_map B S hS
    (IsPullback.of_hasPullback (toFinalSheaf B S hS W) (toFinalSheaf B S hS W))
  have hEpb := isPullback_upliftFunctor_map B S hS (isPullback_equalizer B S hS a b)
  have hw : ι ≫ (upliftFunctor B S hS).map (pairMap B S hS a b) =
      (ι ≫ (upliftFunctor B S hS).map a) ≫
        (upliftFunctor B S hS).map (selfDiagonal B S hS W) := by
    refine hPpb.hom_ext ?_ ?_ <;>
      simp only [Category.assoc, ← Functor.map_comp, pairMap_fst, pairMap_snd,
        pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id]
    exact hab.symm
  exact ⟨hEpb.lift ι (ι ≫ (upliftFunctor B S hS).map a) hw, hEpb.lift_fst _ _ hw⟩

/-- A morphism into the universe lift of `X` which equalizes the universe lifts of `a` and `b`
factors through the universe lift of their equalizer. The source is an arbitrary presheaf of
`Type (u + 1)`, so this is the statement needed for the completion of `X`, which lives in that
universe. -/
alias exists_factorization_uliftPresheaf_equalizer :=
  AlgebraicGeometry.FormalSpace.exists_factorization_upliftFunctor_equalizer

/-- The two morphisms agreeing on the completion `X_{/T}` factors its inclusion through the
equalizer of `a` and `b`. -/
theorem exists_factorization_completion_equalizer (hX : IsAlgebraicSpace B S hS X)
    (hW : IsAlgebraicSpace B S hS W) (a b : X ⟶ W) (T : Set (Space.points B S hS X))
    (hcompletion :
      completionOfAlgebraicSpaceInclusion B S hS hX T ≫ upliftedMap B S hS hX hW a =
        completionOfAlgebraicSpaceInclusion B S hS hX T ≫ upliftedMap B S hS hX hW b) :
    ∃ v : completionOfAlgebraicSpace B S hS hX T ⟶
        upliftedSheaf (equalizer B S hS a b) (isAlgebraicSpace_equalizer B S hS hX hW a b),
      v ≫ upliftedMap B S hS (isAlgebraicSpace_equalizer B S hS hX hW a b) hX
          (equalizerProj B S hS a b) =
        completionOfAlgebraicSpaceInclusion B S hS hX T ≫
          upliftedMap B S hS hX hX (𝟙 X) := by
  obtain ⟨v, hv⟩ := exists_factorization_uliftPresheaf_equalizer B S hS a b
    (completionOfAlgebraicSpaceInclusion B S hS hX T).hom
    (congrArg (fun φ => φ.hom) hcompletion)
  refine ⟨ObjectProperty.homMk v, ?_⟩
  rw [upliftedMap_id, Category.comp_id]
  exact Sheaf.hom_ext hv

/-- **Stacks 0GI1.** Let `X` and `W` be algebraic spaces over `S` with `X` locally Noetherian,
let `T ⊆ |X|` be a closed subset and let `a, b : X ⟶ W` be morphisms over `S` which agree on
the open subspace `X ∖ T` and whose completions along `T` agree. Then `a = b`.

The equalizer `E` of `a` and `b` is an algebraic space whose projection `g : E ⟶ X` is a
monomorphism locally of finite type — Stacks 03HK — and the two hypotheses factor
`X ∖ T ⟶ X` and `X_{/T} ⟶ X` through `g`, so Stacks 0AR6 applied to `𝟙 X` and `g` gives a
section `v` of `g`. Since `g ≫ a = g ≫ b` by construction, `a = v ≫ g ≫ a = v ≫ g ≫ b = b`. -/
@[stacks 0GI1]
theorem eq_of_eq_on_openComplement_of_eq_on_completion
    (hX : IsAlgebraicSpace B S hS X) (hW : IsAlgebraicSpace B S hS W)
    (hXnoeth : Space.HasEtaleLocalProperty B S hS X
      (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (T : Set (Space.points B S hS X)) (hT : IsClosed T) (a b : X ⟶ W)
    (hopen : (Space.openSubspaceOfPoints B S hS X Tᶜ).ι ≫ a =
      (Space.openSubspaceOfPoints B S hS X Tᶜ).ι ≫ b)
    (hcompletion :
      completionOfAlgebraicSpaceInclusion B S hS hX T ≫ upliftedMap B S hS hX hW a =
        completionOfAlgebraicSpaceInclusion B S hS hX T ≫ upliftedMap B S hS hX hW b) :
    a = b := by
  have hE := isAlgebraicSpace_equalizer B S hS hX hW a b
  obtain ⟨v, hv⟩ := exists_factorization_of_openComplement_and_completion B S hS hX hX hE
    (𝟙 X) (equalizerProj B S hS a b) T hT hXnoeth
    (mono_equalizerProj B S hS a b) (isLocallyOfFiniteType_equalizerProj B S hS hW a b)
    (by
      rw [openSubspacesOrderIso_symm_compl B S hS hX T hT]
      exact exists_factorization_openSubspace_equalizer B S hS a b T hopen)
    (exists_factorization_completionSubfunctor_of_completion B S hS hX hX hE (𝟙 X)
      (equalizerProj B S hS a b) T
      (exists_factorization_completion_equalizer B S hS hX hW a b T hcompletion))
  have h := congrArg (fun f : equalizer B S hS a b ⟶ W => v ≫ f)
    (equalizerProj_comp_eq B S hS a b)
  simpa only [← Category.assoc, hv, Category.id_comp] using h

end Main

end AlgebraicGeometry.FormalSpace

end
