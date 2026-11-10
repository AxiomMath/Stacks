module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceSurjective
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.NoRationalCurves
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.ArrowFiberAlgebraicity

/-!
# The coordinate projections of a finite power of the projective line

Let `k` be a field and `B` a big fppf site containing `Spec k`. For `I ⊆ Fin n` the coordinate
projection `(ℙ¹_k)^n ⟶ (ℙ¹_k)^I` of
`AlgebraicGeometry.Space.coordinateProjection` is surjective, flat and locally of finite
presentation — the three hypotheses that Stacks 0AEL asks of the morphism one descends along.

## Main definitions

* `AlgebraicGeometry.Space.coordinateProjectionCompl`: the projection onto the coordinates
  *outside* a finite subset of `Fin n`.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_projectiveLinePower`: a finite power of the
  projective line is an algebraic space over `k`.
* `AlgebraicGeometry.Space.isSurjective_coordinateProjection`,
  `AlgebraicGeometry.Space.isFlat_coordinateProjection` and
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_coordinateProjection`: the three
  properties of the coordinate projection.

## Implementation notes

The projection onto the coordinates in `I` and the projection onto the coordinates outside `I`
exhibit `(ℙ¹_k)^n` as the product of `(ℙ¹_k)^I` with `(ℙ¹_k)^{Iᶜ}`
(`AlgebraicGeometry.Space.isLimit_binaryFan_coordinateProjection`), and the base is terminal
among presheaves on the site (`AlgebraicGeometry.Space.base_isTerminal`), so the projection onto
`I` is the base change of the structure morphism of `(ℙ¹_k)^{Iᶜ}` along the structure morphism
of `(ℙ¹_k)^I`. All three properties are stable under base change, so everything reduces to the
structure morphism of a finite power of the projective line.

That morphism is treated by induction on the number of factors. A power indexed by `Fin (m+1)`
is the product of the power indexed by `Fin m` with one more copy of `ℙ¹_k`
(`AlgebraicGeometry.Space.piFinSuccIso`), so the induction step is again a base change, this
time of the structure morphism of a single `ℙ¹_k`. The latter is represented by an object of
the site (`AlgebraicGeometry.Space.projectiveLineRestrictedYonedaIso`), so it inherits its
three properties from the morphism of schemes `ℙ¹_k ⟶ Spec k`, which is smooth — hence flat and
locally of finite presentation — and surjective because it has a section.

Flatness and local finite presentation are both of the form "a property of morphisms of schemes
which is étale local on the source and target holds on every commuting square of étale charts",
so they are proved together, for an arbitrary such property; surjectivity is a condition on the
map of point sets and is proved separately.

## References

* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 0AEL](https://stacks.math.columbia.edu/tag/0AEL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.Space

variable (k : Type u) [Field k] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (CommRingCat.of k)))

/-! ### The base and a single projective line -/

/-- The structure morphism of a power of the projective line to the base, that base being the
terminal presheaf on the big fppf site over `Spec k`. -/
noncomputable abbrev projectiveLinePowerToBase (α : Type v) [Small.{u} α] :
    projectiveLinePower k B hk α ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))) :=
  (base_isTerminal k B hk).from (projectiveLinePower k B hk α)

/-- The structure morphism of the projective line over `k`, as a morphism of the site. -/
noncomputable abbrev projectiveLineSiteToBase :
    projectiveLineSiteObject k B hk ⟶ Over.mk (𝟙 (B.obj hk)) :=
  Over.homMk (projectiveLineSiteObject k B hk).hom

/-- The morphism of schemes underlying the structure morphism of the projective line in the
site is the structure morphism of `ℙ¹_k` over `Spec k`. -/
theorem toScheme_map_projectiveLineSiteToBase :
    (BigFppfOver.toScheme B (Spec (CommRingCat.of k)) hk).map
        (projectiveLineSiteToBase k B hk) =
      (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) :=
  rfl

/-- The projective line over `k` is an algebraic space over `k`: it is represented by an object
of the site. -/
theorem isAlgebraicSpace_projectiveLineFunctor :
    IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk (projectiveLineFunctor k B hk) :=
  isAlgebraicSpace_of_iso B (Spec (CommRingCat.of k)) hk
    (projectiveLineRestrictedYonedaIso k B hk).symm
    (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _)

/-- The structure morphism of the projective line, factored through its representation by an
object of the site. -/
theorem projectiveLineToBase_eq :
    (base_isTerminal k B hk).from (projectiveLineFunctor k B hk) =
      (projectiveLineRestrictedYonedaIso k B hk).hom ≫
        yoneda.map (projectiveLineSiteToBase k B hk) :=
  (base_isTerminal k B hk).hom_ext _ _

/-! ### Binary products over the base -/

variable {k B hk}

/-- A binary product of presheaves on the big fppf site over `Spec k` is their fibre product
over the base, that base being terminal. -/
theorem isPullback_prod_base
    (F G : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u) :
    IsPullback (Limits.prod.fst : F ⨯ G ⟶ F) Limits.prod.snd
      ((base_isTerminal k B hk).from F) ((base_isTerminal k B hk).from G) :=
  IsPullback.of_is_product (prodIsProd F G) (base_isTerminal k B hk)

/-- A cartesian square of presheaves whose four corners are algebraic spaces is cartesian in the
category of algebraic spaces over `k`. -/
private theorem isPullback_algebraicSpaces_homMk
    {P Z X Y : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk P)
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z)
    (hX : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk X)
    (hY : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Y)
    {p : P ⟶ Z} {q : P ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f) :
    IsPullback
      (ObjectProperty.homMk p : (⟨P, hP⟩ : AlgebraicSpaces B (Spec (CommRingCat.of k)) hk) ⟶
        ⟨Z, hZ⟩)
      (ObjectProperty.homMk q : (⟨P, hP⟩ : AlgebraicSpaces B (Spec (CommRingCat.of k)) hk) ⟶
        ⟨X, hX⟩)
      (ObjectProperty.homMk g : (⟨Z, hZ⟩ : AlgebraicSpaces B (Spec (CommRingCat.of k)) hk) ⟶
        ⟨Y, hY⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (CommRingCat.of k)) hk) ⟶
        ⟨Y, hY⟩) :=
  IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.w) (by simpa using sq)

/-- The square of `AlgebraicGeometry.Space.isPullback_prod_base`, read in the category of
algebraic spaces over `k`. -/
theorem isPullback_prod_base_algebraicSpaces
    {F G : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk F)
    (hG : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk G) :
    IsPullback
      (ObjectProperty.homMk (Limits.prod.fst : F ⨯ G ⟶ F) :
        (⟨F ⨯ G, isAlgebraicSpace_prod B (Spec (CommRingCat.of k)) hk hF hG⟩ :
          AlgebraicSpaces B (Spec (CommRingCat.of k)) hk) ⟶ ⟨F, hF⟩)
      (ObjectProperty.homMk (Limits.prod.snd : F ⨯ G ⟶ G) :
        (⟨F ⨯ G, isAlgebraicSpace_prod B (Spec (CommRingCat.of k)) hk hF hG⟩ :
          AlgebraicSpaces B (Spec (CommRingCat.of k)) hk) ⟶ ⟨G, hG⟩)
      (ObjectProperty.homMk ((base_isTerminal k B hk).from F) :
        (⟨F, hF⟩ : AlgebraicSpaces B (Spec (CommRingCat.of k)) hk) ⟶
          ⟨_, isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _⟩)
      (ObjectProperty.homMk ((base_isTerminal k B hk).from G) :
        (⟨G, hG⟩ : AlgebraicSpaces B (Spec (CommRingCat.of k)) hk) ⟶
          ⟨_, isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _⟩) :=
  isPullback_algebraicSpaces_homMk _ _ _ _ (isPullback_prod_base F G)

/-! ### The chart-type properties of a power of the projective line -/

section ChartProperty

variable (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
  [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
  (hPetale : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y), AlgebraicGeometry.Etale g → P g)

omit [P.IsStableUnderBaseChange] in
include hP hPetale in
/-- A property of morphisms of schemes which is étale local on the source and target, stable
under base change, implied by étaleness and true of `ℙ¹_k ⟶ Spec k` holds on every étale chart
of the structure morphism of the projective line as an algebraic space. -/
theorem holdsOnEveryEtaleChart_projectiveLineToBase (k : Type u) [Field k] (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (CommRingCat.of k)))
    (hPline : P (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k))) :
    HoldsOnEveryEtaleChart B (Spec (CommRingCat.of k)) hk P
      ((base_isTerminal k B hk).from (projectiveLineFunctor k B hk)) := by
  rw [projectiveLineToBase_eq k B hk]
  refine holdsOnEveryEtaleChart_comp B (Spec (CommRingCat.of k)) hk P hP
    (isAlgebraicSpace_projectiveLineFunctor k B hk)
    (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _)
    (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _) _ _
    (holdsOnEveryEtaleChart_of_isEtale_hom B (Spec (CommRingCat.of k)) hk P hPetale
      (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _)
      (isEtale_of_isIso B (Spec (CommRingCat.of k)) hk _))
    (holdsOnEveryEtaleChart_yoneda_map B (Spec (CommRingCat.of k)) hk hP
      (projectiveLineSiteToBase k B hk) ?_)
  rw [toScheme_map_projectiveLineSiteToBase]
  exact hPline

omit [P.IsStableUnderComposition] in
include hP in
/-- Such a property holds on every étale chart of the first projection of a binary product of
algebraic spaces, as soon as it holds on every étale chart of the structure morphism of the
second factor: the first projection is the base change of that structure morphism. -/
theorem holdsOnEveryEtaleChart_prod_fst
    {F G : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk F)
    (hG : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk G)
    (hGb : HoldsOnEveryEtaleChart B (Spec (CommRingCat.of k)) hk P
      ((base_isTerminal k B hk).from G)) :
    HoldsOnEveryEtaleChart B (Spec (CommRingCat.of k)) hk P
      (Limits.prod.fst : F ⨯ G ⟶ F) := by
  have := holdsOnEveryEtaleChart_isStableUnderBaseChange B (Spec (CommRingCat.of k)) hk P hP
  exact MorphismProperty.of_isPullback
    (P := fun ⦃X Y : AlgebraicSpaces B (Spec (CommRingCat.of k)) hk⦄ (f : X ⟶ Y) =>
      HoldsOnEveryEtaleChart B (Spec (CommRingCat.of k)) hk P f.hom)
    (isPullback_prod_base_algebraicSpaces hF hG).flip hGb

end ChartProperty

/-! ### Powers of the projective line are algebraic spaces -/

variable (k B hk)

/-- The empty power of the projective line is terminal. -/
private def isTerminal_projectiveLinePower_fin_zero :
    IsTerminal (projectiveLinePower k B hk (Fin 0)) :=
  IsTerminal.ofUniqueHom (fun _ => Pi.lift fun i => Fin.elim0 i)
    (fun _ _ => Pi.hom_ext _ _ fun i => Fin.elim0 i)

/-- The structure morphism of the empty power of the projective line is an isomorphism. -/
private theorem isIso_projectiveLinePowerToBase_fin_zero :
    IsIso (projectiveLinePowerToBase k B hk (Fin 0)) :=
  ⟨(isTerminal_projectiveLinePower_fin_zero k B hk).from _,
    (isTerminal_projectiveLinePower_fin_zero k B hk).hom_ext _ _,
    (base_isTerminal k B hk).hom_ext _ _⟩

/-- A power of the projective line indexed by `Fin m` is an algebraic space over `k`. -/
theorem isAlgebraicSpace_projectiveLinePowerFin (m : ℕ) :
    IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk (Fin m)) := by
  induction m with
  | zero =>
    exact isAlgebraicSpace_of_iso B (Spec (CommRingCat.of k)) hk
      ((base_isTerminal k B hk).uniqueUpToIso (isTerminal_projectiveLinePower_fin_zero k B hk))
      (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _)
  | succ m ih =>
    exact isAlgebraicSpace_of_iso B (Spec (CommRingCat.of k)) hk
      (piFinSuccIso (projectiveLineFunctor k B hk) m).symm
      (isAlgebraicSpace_prod B (Spec (CommRingCat.of k)) hk ih
        (isAlgebraicSpace_projectiveLineFunctor k B hk))

/-- A power of the projective line indexed by a finite type is an algebraic space over `k`. -/
theorem isAlgebraicSpace_projectiveLinePower (α : Type v) [Small.{u} α] [Finite α] :
    IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk α) :=
  isAlgebraicSpace_of_iso B (Spec (CommRingCat.of k)) hk
    (projectiveLinePowerReindexIso k B hk (Finite.equivFin α)).symm
    (isAlgebraicSpace_projectiveLinePowerFin k B hk (Nat.card α))

/-! ### The chart-type properties of the structure morphism of a power -/

section ChartPropertyPower

variable (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
  [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
  (hPetale : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y), AlgebraicGeometry.Etale g → P g)
  (hPline : P (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k)))

include hP hPetale hPline in
/-- Such a property holds on every étale chart of the structure morphism of a power of the
projective line indexed by `Fin m`. -/
theorem holdsOnEveryEtaleChart_projectiveLinePowerFinToBase (m : ℕ) :
    HoldsOnEveryEtaleChart B (Spec (CommRingCat.of k)) hk P
      (projectiveLinePowerToBase k B hk (Fin m)) := by
  induction m with
  | zero =>
    have := isIso_projectiveLinePowerToBase_fin_zero k B hk
    exact holdsOnEveryEtaleChart_of_isEtale_hom B (Spec (CommRingCat.of k)) hk P hPetale
      (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _)
      (isEtale_of_isIso B (Spec (CommRingCat.of k)) hk _)
  | succ m ih =>
    have hm := isAlgebraicSpace_projectiveLinePowerFin k B hk m
    have hL := isAlgebraicSpace_projectiveLineFunctor k B hk
    have hprod := isAlgebraicSpace_prod B (Spec (CommRingCat.of k)) hk hm hL
    have hfst : HoldsOnEveryEtaleChart B (Spec (CommRingCat.of k)) hk P
        (Limits.prod.fst : projectiveLinePower k B hk (Fin m) ⨯ projectiveLineFunctor k B hk ⟶
          projectiveLinePower k B hk (Fin m)) :=
      holdsOnEveryEtaleChart_prod_fst P hP hm hL
        (holdsOnEveryEtaleChart_projectiveLineToBase P hP hPetale k B hk hPline)
    have heq : projectiveLinePowerToBase k B hk (Fin (m + 1)) =
        (piFinSuccIso (projectiveLineFunctor k B hk) m).hom ≫
          (Limits.prod.fst ≫ projectiveLinePowerToBase k B hk (Fin m)) :=
      (base_isTerminal k B hk).hom_ext _ _
    rw [heq]
    exact holdsOnEveryEtaleChart_comp B (Spec (CommRingCat.of k)) hk P hP
      (isAlgebraicSpace_projectiveLinePowerFin k B hk (m + 1)) hprod
      (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _) _ _
      (holdsOnEveryEtaleChart_of_isEtale_hom B (Spec (CommRingCat.of k)) hk P hPetale hprod
        (isEtale_of_isIso B (Spec (CommRingCat.of k)) hk _))
      (holdsOnEveryEtaleChart_comp B (Spec (CommRingCat.of k)) hk P hP hprod hm
        (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _) _ _ hfst ih)

include hP hPetale hPline in
/-- Such a property holds on every étale chart of the structure morphism of a power of the
projective line indexed by a finite type. -/
theorem holdsOnEveryEtaleChart_projectiveLinePowerToBase (α : Type v) [Small.{u} α] [Finite α] :
    HoldsOnEveryEtaleChart B (Spec (CommRingCat.of k)) hk P
      (projectiveLinePowerToBase k B hk α) := by
  have heq : projectiveLinePowerToBase k B hk α =
      (projectiveLinePowerReindexIso k B hk (Finite.equivFin α)).hom ≫
        projectiveLinePowerToBase k B hk (Fin (Nat.card α)) :=
    (base_isTerminal k B hk).hom_ext _ _
  rw [heq]
  exact holdsOnEveryEtaleChart_comp B (Spec (CommRingCat.of k)) hk P hP
    (isAlgebraicSpace_projectiveLinePower k B hk α)
    (isAlgebraicSpace_projectiveLinePowerFin k B hk (Nat.card α))
    (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _) _ _
    (holdsOnEveryEtaleChart_of_isEtale_hom B (Spec (CommRingCat.of k)) hk P hPetale
      (isAlgebraicSpace_projectiveLinePowerFin k B hk (Nat.card α))
      (isEtale_of_isIso B (Spec (CommRingCat.of k)) hk _))
    (holdsOnEveryEtaleChart_projectiveLinePowerFinToBase k B hk P hP hPetale hPline _)

end ChartPropertyPower

/-! ### Surjectivity of the structure morphism of a power -/

/-- The structure morphism of the projective line as an algebraic space over `k` is surjective
on points: the morphism of schemes `ℙ¹_k ⟶ Spec k` is surjective. -/
theorem isSurjective_projectiveLineToBase :
    IsSurjective B (Spec (CommRingCat.of k)) hk
      ((base_isTerminal k B hk).from (projectiveLineFunctor k B hk)) := by
  rw [projectiveLineToBase_eq k B hk]
  refine isSurjective_comp B (Spec (CommRingCat.of k)) hk
    (isSurjective_of_isIso B (Spec (CommRingCat.of k)) hk _) ?_
  refine surjective_pointsMap_yoneda_map B (Spec (CommRingCat.of k)) hk
    (projectiveLineSiteToBase k B hk) ?_
  rw [toScheme_map_projectiveLineSiteToBase]
  exact projectiveSpaceOver.surjective 1 (Spec (CommRingCat.of k))

variable {k B hk}

/-- The second leg of a cartesian square of presheaves is surjective on points as soon as the
side opposite to it is. -/
private theorem isSurjective_of_isPullback_presheaf
    {W Z X Y : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hg : IsSurjective B (Spec (CommRingCat.of k)) hk g) :
    IsSurjective B (Spec (CommRingCat.of k)) hk q := by
  intro x
  obtain ⟨z, hz⟩ := hg (pointsMap B (Spec (CommRingCat.of k)) hk X f x)
  obtain ⟨w, -, hwq⟩ := exists_point_of_isPullback_presheaf B (Spec (CommRingCat.of k)) hk
    sq z x hz
  exact ⟨w, hwq⟩

/-- The first projection of a binary product of presheaves is surjective on points as soon as
the structure morphism of the second factor is: it is its base change. -/
theorem isSurjective_prod_fst
    {F G : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
    (hG : IsSurjective B (Spec (CommRingCat.of k)) hk ((base_isTerminal k B hk).from G)) :
    IsSurjective B (Spec (CommRingCat.of k)) hk (Limits.prod.fst : F ⨯ G ⟶ F) :=
  isSurjective_of_isPullback_presheaf (isPullback_prod_base F G).flip hG

variable (k B hk)

/-- The structure morphism of a power of the projective line indexed by `Fin m` is surjective
on points. -/
theorem isSurjective_projectiveLinePowerFinToBase (m : ℕ) :
    IsSurjective B (Spec (CommRingCat.of k)) hk (projectiveLinePowerToBase k B hk (Fin m)) := by
  induction m with
  | zero =>
    have := isIso_projectiveLinePowerToBase_fin_zero k B hk
    exact isSurjective_of_isIso B (Spec (CommRingCat.of k)) hk _
  | succ m ih =>
    have heq : projectiveLinePowerToBase k B hk (Fin (m + 1)) =
        (piFinSuccIso (projectiveLineFunctor k B hk) m).hom ≫
          (Limits.prod.fst ≫ projectiveLinePowerToBase k B hk (Fin m)) :=
      (base_isTerminal k B hk).hom_ext _ _
    rw [heq]
    exact isSurjective_comp B (Spec (CommRingCat.of k)) hk
      (isSurjective_of_isIso B (Spec (CommRingCat.of k)) hk _)
      (isSurjective_comp B (Spec (CommRingCat.of k)) hk
        (isSurjective_prod_fst (isSurjective_projectiveLineToBase k B hk)) ih)

/-- The structure morphism of a power of the projective line indexed by a finite type is
surjective on points. -/
theorem isSurjective_projectiveLinePowerToBase (α : Type v) [Small.{u} α] [Finite α] :
    IsSurjective B (Spec (CommRingCat.of k)) hk (projectiveLinePowerToBase k B hk α) := by
  have heq : projectiveLinePowerToBase k B hk α =
      (projectiveLinePowerReindexIso k B hk (Finite.equivFin α)).hom ≫
        projectiveLinePowerToBase k B hk (Fin (Nat.card α)) :=
    (base_isTerminal k B hk).hom_ext _ _
  rw [heq]
  exact isSurjective_comp B (Spec (CommRingCat.of k)) hk
    (isSurjective_of_isIso B (Spec (CommRingCat.of k)) hk _)
    (isSurjective_projectiveLinePowerFinToBase k B hk _)

/-! ### The coordinate projection as a base change -/

/-- The projection of a finite power of the projective line onto the coordinates *outside* a
finite subset. -/
noncomputable abbrev coordinateProjectionCompl (n : ℕ) (I : Finset (Fin n)) :
    projectiveLinePower k B hk (Fin n) ⟶
      projectiveLinePower k B hk {j : Fin n // j ∉ I} :=
  Pi.map' (fun j : {j : Fin n // j ∉ I} => (j : Fin n)) fun _ => 𝟙 _

/-- **A finite power of the projective line is the product of the coordinates in a finite
subset with the coordinates outside it**, the two coordinate projections being the projections
of the product. -/
noncomputable def isLimit_binaryFan_coordinateProjection (n : ℕ) (I : Finset (Fin n)) :
    IsLimit (BinaryFan.mk (coordinateProjection k B hk n I)
      (coordinateProjectionCompl k B hk n I)) := by
  classical
  refine BinaryFan.isLimitMk
    (fun s => Pi.lift fun j => if h : j ∈ I then
      s.fst ≫ Pi.π (fun _ : I => projectiveLineFunctor k B hk) ⟨j, h⟩
    else s.snd ≫ Pi.π (fun _ : {j : Fin n // j ∉ I} => projectiveLineFunctor k B hk) ⟨j, h⟩)
    (fun s => ?_) (fun s => ?_) (fun s m hm₁ hm₂ => ?_)
  · refine Pi.hom_ext _ _ fun a => ?_
    rw [Category.assoc, Pi.map'_comp_π, ← Category.assoc, Pi.lift_comp_π]
    simp
  · refine Pi.hom_ext _ _ fun a => ?_
    rw [Category.assoc, Pi.map'_comp_π, ← Category.assoc, Pi.lift_comp_π]
    simp [a.2]
  · refine Pi.hom_ext _ _ fun j => ?_
    rw [Pi.lift_comp_π]
    by_cases h : j ∈ I
    · rw [dite_eq_left h, ← hm₁, Category.assoc, Pi.map'_comp_π]
      simp
    · rw [dite_eq_right h, ← hm₂, Category.assoc, Pi.map'_comp_π]
      simp

/-- **The coordinate projection is the base change of the structure morphism of the power on
the complementary coordinates.** -/
theorem isPullback_coordinateProjection (n : ℕ) (I : Finset (Fin n)) :
    IsPullback (coordinateProjection k B hk n I) (coordinateProjectionCompl k B hk n I)
      (projectiveLinePowerToBase k B hk I)
      (projectiveLinePowerToBase k B hk {j : Fin n // j ∉ I}) :=
  IsPullback.of_is_product (isLimit_binaryFan_coordinateProjection k B hk n I)
    (base_isTerminal k B hk)

/-! ### The three properties of the coordinate projection -/

/-- **The coordinate projection `(ℙ¹_k)^n ⟶ (ℙ¹_k)^I` is surjective.** It is the base change of
the structure morphism of `(ℙ¹_k)^{Iᶜ}`, which is surjective. -/
theorem isSurjective_coordinateProjection (n : ℕ) (I : Finset (Fin n)) :
    IsSurjective B (Spec (CommRingCat.of k)) hk (coordinateProjection k B hk n I) :=
  isSurjective_of_isPullback_presheaf (isPullback_coordinateProjection k B hk n I).flip
    (isSurjective_projectiveLinePowerToBase k B hk {j : Fin n // j ∉ I})

section ChartPropertyProjection

variable (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
  [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
  (hPetale : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y), AlgebraicGeometry.Etale g → P g)
  (hPline : P (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k)))

include hP hPetale hPline in
/-- A property of morphisms of schemes which is étale local on the source and target, stable
under base change and composition, implied by étaleness and true of `ℙ¹_k ⟶ Spec k` holds on
every étale chart of the coordinate projection. -/
theorem holdsOnEveryEtaleChart_coordinateProjection (n : ℕ) (I : Finset (Fin n)) :
    HoldsOnEveryEtaleChart B (Spec (CommRingCat.of k)) hk P
      (coordinateProjection k B hk n I) := by
  have := holdsOnEveryEtaleChart_isStableUnderBaseChange B (Spec (CommRingCat.of k)) hk P hP
  have hI := isAlgebraicSpace_projectiveLinePower k B hk (↥I)
  have hJ := isAlgebraicSpace_projectiveLinePower k B hk {j : Fin n // j ∉ I}
  have hn := isAlgebraicSpace_projectiveLinePowerFin k B hk n
  have sq : IsPullback
      (ObjectProperty.homMk (coordinateProjection k B hk n I) :
        (⟨_, hn⟩ : AlgebraicSpaces B (Spec (CommRingCat.of k)) hk) ⟶ ⟨_, hI⟩)
      (ObjectProperty.homMk (coordinateProjectionCompl k B hk n I) :
        (⟨_, hn⟩ : AlgebraicSpaces B (Spec (CommRingCat.of k)) hk) ⟶ ⟨_, hJ⟩)
      (ObjectProperty.homMk (projectiveLinePowerToBase k B hk I) :
        (⟨_, hI⟩ : AlgebraicSpaces B (Spec (CommRingCat.of k)) hk) ⟶
          ⟨_, isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _⟩)
      (ObjectProperty.homMk (projectiveLinePowerToBase k B hk {j : Fin n // j ∉ I}) :
        (⟨_, hJ⟩ : AlgebraicSpaces B (Spec (CommRingCat.of k)) hk) ⟶
          ⟨_, isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _⟩) :=
    isPullback_algebraicSpaces_homMk _ _ _ _ (isPullback_coordinateProjection k B hk n I)
  exact MorphismProperty.of_isPullback
    (P := fun ⦃X Y : AlgebraicSpaces B (Spec (CommRingCat.of k)) hk⦄ (f : X ⟶ Y) =>
      HoldsOnEveryEtaleChart B (Spec (CommRingCat.of k)) hk P f.hom)
    sq.flip
    (holdsOnEveryEtaleChart_projectiveLinePowerToBase k B hk P hP hPetale hPline
      {j : Fin n // j ∉ I})

end ChartPropertyProjection

/-- **The coordinate projection `(ℙ¹_k)^n ⟶ (ℙ¹_k)^I` is flat.** -/
theorem isFlat_coordinateProjection (n : ℕ) (I : Finset (Fin n)) :
    IsFlat B (Spec (CommRingCat.of k)) hk (coordinateProjection k B hk n I) :=
  holdsOnEveryEtaleChart_coordinateProjection k B hk
    (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
    Flat.isEtaleLocalOnSourceAndTarget (fun _ hg => have := hg; inferInstance)
    inferInstance n I

/-- **The coordinate projection `(ℙ¹_k)^n ⟶ (ℙ¹_k)^I` is locally of finite presentation.** -/
theorem isLocallyOfFinitePresentation_coordinateProjection (n : ℕ) (I : Finset (Fin n)) :
    IsLocallyOfFinitePresentation B (Spec (CommRingCat.of k)) hk
      (coordinateProjection k B hk n I) :=
  holdsOnEveryEtaleChart_coordinateProjection k B hk
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
    (fun _ hg => have := hg; inferInstance) inferInstance n I

end AlgebraicGeometry.Space

end
