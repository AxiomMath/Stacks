module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.FlatStabilizerQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.GerbeCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.GerbeStabilizerFlatness
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.PreEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ArrowQuotientRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.GroupoidBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.MorphismsToAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatRelationQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.DenseOpenFlatInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.Gerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomPresheafFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationStabilizerFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationExistence
public import StacksFrontier.CategoryTheory.Sites.Gerbe.BaseEquivalence
public import StacksFrontier.CategoryTheory.Sites.Gerbe.IsoClasses

/-!
# An algebraic stack with flat, locally finitely presented inertia is a gerbe (Stacks 06QJ)

This file proves the implication (2) `⟹` (1) of **Stacks 06QJ**: an algebraic stack `𝒳` over `S`
whose inertia projection `I_𝒳 ⟶ 𝒳` is flat and locally of finite presentation is a gerbe. It
also proves Stacks 06RC with the quasi-compactness of the inertia read on the automorphism spaces
at scheme-valued points.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.exists_covering_arrow_of_toQuotientSheaf_eq`: two
  points of the object space with the same image in `U/R'` are joined by an arrow after an fppf
  covering.
* `AlgebraicStacks.isGerbe_of_isFlat_and_isLocallyOfFinitePresentation_inertiaProjection`:
  **Stacks 06QJ**, the implication (2) `⟹` (1).
* `AlgebraicGeometry.Stack.exists_dense_openSubstack_isGerbe_of_isomSpace`: a reduced algebraic
  stack whose automorphism spaces at scheme-valued points are quasi-compact has a dense open
  substack which is a gerbe.

## References

* [Stacks Project, Tag 046O](https://stacks.math.columbia.edu/tag/046O)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04T3](https://stacks.math.columbia.edu/tag/04T3)
* [Stacks Project, Tag 06PE](https://stacks.math.columbia.edu/tag/06PE)
* [Stacks Project, Tag 06PH](https://stacks.math.columbia.edu/tag/06PH)
* [Stacks Project, Tag 06PR](https://stacks.math.columbia.edu/tag/06PR)
* [Stacks Project, Tag 06QJ](https://stacks.math.columbia.edu/tag/06QJ)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} [HasSheafify (BigFppfOver.topology C S hS) (Type u)]

/-- A point of the quotient `R' = R/S` of the arrow space by the stabilizer action lifts, after
an fppf covering, to an arrow of the groupoid with the same source and the same target. -/
theorem exists_covering_arrow_of_arrowStabilizerQuotient
    (G : GroupoidInAlgebraicSpaces C S hS B) {T : BigFppfOver C S hS}
    (r : (arrowStabilizerQuotient G).obj.obj (op T)) :
    ∃ W ∈ BigFppfOver.topology C S hS T,
      ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T), W i →
        ∃ a : G.arrows.obj.obj (op V),
          G.source.hom.app (op V) a =
              G.objects.obj.map i.op ((arrowStabilizerQuotientSource G).app (op T) r) ∧
            G.target.hom.app (op V) a =
              G.objects.obj.map i.op ((arrowStabilizerQuotientTarget G).app (op T) r) := by
  refine ⟨Presheaf.imageSieve (toArrowStabilizerQuotient G) r,
    isLocallySurjective_toArrowStabilizerQuotient G |>.imageSieve_mem r, fun V i hi => ?_⟩
  obtain ⟨a, ha⟩ := hi
  refine ⟨a, ?_, ?_⟩
  · rw [← arrowStabilizerQuotientSource_app_toArrowStabilizerQuotient, ha,
      NatTrans.naturality_apply]
  · rw [← arrowStabilizerQuotientTarget_app_toArrowStabilizerQuotient, ha,
      NatTrans.naturality_apply]

/-- Two points of the object space of a groupoid in algebraic spaces with the same image in the
quotient `U/R'` of the object space by `j' = (t', s')` are the source and the target of an arrow
of the groupoid after an fppf covering. -/
theorem exists_covering_arrow_of_toQuotientSheaf_eq
    (G : GroupoidInAlgebraicSpaces C S hS B) (T : BigFppfOver C S hS)
    (a b : G.objects.obj.obj (op T))
    (hab : (Space.toQuotientSheaf (arrowStabilizerQuotientPreRelation G)).app (op T) a =
      (Space.toQuotientSheaf (arrowStabilizerQuotientPreRelation G)).app (op T) b) :
    ∃ W ∈ BigFppfOver.topology C S hS T,
      ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T), W i →
        ∃ r : G.arrows.obj.obj (op V),
          G.source.hom.app (op V) r = G.objects.obj.map i.op a ∧
            G.target.hom.app (op V) r = G.objects.obj.map i.op b := by
  obtain ⟨E, hE, hk⟩ := (Space.toQuotientSheaf_eq_iff_locally_related
    (arrowStabilizerQuotientPreRelation G)
    (isPreEquivalenceRelation_arrowStabilizerQuotientPreRelation G) T a b).1 hab
  let W : Sieve T :=
    { arrows := fun V i => ∃ r : G.arrows.obj.obj (op V),
        G.source.hom.app (op V) r = G.objects.obj.map i.op a ∧
          G.target.hom.app (op V) r = G.objects.obj.map i.op b
      downward_closed := by
        rintro V V' i ⟨r, hrs, hrt⟩ j
        refine ⟨G.arrows.obj.map j.op r, ?_, ?_⟩
        · rw [NatTrans.naturality_apply, hrs, op_comp, Functor.map_comp_apply]
        · rw [NatTrans.naturality_apply, hrt, op_comp, Functor.map_comp_apply] }
  refine ⟨W, ?_, fun V i hi => hi⟩
  refine (BigFppfOver.topology C S hS).transitive
    (Space.fppf_hypercover_sieve_mem hS T E hE) W ?_
  rintro Y f ⟨Y', g, f', ⟨k⟩, rfl⟩
  obtain ⟨r, hrs, hrt⟩ := hk k
  obtain ⟨W', hW', hlift⟩ := exists_covering_arrow_of_arrowStabilizerQuotient G r
  refine (BigFppfOver.topology C S hS).superset_covering ?_
    ((BigFppfOver.topology C S hS).pullback_stable g hW')
  intro V h hh
  obtain ⟨c, hcs, hct⟩ := hlift (h ≫ g) hh
  refine ⟨c, ?_, ?_⟩
  · rw [hcs, ← arrowStabilizerQuotientPreRelation_source_left G, ← hrs]
    change G.objects.obj.map (h ≫ g).op (G.objects.obj.map (E.f k).op a) = _
    rw [← Functor.map_comp_apply, ← op_comp, Category.assoc]
  · rw [hct, ← arrowStabilizerQuotientPreRelation_target_left G, ← hrt]
    change G.objects.obj.map (h ≫ g).op (G.objects.obj.map (E.f k).op b) = _
    rw [← Functor.map_comp_apply, ← op_comp, Category.assoc]

/-- The quotient `U/R'` of the object space by `j' = (t', s')` is an algebraic space when the
stabilizer and the source and target maps are flat and locally of finite presentation. -/
theorem isAlgebraicSpace_quotientSheaf_arrowStabilizerQuotientPreRelation
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (hSflat : Space.IsFlat C S hS (stabilizer G).hom)
    (hSfp : Space.IsLocallyOfFinitePresentation C S hS (stabilizer G).hom)
    (hsF : Space.IsFlat C S hS G.source.hom) (htF : Space.IsFlat C S hS G.target.hom)
    (hsL : Space.IsLocallyOfFinitePresentation C S hS G.source.hom)
    (htL : Space.IsLocallyOfFinitePresentation C S hS G.target.hom) :
    IsAlgebraicSpace C S hS (Space.quotientSheaf (arrowStabilizerQuotientPreRelation G)).obj := by
  refine Space.bootstrap04S6QuotientSheaf C S hS (arrowStabilizerQuotientPreRelation G)
    (isAlgebraicSpace_arrowStabilizerQuotient G hSflat hSfp) G.objects.property
    (isEquivalenceRelation_arrowStabilizerQuotientPreRelation G) ?_ ?_ ?_ ?_
  · rw [arrowStabilizerQuotientPreRelation_target_left]
    exact isFlat_arrowStabilizerQuotientTarget G hSflat hSfp htF
  · rw [arrowStabilizerQuotientPreRelation_target_left]
    exact isLocallyOfFinitePresentation_arrowStabilizerQuotientTarget G hSflat hSfp htL
  · rw [arrowStabilizerQuotientPreRelation_source_left]
    exact isFlat_arrowStabilizerQuotientSource G hSflat hSfp hsF
  · rw [arrowStabilizerQuotientPreRelation_source_left]
    exact isLocallyOfFinitePresentation_arrowStabilizerQuotientSource G hSflat hSfp hsL

/-- The quotient map `U ⟶ U/R'` of the object space by `j' = (t', s')` is invariant under the
groupoid. -/
theorem isInvariant_toQuotientSheaf_arrowStabilizerQuotientPreRelation
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Space.IsInvariant (Space.groupoidPreRelation G)
      (Space.toQuotientSheaf (arrowStabilizerQuotientPreRelation G)) := by
  have h := Space.target_toQuotientSheaf_eq_source (arrowStabilizerQuotientPreRelation G)
  rw [arrowStabilizerQuotientPreRelation_target_left,
    arrowStabilizerQuotientPreRelation_source_left] at h
  have h₂ := congrArg (toArrowStabilizerQuotient G ≫ ·) h
  simp only [← Category.assoc, toArrowStabilizerQuotient_comp_target,
    toArrowStabilizerQuotient_comp_source] at h₂
  change (Space.groupoidPreRelation G).target.left ≫ _ =
    (Space.groupoidPreRelation G).source.left ≫ _
  rwa [Stack.groupoidPreRelation_target_left, Stack.groupoidPreRelation_source_left]

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic stack `𝒳` over `S` whose inertia projection `I_𝒳 ⟶ 𝒳` is flat and locally of
finite presentation is a gerbe: there are an algebraic space `X` and a 1-morphism `𝒳 ⟶ X` making
`𝒳` a gerbe over `X`. -/
@[stacks 06QJ "(2) implies (1): an algebraic stack whose inertia projection is flat and locally \
of finite presentation is a gerbe"]
theorem isGerbe_of_isFlat_and_isLocallyOfFinitePresentation_inertiaProjection
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (hflat : IsFlat B S hS (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳))
    (hlfp : IsLocallyOfFinitePresentation B S hS
      (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    IsGerbe B S hS 𝒳 := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  obtain ⟨P⟩ := nonempty_groupoidPresentation B S hS 𝒳.val 𝒳.property
  let G := P.groupoid
  let j' := GroupoidInAlgebraicSpaces.arrowStabilizerQuotientPreRelation G
  have hX : IsAlgebraicSpace B S hS (Space.quotientSheaf j').obj :=
    GroupoidInAlgebraicSpaces.isAlgebraicSpace_quotientSheaf_arrowStabilizerQuotientPreRelation G
      (isFlat_presentationStabilizer B S hS P hflat)
      (isLocallyOfFinitePresentation_presentationStabilizer B S hS P hlfp)
      (Space.isFlat_of_isSmooth B S hS _ P.smooth.1) (Space.isFlat_of_isSmooth B S hS _ P.smooth.2)
      (Space.isLocallyOfFinitePresentation_of_isSmooth B S hS P.smooth.1)
      (Space.isLocallyOfFinitePresentation_of_isSmooth B S hS P.smooth.2)
  let X : AlgebraicSpaces B S hS := ⟨(Space.quotientSheaf j').obj, hX⟩
  let φ : G.objects ⟶ X := ObjectProperty.homMk (Space.toQuotientSheaf j')
  let H := (GroupoidInAlgebraicSpaces.overInvariantTarget G
    ((Stack.isTerminal_baseSpace B S hS).from X) φ
    ((Stack.isTerminal_baseSpace B S hS).hom_ext _ _)
    (GroupoidInAlgebraicSpaces.isInvariant_toQuotientSheaf_arrowStabilizerQuotientPreRelation
      G)).val
  have hΦ : CategoryTheory.IsGerbeOver (BigFppfOver.topology B S hS)
      (fibredCategory B S hS X.obj).val.p (quotientStackToBase H).toFunctor :=
    isGerbeOver_quotientStackToBase_of_locallyFull H
      (fun T b => ⟨Presheaf.imageSieve (Space.toQuotientSheaf j') b,
        (Space.isLocallySurjective_toQuotientSheaf j').imageSieve_mem b, fun V i hi => hi⟩)
      (fun T a b hab =>
        GroupoidInAlgebraicSpaces.exists_covering_arrow_of_toQuotientSheaf_eq G T a b hab)
  let i := P.equivalence.inv.functor
  let F' := (quotientStackToBase H).toFunctor
  have hr : F' ⋙ (fibredCategory B S hS X.obj).val.p = (quotientStack G).p :=
    (quotientStackToBase H).w
  have hp : (i ⋙ F') ⋙ (fibredCategory B S hS X.obj).val.p = 𝒳.val.val.p :=
    (Functor.assoc _ _ _).trans ((congrArg (i ⋙ ·) hr).trans P.equivalence.inv.w)
  have e : Functor.IsEquivalenceOver ((i ⋙ F') ⋙ (fibredCategory B S hS X.obj).val.p)
      (F' ⋙ (fibredCategory B S hS X.obj).val.p) i := by
    rw [hp, hr]
    exact StacksRepresentableCFG.EquivalenceOver.toFunctorIsEquivalenceOver P.equivalence.symm
  exact ⟨Stack.algebraicSpaceStack B S hS X.obj hX,
    isRepresentableByAlgebraicSpace_fibredCategory B S hS X.obj hX,
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom ⟨i ⋙ F', hp⟩),
    CategoryTheory.IsGerbeOver.of_isEquivalenceOver_base_symm rfl e hΦ⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

/-!
## Stacks 06RC with the quasi-compactness read on the automorphism spaces
-/

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Automorphism spaces along a fully faithful 1-morphism -/

/-- **A fully faithful 1-morphism of algebraic stacks preserves automorphism spaces.** For a
1-morphism `i : 𝒳' ⟶ 𝒳` whose underlying functor is fully faithful (an inclusion of a substack),
the automorphism space of an object `x` of `𝒳'` is that of its image in `𝒳`. -/
theorem nonempty_isomSpace_iso_of_fullyFaithful {𝒳' 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (i : 𝒳' ⟶ 𝒳) [(CatFiberedInGroupoids.homFunctor i.hom).Full]
    [(CatFiberedInGroupoids.homFunctor i.hom).Faithful] (U : BigFppfOver B S hS) :
    letI : 𝒳'.val.val.p.IsFibered := 𝒳'.val.isFiberedInGroupoids.isFibered
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    ∀ x : 𝒳'.val.val.p.Fiber U,
      Nonempty (isomSpace B S hS 𝒳'.val U x x ≅
        isomSpace B S hS 𝒳.val U ((Functor.fiberFunctorOfCompEq i.hom.hom.w U).obj x)
          ((Functor.fiberFunctorOfCompEq i.hom.hom.w U).obj x)) := by
  let : 𝒳'.val.val.p.IsFibered := 𝒳'.val.isFiberedInGroupoids.isFibered
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  intro x
  have hLift : 𝒳'.val.val.p.IsFibredOneMorphism 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor i.hom) :=
    { comp_eq := i.hom.hom.w
      map_isStronglyCartesian := by
        intro A A' g a b k hk
        have : 𝒳.val.val.p.IsHomLift g ((CatFiberedInGroupoids.homFunctor i.hom).map k) :=
          Functor.isHomLift_map_of_comp_eq i.hom.hom.w g k
        exact 𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift g _ }
  let e := liftedIsomPresheafIso.{_, _, _, _, _, u} hLift 𝒳'.val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids x x
  exact ⟨(Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (isomSpace B S hS 𝒳'.val U x x) uliftFunctorTrivial.symm ≪≫
    Functor.isoWhiskerLeft (Over.iteratedSliceBackward U).op e⟩

/-- **Quasi-compactness of automorphism spaces passes along a fully faithful 1-morphism**, read
at the scheme-valued points of the source. -/
theorem isQuasiCompact_isomSpace_of_fullyFaithful {𝒳' 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (i : 𝒳' ⟶ 𝒳) [(CatFiberedInGroupoids.homFunctor i.hom).Full]
    [(CatFiberedInGroupoids.homFunctor i.hom).Faithful]
    (hqc : letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
      ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
        (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom),
        Space.IsQuasiCompact B U.left.1 U.left.2
          (terminal.from (isomSpace B S hS 𝒳.val U (Functor.sliceValue 𝒳.val.val.p U y hy)
            (Functor.sliceValue 𝒳.val.val.p U y hy)))) :
    letI : 𝒳'.val.val.p.IsFibered := 𝒳'.val.isFiberedInGroupoids.isFibered
    ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳'.val.val.obj)
      (hy : y ⋙ 𝒳'.val.val.p = Over.map U.hom),
      Space.IsQuasiCompact B U.left.1 U.left.2
        (terminal.from (isomSpace B S hS 𝒳'.val U (Functor.sliceValue 𝒳'.val.val.p U y hy)
          (Functor.sliceValue 𝒳'.val.val.p U y hy))) := by
  let : 𝒳'.val.val.p.IsFibered := 𝒳'.val.isFiberedInGroupoids.isFibered
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  intro U y hy
  have hy' : (y ⋙ CatFiberedInGroupoids.homFunctor i.hom) ⋙ 𝒳.val.val.p = Over.map U.hom := by
    rw [Functor.assoc]
    exact (congrArg (fun F => y ⋙ F) i.hom.hom.w).trans hy
  obtain ⟨e⟩ := nonempty_isomSpace_iso_of_fullyFaithful B S hS i U
    (Functor.sliceValue 𝒳'.val.val.p U y hy)
  have hP : (Space.quasiCompactPresheafProperty B U.left.1 U.left.2).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [show terminal.from (isomSpace B S hS 𝒳'.val U (Functor.sliceValue 𝒳'.val.val.p U y hy)
      (Functor.sliceValue 𝒳'.val.val.p U y hy)) = e.hom ≫ terminal.from _ from
    terminal.hom_ext _ _]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (Space.quasiCompactPresheafProperty B U.left.1 U.left.2) e.hom _).2 (hqc U _ hy')

/-- **Stacks 06RC, with the quasi-compactness read on the automorphism spaces.** Let `𝒳` be a
reduced algebraic stack over `S` whose automorphism spaces at scheme-valued points are
quasi-compact. Then there is an open substack `𝒰` of `𝒳`, dense in `|𝒳|`, which is a gerbe. -/
theorem exists_dense_openSubstack_isGerbe_of_isomSpace
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (hred : IsReducedStack B S hS 𝒳)
    (hqc : letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
      ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
        (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom),
        Space.IsQuasiCompact B U.left.1 U.left.2
          (terminal.from (isomSpace B S hS 𝒳.val U (Functor.sliceValue 𝒳.val.val.p U y hy)
            (Functor.sliceValue 𝒳.val.val.p U y hy)))) :
    ∃ 𝒰 : OpenSubstack 𝒳, @Dense _ (pointTopology B S hS 𝒳.val) (𝒰.pointSet B S hS) ∧
      AlgebraicStacks.IsGerbe B S hS 𝒰.toAlgebraicStack := by
  obtain ⟨𝒰, hdense, hF, hL⟩ :=
    exists_dense_openSubstack_isFlat_isLocallyOfFinitePresentation_inertia_of_isomSpace B S hS 𝒳
      hred hqc
  exact ⟨𝒰, hdense,
    AlgebraicStacks.isGerbe_of_isFlat_and_isLocallyOfFinitePresentation_inertiaProjection
      B S hS _ hF hL⟩

end AlgebraicGeometry.Stack

end
