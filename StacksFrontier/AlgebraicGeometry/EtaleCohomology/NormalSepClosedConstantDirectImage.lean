module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Etale.NormalSepClosedFunctionField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.DerivedFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ZariskiRestrictionSheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.IrreducibleSpaces
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ExtensionByInitial

/-!
# Higher direct images of a constant sheaf on a normal scheme with separably closed function field

Let `f : X ⟶ Y` be a morphism of schemes with `X` integral and normal and with separably closed
function field. Then `R^q f_* M = 0` for every `q > 0` and every abelian group `M`, where `M`
also denotes the constant sheaf on the small étale site of `X`.

The higher direct image is the sheafification of the presheaf sending `V` in `Y_étale` to the
`q`-th étale cohomology of `V ×_Y X`, so it is enough to make that presheaf vanish on affine
`V`. For such a `V` the projection `V ×_Y X ⟶ X` is separated and étale, hence a disjoint union
of open immersions; sections over a coproduct are the product of the sections, so the question
reduces to an open subscheme `U` of `X`. There the open subschemes form a dense subsite of the
small étale site — every étale scheme over `X` is covered by opens of `X`, again because
separated étale morphisms split — so étale sheaves on `U` are Zariski sheaves and the constant
étale sheaf is the constant Zariski sheaf. Finally `U` is irreducible, where a constant sheaf has
no higher cohomology.

## Main results

* `Stacks.EtaleCohomology.opensToEtale_isDenseSubsite` — the open subschemes of such a scheme are
  a dense subsite of its small étale site.
* `Stacks.EtaleCohomology.isZero_rightDerived_smallEtalePushforward_constantSheaf` — the higher
  direct images of a constant abelian étale sheaf vanish.

## Implementation notes

The small étale site is Mathlib's `AlgebraicGeometry.Scheme.Etale`. The direct image is
restriction along the base-change functor `Stacks.EtaleCohomology.smallEtaleBaseChange`, and the
higher direct images are the right derived functors of that restriction on abelian sheaves.
Vanishing is expressed by `CategoryTheory.Limits.IsZero`.

A sheaf of abelian groups in a coefficient universe `w` not containing the universe `u` of the
scheme is zero, because the sections over a `u`-indexed coproduct of copies of one object inject
into the sheaf; that degenerate case is split off first, so the main argument may assume
`UnivLE.{u, w}`.

## References

* [Stacks Project, Tag 0EZP](https://stacks.math.columbia.edu/tag/0EZP)
* [Stacks Project, Tag 09Z9](https://stacks.math.columbia.edu/tag/09Z9)
* [Stacks Project, Tag 09AX](https://stacks.math.columbia.edu/tag/09AX)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 02UW](https://stacks.math.columbia.edu/tag/02UW)
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u w
universe v

namespace Stacks.EtaleCohomology

/-- The pushforward of abelian sheaves along `f : X ⟶ Y` on the small étale sites is an
additive functor. -/
local instance smallEtalePushforward_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((smallEtaleBaseChange f).sheafPushforwardContinuous
      AddCommGrpCat.{w} Y.smallEtaleTopology X.smallEtaleTopology).Additive where
  map_add := by intros; rfl

private noncomputable def smallEtaleHigherDirectImageSheafificationIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{w})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (q : ℕ) :
    (((smallEtaleBaseChange f).sheafPushforwardContinuous
      AddCommGrpCat.{w} Y.smallEtaleTopology X.smallEtaleTopology).rightDerived q).obj F ≅
      (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{w}).obj
        ((((smallEtaleBaseChange f).sheafPushforwardContinuous
          AddCommGrpCat.{w} Y.smallEtaleTopology X.smallEtaleTopology ⋙
          sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{w}).rightDerived q).obj F) := by
  let P := (smallEtaleBaseChange f).sheafPushforwardContinuous
    AddCommGrpCat.{w} Y.smallEtaleTopology X.smallEtaleTopology
  let Q := P ⋙ sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{w}
  let T := presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{w}
  letI : P.Additive := smallEtalePushforward_additive f
  letI : Q.Additive := ⟨by intros; rfl⟩
  letI : T.Additive := Functor.additive_of_preserves_binary_products _
  let e : Q ⋙ T ≅ P :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft P (asIso (sheafificationAdjunction
        Y.smallEtaleTopology AddCommGrpCat.{w}).counit) ≪≫ P.rightUnitor
  exact (DerivedFunctor.rightDerivedIso e q).symm.app F ≪≫
    (DerivedFunctor.rightDerivedEvaluationIso Q T F q).symm

private noncomputable def smallEtaleHigherDirectImageSectionsEvaluationIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{w})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (q : ℕ)
    (V : Y.Etale) :
    ((((smallEtaleBaseChange f).sheafPushforwardContinuous
      AddCommGrpCat.{w} Y.smallEtaleTopology X.smallEtaleTopology ⋙
      sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{w}).rightDerived q).obj F).obj
        (Opposite.op V) ≅
      (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{w} ⋙
        (evaluation X.Etaleᵒᵖ AddCommGrpCat.{w}).obj
          (Opposite.op ((smallEtaleBaseChange f).obj V))).rightDerived q).obj F) := by
  let P := (smallEtaleBaseChange f).sheafPushforwardContinuous
    AddCommGrpCat.{w} Y.smallEtaleTopology X.smallEtaleTopology ⋙
      sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{w}
  let E := (evaluation Y.Etaleᵒᵖ AddCommGrpCat.{w}).obj (Opposite.op V)
  letI : P.Additive := ⟨by intros; rfl⟩
  exact DerivedFunctor.rightDerivedEvaluationIso P E F q

private theorem exists_open_lift_of_separated_etale
    {X U : Scheme.{u}} [IsIntegral X] [IsNormal X]
    [IsSepClosed X.functionField] (f : U ⟶ X) [Etale f] [IsSeparated f] (x : U) :
    ∃ (V : X.Opens) (g : V.toScheme ⟶ U),
      g ≫ f = V.ι ∧ x ∈ Set.range g := by
  classical
  obtain ⟨I, W, j, hj, e, he⟩ := AlgebraicGeometry.exists_coproduct_open_immersions X U f
  let (i : I) : IsOpenImmersion (j i) := hj i
  obtain ⟨⟨i, y⟩, hy⟩ := (AlgebraicGeometry.sigmaMk W).surjective (e.hom x)
  have hy' : Sigma.ι W i y = e.hom x := by
    simpa only [AlgebraicGeometry.sigmaMk_mk] using hy
  let g : (j i).opensRange.toScheme ⟶ U :=
    (j i).isoOpensRange.inv ≫ Sigma.ι W i ≫ e.inv
  refine ⟨(j i).opensRange, g, ?_, ?_⟩
  · dsimp [g]
    rw [← he]
    simp only [Category.assoc, e.inv_hom_id_assoc, Sigma.ι_comp_desc,
      Scheme.Hom.isoOpensRange_inv_comp]
  · refine ⟨(j i).isoOpensRange.hom y, ?_⟩
    simpa [g, Scheme.Hom.comp_apply] using congrArg (fun z => e.inv z) hy'

private theorem exists_open_lift_of_etale
    {X U : Scheme.{u}} [IsIntegral X] [IsNormal X]
    [IsSepClosed X.functionField] (f : U ⟶ X) [Etale f] (x : U) :
    ∃ (V : X.Opens) (g : V.toScheme ⟶ U),
      g ≫ f = V.ι ∧ x ∈ Set.range g := by
  obtain ⟨i, y, rfl⟩ := U.affineCover.exists_eq x
  obtain ⟨V, g, hg, z, hz⟩ :=
    exists_open_lift_of_separated_etale (U.affineCover.f i ≫ f) y
  exact ⟨V, g ≫ U.affineCover.f i, by simpa only [Category.assoc] using hg,
    z, by simp only [Scheme.Hom.comp_apply, hz]⟩

private theorem opensToEtale_isCoverDense
    (X : Scheme.{u}) [IsIntegral X] [IsNormal X]
    [IsSepClosed X.functionField] :
    (opensToEtale X).IsCoverDense X.smallEtaleTopology where
  is_cover U := by
    classical
    have h (x : U.left) := exists_open_lift_of_etale (X := X) U.hom x
    choose V g hg hx using h
    let a (x : U.left) : (opensToEtale X).obj (V x) ⟶ U :=
      MorphismProperty.Over.homMk (g x) (hg x)
    have ha : Sieve.ofArrows _ a ∈ X.smallEtaleTopology U :=
      (Scheme.ofArrows_mem_smallEtaleTopology_iff a).mpr
        (Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨x, hx x⟩)
    apply X.smallEtaleTopology.superset_covering _ ha
    rintro W b ⟨T, c, _, ⟨x⟩, hc⟩
    exact ⟨⟨V x, c, a x, hc⟩⟩

private theorem opensToEtale_full (X : Scheme.{u}) :
    (opensToEtale X).Full where
  map_surjective {U V} f := by
    have hUV : U ≤ V := by
      intro x hx
      have hw : f.left ≫ V.ι = U.ι := MorphismProperty.Over.w f
      have h : (f.left ⟨x, hx⟩).val = x :=
        (Scheme.Hom.comp_apply f.left V.ι ⟨x, hx⟩).symm.trans
          (congrArg (fun k : U.toScheme ⟶ X => k ⟨x, hx⟩) hw)
      exact h ▸ (f.left ⟨x, hx⟩).property
    refine ⟨homOfLE hUV, ?_⟩
    apply MorphismProperty.Comma.Hom.ext'
    apply Over.OverMorphism.ext
    apply (cancel_mono V.ι).mp
    exact (X.homOfLE_ι hUV).trans (MorphismProperty.Over.w f).symm

private theorem opensToEtale_functorPushforward_mem_iff (X : Scheme.{u})
    (U : X.Opens) (S : Sieve U) :
    S.functorPushforward (opensToEtale X) ∈
      X.smallEtaleTopology ((opensToEtale X).obj U) ↔
        S ∈ Opens.grothendieckTopology X U := by
  obtain ⟨I, V, f, rfl⟩ := S.exists_eq_ofArrows
  rw [Sieve.functorPushforward_ofArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff,
    Opens.mem_grothendieckTopology]
  constructor
  · intro h x hx
    have hm : (⟨x, hx⟩ : U) ∈ ⋃ i, Set.range
        (((opensToEtale X).map (f i)).left) := h ▸ Set.mem_univ _
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hm
    refine ⟨V i, f i, Sieve.ofArrows_mk _ _ i, ?_⟩
    have hy' : y.1 = x := by
      have h := congrArg Subtype.val hy
      change (X.homOfLE (f i).le y).val = x at h
      exact (X.homOfLE_apply (f i).le y).symm.trans h
    exact hy' ▸ y.2
  · intro h
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨W, g, hg, hx⟩ := h x.1 x.2
    obtain ⟨i, a, ha⟩ := Sieve.ofArrows.exists hg
    refine Set.mem_iUnion.mpr ⟨i, ⟨x.1, a.le hx⟩, ?_⟩
    apply Subtype.ext
    change (X.homOfLE (f i).le ⟨x.1, a.le hx⟩).val = x.val
    exact X.homOfLE_apply _ _

private theorem opensToEtale_isDenseSubsite
    (X : Scheme.{u}) [IsIntegral X] [IsNormal X]
    [IsSepClosed X.functionField] :
    (opensToEtale X).IsDenseSubsite
      (Opens.grothendieckTopology X) X.smallEtaleTopology := by
  let := opensToEtale_isCoverDense X
  let := opensToEtale_full X
  let : (opensToEtale X).Faithful := ⟨fun _ => Subsingleton.elim _ _⟩
  exact { functorPushforward_mem_iff :=
    fun {U} {S} => opensToEtale_functorPushforward_mem_iff X U S }

private noncomputable def constantSheafZariskiRestrictionIso
    (X : Scheme.{u}) [IsIntegral X] [IsNormal X]
    [IsSepClosed X.functionField]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
    [∀ V : X.Etaleᵒᵖ,
      HasLimitsOfShape (StructuredArrow V (opensToEtale X).op) AddCommGrpCat.{w}]
    (M : AddCommGrpCat.{w}) :
    (zariskiRestrictionFunctor X).obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{w}).obj M) ≅
        (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}).obj M := by
  letI := opensToEtale_isDenseSubsite X
  let G := opensToEtale X
  let J := Opens.grothendieckTopology X
  let K := X.smallEtaleTopology
  let E := Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{w}
  let F := (constantSheaf K AddCommGrpCat.{w}).obj M
  let e := (Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility
    J K G AddCommGrpCat.{w}).app ((Functor.const X.Etaleᵒᵖ).obj M)
  exact ((asIso (sheafificationAdjunction J AddCommGrpCat.{w}).counit).app
    (E.inverse.obj F)) ≪≫ e.symm

private theorem isZero_sheafify_of_isCoverDense
    {C D A : Type*} [Category C] [Category D] [Category A]
    [HasZeroMorphisms A] [HasZeroObject A]
    (J : GrothendieckTopology D) [HasSheafify J A]
    (G : C ⥤ D) [G.IsCoverDense J] [G.IsLocallyFull J]
    (P : Dᵒᵖ ⥤ A) (h : ∀ U : C, IsZero (P.obj (Opposite.op (G.obj U)))) :
    IsZero ((presheafToSheaf J A).obj P) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply ((sheafificationAdjunction J A).homEquiv P _).injective
  apply (Functor.whiskerLeft_obj_map_bijective_of_isCoverDense J G P
    ((presheafToSheaf J A).obj P).obj ((presheafToSheaf J A).obj P).property).injective
  ext U
  exact (h U.unop).eq_of_src _ _

private theorem isZero_rightDerived_of_subsingleton_ext
    {A : Type*} [Category A] [Abelian A] [HasExt.{v} A]
    [HasInjectiveResolutions A]
    (G : A ⥤ AddCommGrpCat.{w}) [G.Additive] (Z F : A)
    (e : ∀ W : A, (Z ⟶ W) ≃+ G.obj W)
    (he : ∀ {W W' : A} (a : Z ⟶ W) (g : W ⟶ W'),
      e W' (a ≫ g) = G.map g (e W a))
    (q : ℕ) (hq : 0 < q) (h : Subsingleton (Abelian.Ext Z F q)) :
    IsZero ((G.rightDerived q).obj F) := by
  cases q with
  | zero => omega
  | succ n =>
    let I := injectiveResolution F
    apply IsZero.of_iso _ (I.isoRightDerivedObj G (n + 1))
    change IsZero (((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology (n + 1))
    rw [← HomologicalComplex.exactAt_iff_isZero_homology,
      HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
      ShortComplex.ab_exact_iff]
    intro x hx
    change G.obj (I.cocomplex.X (n + 1)) at x
    change G.map (I.cocomplex.d (n + 1) (n + 2)) x = 0 at hx
    let a : Z ⟶ I.cocomplex.X (n + 1) := (e _).symm x
    have ha : a ≫ I.cocomplex.d (n + 1) (n + 2) = 0 := by
      apply (e _).injective
      rw [he, map_zero]
      dsimp only [a]
      rw [AddEquiv.apply_symm_apply]
      exact hx
    obtain ⟨b, hb⟩ := (I.extMk_eq_zero_iff a (n + 2) rfl ha n rfl).mp (h.elim _ _)
    refine ⟨e _ b, ?_⟩
    change G.map (I.cocomplex.d n (n + 1)) (e _ b) = x
    rw [← he, hb]
    exact (e _).apply_symm_apply x

private theorem sheafSections_additive
    {C : Type*} [Category C] (J : GrothendieckTopology C) (T : C) :
    ((sheafSections J AddCommGrpCat.{w}).obj (Opposite.op T)).Additive where
  map_add := by intros; rfl

attribute [local instance] sheafSections_additive

private theorem isZero_rightDerived_sections_of_subsingleton_cohomology
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{v} (Sheaf J AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{w})]
    {T : C} (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{w})
    (q : ℕ) (hq : 0 < q) (h : Subsingleton (Sheaf.H.{v} F q)) :
    IsZero ((((sheafSections J AddCommGrpCat.{w}).obj (Opposite.op T)).rightDerived q).obj F) := by
  let Z := (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))
  let e (W : Sheaf J AddCommGrpCat.{w}) : (Z ⟶ W) ≃+ W.obj.obj (Opposite.op T) :=
    ((constantSheafAdj J AddCommGrpCat.{w} hT).homAddEquiv _ W).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  apply isZero_rightDerived_of_subsingleton_ext
    ((sheafSections J AddCommGrpCat.{w}).obj (Opposite.op T)) Z F e _ q hq h
  intro W W' a g
  change ((constantSheafAdj J AddCommGrpCat.{w} hT).homEquiv _ W' (a ≫ g))
      (ULift.up (1 : ℤ)) =
    g.hom.app (Opposite.op T)
      (((constantSheafAdj J AddCommGrpCat.{w} hT).homEquiv _ W a) (ULift.up (1 : ℤ)))
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private theorem etaleSections_isZero_of_isEmpty
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w})
    (V : X.Etale) [IsEmpty V.left] : IsZero (F.obj.obj (Opposite.op V)) := by
  have h : (⊥ : Sieve V) ∈ X.smallEtaleTopology V := by
    have he : Sieve.ofArrows (fun _ : PEmpty.{1} => V) (fun _ => 𝟙 V) = ⊥ := by
      ext W g
      simp only [Sieve.ofArrows, Sieve.generate_apply, Sieve.bot_apply, iff_false]
      rintro ⟨T, b, c, ⟨i⟩, _⟩
      exact i.elim
    rw [← he]
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
    exact Set.eq_univ_of_forall fun x => isEmptyElim x
  exact (F.isTerminalOfBotCover V h).isZero

private theorem etaleSheaf_amalgamate_disjoint
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w})
    {I : Type*} {V : X.Etale} {U : I → X.Etale} (a : ∀ i, U i ⟶ V)
    (hc : Sieve.ofArrows U a ∈ X.smallEtaleTopology V)
    (hd : ∀ ⦃W : X.Etale⦄ ⦃i j : I⦄ (b : W ⟶ U i) (c : W ⟶ U j),
      b ≫ a i = c ≫ a j → i ≠ j → IsEmpty W.left)
    [∀ i, Mono (a i)] {A : AddCommGrpCat.{w}}
    (s : ∀ i, A ⟶ F.obj.obj (Opposite.op (U i))) :
    ∃! t : A ⟶ F.obj.obj (Opposite.op V), ∀ i, t ≫ F.obj.map (a i).op = s i := by
  apply F.property.existsUnique_amalgamation_ofArrows a hc s
  intro W i j b c h
  by_cases hij : i = j
  · subst j
    obtain rfl : b = c := (cancel_mono (a i)).mp h
    rfl
  · have := hd b c h hij
    exact (etaleSections_isZero_of_isEmpty F W).eq_of_tgt _ _

private noncomputable def etaleCoproduct {X : Scheme.{u}} {I : Type u}
    (U : I → X.Etale) : X.Etale := by
  letI : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Etale)
  letI : Etale (Sigma.desc fun i => (U i).hom) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{u}) (fun i => inferInstance)
  exact .mk (Sigma.desc fun i => (U i).hom)

private noncomputable def etaleCoproductι {X : Scheme.{u}} {I : Type u}
    (U : I → X.Etale) (i : I) : U i ⟶ etaleCoproduct U :=
  MorphismProperty.Over.homMk (Sigma.ι (fun i => (U i).left) i)
    (by
      change Sigma.ι _ i ≫ Sigma.desc _ = _
      simp)

private theorem etaleSheaf_amalgamate_coproduct
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w})
    {I : Type u} (U : I → X.Etale) {A : AddCommGrpCat.{w}}
    (s : ∀ i, A ⟶ F.obj.obj (Opposite.op (U i))) :
    ∃! t : A ⟶ F.obj.obj (Opposite.op
        (etaleCoproduct U)),
      ∀ i, t ≫ F.obj.map
        (etaleCoproductι U i).op = s i := by
  let V : X.Etale := etaleCoproduct U
  let a (i : I) : U i ⟶ V := etaleCoproductι U i
  let (i : I) : Mono (a i) := by
    apply (Scheme.Etale.forget X ⋙ Over.forget X).mono_of_mono_map
    change Mono (Sigma.ι (fun i => (U i).left) i)
    infer_instance
  apply etaleSheaf_amalgamate_disjoint F a
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨⟨i, y⟩, hy⟩ := (AlgebraicGeometry.sigmaMk fun i => (U i).left).surjective x
    exact Set.mem_iUnion.mpr ⟨i, y, by
      change Sigma.ι (fun i => (U i).left) i y = x
      simpa only [AlgebraicGeometry.sigmaMk_mk] using hy⟩
  · intro W i j b c h hij
    refine ⟨fun x => hij ?_⟩
    have he := congrArg (fun g : W ⟶ V => g.left x) h
    change (b.left ≫ Sigma.ι (fun i => (U i).left) i) x =
      (c.left ≫ Sigma.ι (fun i => (U i).left) j) x at he
    have hs : (Sigma.mk i (b.left x) : Σ i, (U i).left) = Sigma.mk j (c.left x) := by
      apply (AlgebraicGeometry.sigmaMk fun i => (U i).left).injective
      simpa only [AlgebraicGeometry.sigmaMk_mk, Scheme.Hom.comp_apply] using he
    exact congrArg Sigma.fst hs

private theorem univLE_of_nonzero_etaleSheaf
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w})
    (V : X.Etale) {A : AddCommGrpCat.{w}}
    (s t : A ⟶ F.obj.obj (Opposite.op V)) (hst : s ≠ t) : UnivLE.{u, w} := by
  classical
  constructor
  intro I
  let U : I → X.Etale := fun _ => V
  let C : X.Etale := etaleCoproduct U
  let v (i : I) : A ⟶ F.obj.obj (Opposite.op C) :=
    (etaleSheaf_amalgamate_coproduct F U (fun j => if i = j then s else t)).choose
  apply small_of_injective (f := v)
  intro i j h
  by_contra hij
  have h' := congrArg (fun k => k ≫ F.obj.map
    (etaleCoproductι U i).op) h
  have hi := (etaleSheaf_amalgamate_coproduct F U
    (fun k => if i = k then s else t)).choose_spec.1 i
  have hj := (etaleSheaf_amalgamate_coproduct F U
    (fun k => if j = k then s else t)).choose_spec.1 i
  exact hst (by simpa [v, hi, hj, hij, Ne.symm hij] using h')

private theorem isZero_etaleSheaf_of_not_univLE
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w})
    (h : ¬ UnivLE.{u, w}) : IsZero F := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  exact Classical.byContradiction fun hn =>
    h (univLE_of_nonzero_etaleSheaf F V.unop _ _ hn)

private theorem uliftZMultiplesAddEquiv_comp
    {A B : AddCommGrpCat.{w}} (t : AddCommGrpCat.of (ULift.{w} ℤ) ⟶ A) (g : A ⟶ B) :
    AddCommGrpCat.uliftZMultiplesAddEquiv B (t ≫ g) =
      g (AddCommGrpCat.uliftZMultiplesAddEquiv A t) := rfl

private theorem etaleSheaf_coproduct_sections_surjective
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w})
    {I : Type u} (U : I → X.Etale) :
    Function.Surjective (fun t : F.obj.obj (Opposite.op (etaleCoproduct U)) =>
      fun i => F.obj.map (etaleCoproductι U i).op t) := by
  intro s
  let e (A : AddCommGrpCat.{w}) := AddCommGrpCat.uliftZMultiplesAddEquiv A
  obtain ⟨t, ht, _⟩ := etaleSheaf_amalgamate_coproduct F U
    (fun i => (e _).symm (s i))
  refine ⟨e _ t, funext fun i => ?_⟩
  simpa only [e, uliftZMultiplesAddEquiv_comp, AddEquiv.apply_symm_apply]
    using congrArg (e _) (ht i)

private theorem etaleSheaf_coproduct_sections_injective
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w})
    {I : Type u} (U : I → X.Etale) :
    Function.Injective (fun t : F.obj.obj (Opposite.op (etaleCoproduct U)) =>
      fun i => F.obj.map (etaleCoproductι U i).op t) := by
  intro s t h
  let e (A : AddCommGrpCat.{w}) := AddCommGrpCat.uliftZMultiplesAddEquiv A
  apply (e _).symm.injective
  obtain ⟨a, ha, hu⟩ := etaleSheaf_amalgamate_coproduct F U
    (fun i => (e _).symm (F.obj.map (etaleCoproductι U i).op s))
  have hs : (e _).symm s = a := by
    apply hu
    intro i
    apply (e _).injective
    simp only [e, uliftZMultiplesAddEquiv_comp, AddEquiv.apply_symm_apply]
  have ht : (e _).symm t = a := by
    apply hu
    intro i
    apply (e _).injective
    simpa only [e, uliftZMultiplesAddEquiv_comp, AddEquiv.apply_symm_apply]
      using congrFun h i |>.symm
  exact hs.trans ht.symm

private theorem isZero_rightDerived_etaleCoproduct_of_components
    {X : Scheme.{u}} [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{w})]
    {I : Type u} (U : I → X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (q : ℕ) (hq : 0 < q)
    (h : ∀ i, IsZero
      ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{w}).obj
        (Opposite.op (U i))).rightDerived q).obj F)) :
    IsZero ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{w}).obj
      (Opposite.op (etaleCoproduct U))).rightDerived q).obj F) := by
  cases q with
  | zero => omega
  | succ n =>
    let R := injectiveResolution F
    let G (V : X.Etale) := (sheafSections X.smallEtaleTopology AddCommGrpCat.{w}).obj
      (Opposite.op V)
    have he (i : I) :
        (((G (U i)).mapHomologicalComplex (.up ℕ)).obj R.cocomplex).ExactAt (n + 1) := by
      apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
      exact (h i).of_iso (R.isoRightDerivedObj (G (U i)) (n + 1)).symm
    apply IsZero.of_iso _ (R.isoRightDerivedObj (G (etaleCoproduct U)) (n + 1))
    change IsZero ((((G (etaleCoproduct U)).mapHomologicalComplex (.up ℕ)).obj
      R.cocomplex).homology (n + 1))
    rw [← HomologicalComplex.exactAt_iff_isZero_homology,
      HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
      ShortComplex.ab_exact_iff]
    intro x hx
    change (R.cocomplex.X (n + 1)).obj.obj (Opposite.op (etaleCoproduct U)) at x
    have hb (i : I) : ∃ y,
        (R.cocomplex.d n (n + 1)).hom.app (Opposite.op (U i)) y =
          (R.cocomplex.X (n + 1)).obj.map (etaleCoproductι U i).op x := by
      have hi := (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2)
        (by simp) (by simp)).mp (he i)
      apply ((ShortComplex.ab_exact_iff _).mp hi)
      change (R.cocomplex.d (n + 1) (n + 2)).hom.app (Opposite.op (U i))
        ((R.cocomplex.X (n + 1)).obj.map (etaleCoproductι U i).op x) = 0
      have hn := ConcreteCategory.congr_hom
        ((R.cocomplex.d (n + 1) (n + 2)).hom.naturality (etaleCoproductι U i).op) x
      change (R.cocomplex.d (n + 1) (n + 2)).hom.app
        (Opposite.op (etaleCoproduct U)) x = 0 at hx
      simpa only [AddCommGrpCat.comp_apply, hx, map_zero] using hn
    choose b hb using hb
    obtain ⟨y, hy⟩ := etaleSheaf_coproduct_sections_surjective (R.cocomplex.X n) U b
    refine ⟨y, ?_⟩
    change (R.cocomplex.d n (n + 1)).hom.app
      (Opposite.op (etaleCoproduct U)) y = x
    apply etaleSheaf_coproduct_sections_injective (R.cocomplex.X (n + 1)) U
    funext i
    have hn := ConcreteCategory.congr_hom
      ((R.cocomplex.d n (n + 1)).hom.naturality (etaleCoproductι U i).op) y
    have hyi := congrFun hy i
    change (R.cocomplex.X n).obj.map (etaleCoproductι U i).op y = b i at hyi
    change (R.cocomplex.d n (n + 1)).hom.app (Opposite.op (U i))
      ((R.cocomplex.X n).obj.map (etaleCoproductι U i).op y) = _ at hn
    exact hn.symm.trans (by rw [hyi, hb])

/-- Vanishing of derived sections over `W` transfers along an isomorphism `V ≅ W` in `X_étale`. -/
private theorem isZero_rightDerived_etaleSections_of_iso
    {X : Scheme.{u}} [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{w})]
    {V W : X.Etale} (e : V ≅ W) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (q : ℕ)
    (h : IsZero ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{w}).obj
      (Opposite.op W)).rightDerived q).obj F)) :
    IsZero ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{w}).obj
      (Opposite.op V)).rightDerived q).obj F) :=
  h.of_iso ((DerivedFunctor.rightDerivedIso
    ((sheafSections X.smallEtaleTopology AddCommGrpCat.{w}).mapIso e.op) q).symm.app F)

private noncomputable def mapInjectiveResolution
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (G : A ⥤ B) [G.Additive] [G.PreservesHomology] [G.PreservesInjectiveObjects]
    {F : A} (R : InjectiveResolution F) : InjectiveResolution (G.obj F) where
  cocomplex := (G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex
  injective n := G.injective_obj_of_injective (R.injective n)
  ι := (HomologicalComplex.singleMapHomologicalComplex G (.up ℕ) 0).inv.app F ≫
    (G.mapHomologicalComplex (.up ℕ)).map R.ι

private noncomputable def rightDerivedCompIso_of_preservesInjectiveObjects
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasInjectiveResolutions A] [HasInjectiveResolutions B]
    (G : A ⥤ B) (H : B ⥤ C) [G.Additive] [H.Additive]
    [G.PreservesHomology] [G.PreservesInjectiveObjects] (F : A) (q : ℕ) :
    ((G ⋙ H).rightDerived q).obj F ≅ (H.rightDerived q).obj (G.obj F) := by
  let R := injectiveResolution F
  exact R.isoRightDerivedObj (G ⋙ H) q ≪≫
    (HomologicalComplex.homologyFunctor C (.up ℕ) q).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ H)) (.up ℕ)).app R.cocomplex) ≪≫
    ((mapInjectiveResolution G R).isoRightDerivedObj H q).symm

private theorem extendByInitialFunctor_preservesMonomorphisms
    {T : TopCat.{u}} (U : Opens T) :
    (TopCat.Presheaf.extendByInitialFunctor (C := AddCommGrpCat.{w}) U).PreservesMonomorphisms := by
  classical
  constructor
  intro F G f hf
  rw [NatTrans.mono_iff_mono_app]
  intro V
  change Mono (TopCat.Presheaf.ExtensionByInitial.appMap U f V)
  unfold TopCat.Presheaf.ExtensionByInitial.appMap
  split_ifs with hV
  · infer_instance
  · have hz : IsZero (TopCat.Presheaf.ExtensionByInitial.obj U F V) :=
      (TopCat.Presheaf.ExtensionByInitial.isInitial_obj U F hV).isZero
    exact ⟨fun g h _ => hz.eq_of_tgt g h⟩

private theorem sheafRestrict_preservesInjectiveObjects
    {T : TopCat.{u}} (U : Opens T)
    [HasSheafify (Opens.grothendieckTopology U) AddCommGrpCat.{w}]
    [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{w}] :
    (Opens.sheafRestrict (C := AddCommGrpCat.{w}) U).PreservesInjectiveObjects := by
  let := extendByInitialFunctor_preservesMonomorphisms.{u, w} U
  let : (TopCat.Presheaf.extendByInitialSheaf
      (C := AddCommGrpCat.{w}) U).PreservesMonomorphisms := by
    constructor
    intro F G f hf
    change Mono ((presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{w}).map
      ((TopCat.Presheaf.extendByInitialFunctor U).map f.hom))
    let : Mono f := hf
    have : Mono f.hom := by
      change Mono ((sheafToPresheaf _ _).map f)
      exact @Functor.map_mono _ _ _ _ (sheafToPresheaf _ _) _ _ _ f hf
    have : Mono ((TopCat.Presheaf.extendByInitialFunctor U).map f.hom) :=
      Functor.map_mono _ _
    infer_instance
  exact @Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    _ _ _ _ _ _ (TopCat.Presheaf.extendByInitialSheafAdjunction (C := AddCommGrpCat.{w}) U)
    ‹(TopCat.Presheaf.extendByInitialSheaf (C := AddCommGrpCat.{w}) U).PreservesMonomorphisms›

private noncomputable def constantSheafRestrictIso
    {T : TopCat.{u}} (U : Opens T)
    [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{w}]
    [HasSheafify (Opens.grothendieckTopology U) AddCommGrpCat.{w}] :
    constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{w} ⋙
      Opens.sheafRestrict (C := AddCommGrpCat.{w}) U ≅
        constantSheaf (Opens.grothendieckTopology U) AddCommGrpCat.{w} := by
  let a := (constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{w}
    (isTerminalTop : IsTerminal (⊤ : Opens T))).comp
      (TopCat.Presheaf.ExtensionByInitial.sheafRestrictPushforwardAdjunction
        (C := AddCommGrpCat.{w}) U)
  let e : TopCat.Sheaf.pushforward AddCommGrpCat.{w} U.inclusion' ⋙
      (sheafSections (Opens.grothendieckTopology T) AddCommGrpCat.{w}).obj (Opposite.op ⊤) ≅
        (sheafSections (Opens.grothendieckTopology U) AddCommGrpCat.{w}).obj (Opposite.op ⊤) :=
    NatIso.ofComponents (fun F => F.obj.mapIso (eqToIso rfl).op)
      (by
        intro X Y f
        change f.hom.app _ ≫ Y.obj.map _ = X.obj.map _ ≫ f.hom.app _
        exact (f.hom.naturality (eqToIso rfl).hom.op).symm)
  exact (a.ofNatIsoRight e).leftAdjointUniq
    (constantSheafAdj _ _ (isTerminalTop : IsTerminal (⊤ : Opens U)))

private theorem isZero_rightDerived_openSections_constantSheaf
    {T : TopCat.{u}} (U : Opens T) [IrreducibleSpace U]
    [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{w}]
    [HasSheafify (Opens.grothendieckTopology U) AddCommGrpCat.{w}]
    [HasInjectiveResolutions (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{w})]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{w})]
    (M : AddCommGrpCat.{w}) (q : ℕ) (hq : 0 < q) :
    IsZero ((((sheafSections (Opens.grothendieckTopology T) AddCommGrpCat.{w}).obj
      (Opposite.op U)).rightDerived q).obj
        ((constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{w}).obj M)) := by
  let G := Opens.sheafRestrict (C := AddCommGrpCat.{w}) U
  let H := (sheafSections (Opens.grothendieckTopology U) AddCommGrpCat.{w}).obj
    (Opposite.op ⊤)
  let : G.IsLeftAdjoint := ⟨_, ⟨
    TopCat.Presheaf.ExtensionByInitial.sheafRestrictPushforwardAdjunction U⟩⟩
  let : G.IsRightAdjoint := ⟨_, ⟨TopCat.Presheaf.extendByInitialSheafAdjunction U⟩⟩
  let : HasLimitsOfShape (Discrete WalkingPair) ((Opens T)ᵒᵖ ⥤ AddCommGrpCat.{w}) :=
    inferInstance
  let : HasLimitsOfShape (Discrete WalkingPair)
      (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{w}) :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf _ _)
  let : G.Additive := Functor.additive_of_preserves_binary_products _
  let : G.PreservesInjectiveObjects := sheafRestrict_preservesInjectiveObjects U
  let e : G ⋙ H ≅ (sheafSections (Opens.grothendieckTopology T)
      AddCommGrpCat.{w}).obj (Opposite.op U) :=
    NatIso.ofComponents (fun F => F.obj.mapIso (eqToIso
      (Opens.isOpenEmbedding_obj_top U).symm).op)
      (by
        intro X Y f
        change f.hom.app _ ≫ Y.obj.map _ = X.obj.map _ ≫ f.hom.app _
        exact (f.hom.naturality (eqToIso (Opens.isOpenEmbedding_obj_top U).symm).hom.op).symm)
  apply IsZero.of_iso _ ((DerivedFunctor.rightDerivedIso e q).symm.app _)
  apply IsZero.of_iso _ (rightDerivedCompIso_of_preservesInjectiveObjects G H _ q)
  apply IsZero.of_iso _ ((H.rightDerived q).mapIso ((constantSheafRestrictIso U).app M))
  exact isZero_rightDerived_sections_of_subsingleton_cohomology _ isTerminalTop _ q hq
    (Stacks.CohomologyVanishing.subsingleton_sheafH_constantSheaf_of_irreducibleSpace M q hq)

private theorem hasSheafify_opens_of_univLE
    (T : Type u) [TopologicalSpace T] [UnivLE.{u, w}] :
    HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{w} := by
  let : EssentiallySmall.{w} (Opens T) := inferInstance
  let : HasSheafify ((equivSmallModel.{w} (Opens T)).inverse.inducedTopology
      (Opens.grothendieckTopology T)) AddCommGrpCat.{w} := inferInstance
  exact hasSheafifyEssentiallySmallSite _ _

private theorem hasInjectiveResolutions_opens_of_univLE
    (T : Type u) [TopologicalSpace T] [UnivLE.{u, w}]
    [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{w}] :
    HasInjectiveResolutions (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{w}) := by
  let : EssentiallySmall.{w} (Opens T) := inferInstance
  let : HasSheafify ((equivSmallModel.{w} (Opens T)).inverse.inducedTopology
      (Opens.grothendieckTopology T)) AddCommGrpCat.{w} := inferInstance
  let : HasLimitsOfSize.{u, u} AddCommGrpCat.{w} :=
    hasLimitsOfSizeOfUnivLE AddCommGrpCat.{w}
  let : IsGrothendieckAbelian.{w}
      (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{w}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  infer_instance

private theorem isZero_rightDerived_etaleSections_of_isEmpty
    {X : Scheme.{u}} [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{w})]
    (V : X.Etale) [IsEmpty V.left]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (q : ℕ) :
    IsZero ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{w}).obj
      (Opposite.op V)).rightDerived q).obj F) := by
  let R := injectiveResolution F
  let G := (sheafSections X.smallEtaleTopology AddCommGrpCat.{w}).obj (Opposite.op V)
  apply IsZero.of_iso _ (R.isoRightDerivedObj G q)
  exact (((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).sc q).isZero_homology_of_isZero_X₂
    (etaleSections_isZero_of_isEmpty (R.cocomplex.X q) V)

private theorem isZero_rightDerived_etaleOpenSections_constantSheaf
    (X : Scheme.{u}) [IsIntegral X] [IsNormal X]
    [IsSepClosed X.functionField] [UnivLE.{u, w}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{w})]
    (U : X.Opens) (M : AddCommGrpCat.{w}) (q : ℕ) (hq : 0 < q) :
    IsZero ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{w}).obj
      (Opposite.op ((opensToEtale X).obj U))).rightDerived q).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{w}).obj M)) := by
  classical
  by_cases hU : Nonempty U
  · let := hU
    let : Nonempty ((Opens.toTopCat X).obj U) := hU
    let : IrreducibleSpace U := U.isOpenEmbedding.irreducibleSpace
    let := hasSheafify_opens_of_univLE.{u, w} X
    let := hasSheafify_opens_of_univLE.{u, w} U
    let := hasInjectiveResolutions_opens_of_univLE.{u, w} X
    let := hasInjectiveResolutions_opens_of_univLE.{u, w} U
    let := HasExt.standard (Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{w})
    let : HasLimitsOfSize.{u, u} AddCommGrpCat.{w} :=
      hasLimitsOfSizeOfUnivLE AddCommGrpCat.{w}
    let := opensToEtale_isDenseSubsite X
    let E := Functor.IsDenseSubsite.sheafEquiv (Opens.grothendieckTopology X)
      X.smallEtaleTopology (opensToEtale X) AddCommGrpCat.{w}
    let G := E.inverse
    let H := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{w}).obj
      (Opposite.op U)
    let : HasLimitsOfShape (Discrete WalkingPair) (X.Etaleᵒᵖ ⥤ AddCommGrpCat.{w}) :=
      inferInstance
    let : HasLimitsOfShape (Discrete WalkingPair) (Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) :=
      hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf _ _)
    let : PreservesLimitsOfShape (Discrete WalkingPair) G :=
      (E.toAdjunction.rightAdjoint_preservesLimits.{0, 0}).preservesLimitsOfShape
    let : G.IsRightAdjoint := ⟨_, ⟨E.toAdjunction⟩⟩
    let : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isRightAdjoint G
    let : G.Additive := Functor.additive_of_preserves_binary_products _
    change IsZero (((G ⋙ H).rightDerived q).obj _)
    apply IsZero.of_iso _ (rightDerivedCompIso_of_preservesInjectiveObjects G H _ q)
    let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{w}).obj M
    let e : G.obj F ≅ (constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{w}).obj M :=
      ((asIso (sheafificationAdjunction (Opens.grothendieckTopology X)
        AddCommGrpCat.{w}).counit).app (G.obj F)).symm ≪≫
          constantSheafZariskiRestrictionIso X M
    apply IsZero.of_iso _ ((H.rightDerived q).mapIso e)
    exact @isZero_rightDerived_openSections_constantSheaf _ U
      ‹IrreducibleSpace U›
      (hasSheafify_opens_of_univLE.{u, w} X)
      (hasSheafify_opens_of_univLE.{u, w} U)
      (hasInjectiveResolutions_opens_of_univLE.{u, w} X)
      (hasInjectiveResolutions_opens_of_univLE.{u, w} U)
      (HasExt.standard (Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{w})) M q hq
  · let : IsEmpty U := not_nonempty_iff.mp hU
    let : IsEmpty ((opensToEtale X).obj U).left := ‹IsEmpty U›
    exact isZero_rightDerived_etaleSections_of_isEmpty _ _ q

private theorem affineEtale_isCoverDense (X : Scheme.{u}) :
    (ObjectProperty.ι (fun U : X.Etale => IsAffine U.left)).IsCoverDense
      X.smallEtaleTopology where
  is_cover U := by
    let C := U.left.affineCover
    let W (i : C.I₀) : X.Etale := .mk (C.f i ≫ U.hom)
    let a (i : C.I₀) : W i ⟶ U := MorphismProperty.Over.homMk (C.f i)
    have ha : Sieve.ofArrows _ a ∈ X.smallEtaleTopology U := by
      apply (Scheme.ofArrows_mem_smallEtaleTopology_iff a).mpr
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨i, y, hy⟩ := C.exists_eq x
      exact Set.mem_iUnion.mpr ⟨i, y, hy⟩
    apply X.smallEtaleTopology.superset_covering _ ha
    rintro V b ⟨T, c, _, ⟨i⟩, hc⟩
    exact ⟨⟨⟨W i, inferInstanceAs (IsAffine (C.X i))⟩, c, a i, hc⟩⟩

private theorem isZero_rightDerived_smallEtalePushforward_of_affine_sections
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{w})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (q : ℕ)
    (h : ∀ (V : Y.Etale) [IsAffine V.left],
      IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{w} ⋙
        (evaluation X.Etaleᵒᵖ AddCommGrpCat.{w}).obj
          (Opposite.op ((smallEtaleBaseChange f).obj V))).rightDerived q).obj F)) :
    IsZero ((((smallEtaleBaseChange f).sheafPushforwardContinuous
      AddCommGrpCat.{w} Y.smallEtaleTopology X.smallEtaleTopology).rightDerived q).obj F) := by
  let := affineEtale_isCoverDense Y
  apply IsZero.of_iso _ (smallEtaleHigherDirectImageSheafificationIso f F q)
  apply isZero_sheafify_of_isCoverDense Y.smallEtaleTopology
    (ObjectProperty.ι (fun V : Y.Etale => IsAffine V.left))
  intro V
  let := V.property
  exact (h V.obj).of_iso (smallEtaleHigherDirectImageSectionsEvaluationIso f F q V.obj)

/-- **Stacks Project, Tag 0EZP.** Higher direct images of a constant abelian
étale sheaf vanish when the source is integral, normal, and has separably
closed function field. -/
@[stacks 0EZP]
public theorem isZero_rightDerived_smallEtalePushforward_constantSheaf
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsNormal X] [IsSepClosed X.functionField]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{w})]
    (M : AddCommGrpCat.{w}) (q : ℕ) (hq : 0 < q) :
    IsZero ((((smallEtaleBaseChange f).sheafPushforwardContinuous
      AddCommGrpCat.{w} Y.smallEtaleTopology X.smallEtaleTopology).rightDerived q).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{w}).obj M)) := by
  classical
  by_cases hu : UnivLE.{u, w}
  · let := hu
    apply isZero_rightDerived_smallEtalePushforward_of_affine_sections f _ q
    intro V hV
    let : IsAffine V.left := hV
    let : IsAffine ((𝟭 Scheme.{u}).obj V.left) := hV
    let P := (smallEtaleBaseChange f).obj V
    have hP : IsSeparated P.hom := by
      let : V.left.IsSeparated := inferInstance
      have : IsSeparated (V.hom : V.left ⟶ Y) := inferInstance
      change IsSeparated (pullback.snd (V.hom : V.left ⟶ Y) f)
      infer_instance
    obtain ⟨I, U, j, hj, e, he⟩ :=
      AlgebraicGeometry.exists_coproduct_open_immersions X P.left P.hom
    let (i : I) : IsOpenImmersion (j i) := hj i
    let W (i : I) : X.Etale := .mk (j i)
    let eP : P ≅ etaleCoproduct W := MorphismProperty.Over.isoMk e he
    refine isZero_rightDerived_etaleSections_of_iso eP _ q ?_
    apply isZero_rightDerived_etaleCoproduct_of_components W _ q hq
    intro i
    let ei : W i ≅ (opensToEtale X).obj (j i).opensRange :=
      MorphismProperty.Over.isoMk (j i).isoOpensRange
        (Scheme.Hom.isoOpensRange_hom_ι (j i))
    refine isZero_rightDerived_etaleSections_of_iso ei _ q ?_
    exact isZero_rightDerived_etaleOpenSections_constantSheaf X (j i).opensRange M q hq
  · exact isZero_etaleSheaf_of_not_univLE _ hu

end Stacks.EtaleCohomology

/-! ### Sections over objects of the small étale site -/

namespace Stacks.EtaleCohomology

attribute [local instance] smallEtalePushforward_additive

/-- Taking sections over an object of the small étale site is an additive functor on abelian
sheaves. -/
local instance etaleSheafSections_additive {X : Scheme.{u}} (V : X.Etale) :
    ((sheafSections X.smallEtaleTopology AddCommGrpCat.{w}).obj (Opposite.op V)).Additive where
  map_add := by intros; rfl

/-- **The sections criterion for the vanishing of a higher direct image on small étale sites.**
If the `q`-th derived sections of `F` over the base change `X ×_Y V` vanish for every object `V`
of `Y_étale` whose underlying scheme is affine, then the `q`-th higher direct image of `F` along
`f` vanishes: it is the sheafification of the presheaf `V ↦ H^q(X ×_Y V, F)` ([Stacks, Tag
03Q8]), and the objects with affine source are dense in `Y_étale`. -/
public theorem isZero_rightDerived_smallEtalePushforward_of_isAffine_sections
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{w})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (q : ℕ)
    (h : ∀ V : Y.Etale, IsAffine V.left →
      IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{w} ⋙
        (evaluation X.Etaleᵒᵖ AddCommGrpCat.{w}).obj
          (Opposite.op ((smallEtaleBaseChange f).obj V))).rightDerived q).obj F)) :
    IsZero ((((smallEtaleBaseChange f).sheafPushforwardContinuous
      AddCommGrpCat.{w} Y.smallEtaleTopology X.smallEtaleTopology).rightDerived q).obj F) :=
  isZero_rightDerived_smallEtalePushforward_of_affine_sections f F q h

/-- **Positive-degree derived sections over an object of `X_étale` presented as a disjoint union
vanish as soon as they vanish over each summand.** Here `W` is an object of the small étale site
whose underlying scheme is identified, over `X`, with the coproduct of the underlying schemes of
a family `U` of objects of that site; the index type is arbitrary in the universe of the
schemes, so no quasi-compactness is needed. -/
public theorem isZero_rightDerived_etaleSections_of_iso_sigma
    {X : Scheme.{u}} [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{w})]
    {I : Type u} (U : I → X.Etale) (W : X.Etale)
    (e : W.left ≅ ∐ fun i => (U i).left)
    (he : e.hom ≫ Sigma.desc (fun i => (U i).hom) = W.hom)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (q : ℕ) (hq : 0 < q)
    (h : ∀ i, IsZero
      ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{w}).obj
        (Opposite.op (U i))).rightDerived q).obj F)) :
    IsZero ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{w}).obj
      (Opposite.op W)).rightDerived q).obj F) := by
  let eW : W ≅ etaleCoproduct U := MorphismProperty.Over.isoMk e he
  exact isZero_rightDerived_etaleSections_of_iso eW F q
    (isZero_rightDerived_etaleCoproduct_of_components U F q hq h)

end Stacks.EtaleCohomology
