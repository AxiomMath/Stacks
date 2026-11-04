module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeAdjunction
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingPullbackDatum

/-!
# Sections of the direct image from an open subspace over a chart, and Čech glueing

Let `j : W ⟶ X` be the inclusion of an open subspace of an algebraic space, `H` an
`𝒪_W`-module and `F = j_*H`.  Let `M` be an affine étale chart of `X` and `g₁, …, g_r` regular
functions on `M` whose basic opens cover every point of `M` lying over `W`.  This file shows that
the sections `F(M)`, as a module over the regular functions on `M`, satisfy

* `g`-torsion freeness: a section killed by a power of every `gᵢ` is zero; and
* Čech glueing along the `gᵢ`
  (`FormalGlueing.CechGlueingElementary`), when `F` is quasi-coherent.

## Main results

* `AlgebraicGeometry.Space.bijective_modulePushforward_map_openChartInclusion`: restricting
  sections of `j_*H` from `M` to an open `O` of its scheme containing every point over `W` is
  bijective.
* `AlgebraicGeometry.Space.eq_zero_of_forall_pow_smul_eq_zero_modulePushforward_openSubspace`:
  the torsion statement.
* `AlgebraicGeometry.Space.cechGlueingElementary_modulePushforward_openSubspace`: the glueing
  statement.

## Implementation notes

The direct image along an open immersion is restriction of sections along base change of étale
charts (`AlgebraicGeometry.Space.smallBaseChangeModulePushforwardIso`), so the sections of `j_*H`
over `M` are those of `H` over `M ×_X W`.  Every point of `M ×_X W` maps into `O`, so the
projection to `M` factors through the open `O` (Mathlib's
`AlgebraicGeometry.IsOpenImmersion.lift`), and the base change of the inclusion of `O` is an
isomorphism of charts of `W`.  With `O` the union of the basic opens `D(gᵢ)`, the basic-open
charts cover the chart `O`; the two statements are then the sheaf property of `F` on that
covering, using that `gᵢ` is invertible on `D(gᵢ)`.  For glueing the conclusion is read off over
`M` through Stacks 0859 (2) in the form
`AlgebraicGeometry.Space.chartRestrictLinear_openChart_basicOpen_eq_zero_iff`, which is where
quasi-coherence enters.

## References

* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Covering an open of a chart by the charts of a family of opens -/

/-- The charts cut out by a family of Zariski opens of a chart cover the chart cut out by their
union. -/
theorem ofArrows_openChartHomOfLE_iSup_mem_topology {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (M : SmallEtale B S hS F) {ι : Type*} (Ω : ι → (chartScheme M).Opens) :
    Sieve.ofArrows (fun i => openChart B S hS F M (Ω i))
        (fun i => openChartHomOfLE B S hS F M (le_iSup Ω i)) ∈
      SmallEtale.topology B S hS F (openChart B S hS F M (⨆ i, Ω i)) := by
  refine SmallEtale.ofArrows_mem_topology B S hS F _ _ ?_
  rw [Scheme.ofArrows_mem_etalePrecoverage_iff]
  refine ⟨fun x => ?_, fun i => etale_toScheme_toOver_map B S hS F _⟩
  have hx : (⨆ i, Ω i).ι x ∈ ⨆ i, Ω i := (Scheme.Opens.range_ι _).le ⟨x, rfl⟩
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨y, hy⟩ := (Scheme.Opens.range_ι (Ω i)).ge hi
  refine ⟨i, y, ?_⟩
  show (chartScheme M).homOfLE (le_iSup Ω i) y = x
  apply (⨆ i, Ω i).ι.isOpenEmbedding.injective
  rwa [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]

/-! ### Factoring through an open subobject of the site -/

variable {B S hS} in
/-- A morphism of the site landing pointwise in an open lands in the range of its inclusion. -/
theorem range_toScheme_map_subset_range_ι (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) {T : BigFppfOver B S hS} (a : T ⟶ A)
    (ha : ∀ y, (BigFppfOver.toScheme B S hS).map a y ∈ O) :
    Set.range ⇑((BigFppfOver.toScheme B S hS).map a) ⊆ Set.range ⇑O.ι := by
  rw [O.range_ι]
  rintro _ ⟨y, rfl⟩
  exact ha y

variable {B S hS} in
/-- The underlying morphism of `AlgebraicGeometry.Space.openSubLift`. -/
noncomputable def openSubLiftLeft (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) {T : BigFppfOver B S hS} (a : T ⟶ A)
    (ha : ∀ y, (BigFppfOver.toScheme B S hS).map a y ∈ O) : T.left ⟶ (openSub A O).left :=
  B.inclusion.preimage (Y := (openSub A O).left)
    (IsOpenImmersion.lift O.ι ((BigFppfOver.toScheme B S hS).map a)
      (range_toScheme_map_subset_range_ι A O a ha) :)

variable {B S hS} in
/-- `AlgebraicGeometry.Space.openSubLiftLeft` followed by the inclusion of the open is the
original morphism. -/
theorem openSubLiftLeft_comp (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) {T : BigFppfOver B S hS} (a : T ⟶ A)
    (ha : ∀ y, (BigFppfOver.toScheme B S hS).map a y ∈ O) :
    openSubLiftLeft A O a ha ≫ (openSubHom A O).left = a.left := by
  apply B.inclusion.map_injective
  have h1 : B.inclusion.map (openSubLiftLeft A O a ha) =
      IsOpenImmersion.lift O.ι ((BigFppfOver.toScheme B S hS).map a)
        (range_toScheme_map_subset_range_ι A O a ha) :=
    B.inclusion.map_preimage _
  rw [CategoryTheory.Functor.map_comp, h1]
  exact (congrArg (fun k => IsOpenImmersion.lift O.ι ((BigFppfOver.toScheme B S hS).map a)
      (range_toScheme_map_subset_range_ι A O a ha) ≫ k)
    (toScheme_map_openSubHom B S hS A O)).trans (IsOpenImmersion.lift_fac _ _ _)

variable {B S hS} in
/-- A morphism of the big fppf site of `S` into `A` whose underlying morphism of schemes takes
every point into an open `O` factors through the open subobject `openSub A O`. -/
noncomputable def openSubLift (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) {T : BigFppfOver B S hS} (a : T ⟶ A)
    (ha : ∀ y, (BigFppfOver.toScheme B S hS).map a y ∈ O) : T ⟶ openSub A O :=
  Over.homMk (openSubLiftLeft A O a ha) (by
    rw [← Over.w (openSubHom A O), ← Category.assoc, openSubLiftLeft_comp, Over.w a])

variable {B S hS} in
/-- `AlgebraicGeometry.Space.openSubLift` followed by the inclusion of the open is the original
morphism. -/
theorem openSubLift_comp_openSubHom (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) {T : BigFppfOver B S hS} (a : T ⟶ A)
    (ha : ∀ y, (BigFppfOver.toScheme B S hS).map a y ∈ O) :
    openSubLift A O a ha ≫ openSubHom A O = a :=
  Over.OverMorphism.ext (openSubLiftLeft_comp A O a ha)

variable {B S hS} in
/-- The inclusion of an open subobject of the site is a monomorphism. -/
theorem mono_openSubHom_of_opens (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) : Mono (openSubHom A O) := by
  refine ⟨fun {T} g₁ g₂ h => (BigFppfOver.toScheme B S hS).map_injective
    ((cancel_mono O.ι).1 ?_)⟩
  have h' := congrArg (fun k => (BigFppfOver.toScheme B S hS).map k) h
  simp only [Functor.map_comp, toScheme_map_openSubHom] at h'
  exact h'

/-- Two lifts into representable fibre products along `g` and along `i ≫ g`, for a
monomorphism `i` through which the projection of the first factors, are mutually inverse. -/
theorem relativelyRepresentable_lift_comp_lift {Z X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : Z ⟶ X'} (hrep : yoneda.relativelyRepresentable f) {A A' : BigFppfOver B S hS}
    (i : A' ⟶ A) [Mono i] (g : yoneda.obj A ⟶ X') (a : hrep.pullback g ⟶ A')
    (ha : a ≫ i = hrep.snd g)
    (hK : hrep.fst (yoneda.map i ≫ g) ≫ f =
      yoneda.map (hrep.snd (yoneda.map i ≫ g) ≫ i) ≫ g)
    (hL : hrep.fst g ≫ f = yoneda.map a ≫ yoneda.map i ≫ g) :
    hrep.lift _ _ hK ≫ hrep.lift _ _ hL = 𝟙 _ ∧ hrep.lift _ _ hL ≫ hrep.lift _ _ hK = 𝟙 _ := by
  refine ⟨hrep.hom_ext ?_ ?_, hrep.hom_ext ?_ ?_⟩
  · rw [CategoryTheory.Functor.map_comp, Category.assoc, hrep.lift_fst, hrep.lift_fst,
      CategoryTheory.Functor.map_id, Category.id_comp]
  · rw [Category.assoc, hrep.lift_snd, Category.id_comp]
    apply (cancel_mono i).1
    rw [Category.assoc, ha, hrep.lift_snd]
  · rw [CategoryTheory.Functor.map_comp, Category.assoc, hrep.lift_fst, hrep.lift_fst,
      CategoryTheory.Functor.map_id, Category.id_comp]
  · rw [Category.assoc, hrep.lift_snd, ← Category.assoc, hrep.lift_snd, ha, Category.id_comp]

/-! ### Base change of an open chart containing everything over the source -/

variable {B S hS} (X : AlgebraicSpaces B S hS)

section Points

attribute [local instance] pointTopology

/-- If an open `O` of a chart `M` of `X` contains every point of `M` lying over the image of
`j : Y ⟶ X`, then the projection `M ×_X Y ⟶ M` takes every point into `O`. -/
theorem snd_mem_of_forall_chartPointsMap {Y : AlgebraicSpaces B S hS} (j : Y ⟶ X)
    (hrep : yoneda.relativelyRepresentable j.hom) (M : SmallEtale B S hS X.1)
    (O : (chartScheme M).Opens)
    (hO : ∀ x : chartScheme M,
      chartPointsMap M x ∈ Set.range (pointsMap B S hS Y.1 j.hom) → x ∈ O)
    (y : (BigFppfOver.toScheme B S hS).obj (hrep.pullback M.1.hom)) :
    (BigFppfOver.toScheme B S hS).map (hrep.snd M.1.hom) y ∈ O := by
  apply hO
  refine ⟨pointsMap B S hS _ (hrep.fst M.1.hom)
    ((schemePointsHomeomorph B S hS (hrep.pullback M.1.hom)).symm y), ?_⟩
  show pointsMap B S hS _ j.hom (pointsMap B S hS _ (hrep.fst M.1.hom) _) =
    pointsMap B S hS _ M.1.hom ((schemePointsHomeomorph B S hS M.1.left).symm _)
  rw [← schemePointsHomeomorph_symm_naturality B S hS (hrep.snd M.1.hom) y,
    ← pointsMap_comp_apply, ← pointsMap_comp_apply, hrep.w]

end Points

/-- If an open `O` of a chart `M` of `X` contains every point of `M` lying over the image of
`j : Y ⟶ X`, then the base change along `j` of the inclusion of the chart cut out by `O` is an
isomorphism of charts of `Y`. -/
theorem isIso_smallBaseChange_map_openChartInclusion {Y : AlgebraicSpaces B S hS} (j : Y ⟶ X)
    (hrep : yoneda.relativelyRepresentable j.hom) (M : SmallEtale B S hS X.1)
    (O : (chartScheme M).Opens)
    (hO : ∀ x : chartScheme M,
      chartPointsMap M x ∈ Set.range (pointsMap B S hS Y.1 j.hom) → x ∈ O) :
    IsIso ((smallBaseChange B S hS j hrep).map (openChartInclusion B S hS X.1 M O)) := by
  have _ := mono_openSubHom_of_opens ((SmallEtale.toOver B S hS X.1).obj M) O
  let a := openSubLift ((SmallEtale.toOver B S hS X.1).obj M) O (hrep.snd M.1.hom)
    (snd_mem_of_forall_chartPointsMap X j hrep M O hO)
  have ha : a ≫ openSubHom _ O = hrep.snd M.1.hom := openSubLift_comp_openSubHom _ O _ _
  have hL : hrep.fst M.1.hom ≫ j.hom =
      yoneda.map a ≫ yoneda.map (openSubHom _ O) ≫ M.1.hom := by
    rw [← Category.assoc, ← yoneda.map_comp, ha, hrep.w]
  have h := relativelyRepresentable_lift_comp_lift B S hS hrep (openSubHom _ O) M.1.hom a ha
    (representablePullback_lift_cond B S hS j hrep (openChartInclusion B S hS X.1 M O)) hL
  let inv : (smallBaseChange B S hS j hrep).obj M ⟶
      (smallBaseChange B S hS j hrep).obj (openChart B S hS X.1 M O) :=
    ObjectProperty.homMk (CostructuredArrow.homMk
      (hrep.lift (hrep.fst M.1.hom) a hL) (hrep.lift_fst _ _ _))
  exact ⟨⟨inv, ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ h.1),
    ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ h.2)⟩⟩

/-- **Restriction of sections of a direct image from an open subspace.**  Let `j : Y ⟶ X` be an
open immersion of algebraic spaces and `H` an `𝒪_Y`-module.  If an open `O` of a chart `M` of
`X` contains every point of `M` lying over `Y`, then restricting sections of `j_*H` from `M` to
the chart cut out by `O` is bijective. -/
theorem bijective_modulePushforward_map_openChartInclusion {Y : AlgebraicSpaces B S hS}
    (j : Y ⟶ X) (hj : IsOpenImmersion B S hS j.hom) (H : Modules.{u, u} B S hS Y.1 Y.2)
    (M : SmallEtale B S hS X.1) (O : (chartScheme M).Opens)
    (hO : ∀ x : chartScheme M,
      chartPointsMap M x ∈ Set.range (pointsMap B S hS Y.1 j.hom) → x ∈ O) :
    Function.Bijective
      (((modulePushforward B S hS j).obj H).val.map (openChartInclusion B S hS X.1 M O).op) := by
  have hq := isIso_smallBaseChange_map_openChartInclusion X j hj.rep M O hO
  have hG : IsIso (((smallBaseChangeModulePushforward.{u, u} B S hS j hj.rep).obj
      H).val.presheaf.map (openChartInclusion B S hS X.1 M O).op) := by
    show IsIso (H.val.presheaf.map
      ((smallBaseChange B S hS j hj.rep).map (openChartInclusion B S hS X.1 M O)).op)
    exact (H.val.presheaf.mapIso (asIso ((smallBaseChange B S hS j hj.rep).map
      (openChartInclusion B S hS X.1 M O))).op).isIso_hom
  let α := (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).mapIso
    ((smallBaseChangeModulePushforwardIso B S hS j (isEtale_of_isOpenImmersion B S hS hj)
      hj.rep).app H)
  have _ : IsIso (((modulePushforward B S hS j).obj H).val.presheaf.map
      (openChartInclusion B S hS X.1 M O).op) := (NatIso.isIso_map_iff α _).1 hG
  exact ConcreteCategory.bijective_of_isIso
    (((modulePushforward B S hS j).obj H).val.presheaf.map (openChartInclusion B S hS X.1 M O).op)

/-! ### The sheaf property on a covering family of charts -/

section Sheaf

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- Restriction of sections of an `𝒪_F`-module along a morphism of charts, typed as the sections
over the source chart (rather than as a restriction of scalars of them). -/
noncomputable abbrev chartSectionRestrict (G : Modules.{u, u} B S hS F hF)
    {Z Z' : SmallEtale B S hS F} (c : Z' ⟶ Z) (x : G.val.obj (op Z)) : G.val.obj (op Z') :=
  G.val.map c.op x

/-- Restriction of sections is semilinear along restriction of regular functions. -/
theorem chartSectionRestrict_smul (G : Modules.{u, u} B S hS F hF) {Z Z' : SmallEtale B S hS F}
    (c : Z' ⟶ Z) (a : chartRing B S hS F hF Z) (x : G.val.obj (op Z)) :
    chartSectionRestrict G c (a • x) = chartRestrict (hF := hF) c a • chartSectionRestrict G c x :=
  PresheafOfModules.map_smul G.val c.op a x

/-- Restriction of sections is additive. -/
theorem chartSectionRestrict_sub (G : Modules.{u, u} B S hS F hF) {Z Z' : SmallEtale B S hS F}
    (c : Z' ⟶ Z) (x y : G.val.obj (op Z)) :
    chartSectionRestrict G c (x - y) = chartSectionRestrict G c x - chartSectionRestrict G c y :=
  map_sub (ConcreteCategory.hom (G.val.map c.op)) x y

/-- Restriction of sections maps zero to zero. -/
theorem chartSectionRestrict_zero (G : Modules.{u, u} B S hS F hF) {Z Z' : SmallEtale B S hS F}
    (c : Z' ⟶ Z) : chartSectionRestrict G c 0 = 0 :=
  map_zero (ConcreteCategory.hom (G.val.map c.op))

/-- A section killed by `a` restricts to zero along a morphism of charts making `a` a unit. -/
private theorem chartSectionRestrict_eq_zero_of_smul_eq_zero (G : Modules.{u, u} B S hS F hF)
    {Z Z' : SmallEtale B S hS F} (c : Z' ⟶ Z) (a : chartRing B S hS F hF Z)
    (x : G.val.obj (op Z)) (hx : a • x = 0) (hu : IsUnit (chartRestrict (hF := hF) c a)) :
    chartSectionRestrict G c x = 0 :=
  hu.smul_eq_zero.1 ((chartSectionRestrict_smul G c a x).symm.trans
    ((congrArg (chartSectionRestrict G c) hx).trans (chartSectionRestrict_zero G c)))

/-- Restriction of sections along a composite is the composite of the restrictions. -/
theorem chartSectionRestrict_comp (G : Modules.{u, u} B S hS F hF) {Z Z' Z'' : SmallEtale B S hS F}
    (c : Z' ⟶ Z) (d : Z'' ⟶ Z') (x : G.val.obj (op Z)) :
    chartSectionRestrict G (d ≫ c) x = chartSectionRestrict G d (chartSectionRestrict G c x) :=
  PresheafOfModules.map_comp_apply G.val c.op d.op x

/-- The underlying sheaf of sets of an `𝒪_F`-module satisfies the sheaf condition for a covering
family of charts. -/
theorem isSheafFor_ofArrows_modules (G : Modules.{u, u} B S hS F hF) {V : SmallEtale B S hS F}
    {ι : Type*} {D : ι → SmallEtale B S hS F} (h : ∀ i, D i ⟶ V)
    (hcov : Sieve.ofArrows D h ∈ SmallEtale.topology B S hS F V) :
    (Presieve.ofArrows D h).IsSheafFor (G.val.presheaf ⋙ forget AddCommGrpCat) := by
  have hs : Presieve.IsSheaf (SmallEtale.topology B S hS F)
      (G.val.presheaf ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (GrothendieckTopology.HasSheafCompose.isSheaf (F := forget AddCommGrpCat)
        (P := G.val.presheaf) G.isSheaf)
  exact (Presieve.isSheafFor_iff_generate _).mpr (hs _ hcov)

/-- Compatible sections of an `𝒪_F`-module over a covering family of charts glue. -/
theorem exists_sectionRestrict_eq_of_compatible (G : Modules.{u, u} B S hS F hF)
    {V : SmallEtale B S hS F} {ι : Type*} {D : ι → SmallEtale B S hS F} (h : ∀ i, D i ⟶ V)
    (hcov : Sieve.ofArrows D h ∈ SmallEtale.topology B S hS F V)
    (x : ∀ i, G.val.obj (op (D i)))
    (hx : ∀ i j (Z : SmallEtale B S hS F) (a : Z ⟶ D i) (b : Z ⟶ D j), a ≫ h i = b ≫ h j →
      chartSectionRestrict G a (x i) = chartSectionRestrict G b (x j)) :
    ∃ t : G.val.obj (op V), ∀ i, chartSectionRestrict G (h i) t = x i :=
  ((Presieve.isSheafFor_arrows_iff _ _).1 (isSheafFor_ofArrows_modules G h hcov) x hx).exists

/-- Sections of an `𝒪_F`-module agreeing on a covering family of charts are equal. -/
theorem eq_of_forall_sectionRestrict_eq (G : Modules.{u, u} B S hS F hF)
    {V : SmallEtale B S hS F} {ι : Type*} {D : ι → SmallEtale B S hS F} (h : ∀ i, D i ⟶ V)
    (hcov : Sieve.ofArrows D h ∈ SmallEtale.topology B S hS F V)
    (s t : G.val.obj (op V))
    (hst : ∀ i, chartSectionRestrict G (h i) s = chartSectionRestrict G (h i) t) :
    s = t := by
  obtain ⟨u, -, hu⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
    (isSheafFor_ofArrows_modules G h hcov) (fun i => chartSectionRestrict G (h i) t)
    (fun i j Z a b hab =>
      (chartSectionRestrict_comp G (h i) a t).symm.trans
        ((congrArg (fun c => chartSectionRestrict G c t) hab).trans
          (chartSectionRestrict_comp G (h j) b t)))
  exact (hu s hst).trans (hu t fun _ => rfl).symm

end Sheaf

/-! ### Torsion and glueing from bijectivity of restriction to an open chart -/

section Glueing

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  (G : Modules.{u, u} B S hS F hF) {M : SmallEtale B S hS F} {r : ℕ}
  (g : Fin r → chartRing B S hS F hF M)

/-- The local pieces `nᵢ / gᵢᵏ` of a family satisfying the Čech condition agree on every chart on
which `gᵢ` and `gⱼ` become invertible. -/
theorem smul_sectionRestrict_eq_of_cech (k : ℕ) (n : Fin r → G.val.obj (op M))
    (hn : ∀ i j, ∃ l : ℕ, (g i * g j) ^ l • (g j ^ k • n i - g i ^ k • n j) = 0)
    {Z : SmallEtale B S hS F} (c : Z ⟶ M) (i i' : Fin r) (wi wj : chartRing B S hS F hF Z)
    (hwi : chartRestrict (hF := hF) c (g i) * wi = 1)
    (hwj : chartRestrict (hF := hF) c (g i') * wj = 1) :
    wi ^ k • chartSectionRestrict G c (n i) = wj ^ k • chartSectionRestrict G c (n i') := by
  obtain ⟨l, hl⟩ := hn i i'
  have h3 := sub_eq_zero.1 (by
    simpa only [chartSectionRestrict_sub, chartSectionRestrict_smul, map_pow] using
      chartSectionRestrict_eq_zero_of_smul_eq_zero G c _ _ hl (by
        rw [map_pow, map_mul]
        exact ((IsUnit.of_mul_eq_one wi hwi).mul (IsUnit.of_mul_eq_one wj hwj)).pow l))
  calc wi ^ k • chartSectionRestrict G c (n i)
      = (wi ^ k * (chartRestrict (hF := hF) c (g i') * wj) ^ k) •
          chartSectionRestrict G c (n i) := by
        rw [hwj, one_pow, mul_one]
    _ = (wi ^ k * wj ^ k) •
        (chartRestrict (hF := hF) c (g i') ^ k • chartSectionRestrict G c (n i)) := by
        rw [smul_smul]
        congr 1
        ring
    _ = (wi ^ k * wj ^ k) •
        (chartRestrict (hF := hF) c (g i) ^ k • chartSectionRestrict G c (n i')) := by
        rw [h3]
    _ = ((chartRestrict (hF := hF) c (g i) * wi) ^ k * wj ^ k) •
          chartSectionRestrict G c (n i') := by
        rw [smul_smul]
        congr 1
        ring
    _ = wj ^ k • chartSectionRestrict G c (n i') := by
        rw [hwi, one_pow, one_mul]

/-- If restriction of sections from an affine chart `M` to the chart cut out by the union of the
basic opens `D(gᵢ)` is injective, a section killed by a power of every `gᵢ` is zero. -/
theorem eq_zero_of_injective_sectionRestrict_iSup_basicOpen (hM : IsAffine (chartScheme M))
    (hinj : Function.Injective (chartSectionRestrict G
      (openChartInclusion B S hS F M (⨆ i, (chartScheme M).basicOpen (g i)))))
    (s : G.val.obj (op M)) (hs : ∀ i, ∃ k : ℕ, g i ^ k • s = 0) : s = 0 := by
  let Ω : Fin r → (chartScheme M).Opens := fun i => (chartScheme M).basicOpen (g i)
  let ιO := openChartInclusion B S hS F M (⨆ i, Ω i)
  let ιD : ∀ i, openChart B S hS F M (Ω i) ⟶ M := fun i => openChartInclusion B S hS F M (Ω i)
  let hD : ∀ i, openChart B S hS F M (Ω i) ⟶ openChart B S hS F M (⨆ i, Ω i) :=
    fun i => openChartHomOfLE B S hS F M (le_iSup Ω i)
  have hDι : ∀ i, hD i ≫ ιO = ιD i :=
    fun i => openChartHomOfLE_comp_openChartInclusion B S hS F M _
  have hD0 : ∀ i, chartSectionRestrict G (ιD i) s = 0 := by
    intro i
    obtain ⟨k, hk⟩ := hs i
    refine chartSectionRestrict_eq_zero_of_smul_eq_zero G (ιD i) (g i ^ k) s hk ?_
    rw [map_pow]
    exact (isUnit_chartRestrict_openChartInclusion_basicOpen B S hS hF M hM (g i)).pow k
  apply hinj
  refine eq_of_forall_sectionRestrict_eq G hD (ofArrows_openChartHomOfLE_iSup_mem_topology B S hS M
    Ω) _ _ (fun i => ?_)
  rw [← chartSectionRestrict_comp, ← chartSectionRestrict_comp, hDι i, hD0 i,
    chartSectionRestrict_zero]

/-- The glueing step: compatible local pieces over the basic-open charts glue to a section over
the chart cut out by their union. -/
theorem exists_sectionRestrict_iSup_basicOpen_eq (hM : IsAffine (chartScheme M)) (k : ℕ)
    (n : Fin r → G.val.obj (op M))
    (hn : ∀ i j, ∃ l : ℕ, (g i * g j) ^ l • (g j ^ k • n i - g i ^ k • n j) = 0) :
    ∃ τ : G.val.obj (op (openChart B S hS F M (⨆ i, (chartScheme M).basicOpen (g i)))),
      ∀ i, chartRestrict (hF := hF)
          (openChartInclusion B S hS F M ((chartScheme M).basicOpen (g i))) (g i) ^ k •
        chartSectionRestrict G (openChartHomOfLE B S hS F M
          (le_iSup (fun i => (chartScheme M).basicOpen (g i)) i)) τ =
        chartSectionRestrict G (openChartInclusion B S hS F M ((chartScheme M).basicOpen (g i)))
          (n i) := by
  let Ω : Fin r → (chartScheme M).Opens := fun i => (chartScheme M).basicOpen (g i)
  let ιO := openChartInclusion B S hS F M (⨆ i, Ω i)
  let D : Fin r → SmallEtale B S hS F := fun i => openChart B S hS F M (Ω i)
  let ιD : ∀ i, D i ⟶ M := fun i => openChartInclusion B S hS F M (Ω i)
  let hD : ∀ i, D i ⟶ openChart B S hS F M (⨆ i, Ω i) :=
    fun i => openChartHomOfLE B S hS F M (le_iSup Ω i)
  have hDι : ∀ i, hD i ≫ ιO = ιD i :=
    fun i => openChartHomOfLE_comp_openChartInclusion B S hS F M _
  have hu : ∀ i, IsUnit (chartRestrict (hF := hF) (ιD i) (g i)) :=
    fun i => isUnit_chartRestrict_openChartInclusion_basicOpen B S hS hF M hM (g i)
  choose v hv using fun i => (hu i).exists_right_inv
  let t : ∀ i, G.val.obj (op (D i)) := fun i => v i ^ k • chartSectionRestrict G (ιD i) (n i)
  have ht : ∀ (Z : SmallEtale B S hS F) (i : Fin r) (a : Z ⟶ D i),
      chartSectionRestrict G a (t i) =
        chartRestrict (hF := hF) a (v i) ^ k • chartSectionRestrict G (a ≫ ιD i) (n i) := by
    intro Z i a
    show chartSectionRestrict G a (v i ^ k • chartSectionRestrict G (ιD i) (n i)) = _
    rw [chartSectionRestrict_smul, map_pow, chartSectionRestrict_comp]
  obtain ⟨τ, hτ⟩ := exists_sectionRestrict_eq_of_compatible G hD
    (ofArrows_openChartHomOfLE_iSup_mem_topology B S hS M Ω) t (by
      intro i i' Z a b hab
      have hc : a ≫ ιD i = b ≫ ιD i' := by
        rw [← hDι i, ← hDι i', ← Category.assoc, hab, Category.assoc]
      rw [ht Z i a, ht Z i' b, ← hc]
      refine smul_sectionRestrict_eq_of_cech G g k n hn (a ≫ ιD i) i i' _ _ ?_ ?_
      · rw [chartRestrict_comp, RingHom.comp_apply, ← map_mul, hv i, map_one]
      · rw [hc, chartRestrict_comp, RingHom.comp_apply, ← map_mul, hv i', map_one])
  refine ⟨τ, fun i => ?_⟩
  show chartRestrict (hF := hF) (ιD i) (g i) ^ k • chartSectionRestrict G (hD i) τ =
    chartSectionRestrict G (ιD i) (n i)
  rw [hτ i]
  exact (smul_smul (chartRestrict (hF := hF) (ιD i) (g i) ^ k) (v i ^ k)
    (chartSectionRestrict G (ιD i) (n i))).trans (by rw [← mul_pow, hv i, one_pow, one_smul])

/-- If restriction of sections from an affine chart `M` to the chart cut out by the union of the
basic opens `D(gᵢ)` is bijective, the sections over `M` of a module cartesian on affine charts
satisfy Čech glueing along the `gᵢ`. -/
theorem cechGlueingElementary_of_bijective_sectionRestrict_iSup_basicOpen
    (hG : IsCartesianOnAffineCharts G) (hM : IsAffine (chartScheme M))
    (hbij : Function.Bijective (chartSectionRestrict G
      (openChartInclusion B S hS F M (⨆ i, (chartScheme M).basicOpen (g i))))) :
    FormalGlueing.CechGlueingElementary g (G.val.obj (op M)) := by
  intro k n hn
  obtain ⟨τ, hτ⟩ := exists_sectionRestrict_iSup_basicOpen_eq G g hM k n hn
  obtain ⟨m, hm⟩ := hbij.2 τ
  refine ⟨m, fun i => ?_⟩
  let Ω : Fin r → (chartScheme M).Opens := fun i => (chartScheme M).basicOpen (g i)
  let ιD := openChartInclusion B S hS F M (Ω i)
  have hm' : chartSectionRestrict G ιD m = chartSectionRestrict G
      (openChartHomOfLE B S hS F M (le_iSup Ω i)) τ :=
    (congrArg (fun c => chartSectionRestrict G c m)
      (openChartHomOfLE_comp_openChartInclusion B S hS F M (le_iSup Ω i))).symm.trans
      ((chartSectionRestrict_comp G _ _ m).trans (congrArg (chartSectionRestrict G _) hm))
  have hzero : chartSectionRestrict G ιD (g i ^ k • m - n i) = 0 := by
    rw [chartSectionRestrict_sub, chartSectionRestrict_smul, hm', map_pow]
    exact sub_eq_zero.2 (hτ i)
  exact (chartRestrictLinear_openChart_basicOpen_eq_zero_iff B S hS hF G hG M hM (g i) _).1 hzero

end Glueing

/-! ### The torsion and glueing statements -/

/-- Restriction of sections of `j_*H` from `M` to the chart cut out by the union of the basic opens
`D(gᵢ)` is bijective when these cover every point of `M` lying over the open subspace `W`. -/
private theorem bijective_chartSectionRestrict_modulePushforward_openSubspace
    (W : Subfunctor X.1) (hW : IsOpenSubspace B S hS W)
    (H : Modules.{u, u} B S hS W.toFunctor hW.1)
    (M : SmallEtale B S hS X.1) {r : ℕ} (g : Fin r → chartRing B S hS X.1 X.2 M)
    (hcov : ∀ x : chartScheme M, chartPointsMap M x ∈
      Set.range (pointsMap B S hS W.toFunctor W.ι) → ∃ i, x ∈ (chartScheme M).basicOpen (g i)) :
    Function.Bijective (chartSectionRestrict ((modulePushforward B S hS
      (ObjectProperty.homMk W.ι : (⟨W.toFunctor, hW.1⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj H)
      (openChartInclusion B S hS X.1 M (⨆ i, (chartScheme M).basicOpen (g i)))) := by
  let j : (⟨W.toFunctor, hW.1⟩ : AlgebraicSpaces B S hS) ⟶ X := ObjectProperty.homMk W.ι
  have hb := bijective_modulePushforward_map_openChartInclusion X j hW.2 H M
    (⨆ i, (chartScheme M).basicOpen (g i)) fun x hx =>
      TopologicalSpace.Opens.mem_iSup.2 (hcov x hx)
  exact hb

/-- **Sections of the direct image from an open subspace have no `g`-torsion.**  Let `W` be an
open subspace of `X`, `H` an `𝒪_W`-module and `M` an affine étale chart of `X` with regular
functions `g₁, …, g_r` whose basic opens contain every point of `M` lying over `W`.  A section of
`j_*H` over `M` killed by a power of every `gᵢ` is zero. -/
theorem eq_zero_of_forall_pow_smul_eq_zero_modulePushforward_openSubspace
    (W : Subfunctor X.1) (hW : IsOpenSubspace B S hS W)
    (H : Modules.{u, u} B S hS W.toFunctor hW.1)
    (M : SmallEtale B S hS X.1) (hM : IsAffine (chartScheme M))
    {r : ℕ} (g : Fin r → chartRing B S hS X.1 X.2 M)
    (hcov : ∀ x : chartScheme M, chartPointsMap M x ∈
      Set.range (pointsMap B S hS W.toFunctor W.ι) → ∃ i, x ∈ (chartScheme M).basicOpen (g i))
    (s : ((modulePushforward B S hS (ObjectProperty.homMk W.ι :
      (⟨W.toFunctor, hW.1⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj H).val.obj (op M))
    (hs : ∀ i, ∃ k : ℕ, g i ^ k • s = 0) : s = 0 := by
  exact eq_zero_of_injective_sectionRestrict_iSup_basicOpen _ g hM
    (bijective_chartSectionRestrict_modulePushforward_openSubspace X W hW H M g hcov).1 s hs

/-- **Sections of the direct image from an open subspace satisfy Čech glueing.**  Let `W` be an
open subspace of `X`, `H` an `𝒪_W`-module with quasi-coherent direct image `F = j_*H`, and `M`
an affine étale chart of `X` with regular functions `g₁, …, g_r` whose basic opens contain every
point of `M` lying over `W`.  Then a family of sections `nᵢ` of `F` over `M`, read as `nᵢ / gᵢᵏ`,
whose members agree after inverting `gᵢgⱼ`, comes from a single section of `F` over `M`. -/
theorem cechGlueingElementary_modulePushforward_openSubspace
    (W : Subfunctor X.1) (hW : IsOpenSubspace B S hS W)
    (H : Modules.{u, u} B S hS W.toFunctor hW.1)
    (hF : ((modulePushforward B S hS (ObjectProperty.homMk W.ι :
      (⟨W.toFunctor, hW.1⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj H).IsQuasicoherentOnSite)
    (M : SmallEtale B S hS X.1) (hM : IsAffine (chartScheme M))
    {r : ℕ} (g : Fin r → chartRing B S hS X.1 X.2 M)
    (hcov : ∀ x : chartScheme M, chartPointsMap M x ∈
      Set.range (pointsMap B S hS W.toFunctor W.ι) → ∃ i, x ∈ (chartScheme M).basicOpen (g i)) :
    FormalGlueing.CechGlueingElementary g
      (((modulePushforward B S hS (ObjectProperty.homMk W.ι :
        (⟨W.toFunctor, hW.1⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj H).val.obj (op M)) := by
  exact cechGlueingElementary_of_bijective_sectionRestrict_iSup_basicOpen _ g
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 _ hF) hM
    (bijective_chartSectionRestrict_modulePushforward_openSubspace X W hW H M g hcov)

end AlgebraicGeometry.Space

end
