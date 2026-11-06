module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit

/-!
# Base change along a cofiltered inverse system of schemes

Let `D : I ⥤ Scheme` be a cofiltered diagram with affine transition morphisms and limit cone `c`,
and fix a stage `i` and a scheme `X` over `D.obj i`. Pulling `X` back along the transition
morphisms `D.map g` for `g : j ⟶ i` produces a diagram `baseChangeDiagram D i X` indexed by
`Over i`, whose limit is the base change of `X` to `c.pt`. This file collects the calculus of that
construction: the diagram, its limit cone, the stability of affineness and of quasi-compactness
along it, and the comparison morphisms between the base changes of two schemes over `D.obj i`.

A property `P` of morphisms of schemes which is stable under base change and local at the source
can be checked on affine charts, and a chart-wise statement holding at finitely many stages can be
moved to one common stage. The last two sections provide those two reductions.

## Main definitions

* `AlgebraicGeometry.baseChangeDiagram`, `AlgebraicGeometry.baseChangeCone` and
  `AlgebraicGeometry.baseChangeConeIsLimit`: the diagram of base changes of a scheme over a stage,
  its canonical cone and the proof that the cone is a limit.
* `AlgebraicGeometry.baseChangeMap`: the morphism `T ×_S X ⟶ T ×_S Y` induced by a morphism
  `X ⟶ Y` over `S`, with the base-change parameter in the first factor.
* `AlgebraicGeometry.baseChangeTransition`: the morphism `T' ×_S X ⟶ T ×_S X` induced by a
  morphism `T' ⟶ T` over `S`.
* `AlgebraicGeometry.baseChangeDiagramMap`: the natural transformation between the base-change
  diagrams of two schemes over a stage.
* `AlgebraicGeometry.baseChangeMapOpenCover`: the open cover of `T ×_S X` obtained from an open
  cover of `X` by base change.

## Main results

* `AlgebraicGeometry.isIso_pullback_lift_of_isPullback`: the comparison morphism into a chosen
  pullback out of the corner of a pullback square is an isomorphism.
* `AlgebraicGeometry.baseChangeMap_isPullback` and
  `AlgebraicGeometry.baseChangeTransition_isPullback`: the two comparison morphisms sit in
  pullback squares, so every property stable under base change transfers along them.
* `AlgebraicGeometry.baseChangeMap_prop_iff` and `AlgebraicGeometry.overPullback_isPullback`
  identify `baseChangeMap` with the morphism `CategoryTheory.Over.pullback` produces.
* `AlgebraicGeometry.overPullback_map_comp` and `AlgebraicGeometry.overPullback_map_comp_iff`:
  base change along a composite agrees with iterated base change.
* `AlgebraicGeometry.exists_finite_affine_charts`: a morphism with quasi-compact source admits
  finitely many affine source charts, each mapping into an affine chart of the target.
* `AlgebraicGeometry.finitePresentation_appTop_of_affine`: on affine schemes a locally finitely
  presented morphism has finitely presented map of global sections.
* `AlgebraicGeometry.prop_overPullback_chart` and
  `AlgebraicGeometry.prop_overPullback_of_charts`: a property local at the source holds for a base
  change exactly when it holds for the base change of every chart.
* `AlgebraicGeometry.common_stage_of_finite`: finitely many properties, each holding at some stage
  and inherited by later stages, hold simultaneously at one stage.

## Implementation notes

The indexing category is an arbitrary cofiltered category, and its object and morphism universes
are independent of the scheme universe. The condition that a stage `j` is later than `i` is an
object of `Over i`, which packages the stage together with its transition morphism. Results that
need the index category to be small relative to the scheme universe assume
`CategoryTheory.EssentiallySmall`, which supplies the `CategoryTheory.LocallySmall` and
`CategoryTheory.InitiallySmall` hypotheses used by the universe-independent form of Mathlib's
theory of cofiltered limits with affine transition morphisms.

## References

* [Stacks Project, Tag 01YT](https://stacks.math.columbia.edu/tag/01YT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory

/-- The over category of an essentially small category at a fixed object is again essentially
small: it is the category of costructured arrows of the identity functor. -/
instance essentiallySmall_over {I : Type v} [Category.{w} I] [EssentiallySmall.{u} I] (i : I) :
    EssentiallySmall.{u} (Over i) := by
  change EssentiallySmall.{u} (CostructuredArrow (𝟭 I) i)
  infer_instance

end CategoryTheory

namespace AlgebraicGeometry

/-- The canonical comparison morphism into a pullback out of the corner of a pullback square
is an isomorphism. -/
lemma isIso_pullback_lift_of_isPullback {C : Type*} [Category C] {P A B Z : C}
    {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ Z} {g : B ⟶ Z}
    (h : IsPullback fst snd f g) [HasPullback f g] :
    IsIso (pullback.lift fst snd h.w) := by
  have he : pullback.lift fst snd h.w = h.isoPullback.hom :=
    pullback.hom_ext
      ((pullback.lift_fst _ _ _).trans (h.isoPullback_hom_fst).symm)
      ((pullback.lift_snd _ _ _).trans (h.isoPullback_hom_snd).symm)
  rw [he]
  infer_instance

/-! ### Comparison morphisms between base changes -/

section Comparison

variable {S T T' : Scheme.{u}}

/-- The morphism `T ×_S X ⟶ T ×_S Y` induced by a morphism `f : X ⟶ Y` of schemes over `S`. The
base-change parameter is the first pullback factor. -/
noncomputable def baseChangeMap (g : T ⟶ S) (X Y : Over S) (f : X ⟶ Y) :
    pullback g X.hom ⟶ pullback g Y.hom :=
  pullback.lift (pullback.fst g X.hom) (pullback.snd g X.hom ≫ f.left) (by
    rw [Category.assoc, f.w]
    exact pullback.condition)

/-- `AlgebraicGeometry.baseChangeMap` commutes with the projections to `T`. -/
@[simp, reassoc (attr := simp)]
lemma baseChangeMap_fst (g : T ⟶ S) (X Y : Over S) (f : X ⟶ Y) :
    baseChangeMap g X Y f ≫ pullback.fst g Y.hom = pullback.fst g X.hom :=
  pullback.lift_fst _ _ _

/-- `AlgebraicGeometry.baseChangeMap` lies over `f` on the second pullback factor. -/
@[simp, reassoc (attr := simp)]
lemma baseChangeMap_snd (g : T ⟶ S) (X Y : Over S) (f : X ⟶ Y) :
    baseChangeMap g X Y f ≫ pullback.snd g Y.hom = pullback.snd g X.hom ≫ f.left :=
  pullback.lift_snd _ _ _

/-- `AlgebraicGeometry.baseChangeMap` is the base change of `f` along the second projection. -/
lemma baseChangeMap_isPullback (g : T ⟶ S) (X Y : Over S) (f : X ⟶ Y) :
    IsPullback (baseChangeMap g X Y f) (pullback.snd g X.hom) (pullback.snd g Y.hom) f.left := by
  refine ⟨⟨baseChangeMap_snd g X Y f⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro s
    exact pullback.lift (s.fst ≫ pullback.fst g Y.hom) s.snd (by
      calc
        (s.fst ≫ pullback.fst g Y.hom) ≫ g = s.fst ≫ pullback.snd g Y.hom ≫ Y.hom := by
          simp [Category.assoc, pullback.condition]
        _ = (s.snd ≫ f.left) ≫ Y.hom := by rw [← Category.assoc, s.condition]
        _ = s.snd ≫ X.hom := by simp [Category.assoc, f.w])
  · intro s
    apply pullback.hom_ext
    · simp only [Category.assoc, baseChangeMap, pullback.lift_fst]
    · simp only [Category.assoc, baseChangeMap, pullback.lift_snd]
      simpa only [← Category.assoc, pullback.lift_snd] using s.condition.symm
  · intro s
    exact pullback.lift_snd _ _ _
  · intro s m hm₁ hm₂
    apply pullback.hom_ext
    · simpa only [Category.assoc, baseChangeMap, pullback.lift_fst] using
        congrArg (· ≫ pullback.fst g Y.hom) hm₁
    · simpa only [pullback.lift_snd] using hm₂

/-- `AlgebraicGeometry.baseChangeMap` is compatible with composition of morphisms over `S`. -/
lemma baseChangeMap_comp (g : T ⟶ S) (X Y Z : Over S) (p : X ⟶ Y) (q : Y ⟶ Z) :
    baseChangeMap g X Z (p ≫ q) = baseChangeMap g X Y p ≫ baseChangeMap g Y Z q := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- **`AlgebraicGeometry.baseChangeMap` is determined by its two projections**, read through
arbitrary presentations of the two base changes as cartesian squares. If `m` is a morphism between
the tops of two such squares commuting with the projections to `T` and lying over `f` on the other
side, then `m` is the base change of `f`. -/
lemma isoPullback_hom_comp_baseChangeMap (g : T ⟶ S) {X Y : Over S} (f : X ⟶ Y)
    {P Q : Scheme.{u}} {pX : P ⟶ T} {qX : P ⟶ X.left} (hP : IsPullback pX qX g X.hom)
    {pY : Q ⟶ T} {qY : Q ⟶ Y.left} (hQ : IsPullback pY qY g Y.hom) (m : P ⟶ Q)
    (h₁ : m ≫ pY = pX) (h₂ : m ≫ qY = qX ≫ f.left) :
    hP.isoPullback.hom ≫ baseChangeMap g X Y f = m ≫ hQ.isoPullback.hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, baseChangeMap_fst, IsPullback.isoPullback_hom_fst, Category.assoc,
      IsPullback.isoPullback_hom_fst, h₁]
  · rw [Category.assoc, baseChangeMap_snd, ← Category.assoc,
      IsPullback.isoPullback_hom_snd, Category.assoc, IsPullback.isoPullback_hom_snd, h₂]

/-- `AlgebraicGeometry.isoPullback_hom_comp_baseChangeMap` in the direction in which a cartesian
square is transported along the two identifications: the base change of `f` becomes `m` itself. -/
lemma baseChangeMap_comp_isoPullback_inv (g : T ⟶ S) {X Y : Over S} (f : X ⟶ Y)
    {P Q : Scheme.{u}} {pX : P ⟶ T} {qX : P ⟶ X.left} (hP : IsPullback pX qX g X.hom)
    {pY : Q ⟶ T} {qY : Q ⟶ Y.left} (hQ : IsPullback pY qY g Y.hom) (m : P ⟶ Q)
    (h₁ : m ≫ pY = pX) (h₂ : m ≫ qY = qX ≫ f.left) :
    baseChangeMap g X Y f ≫ hQ.isoPullback.inv = hP.isoPullback.inv ≫ m := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact isoPullback_hom_comp_baseChangeMap g f hP hQ m h₁ h₂

/-- The first pullback projection is natural in the scheme being base changed. -/
@[reassoc]
lemma overPullback_map_left_fst (g : T ⟶ S) {X Y : Over S} (f : X ⟶ Y) :
    ((Over.pullback g).map f).left ≫ pullback.fst Y.hom g = pullback.fst X.hom g ≫ f.left := by
  simp only [Over.pullback_map_left, pullback.lift_fst]

/-- The second pullback projection is the structure morphism of the base change. -/
@[reassoc]
lemma overPullback_map_left_snd (g : T ⟶ S) {X Y : Over S} (f : X ⟶ Y) :
    ((Over.pullback g).map f).left ≫ pullback.snd Y.hom g = pullback.snd X.hom g := by
  simp only [Over.pullback_map_left, pullback.lift_snd]

/-- The morphism `CategoryTheory.Over.pullback` produces sits in a pullback square over the
original morphism. -/
lemma overPullback_isPullback (g : T ⟶ S) (X Y : Over S) (f : X ⟶ Y) :
    IsPullback (pullback.fst X.hom g) ((Over.pullback g).map f).left f.left
      (pullback.fst Y.hom g) := by
  refine IsPullback.of_bot ?_ (by simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback Y.hom g)
  simpa only [Over.pullback_map_left, pullback.lift_snd, f.w] using
    IsPullback.of_hasPullback X.hom g

/-- Swapping the two pullback factors identifies the morphism `CategoryTheory.Over.pullback`
produces with `AlgebraicGeometry.baseChangeMap`. -/
noncomputable def baseChangeMapArrowIso (g : T ⟶ S) (X Y : Over S) (f : X ⟶ Y) :
    Arrow.mk ((Over.pullback g).map f).left ≅ Arrow.mk (baseChangeMap g X Y f) :=
  Arrow.isoMk (pullbackSymmetry X.hom g) (pullbackSymmetry Y.hom g) (by
    apply pullback.hom_ext
    · simp only [Arrow.mk_hom, Category.assoc, baseChangeMap_fst,
        pullbackSymmetry_hom_comp_fst, Over.pullback_map_left, pullback.lift_snd]
    · simp only [Arrow.mk_hom, Category.assoc, baseChangeMap_snd,
        pullbackSymmetry_hom_comp_snd_assoc, pullbackSymmetry_hom_comp_snd,
        Over.pullback_map_left, pullback.lift_fst])

/-- A property of morphisms of schemes which respects isomorphisms holds for
`AlgebraicGeometry.baseChangeMap` exactly when it holds for the morphism
`CategoryTheory.Over.pullback` produces. -/
lemma baseChangeMap_prop_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (g : T ⟶ S)
    (X Y : Over S) (f : X ⟶ Y) :
    P (baseChangeMap g X Y f) ↔ P ((Over.pullback g).map f).left :=
  (MorphismProperty.arrow_mk_iso_iff P (baseChangeMapArrowIso g X Y f)).symm

/-- The morphism `T' ×_S X ⟶ T ×_S X` induced by a morphism `h : T' ⟶ T` over `S`. -/
noncomputable def baseChangeTransition (g : T ⟶ S) (g' : T' ⟶ S) (h : T' ⟶ T)
    (hg : h ≫ g = g') (X : Over S) : pullback g' X.hom ⟶ pullback g X.hom :=
  pullback.lift (pullback.fst g' X.hom ≫ h) (pullback.snd g' X.hom) (by
    rw [Category.assoc, hg]
    exact pullback.condition)

/-- `AlgebraicGeometry.baseChangeTransition` lies over `h` on the first pullback factor. -/
@[simp, reassoc (attr := simp)]
lemma baseChangeTransition_fst (g : T ⟶ S) (g' : T' ⟶ S) (h : T' ⟶ T) (hg : h ≫ g = g')
    (X : Over S) :
    baseChangeTransition g g' h hg X ≫ pullback.fst g X.hom = pullback.fst g' X.hom ≫ h :=
  pullback.lift_fst _ _ _

/-- `AlgebraicGeometry.baseChangeTransition` commutes with the projections to `X`. -/
@[simp, reassoc (attr := simp)]
lemma baseChangeTransition_snd (g : T ⟶ S) (g' : T' ⟶ S) (h : T' ⟶ T) (hg : h ≫ g = g')
    (X : Over S) :
    baseChangeTransition g g' h hg X ≫ pullback.snd g X.hom = pullback.snd g' X.hom :=
  pullback.lift_snd _ _ _

/-- The square comparing the base changes of a morphism to two different stages is a pullback
square. -/
lemma baseChangeTransition_isPullback (g : T ⟶ S) (g' : T' ⟶ S) (h : T' ⟶ T) (hg : h ≫ g = g')
    (X Y : Over S) (f : X ⟶ Y) :
    IsPullback (baseChangeMap g' X Y f) (baseChangeTransition g g' h hg X)
      (baseChangeTransition g g' h hg Y) (baseChangeMap g X Y f) := by
  have hbig : IsPullback (baseChangeMap g' X Y f)
      (baseChangeTransition g g' h hg X ≫ pullback.snd g X.hom)
      (baseChangeTransition g g' h hg Y ≫ pullback.snd g Y.hom) f.left := by
    simpa only [baseChangeTransition_snd] using baseChangeMap_isPullback g' X Y f
  have hcomm : baseChangeMap g' X Y f ≫ baseChangeTransition g g' h hg Y =
      baseChangeTransition g g' h hg X ≫ baseChangeMap g X Y f := by
    apply pullback.hom_ext <;> simp [Category.assoc]
  exact IsPullback.of_bot hbig hcomm (baseChangeMap_isPullback g X Y f)

end Comparison

/-! ### The diagram of base changes over a stage -/

section Diagram

variable {I : Type v} [Category.{w} I]

/-- The diagram of base changes of a scheme `X` over the stage `D.obj i` along the transition
morphisms of the inverse system: it sends a later stage `j ⟶ i` to `D.obj j ×_{D.obj i} X`. -/
noncomputable abbrev baseChangeDiagram (D : I ⥤ Scheme.{u}) (i : I) (X : Over (D.obj i)) :
    Over i ⥤ Scheme.{u} :=
  Over.post D ⋙ Over.pullback X.hom ⋙ Over.forget X.left

/-- The cone on `AlgebraicGeometry.baseChangeDiagram` whose point is the base change of `X` to the
limit of the inverse system. -/
noncomputable abbrev baseChangeCone (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I)
    (X : Over (D.obj i)) : Cone (baseChangeDiagram D i X) :=
  (Over.pullback X.hom ⋙ Over.forget X.left).mapCone ((Over.conePost D i).obj c)

/-- The base change of a scheme over a stage to the limit of the inverse system is the limit of
its base changes to the later stages. -/
noncomputable def baseChangeConeIsLimit [IsCofiltered I] (D : I ⥤ Scheme.{u}) {c : Cone D}
    (hc : IsLimit c) (i : I) (X : Over (D.obj i)) : IsLimit (baseChangeCone D c i X) :=
  isLimitOfPreserves (Over.pullback X.hom ⋙ Over.forget X.left) (Over.isLimitConePost i hc)

variable (D : I ⥤ Scheme.{u}) (i : I) (X : Over (D.obj i))

/-- The stage of the base-change diagram at `a` is `D.obj a.left ×_{D.obj i} X`. -/
@[simp]
lemma baseChangeDiagram_obj (a : Over i) :
    (baseChangeDiagram D i X).obj a = pullback (D.map a.hom) X.hom :=
  rfl

/-- The transition morphisms of the base-change diagram are the transition morphisms of the
inverse system, base changed to `X`. -/
lemma baseChangeDiagram_map {a b : Over i} (g : a ⟶ b) :
    (baseChangeDiagram D i X).map g =
      baseChangeTransition (D.map b.hom) (D.map a.hom) (D.map g.left)
        (by rw [← D.map_comp, g.w]) X :=
  rfl

/-- The legs of the base-change cone are the transition morphisms from the limit. -/
lemma baseChangeCone_π_app (c : Cone D) (a : Over i) :
    (baseChangeCone D c i X).π.app a =
      baseChangeTransition (D.map a.hom) (c.π.app i) (c.π.app a.left)
        (by simp) X :=
  rfl

/-- The structure morphism of the base-change diagram: on a later stage `a` it is the composite
`D.obj a.left ×_{D.obj i} X ⟶ X ⟶ D.obj i`. -/
noncomputable def baseChangeStructureMap :
    baseChangeDiagram D i X ⟶ (Functor.const (Over i)).obj (D.obj i) where
  app a := ((Over.post D ⋙ Over.pullback X.hom).obj a).hom ≫ X.hom
  naturality a b g := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    rw [← Category.assoc]
    exact congrArg (· ≫ X.hom) (Over.w ((Over.post D ⋙ Over.pullback X.hom).map g))

/-- The component of `AlgebraicGeometry.baseChangeStructureMap` at `a` is the second projection
followed by the structure morphism of `X`. -/
@[simp]
lemma baseChangeStructureMap_app (a : Over i) :
    (baseChangeStructureMap D i X).app a = pullback.snd (D.map a.hom) X.hom ≫ X.hom :=
  rfl

variable [∀ {a b : I} (g : a ⟶ b), IsAffineHom (D.map g)]

/-- The projection from a stage of the base-change diagram to `X` is affine. -/
lemma isAffineHom_baseChangeDiagram_snd (a : Over i) :
    IsAffineHom (pullback.snd (D.map a.hom) X.hom) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (D.map a.hom) X.hom) inferInstance

/-- The transition morphisms of the base-change diagram are affine, being base changes of the
transition morphisms of the inverse system. -/
lemma isAffineHom_baseChangeDiagram_map {a b : Over i} (g : a ⟶ b) :
    IsAffineHom ((baseChangeDiagram D i X).map g) := by
  have : IsAffineHom ((Over.post D).map g).left := by
    show IsAffineHom (D.map g.left)
    infer_instance
  exact MorphismProperty.overPullbackMap (P := @IsAffineHom) X.hom ((Over.post D).map g)
    inferInstance

/-- Every stage of the base-change diagram of an affine scheme is affine. -/
lemma isAffine_baseChangeDiagram_obj [IsAffine X.left] (a : Over i) :
    IsAffine ((baseChangeDiagram D i X).obj a) :=
  IsAffine.of_isPullback (IsPullback.of_hasPullback (D.map a.hom) X.hom).flip

/-- The projection from a stage of the base-change diagram to `X` is quasi-compact. -/
lemma quasiCompact_baseChangeDiagram_snd (a : Over i) :
    QuasiCompact (pullback.snd (D.map a.hom) X.hom) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (D.map a.hom) X.hom) inferInstance

/-- The projection from a stage of the base-change diagram to `X` is quasi-separated. -/
lemma quasiSeparated_baseChangeDiagram_snd (a : Over i) :
    QuasiSeparated (pullback.snd (D.map a.hom) X.hom) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (D.map a.hom) X.hom) inferInstance

/-- Every stage of the base-change diagram of a quasi-compact scheme is quasi-compact. -/
lemma compactSpace_baseChangeDiagram_obj [CompactSpace X.left] (a : Over i) :
    CompactSpace ((baseChangeDiagram D i X).obj a) :=
  @QuasiCompact.compactSpace_of_compactSpace _ _ _ (quasiCompact_baseChangeDiagram_snd D i X a)
    inferInstance

/-- Every stage of the base-change diagram of a quasi-separated scheme is quasi-separated. -/
lemma quasiSeparatedSpace_baseChangeDiagram_obj [QuasiSeparatedSpace X.left] (a : Over i) :
    QuasiSeparatedSpace ((baseChangeDiagram D i X).obj a) :=
  @quasiSeparatedSpace_of_quasiSeparated _ _ _ inferInstance
    (quasiSeparated_baseChangeDiagram_snd D i X a)

end Diagram

/-! ### The induced morphism of base-change diagrams -/

section DiagramMap

variable {I : Type v} [Category.{w} I] (D : I ⥤ Scheme.{u}) (i : I) {X Y : Over (D.obj i)}
  (f : X ⟶ Y)

/-- A morphism of schemes over a stage induces a morphism of the diagrams of base changes. -/
noncomputable def baseChangeDiagramMap : baseChangeDiagram D i X ⟶ baseChangeDiagram D i Y where
  app a := baseChangeMap (D.map a.hom) X Y f
  naturality a b g := by
    rw [baseChangeDiagram_map, baseChangeDiagram_map]
    exact (baseChangeTransition_isPullback (D.map b.hom) (D.map a.hom) (D.map g.left)
      (by rw [← D.map_comp, g.w]) X Y f).w.symm

/-- The component of `AlgebraicGeometry.baseChangeDiagramMap` at `a` is the base change of `f`
along `D.map a.hom`. -/
@[simp]
lemma baseChangeDiagramMap_app (a : Over i) :
    (baseChangeDiagramMap D i f).app a = baseChangeMap (D.map a.hom) X Y f :=
  rfl

/-- Each square of the morphism of base-change diagrams is a pullback square. -/
lemma baseChangeDiagramMap_isPullback {a b : Over i} (g : a ⟶ b) :
    IsPullback ((baseChangeDiagram D i X).map g) ((baseChangeDiagramMap D i f).app a)
      ((baseChangeDiagramMap D i f).app b) ((baseChangeDiagram D i Y).map g) := by
  rw [baseChangeDiagram_map, baseChangeDiagram_map]
  exact (baseChangeTransition_isPullback (D.map b.hom) (D.map a.hom) (D.map g.left)
    (by rw [← D.map_comp, g.w]) X Y f).flip

/-- The morphism of base-change diagrams is compatible with the limit cones: every square over a
leg of the cone is a pullback square. -/
lemma baseChangeCone_π_isPullback (c : Cone D) (a : Over i) :
    IsPullback ((baseChangeCone D c i X).π.app a) (baseChangeMap (c.π.app i) X Y f)
      ((baseChangeDiagramMap D i f).app a) ((baseChangeCone D c i Y).π.app a) := by
  rw [baseChangeCone_π_app, baseChangeCone_π_app]
  exact (baseChangeTransition_isPullback (D.map a.hom) (c.π.app i) (c.π.app a.left)
    (by simp) X Y f).flip

end DiagramMap

/-! ### Base change along a composite -/

section Comp

variable (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] {S T U : Scheme.{u}}
  (g : T ⟶ S) (h : U ⟶ T) {X Y : Over S} (f : X ⟶ Y)

/-- Base change along a composite agrees with iterated base change. -/
noncomputable def overPullbackCompArrowIso :
    Arrow.mk ((Over.pullback (h ≫ g)).map f).left ≅
      Arrow.mk ((Over.pullback h).map ((Over.pullback g).map f)).left :=
  Arrow.isoMk ((Over.forget _).mapIso ((Over.pullbackComp h g).app X))
    ((Over.forget _).mapIso ((Over.pullbackComp h g).app Y))
    (congrArg (fun z ↦ z.left) ((Over.pullbackComp h g).hom.naturality f)).symm

/-- A property of morphisms of schemes stable under base change holds for the base change along a
composite exactly when it holds for the iterated base change. -/
lemma overPullback_map_comp_iff :
    P ((Over.pullback (h ≫ g)).map f).left ↔
      P ((Over.pullback h).map ((Over.pullback g).map f)).left := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact MorphismProperty.arrow_mk_iso_iff P (overPullbackCompArrowIso g h f)

/-- A property of morphisms of schemes stable under base change, once it holds at a stage, holds
at every later stage. -/
lemma overPullback_map_comp (hf : P ((Over.pullback g).map f).left) :
    P ((Over.pullback (h ≫ g)).map f).left :=
  (overPullback_map_comp_iff P g h f).2 (MorphismProperty.overPullbackMap h _ hf)

end Comp

/-! ### Moving finitely many stages to a common stage -/

section CommonStage

variable {I : Type v} [Category.{w} I] [IsCofiltered I]

/-- Finitely many properties of the later stages over a fixed stage, each holding at some stage
and inherited by every later stage, hold simultaneously at one stage. -/
lemma common_stage_of_finite (i : I) {J : Type*} [Finite J] (P : Over i → J → Prop)
    (hP : ∀ {a b : Over i} (_ : a ⟶ b) (j : J), P b j → P a j)
    (h : ∀ j : J, ∃ a : Over i, P a j) :
    ∃ a : Over i, ∀ j : J, P a j := by
  classical
  have : Fintype J := Fintype.ofFinite J
  have aux (s : Finset J) : ∃ a : Over i, ∀ j ∈ s, P a j := by
    induction s using Finset.induction_on with
    | empty => exact ⟨Over.mk (𝟙 i), by simp⟩
    | @insert j s hj ih =>
        obtain ⟨a, ha⟩ := ih
        obtain ⟨b, hb⟩ := h j
        refine ⟨IsCofiltered.min a b, ?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact hP (IsCofiltered.minToRight a b) k hb
        · exact hP (IsCofiltered.minToLeft a b) k (ha k hk)
  obtain ⟨a, ha⟩ := aux Finset.univ
  exact ⟨a, fun j ↦ ha j (Finset.mem_univ j)⟩

/-- The specialisation of `AlgebraicGeometry.common_stage_of_finite` to a property of morphisms
of schemes stable under base change, applied to finitely many morphisms over a fixed stage. -/
lemma common_stage_of_finite_prop (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (D : I ⥤ Scheme.{u}) (i : I) {J : Type*} [Finite J] (X Y : J → Over (D.obj i))
    (f : ∀ j, X j ⟶ Y j)
    (h : ∀ j, ∃ (k : I) (g : k ⟶ i), P ((Over.pullback (D.map g)).map (f j)).left) :
    ∃ (k : I) (g : k ⟶ i), ∀ j, P ((Over.pullback (D.map g)).map (f j)).left := by
  obtain ⟨a, ha⟩ := common_stage_of_finite i
    (fun a j ↦ P ((Over.pullback (D.map a.hom)).map (f j)).left)
    (by
      intro a b g j hg
      have hc := overPullback_map_comp P (D.map b.hom) (D.map g.left) (f j) hg
      rwa [← D.map_comp, g.w] at hc)
    (fun j ↦ by
      obtain ⟨k, g, hg⟩ := h j
      exact ⟨Over.mk g, hg⟩)
  exact ⟨a.left, a.hom, ha⟩

/-- A cofiltered essentially small category admits a directed cofinal reindexing of the opposite
of each of its over categories, in the scheme universe. -/
lemma exists_directed_cofinal_over [EssentiallySmall.{u} I] (i : I) :
    ∃ (α : Type u) (_ : PartialOrder α) (_ : IsDirected α (· ≤ ·)) (_ : Nonempty α)
      (e : α ⥤ (Over i)ᵒᵖ), e.Final := by
  let E := equivSmallModel.{u} (Over i)
  have : IsCofiltered (SmallModel.{u} (Over i)) := IsCofiltered.of_equivalence E
  obtain ⟨α, _, _, _, e, he⟩ := IsFiltered.exists_directed ((SmallModel.{u} (Over i))ᵒᵖ)
  exact ⟨α, inferInstance, inferInstance, inferInstance, e ⋙ E.inverse.op, inferInstance⟩

end CommonStage

/-! ### Reduction to affine charts -/

section Charts

/-- A morphism with quasi-compact source admits finitely many affine source charts, each mapping
into an affine chart of its target. -/
lemma exists_finite_affine_charts {X Y : Scheme.{u}} [CompactSpace X] (f : X ⟶ Y) :
    ∃ C : Scheme.OpenCover.{u, u} X, Finite C.I₀ ∧ (∀ j, IsAffine (C.X j)) ∧
      ∃ (V : C.I₀ → Scheme.{u}) (b : ∀ j, V j ⟶ Y) (p : ∀ j, C.X j ⟶ V j),
        (∀ j, IsAffine (V j)) ∧ (∀ j, IsOpenImmersion (b j)) ∧ ∀ j, p j ≫ b j = C.f j ≫ f := by
  classical
  let V := Y.affineCover
  let C := V.pullback₁ f
  let U := (Scheme.OpenCover.affineRefinement C).openCover
  let Ufin := Scheme.OpenCover.finiteSubcover U
  let k (j : Ufin.I₀) : U.I₀ := U.idx j.1
  let t (j : Ufin.I₀) : V.I₀ := (Scheme.OpenCover.fromAffineRefinement C).s₀ (k j)
  let p (j : Ufin.I₀) : Ufin.X j ⟶ V.X (t j) :=
    (Scheme.OpenCover.fromAffineRefinement C).h₀ (k j) ≫ V.pullbackHom f (t j)
  have (q : U.I₀) : IsAffine (U.X q) := by
    show IsAffine ((Scheme.OpenCover.affineRefinement C).openCover.X q)
    exact Scheme.isAffine_affineOpenCover _ _ q
  refine ⟨Ufin, inferInstance, ?_, fun j ↦ V.X (t j), fun j ↦ V.f (t j), p, ?_, ?_, ?_⟩
  · intro j
    show IsAffine (U.X (k j))
    infer_instance
  · intro j
    infer_instance
  · intro j
    exact V.map_prop (t j)
  · intro j
    show (((Scheme.OpenCover.fromAffineRefinement C).h₀ (k j) ≫
      V.pullbackHom f (t j)) ≫ V.f (t j)) = U.f (k j) ≫ f
    simp only [Category.assoc, Scheme.Cover.pullbackHom_map]
    rw [← Category.assoc, (Scheme.OpenCover.fromAffineRefinement C).w₀]

/-- On affine schemes a locally finitely presented morphism has finitely presented map of global
section rings. -/
lemma finitePresentation_appTop_of_affine {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] : f.appTop.hom.FinitePresentation :=
  (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mp inferInstance

variable (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] [IsZariskiLocalAtSource P]

omit [P.IsStableUnderBaseChange] in
/-- If a property local at the source holds for the base change of a morphism, it holds for the
base change of its restriction to an open chart of the source mapping into an open chart of the
target. -/
lemma prop_overPullback_chart [P.HasOfPostcompProperty @IsOpenImmersion] {S T : Scheme.{u}}
    (g : T ⟶ S) (X Y U V : Over S) (f : X ⟶ Y) (a : U ⟶ X) (b : V ⟶ Y) (p : U ⟶ V)
    (hp : p ≫ b = a ≫ f) [IsOpenImmersion a.left] [IsOpenImmersion b.left]
    (hf : P ((Over.pullback g).map f).left) : P ((Over.pullback g).map p).left := by
  have hmap {A B : Over S} (q : A ⟶ B) [IsOpenImmersion q.left] :
      IsOpenImmersion ((Over.pullback g).map q).left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) g q inferInstance
  have ha := hmap a
  have hcomp : P (((Over.pullback g).map p).left ≫ ((Over.pullback g).map b).left) := by
    rw [← Over.comp_left, ← Functor.map_comp, hp, Functor.map_comp, Over.comp_left]
    exact IsZariskiLocalAtSource.comp hf _
  exact MorphismProperty.HasOfPostcompProperty.of_postcomp ((Over.pullback g).map p).left
    ((Over.pullback g).map b).left (hmap b) hcomp

/-- An open cover of a scheme over `S` induces an open cover of its base change to `T`. -/
noncomputable def baseChangeMapOpenCover {S T : Scheme.{u}} (g : T ⟶ S) (X : Over S)
    {J : Type*} (U : J → Over S) (a : ∀ j, U j ⟶ X) [∀ j, IsOpenImmersion (a j).left]
    (hcover : ∀ x : X.left, ∃ j y, (a j).left y = x) : (pullback g X.hom).OpenCover :=
  Scheme.Cover.mkOfCovers J (fun j ↦ pullback g (U j).hom)
    (fun j ↦ baseChangeMap g (U j) X (a j))
    (by
      intro x
      obtain ⟨j, y, hy⟩ := hcover ((pullback.snd g X.hom) x)
      obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback
        (baseChangeMap_isPullback g (U j) X (a j)) x y hy.symm
      exact ⟨j, z, hz⟩)
    (by
      intro j
      have : IsOpenImmersion (a j).left := ‹∀ j, IsOpenImmersion (a j).left› j
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (baseChangeMap_isPullback g (U j) X (a j)).flip inferInstance)

/-- A property local at the source and stable under composition, which holds for every open
immersion, holds for a base change as soon as it holds for the base change of every member of a
chart-wise factorisation of the morphism. -/
lemma prop_overPullback_of_charts [P.IsStableUnderComposition]
    (hoi : ∀ {A B : Scheme.{u}} (q : A ⟶ B), IsOpenImmersion q → P q) {S T : Scheme.{u}}
    (g : T ⟶ S) (X Y : Over S) (f : X ⟶ Y) {J : Type*} (U V : J → Over S) (a : ∀ j, U j ⟶ X)
    (b : ∀ j, V j ⟶ Y) (p : ∀ j, U j ⟶ V j) (hp : ∀ j, p j ≫ b j = a j ≫ f)
    [∀ j, IsOpenImmersion (a j).left] [∀ j, IsOpenImmersion (b j).left]
    (hcover : ∀ x : X.left, ∃ j y, (a j).left y = x)
    (hchart : ∀ j, P ((Over.pullback g).map (p j)).left) :
    P ((Over.pullback g).map f).left := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hglobal : P (baseChangeMap g X Y f) := by
    apply IsZariskiLocalAtSource.of_openCover (𝒰 := baseChangeMapOpenCover g X U a hcover)
    intro j
    show P (baseChangeMap g (U j) X (a j) ≫ baseChangeMap g X Y f)
    have hbj : IsOpenImmersion (b j).left := ‹∀ j, IsOpenImmersion (b j).left› j
    have hob : IsOpenImmersion (baseChangeMap g (V j) Y (b j)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (baseChangeMap_isPullback g (V j) Y (b j)).flip inferInstance
    have heq : baseChangeMap g (U j) X (a j) ≫ baseChangeMap g X Y f =
        baseChangeMap g (U j) (V j) (p j) ≫ baseChangeMap g (V j) Y (b j) := by
      rw [← baseChangeMap_comp, ← baseChangeMap_comp, hp j]
    rw [heq]
    exact MorphismProperty.comp_mem P _ _
      ((baseChangeMap_prop_iff P g (U j) (V j) (p j)).2 (hchart j)) (hoi _ hob)
  exact (baseChangeMap_prop_iff P g X Y f).1 hglobal

end Charts

end AlgebraicGeometry
