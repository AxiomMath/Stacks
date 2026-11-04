module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.IntegralFamilyFiniteRange.Basic
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.Induction

/-!
# Approximation of a morphism of schemes by morphisms of finite type over the integers

A morphism between quasi-compact and quasi-separated schemes is the limit of an inverse system of
morphisms between schemes of finite type over the integers, with affine transition morphisms on
both sources and targets.  This is tag 0GS1.

## Main definitions

* `AlgebraicGeometry.LimitFPObjectDescent.FiniteTypeSchemeApproximation`: the absolute
  approximation of a single scheme, tag 01ZA, as a bundle of data.
* `AlgebraicGeometry.LimitFPObjectDescent.CompatibleStageMap`: a morphism between one stage of
  the approximation of the source and one stage of the approximation of the target, compatible
  with the given morphism; these are the index set of the approximating system of arrows.

## Main results

* `AlgebraicGeometry.LimitFPObjectDescent.finiteTypeSchemeApproximation`: tag 01ZA, absolute
  Noetherian approximation, obtained from tag 07RN at the empty open subscheme.
* `AlgebraicGeometry.LimitFPObjectDescent.exists_isLimit_finiteType_arrow`: tag 0GS1.

## Implementation notes

The directed index lies in the scheme universe, so finite-stage descent applies to this
approximation.

The inverse system of morphisms is represented as a functor to the arrow category of schemes.
Its limiting cone is identified with the given morphism by an isomorphism in that arrow category,
which includes the compatible identifications of both its source and its target.  As in Mathlib,
finite type is expressed by local finite type together with quasi-compactness.

Tag 01ZA is the special case of tag 07RN at `V = ∅`, and is obtained here by applying
`AlgebraicGeometry.finiteTypeApproximationOfIsLimit` to the constant system on the empty open
subscheme, indexed by `PUnit`; a cone over a constant diagram on an empty scheme is limiting
because the empty scheme is initial.

Tag 0GS1 is then the construction of the Stacks proof: index the approximating system of arrows
by the triples consisting of a stage of the approximation of the source, a stage of the
approximation of the target, and a morphism between them compatible with the given morphism.
Such a triple exists over any stage of the target by tag 01ZC -- the factorization of a morphism
out of a limit through a stage, which Mathlib supplies as
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` -- and any two
triples have a common refinement by the eventual-equality half of the same tag,
`AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`.  The two projections
to the source and target index categories are initial, so the limits are unchanged, and the cone
of arrows is limiting because the source and target cones jointly reflect limits in a comma
category.

## References

* [Stacks Project, Tag 0GS1](https://stacks.math.columbia.edu/tag/0GS1)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.LimitFPObjectDescent

/-- For a quasi-compact and quasi-separated scheme `X`, the finite type approximation of `X`
relative to the constant system on the empty open subscheme of `X`, indexed by `PUnit`. -/
noncomputable def finiteTypeApproximationOfScheme {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] :
    Scheme.FiniteTypeApproximation
      ((Functor.const PUnit.{u + 1}ᵒᵈ).obj ((⊥ : X.Opens) : Scheme.{u}))
      X (⊥ : X.Opens) (𝟙 _) := by
  let D : PUnit.{u + 1}ᵒᵈ ⥤ Scheme.{u} :=
    (Functor.const PUnit.{u + 1}ᵒᵈ).obj ((⊥ : X.Opens) : Scheme.{u})
  let c : Cone D := Cone.mk ((⊥ : X.Opens) : Scheme.{u}) (𝟙 _)
  letI : IsEmpty ((⊥ : X.Opens) : Scheme.{u}) := ⟨fun x => x.2⟩
  have : IsEmpty (D.obj PUnit.unit) := by
    change IsEmpty ((⊥ : X.Opens) : Scheme.{u})
    infer_instance
  letI : ∀ i : PUnit.{u + 1}ᵒᵈ,
      LocallyOfFiniteType (terminal.from (D.obj i)) := by
    intro i
    cases i
    change LocallyOfFiniteType (terminal.from ((⊥ : X.Opens) : Scheme.{u}))
    infer_instance
  letI : ∀ i : PUnit.{u + 1}ᵒᵈ,
      QuasiCompact (terminal.from (D.obj i)) := by
    intro i
    cases i
    exact ⟨fun _ _ _ => Set.subsingleton_of_subsingleton.isCompact⟩
  have hc : IsLimit c := {
    lift := fun s => s.π.app PUnit.unit
    fac := by
      intro s j
      cases j
      exact Category.comp_id _
    uniq := by
      intro s m hm
      have : IsEmpty s.pt := ⟨fun x => isEmptyElim ((s.π.app PUnit.unit).base x)⟩
      exact (isInitialOfIsEmpty : IsInitial s.pt).hom_ext m (s.π.app PUnit.unit) }
  exact finiteTypeApproximationOfIsLimit D X (⊥ : X.Opens) (𝟙 _) hc

/-- A scheme of finite type over the integers is quasi-compact and quasi-separated.
Alias of `Stacks.IntegralFamilyFiniteRange.compactSpace_and_quasiSeparatedSpace_of_finiteType`. -/
alias finiteTypeStage_compact_qs :=
  Stacks.IntegralFamilyFiniteRange.compactSpace_and_quasiSeparatedSpace_of_finiteType

/-- A scheme locally of finite type over the integers is locally of finite presentation over
the integers. -/
lemma finiteTypeStage_locallyFinitePresentation (T : Scheme.{u})
    [LocallyOfFiniteType (terminal.from T)] :
    LocallyOfFinitePresentation (terminal.from T) := by
  let e : (⊤_ Scheme.{u}) ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal |>.symm
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : IsLocallyNoetherian (⊤_ Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian e.hom
  infer_instance

/-- Let `c` be a limit cone over a cofiltered diagram of quasi-compact and quasi-separated
schemes with affine transition morphisms. Every morphism from `c.pt` to a scheme locally of finite
presentation over the integers factors through the projection to some stage. -/
lemma exists_factor_from_limit {I : Type u} [Category.{u} I] [IsCofiltered I]
    {D : I ⥤ Scheme.{u}}
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {T : Scheme.{u}} (c : Cone D) (hc : IsLimit c) (g : c.pt ⟶ T)
    [LocallyOfFinitePresentation (terminal.from T)] :
    ∃ (i : I) (h : D.obj i ⟶ T), c.π.app i ≫ h = g := by
  let t : D ⟶ (Functor.const I).obj (⊤_ Scheme.{u}) := {
    app i := terminal.from (D.obj i)
    naturality _ _ _ := terminalIsTerminal.hom_ext _ _ }
  have ha : c.π ≫ t = (Functor.const I).map (g ≫ terminal.from T) := by
    ext
    exact terminalIsTerminal.hom_ext _ _
  obtain ⟨i, h, hi, -⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (D := D) (t := t) (f := terminal.from T) (c := c) (hc := hc) g ha
  exact ⟨i, h, hi⟩

/-- Let `c` be a limit cone over a cofiltered diagram of quasi-compact schemes with affine
transition morphisms, and let `T` be locally of finite type over the integers. Two morphisms from
a stage to `T` that agree after composing with the projection from `c.pt` agree after composing
with some transition morphism. -/
lemma exists_stage_equal_of_equal_on_limit {I : Type u} [Category.{u} I]
    [IsCofiltered I] {D : I ⥤ Scheme.{u}}
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] {T : Scheme.{u}}
    [LocallyOfFiniteType (terminal.from T)] (c : Cone D) (hc : IsLimit c)
    {i : I} (g₁ g₂ : D.obj i ⟶ T)
    (h : c.π.app i ≫ g₁ = c.π.app i ≫ g₂) :
    ∃ (k : I) (hki : k ⟶ i), D.map hki ≫ g₁ = D.map hki ≫ g₂ := by
  let t : D ⟶ (Functor.const I).obj (⊤_ Scheme.{u}) := {
    app j := terminal.from (D.obj j)
    naturality _ _ _ := terminalIsTerminal.hom_ext _ _ }
  exact Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (D := D) (t := t) (f := terminal.from T) (c := c) (hc := hc)
    g₁ g₂ (terminalIsTerminal.hom_ext _ _) (terminalIsTerminal.hom_ext _ _) h

/-- A presentation of a scheme `X` as the limit of a directed inverse system of schemes of
finite type over the integers with affine transition morphisms. -/
structure FiniteTypeSchemeApproximation (X : Scheme.{u}) where
  /-- The directed index set of the system. -/
  indexType : Type u
  [indexPreorder : Preorder indexType]
  [indexNonempty : Nonempty indexType]
  [indexDirected : IsDirected indexType (· ≤ ·)]
  /-- The inverse system of schemes. -/
  stages : indexTypeᵒᵖ ⥤ Scheme.{u}
  /-- The projections from `X` to the stages. -/
  projection : (Functor.const indexTypeᵒᵖ).obj X ⟶ stages
  /-- `X`, with the projections, is a limit of the system. -/
  limit : IsLimit (Cone.mk X projection)
  /-- The transition morphisms are affine. -/
  transition_affine : ∀ {i j : indexTypeᵒᵖ} (f : i ⟶ j), IsAffineHom (stages.map f)
  /-- Each stage is locally of finite type over the integers. -/
  stage_locallyOfFiniteType : ∀ i, LocallyOfFiniteType (terminal.from (stages.obj i))
  /-- Each stage is quasi-compact over the integers. -/
  stage_quasiCompact : ∀ i, QuasiCompact (terminal.from (stages.obj i))

attribute [instance] FiniteTypeSchemeApproximation.indexPreorder
  FiniteTypeSchemeApproximation.indexNonempty FiniteTypeSchemeApproximation.indexDirected

/-- Absolute Noetherian approximation: a quasi-compact and quasi-separated scheme is the limit
of a directed inverse system of schemes of finite type over the integers with affine transition
morphisms. -/
noncomputable def finiteTypeSchemeApproximation (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] : FiniteTypeSchemeApproximation X := by
  let Q := finiteTypeApproximationOfScheme (X := X)
  letI : Preorder Q.indexType := Q.indexPreorder
  letI : Nonempty Q.indexType := Q.indexNonempty
  letI : IsDirected Q.indexType (· ≤ ·) := Q.indexDirected
  let e := CategoryTheory.orderDualEquivalence Q.indexType
  let D : Q.indexTypeᵒᵖ ⥤ Scheme.{u} := e.inverse ⋙ Q.ambient
  let c₀ : Cone Q.ambient := Cone.mk X Q.ambientCone
  let c : Cone D := c₀.whisker e.inverse
  exact {
    indexType := Q.indexType
    stages := D
    projection := c.π
    limit := (Functor.Initial.isLimitWhiskerEquiv e.inverse c₀).symm Q.ambientCone_isLimit
    transition_affine g := Q.transition_affine (e.inverse.map g)
    stage_locallyOfFiniteType i := Q.locallyOfFiniteType (e.inverse.obj i)
    stage_quasiCompact i := Q.quasiCompact (e.inverse.obj i) }

/-- The projections of an approximation are compatible with its transition morphisms. -/
@[reassoc]
lemma FiniteTypeSchemeApproximation.projection_app_comp_map {X : Scheme.{u}}
    (A : FiniteTypeSchemeApproximation X) {i i' : A.indexTypeᵒᵖ} (φ : i ⟶ i') :
    A.projection.app i ≫ A.stages.map φ = A.projection.app i' :=
  (Cone.mk X A.projection).w φ

/-- Given approximations `A` of `X` and `B` of `S` and a morphism `f : X ⟶ S`, a morphism from a
stage of `A` to a stage of `B` whose composite with the projection from `X` equals `f` followed
by the projection to that stage of `B`. -/
structure CompatibleStageMap
    {X S : Scheme.{u}} (f : X ⟶ S)
    (A : FiniteTypeSchemeApproximation X) (B : FiniteTypeSchemeApproximation S) where
  /-- The index of the source stage. -/
  source : A.indexTypeᵒᵖ
  /-- The index of the target stage. -/
  target : B.indexTypeᵒᵖ
  /-- The morphism between the stages. -/
  hom : A.stages.obj source ⟶ B.stages.obj target
  /-- The morphism is compatible with `f` and the projections. -/
  compatible : A.projection.app source ≫ hom = f ≫ B.projection.app target

/-- `a.refines b` holds when there are transition maps from the stages of `b` to those of `a`
forming a commutative square with `a.hom` and `b.hom`. -/
def CompatibleStageMap.refines
    {X S : Scheme.{u}} {f : X ⟶ S}
    {A : FiniteTypeSchemeApproximation X} {B : FiniteTypeSchemeApproximation S}
    (a b : CompatibleStageMap f A B) : Prop :=
  ∃ (hi : b.source ⟶ a.source) (hj : b.target ⟶ a.target),
    A.stages.map hi ≫ a.hom = b.hom ≫ B.stages.map hj

/-- For every stage of `B` there is a stage of `A` and a morphism between them compatible with
`f` and the projections. -/
lemma compatibleStageMap_exists
    {X S : Scheme.{u}} (f : X ⟶ S)
    (A : FiniteTypeSchemeApproximation X)
    (B : FiniteTypeSchemeApproximation S) :
    ∀ j : B.indexTypeᵒᵖ, ∃ (i : A.indexTypeᵒᵖ)
      (g : A.stages.obj i ⟶ B.stages.obj j),
      A.projection.app i ≫ g = f ≫ B.projection.app j := by
  intro j
  have : ∀ {i i'} (g : i ⟶ i'), IsAffineHom (A.stages.map g) :=
    A.transition_affine
  have : ∀ i, LocallyOfFiniteType (terminal.from (A.stages.obj i)) :=
    A.stage_locallyOfFiniteType
  have : ∀ i, QuasiCompact (terminal.from (A.stages.obj i)) :=
    A.stage_quasiCompact
  have : ∀ i, CompactSpace (A.stages.obj i) := fun i =>
    (finiteTypeStage_compact_qs (A.stages.obj i)).1
  have : ∀ i, QuasiSeparatedSpace (A.stages.obj i) := fun i =>
    (finiteTypeStage_compact_qs (A.stages.obj i)).2
  have : LocallyOfFiniteType (terminal.from (B.stages.obj j)) := B.stage_locallyOfFiniteType j
  have : LocallyOfFinitePresentation (terminal.from (B.stages.obj j)) :=
    finiteTypeStage_locallyFinitePresentation (B.stages.obj j)
  exact exists_factor_from_limit (Cone.mk X A.projection) A.limit (f ≫ B.projection.app j)

/-- Let `a` be a compatible stage map and `g₀` a morphism from a stage of `A` to a stage of `B`
compatible with `f`. After passing to a further stage, `g₀` followed by a transition map agrees
with `a.hom` preceded by a transition map. -/
lemma CompatibleStageMap.exists_map_comp_eq
    {X S : Scheme.{u}} {f : X ⟶ S}
    {A : FiniteTypeSchemeApproximation X} {B : FiniteTypeSchemeApproximation S}
    (a : CompatibleStageMap f A B) {i i₀ : A.indexTypeᵒᵖ} {j : B.indexTypeᵒᵖ}
    (g₀ : A.stages.obj i₀ ⟶ B.stages.obj j)
    (hg₀ : A.projection.app i₀ ≫ g₀ = f ≫ B.projection.app j)
    (ii₀ : i ⟶ i₀) (iia : i ⟶ a.source) (ja : j ⟶ a.target) :
    ∃ (k : A.indexTypeᵒᵖ) (hk : k ⟶ i),
      A.stages.map (hk ≫ ii₀) ≫ g₀ ≫ B.stages.map ja = A.stages.map (hk ≫ iia) ≫ a.hom := by
  have : ∀ {k l} (q : k ⟶ l), IsAffineHom (A.stages.map q) :=
    A.transition_affine
  have := A.stage_locallyOfFiniteType
  have := A.stage_quasiCompact
  have : ∀ k, CompactSpace (A.stages.obj k) := fun k =>
    (finiteTypeStage_compact_qs (A.stages.obj k)).1
  have := B.stage_locallyOfFiniteType a.target
  have h : A.projection.app i ≫ A.stages.map ii₀ ≫ g₀ ≫ B.stages.map ja =
      A.projection.app i ≫ A.stages.map iia ≫ a.hom := by
    simp only [A.projection_app_comp_map_assoc, B.projection_app_comp_map, reassoc_of% hg₀,
      a.compatible]
  obtain ⟨k, hk, e⟩ := exists_stage_equal_of_equal_on_limit (Cone.mk X A.projection) A.limit
    (A.stages.map ii₀ ≫ g₀ ≫ B.stages.map ja) (A.stages.map iia ≫ a.hom) h
  exact ⟨k, hk, by simpa only [Functor.map_comp, Category.assoc] using e⟩

/-- Any two compatible stage maps are both refined by a third. -/
lemma compatibleStageMap_commonRefinement
    {X S : Scheme.{u}} (f : X ⟶ S)
    (A : FiniteTypeSchemeApproximation X)
    (B : FiniteTypeSchemeApproximation S)
    (a b : CompatibleStageMap f A B) :
    ∃ c : CompatibleStageMap f A B, a.refines c ∧ b.refines c := by
  let j := IsCofiltered.min a.target b.target
  let ja := IsCofiltered.minToLeft a.target b.target
  let jb := IsCofiltered.minToRight a.target b.target
  obtain ⟨i₀, g₀, hg₀⟩ := compatibleStageMap_exists f A B j
  let im := IsCofiltered.minToRight i₀ (IsCofiltered.min a.source b.source)
  let ii₀ := IsCofiltered.minToLeft i₀ (IsCofiltered.min a.source b.source)
  let iia := im ≫ IsCofiltered.minToLeft a.source b.source
  let iib := im ≫ IsCofiltered.minToRight a.source b.source
  obtain ⟨ka, hka, eqa⟩ := a.exists_map_comp_eq g₀ hg₀ ii₀ iia ja
  obtain ⟨kb, hkb, eqb⟩ := b.exists_map_comp_eq g₀ hg₀ ii₀ iib jb
  let hka' := IsCofiltered.minToLeft ka kb
  let hkb' := IsCofiltered.minToRight ka kb
  refine ⟨⟨IsCofiltered.min ka kb, j, A.stages.map (hka' ≫ hka ≫ ii₀) ≫ g₀, ?_⟩,
    ⟨hka' ≫ hka ≫ iia, ja, ?_⟩, ⟨hkb' ≫ hkb ≫ iib, jb, ?_⟩⟩
  · rw [A.projection_app_comp_map_assoc, hg₀]
  · simpa only [Functor.map_comp, Category.assoc] using (A.stages.map hka' ≫= eqa).symm
  · rw [show hka' ≫ hka ≫ ii₀ = hkb' ≫ hkb ≫ ii₀ from Subsingleton.elim _ _]
    simpa only [Functor.map_comp, Category.assoc] using (A.stages.map hkb' ≫= eqb).symm

/-- The type of compatible stage maps, lifted to the universe of schemes. -/
abbrev CompatibleStageIndex
    {X S : Scheme.{u}} (f : X ⟶ S)
    (A : FiniteTypeSchemeApproximation X) (B : FiniteTypeSchemeApproximation S) :=
  ULift.{u} (CompatibleStageMap f A B)

/-- The order on compatible stage maps given by refinement. -/
instance compatibleStageIndexLE
    {X S : Scheme.{u}} {f : X ⟶ S}
    {A : FiniteTypeSchemeApproximation X} {B : FiniteTypeSchemeApproximation S} :
    LE (CompatibleStageIndex f A B) :=
  ⟨fun a b => a.down.refines b.down⟩

/-- Refinement is a preorder on compatible stage maps. -/
instance compatibleStageIndexPreorder
    {X S : Scheme.{u}} {f : X ⟶ S}
    {A : FiniteTypeSchemeApproximation X} {B : FiniteTypeSchemeApproximation S} :
    Preorder (CompatibleStageIndex f A B) where
  le_refl a := ⟨𝟙 _, 𝟙 _, by simp⟩
  le_trans _ _ _ := by
    rintro ⟨hab₁, hab₂, hab⟩ ⟨hbc₁, hbc₂, hbc⟩
    exact ⟨hbc₁ ≫ hab₁, hbc₂ ≫ hab₂, by
      simp only [Functor.map_comp, Category.assoc, hab, reassoc_of% hbc]⟩

/-- Compatible stage maps are directed under refinement. -/
instance compatibleStageIndexDirected
    {X S : Scheme.{u}} {f : X ⟶ S}
    {A : FiniteTypeSchemeApproximation X} {B : FiniteTypeSchemeApproximation S} :
    IsDirected (CompatibleStageIndex f A B) (· ≤ ·) where
  directed a b := by
    obtain ⟨c, hac, hbc⟩ := compatibleStageMap_commonRefinement f A B a.down b.down
    exact ⟨ULift.up c, hac, hbc⟩

/-- For `j ≤ i`, a chosen transition map between the source stages of `i` and `j`. -/
noncomputable def compatibleStageSourceMap
    {X S : Scheme.{u}} {f : X ⟶ S}
    {A : FiniteTypeSchemeApproximation X} {B : FiniteTypeSchemeApproximation S}
    {i j : CompatibleStageIndex f A B}
    (h : j ⟶ i) : i.down.source ⟶ j.down.source :=
  Classical.choose (leOfHom h)

/-- For `j ≤ i`, a chosen transition map between the target stages of `i` and `j`. -/
noncomputable def compatibleStageTargetMap
    {X S : Scheme.{u}} {f : X ⟶ S}
    {A : FiniteTypeSchemeApproximation X} {B : FiniteTypeSchemeApproximation S}
    {i j : CompatibleStageIndex f A B}
    (h : j ⟶ i) : i.down.target ⟶ j.down.target :=
  Classical.choose (Classical.choose_spec (leOfHom h))

/-- The chosen source and target transition maps form a commutative square with the stage maps
of `i` and `j`. -/
lemma compatibleStageMap_square
    {X S : Scheme.{u}} {f : X ⟶ S}
    {A : FiniteTypeSchemeApproximation X} {B : FiniteTypeSchemeApproximation S}
    {i j : CompatibleStageIndex f A B}
    (h : j ⟶ i) :
    A.stages.map (compatibleStageSourceMap h) ≫ j.down.hom =
      i.down.hom ≫ B.stages.map (compatibleStageTargetMap h) :=
  Classical.choose_spec (Classical.choose_spec (leOfHom h))

/-- The inverse system of arrows of schemes indexed by compatible stage maps, sending each to its
underlying morphism between stages. -/
noncomputable def compatibleStageDiagram
    {X S : Scheme.{u}} {f : X ⟶ S}
    (A : FiniteTypeSchemeApproximation X) (B : FiniteTypeSchemeApproximation S) :
    (CompatibleStageIndex f A B)ᵒᵖ ⥤ Arrow Scheme.{u} where
  obj i := Arrow.mk i.unop.down.hom
  map h := Arrow.homMk' (A.stages.map (compatibleStageSourceMap h.unop))
    (B.stages.map (compatibleStageTargetMap h.unop)) (compatibleStageMap_square h.unop)
  map_id _ := Arrow.hom_ext _ _
    ((congrArg A.stages.map (Subsingleton.elim _ _)).trans (A.stages.map_id _))
    ((congrArg B.stages.map (Subsingleton.elim _ _)).trans (B.stages.map_id _))
  map_comp _ _ := Arrow.hom_ext _ _
    ((congrArg A.stages.map (Subsingleton.elim _ _)).trans (A.stages.map_comp _ _))
    ((congrArg B.stages.map (Subsingleton.elim _ _)).trans (B.stages.map_comp _ _))

/-- The functor sending a compatible stage map to the index of its source stage. -/
noncomputable def compatibleSourceProjection
    {X S : Scheme.{u}} {f : X ⟶ S}
    (A : FiniteTypeSchemeApproximation X) (B : FiniteTypeSchemeApproximation S) :
    (CompatibleStageIndex f A B)ᵒᵖ ⥤ A.indexTypeᵒᵖ where
  obj i := i.unop.down.source
  map h := compatibleStageSourceMap h.unop
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The functor sending a compatible stage map to the index of its target stage. -/
noncomputable def compatibleTargetProjection
    {X S : Scheme.{u}} {f : X ⟶ S}
    (A : FiniteTypeSchemeApproximation X) (B : FiniteTypeSchemeApproximation S) :
    (CompatibleStageIndex f A B)ᵒᵖ ⥤ B.indexTypeᵒᵖ where
  obj i := i.unop.down.target
  map h := compatibleStageTargetMap h.unop
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- There is a compatible stage map. -/
theorem compatibleStageIndex_nonempty
    {X S : Scheme.{u}} (f : X ⟶ S)
    (A : FiniteTypeSchemeApproximation X) (B : FiniteTypeSchemeApproximation S) :
    Nonempty (CompatibleStageIndex f A B) := by
  let j : B.indexTypeᵒᵖ := Opposite.op (Classical.choice B.indexNonempty)
  obtain ⟨i, g, hg⟩ := compatibleStageMap_exists f A B j
  exact ⟨ULift.up ⟨i, j, g, hg⟩⟩

/-- The projection from compatible stage maps to the source index category is initial. -/
lemma compatibleSourceProjection_initial
    {X S : Scheme.{u}} (f : X ⟶ S)
    (A : FiniteTypeSchemeApproximation X) (B : FiniteTypeSchemeApproximation S) :
    (compatibleSourceProjection (f := f) A B).Initial := by
  have := compatibleStageIndex_nonempty f A B
  refine Functor.initial_of_exists_of_isCofiltered _ (fun d => ?_)
    (fun _ _ => ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)
  obtain ⟨i, g, hg⟩ :=
    compatibleStageMap_exists f A B (Opposite.op (Classical.choice B.indexNonempty))
  exact ⟨Opposite.op (ULift.up ⟨IsCofiltered.min i d, _,
    A.stages.map (IsCofiltered.minToLeft i d) ≫ g,
    by rw [A.projection_app_comp_map_assoc, hg]⟩), ⟨IsCofiltered.minToRight i d⟩⟩

/-- The projection from compatible stage maps to the target index category is initial. -/
lemma compatibleTargetProjection_initial
    {X S : Scheme.{u}} (f : X ⟶ S)
    (A : FiniteTypeSchemeApproximation X) (B : FiniteTypeSchemeApproximation S) :
    (compatibleTargetProjection (f := f) A B).Initial := by
  have := compatibleStageIndex_nonempty f A B
  refine Functor.initial_of_exists_of_isCofiltered _ (fun d => ?_)
    (fun _ _ => ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)
  let k := IsCofiltered.min (Opposite.op (Classical.choice B.indexNonempty)) d
  obtain ⟨i, g, hg⟩ := compatibleStageMap_exists f A B k
  exact ⟨Opposite.op (ULift.up ⟨i, k, g, hg⟩), ⟨IsCofiltered.minToRight _ d⟩⟩

/-- A morphism between quasi-compact and quasi-separated schemes is a limit of morphisms between
schemes of finite type over `ℤ`, with affine transition morphisms on sources and targets. -/
@[stacks 0GS1]
theorem exists_isLimit_finiteType_arrow
    {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirectedOrder I)
      (D : Iᵒᵖ ⥤ Arrow Scheme.{u}) (c : Cone D),
      (∀ i,
        LocallyOfFiniteType (terminal.from (D.obj i).left) ∧
          QuasiCompact (terminal.from (D.obj i).left)) ∧
      (∀ i,
        LocallyOfFiniteType (terminal.from (D.obj i).right) ∧
          QuasiCompact (terminal.from (D.obj i).right)) ∧
      (∀ {i j : Iᵒᵖ} (g : i ⟶ j),
        IsAffineHom (D.map g).left ∧ IsAffineHom (D.map g).right) ∧
      Nonempty (IsLimit c) ∧ Nonempty (c.pt ≅ Arrow.mk f) := by
  let A := finiteTypeSchemeApproximation X
  let B := finiteTypeSchemeApproximation S
  let I := CompatibleStageIndex f A B
  let Fsrc := compatibleSourceProjection (f := f) A B
  let Ftgt := compatibleTargetProjection (f := f) A B
  let D := compatibleStageDiagram (f := f) A B
  let p : (Functor.const (Iᵒᵖ)).obj (Arrow.mk f) ⟶ D := {
    app i := Arrow.homMk' (A.projection.app (Fsrc.obj i))
      (B.projection.app (Ftgt.obj i)) i.unop.down.compatible
    naturality i j g := Arrow.hom_ext _ _ (A.projection_app_comp_map (Fsrc.map g)).symm
      (B.projection_app_comp_map (Ftgt.map g)).symm }
  let c : Cone D := Cone.mk (Arrow.mk f) p
  have : Fsrc.Initial := compatibleSourceProjection_initial f A B
  have : Ftgt.Initial := compatibleTargetProjection_initial f A B
  exact ⟨I, inferInstance, compatibleStageIndex_nonempty f A B, inferInstance, D, c,
    fun i => ⟨A.stage_locallyOfFiniteType (Fsrc.obj i), A.stage_quasiCompact (Fsrc.obj i)⟩,
    fun i => ⟨B.stage_locallyOfFiniteType (Ftgt.obj i), B.stage_quasiCompact (Ftgt.obj i)⟩,
    fun g => ⟨A.transition_affine (Fsrc.map g), B.transition_affine (Ftgt.map g)⟩,
    ⟨Comma.fstSndJointlyReflectLimit
      ((Functor.Initial.isLimitWhiskerEquiv Fsrc (Cone.mk X A.projection)).symm A.limit)
      ((Functor.Initial.isLimitWhiskerEquiv Ftgt (Cone.mk S B.projection)).symm B.limit)⟩,
    ⟨Iso.refl _⟩⟩

end AlgebraicGeometry.LimitFPObjectDescent
