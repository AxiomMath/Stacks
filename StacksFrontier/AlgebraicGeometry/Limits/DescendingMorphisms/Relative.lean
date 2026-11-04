module

public import Mathlib.CategoryTheory.EssentiallySmall
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# Descending morphisms between relative schemes of finite presentation

Let a scheme be the limit of a cofiltered system of quasi-compact and quasi-separated schemes
whose transition morphisms are affine, and let two schemes of finite presentation over one stage
be given. A morphism between their base changes to the limit already comes from a morphism
between their base changes to some later stage, and two morphisms at one stage that agree after
base change to the limit already agree at some later stage.

## Main definitions

* `AlgebraicGeometry.overPullbackCompIso`: the canonical identification of the iterated base
  change of a scheme over `T` with its direct base change, as an isomorphism in an over category.

## Main results

* `AlgebraicGeometry.exists_morphism_after_baseChange` descends morphisms.
* `AlgebraicGeometry.eventually_eq_of_baseChange_eq` descends equalities of morphisms.

## Implementation notes

A directed inverse system is represented more generally by a functor out of an essentially small
cofiltered category. Smallness is relative to the scheme universe, as the source's directed set
belongs to the same ambient universe as the schemes. A limit in a smaller category of schemes need
not remain a limit after enlarging that universe. The object and morphism universes of the index
category remain independent. Schemes over a base are objects of its over category, and base change
is `CategoryTheory.Over.pullback`. In the morphism assertion, the displayed isomorphisms identify
iterated base change with direct base change; their equations with the first pullback projections
specify the canonical identifications.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

/-! ### Comparing iterated base change with direct base change -/

section Comparison

variable {S S' T : Scheme.{u}}

/-- Two morphisms into a base change of `X` along `r` agree if they agree after composing with the
first projection. -/
private lemma over_pullback_hom_ext {X : Over T} {A : Over S'} (r : S' ⟶ T)
    (u v : A ⟶ (Over.pullback r).obj X)
    (h : u.left ≫ pullback.fst X.hom r = v.left ≫ pullback.fst X.hom r) : u = v := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h
  · exact (Over.w u).trans (Over.w v).symm

/-- The canonical identification of the iterated base change of a scheme over `T`, first to `S`
and then to `S'`, with its direct base change to `S'` along the composite. -/
def overPullbackCompIso (p : S ⟶ T) (q : S' ⟶ S) (r : S' ⟶ T) (h : q ≫ p = r) (X : Over T) :
    (Over.pullback q).obj ((Over.pullback p).obj X) ≅ (Over.pullback r).obj X :=
  Over.isoMk (pullbackLeftPullbackSndIso X.hom p q ≪≫ pullback.congrHom rfl h) (by
    subst h
    simp)

/-- The comparison isomorphism is compatible with the first pullback projections. -/
lemma overPullbackCompIso_fst (p : S ⟶ T) (q : S' ⟶ S) (r : S' ⟶ T) (h : q ≫ p = r)
    (X : Over T) :
    (overPullbackCompIso p q r h X).hom.left ≫ pullback.fst X.hom r =
      pullback.fst ((Over.pullback p).obj X).hom q ≫ pullback.fst X.hom p := by
  subst h
  simp [overPullbackCompIso]

/-- The comparison isomorphism is natural in the scheme being base changed. -/
lemma overPullbackCompIso_naturality (p : S ⟶ T) (q : S' ⟶ S) (r : S' ⟶ T) (h : q ≫ p = r)
    {X Y : Over T} (f : X ⟶ Y) :
    (overPullbackCompIso p q r h X).hom ≫ (Over.pullback r).map f =
      (Over.pullback q).map ((Over.pullback p).map f) ≫
        (overPullbackCompIso p q r h Y).hom := by
  apply over_pullback_hom_ext
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc,
    overPullback_map_left_fst r f, reassoc_of% overPullbackCompIso_fst,
    overPullbackCompIso_fst,
    reassoc_of% overPullback_map_left_fst q ((Over.pullback p).map f),
    overPullback_map_left_fst p f]

/-- Compatibility with the first pullback projections characterises the comparison
isomorphism. -/
lemma iso_eq_overPullbackCompIso (p : S ⟶ T) (q : S' ⟶ S) (r : S' ⟶ T) (h : q ≫ p = r)
    (X : Over T)
    (α : (Over.pullback q).obj ((Over.pullback p).obj X) ≅ (Over.pullback r).obj X)
    (hα : α.hom.left ≫ pullback.fst X.hom r =
      pullback.fst ((Over.pullback p).obj X).hom q ≫ pullback.fst X.hom p) :
    α = overPullbackCompIso p q r h X := by
  exact Iso.ext (over_pullback_hom_ext r _ _ (hα.trans (overPullbackCompIso_fst p q r h X).symm))

end Comparison

/-! ### Descending morphisms and equalities of morphisms -/

section Descent

variable {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- Two morphisms out of a stage of a cofiltered system into a scheme locally of finite type over
the base, which agree after base change to the limit, agree at some later stage. This is the
universe-independent form of
`AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`. -/
private lemma exists_hom_comp_eq_comp_of_locallyOfFiniteType_of_essentiallySmall (hc : IsLimit c)
    {S X : Scheme.{u}} (t : D ⟶ (Functor.const I).obj S) (f : X ⟶ S) [LocallyOfFiniteType f]
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)] [∀ i : I, CompactSpace (D.obj i)]
    {i : I} (a b : D.obj i ⟶ X) (ha : t.app i = a ≫ f) (hb : t.app i = b ≫ f)
    (hab : c.π.app i ≫ a = c.π.app i ≫ b) :
    ∃ (j : I) (e : j ⟶ i), D.map e ≫ a = D.map e ≫ b := by
  let e := equivSmallModel.{u} I
  have : IsCofiltered (SmallModel.{u} I) := IsCofiltered.of_equivalence e
  have (j : SmallModel.{u} I) : CompactSpace ((e.inverse ⋙ D).obj j) := by dsimp; infer_instance
  have {j k} (h : j ⟶ k) : IsAffineHom ((e.inverse ⋙ D).map h) := by dsimp; infer_instance
  let q := e.unitIso.inv.app i
  obtain ⟨j, h, hh⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (e.inverse ⋙ D) (Functor.whiskerLeft e.inverse t) f (c.whisker e.inverse)
    ((Functor.Initial.isLimitWhiskerEquiv e.inverse c).symm hc)
    (D.map q ≫ a) (D.map q ≫ b)
    (by simpa [q, ha] using (t.naturality q).symm)
    (by simpa [q, hb] using (t.naturality q).symm)
    (by simpa using hab)
  exact ⟨e.inverse.obj j, e.inverse.map h ≫ q, by simpa using hh⟩

variable [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)] [∀ i : I, CompactSpace (D.obj i)]
  [∀ i : I, QuasiSeparatedSpace (D.obj i)]

/-- The version of `AlgebraicGeometry.exists_morphism_after_baseChange` that asks of the source
only that it be quasi-compact and quasi-separated over the stage. -/
private theorem exists_morphism_after_baseChange_of_quasiCompact (hc : IsLimit c) (i : I)
    (X Y : Over (D.obj i)) (hX : QuasiCompact X.hom) (hXqs : QuasiSeparated X.hom)
    (hY : LocallyOfFinitePresentation Y.hom)
    (f : (Over.pullback (c.π.app i)).obj X ⟶ (Over.pullback (c.π.app i)).obj Y) :
    ∃ (j : I) (e : j ⟶ i)
      (g : (Over.pullback (D.map e)).obj X ⟶ (Over.pullback (D.map e)).obj Y)
      (α : (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj X) ≅
        (Over.pullback (c.π.app i)).obj X)
      (β : (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj Y) ≅
        (Over.pullback (c.π.app i)).obj Y),
      α.hom.left ≫ pullback.fst X.hom (c.π.app i) =
          pullback.fst ((Over.pullback (D.map e)).obj X).hom (c.π.app j) ≫
            pullback.fst X.hom (D.map e) ∧
        β.hom.left ≫ pullback.fst Y.hom (c.π.app i) =
          pullback.fst ((Over.pullback (D.map e)).obj Y).hom (c.π.app j) ≫
            pullback.fst Y.hom (D.map e) ∧
        α.hom ≫ f = (Over.pullback (c.π.app j)).map g ≫ β.hom := by
  have : LocallyOfFinitePresentation Y.hom := hY
  have : QuasiCompact X.hom := hX
  have : QuasiSeparated X.hom := hXqs
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have : InitiallySmall.{u} (Over i) := initiallySmall_of_essentiallySmall _
  have {j k : Over i} (e : j ⟶ k) : IsAffineHom ((baseChangeDiagram D i X).map e) :=
    isAffineHom_baseChangeDiagram_map D i X e
  have (j : Over i) : CompactSpace ((baseChangeDiagram D i X).obj j) :=
    compactSpace_baseChangeDiagram_obj D i X j
  have (j : Over i) : QuasiSeparatedSpace ((baseChangeDiagram D i X).obj j) :=
    quasiSeparatedSpace_baseChangeDiagram_obj D i X j
  let a : pullback (c.π.app i) X.hom ⟶ Y.left :=
    (pullbackSymmetry (c.π.app i) X.hom).hom ≫ f.left ≫ pullback.fst Y.hom (c.π.app i)
  have hf : f.left ≫ pullback.snd Y.hom (c.π.app i) = pullback.snd X.hom (c.π.app i) := Over.w f
  have hcomp (j : Over i) :
      baseChangeTransition (D.map j.hom) (c.π.app i) (c.π.app j.left) (by simp) X ≫
          (pullback.snd (D.map j.hom) X.hom ≫ X.hom) =
        ((pullbackSymmetry (c.π.app i) X.hom).hom ≫
          f.left ≫ pullback.fst Y.hom (c.π.app i)) ≫ Y.hom := by
    rw [baseChangeTransition_snd_assoc, Category.assoc, Category.assoc, pullback.condition,
      reassoc_of% hf, ← Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact pullback.condition.symm
  have ha : (baseChangeCone D c i X).π ≫ baseChangeStructureMap D i X =
      (Functor.const _).map (a ≫ Y.hom) := by
    ext j
    exact hcomp j
  obtain ⟨j, u₀, hu₀, hu₀'⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_initiallySmall
      (baseChangeDiagram D i X) (baseChangeCone D c i X) (baseChangeStructureMap D i X) Y.hom
      (baseChangeConeIsLimit D hc i X) a ha
  obtain ⟨u, hu, hu'⟩ : ∃ u : pullback (D.map j.hom) X.hom ⟶ Y.left,
      baseChangeTransition (D.map j.hom) (c.π.app i) (c.π.app j.left) (by simp) X ≫ u = a ∧
      u ≫ Y.hom = pullback.snd (D.map j.hom) X.hom ≫ X.hom := ⟨u₀, hu₀, hu₀'⟩
  have hw : ((pullbackSymmetry X.hom (D.map j.hom)).hom ≫ u) ≫ Y.hom =
      pullback.snd X.hom (D.map j.hom) ≫ D.map j.hom := by
    rw [Category.assoc, hu', ← Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact pullback.condition
  let g : (Over.pullback (D.map j.hom)).obj X ⟶ (Over.pullback (D.map j.hom)).obj Y :=
    Over.homMk (pullback.lift ((pullbackSymmetry X.hom (D.map j.hom)).hom ≫ u)
      (pullback.snd X.hom (D.map j.hom)) hw) (pullback.lift_snd _ _ _)
  let α := overPullbackCompIso (D.map j.hom) (c.π.app j.left) (c.π.app i) (c.w j.hom) X
  let β := overPullbackCompIso (D.map j.hom) (c.π.app j.left) (c.π.app i) (c.w j.hom) Y
  refine ⟨j.left, j.hom, g, α, β, overPullbackCompIso_fst _ _ _ _ _,
    overPullbackCompIso_fst _ _ _ _ _, ?_⟩
  have hαw : α.hom.left ≫ pullback.snd X.hom (c.π.app i) =
      pullback.snd (pullback.snd X.hom (D.map j.hom)) (c.π.app j.left) := by
    simpa only [Over.pullback_obj_hom] using Over.w α.hom
  have hδ : α.hom.left ≫ (pullbackSymmetry X.hom (c.π.app i)).hom ≫
      baseChangeTransition (D.map j.hom) (c.π.app i) (c.π.app j.left) (by simp) X =
      pullback.fst (pullback.snd X.hom (D.map j.hom)) (c.π.app j.left) ≫
        (pullbackSymmetry X.hom (D.map j.hom)).hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, baseChangeTransition_fst,
        pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_fst]
      rw [← Category.assoc, hαw]
      exact pullback.condition.symm
    · simp only [Category.assoc, baseChangeTransition_snd, pullbackSymmetry_hom_comp_snd]
      simpa only [Over.pullback_obj_hom] using
        overPullbackCompIso_fst (D.map j.hom) (c.π.app j.left) (c.π.app i) (c.w j.hom) X
  apply over_pullback_hom_ext
  · have h : pullback.fst (pullback.snd X.hom (D.map j.hom)) (c.π.app j.left) ≫
        (pullbackSymmetry X.hom (D.map j.hom)).hom ≫ u =
        α.hom.left ≫ (pullbackSymmetry X.hom (c.π.app i)).hom ≫ a := by
      rw [← Category.assoc, ← hδ, Category.assoc, Category.assoc, hu]
    have hs : (pullbackSymmetry X.hom (c.π.app i)).hom ≫
        (pullbackSymmetry (c.π.app i) X.hom).hom = 𝟙 _ := by
      apply pullback.hom_ext <;> simp
    have hg : g.left ≫ pullback.fst Y.hom (D.map j.hom) =
        (pullbackSymmetry X.hom (D.map j.hom)).hom ≫ u := pullback.lift_fst _ _ _
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc,
      overPullbackCompIso_fst (D.map j.hom) (c.π.app j.left) (c.π.app i) (c.w j.hom) Y,
      reassoc_of% overPullback_map_left_fst, hg]
    simp only [Over.pullback_obj_hom]
    rw [h]
    simp only [a]
    rw [← Category.assoc (pullbackSymmetry X.hom (c.π.app i)).hom
      (pullbackSymmetry (c.π.app i) X.hom).hom, hs, Category.id_comp]

omit [∀ i : I, QuasiSeparatedSpace (D.obj i)] in
/-- The version of `AlgebraicGeometry.eventually_eq_of_baseChange_eq` that asks of the source only
that it be quasi-compact over the stage and of the target only that it be locally of finite
type. -/
private theorem eventually_eq_of_baseChange_eq_of_locallyOfFiniteType (hc : IsLimit c) (i : I)
    (X Y : Over (D.obj i)) (hX : QuasiCompact X.hom) (hY : LocallyOfFiniteType Y.hom)
    (f g : X ⟶ Y)
    (hfg : (Over.pullback (c.π.app i)).map f = (Over.pullback (c.π.app i)).map g) :
    ∃ (j : I) (e : j ⟶ i),
      (Over.pullback (D.map e)).map f = (Over.pullback (D.map e)).map g := by
  have : LocallyOfFiniteType Y.hom := hY
  have : QuasiCompact X.hom := hX
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have {j k : Over i} (e : j ⟶ k) : IsAffineHom ((baseChangeDiagram D i X).map e) :=
    isAffineHom_baseChangeDiagram_map D i X e
  have (j : Over i) : CompactSpace ((baseChangeDiagram D i X).obj j) :=
    compactSpace_baseChangeDiagram_obj D i X j
  have heq : pullback.fst X.hom (c.π.app i) ≫ f.left =
      pullback.fst X.hom (c.π.app i) ≫ g.left := by
    simpa only [overPullback_map_left_fst] using
      congrArg (fun k => k.left ≫ pullback.fst Y.hom (c.π.app i)) hfg
  have hsnd : pullback.snd (c.π.app i) X.hom ≫ f.left =
      pullback.snd (c.π.app i) X.hom ≫ g.left := by
    rw [← pullbackSymmetry_hom_comp_fst (c.π.app i) X.hom, Category.assoc, Category.assoc]
    exact congrArg (fun k => (pullbackSymmetry (c.π.app i) X.hom).hom ≫ k) heq
  have hab : baseChangeTransition (D.map (𝟙 i)) (c.π.app i) (c.π.app i) (by simp) X ≫
      (pullback.snd (D.map (𝟙 i)) X.hom ≫ f.left) =
      baseChangeTransition (D.map (𝟙 i)) (c.π.app i) (c.π.app i) (by simp) X ≫
      (pullback.snd (D.map (𝟙 i)) X.hom ≫ g.left) := by
    rw [← Category.assoc, ← Category.assoc, baseChangeTransition_snd, hsnd]
  obtain ⟨j, e, hj⟩ := exists_hom_comp_eq_comp_of_locallyOfFiniteType_of_essentiallySmall
    (baseChangeDiagram D i X) (baseChangeCone D c i X) (baseChangeConeIsLimit D hc i X)
    (baseChangeStructureMap D i X) Y.hom
    (i := Over.mk (𝟙 i))
    (pullback.snd (D.map (𝟙 i)) X.hom ≫ f.left)
    (pullback.snd (D.map (𝟙 i)) X.hom ≫ g.left)
    ((Category.assoc _ _ _).trans
      (congrArg (fun k => pullback.snd (D.map (𝟙 i)) X.hom ≫ k) (Over.w f))).symm
    ((Category.assoc _ _ _).trans
      (congrArg (fun k => pullback.snd (D.map (𝟙 i)) X.hom ≫ k) (Over.w g))).symm
    hab
  refine ⟨j.left, j.hom, ?_⟩
  have hbct : (baseChangeDiagram D i X).map e ≫ pullback.snd (D.map (𝟙 i)) X.hom =
      pullback.snd (D.map j.hom) X.hom :=
    baseChangeTransition_snd (D.map (𝟙 i)) (D.map j.hom) (D.map e.left)
      (by simpa using congrArg D.map (Over.w e)) X
  have hj' : pullback.snd (D.map j.hom) X.hom ≫ f.left =
      pullback.snd (D.map j.hom) X.hom ≫ g.left := by
    rw [← hbct]
    exact (Category.assoc _ _ _).trans (hj.trans (Category.assoc _ _ _).symm)
  apply over_pullback_hom_ext
  rw [overPullback_map_left_fst, overPullback_map_left_fst]
  simpa only [pullbackSymmetry_hom_comp_snd_assoc] using
    congrArg (fun k => (pullbackSymmetry X.hom (D.map j.hom)).hom ≫ k) hj'

end Descent

/-- A morphism between the base changes of two schemes of finite presentation
descends after passing to a later stage of a cofiltered inverse system. -/
@[stacks 01ZM "part (2)"]
theorem exists_morphism_after_baseChange
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (X Y : Over (D.obj i))
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom)
    (f : (Over.pullback (c.π.app i)).obj X ⟶ (Over.pullback (c.π.app i)).obj Y) :
    ∃ (j : I) (e : j ⟶ i)
      (g : (Over.pullback (D.map e)).obj X ⟶ (Over.pullback (D.map e)).obj Y)
      (α : (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj X) ≅
        (Over.pullback (c.π.app i)).obj X)
      (β : (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj Y) ≅
        (Over.pullback (c.π.app i)).obj Y),
      α.hom.left ≫ pullback.fst X.hom (c.π.app i) =
          pullback.fst ((Over.pullback (D.map e)).obj X).hom (c.π.app j) ≫
            pullback.fst X.hom (D.map e) ∧
        β.hom.left ≫ pullback.fst Y.hom (c.π.app i) =
          pullback.fst ((Over.pullback (D.map e)).obj Y).hom (c.π.app j) ≫
            pullback.fst Y.hom (D.map e) ∧
        α.hom ≫ f = (Over.pullback (c.π.app j)).map g ≫ β.hom :=
  exists_morphism_after_baseChange_of_quasiCompact D c hc i X Y hX.2.1 hX.2.2 hY.1 f

/-- Two morphisms at one stage which become equal after base change to the
inverse limit are equal after passing to a later stage. -/
@[stacks 01ZM "part (3)"]
theorem eventually_eq_of_baseChange_eq
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (X Y : Over (D.obj i))
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom) (f g : X ⟶ Y)
    (hfg : (Over.pullback (c.π.app i)).map f = (Over.pullback (c.π.app i)).map g) :
    ∃ (j : I) (e : j ⟶ i),
      (Over.pullback (D.map e)).map f = (Over.pullback (D.map e)).map g := by
  have : LocallyOfFinitePresentation Y.hom := hY.1
  exact eventually_eq_of_baseChange_eq_of_locallyOfFiniteType D c hc i X Y hX.2.1 inferInstance
    f g hfg

end AlgebraicGeometry
