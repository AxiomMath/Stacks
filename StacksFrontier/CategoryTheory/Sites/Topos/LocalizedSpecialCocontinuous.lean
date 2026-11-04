module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite

/-!
# Localizing a special cocontinuous functor at an object

Let `G : C ⥤ D` be a functor of sites exhibiting `(C, J)` as a dense subsite of `(D, K)` — the
hypotheses of a *special cocontinuous functor* in the sense of Stacks 03CG — and let `R` be a
sheaf of rings on `(D, K)`.  Restriction of sections along `G` carries `R` to a sheaf of rings
on `(C, J)` and sheaves of `R`-modules to sheaves of modules over it, and this restriction is an
equivalence by the Comparison Lemma for modules,
`Stacks.DenseSubsiteModules.moduleRestrictionEquivalence`.

This file localizes that picture at an object `U` of `C`, which is what Section 03DG of the
source prescribes and what the local conditions of Stacks 03DL consume.  The localization
`Over.post G : Over U ⥤ Over (G.obj U)` is again a dense subsite inclusion
(`Stacks.Sites.overPost_isDenseSubsite`), the two localized structure sheaves agree on the nose,
and the resulting equivalence of categories of sheaves of modules commutes with
`SheafOfModules.over` on the nose as well.  Together with the transport of a covering between
the two sites, that is the whole of the geometric input of Stacks 03DM.

The last section carries the sectionwise finite-type condition
`PresheafOfModules.IsFiniteType` across the restriction of sections along `G`, in both
directions.  That is the one local condition of Stacks 03DL which is not stated as a property of
the restrictions of a module to the members of a covering family, so it is not reached by the
covering transport below; it is the condition the coherence clause of Stacks 03DL is built from,
both for a module and for its sheaves of relations.

## Main definitions

* `Stacks.LocalizedDenseSubsite.sliceEquivalence`: the localized Comparison Lemma, the
  equivalence `SheafOfModules (R.over (G.obj U)) ≌ SheafOfModules ((restriction of R).over U)`.
* `Stacks.LocalizedDenseSubsite.sliceEquivalenceUnitIso` and `.sliceEquivalenceObjIso`: it
  carries the structure sheaf to the structure sheaf and the restriction of a module to the
  restriction of its restriction.
* `Stacks.LocalizedDenseSubsite.sliceRestriction`: the same comparison preceded by restriction
  along an arrow `G.obj U ⟶ V`, which is what a covering of `G.obj U` refined by images of `G`
  needs; `.sliceRestrictionUnitIso` and `.sliceRestrictionObjIso` are its two comparisons.

## Main results

* `Stacks.LocalizedDenseSubsite.ringRestriction_over`: the structure sheaf of the localized
  subsite is the localization of the restricted structure sheaf.
* `Stacks.LocalizedDenseSubsite.forall_exists_cover_iff`: **the covering transport of
  Stacks 03DM.**  A property of modules on slices which travels along `sliceRestriction` in one
  direction and along `sliceEquivalence` in the other holds on a covering of every object of
  `D` exactly when the corresponding property of the restricted module holds on a covering of
  every object of `C`.  This is the first two paragraphs of the proof of Stacks 03DM, with the
  property left abstract, as the source leaves it.
* `Stacks.LocalizedDenseSubsite.ofArrows_mem_of_coversTop_over`: a family of objects of the
  slice site over `U` covering its terminal object generates a covering sieve of `U`.  This is
  the converse of `Stacks.SheafOfModules.coversTop_over_of_ofArrows_mem`, and the two translate
  between the ways the clauses of Stacks 03DL record a covering.
* `Stacks.LocalizedDenseSubsite.coversTop_map`: the images of a family covering the terminal
  object of the subsite cover the terminal object of the ambient site.
* `Stacks.DenseSubsiteModules.isFiniteType_pushforward₀` and
  `Stacks.DenseSubsiteModules.isFiniteType_of_pushforward₀`: **the Comparison Lemma for the
  sectionwise finite-type condition.**  A presheaf of modules on `(D, K)` is of finite type if
  and only if its restriction of sections along `G` is of finite type on `(C, J)`.  Each half
  rests on the corresponding half for a single finite generating family,
  `Stacks.DenseSubsiteModules.generates_pushforward₀` and
  `Stacks.DenseSubsiteModules.generates_of_pushforward₀`.

## Implementation notes

The two sites are taken in a common pair of universes.  This is forced by the statement being
transported, not by the method: the covering families of Stacks 03DL are indexed in
`Type (max u v)` for the universes `u`, `v` of the site, so an index type for a covering of one
site is an index type for a covering of the other only when those universes agree.

`sliceEquivalenceObjIso` and the identity `ringRestriction_over` are definitional: restriction
along `Over.post G` and restriction along `Over.forget` are both computed by reindexing
sections, and `Over.post G ⋙ Over.forget (G.obj U)` is `Over.forget U ⋙ G` on the nose.

## References

* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG)
* [Stacks Project, Tag 03CG](https://stacks.math.columbia.edu/tag/03CG)
* [Stacks Project, Tag 03CH](https://stacks.math.columbia.edu/tag/03CH)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Functor Opposite

universe w m u v

namespace Stacks.LocalizedDenseSubsite

/-- A family of objects of the slice site over `U` covering its terminal object generates a
covering sieve of `U`.  This is the converse of
`Stacks.SheafOfModules.coversTop_over_of_ofArrows_mem`. -/
theorem ofArrows_mem_of_coversTop_over {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {I : Type*} (U : C) (V : I → Over U)
    (h : (J.over U).CoversTop V) :
    Sieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (V i).hom) ∈ J U := by
  have h' := h (Over.mk (𝟙 U))
  rw [GrothendieckTopology.mem_over_iff] at h'
  refine J.superset_covering ?_ h'
  rintro Z g ⟨A, α, β, ⟨i, ⟨γ⟩⟩, rfl⟩
  refine (Sieve.mem_ofArrows_iff _ _ _).2 ⟨i, β ≫ γ.left, ?_⟩
  have hα : α.left = A.hom := by simpa using Over.w α
  have hγ : γ.left ≫ (V i).hom = A.hom := Over.w γ
  simp only [Over.forget_map, Category.assoc, hγ, hα]

/-- **The two ways of recording a covering of every object agree.**  A property holds on the
members of a family covering the terminal object of the slice site at every object exactly when
it holds on the sources of a family of arrows generating a covering sieve of every object.  The
clauses of Stacks 03DL use both forms, and the index type is unchanged. -/
theorem forall_exists_coversTop_iff_forall_exists_ofArrows {E : Type u} [Category.{v} E]
    (L : GrothendieckTopology E) (P : E → Prop) :
    (∀ V : E, ∃ (I : Type (max u v)) (Y : I → Over V),
        (L.over V).CoversTop Y ∧ ∀ i, P (Y i).left) ↔
      ∀ V : E, ∃ (I : Type (max u v)) (Y : I → E) (f : ∀ i, Y i ⟶ V),
        Sieve.ofArrows Y f ∈ L V ∧ ∀ i, P (Y i) := by
  constructor
  · intro h V
    obtain ⟨I, Y, hY, hP⟩ := h V
    exact ⟨I, fun i ↦ (Y i).left, fun i ↦ (Y i).hom,
      ofArrows_mem_of_coversTop_over L V Y hY, hP⟩
  · intro h V
    obtain ⟨I, Y, f, hf, hP⟩ := h V
    exact ⟨I, fun i ↦ Over.mk (f i),
      Stacks.SheafOfModules.coversTop_over_of_ofArrows_mem L V Y f hf, hP⟩

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (G : C ⥤ D) [G.IsDenseSubsite J K] (R : Sheaf K RingCat.{w})

/-- The localization of the dense subsite inclusion at an object, as an instance. -/
instance instIsDenseSubsiteOverPost (U : C) :
    (Over.post (X := U) G).IsDenseSubsite (J.over U) (K.over (G.obj U)) :=
  Stacks.Sites.overPost_isDenseSubsite G U

/-- The structure sheaf of the localization of the dense subsite at `U` is the localization at
`U` of the restricted structure sheaf: both reindex the sections of `R` along
`Over.forget U ⋙ G`. -/
theorem ringRestriction_over (U : C) :
    Stacks.DenseSubsiteModules.ringRestriction (J.over U) (K.over (G.obj U))
        (Over.post (X := U) G) (R.over (G.obj U)) =
      (Stacks.DenseSubsiteModules.ringRestriction J K G R).over U := rfl

variable [∀ (U : C) (X : (Over (G.obj U))ᵒᵖ),
    HasLimitsOfShape (StructuredArrow X (Over.post (X := U) G).op) AddCommGrpCat.{w}]

/-- **The localized Comparison Lemma for sheaves of modules.**  For `U` an object of a dense
subsite `C` of `D`, restriction of sections along `Over.post G : Over U ⥤ Over (G.obj U)` is an
equivalence from sheaves of modules over the localized structure sheaf of `D` to sheaves of
modules over the localized restricted structure sheaf of `C`.

This is the left vertical arrow of the square of localized ringed topoi of Stacks 03CH, at the
level of modules. -/
noncomputable def sliceEquivalence (U : C) :
    SheafOfModules.{w} (R.over (G.obj U)) ≌
      SheafOfModules.{w} ((Stacks.DenseSubsiteModules.ringRestriction J K G R).over U) :=
  Stacks.DenseSubsiteModules.moduleRestrictionEquivalence (J.over U) (K.over (G.obj U))
    (Over.post (X := U) G) (R.over (G.obj U))

/-- The localized Comparison Lemma carries the localized structure sheaf of `D` to the
localized restricted structure sheaf of `C`. -/
noncomputable def sliceEquivalenceUnitIso (U : C) :
    (sliceEquivalence J K G R U).functor.obj
        (SheafOfModules.unit (R.over (G.obj U))) ≅
      SheafOfModules.unit
        ((Stacks.DenseSubsiteModules.ringRestriction J K G R).over U) :=
  Iso.refl _

/-- The localized Comparison Lemma carries the restriction of a module to `Over (G.obj U)` to
the restriction to `Over U` of its restriction along `G`. -/
noncomputable def sliceEquivalenceObjIso (U : C) (F : SheafOfModules.{w} R) :
    (sliceEquivalence J K G R U).functor.obj (F.over (G.obj U)) ≅
      ((Stacks.DenseSubsiteModules.moduleRestriction J K G R).obj F).over U :=
  Iso.refl _

section SliceRestriction

variable [∀ V : D, HasWeakSheafify (K.over V) AddCommGrpCat.{w}]
  [∀ V : D, (K.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Restriction of modules from the slice of `D` at `V` to the slice of `C` at `U`, along an
arrow `a : G.obj U ⟶ V`: first restrict to the slice at `G.obj U`, then apply the localized
Comparison Lemma.  This is the comparison that a covering of `G.obj U` refined by images of
`G` calls for. -/
noncomputable def sliceRestriction (U : C) (V : D) (a : G.obj U ⟶ V) :
    SheafOfModules.{w} (R.over V) ⥤
      SheafOfModules.{w} ((Stacks.DenseSubsiteModules.ringRestriction J K G R).over U) :=
  SheafOfModules.overMap.{w} R a ⋙ (sliceEquivalence J K G R U).functor

/-- `sliceRestriction` preserves colimits: it is restriction of modules along `a`, which
preserves colimits, followed by an equivalence. -/
instance preservesColimits_sliceRestriction (U : C) (V : D) (a : G.obj U ⟶ V) :
    PreservesColimitsOfSize.{w, w} (sliceRestriction J K G R U V a) :=
  have := Stacks.SheafOfModules.overMap_preservesColimits.{u, v, w, w} R a
  inferInstanceAs (PreservesColimitsOfSize.{w, w}
    (SheafOfModules.overMap.{w} R a ⋙ (sliceEquivalence J K G R U).functor))

/-- `sliceRestriction` carries the localized structure sheaf of `D` to the localized restricted
structure sheaf of `C`. -/
noncomputable def sliceRestrictionUnitIso (U : C) (V : D) (a : G.obj U ⟶ V) :
    (sliceRestriction J K G R U V a).obj (SheafOfModules.unit (R.over V)) ≅
      SheafOfModules.unit
        ((Stacks.DenseSubsiteModules.ringRestriction J K G R).over U) :=
  (sliceEquivalence J K G R U).functor.mapIso
      (SheafOfModules.overMapUnitIso (R := R) a) ≪≫
    sliceEquivalenceUnitIso J K G R U

/-- `sliceRestriction` carries the restriction of a module to the slice of `D` at `V` to the
restriction to the slice of `C` at `U` of its restriction along `G`. -/
noncomputable def sliceRestrictionObjIso (U : C) (V : D) (a : G.obj U ⟶ V)
    (F : SheafOfModules.{w} R) :
    (sliceRestriction J K G R U V a).obj (F.over V) ≅
      ((Stacks.DenseSubsiteModules.moduleRestriction J K G R).obj F).over U :=
  (sliceEquivalence J K G R U).functor.mapIso
      ((SheafOfModules.overFunctorMap.{w} R a).app F) ≪≫
    sliceEquivalenceObjIso J K G R U F

end SliceRestriction

/-! ### The covering transport -/

omit [∀ (U : C) (X : (Over (G.obj U))ᵒᵖ),
  HasLimitsOfShape (StructuredArrow X (Over.post (X := U) G).op) AddCommGrpCat.{w}] in
/-- **The images of a family covering the terminal object of a dense subsite cover the terminal
object of the ambient site.**  An object of `D` is covered by images of `G` because `G` is cover
dense, and the given family covers each object of `C`, so its image covers each of those
images. -/
theorem coversTop_map {I : Type*} (X : I → C) (h : J.CoversTop X) :
    K.CoversTop (fun i ↦ G.obj (X i)) := by
  have _ := Functor.IsDenseSubsite.isCoverDense J K G
  intro V
  refine K.transitive (G.is_cover_of_isCoverDense K V) _ ?_
  rintro Y₀ fm ⟨⟨W, lift, mp, fac⟩⟩
  refine K.superset_covering ?_
    (K.pullback_stable lift ((G.functorPushforward_mem_iff J K).2 (h W)))
  rintro Y₁ c ⟨W₁, q, p, ⟨i, ⟨γ⟩⟩, -⟩
  exact ⟨i, ⟨p ≫ G.map γ⟩⟩

variable [G.IsCocontinuous J K]

omit [∀ (U : C) (X : (Over (G.obj U))ᵒᵖ),
  HasLimitsOfShape (StructuredArrow X (Over.post (X := U) G).op) AddCommGrpCat.{w}] in
/-- **The covering transport of Stacks 03DM.**  Let `Pᴰ` be a property of a sheaf of modules on
a slice of `D` and `Pᶜ` the corresponding property on a slice of `C`.  Suppose that `Pᴰ` for the
restriction of `F` to a slice of `D` gives `Pᶜ` for the restriction of the restriction of `F`
along `G`, for every arrow from the image of the object of `C` to the object of `D`, and that
conversely `Pᶜ` at `U` gives `Pᴰ` at `G.obj U`.  Then `F` has `Pᴰ` on a covering of every object
of `D` exactly when its restriction along `G` has `Pᶜ` on a covering of every object of `C`.

This is the geometric content of the first two paragraphs of the proof of Stacks 03DM.  In one
direction a covering of `G.obj U` is pulled back by cocontinuity of `G` and refined by the
factorizations of its members through the images of `G`; in the other the images of a covering
of each object of `C` are pushed forward, and an arbitrary object of `D` is covered by images of
`G` because `G` is cover dense. -/
theorem forall_exists_cover_iff {F : SheafOfModules.{w} R}
    (Pd : ∀ V : D, SheafOfModules.{w} (R.over V) → Prop)
    (Pc : ∀ W : C, SheafOfModules.{w}
      ((Stacks.DenseSubsiteModules.ringRestriction J K G R).over W) → Prop)
    (hfwd : ∀ (W : C) (V : D) (_ : G.obj W ⟶ V), Pd V (F.over V) →
      Pc W (((Stacks.DenseSubsiteModules.moduleRestriction J K G R).obj F).over W))
    (hbwd : ∀ W : C,
      Pc W (((Stacks.DenseSubsiteModules.moduleRestriction J K G R).obj F).over W) →
      Pd (G.obj W) (F.over (G.obj W))) :
    (∀ V : D, ∃ (I : Type (max u v)) (Y : I → D) (f : ∀ i, Y i ⟶ V),
        Sieve.ofArrows Y f ∈ K V ∧ ∀ i, Pd (Y i) (F.over (Y i))) ↔
      ∀ W : C, ∃ (I : Type (max u v)) (Z : I → C) (g : ∀ i, Z i ⟶ W),
        Sieve.ofArrows Z g ∈ J W ∧ ∀ i,
          Pc (Z i)
            (((Stacks.DenseSubsiteModules.moduleRestriction J K G R).obj F).over (Z i)) := by
  classical
  have _ := Functor.IsDenseSubsite.isCoverDense J K G
  constructor
  · intro h W
    obtain ⟨I, Y, f, hcover, hY⟩ := h (G.obj W)
    refine ⟨(Σ Z : C, (Z ⟶ W) × Σ i : I, (G.obj Z ⟶ Y i)), fun l ↦ l.1, fun l ↦ l.2.1, ?_,
      fun l ↦ hfwd l.1 (Y l.2.2.1) l.2.2.2 (hY l.2.2.1)⟩
    apply J.superset_covering _ (G.cover_lift J K hcover)
    intro Z g hg
    obtain ⟨i, a, -⟩ := (Sieve.mem_ofArrows_iff Y f (G.map g)).mp hg
    exact Sieve.ofArrows_mk
      (fun l : (Σ Z : C, (Z ⟶ W) × Σ i : I, (G.obj Z ⟶ Y i)) ↦ l.1)
      (fun l ↦ l.2.1) ⟨Z, g, i, a⟩
  · intro h V
    choose I Z g hcover hP using h
    refine ⟨(Σ W : C, (G.obj W ⟶ V) × I W), fun l ↦ G.obj (Z l.1 l.2.2),
      fun l ↦ G.map (g l.1 l.2.2) ≫ l.2.1, ?_, fun l ↦ hbwd _ (hP l.1 l.2.2)⟩
    refine K.transitive (G.is_cover_of_isCoverDense K V) _ ?_
    rintro Y₀ fm ⟨⟨W, lift, mp, fac⟩⟩
    refine K.superset_covering ?_
      (K.pullback_stable lift ((G.functorPushforward_mem_iff J K).2 (hcover W)))
    rintro Y₁ c ⟨W₁, q, p, hq, hcomp⟩
    obtain ⟨j, r, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hq
    refine (Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨W, mp, j⟩, p ≫ G.map r, ?_⟩
    have hc : c ≫ lift = p ≫ G.map (r ≫ g W j) := hcomp
    have hcf : c ≫ fm = p ≫ G.map (r ≫ g W j) ≫ mp := by
      rw [← fac, ← Category.assoc, hc, Category.assoc]
    rw [hcf]
    simp

section Global

variable [∀ X : Dᵒᵖ, HasLimitsOfShape (StructuredArrow X G.op) AddCommGrpCat.{w}]

/-- The Comparison Lemma for modules, read as an equivalence, is the restriction functor: the
two agree on objects. -/
noncomputable def moduleRestrictionEquivalenceObjIso (F : SheafOfModules.{w} R) :
    (Stacks.DenseSubsiteModules.moduleRestrictionEquivalence J K G R).functor.obj F ≅
      (Stacks.DenseSubsiteModules.moduleRestriction J K G R).obj F :=
  Iso.refl _

end Global

end Stacks.LocalizedDenseSubsite

namespace Stacks.DenseSubsiteModules

/-! ### The sectionwise finite-type condition on a dense subsite -/

section FiniteType

variable {E : Type u} [Category.{v} E] {E' : Type u} [Category.{v} E']
  (L : GrothendieckTopology E) (L' : GrothendieckTopology E') (H : E ⥤ E')
  {A : E'ᵒᵖ ⥤ RingCat.{w}} (M : PresheafOfModules.{m} A)

/-- Restricting a section twice is restricting it along any arrow equal to the composite. -/
private theorem restrict_restrict {X Y Z : E'} (p : Y ⟶ X) (q : Z ⟶ Y) {r : Z ⟶ X}
    (h : q ≫ p = r) (x : M.obj (op X)) :
    M.restrictₛₗ q.op (M.restrictₛₗ p.op x) = M.restrictₛₗ r.op x := by
  show M.map q.op (M.map p.op x) = M.map r.op x
  exact (M.map_comp_apply p.op q.op x).symm.trans (M.congr_map_apply (by rw [← h, op_comp]) x)

/-- **A generating family stays generating after restriction along an arrow.**  Every section
over an object of the site is locally a linear combination of the restrictions of the family, so
the same is true of the restricted family after composing with the arrow. -/
theorem generates_restrict {U U' : E'} (a : U' ⟶ U) {n : ℕ} (s : Fin n → M.obj (op U))
    (hs : PresheafOfModules.Generates L' M s) :
    PresheafOfModules.Generates L' M (fun i ↦ M.restrictₛₗ a.op (s i)) := by
  intro V f t
  obtain ⟨T, hT, hTgen⟩ := hs V (f ≫ a) t
  refine ⟨T, hT, fun W g hg ↦ ?_⟩
  obtain ⟨b, hb⟩ := hTgen W g hg
  refine ⟨b, ?_⟩
  simpa only [restrict_restrict M a (g ≫ f) (Category.assoc g f a)] using hb

/-- **A finite generating family restricts to the subsite.**  If a finite family of sections
over the image of an object of `C` generates a presheaf of modules on `(D, K)`, then it
generates the restriction of sections along `H` on `(C, J)`.

Cocontinuity of `H` is what is needed and all that is needed: a covering of the image of an
object on which a section is a linear combination of the family is pulled back to a covering of
the object itself. -/
theorem generates_pushforward₀ [H.IsCocontinuous L L'] {U : E} {n : ℕ}
    (s : Fin n → M.obj (op (H.obj U)))
    (hs : PresheafOfModules.Generates L' M s) :
    PresheafOfModules.Generates L ((PresheafOfModules.pushforward₀ H A).obj M)
      (fun i ↦ (s i : ((PresheafOfModules.pushforward₀ H A).obj M).obj (op U))) := by
  intro V f t
  obtain ⟨T, hT, hTgen⟩ := hs (H.obj V) (H.map f) t
  refine ⟨Sieve.functorPullback H T, H.cover_lift L L' hT, fun W g hg ↦ ?_⟩
  obtain ⟨b, hb⟩ := hTgen (H.obj W) (H.map g) hg
  refine ⟨b, ?_⟩
  have hc (i : Fin n) : M.restrictₛₗ (H.map (g ≫ f)).op (s i) =
      M.restrictₛₗ (H.map g ≫ H.map f).op (s i) := by
    show M.map (H.map (g ≫ f)).op (s i) = M.map (H.map g ≫ H.map f).op (s i)
    exact M.congr_map_apply (by rw [H.map_comp]) (s i)
  have key : (∑ i, b i • M.restrictₛₗ (H.map (g ≫ f)).op (s i)) =
      M.restrictₛₗ (H.map g).op t := by
    simpa only [hc] using hb
  exact key

/-- **A finite family generating the restriction to a dense subsite generates.**  If a finite
family of sections over the image of an object of `C` generates the restriction of sections of a
presheaf of modules along `H`, then it generates the presheaf itself.

The sections over an arbitrary object `V` of `D` on which a given section is a linear
combination of the family form a sieve, so it suffices to cover `V`; `V` is covered by the
images of `H` because `H` is cover dense, and on the image `H.obj U₁` of an object of `C` the
arrow to `H.obj U` at hand is, after a further covering, the image of an arrow of `C`, because
`H` is locally full.  On that further covering the hypothesis applies, after pushing its own
covering forward, which is a covering of `D` because `H` is a dense subsite.

Local fullness is all that is asked, not fullness: a special cocontinuous functor of Stacks 03CG
is a cocontinuous dense subsite inclusion and nothing more, and the functors Stacks 03CR produces
need not be full or faithful. -/
theorem generates_of_pushforward₀ [H.IsDenseSubsite L L']
    {U : E} {n : ℕ} (s : Fin n → M.obj (op (H.obj U)))
    (hs : PresheafOfModules.Generates L ((PresheafOfModules.pushforward₀ H A).obj M)
      (fun i ↦ (s i : ((PresheafOfModules.pushforward₀ H A).obj M).obj (op U)))) :
    PresheafOfModules.Generates L' M s := by
  have _ := Functor.IsDenseSubsite.isCoverDense L L' H
  have _ := Functor.IsDenseSubsite.isLocallyFull L L' H
  intro V f t
  let S : Sieve V :=
    { arrows := fun Y c ↦ ∃ b : Fin n → A.obj (op Y),
        ∑ i, b i • M.restrictₛₗ (c ≫ f).op (s i) = M.restrictₛₗ c.op t
      downward_closed := by
        rintro Y Z c ⟨b, hb⟩ g
        have h2 := congrArg (M.restrictₛₗ g.op) hb
        simp only [_root_.map_sum, map_smulₛₗ] at h2
        simp only [restrict_restrict M (c ≫ f) g (Category.assoc g c f).symm,
          restrict_restrict M c g rfl] at h2
        exact ⟨_, h2⟩ }
  refine ⟨S, ?_, fun _ _ h ↦ h⟩
  refine L'.transitive (H.is_cover_of_isCoverDense L' V) _ ?_
  rintro Y₀ fm ⟨⟨U₁, lift, mp, fac⟩⟩
  refine L'.transitive (L'.pullback_stable lift
    (H.functorPushforward_imageSieve_mem L' (mp ≫ f))) _ ?_
  rintro Y₁ c₀ ⟨U₂, r₀, p₀, ⟨h₁, hh₁⟩, hc₀⟩
  obtain ⟨T, hT, hTgen⟩ := hs U₂ h₁ (M.restrictₛₗ (H.map r₀ ≫ mp).op t)
  refine L'.superset_covering ?_ (L'.pullback_stable p₀
    ((H.functorPushforward_mem_iff L L').2 hT))
  rintro Y₂ c ⟨Z, r, p, hr, hcp⟩
  obtain ⟨b, hb⟩ := hTgen Z r hr
  have hb' : (∑ i, b i • M.restrictₛₗ (H.map (r ≫ h₁)).op (s i)) =
      M.restrictₛₗ (H.map r).op (M.restrictₛₗ (H.map r₀ ≫ mp).op t) := hb
  have key2 : p ≫ H.map r ≫ H.map r₀ ≫ mp = (c ≫ c₀) ≫ fm := by
    rw [← fac, ← Category.assoc p, ← hcp, Category.assoc, ← Category.assoc p₀, ← hc₀]
    simp
  have hS : S.arrows (H.map r ≫ H.map r₀ ≫ mp) := by
    refine ⟨b, ?_⟩
    rw [← restrict_restrict M (H.map r₀ ≫ mp) (H.map r) rfl t,
      show (H.map r ≫ H.map r₀ ≫ mp) ≫ f = H.map (r ≫ h₁) by simp [hh₁]]
    exact hb'
  change S.arrows ((c ≫ c₀) ≫ fm)
  rw [← key2]
  exact S.downward_closed hS p

/-- **The sectionwise finite-type condition restricts to a subsite along a cocontinuous
functor.**  If a presheaf of modules on `(D, K)` is of finite type, then so is its restriction
of sections along `H` on `(C, J)`.

The objects of `C` admitting an arrow from their image to a member of the given covering family
cover `C`, by cocontinuity, and on each of them the generating family of that member restricts
to a generating family by `generates_restrict` and `generates_pushforward₀`. -/
theorem isFiniteType_pushforward₀ [H.IsCocontinuous L L']
    (hM : PresheafOfModules.IsFiniteType L' M) :
    PresheafOfModules.IsFiniteType L ((PresheafOfModules.pushforward₀ H A).obj M) := by
  classical
  obtain ⟨I, X, hX, hgen⟩ := hM.exists_generators
  let T : Set E := {U : E | ∃ i, Nonempty (H.obj U ⟶ X i)}
  refine ⟨T, fun t ↦ t.1, ?_, ?_⟩
  · intro Z
    refine L.superset_covering ?_ (H.cover_lift L L' (hX (H.obj Z)))
    intro Y g hg
    rw [Sieve.mem_ofObjects_iff]
    obtain ⟨i, ⟨a⟩⟩ := (Sieve.mem_ofObjects_iff X (H.map g)).1 hg
    exact ⟨⟨Y, i, ⟨a⟩⟩, ⟨𝟙 Y⟩⟩
  · rintro ⟨U, i, ⟨a⟩⟩
    obtain ⟨n, s, hs⟩ := hgen i
    exact ⟨n, fun j ↦ M.restrictₛₗ a.op (s j),
      generates_pushforward₀ L L' H M _ (generates_restrict L' M a s hs)⟩

/-- **The sectionwise finite-type condition descends from a dense subsite.**  If the restriction
of sections of a presheaf of modules along `H` is of finite type on `(C, J)`, then the presheaf
itself is of finite type on `(D, K)`.

The images of the given covering family of `C` cover `D` by
`Stacks.LocalizedDenseSubsite.coversTop_map`, and on each image the generating family generates
by `generates_of_pushforward₀`. -/
theorem isFiniteType_of_pushforward₀ [H.IsDenseSubsite L L']
    (hM : PresheafOfModules.IsFiniteType L ((PresheafOfModules.pushforward₀ H A).obj M)) :
    PresheafOfModules.IsFiniteType L' M := by
  classical
  obtain ⟨I, X, hX, hgen⟩ := hM.exists_generators
  refine ⟨Set.range (fun i ↦ H.obj (X i)), fun t ↦ t.1, ?_, ?_⟩
  · intro Z
    refine L'.superset_covering ?_
      (Stacks.LocalizedDenseSubsite.coversTop_map L L' H X hX Z)
    intro Y g hg
    rw [Sieve.mem_ofObjects_iff] at hg ⊢
    obtain ⟨i, ⟨a⟩⟩ := hg
    exact ⟨⟨H.obj (X i), ⟨i, rfl⟩⟩, ⟨a⟩⟩
  · rintro ⟨V, i, rfl⟩
    obtain ⟨n, s, hs⟩ := hgen i
    exact ⟨n, fun j ↦ (s j : M.obj (op (H.obj (X i)))),
      generates_of_pushforward₀ L L' H M _ hs⟩

/-- **The sectionwise finite-type condition is intrinsic.**  A presheaf of modules on `(D, K)` is
of finite type if and only if its restriction of sections along a cocontinuous dense subsite
inclusion `H` is of finite type on `(C, J)`. -/
theorem isFiniteType_pushforward₀_iff [H.IsDenseSubsite L L']
    [H.IsCocontinuous L L'] :
    PresheafOfModules.IsFiniteType L' M ↔
      PresheafOfModules.IsFiniteType L ((PresheafOfModules.pushforward₀ H A).obj M) :=
  ⟨isFiniteType_pushforward₀ L L' H M, isFiniteType_of_pushforward₀ L L' H M⟩

end FiniteType

end Stacks.DenseSubsiteModules

end
