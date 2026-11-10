module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.UnderlyingSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.MonomorphismPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Points of an inverse limit of decent algebraic spaces

Let `D` be a directed inverse system of decent algebraic spaces over a scheme `S`, indexed by
a category small enough for the chosen big fppf site. A family of points of the stages which
is compatible with the transition morphisms is induced by exactly one point of `limit D`; that
is, `|lim D| = lim |D|` as sets.

## Main results

* `AlgebraicGeometry.Space.existsUnique_point_limit` is the unique-lift statement: a compatible
  family of points of the stages comes from a unique point of the limit.
* `AlgebraicGeometry.Space.existsUnique_point_limit_of_monoBoundedBy`: the same conclusion
  from the cofinality-free cardinality hypothesis, for a system bounded by one object of the
  site.
* `AlgebraicGeometry.Space.subsingleton_points_yoneda`: a presheaf represented by an object of
  the site whose underlying scheme has at most one point has at most one point.

## Implementation notes

The unique-lift formulation says exactly that the canonical map from the points of the limit
to the inverse limit of the point sets is a bijection, while keeping the compatibility with
each limit projection explicit.

Decency enters through condition (4) of Stacks 03JV: every point `x i` of a stage has a
field-valued representative `p i` whose associated morphism
`AlgebraicGeometry.Space.fieldMorphism` is a monomorphism. Such a representative is terminal
in its equivalence class — this is Stacks 0H2X,
`AlgebraicGeometry.Space.FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono` — so
compatibility of the family turns the field spectra into an inverse system `E` of objects of
the site, with a natural transformation to `D`. That system is affine with spectra of fields
as stages, hence has a limit in the site whose underlying scheme has exactly one point: at
most one because passing to underlying sets preserves a cofiltered limit with affine
transitions (Stacks 0CUE), and at least one by Stacks 01Z2. The unique point of the limit is
then the image of the unique point of `limit E`, and a second point of `limit D` with the same
images factors through `limit E` by the universal property, hence agrees with it.

The affineness of the transition morphisms of `D` and the bound on its morphism types are
retained from the source statement but are not needed: the inverse system `E` of field spectra
produced from decency is affine for free, and only its index category has to be small for the
site. They are kept so that the statement is the one of the source.

## References

* [Stacks Project, Tag 0CUJ](https://stacks.math.columbia.edu/tag/0CUJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A presheaf represented by an object of the big fppf site of `S` whose underlying scheme
has at most one point has at most one point: its points inject into the points of the
representing scheme. -/
theorem subsingleton_points_yoneda (U : BigFppfOver B S hS)
    [Subsingleton ((BigFppfOver.toScheme B S hS).obj U)] :
    Subsingleton (points B S hS (yoneda.obj U)) :=
  (injective_pointsToScheme B S hS U).subsingleton

section InverseLimit

variable {I : Type u} [Category.{u} I] [IsCofiltered I]

/-- Two morphisms of the site agreeing after composing with a monomorphism out of a represented
presheaf are equal. -/
private theorem eq_of_yoneda_map_comp_eq {X Y : BigFppfOver B S hS}
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (β : yoneda.obj Y ⟶ P) [Mono β] {f g : X ⟶ Y}
    (h : yoneda.map f ≫ β = yoneda.map g ≫ β) : f = g :=
  yoneda.map_injective ((cancel_mono β).1 h)

/-- A factorization of the pushforward of a field-valued point through a morphism of presheaves
gives a factorization of the point composed with that morphism. -/
private theorem exists_comp_eq_of_factor_map {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : F ⟶ G)
    (q : FieldValuedPoint B S hS F) {W : BigFppfOver B S hS} (β : yoneda.obj W ⟶ G)
    (h : ∃ g : q.siteObject B S hS F ⟶ W,
      yoneda.map g ≫ β = yonedaEquiv.symm (FieldValuedPoint.map B S hS F φ q).value) :
    ∃ g : q.siteObject B S hS F ⟶ W, yoneda.map g ≫ β = yonedaEquiv.symm q.value ≫ φ :=
  h.imp fun _ hg ↦ hg.trans (yonedaEquiv_symm_naturality_right _ φ q.value).symm

/-- The unique-lift statement for an inverse system `D` of presheaves presented, stage by
stage, by a monomorphism from a represented presheaf with a one-point affine underlying
scheme, given the limit of the presenting system in the site and its preservation by the
underlying scheme functor. -/
private theorem existsUnique_point_limit_of_fieldDiagram_of_hasLimit
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (E : I ⥤ BigFppfOver B S hS)
    (α : E ⋙ yoneda ⟶ D) (hlim : HasLimit E)
    (hpres : PreservesLimit E (BigFppfOver.toScheme B S hS))
    (hAffine : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
    (hOne : ∀ i, Subsingleton ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
    (hNonempty : ∀ i, Nonempty ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
    (hMono : ∀ i, Mono (α.app i))
    (x : ∀ i, points B S hS (D.obj i))
    (hImage : ∀ (i : I) (z : points B S hS (yoneda.obj (E.obj i))),
      pointsMap B S hS (yoneda.obj (E.obj i)) (α.app i) z = x i)
    (hFactor : ∀ (i : I) (q : FieldValuedPoint B S hS (D.obj i)),
      q.class B S hS (D.obj i) = x i →
        ∃ f : q.siteObject B S hS (D.obj i) ⟶ E.obj i,
          yoneda.map f ≫ α.app i = yonedaEquiv.symm q.value) :
    ∃! y : points B S hS (limit D),
      ∀ i, pointsMap B S hS (limit D) (limit.π D i) y = x i := by
  classical
  have : HasLimit E := hlim
  have : PreservesLimit E (BigFppfOver.toScheme B S hS) := hpres
  have hc : IsLimit (limit.cone E) := limit.isLimit E
  have hcQ : IsLimit ((BigFppfOver.toScheme B S hS).mapCone (limit.cone E)) :=
    isLimitOfPreserves (BigFppfOver.toScheme B S hS) hc
  -- The underlying scheme of `limit E` has exactly one point.
  have : ∀ i, IsAffine ((E ⋙ BigFppfOver.toScheme B S hS).obj i) := hAffine
  have : ∀ i, Nonempty ((E ⋙ BigFppfOver.toScheme B S hS).obj i) := hNonempty
  have : ∀ i, CompactSpace ((E ⋙ BigFppfOver.toScheme B S hS).obj i) := fun i ↦ inferInstance
  have : ∀ {i j : I} (f : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((E ⋙ BigFppfOver.toScheme B S hS).map f) :=
    fun _ ↦ inferInstance
  have : Subsingleton ((E ⋙ BigFppfOver.toScheme B S hS) ⋙ Scheme.forget).sections :=
    ⟨fun s t ↦ Subtype.ext (funext fun i ↦ (hOne i).elim _ _)⟩
  have : PreservesLimit (E ⋙ BigFppfOver.toScheme B S hS) Scheme.forget :=
    preservesLimit_forget_of_isCofiltered_of_isAffineHom _
  have : Subsingleton ((BigFppfOver.toScheme B S hS).obj (limit E)) :=
    (Types.isLimitEquivSections (isLimitOfPreserves Scheme.forget hcQ)).injective.subsingleton
  have hLimNonempty : Nonempty ((BigFppfOver.toScheme B S hS).obj (limit E)) :=
    Scheme.nonempty_of_isLimit (E ⋙ BigFppfOver.toScheme B S hS) _ hcQ
  have hPointsOne : Subsingleton (points B S hS (yoneda.obj (limit E))) :=
    subsingleton_points_yoneda B S hS (limit E)
  -- The unique point of `limit E`, and the morphism it is pushed forward along.
  let z : points B S hS (yoneda.obj (limit E)) :=
    (schemePointRepresentative B S hS (limit E) hLimNonempty.some).class B S hS
      (yoneda.obj (limit E))
  let m : yoneda.obj (limit E) ⟶ limit D :=
    limit.lift D ((Cone.postcompose α).obj (yoneda.mapCone (limit.cone E)))
  have hm (i : I) :
      m ≫ limit.π D i = yoneda.map ((limit.cone E).π.app i) ≫ α.app i :=
    limit.lift_π _ _
  refine ⟨pointsMap B S hS (yoneda.obj (limit E)) m z, fun i ↦ ?_, ?_⟩
  · rw [← pointsMap_comp_apply, hm i, pointsMap_comp_apply]
    exact hImage i _
  · intro y hy
    induction y using Quot.inductionOn with
    | h q =>
      have hstage (i : I) : ∃ g : q.siteObject B S hS (limit D) ⟶ E.obj i,
          yoneda.map g ≫ α.app i = yonedaEquiv.symm q.value ≫ limit.π D i := by
        exact exists_comp_eq_of_factor_map B S hS _ q _
          (hFactor i (FieldValuedPoint.map B S hS (limit D) (limit.π D i) q) (hy i))
      choose f hf' using hstage
      -- The point `q` of the limit factors through `limit E`.
      let d : Cone E :=
        { pt := q.siteObject B S hS (limit D)
          π :=
            { app := f
              naturality := fun i j g ↦ by
                have hα : yoneda.map (E.map g) ≫ α.app j = α.app i ≫ D.map g :=
                  α.naturality g
                simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
                have := hMono j
                apply eq_of_yoneda_map_comp_eq B S hS (α.app j)
                rw [yoneda.map_comp, Category.assoc, hα, ← Category.assoc, hf' i,
                  Category.assoc, limit.w, hf' j] } }
      have ha : yoneda.map (hc.lift d) ≫ m = yonedaEquiv.symm q.value := by
        refine limit.hom_ext fun i ↦ ?_
        rw [Category.assoc, hm i, ← Category.assoc, ← yoneda.map_comp, hc.fac]
        exact hf' i
      have hval : m.app (Opposite.op (q.siteObject B S hS (limit D))) (hc.lift d) = q.value := by
        have hav := congrArg yonedaEquiv ha
        rwa [yonedaEquiv_comp, yonedaEquiv_yoneda_map, Equiv.apply_symm_apply] at hav
      let w : FieldValuedPoint B S hS (yoneda.obj (limit E)) :=
        ⟨q.carrier, q.contained, q.toBase, hc.lift d⟩
      have hw : pointsMap B S hS (yoneda.obj (limit E)) m
          (w.class B S hS (yoneda.obj (limit E))) = q.class B S hS (limit D) := by
        rw [pointsMap_class]
        congr 1
        change FieldValuedPoint.mk q.carrier q.contained q.toBase
          (m.app (Opposite.op (q.siteObject B S hS (limit D))) (hc.lift d)) = q
        rw [hval]
      exact hw.symm.trans
        (congrArg (pointsMap B S hS (yoneda.obj (limit E)) m) (hPointsOne.elim _ _))

/-- The unique-lift statement for an inverse system `D` of presheaves presented, stage by
stage, by a monomorphism from a represented presheaf with a one-point affine underlying
scheme. -/
private theorem existsUnique_point_limit_of_fieldDiagram
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (E : I ⥤ BigFppfOver B S hS)
    (α : E ⋙ yoneda ⟶ D) (hSize : #I < B.cutoff.ord.cof)
    (hAffine : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
    (hOne : ∀ i, Subsingleton ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
    (hNonempty : ∀ i, Nonempty ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
    (hMono : ∀ i, Mono (α.app i))
    (x : ∀ i, points B S hS (D.obj i))
    (hImage : ∀ (i : I) (z : points B S hS (yoneda.obj (E.obj i))),
      pointsMap B S hS (yoneda.obj (E.obj i)) (α.app i) z = x i)
    (hFactor : ∀ (i : I) (q : FieldValuedPoint B S hS (D.obj i)),
      q.class B S hS (D.obj i) = x i →
        ∃ f : q.siteObject B S hS (D.obj i) ⟶ E.obj i,
          yoneda.map f ≫ α.app i = yonedaEquiv.symm q.value) :
    ∃! y : points B S hS (limit D),
      ∀ i, pointsMap B S hS (limit D) (limit.π D i) y = x i :=
  existsUnique_point_limit_of_fieldDiagram_of_hasLimit B S hS D E α
    (BigFppfOver.hasLimit_of_isAffine E hAffine hSize)
    (BigFppfOver.preservesLimit_toScheme E hAffine hSize) hAffine hOne hNonempty hMono x hImage
    hFactor

/-- The common core of the two forms below: a compatible family of points of decent algebraic
spaces is induced by exactly one point of the limit, provided every system `E` of affine
objects of the site with monomorphisms `α` to the stages has a limit in the site, preserved by
the underlying scheme functor. -/
private theorem existsUnique_point_limit_of_siteLimit
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hDecent : ∀ i, IsDecentSpace B S hS (D.obj i))
    (x : ∀ i, points B S hS (D.obj i))
    (hx : ∀ {i j : I} (f : i ⟶ j), pointsMap B S hS (D.obj i) (D.map f) (x i) = x j)
    (hsite : ∀ (E : I ⥤ BigFppfOver B S hS) (α : E ⋙ yoneda ⟶ D),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i))) →
      (∀ i, Mono (α.app i)) →
      HasLimit E ∧ PreservesLimit E (BigFppfOver.toScheme B S hS)) :
    ∃! y : points B S hS (limit D),
      ∀ i, pointsMap B S hS (limit D) (limit.π D i) y = x i := by
  classical
  -- Decency presents each `x i` by a monomorphism from the spectrum of a field.
  choose p hp hmono _hqc using fun i ↦ hDecent i (x i)
  let A : I → BigFppfOver B S hS := fun i ↦ (p i).siteObject B S hS (D.obj i)
  let a : ∀ i, yoneda.obj (A i) ⟶ D.obj i := fun i ↦ fieldMorphism B S hS (D.obj i) (p i)
  have hMonoA : ∀ i, Mono (a i) := hmono
  -- Every representative of `x i` factors through the monomorphic one, by Stacks 0H2X.
  have hFactor : ∀ (i : I) (q : FieldValuedPoint B S hS (D.obj i)),
      q.class B S hS (D.obj i) = x i →
        ∃ g : q.siteObject B S hS (D.obj i) ⟶ A i,
          yoneda.map g ≫ a i = yonedaEquiv.symm q.value := by
    intro i q hq
    have := hmono i
    obtain ⟨g, hg, -⟩ := FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono
      B S hS (D.obj i) (hD i) (p i) q ((hp i).trans hq.symm)
    exact ⟨g, (yonedaEquiv_symm_naturality_left g (D.obj i) (p i).value).trans
      (congrArg yonedaEquiv.symm hg)⟩
  -- Hence the field spectra form an inverse system over `D`.
  have hMap : ∀ {i j : I} (f : i ⟶ j),
      ∃ g : A i ⟶ A j, yoneda.map g ≫ a j = a i ≫ D.map f := by
    intro i j f
    have hq : (FieldValuedPoint.map B S hS (D.obj i) (D.map f) (p i)).class B S hS (D.obj j) =
        x j := by
      rw [← pointsMap_class, hp i]
      exact hx f
    exact exists_comp_eq_of_factor_map B S hS (D.map f) (p i) _ (hFactor j _ hq)
  choose m hm using @hMap
  let E : I ⥤ BigFppfOver B S hS :=
    { obj := A
      map := m
      map_id := fun i ↦ by
        apply eq_of_yoneda_map_comp_eq B S hS (a i)
        rw [hm, D.map_id, Category.comp_id, yoneda.map_id, Category.id_comp]
      map_comp := fun f g ↦ by
        apply eq_of_yoneda_map_comp_eq B S hS (a _)
        rw [hm, yoneda.map_comp, Category.assoc, hm, ← Category.assoc, hm, Category.assoc,
          D.map_comp] }
  let α : E ⋙ yoneda ⟶ D := { app := a, naturality := fun i j f ↦ hm f }
  have hAffine : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i)) := fun i ↦
    inferInstanceAs (IsAffine (Spec (.of (p i).carrier)))
  have hOne : ∀ i, Subsingleton ((BigFppfOver.toScheme B S hS).obj (E.obj i)) := fun i ↦
    inferInstanceAs (Subsingleton (Spec (.of (p i).carrier)))
  have hNonempty : ∀ i, Nonempty ((BigFppfOver.toScheme B S hS).obj (E.obj i)) := fun i ↦
    ⟨IsLocalRing.closedPoint (p i).carrier⟩
  obtain ⟨hlim, hpres⟩ := hsite E α hAffine hMonoA
  refine existsUnique_point_limit_of_fieldDiagram_of_hasLimit B S hS D E α hlim hpres hAffine
    hOne hNonempty hMonoA x (fun i z ↦ ?_) hFactor
  have := hOne i
  have : Subsingleton (points B S hS (yoneda.obj (E.obj i))) :=
    subsingleton_points_yoneda B S hS (E.obj i)
  rw [Subsingleton.elim z
    (((p i).tautologicalPoint B S hS (D.obj i)).class B S hS (yoneda.obj (A i)))]
  exact (pointsMap_fieldMorphism_tautologicalPoint B S hS (D.obj i) (p i)).trans (hp i)

/-- **Stacks 0CUJ.** Let `D` be a directed inverse system of decent algebraic spaces over `S`
with affine transition morphisms, indexed by a category whose object type and whose morphism
types are smaller than the cofinality of the site's size cutoff. Then a family of points of
the stages which is compatible with the transition morphisms is induced by exactly one point
of `limit D`; that is, `|lim D| = lim |D|` as sets. -/
@[stacks 0CUJ]
theorem existsUnique_point_limit (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hSize : #I < B.cutoff.ord.cof)
    (_hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (_hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hDecent : ∀ i, IsDecentSpace B S hS (D.obj i))
    (x : ∀ i, points B S hS (D.obj i))
    (hx : ∀ {i j : I} (f : i ⟶ j), pointsMap B S hS (D.obj i) (D.map f) (x i) = x j) :
    ∃! y : points B S hS (limit D),
      ∀ i, pointsMap B S hS (limit D) (limit.π D i) y = x i :=
  existsUnique_point_limit_of_siteLimit B S hS D hD hDecent x hx fun E _ hAffine _ ↦
    ⟨BigFppfOver.hasLimit_of_isAffine E hAffine hSize,
      BigFppfOver.preservesLimit_toScheme E hAffine hSize⟩

/-- **`|lim D| = lim |D|` with no cofinality hypothesis.** The index category is only asked
to have fewer objects than the site's size cutoff, in exchange for the system being bounded
by one object `Z` of the site in the sense of
`AlgebraicGeometry.Space.MonoBoundedBy`. The `@[stacks 0CUJ]` tag stays on the form carrying
the source's own hypothesis. -/
theorem existsUnique_point_limit_of_monoBoundedBy (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hSize : #I < B.cutoff) {Z : BigFppfOver B S hS} (hZ : MonoBoundedBy B S hS D Z)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hDecent : ∀ i, IsDecentSpace B S hS (D.obj i))
    (x : ∀ i, points B S hS (D.obj i))
    (hx : ∀ {i j : I} (f : i ⟶ j), pointsMap B S hS (D.obj i) (D.map f) (x i) = x j) :
    ∃! y : points B S hS (limit D),
      ∀ i, pointsMap B S hS (limit D) (limit.π D i) y = x i :=
  existsUnique_point_limit_of_siteLimit B S hS D hD hDecent x hx fun E α hAffine hMono ↦
    have hstage : ∀ i, ((BigFppfOver.toScheme B S hS).obj (E.obj i)).size ≤
        monoSizeBound B S hS Z := fun i ↦
      size_le_monoSizeBound_of_monoBoundedBy B S hS hZ (α.app i) (hMono i)
    ⟨BigFppfOver.hasLimit_of_isAffine_of_size_le E hAffine hSize
        (monoSizeBound_lt_cutoff B S hS Z) hstage,
      BigFppfOver.preservesLimit_toScheme_of_size_le E hAffine hSize
        (monoSizeBound_lt_cutoff B S hS Z) hstage⟩

end InverseLimit

end AlgebraicGeometry.Space

end
