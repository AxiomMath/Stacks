module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenFiltrationSeparatedNeighbourhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtFinitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.AffineChartModel
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjects

/-!
# Étale descent of an open locus cut out at the points with values in a field

Let `Y` be an algebraic space over a scheme `S` and let `P` be a property of the test schemes
`T ⟶ Y` whose underlying scheme is the spectrum of a field.  In the proof of Stacks 0DLC,
part (1), an open `W ⊆ Y` is characterized by "`y ∈ |W|` if and only if `P(y)`" for the points
`y : Spec(k) ⟶ Y` with values in a field, and its openness is obtained étale locally: on every
affine étale chart `V ⟶ Y` the corresponding locus is open, "hence `W` is open".  This file
carries that step out.

Two inputs make it work, exactly as in the source.  First, `P` depends only on the point of
`|Y|` underlying `y`: it does not change under a field extension `Spec(k') ⟶ Spec(k)` over `Y`
(in the source this is the observation drawn from Stacks 0AA7).  Second, on every affine étale
chart `V ⟶ Y` the set of points of `|V|` whose field-valued representatives satisfy `P` is open.
Then the set `W` of points of `|Y|` all of whose field-valued representatives satisfy `P` is the
union of the images of those opens, which are open because an étale morphism is open on points
(Stacks 03BX), and every point of `|Y|` lies in the image of an affine étale chart.

## Main definitions

* `AlgebraicGeometry.Space.schemesOverPoints`: the set of points of `|Y|` a test scheme passes
  through.
* `AlgebraicGeometry.Space.FieldValuedPoint.toSchemesOver`: a field-valued point of `Y`, as a
  test scheme over `Y`.

## Main results

* `AlgebraicGeometry.Space.exists_isOpen_forall_isFieldObject_iff`: the descent of the locus, at
  the level of the point set `|Y|`.
* `AlgebraicGeometry.Space.exists_openSubspace_forall_isFieldObject_iff`: the same, as an open
  subspace of `Y`: there is an open subspace `W` of `Y` such that a test scheme `y` over `Y`
  with values in a field factors through `W` if and only if `P(y)`.
* `AlgebraicGeometry.Space.exists_common_extension_of_mem`: two test schemes over `Y` with values
  in fields passing through the same point of `|Y|` have a common field extension over `Y`
  (Stacks 03BU).

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

section Points

variable {Y : AlgebraicSpaces B S hS}

/-- The structure morphism of a test scheme `T ⟶ Y`, as a morphism of presheaves out of the
presheaf represented by `T`. -/
def schemesOverHom (T : SchemesOver Y) : yoneda.obj T.left ⟶ Y.1 :=
  T.hom.hom

/-- The set of points of `|Y|` through which a test scheme `T ⟶ Y` passes: the image of `|T|`. -/
abbrev schemesOverPoints (T : SchemesOver Y) : Set (points B S hS Y.1) :=
  Set.range (pointsMap B S hS (yoneda.obj T.left) (schemesOverHom T))

/-- A test scheme lies in the subspace cut out by a set of points exactly when the points it
passes through lie in that set. -/
theorem testPoint_mem_openSubspaceOfPoints_iff (W : Set (points B S hS Y.1))
    (T : SchemesOver Y) :
    testPoint T ∈ (openSubspaceOfPoints B S hS Y.1 W).obj (op T.left) ↔
      schemesOverPoints T ⊆ W := by
  rw [mem_openSubspaceOfPoints_iff, yonedaEquiv_symm_testPoint]
  exact Iff.rfl

/-- The represented presheaf of an object of the site whose underlying scheme is the spectrum
of a field has exactly one point. -/
theorem subsingleton_points_yoneda_of_isFieldObject {U : BigFppfOver B S hS}
    (hU : Stack.IsFieldObject B S hS U) : Subsingleton (points B S hS (yoneda.obj U)) := by
  obtain ⟨k, _, ⟨e⟩⟩ := hU
  refine ⟨fun a b => (pointsEquivScheme B S hS U).injective ?_⟩
  have hinj : Function.Injective e.hom.base := by
    intro x y hxy
    have := congrArg e.inv.base hxy
    simp only [← Scheme.Hom.comp_apply, e.hom_inv_id] at this
    exact this
  exact hinj (Subsingleton.elim _ _)

/-- The represented presheaf of an object of the site whose underlying scheme is the spectrum
of a field has a point. -/
theorem nonempty_points_yoneda_of_isFieldObject {U : BigFppfOver B S hS}
    (hU : Stack.IsFieldObject B S hS U) : Nonempty (points B S hS (yoneda.obj U)) := by
  obtain ⟨k, _, ⟨e⟩⟩ := hU
  exact ⟨(pointsEquivScheme B S hS U).symm (e.inv.base (IsLocalRing.closedPoint k))⟩

/-- A test scheme with values in a field passes through exactly one point of `|Y|`. -/
theorem exists_schemesOverPoints_eq_singleton {T : SchemesOver Y}
    (hT : Stack.IsFieldObject B S hS T.left) : ∃ x, schemesOverPoints T = {x} := by
  have := subsingleton_points_yoneda_of_isFieldObject hT
  obtain ⟨w⟩ := nonempty_points_yoneda_of_isFieldObject hT
  refine ⟨pointsMap B S hS (yoneda.obj T.left) (schemesOverHom T) w, ?_⟩
  ext x
  constructor
  · rintro ⟨w', rfl⟩
    rw [Subsingleton.elim w' w]
    rfl
  · rintro rfl
    exact ⟨w, rfl⟩

/-- For a test scheme with values in a field, the points it passes through lie in a set as soon
as one of them does. -/
theorem schemesOverPoints_subset_iff {T : SchemesOver Y}
    (hT : Stack.IsFieldObject B S hS T.left) {x : points B S hS Y.1}
    (hx : x ∈ schemesOverPoints T) (W : Set (points B S hS Y.1)) :
    schemesOverPoints T ⊆ W ↔ x ∈ W := by
  obtain ⟨y, hy⟩ := exists_schemesOverPoints_eq_singleton hT
  rw [hy] at hx ⊢
  rw [Set.mem_singleton_iff.1 hx, Set.singleton_subset_iff]

/-- A field-valued point of `Y`, as a test scheme over `Y`: the spectrum of its field, with the
morphism to `Y` that its section is. -/
def FieldValuedPoint.toSchemesOver (p : FieldValuedPoint B S hS Y.1) : SchemesOver Y :=
  CostructuredArrow.mk (Y := p.siteObject)
    (ObjectProperty.homMk (yonedaEquiv.symm p.value) :
      (schemeSpaceFunctor B S hS).obj p.siteObject ⟶ Y)

/-- The test scheme of a field-valued point has values in a field. -/
theorem FieldValuedPoint.isFieldObject_toSchemesOver (p : FieldValuedPoint B S hS Y.1) :
    Stack.IsFieldObject B S hS (FieldValuedPoint.toSchemesOver p).left :=
  ⟨p.carrier, p.field, ⟨Iso.refl _⟩⟩

/-- The test scheme of a field-valued point passes through the point it represents. -/
theorem FieldValuedPoint.class_mem_schemesOverPoints (p : FieldValuedPoint B S hS Y.1) :
    p.class B S hS Y.1 ∈ schemesOverPoints (FieldValuedPoint.toSchemesOver p) :=
  ⟨(FieldValuedPoint.tautological B S hS p).class B S hS _,
    FieldValuedPoint.pointsMap_class_tautological B S hS p⟩

/-- Every point of `|Y|` is passed through by a test scheme with values in a field. -/
theorem exists_isFieldObject_mem_schemesOverPoints (x : points B S hS Y.1) :
    ∃ T : SchemesOver Y, Stack.IsFieldObject B S hS T.left ∧ x ∈ schemesOverPoints T := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  exact ⟨_, FieldValuedPoint.isFieldObject_toSchemesOver p,
    FieldValuedPoint.class_mem_schemesOverPoints p⟩

/-- A field-valued point of `Y` dominating the image of a field-valued point of a test scheme
`T₀` maps to `T₀` as a test scheme. -/
theorem nonempty_toSchemesOver_hom_of_dominates (T₀ : SchemesOver Y)
    (w : FieldValuedPoint B S hS (yoneda.obj T₀.left)) (r : FieldValuedPoint B S hS Y.1)
    (h : FieldValuedPoint.Dominates B S hS Y.1 r
      (FieldValuedPoint.map B S hS _ (schemesOverHom T₀) w)) :
    Nonempty (FieldValuedPoint.toSchemesOver r ⟶ T₀) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨CostructuredArrow.homMk (f ≫ w.value) ?_⟩
  refine ObjectProperty.hom_ext _ ?_
  change yoneda.map (f ≫ w.value) ≫ schemesOverHom T₀ = yonedaEquiv.symm r.value
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, yonedaEquiv_apply]
  change (schemesOverHom T₀).app _ (𝟙 _ ≫ f ≫ w.value) = r.value
  rw [Category.id_comp, ← hf]
  exact NatTrans.naturality_apply (schemesOverHom T₀) f.op w.value

/-- **Common field extensions of test schemes (Stacks 03BU).**  Two test schemes over `Y` with
values in fields which pass through the same point of `|Y|` admit a common field extension over
`Y`: a test scheme with values in a field mapping to both over `Y`. -/
theorem exists_common_extension_of_mem {T₀ T₀' : SchemesOver Y} {x : points B S hS Y.1}
    (hx : x ∈ schemesOverPoints T₀) (hx' : x ∈ schemesOverPoints T₀') :
    ∃ T₁ : SchemesOver Y, Stack.IsFieldObject B S hS T₁.left ∧
      Nonempty (T₁ ⟶ T₀) ∧ Nonempty (T₁ ⟶ T₀') := by
  obtain ⟨w, rfl⟩ := hx
  obtain ⟨w', hw'⟩ := hx'
  obtain ⟨u, rfl⟩ := Quot.exists_rep w
  obtain ⟨u', rfl⟩ := Quot.exists_rep w'
  rw [pointsMap_class, pointsMap_class, FieldValuedPoint.class_eq_class_iff] at hw'
  obtain ⟨r, h', h⟩ := hw'
  exact ⟨_, FieldValuedPoint.isFieldObject_toSchemesOver r,
    nonempty_toSchemesOver_hom_of_dominates T₀ u r h,
    nonempty_toSchemesOver_hom_of_dominates T₀' u' r h'⟩

/-- The points a test scheme passes through, after composing with `c : U ⟶ Y`, are the images of
those it passes through in `|U|`. -/
theorem schemesOverPoints_map {U : AlgebraicSpaces B S hS} (c : U ⟶ Y) (T : SchemesOver U) :
    schemesOverPoints ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS) c).obj T) =
      pointsMap B S hS U.1 c.hom '' schemesOverPoints T := by
  change Set.range (pointsMap B S hS (yoneda.obj T.left) (schemesOverHom T ≫ c.hom)) = _
  rw [pointsMap_comp, Set.range_comp]

end Points

/-! ### The descent of the locus -/

section Descent

variable {Y : AlgebraicSpaces B S hS}

/-- A property of the test schemes over `Y` with values in fields which does not change under a
field extension over `Y` transports between two test schemes through the same point of `|Y|`. -/
theorem of_mem_schemesOverPoints (P : SchemesOver Y → Prop)
    (hP : ∀ {T₁ T₀ : SchemesOver Y}, (T₁ ⟶ T₀) → Stack.IsFieldObject B S hS T₁.left →
      Stack.IsFieldObject B S hS T₀.left → (P T₀ ↔ P T₁))
    {T T₀ : SchemesOver Y} (hT : Stack.IsFieldObject B S hS T.left)
    (hT₀ : Stack.IsFieldObject B S hS T₀.left) {x : points B S hS Y.1}
    (hx : x ∈ schemesOverPoints T) (hx₀ : x ∈ schemesOverPoints T₀) (h : P T) : P T₀ := by
  obtain ⟨T₁, hT₁, ⟨g⟩, ⟨g₀⟩⟩ := exists_common_extension_of_mem hx hx₀
  exact (hP g₀ hT₁ hT₀).2 ((hP g hT₁ hT).1 h)

/-- **Étale descent of an open locus cut out at the points with values in a field**, on the
point set `|Y|`.  Let `P` be a property of the test schemes over `Y` with values in fields that
does not change under a field extension over `Y`, and assume that for every affine étale chart
`φ : Spec(A) ⟶ Y` there is an open set of points of `Spec(A)` which a test scheme `T` over
`Spec(A)` with values in a field passes through exactly when `P(T ⟶ Spec(A) ⟶ Y)`.  Then there
is an open set `W` of points of `|Y|` which a test scheme `T₀` over `Y` with values in a field
passes through exactly when `P(T₀)`.

`W` is the set of points all of whose field-valued representatives satisfy `P`.  It is the union
of the images of the chart opens, each open because an étale morphism from a scheme is open on
points, and every point of `|Y|` lies in the image of an affine étale chart. -/
theorem exists_isOpen_forall_isFieldObject_iff (P : SchemesOver Y → Prop)
    (hP : ∀ {T₁ T₀ : SchemesOver Y}, (T₁ ⟶ T₀) → Stack.IsFieldObject B S hS T₁.left →
      Stack.IsFieldObject B S hS T₀.left → (P T₀ ↔ P T₁))
    (hloc : ∀ {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
      (gA : B.obj hA ⟶ B.obj hS) (φ : schemeSpace (specFppfOver B S hS hA gA) ⟶ Y),
      IsEtale B S hS φ.hom →
      ∃ Wc : Set (points B S hS (yoneda.obj (specFppfOver B S hS hA gA))), IsOpen Wc ∧
        ∀ T : SchemesOver (schemeSpace (specFppfOver B S hS hA gA)),
          Stack.IsFieldObject B S hS T.left →
          (schemesOverPoints T ⊆ Wc ↔
            P ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS) φ).obj T))) :
    ∃ W : Set (points B S hS Y.1), IsOpen W ∧
      ∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left →
        (schemesOverPoints T₀ ⊆ W ↔ P T₀) := by
  let W : Set (points B S hS Y.1) := {x | ∀ T₀ : SchemesOver Y,
    Stack.IsFieldObject B S hS T₀.left → x ∈ schemesOverPoints T₀ → P T₀}
  have hmem : ∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left →
      (schemesOverPoints T₀ ⊆ W ↔ P T₀) := by
    intro T₀ hT₀
    obtain ⟨x, hx⟩ := exists_schemesOverPoints_eq_singleton hT₀
    have hx₀ : x ∈ schemesOverPoints T₀ := hx ▸ rfl
    rw [schemesOverPoints_subset_iff hT₀ hx₀]
    exact ⟨fun h => h T₀ hT₀ hx₀, fun h T₀' hT₀' hx' =>
      of_mem_schemesOverPoints P hP hT₀ hT₀' hx₀ hx' h⟩
  refine ⟨W, ?_, hmem⟩
  rw [isOpen_iff_forall_mem_open]
  intro x hxW
  -- an affine étale chart through `x`
  obtain ⟨Z, b, hZ, hb, hz⟩ :=
    exists_affine_etale_chart_at_finite_points B S hS Y.1 Y.2 (n := 1) (fun _ => x)
  obtain ⟨z, hzx⟩ := hz 0
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Z) := hZ
  let e := ((BigFppfOver.toScheme B S hS).obj Z).isoSpec
  have hA : B.Contains (Spec (CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤))) :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact e.inv) Z.left.2
  let gA : B.obj hA ⟶ B.obj hS := ObjectProperty.homMk e.inv ≫ Z.hom
  let eV : specFppfOver B S hS hA gA ≅ Z :=
    Over.isoMk (B.inclusion.preimageIso e.symm) (B.inclusion.map_injective (by
      rw [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      rfl))
  let φ : schemeSpace (specFppfOver B S hS hA gA) ⟶ Y :=
    ObjectProperty.homMk (yoneda.map eV.hom ≫ b)
  have hφ' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ.hom := by
    have := isMultiplicative_presheaf_etale B S hS
    exact MorphismProperty.comp_mem _ _ _
      (presheaf_etale_of_iso B S hS (yoneda.mapIso eV)) hb
  have hφ : IsEtale B S hS φ.hom := isEtale_of_presheaf_etale B S hS hφ'
  obtain ⟨Wc, hWc, hWcP⟩ := hloc hA gA φ hφ
  have himage : x ∈ Set.range (pointsMap B S hS _ φ.hom) := by
    refine ⟨pointsMap B S hS _ (yoneda.map eV.inv) z, ?_⟩
    change (pointsMap B S hS _ (yoneda.map eV.hom ≫ b) ∘
      pointsMap B S hS _ (yoneda.map eV.inv)) z = x
    rw [← pointsMap_comp, ← Category.assoc, ← yoneda.map_comp, eV.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, hzx]
  have hiff : ∀ w, pointsMap B S hS _ φ.hom w ∈ W ↔ w ∈ Wc := by
    intro w
    obtain ⟨T, hT, hwT⟩ := exists_isFieldObject_mem_schemesOverPoints (Y := schemeSpace _) w
    have hwT' := schemesOverPoints_map φ T ▸ Set.mem_image_of_mem _ hwT
    exact ((schemesOverPoints_subset_iff (T := (CostructuredArrow.map
          (S := schemeSpaceFunctor B S hS) φ).obj T) hT hwT' W).symm.trans
      ((hmem _ hT).trans (hWcP T hT).symm)).trans (schemesOverPoints_subset_iff hT hwT Wc)
  refine ⟨pointsMap B S hS _ φ.hom '' Wc, ?_,
    isOpenMap_pointsMap_of_etale B S hS Y.2 _ φ.hom hφ' Wc hWc, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact (hiff w).2 hw
  · obtain ⟨w, rfl⟩ := himage
    exact ⟨w, (hiff w).1 hxW, rfl⟩

/-- **Étale descent of an open locus cut out at the points with values in a field.**  In the
situation of `AlgebraicGeometry.Space.exists_isOpen_forall_isFieldObject_iff`, there is an open
subspace `W` of `Y` such that a test scheme `T₀` over `Y` with values in a field factors through
`W` exactly when `P(T₀)`. -/
theorem exists_openSubspace_forall_isFieldObject_iff (P : SchemesOver Y → Prop)
    (hP : ∀ {T₁ T₀ : SchemesOver Y}, (T₁ ⟶ T₀) → Stack.IsFieldObject B S hS T₁.left →
      Stack.IsFieldObject B S hS T₀.left → (P T₀ ↔ P T₁))
    (hloc : ∀ {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
      (gA : B.obj hA ⟶ B.obj hS) (φ : schemeSpace (specFppfOver B S hS hA gA) ⟶ Y),
      IsEtale B S hS φ.hom →
      ∃ Wc : Set (points B S hS (yoneda.obj (specFppfOver B S hS hA gA))), IsOpen Wc ∧
        ∀ T : SchemesOver (schemeSpace (specFppfOver B S hS hA gA)),
          Stack.IsFieldObject B S hS T.left →
          (schemesOverPoints T ⊆ Wc ↔
            P ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS) φ).obj T))) :
    ∃ W : OpenSubspaces B S hS Y.1, ∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left →
      (testPoint T₀ ∈ W.1.obj (op T₀.left) ↔ P T₀) := by
  obtain ⟨W, hW, hWP⟩ := exists_isOpen_forall_isFieldObject_iff P hP hloc
  exact ⟨⟨openSubspaceOfPoints B S hS Y.1 W, isOpenSubspace_openSubspaceOfPoints B S hS Y.2 W hW⟩,
    fun T₀ hT₀ => (testPoint_mem_openSubspaceOfPoints_iff W T₀).trans (hWP T₀ hT₀)⟩

/-- An open subspace `W` of `Y` is cut out by its set of points: a test scheme lies in `W`
exactly when the points it passes through lie in the image of `|W|`. -/
theorem testPoint_mem_iff_schemesOverPoints_subset (W : OpenSubspaces B S hS Y.1)
    (T : SchemesOver Y) :
    testPoint T ∈ W.1.obj (op T.left) ↔
      schemesOverPoints T ⊆ Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) := by
  rw [← testPoint_mem_openSubspaceOfPoints_iff,
    ← eq_openSubspaceOfPoints_range_pointsMap B S hS Y.2 W.1 W.2]

/-- The image of the points of an open subspace is open. -/
theorem isOpen_range_pointsMap_openSubspace (W : OpenSubspaces B S hS Y.1) :
    IsOpen (Set.range (pointsMap B S hS W.1.toFunctor W.1.ι)) :=
  isOpen_range_pointsMap_of_isOpenImmersion B S hS W.1.ι W.2.2

end Descent

end AlgebraicGeometry.Space

end
