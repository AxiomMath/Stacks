module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology

/-!
# Points of a represented presheaf

For an object `U` of the big fppf site of `S`, the map `|h_U| → U` sending a field-valued point
of the represented presheaf to the image of its field spectrum is a bijection, and a
homeomorphism for the point topology. Consequently, for a morphism of the site, the induced map
on points is closed, open or surjective exactly when the underlying morphism of schemes is.

## Main definitions

* `AlgebraicGeometry.Space.pointsToScheme` is the map `|h_U| → U`, obtained from
  `AlgebraicGeometry.Space.schemePoint` by passing to the quotient.
* `AlgebraicGeometry.Space.pointsEquivScheme` is the resulting bijection.

## Main results

* `AlgebraicGeometry.Space.bijective_pointsToScheme`: the comparison map is a bijection.
* `AlgebraicGeometry.Space.isOpen_pointTopology_yoneda_iff_isOpen_image` and
  `AlgebraicGeometry.Space.isClosed_pointTopology_yoneda_iff_isClosed_image`: the bijection
  identifies the point topology of a represented presheaf with the topology of the scheme.
* `AlgebraicGeometry.Space.isClosedMap_pointsMap_yoneda_iff`,
  `AlgebraicGeometry.Space.isOpenMap_pointsMap_yoneda_iff` and
  `AlgebraicGeometry.Space.surjective_pointsMap_yoneda_iff`: for a morphism of the site, the
  induced map on points is closed, open, surjective exactly when the underlying map of
  schemes is.
* `AlgebraicGeometry.exists_residueFieldHom_comp_fromSpecResidueField`: a morphism from the
  spectrum of a field into a scheme whose image is the single point `x` factors through
  `Spec` of the residue field at `x`.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism from the spectrum of a field into a scheme whose set-theoretic image is the
single point `x` factors through `Spec` of the residue field at `x`. -/
theorem exists_residueFieldHom_comp_fromSpecResidueField {X : Scheme.{u}} {K : Type u}
    [Field K] (g : Spec (CommRingCat.of K) ⟶ X) (x : X) (hx : ∀ y, g y = x) :
    ∃ φ : X.residueField x ⟶ CommRingCat.of K,
      Spec.map φ ≫ X.fromSpecResidueField x = g := by
  obtain rfl : x = g (IsLocalRing.closedPoint K) := (hx _).symm
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X g⟩

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison map -/

/-- The underlying scheme point of a field-valued point is unchanged by passing to an
extension. -/
theorem schemePoint_eq_of_dominates (U : BigFppfOver B S hS)
    {p q : FieldValuedPoint B S hS (yoneda.obj U)}
    (h : FieldValuedPoint.Dominates B S hS (yoneda.obj U) p q) :
    schemePoint B S hS U p = schemePoint B S hS U q := by
  obtain ⟨σ, hσ⟩ := h
  have hsubq : Subsingleton ((BigFppfOver.toScheme B S hS).obj q.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of q.carrier)))
  have hvalue : (BigFppfOver.toScheme B S hS).map p.value =
      (BigFppfOver.toScheme B S hS).map σ ≫ (BigFppfOver.toScheme B S hS).map q.value := by
    rw [← Functor.map_comp]
    exact congrArg (BigFppfOver.toScheme B S hS).map hσ.symm
  refine (congrFun (congrArg (fun m : (BigFppfOver.toScheme B S hS).obj p.siteObject ⟶
      (BigFppfOver.toScheme B S hS).obj U ↦ ⇑m) hvalue)
    (IsLocalRing.closedPoint p.carrier :
      (BigFppfOver.toScheme B S hS).obj p.siteObject)).trans ?_
  exact (Scheme.Hom.comp_apply _ _ _).trans
    (congrArg (fun y ↦ (BigFppfOver.toScheme B S hS).map q.value y)
      (@Subsingleton.elim _ hsubq _ (IsLocalRing.closedPoint q.carrier)))

/-- Two field-valued points with a common extension have the same underlying scheme point. -/
theorem schemePoint_eq_of_hasCommonExtension (U : BigFppfOver B S hS)
    {p q : FieldValuedPoint B S hS (yoneda.obj U)}
    (h : FieldValuedPoint.HasCommonExtension B S hS (yoneda.obj U) p q) :
    schemePoint B S hS U p = schemePoint B S hS U q := by
  obtain ⟨r, hp, hq⟩ := h
  rw [← schemePoint_eq_of_dominates B S hS U hp, schemePoint_eq_of_dominates B S hS U hq]

/-- The comparison map from the points of a represented presheaf to the points of the
representing scheme. -/
noncomputable def pointsToScheme (U : BigFppfOver B S hS) :
    points B S hS (yoneda.obj U) → (BigFppfOver.toScheme B S hS).obj U :=
  Quot.lift (schemePoint B S hS U)
    fun _ _ h ↦ schemePoint_eq_of_hasCommonExtension B S hS U h

/-- The comparison map sends the class of a field-valued point to its underlying scheme
point. -/
@[simp]
theorem pointsToScheme_class (U : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    pointsToScheme B S hS U (p.class B S hS (yoneda.obj U)) = schemePoint B S hS U p := rfl

/-! ### Bijectivity -/

/-- Every point of a scheme in the big fppf site of `S` is the underlying scheme point of a
field-valued point of its represented presheaf, namely of the one given by the residue field
there. -/
theorem exists_fieldValuedPoint_schemePoint_eq (U : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    ∃ p : FieldValuedPoint B S hS (yoneda.obj U), schemePoint B S hS U p = x := by
  obtain ⟨K, instK, hK, ρ, hρ⟩ := exists_fieldSpec_at_point B U.left.2 x
  exact ⟨{ carrier := K, contained := hK, toBase := ρ ≫ U.hom.hom
           value := Over.homMk (⟨ρ⟩ : B.obj hK ⟶ U.left) (by ext; rfl) }, hρ _⟩

/-- Two field-valued points of a represented presheaf with the same underlying scheme point
admit a common field-valued extension. -/
theorem hasCommonExtension_of_schemePoint_eq (U : BigFppfOver B S hS)
    {p q : FieldValuedPoint B S hS (yoneda.obj U)}
    (h : schemePoint B S hS U p = schemePoint B S hS U q) :
    FieldValuedPoint.HasCommonExtension B S hS (yoneda.obj U) p q := by
  have hsubp : Subsingleton ((BigFppfOver.toScheme B S hS).obj p.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  have hsubq : Subsingleton ((BigFppfOver.toScheme B S hS).obj q.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of q.carrier)))
  have hp : ∀ y, (BigFppfOver.toScheme B S hS).map p.value y = schemePoint B S hS U p :=
    fun y ↦ congrArg (fun z ↦ (BigFppfOver.toScheme B S hS).map p.value z)
      (@Subsingleton.elim _ hsubp y (IsLocalRing.closedPoint p.carrier))
  have hq : ∀ y, (BigFppfOver.toScheme B S hS).map q.value y = schemePoint B S hS U p :=
    fun y ↦ (congrArg (fun z ↦ (BigFppfOver.toScheme B S hS).map q.value z)
      (@Subsingleton.elim _ hsubq y (IsLocalRing.closedPoint q.carrier))).trans h.symm
  obtain ⟨φp, hφp⟩ := exists_residueFieldHom_comp_fromSpecResidueField (K := p.carrier)
    ((BigFppfOver.toScheme B S hS).map p.value) _ hp
  obtain ⟨φq, hφq⟩ := exists_residueFieldHom_comp_fromSpecResidueField (K := q.carrier)
    ((BigFppfOver.toScheme B S hS).map q.value) _ hq
  obtain ⟨Ω, instΩ, hΩ, ca, cb, key⟩ :=
    exists_fieldSpec_common B (K := p.carrier) (L := q.carrier)
      (M := ((BigFppfOver.toScheme B S hS).obj U).residueField (schemePoint B S hS U p))
      p.contained q.contained (Spec.map φp) (Spec.map φq)
  have hkey : ca ≫ (BigFppfOver.toScheme B S hS).map p.value =
      cb ≫ (BigFppfOver.toScheme B S hS).map q.value := by
    rw [← hφp, ← hφq, ← Category.assoc, ← Category.assoc, key]
  have hpb : (BigFppfOver.toScheme B S hS).map p.value ≫ U.hom.hom = p.toBase :=
    congrArg (fun k ↦ k.hom) (Over.w p.value)
  have hqb : (BigFppfOver.toScheme B S hS).map q.value ≫ U.hom.hom = q.toBase :=
    congrArg (fun k ↦ k.hom) (Over.w q.value)
  have hbase : cb ≫ q.toBase = ca ≫ p.toBase := by
    rw [← hpb, ← hqb, ← Category.assoc, ← Category.assoc, hkey]
  let σ : (Over.mk (⟨ca ≫ p.toBase⟩ : B.obj hΩ ⟶ B.obj hS) : BigFppfOver B S hS) ⟶
      p.siteObject := Over.homMk (⟨ca⟩ : B.obj hΩ ⟶ B.obj p.contained) (by ext; rfl)
  let τ : (Over.mk (⟨ca ≫ p.toBase⟩ : B.obj hΩ ⟶ B.obj hS) : BigFppfOver B S hS) ⟶
      q.siteObject := Over.homMk (⟨cb⟩ : B.obj hΩ ⟶ B.obj q.contained) (by ext; exact hbase)
  refine ⟨{ carrier := Ω, contained := hΩ, toBase := ca ≫ p.toBase
            value := σ ≫ p.value }, ⟨σ, rfl⟩, ⟨τ, ?_⟩⟩
  change τ ≫ q.value = σ ≫ p.value
  ext
  exact hkey.symm

/-- The comparison map from points of a represented presheaf to points of the scheme is
injective. -/
theorem injective_pointsToScheme (U : BigFppfOver B S hS) :
    Function.Injective (pointsToScheme B S hS U) := by
  intro w₁ w₂ h
  obtain ⟨p, rfl⟩ := Quot.exists_rep w₁
  obtain ⟨q, rfl⟩ := Quot.exists_rep w₂
  exact FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS (yoneda.obj U)
    (hasCommonExtension_of_schemePoint_eq B S hS U h)

/-- The comparison map from points of a represented presheaf to points of the scheme is
surjective. -/
theorem surjective_pointsToScheme (U : BigFppfOver B S hS) :
    Function.Surjective (pointsToScheme B S hS U) := by
  intro x
  obtain ⟨p, hp⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS U x
  exact ⟨p.class B S hS (yoneda.obj U), hp⟩

/-- The points of a scheme, viewed as an algebraic space through its functor
of points, are in canonical one-to-one correspondence with the points of the representing
scheme, the correspondence being `AlgebraicGeometry.Space.pointsToScheme`. -/
@[stacks 03BV]
theorem bijective_pointsToScheme (U : BigFppfOver B S hS) :
    Function.Bijective (pointsToScheme B S hS U) :=
  ⟨injective_pointsToScheme B S hS U, surjective_pointsToScheme B S hS U⟩

/-- The bijection between the points of a represented presheaf and the points of the
representing scheme. -/
noncomputable def pointsEquivScheme (U : BigFppfOver B S hS) :
    points B S hS (yoneda.obj U) ≃ (BigFppfOver.toScheme B S hS).obj U :=
  Equiv.ofBijective _ (bijective_pointsToScheme B S hS U)

/-! ### The topology -/

/-- Under the comparison bijection the point topology of a represented presheaf is the
topology of the representing scheme. -/
theorem isOpen_pointTopology_yoneda_iff_isOpen_image (U : BigFppfOver B S hS)
    (W : Set (points B S hS (yoneda.obj U))) :
    @IsOpen _ (pointTopology B S hS (yoneda.obj U)) W ↔
      IsOpen (pointsToScheme B S hS U '' W) := by
  rw [isOpen_yoneda_iff_isSchemeOpen]
  refine ⟨?_, fun hV ↦ ⟨_, hV, fun p ↦ (injective_pointsToScheme B S hS U).mem_set_image.symm⟩⟩
  rintro ⟨V, hV, hmem⟩
  have hWeq : W = pointsToScheme B S hS U ⁻¹' V := by
    ext w
    obtain ⟨p, rfl⟩ := Quot.exists_rep w
    exact hmem p
  rwa [hWeq, Set.image_preimage_eq _ (surjective_pointsToScheme B S hS U)]

/-- The closed-set form of
`AlgebraicGeometry.Space.isOpen_pointTopology_yoneda_iff_isOpen_image`. -/
theorem isClosed_pointTopology_yoneda_iff_isClosed_image (U : BigFppfOver B S hS)
    (W : Set (points B S hS (yoneda.obj U))) :
    @IsClosed _ (pointTopology B S hS (yoneda.obj U)) W ↔
      IsClosed (pointsToScheme B S hS U '' W) := by
  rw [← @isOpen_compl_iff _ W (pointTopology B S hS (yoneda.obj U)), ← isOpen_compl_iff,
    isOpen_pointTopology_yoneda_iff_isOpen_image,
    Set.image_compl_eq (bijective_pointsToScheme B S hS U)]

/-! ### Transport of point-set conditions to schemes -/

/-- The comparison bijections are natural in the site object. -/
theorem pointsToScheme_pointsMap_yoneda {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (w : points B S hS (yoneda.obj U)) :
    pointsToScheme B S hS V (pointsMap B S hS (yoneda.obj U) (yoneda.map h) w) =
      (BigFppfOver.toScheme B S hS).map h (pointsToScheme B S hS U w) := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep w
  exact schemePoint_map_yoneda B S hS h p

/-- The comparison bijections carry the image of a set of points under `pointsMap` to its image
under the underlying morphism of schemes. -/
theorem image_pointsToScheme_image_pointsMap {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (W : Set (points B S hS (yoneda.obj U))) :
    pointsToScheme B S hS V '' (pointsMap B S hS (yoneda.obj U) (yoneda.map h) '' W) =
      (BigFppfOver.toScheme B S hS).map h '' (pointsToScheme B S hS U '' W) := by
  rw [Set.image_image, Set.image_image]
  exact Set.image_congr' (pointsToScheme_pointsMap_yoneda B S hS h)

/-- For a morphism of the big fppf site of `S`, the induced map on points is closed for the
point topology exactly when the underlying map of schemes is closed. -/
theorem isClosedMap_pointsMap_yoneda_iff {U V : BigFppfOver B S hS} (h : U ⟶ V) :
    @IsClosedMap _ _ (pointTopology B S hS (yoneda.obj U))
        (pointTopology B S hS (yoneda.obj V))
        (pointsMap B S hS (yoneda.obj U) (yoneda.map h)) ↔
      IsClosedMap ⇑((BigFppfOver.toScheme B S hS).map h) := by
  constructor
  · intro hcl C hC
    have hW := (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS U
      (pointsToScheme B S hS U ⁻¹' C)).mpr
      (by rwa [Set.image_preimage_eq _ (surjective_pointsToScheme B S hS U)])
    have h₂ := (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS V _).mp (hcl _ hW)
    rwa [image_pointsToScheme_image_pointsMap,
      Set.image_preimage_eq _ (surjective_pointsToScheme B S hS U)] at h₂
  · intro hcl W hW
    rw [isClosed_pointTopology_yoneda_iff_isClosed_image] at hW ⊢
    rw [image_pointsToScheme_image_pointsMap]
    exact hcl _ hW

/-- For a morphism of the big fppf site of `S`, the induced map on points is open for the
point topology exactly when the underlying map of schemes is open. -/
theorem isOpenMap_pointsMap_yoneda_iff {U V : BigFppfOver B S hS} (h : U ⟶ V) :
    @IsOpenMap _ _ (pointTopology B S hS (yoneda.obj U))
        (pointTopology B S hS (yoneda.obj V))
        (pointsMap B S hS (yoneda.obj U) (yoneda.map h)) ↔
      IsOpenMap ⇑((BigFppfOver.toScheme B S hS).map h) := by
  constructor
  · intro hop C hC
    have hW := (isOpen_pointTopology_yoneda_iff_isOpen_image B S hS U
      (pointsToScheme B S hS U ⁻¹' C)).mpr
      (by rwa [Set.image_preimage_eq _ (surjective_pointsToScheme B S hS U)])
    have h₂ := (isOpen_pointTopology_yoneda_iff_isOpen_image B S hS V _).mp (hop _ hW)
    rwa [image_pointsToScheme_image_pointsMap,
      Set.image_preimage_eq _ (surjective_pointsToScheme B S hS U)] at h₂
  · intro hop W hW
    rw [isOpen_pointTopology_yoneda_iff_isOpen_image] at hW ⊢
    rw [image_pointsToScheme_image_pointsMap]
    exact hop _ hW

/-- For a morphism of the big fppf site of `S`, the induced map on points is surjective
exactly when the underlying map of schemes is surjective. -/
theorem surjective_pointsMap_yoneda_iff {U V : BigFppfOver B S hS} (h : U ⟶ V) :
    Function.Surjective (pointsMap B S hS (yoneda.obj U) (yoneda.map h)) ↔
      Function.Surjective ⇑((BigFppfOver.toScheme B S hS).map h) := by
  constructor
  · intro hs y
    obtain ⟨w, hw⟩ := hs ((pointsEquivScheme B S hS V).symm y)
    refine ⟨pointsToScheme B S hS U w, ?_⟩
    rw [← pointsToScheme_pointsMap_yoneda B S hS h w, hw]
    exact (pointsEquivScheme B S hS V).apply_symm_apply y
  · intro hs w
    obtain ⟨x, hx⟩ := hs (pointsToScheme B S hS V w)
    obtain ⟨v, hv⟩ := surjective_pointsToScheme B S hS U x
    refine ⟨v, (injective_pointsToScheme B S hS V) ?_⟩
    rw [pointsToScheme_pointsMap_yoneda B S hS h v, hv, hx]

end Space

end AlgebraicGeometry

end
