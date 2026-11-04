module

public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedOverFieldCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordLocusPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint

/-!
# The automorphism group of a field-valued point, over the field

A field-valued point `x` of an algebraic stack `𝒳` records an object of the site together with an
identification of its underlying scheme with `Spec k`. The automorphism group algebraic space
`G_x = Isom_𝒳(x, x)` of Stacks 04YP lives over that object of the site. Viewing it over `Spec k`
itself along the identification (the lower-shriek extension of Stacks 03I5 (2)) gives an
algebraic space over the field, on which the notions of algebraic spaces over a field
(geometric reducedness, Stacks 0DMQ; dimension, Stacks 04N6) are defined.

## Main definitions

* `AlgebraicGeometry.Stack.FieldValuedPoint.toFieldSpectrum`: the isomorphism of the site from the
  recorded base of a field-valued point onto the spectrum of its field.
* `AlgebraicGeometry.Stack.automorphismGroupSpaceOverField`: the automorphism group algebraic
  space of a field-valued point, viewed over the spectrum of its field.

## Main results

* `isUnramifiedAutomorphismGroupSpace_iff_isGeometricallyReduced_and_dimension_le_zero`:
  when `G_x` is locally of finite type over the field, it is unramified over the field exactly
  when it is geometrically reduced over the field and has dimension at most zero. This is the
  equivalence of conditions (3)(b) and (3)(c) of Stacks 0DSW for an arbitrary algebraic stack;
  `isUnramifiedAutomorphismGroupSpace_iff_isGeometricallyReduced_and_dimension_eq_zero`
  is the same with the dimension equal to zero, `G_x` having a point, the identity.

* `AlgebraicGeometry.Stack.dmLocus_iff_automorphismLocus`: an object of an algebraic stack, over
  any scheme, lies in the Deligne–Mumford locus exactly when its automorphism group algebraic space
  is unramified; `AlgebraicGeometry.Stack.dmLocus_iff_isUnramified_automorphismGroupSpace` reads
  this on a fibre. This is Stacks 0DSW (2) for an arbitrary algebraic stack.
* `AlgebraicGeometry.Stack.exists_largest_isAbsolutelyDM_openSubstack_eq_dmLocus`: the
  Deligne–Mumford locus is cut out by the largest Deligne–Mumford open substack, the open
  substack of objects with unramified automorphism group. This is Stacks 0DSW (1) for an
  arbitrary algebraic stack.

## References

* [Stacks Project, Tag 0DSW](https://stacks.math.columbia.edu/tag/0DSW)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 04YP](https://stacks.math.columbia.edu/tag/04YP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The isomorphism of the site from the recorded base of a field-valued point onto the spectrum
of its field: the recorded identification of the underlying schemes, read in the site. -/
noncomputable def FieldValuedPoint.toFieldSpectrum
    {𝒜 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)} (x : FieldValuedPoint B S hS 𝒜) :
    x.base.left ⟶ B.obj (contains_spectrum_fieldValuedPoint B S hS x) :=
  (B.inclusion.preimageIso (X := x.base.left)
    (Y := B.obj (contains_spectrum_fieldValuedPoint B S hS x)) x.isSpec).hom

/-- The morphism `FieldValuedPoint.toFieldSpectrum` is an isomorphism. -/
instance FieldValuedPoint.isIso_toFieldSpectrum
    {𝒜 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)} (x : FieldValuedPoint B S hS 𝒜) :
    IsIso (x.toFieldSpectrum B S hS) := by
  unfold FieldValuedPoint.toFieldSpectrum
  infer_instance

/-- The automorphism group algebraic space `G_x` of a field-valued point `x` of an algebraic stack
(Stacks 04YP), viewed over the spectrum of the field of `x` along
`AlgebraicGeometry.Stack.FieldValuedPoint.toFieldSpectrum`. -/
noncomputable def automorphismGroupSpaceOverField (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : FieldValuedPoint B S hS 𝒳.val.val) :
    (BigFppfOver B (Spec (.of x.carrier)) (contains_spectrum_fieldValuedPoint B S hS x))ᵒᵖ ⥤
      Type u :=
  (OverShriek.relocalizePresheafFunctor (x.toFieldSpectrum B S hS)).obj
    (automorphismGroupSpace B S hS 𝒳.val 𝒳.property x.base ⟨x.obj, x.over⟩).obj.X.left

/-- The automorphism group of a field-valued point, viewed over the field, is an algebraic space
over the field (Stacks 03I5 (2)). -/
theorem isAlgebraicSpace_automorphismGroupSpaceOverField (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : FieldValuedPoint B S hS 𝒳.val.val) :
    IsAlgebraicSpace B (Spec (.of x.carrier)) (contains_spectrum_fieldValuedPoint B S hS x)
      (automorphismGroupSpaceOverField B S hS 𝒳 x) :=
  isAlgebraicSpace_viewOver B _ _ _ _ _ _
    (automorphismGroupSpace B S hS 𝒳.val 𝒳.property x.base ⟨x.obj, x.over⟩).property

/-- **The equivalence of (3)(b) and (3)(c) of Stacks 0DSW, for any algebraic stack.** Let `x` be a
field-valued point of an algebraic stack whose automorphism group algebraic space `G_x` is locally
of finite type over the field. Then `G_x` is unramified over the field if and only if it is
geometrically reduced over the field and has dimension at most zero. -/
theorem isUnramifiedAutomorphismGroupSpace_iff_isGeometricallyReduced_and_dimension_le_zero
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : FieldValuedPoint B S hS 𝒳.val.val)
    (hlft : Space.IsLocallyOfFiniteType B x.base.left.1 x.base.left.2
      (automorphismGroupSpace B S hS 𝒳.val 𝒳.property x.base ⟨x.obj, x.over⟩).obj.X.hom) :
    IsUnramifiedAutomorphismGroupSpace B S hS 𝒳 x ↔
      Space.IsGeometricallyReduced x.carrier B (contains_spectrum_fieldValuedPoint B S hS x)
          (automorphismGroupSpaceOverField B S hS 𝒳 x)
          (isAlgebraicSpace_automorphismGroupSpaceOverField B S hS 𝒳 x) ∧
        Space.dimension B (Spec (.of x.carrier)) (contains_spectrum_fieldValuedPoint B S hS x)
          (automorphismGroupSpaceOverField B S hS 𝒳 x)
          (isAlgebraicSpace_automorphismGroupSpaceOverField B S hS 𝒳 x) ≤ 0 :=
  Space.isUnramified_iff_isGeometricallyReduced_viewOver_and_dimension_le_zero x.carrier B
    (contains_spectrum_fieldValuedPoint B S hS x) x.base.left.2 (x.toFieldSpectrum B S hS)
    (automorphismGroupSpace B S hS 𝒳.val 𝒳.property x.base ⟨x.obj, x.over⟩).property _ hlft

/-- The automorphism group of a field-valued point, viewed over the field, does not have dimension
`⊥`: it has a point, the identity. -/
theorem dimension_automorphismGroupSpaceOverField_ne_bot (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : FieldValuedPoint B S hS 𝒳.val.val) :
    Space.dimension B (Spec (.of x.carrier)) (contains_spectrum_fieldValuedPoint B S hS x)
      (automorphismGroupSpaceOverField B S hS 𝒳 x)
      (isAlgebraicSpace_automorphismGroupSpaceOverField B S hS 𝒳 x) ≠ ⊥ := by
  let hk := contains_spectrum_fieldValuedPoint B S hS x
  let G := automorphismGroupSpace B S hS 𝒳.val 𝒳.property x.base ⟨x.obj, x.over⟩
  let ι := x.toFieldSpectrum B S hS
  let s : G.obj.X.left.obj (Opposite.op (Over.mk (inv ι))) :=
    (MonObj.one (X := G.obj.X)).left.app _ (terminal.from _)
  let p : Space.FieldValuedPoint B (Spec (.of x.carrier)) hk
      (automorphismGroupSpaceOverField B S hS 𝒳 x) :=
    { carrier := x.carrier
      contained := hk
      toBase := 𝟙 _
      value := OverShriek.relocalizeMk ι _ (inv ι) s (IsIso.inv_hom_id ι) }
  intro hbot
  refine Space.dimensionAtPoint_ne_bot B _ hk _
    (isAlgebraicSpace_automorphismGroupSpaceOverField B S hS 𝒳 x) (p.class B _ hk _)
    (eq_bot_iff.mpr ?_)
  rw [← hbot]
  exact le_iSup (fun y => Space.dimensionAtPoint B _ hk _
    (isAlgebraicSpace_automorphismGroupSpaceOverField B S hS 𝒳 x) y) _

/-- **The equivalence of (3)(b) and (3)(c) of Stacks 0DSW, for any algebraic stack, with the
dimension equal to zero.** Let `x` be a field-valued point of an algebraic stack whose
automorphism group algebraic space `G_x` is locally of finite type over the field. Then `G_x` is
unramified over the field if and only if it is geometrically reduced over the field and has
dimension `0`. -/
theorem isUnramifiedAutomorphismGroupSpace_iff_isGeometricallyReduced_and_dimension_eq_zero
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : FieldValuedPoint B S hS 𝒳.val.val)
    (hlft : Space.IsLocallyOfFiniteType B x.base.left.1 x.base.left.2
      (automorphismGroupSpace B S hS 𝒳.val 𝒳.property x.base ⟨x.obj, x.over⟩).obj.X.hom) :
    IsUnramifiedAutomorphismGroupSpace B S hS 𝒳 x ↔
      Space.IsGeometricallyReduced x.carrier B (contains_spectrum_fieldValuedPoint B S hS x)
          (automorphismGroupSpaceOverField B S hS 𝒳 x)
          (isAlgebraicSpace_automorphismGroupSpaceOverField B S hS 𝒳 x) ∧
        Space.dimension B (Spec (.of x.carrier)) (contains_spectrum_fieldValuedPoint B S hS x)
          (automorphismGroupSpaceOverField B S hS 𝒳 x)
          (isAlgebraicSpace_automorphismGroupSpaceOverField B S hS 𝒳 x) = 0 := by
  rw [isUnramifiedAutomorphismGroupSpace_iff_isGeometricallyReduced_and_dimension_le_zero B S hS
    𝒳 x hlft]
  refine and_congr Iff.rfl ⟨fun hle => le_antisymm hle ?_, fun h0 => h0.le⟩
  obtain ⟨d, hd⟩ :=
    WithBot.ne_bot_iff_exists.mp (dimension_automorphismGroupSpaceOverField_ne_bot B S hS 𝒳 x)
  rw [← hd]
  exact_mod_cast (zero_le : (0 : ℕ∞) ≤ d)

/-- **Stacks 03I4 (2), for representability.** The lower-shriek extension along a morphism `g` of
the site of a representable presheaf is representable: by the scheme representing it, viewed over
the target of `g`. -/
theorem isRepresentable_relocalizePresheafFunctor_obj {T T' : B.Schemes} (g : T ⟶ T')
    (F : (BigFppfOver B (B.inclusion.obj T) T.property)ᵒᵖ ⥤ Type u) [F.IsRepresentable] :
    ((OverShriek.relocalizePresheafFunctor g).obj F).IsRepresentable :=
  isRepresentable_of_natIso _
    ((relocalizedYonedaIso B T T' g F.reprX).symm ≪≫
      (OverShriek.relocalizePresheafFunctor g).mapIso F.reprW)

/-- If the automorphism group algebraic space of a field-valued point is a scheme, so is the
automorphism group viewed over the field. -/
theorem isRepresentable_automorphismGroupSpaceOverField (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : FieldValuedPoint B S hS 𝒳.val.val)
    [(automorphismGroupSpace B S hS 𝒳.val 𝒳.property x.base
      ⟨x.obj, x.over⟩).obj.X.left.IsRepresentable] :
    (automorphismGroupSpaceOverField B S hS 𝒳 x).IsRepresentable :=
  isRepresentable_relocalizePresheafFunctor_obj B (x.toFieldSpectrum B S hS) _

/-! ### The Deligne–Mumford locus at an arbitrary object -/

section Locus

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The open substack of objects with unramified automorphism group is Deligne–Mumford. -/
private theorem isAbsolutelyDM_automorphismLocusSubstack (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    AlgebraicStacks.IsAbsolutelyDM B S hS hZ (automorphismLocusSubstack B S hS _ 𝒳 _
      (unramifiedLocus_spec B S hS 𝒳).1 (unramifiedLocus_spec B S hS 𝒳).2).toAlgebraicStack :=
  (isAbsolutelyDM_iff_forall_automorphismLocus B S hS hZ _).mpr fun y =>
    (automorphismLocus_toAlgebraicStack_iff B S hS _ 𝒳 _ y).mpr y.property

/-- **The Deligne–Mumford locus is the unramified automorphism locus.** An object of an algebraic
stack lies in its Deligne–Mumford locus exactly when its automorphism group algebraic space is
unramified over the base of the object. This is the argument of Stacks 0DSN, which does not use
that the object lies over a field. -/
theorem dmLocus_iff_automorphismLocus (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : 𝒳.val.val.obj) :
    dmLocus B S hS hZ 𝒳 x ↔
      automorphismLocus B S hS (@_root_.AlgebraicGeometry.Unramified) 𝒳 x := by
  refine (dmLocus_apply_iff B S hS hZ 𝒳 x).trans ⟨?_, fun hx => ?_⟩
  · rintro ⟨V, hV, hxV⟩
    exact (automorphismLocus_toAlgebraicStack_iff B S hS _ 𝒳 V ⟨x, hxV⟩).mp
      ((isAbsolutelyDM_iff_forall_automorphismLocus B S hS hZ V.toAlgebraicStack).mp hV _)
  · let V := automorphismLocusSubstack B S hS _ 𝒳 _ (unramifiedLocus_spec B S hS 𝒳).1
      (unramifiedLocus_spec B S hS 𝒳).2
    exact ⟨V, isAbsolutelyDM_automorphismLocusSubstack B S hS hZ 𝒳, hx⟩

/-- **Stacks 0DSW (2), for any algebraic stack.** An object `x` of an algebraic stack over `U`
lies in the Deligne–Mumford locus exactly when its automorphism group algebraic space
`Isom_𝒳(x, x)` is unramified over `U`. -/
theorem dmLocus_iff_isUnramified_automorphismGroupSpace (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {U : BigFppfOver B S hS} (x : 𝒳.val.val.p.Fiber U) :
    dmLocus B S hS hZ 𝒳 x.1 ↔ Space.IsUnramified B U.left.1 U.left.2
      (automorphismGroupSpace B S hS 𝒳.val 𝒳.property U x).obj.X.hom :=
  (dmLocus_iff_automorphismLocus B S hS hZ 𝒳 x.1).trans
    ((automorphismLocus_iff B S hS _ 𝒳 x).trans
      (holdsOnEveryEtaleChart_isomSpaceOver_hom_iff B S hS 𝒳 _ U x x).symm)

/-- **Stacks 0DSW (1), for any algebraic stack.** The Deligne–Mumford locus is cut out by an
open substack, which is Deligne–Mumford and contains every Deligne–Mumford open substack: the
open substack of objects with unramified automorphism group. -/
theorem exists_largest_isAbsolutelyDM_openSubstack_eq_dmLocus (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    ∃ W : OpenSubstack 𝒳,
      W.property = dmLocus B S hS hZ 𝒳 ∧
      AlgebraicStacks.IsAbsolutelyDM B S hS hZ W.toAlgebraicStack ∧
      ∀ V : OpenSubstack 𝒳, AlgebraicStacks.IsAbsolutelyDM B S hS hZ V.toAlgebraicStack →
        V.property ≤ W.property := by
  let W := automorphismLocusSubstack B S hS _ 𝒳 _ (unramifiedLocus_spec B S hS 𝒳).1
    (unramifiedLocus_spec B S hS 𝒳).2
  have hW : W.property = dmLocus B S hS hZ 𝒳 :=
    funext fun x => propext (dmLocus_iff_automorphismLocus B S hS hZ 𝒳 x).symm
  exact ⟨W, hW, isAbsolutelyDM_automorphismLocusSubstack B S hS hZ 𝒳,
    fun V hV => hW ▸ le_dmLocus B S hS hZ 𝒳 V hV⟩

end Locus

end AlgebraicGeometry.Stack

end
