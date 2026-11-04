module

public import StacksFrontier.Homology.KFlat.BifunctorShift
public import StacksFrontier.Homology.KFlat.BifunctorLocalization
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift

/-!
# The K-flat cochain complexes are a shift-compatible model for the K-flat objects

`CochainComplex.KFlatBifunctor.kFlatQ F` localizes the full subcategory of **K-flat objects of
the homotopy category** `K(B)`, and that is the category every K-flat descent in this
development — and so every transformation obtained from one — is defined on.  A transformation
there is, however, not recognisable as a composite of whiskerings: its components are written
in terms of a *chosen cochain representative* `M.obj.as` of a homotopy class, and choosing a
representative of a homotopy class is not functorial.

The cure is the functor of this file.
`CochainComplex.KFlatBifunctor.kFlatQuotient F`, the homotopy quotient from the K-flat cochain
complexes to the K-flat objects, is *surjective on objects on the nose* and commutes with the
shift, so by `CategoryTheory.NatTrans.CommShift₂.of_essSurj` a shift compatibility on the
models may be tested after restriction along it — and after that restriction the chosen
representative is the object itself, so `DerivedCategory.quotientCompQhIso` becomes an
isomorphism of *functors*.

The functor, the complex-level object property and the bridge isomorphism all already exist in
`StacksFrontier/Homology/KFlat/BifunctorLocalization.lean`; what this file adds is the shift
package for them.

## Main results

* `CochainComplex.KFlatBifunctor.kFlatComplexes_isStableUnderShift` and
  `kFlatComplexesLeft_isStableUnderShift`: **a shift of a K-flat cochain complex is K-flat**,
  so `CategoryTheory.ObjectProperty.hasShift` puts a shift on the category of K-flat complexes.
* `CochainComplex.KFlatBifunctor.kFlatQuotient_commShift` (and the left mirror): **the homotopy
  quotient from the K-flat complexes to the K-flat objects commutes with the shift.**
* `CochainComplex.KFlatBifunctor.kFlatQuotient_essSurj` (and the left mirror): **it is
  essentially surjective** — indeed surjective on objects, by
  `kFlatQuotient_obj_objAs`.
* `CochainComplex.KFlatBifunctor.kFlatQuotientCompQIso_commShift`: **the bridge
  `kFlatQuotient ⋙ kFlatQ ≅ kFlatComplexQ` is shift-compatible.**

## Implementation notes

**Why the bridge has to be reassembled before its compatibility is available.**
`kFlatQuotientCompQIso` is `DerivedCategory.quotientCompQhIso` whiskered by the inclusion of
the K-flat complexes, and that transformation is shift-compatible in Mathlib.  But
`CategoryTheory.NatTrans.CommShift` takes the `CategoryTheory.Functor.CommShift` data of its
source and target as instance arguments, and the datum instance search finds for
`kFlatQuotient F ⋙ kFlatQ F` is `CategoryTheory.Functor.CommShift.comp` of the datum of
`kFlatQuotient F` with that of `kFlatQ F` — not the datum of
`(kFlatComplexes F).ι ⋙ HomotopyCategory.quotient _ _ ⋙ DerivedCategory.Qh`, which is what the
whiskering supplies.  The two differ by an associator and by
`CategoryTheory.ObjectProperty.liftCompιIso`, each of which is shift-compatible on its own.
So `kFlatQuotientCompQIsoAssoc` writes the bridge as the composite of those four factors, where
`infer_instance` succeeds, and `kFlatQuotientCompQIsoAssoc_eq` records that it is the same
isomorphism — the two reassociations being the identity on every object.  This is the same step
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTransAssoc` takes.

**Shift stability is not `rfl`.**  `CategoryTheory.HasShift.quotient` is `irreducible` in
Mathlib, so `((HomotopyCategory.quotient _ _).obj K)⟦n⟧` is not syntactically
`(HomotopyCategory.quotient _ _).obj (K⟦n⟧)`; `HomotopyCategory.shift_quotient_obj` is the
lemma that crosses, and it has to be used rather than `rfl`.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-! ### The shift on the K-flat complexes -/

/-- **A shift of a K-flat cochain complex is K-flat.**  This is
`kFlatObjects_isStableUnderShift` at the homotopy class of the complex, crossed back along
`HomotopyCategory.shift_quotient_obj`. -/
instance kFlatComplexes_isStableUnderShift : (kFlatComplexes F).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K hK => by
    have h := (kFlatObjects F).le_shift n
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K) hK
    rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj] at h
    exact h⟩

/-- **A shift of a left K-flat cochain complex is left K-flat**, the mirror in the first
variable of `F`. -/
instance kFlatComplexesLeft_isStableUnderShift : (kFlatComplexesLeft F).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K hK => by
    have h := (kFlatObjectsLeft F).le_shift n
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) hK
    rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj] at h
    exact h⟩

example : HasShift (kFlatComplexes F).FullSubcategory ℤ := inferInstance

example : (kFlatComplexes F).ι.CommShift ℤ := inferInstance

/-! ### The homotopy quotient from the K-flat complexes to the K-flat objects -/

/-- **The homotopy quotient from the K-flat complexes to the K-flat objects commutes with the
shift.**  It is `CategoryTheory.ObjectProperty.lift` of the inclusion followed by the homotopy
quotient, and `CategoryTheory.Functor.CommShift.ofComp` transports the datum of that composite
through the fully faithful inclusion of the K-flat objects.  Seated by name: the `hF`
side-condition argument of `CategoryTheory.ObjectProperty.lift` blocks the keyed match on
Mathlib's instance. -/
@[instance_reducible]
def kFlatQuotient_commShift : (kFlatQuotient F).CommShift ℤ :=
  Functor.CommShift.ofComp ((kFlatObjects F).liftCompιIso
    ((kFlatComplexes F).ι ⋙ HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (fun K ↦ K.2)) ℤ

/-- The mirror of `kFlatQuotient_commShift` in the first variable of `F`. -/
@[instance_reducible]
def kFlatQuotientLeft_commShift : (kFlatQuotientLeft F).CommShift ℤ :=
  Functor.CommShift.ofComp ((kFlatObjectsLeft F).liftCompιIso
    ((kFlatComplexesLeft F).ι ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (fun K ↦ K.2)) ℤ

/-- The identification of the homotopy quotient composed with the inclusion of the K-flat
objects with the inclusion of the K-flat complexes composed with the homotopy quotient is
shift-compatible, by `CategoryTheory.Functor.CommShift.ofComp_compatibility`. -/
theorem kFlatQuotientCompι_commShift :
    letI := kFlatQuotient_commShift F
    NatTrans.CommShift ((kFlatObjects F).liftCompιIso
      ((kFlatComplexes F).ι ⋙ HomotopyCategory.quotient B (ComplexShape.up ℤ))
      (fun K ↦ K.2)).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

/-- **Every K-flat object of the homotopy category is the homotopy class of a K-flat cochain
complex**, and on the nose: the object property of the K-flat objects is K-flatness of the
underlying complex, so the underlying complex of a K-flat object witnesses it. -/
theorem kFlatQuotient_obj_objAs (M : (kFlatObjects F).FullSubcategory) :
    (kFlatQuotient F).obj ⟨M.obj.as, M.property⟩ = M := rfl

/-- **The homotopy quotient from the K-flat complexes to the K-flat objects is essentially
surjective**, by `kFlatQuotient_obj_objAs`. -/
instance kFlatQuotient_essSurj : (kFlatQuotient F).EssSurj where
  mem_essImage M := ⟨⟨M.obj.as, M.property⟩, ⟨Iso.refl _⟩⟩

/-- The mirror of `kFlatQuotient_obj_objAs` in the first variable of `F`. -/
theorem kFlatQuotientLeft_obj_objAs (M : (kFlatObjectsLeft F).FullSubcategory) :
    (kFlatQuotientLeft F).obj ⟨M.obj.as, M.property⟩ = M := rfl

/-- The mirror of `kFlatQuotient_essSurj` in the first variable of `F`. -/
instance kFlatQuotientLeft_essSurj : (kFlatQuotientLeft F).EssSurj where
  mem_essImage M := ⟨⟨M.obj.as, M.property⟩, ⟨Iso.refl _⟩⟩

/-! ### The bridge to the derived category -/

variable [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]

/-- `kFlatQuotientCompQIso` with its two reassociations and the lift comparison written out, so
that every junction matches a factor whose shift compatibility is an instance. -/
def kFlatQuotientCompQIsoAssoc :
    kFlatQuotient F ⋙ kFlatQ F ≅ kFlatComplexQ F :=
  (Functor.associator (kFlatQuotient F) (kFlatObjects F).ι DerivedCategory.Qh).symm ≪≫
    Functor.isoWhiskerRight ((kFlatObjects F).liftCompιIso
        ((kFlatComplexes F).ι ⋙ HomotopyCategory.quotient B (ComplexShape.up ℤ))
        (fun K ↦ K.2)) DerivedCategory.Qh ≪≫
      Functor.associator (kFlatComplexes F).ι
          (HomotopyCategory.quotient B (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
        Functor.isoWhiskerLeft (kFlatComplexes F).ι (DerivedCategory.quotientCompQhIso B)

omit [HasDerivedCategory A] [HasDerivedCategory D] in
/-- The reassociated bridge is `kFlatQuotientCompQIso`: the two associators and the lift
comparison are the identity on every object. -/
theorem kFlatQuotientCompQIsoAssoc_eq :
    kFlatQuotientCompQIsoAssoc F = kFlatQuotientCompQIso F := by
  ext K
  have h : ((kFlatObjects F).liftCompιIso
      ((kFlatComplexes F).ι ⋙ HomotopyCategory.quotient B (ComplexShape.up ℤ))
      (fun K ↦ K.2)).hom.app K = 𝟙 _ := rfl
  simp [kFlatQuotientCompQIsoAssoc, kFlatQuotientCompQIso, h]

omit [HasDerivedCategory A] [HasDerivedCategory D] in
/-- **The bridge `kFlatQuotient ⋙ kFlatQ ≅ kFlatComplexQ` is shift-compatible.**  Each of the
four factors of `kFlatQuotientCompQIsoAssoc` is: the two associators by
`CategoryTheory.NatTrans.CommShift.associator`, the lift comparison by
`kFlatQuotientCompι_commShift`, and `DerivedCategory.quotientCompQhIso` by Mathlib. -/
theorem kFlatQuotientCompQIso_commShift :
    letI := kFlatQuotient_commShift F
    NatTrans.CommShift (kFlatQuotientCompQIso F).hom ℤ := by
  let := kFlatQuotient_commShift F
  let := kFlatQuotientCompι_commShift F
  let : NatTrans.CommShift (kFlatQuotientCompQIsoAssoc F).hom ℤ := by
    unfold kFlatQuotientCompQIsoAssoc
    dsimp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
    infer_instance
  exact NatTrans.commShift_of_eq (congrArg Iso.hom (kFlatQuotientCompQIsoAssoc_eq F).symm)

end CochainComplex.KFlatBifunctor

end

end
