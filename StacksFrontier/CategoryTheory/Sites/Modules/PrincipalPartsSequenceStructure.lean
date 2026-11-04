module

public import StacksFrontier.CategoryTheory.Sites.Modules.PrincipalPartsJet
import StacksCore.Tactic.StacksAttribute

/-!
# The functorial sequence of principal parts, packaged

Let `φ : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site. Tag 09CW asserts
that the sheaves of first principal parts of the sheaves of `O₂`-modules assemble into a
functor sitting in a short exact sequence

`0 ⟶ Ω_{O₂/O₁} ⊗_{O₂} F ⟶ P¹_{O₂/O₁}(F) ⟶ F ⟶ 0`

natural in `F`, with the two maps pinned by their effect on the universal operator: the first
sends `x ⊗ d b` to `D (b x) - b D x` and the second sends `D x` to `x`.

The structure `PrincipalPartsSequence` records such a functor, whose values are the
representing objects `Functor.coreprX` of Tags 04BL and 09CT, together with the two natural
transformations, their formulas on the universal operator, and short exactness. The structure
is inhabited by `principalPartsSequenceOfSite`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.moduleSheaves`: sheaves of modules over the sheaf of
  rings underlying a sheaf of commutative rings.
* `AlgebraicGeometry.SheafOfModules.PrincipalPartsSequence`: the eight-field record of a
  functorial sequence of first principal parts together with the formulas pinning its two
  arrows and its short exactness.
* `AlgebraicGeometry.SheafOfModules.principalPartsSequenceOfSite`: the canonical such
  sequence, built from `principalPartsFunctor`, `principalPartsInclusion` and
  `principalPartsProjection`.
* `AlgebraicGeometry.SheafOfModules.principalPartsSequence`: a choice of such a sequence.

## Main results

* `AlgebraicGeometry.SheafOfModules.principalPartsSequence_nonempty`: **Tag 09CW**, in the
  form that asserts the whole functorial sequence exists.

## Implementation notes

The three identifications that make the fields line up are all definitional and are paid
once each, by `rfl` in `principalParts_obj` and by `exact` in the three section formulas:
`principalPartsFunctor φ' 1 |>.obj F` *is* `(differentialOperatorsFunctor φ' F 1).coreprX`,
`moduleOfDifferentialsOfSite O₁ O₂ φ` *is* `(derivationsFunctor O₁ O₂ φ).coreprX`, and
`universalDiffOp φ' F 1` *is* `(differentialOperatorsFunctor φ' F 1).coreprx.1`. Consequently
`eqToHom (principalParts_obj F).symm` is the identity, so the `eqToHom` conjugations in three
of the fields cost nothing: `Eq` is a `Prop`, so the field's proof is definitionally `rfl`
and `eqToHom` iota-reduces to `𝟙`. The fields are therefore stated with the conjugation
present — it is what makes the record expressible without a `coreprX`-valued functor — and
discharged by defeq-tolerant `exact`, never by `rw` or `simp`, which cannot see through it.

`principalParts` is a field rather than being defined to be `principalPartsFunctor` so that
the record states what Tag 09CW states: *some* functor whose values are the representing
objects of 09CT and which carries the two natural transformations. `principalParts_obj` is
what ties it back down.

Universes. The site is `C : Type u` with `Category.{v} C`, the structure sheaves are
`CommRingCat.{w}`-valued and coefficient modules live in `SheafOfModules.{max u v w m}` for a
free `m`. This is forced, not chosen: it is the universe in which Tags 04BL and 09CT are
corepresentable at all, since the hom types of `SheafOfModules.{t}` on this site lie in
`Type (max u v t)` and the representing objects are built from the structure sheaves. Nothing
is narrowed — `u`, `v`, `w`, `m` are free and the site is not assumed small. The sheafification
hypotheses are exactly those of `PrincipalPartsJet`.

## References

* [Stacks Project, Tag 09CW](https://stacks.math.columbia.edu/tag/09CW)
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), relative
  differentials, and [Tag 09CT](https://stacks.math.columbia.edu/tag/09CT), principal parts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w m

namespace AlgebraicGeometry.SheafOfModules

section PrincipalPartsSequence

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w m}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w m}]

/-- Sheaves of modules over the sheaf of rings underlying a sheaf of commutative rings. -/
abbrev moduleSheaves (O : Sheaf J CommRingCat.{w}) :=
  _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O)

/-- A functorial sequence whose terms are relative differentials tensored with
the coefficient module, first principal parts, and the coefficient module. -/
structure PrincipalPartsSequence (O₁ O₂ : Sheaf J CommRingCat.{w})
    (φ : O₁ ⟶ O₂) where
  /-- The functor of first principal parts. -/
  principalParts : moduleSheaves.{v, u, w, m} O₂ ⥤ moduleSheaves.{v, u, w, m} O₂
  /-- The value of `principalParts` at `F` is the object corepresenting differential operators
  of order at most `1` on `F`. -/
  principalParts_obj (F : moduleSheaves.{v, u, w, m} O₂) :
    letI := differentialOperatorsFunctor_isCorepresentable.{v, u, w, m}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ) F 1;
    principalParts.obj F =
      (differentialOperatorsFunctor.{v, u, w, m}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)
        F 1).coreprX
  /-- The image of a morphism `f : F ⟶ G` under `principalParts` sends the universal operator
  of `F` at `x` to the universal operator of `G` at `f x`. -/
  principalParts_map_universal {F G : moduleSheaves.{v, u, w, m} O₂}
      (f : F ⟶ G) (X : Cᵒᵖ) (x : F.val.obj X) :
    letI := differentialOperatorsFunctor_isCorepresentable.{v, u, w, m}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ) F 1;
    letI := differentialOperatorsFunctor_isCorepresentable.{v, u, w, m}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ) G 1;
    ((principalParts.map f).val.app X).hom
      (((eqToHom (principalParts_obj F).symm).val.app X).hom
        ((differentialOperatorsFunctor.{v, u, w, m}
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)
          F 1).coreprx.1 X x)) =
      ((eqToHom (principalParts_obj G).symm).val.app X).hom
        ((differentialOperatorsFunctor.{v, u, w, m}
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)
          G 1).coreprx.1 X (((f.val.app X).hom) x))
  /-- The natural transformation `Ω_{O₂/O₁} ⊗_{O₂} F ⟶ P¹_{O₂/O₁}(F)`. -/
  inclusion : (Stacks.SheafOfModules.Tensor.sheafTensor O₂).flip.obj
      (derivationsFunctor.{m} O₁ O₂ φ).coreprX ⟶ principalParts
  /-- The inclusion sends `x ⊗ d b` to `D (b x) - b D x`, where `D` is the universal
  operator. -/
  inclusion_universal (F : moduleSheaves.{v, u, w, m} O₂)
      (X : Cᵒᵖ) (b : O₂.obj.obj X) (x : F.val.obj X) :
    letI := differentialOperatorsFunctor_isCorepresentable.{v, u, w, m}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ) F 1;
    ((inclusion.app F).val.app X).hom
      (((toSheafify J
        ((PresheafOfModules.tensorRight
          (O := O₂.obj)
          (derivationsFunctor.{m} O₁ O₂ φ).coreprX.val).obj
            F.val).presheaf).app X).hom
        (x ⊗ₜ[_] ((derivationsFunctor.{m} O₁ O₂ φ).coreprx.d b))) =
      ((eqToHom (principalParts_obj F).symm).val.app X).hom
        ((differentialOperatorsFunctor.{v, u, w, m}
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)
          F 1).coreprx.1 X
            ((show (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj.obj X from b) • x)) -
        (show (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj.obj X from b) •
          ((eqToHom (principalParts_obj F).symm).val.app X).hom
          ((differentialOperatorsFunctor.{v, u, w, m}
            ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)
            F 1).coreprx.1 X x)
  /-- The natural transformation `P¹_{O₂/O₁}(F) ⟶ F`. -/
  projection : principalParts ⟶ 𝟭 (moduleSheaves.{v, u, w, m} O₂)
  /-- The projection sends `D x` to `x`, where `D` is the universal operator. -/
  projection_universal (F : moduleSheaves.{v, u, w, m} O₂)
      (X : Cᵒᵖ) (x : F.val.obj X) :
    letI := differentialOperatorsFunctor_isCorepresentable.{v, u, w, m}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ) F 1;
    ((projection.app F).val.app X).hom
      (((eqToHom (principalParts_obj F).symm).val.app X).hom
        ((differentialOperatorsFunctor.{v, u, w, m}
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)
          F 1).coreprx.1 X x)) = x
  /-- For every `F`, the inclusion followed by the projection is a short exact sequence. -/
  shortExact (F : moduleSheaves.{v, u, w, m} O₂) :
    ∃ h : inclusion.app F ≫ projection.app F = 0,
      (ShortComplex.mk (inclusion.app F) (projection.app F) h).ShortExact

/-- The canonical functorial sequence of first principal parts: the functor is
`principalPartsFunctor`, the inclusion is `principalPartsInclusion` and the projection is
`principalPartsProjection`. -/
noncomputable def principalPartsSequenceOfSite (O₁ O₂ : Sheaf J CommRingCat.{w})
    (φ : O₁ ⟶ O₂) : PrincipalPartsSequence.{v, u, w, m} O₁ O₂ φ where
  principalParts := principalPartsFunctor.{v, u, w, m} (underlyingRingSheafMapOfSite φ) 1
  principalParts_obj _ := rfl
  principalParts_map_universal f X x :=
    principalPartsMap_universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) f 1 X x
  inclusion := principalPartsInclusion.{v, u, w, m} φ
  inclusion_universal F X b x :=
    principalPartsInclusion_toSheafify_tmul_d.{v, u, w, m} φ F X x b
  projection := principalPartsProjection.{v, u, w, m} (underlyingRingSheafMapOfSite φ) 1
  projection_universal F X x :=
    principalPartsProjection_universalDiffOp.{v, u, w, m}
      (underlyingRingSheafMapOfSite φ) 1 F X x
  shortExact F := exists_shortExact_principalPartsSequence'.{v, u, w, m} φ F

/-- The functorial short exact sequence of first principal parts exists. -/
@[stacks 09CW "the tag's OWN assertion: a functorial first-principal-parts sequence \
exists, i.e. the eight-field record is inhabited. The individual clauses of field 8 are \
carried separately in `PrincipalPartsJet.lean` and `PrincipalPartsSequence.lean`.",
  sga "6 II AppII.1.2.4" "n = 1"]
theorem principalPartsSequence_nonempty (O₁ O₂ : Sheaf J CommRingCat.{w})
    (φ : O₁ ⟶ O₂) : Nonempty (PrincipalPartsSequence.{v, u, w, m} O₁ O₂ φ) :=
  ⟨principalPartsSequenceOfSite.{v, u, w, m} O₁ O₂ φ⟩

/-- The chosen functorial sequence of first principal parts. -/
noncomputable def principalPartsSequence (O₁ O₂ : Sheaf J CommRingCat.{w})
    (φ : O₁ ⟶ O₂) : PrincipalPartsSequence.{v, u, w, m} O₁ O₂ φ :=
  Classical.choice (principalPartsSequence_nonempty.{v, u, w, m} O₁ O₂ φ)

end PrincipalPartsSequence

end AlgebraicGeometry.SheafOfModules

end
