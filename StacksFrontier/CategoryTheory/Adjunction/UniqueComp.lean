module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# Uniqueness of a left adjoint and composition of adjunctions

Let `adj₀₁ : F₀₁ ⊣ G₁₀` and `adj₁₂ : F₁₂ ⊣ G₂₁` be adjunctions, let `adj₀₂ : F₀₂ ⊣ G₂₀` be a
third one, and let `e : G₂₁ ⋙ G₁₀ ≅ G₂₀` compare the composite of the two right adjoints with
the third.  Then `F₀₁ ⋙ F₁₂` and `F₀₂` are two left adjoints of `G₂₀` — the first by composing
the two adjunctions and reading the resulting right adjoint through `e` — so they are
isomorphic in two *a priori* different ways: by
`CategoryTheory.Adjunction.leftAdjointUniq`, the uniqueness of a left adjoint, and by
`CategoryTheory.Adjunction.leftAdjointCompIso`, the induced comparison of left adjoints.

This file identifies them.  The point of the identification is that it is
`leftAdjointCompIso` for which Mathlib proves the pseudofunctor coherences —
`CategoryTheory.Adjunction.leftAdjointCompIso_assoc`,
`CategoryTheory.Adjunction.leftAdjointCompIso_comp_id` and
`CategoryTheory.Adjunction.leftAdjointCompIso_id_comp` — so a comparison of left adjoints
*defined* by uniqueness inherits all of them, each from the corresponding coherence of the
comparisons `e` of right adjoints.

## Main results

* `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_comp`: the comparison of
  `F₀₁ ⋙ F₁₂` with `F₀₂` given by uniqueness of a left adjoint of `G₂₀` is the comparison
  induced by `e`.
* `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_comp_assoc`: consequently the
  associativity coherence for three composable adjunctions, in the uniqueness form.
* `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_comp_id` and
  `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_id_comp`: likewise the two unit
  laws.
* `CategoryTheory.Adjunction.leftAdjointUniq_comp`: for two composable pairs of adjunctions
  with a common right adjoint in each pair, the comparison of the two left adjoints of the
  composite right adjoint is the whiskered composite of the two comparisons.
* `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_congr`: transporting the right
  adjoints of two adjunctions along one and the same isomorphism leaves the comparison of
  their left adjoints unchanged.
* `CategoryTheory.Adjunction.eq_ofNatIsoRight_of_conjugateEquiv_id`: two adjunctions with the
  same left adjoint are transports of one another along the isomorphism of right adjoints that
  the mate of the identity exhibits.
* `CategoryTheory.Adjunction.leftAdjointUniq_hom_comp_whisker`: the hexagon those two
  statements combine to — the comparison of two *systems* of left adjoints is compatible with
  composition, the composition isomorphism on the left-adjoint side being the one induced by a
  composition isomorphism `e` of the right adjoints, provided the second system's adjunction
  for the composite is the composite of its adjunctions read through `e`.
* `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoLeft`: retyping the left adjoint of the
  second adjunction post-composes the comparison with that retyping.
* `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoLeft_left`: retyping the left adjoint of
  the *first* adjunction pre-composes the comparison with the inverse of that retyping.
* `CategoryTheory.leftAdjointUniq_transport`: conjugating two adjunctions with a common right
  adjoint by one and the same pair of equivalences whiskers their comparison and changes it in
  no other way.  This is what makes a comparison of left adjoints constructed on one pair of
  categories available on an equivalent pair.

## Implementation notes

Both isomorphisms are values of `CategoryTheory.conjugateIsoEquiv`, so it suffices to compare
their conjugates, and `CategoryTheory.conjugateEquiv` is a bijection.  The conjugate of the
uniqueness comparison is `e.inv` by
`Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom`, and the conjugate of
the induced comparison is `e.inv` by definition.

The three coherences are then Mathlib's, with no further work: the hypothesis of each is a
coherence of the comparisons of *right* adjoints, which is where such a coherence is usually
available, since right adjoints are the ones given by an explicit construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]

section

variable {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
  {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀}

/-- **The comparison of two left adjoints of one functor is the comparison induced by the
comparison of the right adjoints.**

`F₀₁ ⋙ F₁₂` is left adjoint to `G₂₁ ⋙ G₁₀`, hence to `G₂₀` through `e`, and `F₀₂` is left
adjoint to `G₂₀`; so the two are compared both by uniqueness of a left adjoint and by
`CategoryTheory.Adjunction.leftAdjointCompIso`.  The two comparisons agree. -/
theorem leftAdjointUniq_ofNatIsoRight_comp (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁)
    (adj₀₂ : F₀₂ ⊣ G₂₀) (e : G₂₁ ⋙ G₁₀ ≅ G₂₀) :
    leftAdjointUniq ((adj₀₁.comp adj₁₂).ofNatIsoRight e) adj₀₂ =
      leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e := by
  refine Iso.ext ((conjugateEquiv adj₀₂ (adj₀₁.comp adj₁₂)).injective ?_)
  rw [Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom]
  simp [leftAdjointCompIso]

end

section

variable
  {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃} {F₀₂ : C₀ ⥤ C₂} {F₁₃ : C₁ ⥤ C₃} {F₀₃ : C₀ ⥤ C₃}
  {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₃₂ : C₃ ⥤ C₂} {G₂₀ : C₂ ⥤ C₀} {G₃₁ : C₃ ⥤ C₁} {G₃₀ : C₃ ⥤ C₀}
  (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₂₃ : F₂₃ ⊣ G₃₂) (adj₀₂ : F₀₂ ⊣ G₂₀)
  (adj₁₃ : F₁₃ ⊣ G₃₁) (adj₀₃ : F₀₃ ⊣ G₃₀)

/-- **The associativity coherence of the comparison of left adjoints given by uniqueness.**

For three composable adjunctions and comparisons `e` of the composites of the right adjoints
satisfying the associativity coherence, the comparisons of the left adjoints obtained from
uniqueness of a left adjoint satisfy the corresponding coherence.

This is `CategoryTheory.Adjunction.leftAdjointCompIso_assoc` read through
`CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_comp`. -/
theorem leftAdjointUniq_ofNatIsoRight_comp_assoc
    (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) (e₁₂₃ : G₃₂ ⋙ G₂₁ ≅ G₃₁)
    (e₀₁₃ : G₃₁ ⋙ G₁₀ ≅ G₃₀) (e₀₂₃ : G₃₂ ⋙ G₂₀ ≅ G₃₀)
    (h : isoWhiskerLeft G₃₂ e₀₁₂ ≪≫ e₀₂₃ =
      (associator _ _ _).symm ≪≫ isoWhiskerRight e₁₂₃ _ ≪≫ e₀₁₃) :
    isoWhiskerLeft F₀₁
          (leftAdjointUniq ((adj₁₂.comp adj₂₃).ofNatIsoRight e₁₂₃) adj₁₃) ≪≫
        leftAdjointUniq ((adj₀₁.comp adj₁₃).ofNatIsoRight e₀₁₃) adj₀₃ =
      (associator _ _ _).symm ≪≫
        isoWhiskerRight
            (leftAdjointUniq ((adj₀₁.comp adj₁₂).ofNatIsoRight e₀₁₂) adj₀₂) F₂₃ ≪≫
          leftAdjointUniq ((adj₀₂.comp adj₂₃).ofNatIsoRight e₀₂₃) adj₀₃ := by
  simp only [leftAdjointUniq_ofNatIsoRight_comp]
  exact leftAdjointCompIso_assoc adj₀₁ adj₁₂ adj₂₃ adj₀₂ adj₁₃ adj₀₃ e₀₁₂ e₁₂₃ e₀₁₃ e₀₂₃ h

end

/-- **The right unit law of the comparison of left adjoints given by uniqueness.**  If the
right adjoint composed on the inside is isomorphic to the identity compatibly with the
comparison, then the comparison of the left adjoints is the whiskered identity comparison. -/
theorem leftAdjointUniq_ofNatIsoRight_comp_id
    {F₀₁ : C₀ ⥤ C₁} {F₁₁' : C₁ ⥤ C₁} {G₁₀ : C₁ ⥤ C₀} {G₁'₁ : C₁ ⥤ C₁}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₁' : F₁₁' ⊣ G₁'₁)
    (e₀₁₁' : G₁'₁ ⋙ G₁₀ ≅ G₁₀) (e₁'₁ : G₁'₁ ≅ 𝟭 _)
    (h : e₀₁₁' = isoWhiskerRight e₁'₁ G₁₀ ≪≫ leftUnitor G₁₀) :
    leftAdjointUniq ((adj₀₁.comp adj₁₁').ofNatIsoRight e₀₁₁') adj₀₁ =
      isoWhiskerLeft _ (leftAdjointIdIso adj₁₁' e₁'₁) ≪≫ rightUnitor F₀₁ := by
  rw [leftAdjointUniq_ofNatIsoRight_comp]
  exact leftAdjointCompIso_comp_id adj₀₁ adj₁₁' e₀₁₁' e₁'₁ h

/-- **The left unit law of the comparison of left adjoints given by uniqueness.** -/
theorem leftAdjointUniq_ofNatIsoRight_id_comp
    {F₀₀' : C₀ ⥤ C₀} {F₀'₁ : C₀ ⥤ C₁} {G₀'₀ : C₀ ⥤ C₀} {G₁₀' : C₁ ⥤ C₀}
    (adj₀₀' : F₀₀' ⊣ G₀'₀) (adj₀'₁ : F₀'₁ ⊣ G₁₀')
    (e₀₀'₁ : G₁₀' ⋙ G₀'₀ ≅ G₁₀') (e₀'₀ : G₀'₀ ≅ 𝟭 _)
    (h : e₀₀'₁ = isoWhiskerLeft G₁₀' e₀'₀ ≪≫ rightUnitor G₁₀') :
    leftAdjointUniq ((adj₀₀'.comp adj₀'₁).ofNatIsoRight e₀₀'₁) adj₀'₁ =
      isoWhiskerRight (leftAdjointIdIso adj₀₀' e₀'₀) F₀'₁ ≪≫ leftUnitor F₀'₁ := by
  rw [leftAdjointUniq_ofNatIsoRight_comp]
  exact leftAdjointCompIso_id_comp adj₀₀' adj₀'₁ e₀₀'₁ e₀'₀ h

/-- **The comparison of two left adjoints of a composite is the composite of the two
comparisons.** If `F₀₁` and `F₀₁'` are both left adjoint to `G₁₀`, and `F₁₂` and `F₁₂'` are
both left adjoint to `G₂₁`, then the comparison of the two left adjoints of `G₂₁ ⋙ G₁₀` given
by uniqueness is the whiskered composite of the two comparisons. -/
theorem leftAdjointUniq_comp {F₀₁ F₀₁' : C₀ ⥤ C₁} {G₁₀ : C₁ ⥤ C₀}
    {F₁₂ F₁₂' : C₁ ⥤ C₂} {G₂₁ : C₂ ⥤ C₁}
    (adjA₁ : F₀₁ ⊣ G₁₀) (adjB₁ : F₀₁' ⊣ G₁₀) (adjA₂ : F₁₂ ⊣ G₂₁) (adjB₂ : F₁₂' ⊣ G₂₁) :
    (leftAdjointUniq (adjA₁.comp adjA₂) (adjB₁.comp adjB₂)).hom =
      Functor.whiskerRight (leftAdjointUniq adjA₁ adjB₁).hom F₁₂ ≫
        Functor.whiskerLeft F₀₁' (leftAdjointUniq adjA₂ adjB₂).hom := by
  ext x
  apply ((adjA₁.comp adjA₂).homEquiv x _).injective
  rw [homEquiv_leftAdjointUniq_hom_app]
  simp only [homEquiv_unit, comp_unit_app, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_map, Functor.comp_obj, Functor.map_comp,
    Category.assoc]
  rw [← Functor.map_comp G₁₀, ← Functor.map_comp G₁₀, ← Category.assoc,
    adjA₂.unit_naturality, Category.assoc, unit_leftAdjointUniq_hom_app adjA₂ adjB₂,
    Functor.map_comp, ← Category.assoc, unit_leftAdjointUniq_hom_app adjA₁ adjB₁]

/-- **Transporting the right adjoints of two adjunctions along one and the same isomorphism
does not change the comparison of their left adjoints.**

The comparison is characterised by the equation `unit₁ ≫ G.map (comparison) = unit₂` on units,
and transporting along `e` multiplies both sides of that equation by the isomorphism
`e.hom`. -/
theorem leftAdjointUniq_ofNatIsoRight_congr {F F' : C₀ ⥤ C₁} {G G' : C₁ ⥤ C₀}
    (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G) (e : G ≅ G') :
    leftAdjointUniq (adj₁.ofNatIsoRight e) (adj₂.ofNatIsoRight e) =
      leftAdjointUniq adj₁ adj₂ := by
  refine Iso.ext (NatTrans.ext (funext fun x => ?_))
  refine (adj₁.homEquiv x (F'.obj x)).injective ?_
  rw [homEquiv_unit, homEquiv_unit, unit_leftAdjointUniq_hom_app adj₁ adj₂]
  have h := unit_leftAdjointUniq_hom_app (adj₁.ofNatIsoRight e) (adj₂.ofNatIsoRight e) x
  simp only [ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.assoc] at h
  rw [← e.hom.naturality, ← Category.assoc] at h
  exact (cancel_mono (e.hom.app (F'.obj x))).mp h

/-- **Two adjunctions with the same left adjoint are transports of one another along the
isomorphism of right adjoints their mate exhibits.**

The mate of the identity of the common left adjoint is a map `R ⟶ R'` of the two right
adjoints; if it is an isomorphism `e`, the second adjunction is the first read through `e`.
Both sides have the same unit, by the transposed form
`CategoryTheory.unit_conjugateEquiv` of the hypothesis. -/
theorem eq_ofNatIsoRight_of_conjugateEquiv_id {L : C₀ ⥤ C₁} {R R' : C₁ ⥤ C₀}
    (adj : L ⊣ R) (adj' : L ⊣ R') (e : R ≅ R')
    (h : conjugateEquiv adj adj' (𝟙 L) = e.hom) :
    adj' = adj.ofNatIsoRight e := by
  refine Adjunction.ext (NatTrans.ext (funext fun c => ?_))
  have hc := unit_conjugateEquiv adj adj' (𝟙 L) c
  rw [h] at hc
  simpa using hc.symm

/-- **The comparison of two systems of left adjoints is compatible with composition**, in the
form in which a composition isomorphism of *right* adjoints presents it.

Let `G₁₀` and `G₂₁` be two composable right adjoints with two left adjoints each — `F₀₁, F₀₁'`
and `F₁₂, F₁₂'` — and let `G₂₀` be a third right adjoint with left adjoints `F₀₂` and
`F₀₁' ⋙ F₁₂'`, the composite of the two second ones; let `e : G₂₁ ⋙ G₁₀ ≅ G₂₀` compare the
composite of the first two right adjoints with the third.  Assume that the adjunction of
`F₀₁' ⋙ F₁₂'` with `G₂₀` is the composite of the two, read through `e`.

Then the comparison `F₀₂ ≅ F₀₁' ⋙ F₁₂'` of the two left adjoints of `G₂₀` factors as the
composition isomorphism `F₀₂ ≅ F₀₁ ⋙ F₁₂` induced by `e` followed by the horizontal composite
of the two comparisons.  This is the hexagon a cocycle condition for a system of comparisons
needs; its only input beyond `CategoryTheory.Adjunction.leftAdjointUniq_comp` and
`CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_congr` is the hypothesis `hcomp`, the
compatibility of the second system of adjunctions with composition. -/
theorem leftAdjointUniq_hom_comp_whisker {F₀₁ F₀₁' : C₀ ⥤ C₁} {G₁₀ : C₁ ⥤ C₀}
    {F₁₂ F₁₂' : C₁ ⥤ C₂} {G₂₁ : C₂ ⥤ C₁} {F₀₂ : C₀ ⥤ C₂} {G₂₀ : C₂ ⥤ C₀}
    (adjA₁ : F₀₁ ⊣ G₁₀) (adjB₁ : F₀₁' ⊣ G₁₀) (adjA₂ : F₁₂ ⊣ G₂₁) (adjB₂ : F₁₂' ⊣ G₂₁)
    (adjA : F₀₂ ⊣ G₂₀) (adjB : F₀₁' ⋙ F₁₂' ⊣ G₂₀) (e : G₂₁ ⋙ G₁₀ ≅ G₂₀)
    (hcomp : adjB = (adjB₁.comp adjB₂).ofNatIsoRight e) :
    (leftAdjointUniq adjA ((adjA₁.comp adjA₂).ofNatIsoRight e)).hom ≫
        Functor.whiskerRight (leftAdjointUniq adjA₁ adjB₁).hom F₁₂ ≫
          Functor.whiskerLeft F₀₁' (leftAdjointUniq adjA₂ adjB₂).hom =
      (leftAdjointUniq adjA adjB).hom := by
  subst hcomp
  rw [← leftAdjointUniq_comp adjA₁ adjB₁ adjA₂ adjB₂,
    ← leftAdjointUniq_ofNatIsoRight_congr (adjA₁.comp adjA₂) (adjB₁.comp adjB₂) e,
    leftAdjointUniq_trans]

/-- Reading an adjunction through the identity isomorphism of its right adjoint returns the
adjunction. -/
theorem ofNatIsoRight_refl {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} (adj : L ⊣ R) :
    adj.ofNatIsoRight (Iso.refl R) = adj := by
  apply Adjunction.ext
  simp [Adjunction.ofNatIsoRight]

/-- **Retyping the left adjoint of the second adjunction post-composes the comparison.**  If
the second of two adjunctions with a common right adjoint is read through an isomorphism of
its left adjoint, the comparison of the two left adjoints acquires that isomorphism as a last
factor. -/
theorem leftAdjointUniq_ofNatIsoLeft {F F' F'' : C₀ ⥤ C₁} {G : C₁ ⥤ C₀}
    (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G) (ι : F' ≅ F'') :
    leftAdjointUniq adj₁ (adj₂.ofNatIsoLeft ι) = leftAdjointUniq adj₁ adj₂ ≪≫ ι := by
  refine Iso.ext (NatTrans.ext (funext fun x => ?_))
  refine (adj₁.homEquiv x _).injective ?_
  rw [homEquiv_leftAdjointUniq_hom_app]
  simp only [Iso.trans_hom, NatTrans.comp_app, homEquiv_unit, Functor.map_comp,
    ofNatIsoLeft_unit, Functor.whiskerRight_app, ← Category.assoc]
  rw [unit_leftAdjointUniq_hom_app adj₁ adj₂]

/-- **Retyping the left adjoint of the first adjunction pre-composes the comparison with the
inverse of that retyping.**  The companion of
`CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoLeft` for the other argument: if `F` and
`F''` are both left adjoint to `G` and `e : F ≅ F'`, then `F'` is left adjoint to `G` too, and
the comparison of `F'` with `F''` given by uniqueness of a left adjoint is `e` inverted
followed by the comparison of `F` with `F''`. -/
theorem leftAdjointUniq_ofNatIsoLeft_left {F F' F'' : C₀ ⥤ C₁} {G : C₁ ⥤ C₀}
    (adj : F ⊣ G) (e : F ≅ F') (adj' : F'' ⊣ G) :
    leftAdjointUniq (adj.ofNatIsoLeft e) adj' = e.symm ≪≫ leftAdjointUniq adj adj' := by
  ext x
  apply ((adj.ofNatIsoLeft e).homEquiv _ _).injective
  rw [homEquiv_leftAdjointUniq_hom_app, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    homEquiv_ofNatIsoLeft_apply, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp,
    homEquiv_leftAdjointUniq_hom_app]

end CategoryTheory.Adjunction

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {CX : Type u₁} [Category.{v₁} CX] {DX : Type u₂} [Category.{v₂} DX]
  {CY : Type u₃} [Category.{v₃} CY] {DY : Type u₄} [Category.{v₄} DY]

/-- **Conjugating two adjunctions with a common right adjoint by one and the same pair of
equivalences does not change the comparison of their left adjoints**: it only whiskers it.

Conjugation is composition with the adjunction of each equivalence, and
`CategoryTheory.Adjunction.leftAdjointUniq_comp` turns the comparison of the two composites
into a horizontal composite of three comparisons, of which the two outer ones are comparisons
of an adjunction with itself. -/
theorem leftAdjointUniq_transport (eX : CX ≌ DX) (eY : CY ≌ DY)
    {L₁ L₂ : CY ⥤ CX} {R : CX ⥤ CY} (adj₁ : L₁ ⊣ R) (adj₂ : L₂ ⊣ R) :
    Adjunction.leftAdjointUniq ((eY.symm.toAdjunction.comp adj₁).comp eX.toAdjunction)
        ((eY.symm.toAdjunction.comp adj₂).comp eX.toAdjunction) =
      Functor.isoWhiskerLeft eY.inverse
        (Functor.isoWhiskerRight (Adjunction.leftAdjointUniq adj₁ adj₂) eX.functor) := by
  refine Iso.ext ?_
  rw [Adjunction.leftAdjointUniq_comp, Adjunction.leftAdjointUniq_comp,
    Adjunction.leftAdjointUniq_refl, Adjunction.leftAdjointUniq_refl,
    Functor.whiskerLeft_id', Category.comp_id, Functor.whiskerRight_id', Category.id_comp]
  rfl

end CategoryTheory

end
