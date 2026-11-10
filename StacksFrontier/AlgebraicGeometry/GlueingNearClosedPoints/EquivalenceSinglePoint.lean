module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Germ

/-!
# The canonical restriction functor is an equivalence for a one-element family of points

[Stacks, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q) asserts that, for a finite family
`s : I → S` of pairwise distinct closed points of a scheme `S` whose open complement has
quasi-compact inclusion, `AlgebraicGeometry.canonicalRestrictionFunctor` from schemes of finite
presentation over `S` to gluing data near the family is an *equivalence* of categories.  This
file proves that assertion when the index type `I` has exactly one element: the family is then a
single closed point, its open complement is the punctured scheme, and the assertion is
[Stacks, Tag 0BPA], which is available as
`AlgebraicGeometry.GlueingNearPoint.restrictionFunctorAtPoint_isEquivalence`.

Only the shape of the two statements has to be reconciled: the gluing data of Tag 0E8Q has one
component for each index, written as an object of a dependent product category, while the gluing
data of Tag 0BPA has a single component.  Evaluating at the unique index is a functor
`AlgebraicGeometry.glueingDataEval` between the two categories of gluing data which is full and
faithful, and whose composite with the canonical restriction functor of Tag 0E8Q is, on the nose,
the canonical restriction functor of Tag 0BPA.  A functor whose composite with a full and faithful
functor is an equivalence is itself an equivalence, which is
`AlgebraicGeometry.isEquivalence_of_comp_fullyFaithful`.

The general case, for a family of two or more points, is **not** proved here.  It is proved in
the source by induction on the family: one peels off one point `s i₀` and applies Tag 0BPA to it
relative to the smaller ambient scheme `S ∖ {s i | i ≠ i₀}`, whose own open complement of
`s i₀` is the open complement of the whole family.  Carrying that out requires identifying the
gluing data for the whole family with gluing data for the smaller family whose component over
the smaller ambient scheme has itself been decomposed, which is a substantially larger
undertaking, carried out in `EquivalenceGeneral.lean`.

## Main definitions

* `AlgebraicGeometry.glueingDataEval`: evaluation of gluing data near a one-element family of
  closed points at the unique index, landing in the gluing data near the single point of the
  family.

## Main results

* `AlgebraicGeometry.isEquivalence_of_comp_fullyFaithful`: a functor whose composite with a full
  and faithful functor is an equivalence is an equivalence.
* `AlgebraicGeometry.complementOfClosedPoints_eq_puncturedOpen`: the open complement of a
  one-element family of closed points is the complement of its unique point.
* `AlgebraicGeometry.canonicalRestrictionFunctor_isEquivalence_of_unique`: **Stacks Project,
  Tag 0E8Q**, for a family of closed points indexed by a type with a unique element: the
  canonical restriction functor is an equivalence of categories.

## References

* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
* [Stacks Project, Lemma 32.14.1 (0BPA)](https://stacks.math.columbia.edu/tag/0BPA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace AlgebraicGeometry

/-! ### Generalities -/

/-- A functor whose composite with a full and faithful functor is an equivalence is itself an
equivalence of categories. -/
theorem isEquivalence_of_comp_fullyFaithful {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] (F : A ⥤ B) (G : B ⥤ C)
    [G.Full] [G.Faithful] [(F ⋙ G).IsEquivalence] : F.IsEquivalence where
  faithful := ⟨fun {_ _} f g h => (F ⋙ G).map_injective (by
    simp only [Functor.comp_map]
    exact congrArg G.map h)⟩
  full := ⟨fun {_ _} f => ⟨(F ⋙ G).preimage (G.map f),
    G.map_injective ((F ⋙ G).map_preimage (G.map f))⟩⟩
  essSurj := ⟨fun Z => ⟨(F ⋙ G).objPreimage (G.obj Z),
    ⟨G.preimageIso ((F ⋙ G).objObjPreimageIso (G.obj Z))⟩⟩⟩

/-- A morphism between two objects of a product category indexed by a type with a unique
element, given its unique component. -/
def piUniqueHom {I : Type u₁} [Unique I] {C : I → Type u₂} [∀ i, Category.{v₁} (C i)]
    {X Y : ∀ i, C i} (r : X default ⟶ Y default) (i : I) : X i ⟶ Y i := by
  obtain rfl := Unique.eq_default i
  exact r

/-- The morphism `piUniqueHom r` has component `r` at the unique index. -/
@[simp]
theorem piUniqueHom_default {I : Type u₁} [Unique I] {C : I → Type u₂}
    [∀ i, Category.{v₁} (C i)] {X Y : ∀ i, C i} (r : X default ⟶ Y default) :
    piUniqueHom r default = r :=
  rfl

/-! ### Gluing data near a one-element family of closed points -/

variable {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
  (hs : ∀ i, s i ∈ closedPoints S)

/-- Evaluation of gluing data near a family of closed points at a unique index: the component
over the open complement is kept, and the single component over the local scheme at the unique
point of the family, together with the single comparison isomorphism, is extracted from the
family of them. -/
noncomputable def glueingDataEval [Unique I] :
    glueingData s hs ⥤
      GlueingNearPoint.glueingDataNearPoint S (complementOfClosedPoints s hs) (s default) where
  obj Z := ⟨⟨Z.obj.left, Z.obj.right default, Z.obj.hom default⟩,
    ((isIso_pi_iff _).mp Z.property) default⟩
  map f := ⟨⟨f.hom.left, f.hom.right default, congrFun f.hom.w default⟩⟩

/-- Evaluation at the unique index is faithful on gluing data near a one-element family. -/
instance [Unique I] : (glueingDataEval s hs).Faithful where
  map_injective {_ _} f g h := by
    refine ObjectProperty.hom_ext _ (Comma.hom_ext _ _ (congrArg (fun k => k.hom.left) h) ?_)
    refine funext fun i => ?_
    obtain rfl := Unique.eq_default i
    exact congrArg (fun k => k.hom.right) h

/-- Evaluation at the unique index is full on gluing data near a one-element family. -/
instance [Unique I] : (glueingDataEval s hs).Full where
  map_surjective {_ _} φ := by
    refine ⟨ObjectProperty.homMk ⟨φ.hom.left, piUniqueHom φ.hom.right, ?_⟩, ?_⟩
    · refine funext fun i => ?_
      obtain rfl := Unique.eq_default i
      exact φ.hom.w
    · exact ObjectProperty.hom_ext _ (Comma.hom_ext _ _ rfl rfl)

/-- Evaluating the canonical restriction functor of a one-element family of closed points at the
unique index gives the canonical restriction functor at the single point of the family. -/
theorem canonicalRestrictionFunctor_comp_glueingDataEval [Unique I] :
    canonicalRestrictionFunctor s hs ⋙ glueingDataEval s hs =
      GlueingNearPoint.restrictionFunctorAtPoint S (complementOfClosedPoints s hs)
        (s default) :=
  rfl

/-- The open complement of a one-element family of closed points is the open complement of its
unique point. -/
theorem complementOfClosedPoints_eq_puncturedOpen [Unique I] :
    complementOfClosedPoints s hs =
      GlueingNearPoint.puncturedOpen (mem_closedPoints_iff.mp (hs default)) := by
  apply TopologicalSpace.Opens.ext
  change ⋂ i, ({s i}ᶜ : Set S) = ({s default}ᶜ : Set S)
  refine Set.eq_of_subset_of_subset (Set.iInter_subset _ default) fun x hx => ?_
  refine Set.mem_iInter.mpr fun i => ?_
  obtain rfl := Unique.eq_default i
  exact hx

/-- **Stacks Project, Lemma 32.14.1 (0BPA)**, stated for an open subscheme which is only assumed
to be *equal* to the open complement of the closed point: restriction to it and to the local
scheme at the point is an equivalence onto the category of gluing data. -/
theorem restrictionFunctorAtPoint_isEquivalence_of_eq {t : S} (V : S.Opens)
    (ht : IsClosed ({t} : Set S)) (hV : V = GlueingNearPoint.puncturedOpen ht)
    (hqc : QuasiCompact V.ι) :
    (GlueingNearPoint.restrictionFunctorAtPoint S V t).IsEquivalence := by
  subst hV
  exact GlueingNearPoint.restrictionFunctorAtPoint_isEquivalence S t ht hqc

/-- **Stacks Project, Tag 0E8Q**, for a family of closed points indexed by a type with a unique
element: the canonical restriction functor from schemes of finite presentation over `S` to gluing
data near the family is an equivalence of categories.

The family is a single closed point whose open complement has quasi-compact inclusion, so this is
[Stacks, Tag 0BPA] after evaluating the one-index gluing data at its unique index. -/
@[stacks 0E8Q "equivalence, special case of a one-element family of points"]
theorem canonicalRestrictionFunctor_isEquivalence_of_unique [Unique I]
    (hqc : QuasiCompact (complementOfClosedPoints s hs).ι) :
    (canonicalRestrictionFunctor s hs).IsEquivalence := by
  have h : (canonicalRestrictionFunctor s hs ⋙ glueingDataEval s hs).IsEquivalence := by
    rw [canonicalRestrictionFunctor_comp_glueingDataEval]
    exact restrictionFunctorAtPoint_isEquivalence_of_eq _ (mem_closedPoints_iff.mp (hs default))
      (complementOfClosedPoints_eq_puncturedOpen s hs) hqc
  exact isEquivalence_of_comp_fullyFaithful _ (glueingDataEval s hs)

end AlgebraicGeometry

end
