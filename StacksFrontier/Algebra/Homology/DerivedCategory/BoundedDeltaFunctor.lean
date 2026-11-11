module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import StacksFrontier.Algebra.Homology.DerivedCategory.CanonicalDeltaFunctor
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Minus
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical `δ`-functors `Comp⁺(𝒜) ⥤ D⁺(𝒜)`, `Comp⁻(𝒜) ⥤ D⁻(𝒜)`, `Compᵇ(𝒜) ⥤ Dᵇ(𝒜)`

Let `𝒜` be an abelian category. The localization functor `Q : Comp(𝒜) ⥤ D(𝒜)` is a `δ`-functor
with connecting morphism `δ = -p ∘ q⁻¹` (`DerivedCategory.exists_deltaFunctorStructure_δ_eq`),
where for a short exact sequence `0 → A^• → B^• → C^• → 0` the map `q : C(a)^• → C^•` is the
quasi-isomorphism from the cone of `a` and `p : C(a)^• → A^•[1]` the projection. The same
construction makes each of the three functors
`Comp⁺(𝒜) ⥤ D⁺(𝒜)`, `Comp⁻(𝒜) ⥤ D⁻(𝒜)` and `Compᵇ(𝒜) ⥤ Dᵇ(𝒜)`
into a `δ`-functor, and this file proves it.

Here `Comp⁺(𝒜)`, `Comp⁻(𝒜)` and `Compᵇ(𝒜)` are the full subcategories of `Comp(𝒜)` cut out by
`CochainComplex.plus 𝒜`, `CochainComplex.minus 𝒜` and their intersection (complexes with
`Kⁿ = 0` for `n ≪ 0`, resp. `n ≫ 0`, resp. both), and `D⁺(𝒜)`, `D⁻(𝒜)`, `Dᵇ(𝒜)` are Mathlib's
`DerivedCategory.Plus 𝒜`, `DerivedCategory.Minus 𝒜`, `DerivedCategory.Bounded 𝒜`, the full
triangulated subcategories of `D(𝒜)` of objects with bounded below, bounded above, bounded
cohomology. The functors are the restrictions of `Q`: Mathlib's `DerivedCategory.Plus.Q`, and
`DerivedCategory.Minus.Q`, `DerivedCategory.Bounded.Q` defined here in the same way.

## Main results

* `DerivedCategory.exists_deltaFunctorStructure_lift_δ_eq`: for a full subcategory `P` of
  `Comp(𝒜)` closed under finite limits and colimits and a triangulated subcategory `P'` of
  `D(𝒜)` containing the image of `P`, the restriction `P ⥤ P'` of `Q` is a `δ`-functor whose
  connecting morphism is, in `D(𝒜)`, the connecting morphism `-p ∘ q⁻¹` of `Q`.
* `DerivedCategory.exists_deltaFunctorStructure_δ_eq_and_plus_minus_bounded`: Stacks 0152 in
  full, the four `δ`-functors.

## Implementation notes

A short exact sequence of `Comp⁺(𝒜)` is a short exact sequence of the abelian category
`Comp⁺(𝒜)` itself; since `Comp⁺(𝒜)` is closed in `Comp(𝒜)` under finite limits and colimits,
the inclusion is exact and the sequence stays short exact in `Comp(𝒜)`, which is where the cone
construction is made. The connecting morphism in `D⁺(𝒜)` is the unique morphism whose image
in `D(𝒜)` (a fully faithful inclusion) is `-p ∘ q⁻¹ = DerivedCategory.triangleOfSESδ`; this
image is what the statements pin down, the commutation isomorphism of the inclusion with the
shift being inserted so that both sides have the same type.

## References

* [Stacks, Tag 0152](https://stacks.math.columbia.edu/tag/0152)
-/

@[expose] public section

universe w v u

open CategoryTheory Category Limits Pretriangulated

namespace CategoryTheory.ObjectProperty

variable {D : Type*} [Category* D] {P₁ P₂ : ObjectProperty D}

/-- The intersection of two properties of objects closed under limits of shape `J` is closed
under limits of shape `J`. -/
instance isClosedUnderLimitsOfShape_inf (J : Type*) [Category* J]
    [P₁.IsClosedUnderLimitsOfShape J] [P₂.IsClosedUnderLimitsOfShape J] :
    (P₁ ⊓ P₂).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    exact ⟨P₁.prop_of_isLimit p.isLimit (fun j ↦ (p.prop_diag_obj j).1),
      P₂.prop_of_isLimit p.isLimit (fun j ↦ (p.prop_diag_obj j).2)⟩

/-- The intersection of two properties of objects closed under colimits of shape `J` is closed
under colimits of shape `J`. -/
instance isClosedUnderColimitsOfShape_inf (J : Type*) [Category* J]
    [P₁.IsClosedUnderColimitsOfShape J] [P₂.IsClosedUnderColimitsOfShape J] :
    (P₁ ⊓ P₂).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    exact ⟨P₁.prop_of_isColimit p.isColimit (fun j ↦ (p.prop_diag_obj j).1),
      P₂.prop_of_isColimit p.isColimit (fun j ↦ (p.prop_diag_obj j).2)⟩

end CategoryTheory.ObjectProperty

namespace CochainComplex

variable (C : Type*) [Category* C] [HasZeroMorphisms C]

/-- Bounded above complexes are closed under finite limits: a limit of finitely many complexes
which all vanish in degrees `> n` vanishes in degrees `> n`. -/
instance (J : Type*) [SmallCategory J] [FinCategory J] [HasLimitsOfShape J C] :
    (CochainComplex.minus C).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro K ⟨p⟩
    obtain ⟨n, hn⟩ : ∃ (n : ℤ), ∀ (j : J), (p.diag.obj j).IsStrictlyLE n := by
      choose n hn using p.prop_diag_obj
      exact ⟨Finset.max' (Finset.image n ⊤ ∪ {0}) ⟨0, by grind⟩, fun j ↦
        (p.diag.obj j).isStrictlyLE_of_le _ _ (Finset.le_max' _ (n j) (by simp))⟩
    refine ⟨n, ?_⟩
    rw [isStrictlyLE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isLimitOfPreserves (HomologicalComplex.eval _ _ i) p.isLimit).hom_ext
      (fun j ↦ (isZero_of_isStrictlyLE (p.diag.obj j) n i).eq_of_tgt _ _)

/-- Bounded above complexes are closed under finite colimits: a colimit of finitely many
complexes which all vanish in degrees `> n` vanishes in degrees `> n`. -/
instance (J : Type*) [SmallCategory J] [FinCategory J] [HasColimitsOfShape J C] :
    (CochainComplex.minus C).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro K ⟨p⟩
    obtain ⟨n, hn⟩ : ∃ (n : ℤ), ∀ (j : J), (p.diag.obj j).IsStrictlyLE n := by
      choose n hn using p.prop_diag_obj
      exact ⟨Finset.max' (Finset.image n ⊤ ∪ {0}) ⟨0, by grind⟩, fun j ↦
        (p.diag.obj j).isStrictlyLE_of_le _ _ (Finset.le_max' _ (n j) (by simp))⟩
    refine ⟨n, ?_⟩
    rw [isStrictlyLE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isColimitOfPreserves (HomologicalComplex.eval _ _ i) p.isColimit).hom_ext
      (fun j ↦ (isZero_of_isStrictlyLE (p.diag.obj j) n i).eq_of_src _ _)

end CochainComplex

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

section lift

variable (P : ObjectProperty (CochainComplex C ℤ))
  [PreservesFiniteLimits P.ι] [PreservesFiniteColimits P.ι]
  (P' : ObjectProperty (DerivedCategory C)) [P'.IsTriangulated]
  (hP : ∀ K : P.FullSubcategory, P' (Q.obj K.obj))

/-- The connecting morphism of the restriction `P ⥤ P'` of `Q`: the unique morphism of `P'`
whose image in `D(𝒜)` is `DerivedCategory.triangleOfSESδ = -p ∘ q⁻¹`. -/
noncomputable def liftδ {S : ShortComplex P.FullSubcategory} (hS : S.ShortExact) :
    (P'.lift (P.ι ⋙ Q) hP).obj S.X₃ ⟶ ((P'.lift (P.ι ⋙ Q) hP).obj S.X₁)⟦(1 : ℤ)⟧ :=
  P'.fullyFaithfulι.preimage (triangleOfSESδ (hS.map_of_exact P.ι) ≫
    (P'.ι.commShiftIso (1 : ℤ)).inv.app ((P'.lift (P.ι ⋙ Q) hP).obj S.X₁))

lemma ι_map_liftδ {S : ShortComplex P.FullSubcategory} (hS : S.ShortExact) :
    P'.ι.map (liftδ P P' hP hS) ≫
        (P'.ι.commShiftIso (1 : ℤ)).hom.app ((P'.lift (P.ι ⋙ Q) hP).obj S.X₁) =
      triangleOfSESδ (hS.map_of_exact P.ι) := by
  simp [liftδ]

/-- **The restriction of the canonical `δ`-functor.** Let `P` be a property of cochain complexes
of `𝒜` whose full subcategory is closed under finite limits and colimits (so that its inclusion
into `Comp(𝒜)` is exact), and let `P'` be a triangulated subcategory of `D(𝒜)` containing the
image of `P` under `Q`. Then the restriction `P ⥤ P'` of `Q` has a `δ`-functor structure whose
connecting morphism has image `DerivedCategory.triangleOfSESδ = -p ∘ q⁻¹` in `D(𝒜)`. -/
theorem exists_deltaFunctorStructure_lift_δ_eq :
    ∃ h : Functor.DeltaFunctorStructure P.FullSubcategory P'.FullSubcategory
        (P'.lift (P.ι ⋙ Q) hP),
      ∀ {S : ShortComplex P.FullSubcategory} (hS : S.ShortExact),
        P'.ι.map (h.δ hS) ≫
            (P'.ι.commShiftIso (1 : ℤ)).hom.app ((P'.lift (P.ι ⋙ Q) hP).obj S.X₁) =
          triangleOfSESδ (hS.map_of_exact P.ι) := by
  refine ⟨Functor.DeltaFunctorStructure.mk (liftδ P P' hP) ?_ ?_,
    fun hS ↦ ι_map_liftδ P P' hP hS⟩
  · intro S hS
    rw [← P'.ι.map_distinguished_iff]
    refine isomorphic_distinguished _ (triangleOfSES_distinguished (hS.map_of_exact P.ι)) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
    · exact (comp_id _).trans (id_comp _).symm
    · exact (comp_id _).trans (id_comp _).symm
    · refine Eq.trans ?_ (id_comp _).symm
      refine Eq.trans (congrArg (_ ≫ ·) ((shiftFunctor _ (1 : ℤ)).map_id _)) ?_
      exact (comp_id _).trans (ι_map_liftδ P P' hP hS)
  · intro S₁ S₂ h₁ h₂ φ
    apply P'.fullyFaithfulι.map_injective
    rw [← cancel_mono ((P'.ι.commShiftIso (1 : ℤ)).hom.app
      ((P'.lift (P.ι ⋙ Q) hP).obj S₂.X₁)), Functor.map_comp, Functor.map_comp, assoc, assoc,
      Functor.commShiftIso_hom_naturality, ι_map_liftδ, ← assoc, ι_map_liftδ]
    exact triangleOfSESδ_naturality (h₁.map_of_exact P.ι) (h₂.map_of_exact P.ι)
      (P.ι.mapShortComplex.map φ)

end lift

instance : PreservesFiniteLimits (CochainComplex.plus C).ι := ⟨fun _ _ _ ↦ inferInstance⟩

instance : PreservesFiniteColimits (CochainComplex.plus C).ι := ⟨fun _ _ _ ↦ inferInstance⟩

instance : PreservesFiniteLimits (CochainComplex.minus C).ι := ⟨fun _ _ _ ↦ inferInstance⟩

instance : PreservesFiniteColimits (CochainComplex.minus C).ι := ⟨fun _ _ _ ↦ inferInstance⟩

instance : PreservesFiniteLimits (CochainComplex.plus C ⊓ CochainComplex.minus C).ι :=
  ⟨fun _ _ _ ↦ inferInstance⟩

instance : PreservesFiniteColimits (CochainComplex.plus C ⊓ CochainComplex.minus C).ι :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- The functor `Comp⁻(𝒜) ⥤ D⁻(𝒜)` induced by `Q`, from bounded above complexes to the bounded
above derived category. -/
noncomputable def Minus.Q : (CochainComplex.minus C).FullSubcategory ⥤ DerivedCategory.Minus C :=
  ObjectProperty.lift _ ((CochainComplex.minus C).ι ⋙ DerivedCategory.Q)
    (fun ⟨K, n, hn⟩ ↦ ⟨n, by dsimp; infer_instance⟩)

/-- The functor `Compᵇ(𝒜) ⥤ Dᵇ(𝒜)` induced by `Q`, from bounded complexes to the bounded derived
category. -/
noncomputable def Bounded.Q :
    (CochainComplex.plus C ⊓ CochainComplex.minus C).FullSubcategory ⥤
      DerivedCategory.Bounded C :=
  ObjectProperty.lift _ ((CochainComplex.plus C ⊓ CochainComplex.minus C).ι ⋙ DerivedCategory.Q)
    (fun ⟨K, ⟨n, hn⟩, ⟨m, hm⟩⟩ ↦ ⟨⟨n, by dsimp; infer_instance⟩, ⟨m, by dsimp; infer_instance⟩⟩)

/-- **Stacks 0152 for `Comp⁺(𝒜) ⥤ D⁺(𝒜)`.** The functor `DerivedCategory.Plus.Q` from bounded
below complexes to the bounded below derived category has a `δ`-functor structure whose
connecting morphism has image `-p ∘ q⁻¹ = DerivedCategory.triangleOfSESδ` in `D(𝒜)`. -/
theorem Plus.exists_deltaFunctorStructure_δ_eq :
    ∃ h : Functor.DeltaFunctorStructure (CochainComplex.Plus C) (DerivedCategory.Plus C) Plus.Q,
      ∀ {S : ShortComplex (CochainComplex.Plus C)} (hS : S.ShortExact),
        Plus.ι.map (h.δ hS) ≫ (Plus.ι.commShiftIso (1 : ℤ)).hom.app (Plus.Q.obj S.X₁) =
          triangleOfSESδ (hS.map_of_exact (CochainComplex.Plus.ι C)) :=
  exists_deltaFunctorStructure_lift_δ_eq (CochainComplex.plus C) _ _

/-- **Stacks 0152 for `Comp⁻(𝒜) ⥤ D⁻(𝒜)`.** The functor `DerivedCategory.Minus.Q` from bounded
above complexes to the bounded above derived category has a `δ`-functor structure whose
connecting morphism has image `-p ∘ q⁻¹ = DerivedCategory.triangleOfSESδ` in `D(𝒜)`. -/
theorem Minus.exists_deltaFunctorStructure_δ_eq :
    ∃ h : Functor.DeltaFunctorStructure (CochainComplex.minus C).FullSubcategory
        (DerivedCategory.Minus C) Minus.Q,
      ∀ {S : ShortComplex (CochainComplex.minus C).FullSubcategory} (hS : S.ShortExact),
        Minus.ι.map (h.δ hS) ≫ (Minus.ι.commShiftIso (1 : ℤ)).hom.app (Minus.Q.obj S.X₁) =
          triangleOfSESδ (hS.map_of_exact (CochainComplex.minus C).ι) :=
  exists_deltaFunctorStructure_lift_δ_eq (CochainComplex.minus C) _ _

/-- **Stacks 0152 for `Compᵇ(𝒜) ⥤ Dᵇ(𝒜)`.** The functor `DerivedCategory.Bounded.Q` from bounded
complexes to the bounded derived category has a `δ`-functor structure whose connecting morphism
has image `-p ∘ q⁻¹ = DerivedCategory.triangleOfSESδ` in `D(𝒜)`. -/
theorem Bounded.exists_deltaFunctorStructure_δ_eq :
    ∃ h : Functor.DeltaFunctorStructure
        (CochainComplex.plus C ⊓ CochainComplex.minus C).FullSubcategory
        (DerivedCategory.Bounded C) Bounded.Q,
      ∀ {S : ShortComplex (CochainComplex.plus C ⊓ CochainComplex.minus C).FullSubcategory}
        (hS : S.ShortExact),
        Bounded.ι.map (h.δ hS) ≫ (Bounded.ι.commShiftIso (1 : ℤ)).hom.app (Bounded.Q.obj S.X₁) =
          triangleOfSESδ (hS.map_of_exact (CochainComplex.plus C ⊓ CochainComplex.minus C).ι) :=
  exists_deltaFunctorStructure_lift_δ_eq (CochainComplex.plus C ⊓ CochainComplex.minus C) _ _

/-- **The canonical `δ`-functors** ([Stacks, Tag 0152]). Let `𝒜` be an abelian category. Each of
the four functors `Q : Comp(𝒜) ⥤ D(𝒜)`, `Comp⁺(𝒜) ⥤ D⁺(𝒜)`, `Comp⁻(𝒜) ⥤ D⁻(𝒜)` and
`Compᵇ(𝒜) ⥤ Dᵇ(𝒜)` has a `δ`-functor structure whose connecting morphism attached to a short exact
sequence `0 → A^• → B^• → C^• → 0` is `δ = -p ∘ q⁻¹ = DerivedCategory.triangleOfSESδ` (for the
three bounded variants: its image in `D(𝒜)` under the fully faithful inclusion is). -/
@[stacks 0152]
theorem exists_deltaFunctorStructure_δ_eq_and_plus_minus_bounded :
    (∃ h : Functor.DeltaFunctorStructure (CochainComplex C ℤ) (DerivedCategory C) Q,
      ∀ {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact),
        h.δ hS = triangleOfSESδ hS) ∧
    (∃ h : Functor.DeltaFunctorStructure (CochainComplex.Plus C) (DerivedCategory.Plus C) Plus.Q,
      ∀ {S : ShortComplex (CochainComplex.Plus C)} (hS : S.ShortExact),
        Plus.ι.map (h.δ hS) ≫ (Plus.ι.commShiftIso (1 : ℤ)).hom.app (Plus.Q.obj S.X₁) =
          triangleOfSESδ (hS.map_of_exact (CochainComplex.Plus.ι C))) ∧
    (∃ h : Functor.DeltaFunctorStructure (CochainComplex.minus C).FullSubcategory
        (DerivedCategory.Minus C) Minus.Q,
      ∀ {S : ShortComplex (CochainComplex.minus C).FullSubcategory} (hS : S.ShortExact),
        Minus.ι.map (h.δ hS) ≫ (Minus.ι.commShiftIso (1 : ℤ)).hom.app (Minus.Q.obj S.X₁) =
          triangleOfSESδ (hS.map_of_exact (CochainComplex.minus C).ι)) ∧
    (∃ h : Functor.DeltaFunctorStructure
        (CochainComplex.plus C ⊓ CochainComplex.minus C).FullSubcategory
        (DerivedCategory.Bounded C) Bounded.Q,
      ∀ {S : ShortComplex (CochainComplex.plus C ⊓ CochainComplex.minus C).FullSubcategory}
        (hS : S.ShortExact),
        Bounded.ι.map (h.δ hS) ≫ (Bounded.ι.commShiftIso (1 : ℤ)).hom.app (Bounded.Q.obj S.X₁) =
          triangleOfSESδ (hS.map_of_exact (CochainComplex.plus C ⊓ CochainComplex.minus C).ι)) :=
  ⟨DerivedCategory.exists_deltaFunctorStructure_δ_eq C, Plus.exists_deltaFunctorStructure_δ_eq,
    Minus.exists_deltaFunctorStructure_δ_eq, Bounded.exists_deltaFunctorStructure_δ_eq⟩

end DerivedCategory
