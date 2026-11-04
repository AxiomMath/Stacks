module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtaleFunctor
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismUniquenessAlongClosedSubset
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Artin's theorem on dilatations

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a locally Noetherian algebraic
space over `S`, let `T ⊆ |X|` be a closed subset and let `U ⊆ X` be the open subspace with
`|U| = |X| ∖ T`. Write `𝔛 = X_{/T}` for the completion of `X` along `T`. **Stacks 0GDU**,
Artin's theorem on dilatations, says that for every formal modification `𝔣 : 𝔛' ⟶ 𝔛`
(Definition 0GDK) there is a unique proper morphism `f : X' ⟶ X` of algebraic spaces which is an
isomorphism over `U` and whose completion `f_{/T}` recovers `𝔣`.

This file proves the faithfulness half of Stacks 0GDR: a morphism over `X` into a modification
of `X` outside `U` is determined by its completion along `T`. It also proves Stacks 0GDU from
Theorem 0ARB, that the completion functor of Stacks 0AR5 from the finite-type modifications of
`X` outside `U` to the rig-étale morphisms with locally Noetherian source over `𝔛` is an
equivalence, and Lemma 0ARX, that a finite-type modification is proper exactly when the
rig-étale morphism it corresponds to is a formal modification, both taken as hypotheses.

## Main definitions

* `AlgebraicGeometry.FormalSpace.rigEtaleOverCompletionOfIsFormalModification`: a formal
  modification over `𝔛` as an object of the right-hand collection of Stacks 0AR5.

## Main results

* `AlgebraicGeometry.Space.isFiniteTypeModification_of_isProper`: a proper modification of `X`
  outside `U` is a finite-type modification.
* `AlgebraicGeometry.Space.comp_eq_openComplement_of_comp_eq`: two morphisms over `X` into a
  modification of `X` outside `U` agree on the open complement of the inverse image of `T`.
* `AlgebraicGeometry.Space.eq_of_completionSubfunctorMap_eq_of_isIso_pullback_snd`: **the
  faithfulness half of Stacks 0GDR.** Two morphisms `a, b : Y ⟶ X'` over `X`, with `Y` a locally
  Noetherian algebraic space and `X' ⟶ X` an isomorphism over `U`, whose completions along `T`
  agree, are equal.
* `AlgebraicGeometry.Space.over_hom_ext_of_completionSubfunctorMap_eq`: the same statement for
  morphisms in the slice category over `X`.
* `AlgebraicGeometry.FormalSpace.exists_isProper_iso_of_isFormalModification`: the existence
  half of Stacks 0GDU, from Stacks 0ARB and Stacks 0ARX as hypotheses.
* `AlgebraicGeometry.FormalSpace.existsUnique_hom_of_iso_of_isEquivalence` and
  `AlgebraicGeometry.FormalSpace.isIso_of_map_comp_iso_hom_eq`: the uniqueness half, from
  Stacks 0ARB as a hypothesis: between two solutions there is exactly one morphism over `X`
  compatible with the two identifications with `𝔣`, and it is an isomorphism.

## References

* [Stacks Project, Tag 0GDU](https://stacks.math.columbia.edu/tag/0GDU)
* [Stacks Project, Tag 0GDK](https://stacks.math.columbia.edu/tag/0GDK)
* [Stacks Project, Tag 0GDR](https://stacks.math.columbia.edu/tag/0GDR)
* [Stacks Project, Tag 0ARB](https://stacks.math.columbia.edu/tag/0ARB)
* [Stacks Project, Tag 0ARX](https://stacks.math.columbia.edu/tag/0ARX)
* [Stacks Project, Tag 0AR5](https://stacks.math.columbia.edu/tag/0AR5)
* [Stacks Project, Tag 0AR7](https://stacks.math.columbia.edu/tag/0AR7)
* [Stacks Project, Tag 0AS2](https://stacks.math.columbia.edu/tag/0AS2)
* [Stacks Project, Tag 0AR3](https://stacks.math.columbia.edu/tag/0AR3)
* [Stacks Project, Tag 0AR4](https://stacks.math.columbia.edu/tag/0AR4)
* [Stacks Project, Tag 0GB8](https://stacks.math.columbia.edu/tag/0GB8)
* [Stacks Project, Tag 0GB9](https://stacks.math.columbia.edu/tag/0GB9)
* [Stacks Project, Tag 0AKG](https://stacks.math.columbia.edu/tag/0AKG)
* [Stacks Project, Tag 0AKA](https://stacks.math.columbia.edu/tag/0AKA)
* [Stacks Project, Tag 0ALQ](https://stacks.math.columbia.edu/tag/0ALQ)
* [Stacks Project, Tag 0GBA](https://stacks.math.columbia.edu/tag/0GBA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

variable {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Proper modifications are finite-type modifications -/

/-- A modification of `W` outside `W₀` whose structure morphism is proper is a finite-type
modification in the sense of **Stacks 0AS2**. -/
theorem isFiniteTypeModification_of_isProper {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W₀ : Subfunctor W} {M : Over W} (hM : IsModification B S hS W₀ M)
    (hproper : IsProper B S hS M.hom) : IsFiniteTypeModification B S hS W₀ M :=
  ⟨hM, (IsProper.isFiniteType B S hS hproper).1⟩

/-! ### Morphisms over `X` and the open complement of `T` -/

/-- A morphism `a : Y ⟶ X'` over `g : Y ⟶ X` computes the map on points of `g` through the map
on points of the structure morphism of `X'`. -/
theorem pointsMap_pointsMap_of_comp_eq {f : X' ⟶ X} {g : Y ⟶ X} {a : Y ⟶ X'}
    (hag : a ≫ f = g) (y : points B S hS Y) :
    pointsMap B S hS X' f (pointsMap B S hS Y a y) = pointsMap B S hS Y g y := by
  rw [← hag, pointsMap_comp]
  rfl

/-- The points of `Y` lying over the complement of `T` are carried by a morphism over `X` into
the complement of the inverse image of `T`. -/
theorem compl_preimage_subset_preimage_of_comp_eq {f : X' ⟶ X} {g : Y ⟶ X} {a : Y ⟶ X'}
    (hag : a ≫ f = g) (T : Set (points B S hS X)) :
    (pointsMap B S hS Y g ⁻¹' T)ᶜ ⊆
      pointsMap B S hS Y a ⁻¹' (pointsMap B S hS X' f ⁻¹' Tᶜ) := by
  intro y hy
  rwa [Set.mem_preimage, Set.mem_preimage, pointsMap_pointsMap_of_comp_eq B S hS hag y]

/-- The points of `Y` lying over `T` are carried by a morphism over `X` into the inverse image
of `T`. -/
theorem image_preimage_subset_preimage_of_comp_eq {f : X' ⟶ X} {g : Y ⟶ X} {a : Y ⟶ X'}
    (hag : a ≫ f = g) (T : Set (points B S hS X)) :
    pointsMap B S hS Y a '' (pointsMap B S hS Y g ⁻¹' T) ⊆ pointsMap B S hS X' f ⁻¹' T := by
  rintro _ ⟨y, hy, rfl⟩
  simpa only [Set.mem_preimage, pointsMap_pointsMap_of_comp_eq B S hS hag y] using hy

/-- Two morphisms `a, b : Y ⟶ X'` over `X` into a modification of `X` outside the open subspace
`U` with `|U| = |X| ∖ T` agree on the open complement of `|g|⁻¹T` in `Y`. -/
theorem comp_eq_openComplement_of_comp_eq {f : X' ⟶ X} {T : Set (points B S hS X)}
    (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι))
    {g : Y ⟶ X} {a b : Y ⟶ X'} (hag : a ≫ f = g) (hbg : b ≫ f = g) :
    (openSubspaceOfPoints B S hS Y (pointsMap B S hS Y g ⁻¹' T)ᶜ).ι ≫ a =
      (openSubspaceOfPoints B S hS Y (pointsMap B S hS Y g ⁻¹' T)ᶜ).ι ≫ b := by
  have hle : ∀ {c : Y ⟶ X'}, c ≫ f = g →
      Subfunctor.range
          ((openSubspaceOfPoints B S hS Y (pointsMap B S hS Y g ⁻¹' T)ᶜ).ι ≫ c) ≤
        openSubspaceOfPoints B S hS X' (pointsMap B S hS X' f ⁻¹' Tᶜ) := by
    intro c hc
    rw [Subfunctor.range_comp, Subfunctor.range_ι, Subfunctor.image_le_iff,
      preimage_openSubspaceOfPoints]
    exact openSubspaceOfPoints_mono B S hS
      (compl_preimage_subset_preimage_of_comp_eq B S hS hc T)
  have hiso : IsIso (openComplementRestriction B S hS f T) :=
    isIso_openComplementRestriction B S hS f T hfU
  have key :
      Subfunctor.lift _ (hle hag) ≫ openComplementRestriction B S hS f T =
        Subfunctor.lift _ (hle hbg) ≫ openComplementRestriction B S hS f T := by
    rw [← cancel_mono (openSubspaceOfPoints B S hS X Tᶜ).ι, Category.assoc, Category.assoc,
      openComplementRestriction_ι, ← Category.assoc, ← Category.assoc,
      Subfunctor.lift_ι, Subfunctor.lift_ι, Category.assoc, Category.assoc, hag, hbg]
  simpa only [Subfunctor.lift_ι] using
    (cancel_mono (openComplementRestriction B S hS f T)).mp key =≫
      (openSubspaceOfPoints B S hS X' (pointsMap B S hS X' f ⁻¹' Tᶜ)).ι

/-! ### The faithfulness half of Stacks 0GDR -/

/-- **The faithfulness half of Stacks 0GDR.** Let `X` be an algebraic space over `S`, let
`T ⊆ |X|` be a closed subset with complementary open subspace `U ⊆ X` and let `f : X' ⟶ X` be a
morphism of algebraic spaces whose base change to `U` is an isomorphism. For a locally
Noetherian algebraic space `Y` over `X` two morphisms `Y ⟶ X'` over `X` whose completions along
`T` agree are equal. -/
theorem eq_of_completionSubfunctorMap_eq_of_isIso_pullback_snd
    (hY : IsAlgebraicSpace B S hS Y) (hX' : IsAlgebraicSpace B S hS X')
    (hYnoeth : HasEtaleLocalProperty B S hS Y
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hX'noeth : HasEtaleLocalProperty B S hS X'
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    {f : X' ⟶ X} {T : Set (points B S hS X)} (hT : IsClosed T)
    (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι))
    {g : Y ⟶ X} {a b : Y ⟶ X'} (hag : a ≫ f = g) (hbg : b ≫ f = g)
    (hcompletion :
      completionSubfunctorMap B S hS a (pointsMap B S hS Y g ⁻¹' T)
          (pointsMap B S hS X' f ⁻¹' T)
          (image_preimage_subset_preimage_of_comp_eq B S hS hag T) =
        completionSubfunctorMap B S hS b (pointsMap B S hS Y g ⁻¹' T)
          (pointsMap B S hS X' f ⁻¹' T)
          (image_preimage_subset_preimage_of_comp_eq B S hS hbg T)) :
    a = b :=
  eq_of_eq_on_compl_of_completionSubfunctorMap_eq B S hS hY hX' hYnoeth hX'noeth
    (hT.preimage (continuous_pointsMap B S hS g))
    (hT.preimage (continuous_pointsMap B S hS f)) a b _ _
    (comp_eq_openComplement_of_comp_eq B S hS hfU hag hbg) hcompletion

/-- **The faithfulness half of Stacks 0GDR, in the slice category over `X`.** At most one
morphism over `X` between two modifications of `X` outside `U` induces a prescribed morphism of
completions along `T`. -/
theorem over_hom_ext_of_completionSubfunctorMap_eq {M N : Over X}
    (hM : IsAlgebraicSpace B S hS M.left) (hN : IsAlgebraicSpace B S hS N.left)
    (hMnoeth : HasEtaleLocalProperty B S hS M.left
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hNnoeth : HasEtaleLocalProperty B S hS N.left
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    {T : Set (points B S hS X)} (hT : IsClosed T)
    (hNU : IsIso (pullback.snd N.hom (openSubspaceOfPoints B S hS X Tᶜ).ι))
    (φ ψ : M ⟶ N)
    (hcompletion :
      completionSubfunctorMap B S hS φ.left (pointsMap B S hS M.left M.hom ⁻¹' T)
          (pointsMap B S hS N.left N.hom ⁻¹' T)
          (image_preimage_subset_preimage_of_comp_eq B S hS (Over.w φ) T) =
        completionSubfunctorMap B S hS ψ.left (pointsMap B S hS M.left M.hom ⁻¹' T)
          (pointsMap B S hS N.left N.hom ⁻¹' T)
          (image_preimage_subset_preimage_of_comp_eq B S hS (Over.w ψ) T)) :
    φ = ψ :=
  Over.OverMorphism.ext
    (eq_of_completionSubfunctorMap_eq_of_isIso_pullback_snd B S hS hM hN hMnoeth hNnoeth hT hNU
      (Over.w φ) (Over.w ψ) hcompletion)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopology

variable {B S hS}

/-! ### A formal modification as an object of the right-hand collection of Stacks 0AR5 -/

/-- A formal modification `𝔣 : 𝔛' ⟶ X_{/T}` is an object of the right-hand collection of
Stacks 0AR5. -/
def rigEtaleOverCompletionOfIsFormalModification
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : Set (Space.points B S hS X)}
    {W : FppfSheaf B S hS} {𝔣 : W ⟶ Space.completionSheaf B S hS X T}
    (h𝔣 : IsFormalModification B S hS 𝔣) : RigEtaleOverCompletion B S hS X T :=
  ⟨Over.mk 𝔣, h𝔣.isLocallyNoetherian_source.1, h𝔣.isLocallyNoetherian_source, h𝔣.isRigEtale⟩

/-! ### Stacks 0GDU from Stacks 0ARB and Stacks 0ARX -/

/-- Two objects which a fully faithful functor carries to the same object, up to a prescribed
isomorphism in each case, have exactly one morphism between them compatible with the two
prescribed isomorphisms. -/
private theorem existsUnique_hom_of_iso {C : Type*} {D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {M₁ M₂ : C} {P : D}
    (e₁ : F.obj M₁ ≅ P) (e₂ : F.obj M₂ ≅ P) :
    ∃! φ : M₁ ⟶ M₂, F.map φ ≫ e₂.hom = e₁.hom := by
  refine ⟨(F.preimageIso (e₁ ≪≫ e₂.symm)).hom, ?_, ?_⟩
  · simp [Functor.preimageIso]
  · intro ψ hψ
    refine F.map_injective ?_
    rw [← cancel_mono e₂.hom, hψ]
    simp [Functor.preimageIso]

/-- A morphism compatible with two prescribed isomorphisms as above is an isomorphism. -/
private theorem isIso_of_map_comp_eq {C : Type*} {D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {M₁ M₂ : C} {P : D}
    (e₁ : F.obj M₁ ≅ P) (e₂ : F.obj M₂ ≅ P) (φ : M₁ ⟶ M₂)
    (hφ : F.map φ ≫ e₂.hom = e₁.hom) : IsIso φ := by
  have hmap : F.map φ = e₁.hom ≫ e₂.inv := by rw [← hφ]; simp
  have : IsIso (F.map φ) := by rw [hmap]; infer_instance
  exact isIso_of_reflects_iso φ F

section Dilatations

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Set (Space.points B S hS X))
  (hT : IsClosed T) (hX : Space.IsLocallyNoetherian B S hS X)
  (h0AIZ : IsFormalAlgebraicSpaceCompletionSheaf B S hS X T)
  (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
  (hred : ChartSquareReducesToIsEtaleOutsideModifications T)

/-- **The existence half of Stacks 0GDU**, from Stacks 0ARB and Stacks 0ARX taken as
hypotheses. Granted Stacks 0ARB, that the completion functor of Stacks 0AR5 is an equivalence
(`h0ARB`), and Stacks 0ARX, that a finite-type modification of `X` outside `U` is proper exactly
when the rig-étale morphism over `X_{/T}` it corresponds to is a formal modification (`h0ARX`):
every formal modification `𝔣 : 𝔛' ⟶ X_{/T}` is the completion along `T` of a morphism
`f : X' ⟶ X` of algebraic spaces which is locally of finite type, an isomorphism over `U` and
proper. -/
theorem exists_isProper_iso_of_isFormalModification
    (h0ARB :
      (completionFiniteTypeModificationFunctor T hT hX h0AIZ hnoeth hred).IsEquivalence)
    (h0ARX : ∀ (M : Space.FiniteTypeModification B S hS
          (Space.openSubspaceOfPoints B S hS X Tᶜ))
        (P : RigEtaleOverCompletion B S hS X T),
        ((completionFiniteTypeModificationFunctor T hT hX h0AIZ hnoeth hred).obj M ≅ P) →
          (Space.IsProper B S hS M.obj.hom ↔ IsFormalModification B S hS P.obj.hom))
    {W : FppfSheaf B S hS} {𝔣 : W ⟶ Space.completionSheaf B S hS X T}
    (h𝔣 : IsFormalModification B S hS 𝔣) :
    ∃ (M : Space.FiniteTypeModification B S hS
          (Space.openSubspaceOfPoints B S hS X Tᶜ))
        (_ : (completionFiniteTypeModificationFunctor T hT hX h0AIZ hnoeth hred).obj M ≅
          rigEtaleOverCompletionOfIsFormalModification h𝔣),
      Space.IsProper B S hS M.obj.hom := by
  have := h0ARB
  let e := (completionFiniteTypeModificationFunctor T hT hX h0AIZ hnoeth hred).objObjPreimageIso
    (rigEtaleOverCompletionOfIsFormalModification h𝔣)
  exact ⟨_, e, (h0ARX _ _ e).2 h𝔣⟩

/-- **The uniqueness half of Stacks 0GDU**, from Stacks 0ARB taken as a hypothesis. Between two
finite-type modifications of `X` outside `U` whose completions along `T` are identified with the
same rig-étale morphism over `X_{/T}` there is exactly one morphism over `X` compatible with the
two identifications. -/
theorem existsUnique_hom_of_iso_of_isEquivalence
    (h0ARB :
      (completionFiniteTypeModificationFunctor T hT hX h0AIZ hnoeth hred).IsEquivalence)
    {M₁ M₂ : Space.FiniteTypeModification B S hS
      (Space.openSubspaceOfPoints B S hS X Tᶜ)}
    {P : RigEtaleOverCompletion B S hS X T}
    (e₁ : (completionFiniteTypeModificationFunctor T hT hX h0AIZ hnoeth hred).obj M₁ ≅ P)
    (e₂ : (completionFiniteTypeModificationFunctor T hT hX h0AIZ hnoeth hred).obj M₂ ≅ P) :
    ∃! φ : M₁ ⟶ M₂,
      (completionFiniteTypeModificationFunctor T hT hX h0AIZ hnoeth hred).map φ ≫ e₂.hom =
        e₁.hom :=
  have := h0ARB
  existsUnique_hom_of_iso _ e₁ e₂

/-- **The uniqueness half of Stacks 0GDU**, continued: the compatible morphism is an
isomorphism. -/
theorem isIso_of_map_comp_iso_hom_eq
    (h0ARB :
      (completionFiniteTypeModificationFunctor T hT hX h0AIZ hnoeth hred).IsEquivalence)
    {M₁ M₂ : Space.FiniteTypeModification B S hS
      (Space.openSubspaceOfPoints B S hS X Tᶜ)}
    {P : RigEtaleOverCompletion B S hS X T}
    (e₁ : (completionFiniteTypeModificationFunctor T hT hX h0AIZ hnoeth hred).obj M₁ ≅ P)
    (e₂ : (completionFiniteTypeModificationFunctor T hT hX h0AIZ hnoeth hred).obj M₂ ≅ P)
    (φ : M₁ ⟶ M₂)
    (hφ : (completionFiniteTypeModificationFunctor T hT hX h0AIZ hnoeth hred).map φ ≫ e₂.hom =
      e₁.hom) :
    IsIso φ :=
  have := h0ARB
  isIso_of_map_comp_eq _ e₁ e₂ φ hφ

end Dilatations

end AlgebraicGeometry.FormalSpace

end
