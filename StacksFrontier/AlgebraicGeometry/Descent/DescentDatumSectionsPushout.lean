module

public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPushoutIntersection
public import StacksFrontier.AlgebraicGeometry.Groupoids.DescentDatumInvariantSet

/-!
# Rings of functions on an invariant subset of a descent datum

Let `f : X ⟶ S` be a flat morphism of affine schemes and let `D` be a descent datum relative to
`f`, with underlying scheme `V` over `X`, quasi-separated, and gluing isomorphism
`φ : V ×_S X ≅ X ×_S V`. Let `E ⊆ V` be an intersection of a nonempty family of quasi-compact
opens which is invariant under `φ` set-theoretically, and write `E ×_S X` and `X ×_S E` for the
inverse images of `E` under the projections `V ×_S X ⟶ V` and `X ×_S V ⟶ V`. This file proves:

* `Γ(E ×_S X)` is `Γ(E) ⊗_{Γ(S)} Γ(X)` and `Γ(X ×_S E)` is `Γ(X) ⊗_{Γ(S)} Γ(E)`, as pushout
  squares of rings;
* `φ` induces an isomorphism `Φ : Γ(E ×_S X) ≅ Γ(X ×_S E)`;
* `Φ` lies over `Γ(X) ⊗_{Γ(S)} Γ(X)`.

## Main definitions

* `AlgebraicGeometry.DescentDatum.transitionSectionsIso` : the isomorphism
  `Γ(E ×_S X, 𝒪) ≅ Γ(X ×_S E, 𝒪)` induced by the gluing isomorphism of the datum on the rings of
  functions.
* `AlgebraicGeometry.DescentDatum.transitionSectionsIsoOfInvariant` : the same isomorphism, with
  the two containments it needs supplied by set-theoretic invariance of `E`.

## Main results

* `AlgebraicGeometry.DescentDatum.transitionPullbackIso_hom_comp_pullbackFst` and
  `AlgebraicGeometry.DescentDatum.transitionPullbackIso_hom_comp_pullbackSnd`, with their two
  companions for the inverse: the gluing isomorphism lies over `X ×_S X`, read on the literal
  fibre products.
* `AlgebraicGeometry.DescentDatum.isPushout_sectionsRingOnSubset_transitionSource` and
  `AlgebraicGeometry.DescentDatum.isPushout_sectionsRingOnSubset_transitionTarget` : `Γ(E ×_S X)`
  and `Γ(X ×_S E)` are pushouts of `Γ(E)` and `Γ(X)` over `Γ(S)`.
* `AlgebraicGeometry.DescentDatum.structureMap_comp_transitionSectionsIso_hom` and
  `AlgebraicGeometry.DescentDatum.base_comp_transitionSectionsIso_hom` : `Φ` lies over
  `Γ(X) ⊗_{Γ(S)} Γ(X)`.

## Implementation notes

`E ×_S X` and `X ×_S E` are the inverse images `pullback.fst ⁻¹' E` and `pullback.snd ⁻¹' E`. Both
pushout squares have `AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap` as their comparison
morphism, and `Φ` is `AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap` of `φ⁻¹`, with inverse
that of `φ`. The containments `E ×_S X ⊆ φ⁻¹(X ×_S E)` and `X ×_S E ⊆ (φ⁻¹)⁻¹(E ×_S X)` are
arguments of `AlgebraicGeometry.DescentDatum.transitionSectionsIso`;
`AlgebraicGeometry.DescentDatum.transitionSectionsIsoOfInvariant` supplies them from set-theoretic
invariance of `E`.

## References

* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
* [Stacks Project, Tag 023G](https://stacks.math.columbia.edu/tag/023G)
* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f)

/-! ### The gluing isomorphism lies over `X ×_S X` -/

/-- The gluing isomorphism on the literal fibre products, written via the `Over` category. -/
private theorem transitionPullbackIso_hom_eq :
    D.transitionPullbackIso.hom =
      (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).inv ≫
        D.transition.hom.left.left ≫
          (Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj D.over)).hom := rfl

/-- The gluing isomorphism preserves the first component of the base: on the literal fibre
products, `φ` followed by the projection of `X ×_S V` to `X` is the projection of `V ×_S X` to
`V` followed by the structure morphism `V ⟶ X`. -/
theorem transitionPullbackIso_hom_comp_pullbackFst :
    D.transitionPullbackIso.hom ≫ pullback.fst f (D.over.hom ≫ f) =
      pullback.fst (D.over.hom ≫ f) f ≫ D.over.hom := by
  have h1 : (Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj D.over)).hom ≫
      pullback.fst f (D.over.hom ≫ f) =
      (prod.fst : Over.mk f ⨯ (Over.map f).obj D.over ⟶ Over.mk f).left :=
    Over.prodLeftIsoPullback_hom_fst _ _
  have h2 : (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).inv ≫
      (prod.fst : (Over.map f).obj D.over ⨯ Over.mk f ⟶ (Over.map f).obj D.over).left =
      pullback.fst (D.over.hom ≫ f) f :=
    Over.prodLeftIsoPullback_inv_fst _ _
  rw [transitionPullbackIso_hom_eq, Category.assoc, Category.assoc, h1, ← Over.comp_left,
    DescentData.gluing_hom_fst, Over.comp_left, ← Category.assoc, h2]
  rfl

/-- The gluing isomorphism preserves the second component of the base: on the literal fibre
products, `φ` followed by the projection of `X ×_S V` to `V` and then by the structure morphism
`V ⟶ X` is the projection of `V ×_S X` to `X`. -/
theorem transitionPullbackIso_hom_comp_pullbackSnd :
    D.transitionPullbackIso.hom ≫ pullback.snd f (D.over.hom ≫ f) ≫ D.over.hom =
      pullback.snd (D.over.hom ≫ f) f := by
  have h1 : (Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj D.over)).hom ≫
      pullback.snd f (D.over.hom ≫ f) =
      (prod.snd : Over.mk f ⨯ (Over.map f).obj D.over ⟶ (Over.map f).obj D.over).left :=
    Over.prodLeftIsoPullback_hom_snd _ _
  have h2 : (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).inv ≫
      (prod.snd : (Over.map f).obj D.over ⨯ Over.mk f ⟶ Over.mk f).left =
      pullback.snd (D.over.hom ≫ f) f :=
    Over.prodLeftIsoPullback_inv_snd _ _
  have h1' : (Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj D.over)).hom ≫
      pullback.snd f (D.over.hom ≫ f) ≫ D.over.hom =
      (prod.snd ≫ structureMap f D.over :
        Over.mk f ⨯ (Over.map f).obj D.over ⟶ Over.mk f).left := by
    rw [Over.comp_left, ← Category.assoc, h1]
    rfl
  rw [transitionPullbackIso_hom_eq, Category.assoc, Category.assoc, h1', ← Over.comp_left,
    DescentData.gluing_hom_snd_structureMap, h2]

/-- The inverse of the gluing isomorphism preserves the first component of the base. -/
theorem transitionPullbackIso_inv_comp_pullbackFst :
    D.transitionPullbackIso.inv ≫ pullback.fst (D.over.hom ≫ f) f ≫ D.over.hom =
      pullback.fst f (D.over.hom ≫ f) := by
  rw [← D.transitionPullbackIso_hom_comp_pullbackFst, Iso.inv_hom_id_assoc]

/-- The inverse of the gluing isomorphism preserves the second component of the base. -/
theorem transitionPullbackIso_inv_comp_pullbackSnd :
    D.transitionPullbackIso.inv ≫ pullback.snd (D.over.hom ≫ f) f =
      pullback.snd f (D.over.hom ≫ f) ≫ D.over.hom := by
  rw [← D.transitionPullbackIso_hom_comp_pullbackSnd, Iso.inv_hom_id_assoc]

/-! ### The isomorphism `Φ` of the rings of functions -/

variable (E : Set D.over.left)

/-- The isomorphism `Γ(E ×_S X, 𝒪) ≅ Γ(X ×_S E, 𝒪)` of rings of functions induced by the gluing
isomorphism `φ` of a descent datum, where `E ×_S X` and `X ×_S E` are the inverse images of `E`
under the two projections. It takes as hypotheses the containments `E ×_S X ⊆ φ⁻¹(X ×_S E)` and
`X ×_S E ⊆ (φ⁻¹)⁻¹(E ×_S X)`. -/
def transitionSectionsIso
    (h₁ : (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E))
    (h₂ : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E)) :
    (pullback (D.over.hom ≫ f) f).sectionsRingOnSubset
        (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ≅
      (pullback f (D.over.hom ≫ f)).sectionsRingOnSubset
        (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) where
  hom := Scheme.sectionsRingOnSubsetMap D.transitionPullbackIso.inv _ _ h₂
  inv := Scheme.sectionsRingOnSubsetMap D.transitionPullbackIso.hom _ _ h₁
  hom_inv_id :=
    have h₀ : (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
        ⇑(𝟙 (pullback (D.over.hom ≫ f) f) : _ ⟶ _) ⁻¹'
          (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) := Set.Subset.refl _
    (Scheme.sectionsRingOnSubsetMap_comp D.transitionPullbackIso.hom
        D.transitionPullbackIso.inv _ _ _ h₂ h₁).trans
      ((Scheme.sectionsRingOnSubsetMap_congr D.transitionPullbackIso.hom_inv_id _ _ _ h₀).trans
        (Scheme.sectionsRingOnSubsetMap_id _ h₀))
  inv_hom_id :=
    have h₀ : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
        ⇑(𝟙 (pullback f (D.over.hom ≫ f)) : _ ⟶ _) ⁻¹'
          (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) := Set.Subset.refl _
    (Scheme.sectionsRingOnSubsetMap_comp D.transitionPullbackIso.inv
        D.transitionPullbackIso.hom _ _ _ h₁ h₂).trans
      ((Scheme.sectionsRingOnSubsetMap_congr D.transitionPullbackIso.inv_hom_id _ _ _ h₀).trans
        (Scheme.sectionsRingOnSubsetMap_id _ h₀))

/-- `Φ` is the restriction map along `φ⁻¹`. -/
lemma transitionSectionsIso_hom
    (h₁ : (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E))
    (h₂ : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E)) :
    (D.transitionSectionsIso E h₁ h₂).hom =
      Scheme.sectionsRingOnSubsetMap D.transitionPullbackIso.inv _ _ h₂ := rfl

/-- The inverse of `Φ` is the restriction map along `φ`. -/
lemma transitionSectionsIso_inv
    (h₁ : (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E))
    (h₂ : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E)) :
    (D.transitionSectionsIso E h₁ h₂).inv =
      Scheme.sectionsRingOnSubsetMap D.transitionPullbackIso.hom _ _ h₁ := rfl

/-- Set-theoretic invariance of `E` gives the containment `E ×_S X ⊆ φ⁻¹(X ×_S E)`. -/
lemma subset_preimage_transitionPullbackIso_hom (hE : D.IsTransitionInvariantSet E) :
    (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) :=
  fun z hz ↦ D.mem_of_isTransitionInvariantSet E hE z hz

/-- Set-theoretic invariance of `E` gives the containment `X ×_S E ⊆ φ(E ×_S X)`, in the form
`X ×_S E ⊆ (φ⁻¹)⁻¹(E ×_S X)`. -/
lemma subset_preimage_transitionPullbackIso_inv (hE : D.IsTransitionInvariantSet E) :
    (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) :=
  fun z hz ↦ D.mem_of_isTransitionInvariantSet' E hE z hz

/-- `Φ` for a set-theoretically invariant `E`: the two containments
`AlgebraicGeometry.DescentDatum.transitionSectionsIso` asks for are supplied by invariance. -/
def transitionSectionsIsoOfInvariant (hE : D.IsTransitionInvariantSet E) :
    (pullback (D.over.hom ≫ f) f).sectionsRingOnSubset
        (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ≅
      (pullback f (D.over.hom ≫ f)).sectionsRingOnSubset
        (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) :=
  D.transitionSectionsIso E (D.subset_preimage_transitionPullbackIso_hom E hE)
    (D.subset_preimage_transitionPullbackIso_inv E hE)

/-! ### `Φ` lies over `Γ(X) ⊗_{Γ(S)} Γ(X)` -/

/-- `Φ` carries the `Γ(E)`-leg of the first square to the `Γ(X)`-leg of the second: composed
with the structure map `Γ(X, ⊤) ⟶ Γ(E, 𝒪_V|_E)`, the comparison morphism of
`AlgebraicGeometry.DescentDatum.isPushout_sectionsRingOnSubset_transitionSource` followed by `Φ`
is the `Γ(X, ⊤)`-leg of
`AlgebraicGeometry.DescentDatum.isPushout_sectionsRingOnSubset_transitionTarget`. -/
theorem structureMap_comp_transitionSectionsIso_hom (E : Set D.over.left)
    (h₁ : (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E))
    (h₂ : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E)) :
    (D.over.hom.appTop ≫ D.over.left.topToSubset E) ≫
        Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
            (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
          (D.transitionSectionsIso E h₁ h₂).hom =
      (pullback.fst f (D.over.hom ≫ f)).appTop ≫
        (pullback f (D.over.hom ≫ f)).topToSubset
          (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) := by
  rw [transitionSectionsIso_hom, Category.assoc,
    Scheme.topToSubset_comp_sectionsRingOnSubsetMap_assoc,
    Scheme.topToSubset_comp_sectionsRingOnSubsetMap, ← Category.assoc, ← Category.assoc,
    ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
    D.transitionPullbackIso_inv_comp_pullbackFst]

/-- `Φ` carries the `Γ(X)`-leg of the first square to the `Γ(E)`-leg of the second: the
`Γ(X, ⊤)`-leg of `AlgebraicGeometry.DescentDatum.isPushout_sectionsRingOnSubset_transitionSource`
followed by `Φ` is the comparison morphism of
`AlgebraicGeometry.DescentDatum.isPushout_sectionsRingOnSubset_transitionTarget` precomposed with
the structure map `Γ(X, ⊤) ⟶ Γ(E, 𝒪_V|_E)`. -/
theorem base_comp_transitionSectionsIso_hom (E : Set D.over.left)
    (h₁ : (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E))
    (h₂ : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E)) :
    ((pullback.snd (D.over.hom ≫ f) f).appTop ≫
          (pullback (D.over.hom ≫ f) f).topToSubset
            (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E)) ≫
        (D.transitionSectionsIso E h₁ h₂).hom =
      (D.over.hom.appTop ≫ D.over.left.topToSubset E) ≫
        Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
          (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _) := by
  rw [transitionSectionsIso_hom, Category.assoc, Category.assoc,
    Scheme.topToSubset_comp_sectionsRingOnSubsetMap,
    Scheme.topToSubset_comp_sectionsRingOnSubsetMap, ← Category.assoc, ← Category.assoc,
    ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
    D.transitionPullbackIso_inv_comp_pullbackSnd]

/-! ### `Γ(E ×_S X)` and `Γ(X ×_S E)` as pushouts -/

variable [IsAffine S] [IsAffine X] [Flat f] [QuasiSeparatedSpace D.over.left]

/-- For `f : X ⟶ S` a flat morphism of affine schemes and `E` an intersection of a nonempty
family of quasi-compact opens of the quasi-separated scheme `V` underlying a descent datum,
```
Γ(E ×_S X, 𝒪) = Γ(E, 𝒪_V|_E) ⊗_{Γ(S, ⊤)} Γ(X, ⊤),
```
as a pushout square of rings with comparison morphism
`AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap`. -/
theorem isPushout_sectionsRingOnSubset_transitionSource {I : Type u} [Nonempty I]
    (U : I → D.over.left.Opens) (hU : ∀ i, IsCompact (U i : Set D.over.left))
    (E : Set D.over.left) (hE : E = ⋂ i, (U i : Set D.over.left)) :
    IsPushout ((D.over.hom ≫ f).appTop ≫ D.over.left.topToSubset E) f.appTop
      (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
        (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _))
      ((pullback.snd (D.over.hom ≫ f) f).appTop ≫
        (pullback (D.over.hom ≫ f) f).topToSubset
          (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E)) :=
  isPushout_sectionsRingOnSubsetMap_of_flat_of_isAffine
    (IsPullback.of_hasPullback (D.over.hom ≫ f) f) U hU E hE

/-- For `f : X ⟶ S` a flat morphism of affine schemes and `E` an intersection of a nonempty
family of quasi-compact opens of the quasi-separated scheme `V` underlying a descent datum,
```
Γ(X ×_S E, 𝒪) = Γ(E, 𝒪_V|_E) ⊗_{Γ(S, ⊤)} Γ(X, ⊤),
```
as a pushout square of rings with comparison morphism
`AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap`, the base change being taken along the
projection `X ×_S V ⟶ V`. -/
theorem isPushout_sectionsRingOnSubset_transitionTarget {I : Type u} [Nonempty I]
    (U : I → D.over.left.Opens) (hU : ∀ i, IsCompact (U i : Set D.over.left))
    (E : Set D.over.left) (hE : E = ⋂ i, (U i : Set D.over.left)) :
    IsPushout ((D.over.hom ≫ f).appTop ≫ D.over.left.topToSubset E) f.appTop
      (Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
        (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _))
      ((pullback.fst f (D.over.hom ≫ f)).appTop ≫
        (pullback f (D.over.hom ≫ f)).topToSubset
          (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E)) :=
  isPushout_sectionsRingOnSubsetMap_of_flat_of_isAffine
    (IsPullback.of_hasPullback f (D.over.hom ≫ f)).flip U hU E hE

end DescentDatum

end AlgebraicGeometry

end

end
