module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningOfFormallyUnramified

/-!
# Two universal first-order thickenings of one morphism of algebraic spaces

Let `h : Z ⟶ X` be a morphism of algebraic spaces over a scheme `S`.  A universal first-order
thickening of `h`, in the sense of `AlgebraicGeometry.Space.UniversalFirstOrderThickening`, is
not unique on the nose: it is a choice of ambient space, of a closed subspace of it, and of an
identification of `Z` with that subspace.  The universal property of Stacks 0602 nevertheless
pins the choice down up to a unique isomorphism, exactly as the scheme-level
`Stacks.Thickenings.UniversalFirstOrderThickening.canonicalIso` does one category down.

## Main definitions

* `AlgebraicGeometry.Space.UniversalFirstOrderThickening.subComparison`: the identification of
  the smaller spaces of two universal first-order thickenings of `h`, read through the two
  identifications of `Z` with them.
* `AlgebraicGeometry.Space.UniversalFirstOrderThickening.canonicalMap`: the canonical morphism
  between the ambient spaces, the morphism of Stacks 060A at the identity square on `h`.
* `AlgebraicGeometry.Space.UniversalFirstOrderThickening.canonicalIso`: the two ambient spaces
  are canonically isomorphic.

## Main results

* `AlgebraicGeometry.Space.UniversalFirstOrderThickening.canonicalMap_restrict` and
  `AlgebraicGeometry.Space.UniversalFirstOrderThickening.canonicalMap_over`: the canonical
  morphism restricts to `subComparison` on the smaller space and lies over `X`.
* `AlgebraicGeometry.Space.UniversalFirstOrderThickening.eq_canonicalMap`: those two
  commutativities characterise it.
* `AlgebraicGeometry.Space.UniversalFirstOrderThickening.isIso_of_restrict_of_over`: any
  morphism of thickenings over `X` between two universal first-order thickenings of `h` is an
  isomorphism.

## Implementation notes

Everything here is Stacks 060A at the identity square `h ≫ 𝟙 X = 𝟙 Z ≫ h`, assembled from the
public interface of `StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningFunctorial.lean`:
`AlgebraicGeometry.Space.universalThickeningMap` for the morphism, its two commutativities, and
`AlgebraicGeometry.Space.eq_universalThickeningMap` for the uniqueness that makes the two
composites identities.  No new appeal to the universal property is made.

The identity square is not quite the identity on the data, because the two thickenings identify
`Z` with their smaller spaces by different isomorphisms; the morphism of smaller spaces is
therefore `subComparison`, the composite of one identification with the inverse of the other,
rather than `𝟙`.  That is the only difference from the scheme-level development, where the
smaller object of a thickening is `Z` itself and the comparison is literally `𝟙 Z`.

## References

* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 0606](https://stacks.math.columbia.edu/tag/0606)
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
* [Stacks Project, Tag 060A](https://stacks.math.columbia.edu/tag/060A)
* [Stacks Project, Tag 04F2](https://stacks.math.columbia.edu/tag/04F2), the case of schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

namespace UniversalFirstOrderThickening

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Z X : AlgebraicSpaces B S hS} {h : Z ⟶ X}

/-! ### The identity square on `h` -/

/-- The structure morphism of a universal first-order thickening, read through the
identification of `Z` with the smaller space: the composite `Z' ⊃ Z ≅ Z ⟶ X` is `h` with that
identification undone. -/
theorem sub_ι_toBase (t : UniversalFirstOrderThickening B S hS h) :
    t.sub.ι ≫ t.toBase.hom = t.sourceIso.inv ≫ h.hom := by
  rw [← t.sourceIso_ι_toBase, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The identification of the smaller spaces of two universal first-order thickenings of `h`:
undo the first identification of `Z` and redo the second. -/
def subComparison (t₁ t₂ : UniversalFirstOrderThickening B S hS h) :
    t₁.sub.toFunctor ⟶ t₂.sub.toFunctor :=
  t₁.sourceIso.inv ≫ t₂.sourceIso.hom

/-- The identification of the smaller space of a thickening with itself is the identity. -/
theorem subComparison_self (t : UniversalFirstOrderThickening B S hS h) :
    subComparison t t = 𝟙 t.sub.toFunctor := by
  rw [subComparison, Iso.inv_hom_id]

/-- The identifications of the smaller spaces compose. -/
theorem subComparison_comp (t₁ t₂ t₃ : UniversalFirstOrderThickening B S hS h) :
    subComparison t₁ t₂ ≫ subComparison t₂ t₃ = subComparison t₁ t₃ := by
  rw [subComparison, subComparison, subComparison, Category.assoc,
    ← Category.assoc t₂.sourceIso.hom, Iso.hom_inv_id, Category.id_comp]

/-- The solid diagram of Stacks 0602 at the identity square on `h`: the two structure morphisms
agree once the smaller spaces are identified.  This is the hypothesis that
`AlgebraicGeometry.Space.universalThickeningMap` consumes. -/
theorem subComparison_sq (t₁ t₂ : UniversalFirstOrderThickening B S hS h) :
    t₁.sub.ι ≫ t₁.toBase.hom ≫ (𝟙 X : X ⟶ X).hom
      = subComparison t₁ t₂ ≫ t₂.sub.ι ≫ t₂.toBase.hom := by
  have hright : subComparison t₁ t₂ ≫ t₂.sub.ι ≫ t₂.toBase.hom = t₁.sourceIso.inv ≫ h.hom := by
    rw [subComparison, Category.assoc, t₂.sourceIso_ι_toBase]
  rw [hright, ← sub_ι_toBase t₁, ObjectProperty.FullSubcategory.id_hom, Category.comp_id]

/-! ### The canonical morphism -/

/-- **The canonical morphism between two universal first-order thickenings of `h`**: the
morphism of Stacks 060A attached to the identity square on `h`. -/
noncomputable def canonicalMap (t₁ t₂ : UniversalFirstOrderThickening B S hS h) :
    t₁.ambient ⟶ t₂.ambient :=
  universalThickeningMap B S hS (𝟙 X) (subComparison t₁ t₂) t₁.isUniversal t₂.isUniversal
    (subComparison_sq t₁ t₂)

/-- The canonical morphism restricts to the identification of the smaller spaces. -/
theorem canonicalMap_restrict (t₁ t₂ : UniversalFirstOrderThickening B S hS h) :
    t₁.sub.ι ≫ (canonicalMap t₁ t₂).hom = subComparison t₁ t₂ ≫ t₂.sub.ι :=
  universalThickeningMap_restrict B S hS (𝟙 X) (subComparison t₁ t₂) t₁.isUniversal
    t₂.isUniversal (subComparison_sq t₁ t₂)

/-- The canonical morphism is a morphism over `X`. -/
theorem canonicalMap_over (t₁ t₂ : UniversalFirstOrderThickening B S hS h) :
    canonicalMap t₁ t₂ ≫ t₂.toBase = t₁.toBase :=
  (universalThickeningMap_over B S hS (𝟙 X) (subComparison t₁ t₂) t₁.isUniversal
    t₂.isUniversal (subComparison_sq t₁ t₂)).trans (Category.comp_id _)

/-- **The canonical morphism is canonical.**  A morphism of the ambient spaces which restricts
to the identification of the smaller spaces and lies over `X` is the canonical one. -/
theorem eq_canonicalMap (t₁ t₂ : UniversalFirstOrderThickening B S hS h)
    (c : t₁.ambient ⟶ t₂.ambient)
    (hc : t₁.sub.ι ≫ c.hom = subComparison t₁ t₂ ≫ t₂.sub.ι)
    (hc' : c ≫ t₂.toBase = t₁.toBase) :
    c = canonicalMap t₁ t₂ :=
  eq_universalThickeningMap B S hS (𝟙 X) (subComparison t₁ t₂) t₁.isUniversal t₂.isUniversal
    (subComparison_sq t₁ t₂) c hc (by rw [hc', Category.comp_id])

/-- The canonical morphism from a universal first-order thickening to itself is the identity. -/
theorem canonicalMap_self (t : UniversalFirstOrderThickening B S hS h) :
    canonicalMap t t = 𝟙 t.ambient :=
  (eq_canonicalMap t t (𝟙 t.ambient)
    (by rw [subComparison_self, ObjectProperty.FullSubcategory.id_hom, Category.comp_id,
      Category.id_comp])
    (Category.id_comp _)).symm

/-- The canonical morphisms between universal first-order thickenings of `h` compose. -/
theorem canonicalMap_comp (t₁ t₂ t₃ : UniversalFirstOrderThickening B S hS h) :
    canonicalMap t₁ t₂ ≫ canonicalMap t₂ t₃ = canonicalMap t₁ t₃ :=
  eq_canonicalMap t₁ t₃ _
    (by
      rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc, canonicalMap_restrict,
        Category.assoc,
        canonicalMap_restrict, ← Category.assoc, subComparison_comp])
    (by rw [Category.assoc, canonicalMap_over, canonicalMap_over])

/-- The two canonical morphisms between two universal first-order thickenings of `h` are
mutually inverse. -/
theorem canonicalMap_comp_canonicalMap (t₁ t₂ : UniversalFirstOrderThickening B S hS h) :
    canonicalMap t₁ t₂ ≫ canonicalMap t₂ t₁ = 𝟙 t₁.ambient := by
  rw [canonicalMap_comp, canonicalMap_self]

/-- **Two universal first-order thickenings of one morphism of algebraic spaces have
canonically isomorphic ambient spaces.** -/
noncomputable def canonicalIso (t₁ t₂ : UniversalFirstOrderThickening B S hS h) :
    t₁.ambient ≅ t₂.ambient where
  hom := canonicalMap t₁ t₂
  inv := canonicalMap t₂ t₁
  hom_inv_id := canonicalMap_comp_canonicalMap t₁ t₂
  inv_hom_id := canonicalMap_comp_canonicalMap t₂ t₁

/-- **Any morphism of thickenings over `X` between two universal first-order thickenings of `h`
is an isomorphism**, since it is the canonical one. -/
theorem isIso_of_restrict_of_over (t₁ t₂ : UniversalFirstOrderThickening B S hS h)
    (c : t₁.ambient ⟶ t₂.ambient)
    (hc : t₁.sub.ι ≫ c.hom = subComparison t₁ t₂ ≫ t₂.sub.ι)
    (hc' : c ≫ t₂.toBase = t₁.toBase) :
    IsIso c := by
  rw [eq_canonicalMap t₁ t₂ c hc hc']
  exact ⟨canonicalMap t₂ t₁, canonicalMap_comp_canonicalMap t₁ t₂,
    canonicalMap_comp_canonicalMap t₂ t₁⟩

/-! ### The thickening of a morphism of schemes -/

/-- **A scheme-level universal first-order thickening of a morphism of the site, read as a
universal first-order thickening of the algebraic spaces its source and target represent.**

The universal property is
`AlgebraicGeometry.Space.isUniversalFirstOrderThickening_range_yoneda_map`, which is where the
passage from the scheme-level test diagrams to the space-level ones happens; the smaller space
is the range of the Yoneda image of the inclusion, and `Z` is identified with it by the
comparison with the range, invertible because the inclusion is a closed immersion hence a
monomorphism.

Formal unramifiedness is a hypothesis rather than a conclusion.  It is a field of
`AlgebraicGeometry.Space.UniversalFirstOrderThickening` and a property of the morphism being
thickened, not of the thickening, so in the one place this definition is used it is supplied by
the thickening already in hand. -/
noncomputable def ofSite {V₀ U₀ V' : BigFppfOver B S hS} {q : V₀ ⟶ U₀}
    (hfu : FormallyUnramified ((schemeSpaceFunctor B S hS).map q).hom)
    (i : V₀ ⟶ V') (p : V' ⟶ U₀)
    (ht : Stacks.Thickenings.IsUniversalFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map q) ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map p)) :
    UniversalFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).map q) := by
  have hclosed : IsClosedImmersion B S hS (yoneda.map i) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.IsClosedImmersion.{u}) i).2 ht.isFirstOrderThickening.1
  have hiso : IsIso (Subfunctor.toRange (yoneda.map i)) := by
    have : Mono (yoneda.map i) := mono_of_isClosedImmersion B S hS (yoneda.map i) hclosed
    infer_instance
  have hip : i ≫ p = q := (BigFppfOver.toScheme B S hS).map_injective
    ((Functor.map_comp _ _ _).trans ht.inclusion_toBase)
  exact
    { formallyUnramified := hfu
      ambient := (schemeSpaceFunctor B S hS).obj V'
      toBase := (schemeSpaceFunctor B S hS).map p
      sub := Subfunctor.range (yoneda.map i)
      isUniversal := isUniversalFirstOrderThickening_range_yoneda_map B S hS i p ht
      sourceIso := @asIso _ _ _ _ (Subfunctor.toRange (yoneda.map i)) hiso
      sourceIso_ι_toBase :=
        ((Category.assoc (Subfunctor.toRange (yoneda.map i))
              (Subfunctor.range (yoneda.map i)).ι (yoneda.map p)).symm.trans
            (congrArg (fun z => z ≫ yoneda.map p)
              (Subfunctor.toRange_ι (yoneda.map i)))).trans
          ((yoneda.map_comp i p).symm.trans (congrArg yoneda.map hip)) }

/-- **The ambient space of a universal first-order thickening of a morphism of schemes is the
algebraic space represented by the ambient scheme of a scheme-level universal first-order
thickening of the same morphism.**

This is the identification of the two universal first-order thickenings of a representable
morphism: `AlgebraicGeometry.Space.UniversalFirstOrderThickening.canonicalIso` at the
space-level thickening in hand and the one the scheme-level thickening represents. -/
noncomputable def representedAmbientIso {V₀ U₀ V' : BigFppfOver B S hS} {q : V₀ ⟶ U₀}
    (s : UniversalFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).map q))
    (i : V₀ ⟶ V') (p : V' ⟶ U₀)
    (ht : Stacks.Thickenings.IsUniversalFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map q) ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map p)) :
    s.ambient ≅ (schemeSpaceFunctor B S hS).obj V' :=
  canonicalIso s (ofSite s.formallyUnramified i p ht)

/-- The identification of the ambient spaces restricts to the identification of the smaller
spaces. -/
theorem representedAmbientIso_restrict {V₀ U₀ V' : BigFppfOver B S hS} {q : V₀ ⟶ U₀}
    (s : UniversalFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).map q))
    (i : V₀ ⟶ V') (p : V' ⟶ U₀)
    (ht : Stacks.Thickenings.IsUniversalFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map q) ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map p)) :
    s.sub.ι ≫ (representedAmbientIso s i p ht).hom.hom
      = subComparison s (ofSite s.formallyUnramified i p ht) ≫
        (Subfunctor.range (yoneda.map i)).ι :=
  canonicalMap_restrict s (ofSite s.formallyUnramified i p ht)

/-- The identification of the ambient spaces lies over the common target. -/
theorem representedAmbientIso_over {V₀ U₀ V' : BigFppfOver B S hS} {q : V₀ ⟶ U₀}
    (s : UniversalFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).map q))
    (i : V₀ ⟶ V') (p : V' ⟶ U₀)
    (ht : Stacks.Thickenings.IsUniversalFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map q) ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map p)) :
    (representedAmbientIso s i p ht).hom ≫ (schemeSpaceFunctor B S hS).map p = s.toBase :=
  canonicalMap_over s (ofSite s.formallyUnramified i p ht)

end UniversalFirstOrderThickening

end AlgebraicGeometry.Space

end
