module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.MorphismsIntoBoundedBelowInjectives
import StacksCore.Tactic.StacksAttribute

/-!
# The bounded below derived category and complexes of injectives

Let `A` be an abelian category with enough injectives and let `I ⊆ A` be the additive
subcategory of injective objects. Writing `K(A) = HomotopyCategory A (ComplexShape.up ℤ)`,
the full subcategory `K⁺(I)` of `K(A)` on the bounded below complexes of injective objects
is carried by the localization functor to an equivalence `K⁺(I) ≌ D⁺(A)`.

Fully faithfulness is part (1) of [Stacks, Tag 03T6] — morphisms into a bounded below
complex of injectives do not change on passing from `K(A)` to `D(A)` — which is
`CochainComplex.Qh_map_bijective_of_injective_of_plus`; essential surjectivity is the
existence of bounded below injective resolutions,
`CochainComplex.exists_injectiveResolution_isStrictlyGE`.

## Main definitions

* `CategoryTheory.HomotopyCategory.plusInjective`: the property of an object of the homotopy
  category of being bounded below with injective terms.
* `CategoryTheory.HomotopyCategory.PlusInjective`: the category `K⁺(I)` cut out by that
  property.
* `CategoryTheory.HomotopyCategory.PlusInjective.toDerivedPlus`: the canonical functor
  `K⁺(I) ⥤ D⁺(A)`.

## Main results

* `CategoryTheory.HomotopyCategory.PlusInjective.isEquivalence_toDerivedPlus`
  ([Stacks, Tag 03T6] part (3)): the canonical functor `K⁺(I) ⥤ D⁺(A)` is an equivalence
  when `A` has enough injectives.

## Implementation notes

The source's `K⁺(I)`, the homotopy category of the additive subcategory of injectives, is
realized as the full subcategory of `K(A)` on the complexes that are bounded below and
degreewise injective; this is the image of the source's category under the fully faithful
functor induced by `I ⊆ A`, so the two have the same objects and the same morphisms.
The `HasDerivedCategory` hypothesis is the universe-sensitive existence assumption for
Mathlib's chosen derived category.

Fully faithfulness needs no hypothesis on `A`: it is part (1) of the tag, which holds for
every abelian category. Only essential surjectivity consumes `EnoughInjectives A`.

As with part (4) of the tag, `CategoryTheory.HomotopyCategory.MinusProjective`, the
equivalence is recorded as `Functor.IsEquivalence` of the canonical functor; the source's
parenthetical "as triangulated categories" is not part of the conclusion formalized here.

## References

* [Stacks Project, Tag 03T6](https://stacks.math.columbia.edu/tag/03T6)
-/

@[expose] public noncomputable section

namespace CategoryTheory

universe w v u

namespace HomotopyCategory

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- The property of an object of the homotopy category of cochain complexes that it is
strictly bounded below and all its terms are injective. -/
def plusInjective : ObjectProperty (HomotopyCategory A (.up ℤ)) :=
  fun K ↦ (∃ n : ℤ, CochainComplex.IsStrictlyGE K.as n) ∧ ∀ i : ℤ, Injective (K.as.X i)

/-- The category `K⁺(I)` of bounded below complexes of injective objects up to homotopy. -/
abbrev PlusInjective := (plusInjective A).FullSubcategory

namespace PlusInjective

variable [HasDerivedCategory.{w} A]

/-- The canonical functor `K⁺(I) ⥤ D⁺(A)`, the restriction of the localization functor. -/
def toDerivedPlus : PlusInjective A ⥤ DerivedCategory.Plus A :=
  ObjectProperty.lift DerivedCategory.TStructure.t.plus
    ((plusInjective A).ι ⋙ DerivedCategory.Qh) (by
      rintro ⟨K, ⟨n, hn⟩, _⟩
      refine ⟨n, K.as, (DerivedCategory.quotientCompQhIso A).app K.as, ?_⟩
      let _ := hn
      infer_instance)

private lemma nonempty_fullyFaithful_toDerivedPlus :
    Nonempty ((toDerivedPlus A ⋙ DerivedCategory.Plus.ι).FullyFaithful) := by
  show Nonempty (((plusInjective A).ι ⋙ DerivedCategory.Qh).FullyFaithful)
  rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
  rintro ⟨X, hX⟩ ⟨Y, hY⟩
  obtain ⟨I, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  obtain ⟨n, hn⟩ := hY.1
  let _ : ∀ n, Injective (I.X n) := hY.2
  exact (CochainComplex.Qh_map_bijective_of_injective_of_plus X I ⟨n, hn⟩).comp
    (((plusInjective A).fullyFaithfulι).map_bijective _ _)

private lemma essSurj_toDerivedPlus [EnoughInjectives A] :
    (toDerivedPlus A).EssSurj := by
  refine ⟨fun Y ↦ ?_⟩
  obtain ⟨n, hn⟩ := Y.property
  obtain ⟨K, hK, ⟨e⟩⟩ := Y.obj.exists_iso_Q_obj_of_isGE n
  obtain ⟨R, -, hR⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE n K
  have : IsIso (DerivedCategory.Q.map R.ι) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso A R.ι).mpr R.quasiIso
  exact ⟨⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj R.cocomplex,
    ⟨⟨n, hR⟩, R.injective⟩⟩, ⟨(DerivedCategory.TStructure.t.plus).fullyFaithfulι.preimageIso
    ((DerivedCategory.quotientCompQhIso A).app R.cocomplex ≪≫
      (asIso (DerivedCategory.Q.map R.ι)).symm ≪≫ e.symm)⟩⟩

/-- **Stacks 03T6, part (3).** If `A` has enough injectives and `I ⊆ A` is the additive
subcategory of injectives, then `D⁺(A) ≅ K⁺(I)`: the canonical functor from the bounded below
homotopy category of complexes of injective objects to the bounded below derived category is
an equivalence. -/
@[stacks 03T6 "injective_equivalence", sga "4½ Etat_0 3.2.3" "(3)", sga "4½ Etat_0 3.1.4"]
theorem isEquivalence_toDerivedPlus [EnoughInjectives A] :
    (toDerivedPlus A).IsEquivalence := by
  let hff := (Classical.choice (nonempty_fullyFaithful_toDerivedPlus A)).ofCompFaithful
  exact ⟨hff.faithful, hff.full, essSurj_toDerivedPlus A⟩

end PlusInjective

end HomotopyCategory

end CategoryTheory
