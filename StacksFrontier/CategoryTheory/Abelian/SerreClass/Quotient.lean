module

public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
public import StacksCore.CategoryTheory.Abelian.SerreClass.Localization
import StacksCore.Tactic.StacksAttribute

/-! # The Serre quotient `A/C` and its universal property

Stacks tag 02MS (Lemma 12.10.6). Let `A` be an abelian category and `C ⊂ A` a Serre subcategory.
There is an abelian category `A/C` and an exact functor `F : A ⥤ A/C` which is essentially
surjective and whose kernel is `C`. For any exact functor `G : A ⥤ B` with `C ⊂ Ker G` there is a
factorization `G = H ∘ F` for a unique exact functor `H : A/C ⥤ B`.

As in Mathlib's `ObjectProperty.SerreClassLocalization`, `A/C` is any category `D` with a
localization functor `L : C ⥤ D` for `P.isoModSerre`, a preadditive structure and `[L.Additive]`
(the localization `P.isoModSerre.Localization` with `P.isoModSerre.Q` is one). The clauses:

* `A/C` is abelian: Mathlib's `SerreClassLocalization.abelian`, whose preadditive structure is the
  given one (`exists_abelian`);
* `F` is exact: Mathlib's `preservesFiniteLimits` and `preservesFiniteColimits`;
* `F` is essentially surjective: `essSurj`;
* `Ker F = C`: `kernel_eq`, from Mathlib's `isZero_obj_iff`;
* the universal property: `exists_exact_lift` (an exact `H` with `L ⋙ H ≅ G`) and
  `existsUnique_iso_of_comp_iso` (any two such factorizations are related by a unique isomorphism
  compatible with the given ones). Mathlib's `fullyFaithfulWhiskeringLeft` and
  `essImage_whiskeringLeft` are the same statement as an equivalence of categories of exact
  functors.

`exists_abelian_and_universal` states the whole lemma.

## Implementation notes

The prose names the categories as the Stacks project does; in the code the abelian category `A`
is `C` and the Serre subcategory is the `ObjectProperty` `P`. The `H` of the Stacks statement is
unique in the only sense that is invariant under replacing `A/C` by an equivalent category: up to
a unique isomorphism compatible with the factorizations of `G`.
-/

@[expose] public section

universe u₃ v₃

namespace CategoryTheory.ObjectProperty.SerreClassLocalization

open Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C]
  (L : C ⥤ D) (P : ObjectProperty C) [P.IsSerreClass] [L.IsLocalization P.isoModSerre]
  [Preadditive D] [L.Additive]

add_to_stacks 02MS "`F` is exact: it preserves finite limits"
  CategoryTheory.ObjectProperty.SerreClassLocalization.preservesFiniteLimits
add_to_stacks 02MS "`F` is exact: it preserves finite colimits"
  CategoryTheory.ObjectProperty.SerreClassLocalization.preservesFiniteColimits
add_to_stacks 02MS "`Ker F = C`, objectwise: `F X = 0` iff `X ∈ C`"
  CategoryTheory.ObjectProperty.SerreClassLocalization.isZero_obj_iff
add_to_stacks 02MS "universal property: precomposing with `F` is fully faithful on exact functors"
  CategoryTheory.ObjectProperty.SerreClassLocalization.fullyFaithfulWhiskeringLeft
add_to_stacks 02MS
  "universal property: an exact functor factors through `F` iff it inverts `isoModSerre`"
  CategoryTheory.ObjectProperty.SerreClassLocalization.essImage_whiskeringLeft

include L P in
/-- **Stacks 02MS**, `A/C` is abelian: there is an abelian structure on `D` whose preadditive
structure is the given one. -/
@[stacks 02MS "`A/C` is abelian, with its given preadditive structure"]
theorem exists_abelian : ∃ h : Abelian D, h.toPreadditive = ‹Preadditive D› :=
  ⟨abelian L P, rfl⟩

omit [Preadditive D] [L.Additive] in
include P in
/-- **Stacks 02MS**, the quotient functor `F : A ⥤ A/C` is essentially surjective. -/
@[stacks 02MS "`F` is essentially surjective"]
theorem essSurj : L.EssSurj :=
  Localization.essSurj L P.isoModSerre

/-- **Stacks 02MS**, the kernel of the quotient functor `F : A ⥤ A/C` is exactly `C`. -/
@[stacks 02MS "`Ker F = C`"]
theorem kernel_eq : L.kernel = P := by
  ext X
  exact isZero_obj_iff L P X

variable {B : Type*} [Category* B] [Abelian B]

/-- **Stacks 02MS**, the universal property, existence: an exact `G : A ⥤ B` whose kernel contains
`C` factors as `G ≅ F ⋙ H` through an exact `H : A/C ⥤ B`. -/
@[stacks 02MS "universal property, existence of the exact factorization `G ≅ F ⋙ H`"]
theorem exists_exact_lift (G : C ⥤ B) [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (hG : P ≤ G.kernel) :
    ∃ H : D ⥤ B, PreservesFiniteLimits H ∧ PreservesFiniteColimits H ∧ Nonempty (L ⋙ H ≅ G) := by
  let e := liftOfLeKernelFac L P G hG
  have : PreservesFiniteLimits (L ⋙ liftOfLeKernel L P G hG) :=
    preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits (L ⋙ liftOfLeKernel L P G hG) :=
    preservesFiniteColimits_of_natIso e.symm
  exact ⟨_, (preservesFiniteLimits_comp_iff L P _).1 inferInstance,
    (preservesFiniteColimits_comp_iff L P _).1 inferInstance, ⟨e⟩⟩

omit [Preadditive D] [L.Additive] [Abelian B] in
include P in
/-- **Stacks 02MS**, the universal property, uniqueness: two factorizations `e₁ : F ⋙ H₁ ≅ G` and
`e₂ : F ⋙ H₂ ≅ G` are related by a unique isomorphism `φ : H₁ ≅ H₂` with `F ⋙ φ` followed by `e₂`
equal to `e₁`. -/
@[stacks 02MS "universal property, uniqueness of `H` up to a unique compatible isomorphism"]
theorem existsUnique_iso_of_comp_iso {G : C ⥤ B} (H₁ H₂ : D ⥤ B) (e₁ : L ⋙ H₁ ≅ G)
    (e₂ : L ⋙ H₂ ≅ G) : ∃! φ : H₁ ≅ H₂, Functor.isoWhiskerLeft L φ ≪≫ e₂ = e₁ := by
  let hL := Localization.fullyFaithfulWhiskeringLeft L P.isoModSerre B
  refine ⟨hL.preimageIso (e₁ ≪≫ e₂.symm), ?_, fun φ hφ ↦ ?_⟩
  · ext X
    have h := congrArg (fun τ ↦ τ.app X) (hL.map_preimage (e₁.hom ≫ e₂.inv))
    dsimp at h
    simp [h]
  · refine Iso.ext (hL.map_injective ?_)
    rw [hL.preimageIso_hom, hL.map_preimage]
    ext X
    change φ.hom.app (L.obj X) = e₁.hom.app X ≫ e₂.inv.app X
    simp [← hφ]

/-- **Stacks 02MS.** For a Serre subcategory `C` of an abelian category `A`, the quotient
`F : A ⥤ A/C` (any localization functor for `P.isoModSerre`) has: `A/C` abelian, `F` exact,
`F` essentially surjective, `Ker F = C`, and every exact `G : A ⥤ B` to an abelian category with
`C ⊂ Ker G` factors as `G ≅ F ⋙ H` through an exact `H`, unique up to a unique isomorphism
compatible with the factorizations. -/
@[stacks 02MS]
theorem exists_abelian_and_universal :
    (∃ h : Abelian D, h.toPreadditive = ‹Preadditive D›) ∧
      (PreservesFiniteLimits L ∧ PreservesFiniteColimits L) ∧ L.EssSurj ∧ L.kernel = P ∧
      ∀ {B : Type u₃} [Category.{v₃} B] [Abelian B] (G : C ⥤ B) [PreservesFiniteLimits G]
        [PreservesFiniteColimits G], P ≤ G.kernel →
        (∃ H : D ⥤ B, PreservesFiniteLimits H ∧ PreservesFiniteColimits H ∧
          Nonempty (L ⋙ H ≅ G)) ∧
        ∀ (H₁ H₂ : D ⥤ B) (e₁ : L ⋙ H₁ ≅ G) (e₂ : L ⋙ H₂ ≅ G),
          ∃! φ : H₁ ≅ H₂, Functor.isoWhiskerLeft L φ ≪≫ e₂ = e₁ :=
  ⟨exists_abelian L P, ⟨preservesFiniteLimits L P, preservesFiniteColimits L P⟩, essSurj L P,
    kernel_eq L P, fun G _ _ hG ↦
      ⟨exists_exact_lift L P G hG, fun H₁ H₂ e₁ e₂ ↦ existsUnique_iso_of_comp_iso L P H₁ H₂ e₁ e₂⟩⟩

end CategoryTheory.ObjectProperty.SerreClassLocalization
