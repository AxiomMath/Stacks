module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Subobject.Basic
public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.Finiteness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite type and finite quasi-coherent subalgebras

Let `X` be a scheme and `A` a sheaf of commutative `𝒪_X`-algebras. A *quasi-coherent subalgebra* of
`A` is a categorical subobject of `A` in the category
`Stacks.RelativeSpec.AlgebraSheaf X = Under X.sheaf` whose underlying algebra sheaf is
quasi-coherent. This file introduces the two full subcategories of such subobjects that occur in
the approximation theorems of the Stacks Project — those of finite type ([Stacks, Tag 05JT]) and
the finite ones ([Stacks, Tag 0817] (1)) — together with the canonical cocone from either diagram
to `A`.

If `A` is integral, then a quasi-coherent subalgebra of `A` is finite exactly when it is of finite
type, so the two diagrams coincide, and each of the two assertions of [Stacks, Tag 0817] (1)
follows from the corresponding assertion of [Stacks, Tag 05JT].

## Main definitions

* `Stacks.RelativeSpec.FiniteTypeSubalgebra` and `Stacks.RelativeSpec.FiniteSubalgebra`: the
  categories of quasi-coherent subalgebras of `A` which are of finite type, resp. finite.
* `Stacks.RelativeSpec.finiteTypeSubalgebraDiagram`, `Stacks.RelativeSpec.finiteSubalgebraDiagram`:
  the corresponding diagrams of algebra sheaves, and
  `Stacks.RelativeSpec.finiteTypeSubalgebraCocone`, `Stacks.RelativeSpec.finiteSubalgebraCocone`
  their canonical cocones with point `A`.

## Main results

* `Stacks.RelativeSpec.AlgebraSheaf.IsIntegral.subobject_isFinite_iff_isFiniteType`: a subalgebra
  of an integral algebra sheaf is finite if and only if it is of finite type.
* `Stacks.RelativeSpec.finiteSubalgebraProperty_eq_finiteTypeSubalgebraProperty`: for an integral
  algebra sheaf, the finite and the finite type quasi-coherent subalgebras coincide.
* `Stacks.CategoryTheory.isFiltered_subobject_fullSubcategory_iff`: a class of subobjects of a
  fixed object is filtered exactly when it is nonempty and any two of its members have a common
  upper bound.
* `Stacks.RelativeSpec.isFiltered_finiteTypeSubalgebra_iff`: the directedness assertion of
  [Stacks, Tag 05JT] is equivalent to the existence of upper bounds among the finite type
  quasi-coherent subalgebras.
* `Stacks.RelativeSpec.isFiltered_finiteSubalgebra_of_isFiltered` and
  `Stacks.RelativeSpec.isColimit_finiteSubalgebraCocone_of_isColimit`: the two assertions of
  [Stacks, Tag 0817] (1), given the two assertions of [Stacks, Tag 05JT].

## References

* [Stacks Project, Tag 02JJ](https://stacks.math.columbia.edu/tag/02JJ)
* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.CategoryTheory

variable {C : Type u} [Category.{v} C] {A : C}

/-- A class `P` of subobjects of a fixed object `A`, viewed as a full subcategory of `Subobject A`,
is filtered if and only if it is nonempty and any two of its members admit a common upper bound. -/
theorem isFiltered_subobject_fullSubcategory_iff (P : ObjectProperty (Subobject A)) :
    IsFiltered P.FullSubcategory ↔
      (∃ B, P B) ∧ ∀ B₁ B₂, P B₁ → P B₂ → ∃ Z, P Z ∧ B₁ ≤ Z ∧ B₂ ≤ Z := by
  constructor
  · intro h
    obtain ⟨⟨B, hB⟩⟩ := h.nonempty
    refine ⟨⟨B, hB⟩, fun B₁ B₂ h₁ h₂ ↦ ?_⟩
    obtain ⟨Z, f, g, -⟩ := IsFilteredOrEmpty.cocone_objs (C := P.FullSubcategory) ⟨B₁, h₁⟩ ⟨B₂, h₂⟩
    exact ⟨Z.obj, Z.property, leOfHom f.hom, leOfHom g.hom⟩
  · rintro ⟨⟨B, hB⟩, hdir⟩
    have : Nonempty P.FullSubcategory := ⟨⟨B, hB⟩⟩
    refine
      { cocone_objs := fun B₁ B₂ ↦ ?_
        cocone_maps := fun _ B₂ _ _ ↦ ⟨B₂, 𝟙 _, ObjectProperty.hom_ext P (Subsingleton.elim _ _)⟩ }
    obtain ⟨Z, hZ, h₁, h₂⟩ := hdir B₁.obj B₂.obj B₁.property B₂.property
    exact ⟨⟨Z, hZ⟩, ObjectProperty.homMk (homOfLE h₁), ObjectProperty.homMk (homOfLE h₂), trivial⟩

end Stacks.CategoryTheory

namespace Stacks.RelativeSpec

variable {X : Scheme.{u}}

namespace AlgebraSheaf

/-- A subalgebra of an integral algebra sheaf is finite exactly when it is of finite type. -/
theorem IsIntegral.subobject_isFinite_iff_isFiniteType {A : AlgebraSheaf X} (hA : A.IsIntegral)
    (B : Subobject A) :
    IsFinite (B : AlgebraSheaf X) ↔ IsFiniteType (B : AlgebraSheaf X) := by
  refine ⟨fun h ↦ h.isFiniteType, fun h U hU ↦ ?_⟩
  refine RingHom.IsIntegral.to_finite ?_ (h U hU)
  have hinj : Function.Injective (B.arrow.right.hom.app (op U)).hom :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp <|
      (NatTrans.mono_iff_mono_app B.arrow.right.hom).mp
        ((Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mp (Under.mono_right_of_mono B.arrow)) _
  refine RingHom.IsIntegral.tower_bot _ _ hinj ?_
  have hw := congrArg (fun k : X.sheaf ⟶ A.right ↦ (k.hom.app (op U)).hom) (Under.w B.arrow)
  change (B.arrow.right.hom.app (op U)).hom.comp ((B : AlgebraSheaf X).hom.hom.app (op U)).hom =
    (A.hom.hom.app (op U)).hom at hw
  rw [hw]
  exact hA U hU

end AlgebraSheaf

variable (A : AlgebraSheaf X)

/-- The property of a subobject of an algebra sheaf `A` that it is quasi-coherent and of finite
type. -/
@[ega "IV 8.12.2" "partial"]
def finiteTypeSubalgebraProperty : ObjectProperty (Subobject A) :=
  fun B ↦ (B : AlgebraSheaf X).IsQuasicoherent ∧ (B : AlgebraSheaf X).IsFiniteType

/-- The property of a subobject of an algebra sheaf `A` that it is quasi-coherent and finite. -/
def finiteSubalgebraProperty : ObjectProperty (Subobject A) :=
  fun B ↦ (B : AlgebraSheaf X).IsQuasicoherent ∧ (B : AlgebraSheaf X).IsFinite

/-- The category of finite type quasi-coherent subalgebras of `A`. -/
@[ega "IV 8.12.2" "partial"]
abbrev FiniteTypeSubalgebra := (finiteTypeSubalgebraProperty A).FullSubcategory

/-- The category of finite quasi-coherent subalgebras of `A`. -/
abbrev FiniteSubalgebra := (finiteSubalgebraProperty A).FullSubcategory

/-- The diagram of all finite type quasi-coherent subalgebras of `A`. -/
@[ega "IV 8.12.2" "partial"]
noncomputable def finiteTypeSubalgebraDiagram : FiniteTypeSubalgebra A ⥤ AlgebraSheaf X :=
  (finiteTypeSubalgebraProperty A).ι ⋙ Subobject.underlying

/-- The diagram of all finite quasi-coherent subalgebras of `A`. -/
noncomputable def finiteSubalgebraDiagram : FiniteSubalgebra A ⥤ AlgebraSheaf X :=
  (finiteSubalgebraProperty A).ι ⋙ Subobject.underlying

/-- The canonical cocone from the finite type quasi-coherent subalgebras of `A` to `A`, whose legs
are their inclusions. -/
noncomputable def finiteTypeSubalgebraCocone : Cocone (finiteTypeSubalgebraDiagram A) :=
  Cocone.mk A
    { app := fun B ↦ B.obj.arrow
      naturality := fun _ _ f ↦ Subobject.underlying_arrow f.hom }

/-- The canonical cocone from the finite quasi-coherent subalgebras of `A` to `A`, whose legs are
their inclusions. -/
noncomputable def finiteSubalgebraCocone : Cocone (finiteSubalgebraDiagram A) :=
  Cocone.mk A
    { app := fun B ↦ B.obj.arrow
      naturality := fun _ _ f ↦ Subobject.underlying_arrow f.hom }

/-- The finite type quasi-coherent subalgebras of `A` form a filtered category exactly when there
is at least one of them and any two of them are contained in a third. -/
theorem isFiltered_finiteTypeSubalgebra_iff :
    IsFiltered (FiniteTypeSubalgebra A) ↔
      (∃ B : Subobject A, finiteTypeSubalgebraProperty A B) ∧
        ∀ B₁ B₂ : Subobject A, finiteTypeSubalgebraProperty A B₁ →
          finiteTypeSubalgebraProperty A B₂ →
            ∃ Z, finiteTypeSubalgebraProperty A Z ∧ B₁ ≤ Z ∧ B₂ ≤ Z :=
  Stacks.CategoryTheory.isFiltered_subobject_fullSubcategory_iff _

/-- The finite quasi-coherent subalgebras of `A` form a filtered category exactly when there is at
least one of them and any two of them are contained in a third. -/
theorem isFiltered_finiteSubalgebra_iff :
    IsFiltered (FiniteSubalgebra A) ↔
      (∃ B : Subobject A, finiteSubalgebraProperty A B) ∧
        ∀ B₁ B₂ : Subobject A, finiteSubalgebraProperty A B₁ → finiteSubalgebraProperty A B₂ →
            ∃ Z, finiteSubalgebraProperty A Z ∧ B₁ ≤ Z ∧ B₂ ≤ Z :=
  Stacks.CategoryTheory.isFiltered_subobject_fullSubcategory_iff _

variable {A}

/-- For an integral algebra sheaf `A`, the two properties "quasi-coherent and finite" and
"quasi-coherent and of finite type" on subobjects of `A` are equal. -/
theorem finiteSubalgebraProperty_eq_finiteTypeSubalgebraProperty (hA : A.IsIntegral) :
    finiteSubalgebraProperty A = finiteTypeSubalgebraProperty A :=
  funext fun B ↦ propext
    (and_congr_right fun _ ↦ hA.subobject_isFinite_iff_isFiniteType B)

/-- For an integral algebra sheaf, the category of finite quasi-coherent subalgebras and the
category of finite type quasi-coherent subalgebras are equivalent, by the identity on
subobjects. -/
noncomputable def finiteSubalgebraEquiv (hA : A.IsIntegral) :
    FiniteSubalgebra A ≌ FiniteTypeSubalgebra A :=
  have hle : finiteSubalgebraProperty A ≤ finiteTypeSubalgebraProperty A :=
    fun B hB ↦ ⟨hB.1, (hA.subobject_isFinite_iff_isFiniteType B).mp hB.2⟩
  have hge : finiteTypeSubalgebraProperty A ≤ finiteSubalgebraProperty A :=
    fun B hB ↦ ⟨hB.1, (hA.subobject_isFinite_iff_isFiniteType B).mpr hB.2⟩
  { functor := ObjectProperty.ιOfLE hle
    inverse := ObjectProperty.ιOfLE hge
    unitIso := NatIso.ofComponents fun _ ↦ Iso.refl _
    counitIso := NatIso.ofComponents fun _ ↦ Iso.refl _ }

/-- If the finite type quasi-coherent subalgebras of an integral algebra sheaf form a filtered
category, then so do its finite quasi-coherent subalgebras. -/
theorem isFiltered_finiteSubalgebra_of_isFiltered (hA : A.IsIntegral)
    (h : IsFiltered (FiniteTypeSubalgebra A)) : IsFiltered (FiniteSubalgebra A) :=
  have := h
  IsFiltered.of_equivalence (finiteSubalgebraEquiv hA).symm

/-- If an integral algebra sheaf has at least one finite type quasi-coherent subalgebra and any two
of them are contained in a third, then its finite quasi-coherent subalgebras form a filtered
category. -/
theorem isFiltered_finiteSubalgebra_of_exists_upperBound (hA : A.IsIntegral)
    (h₀ : ∃ B : Subobject A, finiteTypeSubalgebraProperty A B)
    (h : ∀ B₁ B₂ : Subobject A, finiteTypeSubalgebraProperty A B₁ →
      finiteTypeSubalgebraProperty A B₂ →
        ∃ Z, finiteTypeSubalgebraProperty A Z ∧ B₁ ≤ Z ∧ B₂ ≤ Z) :
    IsFiltered (FiniteSubalgebra A) :=
  isFiltered_finiteSubalgebra_of_isFiltered hA (isFiltered_finiteTypeSubalgebra_iff A |>.2 ⟨h₀, h⟩)

/-- If an integral algebra sheaf is the colimit of its finite type quasi-coherent subalgebras, then
it is the colimit of its finite quasi-coherent subalgebras. -/
theorem isColimit_finiteSubalgebraCocone_of_isColimit (hA : A.IsIntegral)
    (h : Nonempty (IsColimit (finiteTypeSubalgebraCocone A))) :
    Nonempty (IsColimit (finiteSubalgebraCocone A)) :=
  h.map fun hc ↦ hc.whiskerEquivalence (finiteSubalgebraEquiv hA)

end Stacks.RelativeSpec

end
