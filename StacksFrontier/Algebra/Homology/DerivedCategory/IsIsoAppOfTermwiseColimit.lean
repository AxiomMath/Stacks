module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedColimits
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolutionPostnikov
public import StacksFrontier.Homology.HomologyColimit

/-!
# A morphism of exact functors commuting with direct sums is invertible on a termwise colimit

Let `A` and `B` be Grothendieck abelian categories and let `L, R : D(A) ⥤ D(B)` be exact functors
commuting with countable direct sums. For a morphism `φ : L ⟶ R` and a system
`S : ℕ ⥤ C(A)` of complexes, if `φ` is invertible at every `Q(Sₙ)` then it is invertible at
`Q(colim Sₙ)`.

This is the "our functors commute with direct sums, hence with homotopy colimits" step of the
proof of [Stacks, Tag 0F1N]. `Q(colim Sₙ)` is a derived colimit of the `Q(Sₙ)`, with the images
of the colimit coprojections as coprojections ([Stacks, Tag 0949]). `L` and `R` carry it to
derived colimits of the image systems ([Stacks, Tag 090Z]), and the cohomology functors
`Hⁱ : D(B) ⥤ B`, which are homological and commute with countable direct sums, turn those into
ordinary colimits ([Stacks, Tag 0CRK]). So `Hⁱ(φ)` at `Q(colim Sₙ)` is the colimit of the
`Hⁱ(φ)` at the `Q(Sₙ)`, an isomorphism, and the `Hⁱ` detect isomorphisms of `D(B)`.

Only the naturality of `φ` is used, never a compatibility of `φ` with the shifts: the
argument runs on cohomology objects, where the coprojections of the derived colimits are images
of morphisms of `D(A)`.

The case used is the tower of stupid truncations `σ^{≥-n}K` of a complex `K`, whose colimit is
`K`. It gives the reduction of the source to bounded below objects:
`isIso_app_of_forall_isGE`.

## Main results

* `Stacks.DerivedCategoryColimit.isIso_app_Q_obj_colimit` — invertibility at a termwise
  colimit.
* `Stacks.DerivedCategoryColimit.isIso_app_Q_obj_of_stupidTrunc` — invertibility at `Q(K)` from
  invertibility at every `Q(σ^{≥-n}K)`.
* `Stacks.DerivedCategoryColimit.isIso_app_of_forall_isGE` — invertibility everywhere from
  invertibility at the bounded below objects.

## References

* [Stacks Project, Tag 0F1N](https://stacks.math.columbia.edu/tag/0F1N)
* [Stacks Project, Tag 0949](https://stacks.math.columbia.edu/tag/0949)
* [Stacks Project, Tag 0CRK](https://stacks.math.columbia.edu/tag/0CRK)
-/

@[expose] public section

universe w₁ w₂ z₁ z₂ v₁ v₂ u₁ u₂

open CategoryTheory Limits Pretriangulated

namespace Stacks.DerivedCategoryColimit

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{w₁} A]
  [HasDerivedCategory.{z₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{w₂} B]
  [HasDerivedCategory.{z₂} B]

omit [HasDerivedCategory A] in
/-- In a Grothendieck abelian category countable direct sums exist and are exact. -/
theorem hasExactCountableDirectSums : HasExactCountableDirectSums A where
  hasCoproducts := inferInstance
  exact_colim := fun J _ => by
    have : HasExactColimitsOfShape (Discrete J) A :=
      HasExactColimitsOfShape.of_domain_equivalence A (Discrete.equivalence Equiv.ulift.{w₁})
    exact ⟨inferInstance, inferInstance⟩

/-- The localization functor of a Grothendieck abelian category, at any model of its derived
category, preserves countable direct sums (Stacks 0A5L). -/
theorem preservesColimitsOfShape_discrete_nat_Q :
    PreservesColimitsOfShape (Discrete ℕ) (DerivedCategory.Q (C := A)) :=
  derivedCategory_Q_preservesCoproductsOfShape A hasExactCountableDirectSums ℕ

/-- The cohomology functors of the derived category of a Grothendieck abelian category, at any
model, preserve countable direct sums: so do the localization functor and the cohomology of
complexes, countable direct sums being exact. -/
theorem preservesColimitsOfShape_discrete_nat_homologyFunctor (i : ℤ) :
    PreservesColimitsOfShape (Discrete ℕ) (DerivedCategory.homologyFunctor B i) := by
  have := preservesColimitsOfShape_discrete_nat_Q (A := B)
  have : HasExactColimitsOfShape (Discrete ℕ) B :=
    HasExactColimitsOfShape.of_domain_equivalence B (Discrete.equivalence Equiv.ulift.{w₂})
  have := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor (A := B)
    (J := Discrete ℕ) (ComplexShape.up ℤ) i
  have : PreservesColimitsOfShape (Discrete ℕ)
      (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor B i) :=
    preservesColimitsOfShape_of_natIso (DerivedCategory.homologyFunctorFactors B i).symm
  exact preservesColimitsOfShape_discrete_of_essSurj_comp DerivedCategory.Q _ ℕ

variable [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
  [HasExactColimitsOfShape ℕ B]
  {L R : DerivedCategory A ⥤ DerivedCategory B} [L.CommShift ℤ] [R.CommShift ℤ]
  [L.IsTriangulated] [R.IsTriangulated]
  [PreservesColimitsOfShape (Discrete ℕ) L] [PreservesColimitsOfShape (Discrete ℕ) R]

/-- The family of images of a family with a coproduct has a coproduct, up to the evident
isomorphism. -/
private theorem hasCoproduct_obj_comp {C D : Type*} [Category C] [Category D] (F : ℕ ⥤ C)
    (G : C ⥤ D) [HasCoproduct F.obj] [PreservesColimitsOfShape (Discrete ℕ) G] :
    HasCoproduct (F ⋙ G).obj :=
  have : HasColimit (Discrete.functor F.obj ⋙ G) := inferInstance
  hasColimit_of_iso (F := Discrete.functor F.obj ⋙ G) (Discrete.natIso fun _ => Iso.refl _)

/-- **A morphism of exact functors commuting with countable direct sums is invertible at a
termwise colimit as soon as it is invertible at every member of the system.** -/
theorem isIso_app_Q_obj_colimit (φ : L ⟶ R) (S : ℕ ⥤ CochainComplex A ℤ)
    (hS : ∀ n, IsIso (φ.app (DerivedCategory.Q.obj (S.obj n)))) :
    IsIso (φ.app (DerivedCategory.Q.obj (colimit S))) := by
  have := preservesColimitsOfShape_discrete_nat_Q (A := A)
  have : HasCoproduct (S ⋙ DerivedCategory.Q).obj := hasCoproduct_obj_comp S _
  have : HasCoproduct ((S ⋙ DerivedCategory.Q) ⋙ L).obj := hasCoproduct_obj_comp _ L
  have : HasCoproduct ((S ⋙ DerivedCategory.Q) ⋙ R).obj := hasCoproduct_obj_comp _ R
  have hS' := DerivedCategory.isHomotopyColimitWith_Q_obj_colimit S
  obtain ⟨pL, qL, hTL, hpL⟩ := hS'.map L
  obtain ⟨pR, qR, hTR, hpR⟩ := hS'.map R
  rw [DerivedCategory.isIso_iff]
  intro i
  let H := DerivedCategory.homologyFunctor B i
  have := preservesColimitsOfShape_discrete_nat_homologyFunctor (B := B) i
  obtain ⟨eL, heL⟩ := exists_iso_colimit_of_isHomotopyColimit _ H pL qL hTL
  obtain ⟨eR, heR⟩ := exists_iso_colimit_of_isHomotopyColimit _ H pR qR hTR
  let α : ((S ⋙ DerivedCategory.Q) ⋙ L) ⋙ H ⟶ ((S ⋙ DerivedCategory.Q) ⋙ R) ⋙ H :=
    Functor.whiskerRight (Functor.whiskerLeft (S ⋙ DerivedCategory.Q) φ) H
  have : ∀ n, IsIso (α.app n) := fun n => by
    have := hS n
    dsimp [α]
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  have key : H.map (φ.app (DerivedCategory.Q.obj (colimit S))) =
      eL.inv ≫ colimMap α ≫ eR.hom := by
    rw [← cancel_epi eL.hom, Iso.hom_inv_id_assoc]
    refine colimit.hom_ext fun n => ?_
    rw [reassoc_of% (heL n), ι_colimMap_assoc, heR n, hpL n, hpR n]
    simp only [α, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj,
      ← H.map_comp, φ.naturality]
  rw [key]
  infer_instance

/-- **Invertibility at a complex from invertibility at its stupid truncations.** A morphism of
exact functors commuting with countable direct sums is invertible at `Q(K)` as soon as it is
invertible at every `Q(σ^{≥-n}K)`, `n ∈ ℕ`: `K` is the colimit of the tower of its stupid
truncations. -/
theorem isIso_app_Q_obj_of_stupidTrunc (φ : L ⟶ R) (K : CochainComplex A ℤ)
    (hK : ∀ n : ℕ, IsIso (φ.app (DerivedCategory.Q.obj
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE (-(n : ℤ))))))) :
    IsIso (φ.app (DerivedCategory.Q.obj K)) :=
  (NatTrans.isIso_app_iff_of_iso φ
    (DerivedCategory.Q.mapIso (StacksDraft.BrutalPostnikov.colimitTruncTowerIso K))).1
    (isIso_app_Q_obj_colimit φ (StacksDraft.BrutalPostnikov.truncTower K) hK)

/-- **A morphism of exact functors commuting with countable direct sums is invertible as soon as
it is invertible at the bounded below objects.** Every object is `Q(K)` for a complex `K`, and the
stupid truncations `σ^{≥-n}K` are bounded below. -/
theorem isIso_app_of_forall_isGE (φ : L ⟶ R)
    (h : ∀ (E : DerivedCategory A) (a : ℤ), E.IsGE a → IsIso (φ.app E))
    (E : DerivedCategory A) : IsIso (φ.app E) := by
  refine (NatTrans.isIso_app_iff_of_iso φ (DerivedCategory.Q.objObjPreimageIso E)).1 ?_
  refine isIso_app_Q_obj_of_stupidTrunc φ _ fun n => h _ (-(n : ℤ)) ?_
  rw [DerivedCategory.isGE_Q_obj_iff]
  infer_instance

end Stacks.DerivedCategoryColimit
