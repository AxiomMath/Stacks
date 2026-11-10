module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.HomToInjectiveSingle
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveHomotopy

/-!
# A morphism of derived categories killed by a jointly faithful family of exact functors

Let `A` be an abelian category and `F r : A ⥤ B r` a family of exact functors which is
*jointly faithful with gluing*: a morphism of `A` vanishes as soon as all its images do, and every
family of morphisms `F r M ⟶ F r N` is the family of images of one morphism `M ⟶ N`. If the
`F r` carry K-injective complexes to K-injective complexes and `A` has K-injective resolutions,
then a morphism of `D(A)` vanishes as soon as all its images under the induced functors
`D(A) ⥤ D(B r)` do.

The motivating case is the restrictions of sheaves of modules to the members of a decomposition
of a space into disjoint open subsets: the derived category of the space then embeds into the
product of the derived categories of the pieces, which is the sense in which "the derived category
decomposes as a product" in the proof of [Stacks, Tag 0FUW].

The proof: a morphism `Q(K) ⟶ Q(I)` with `I` K-injective is the class of a morphism of complexes
`f : K ⟶ I`; each `F r f` is null-homotopic because its target is K-injective and its class
vanishes; the homotopies glue to a homotopy of `f` to zero, because the defining identities of a
homotopy can be checked after applying the `F r`.

## Main results

* `DerivedCategory.eq_zero_of_forall_mapDerivedCategory_map_eq_zero`: the vanishing.

## References

* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
* [Stacks Project, Tag 070G](https://stacks.math.columbia.edu/tag/070G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

universe w w' v v' u u'

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {ι : Type*} {B : ι → Type u'} [∀ r, Category.{v'} (B r)] [∀ r, Abelian (B r)]
  [∀ r, HasDerivedCategory.{w'} (B r)] (F : ∀ r, A ⥤ B r) [∀ r, (F r).Additive]
  [∀ r, PreservesFiniteLimits (F r)] [∀ r, PreservesFiniteColimits (F r)]

omit [HasDerivedCategory.{w} A] [∀ r, HasDerivedCategory.{w'} (B r)]
  [∀ r, PreservesFiniteLimits (F r)] [∀ r, PreservesFiniteColimits (F r)] in
/-- **A homotopy assembled from homotopies of the images.** If the images of `f : K ⟶ L` under a
jointly faithful family of additive functors with gluing are all null-homotopic, then `f` is. -/
theorem nonempty_homotopy_zero_of_forall
    (hglue : ∀ (M N : A) (h : ∀ r, (F r).obj M ⟶ (F r).obj N), ∃ g : M ⟶ N, ∀ r, (F r).map g = h r)
    (hinj : ∀ {M N : A} (g : M ⟶ N), (∀ r, (F r).map g = 0) → g = 0)
    {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (H : ∀ r, Homotopy (((F r).mapHomologicalComplex (ComplexShape.up ℤ)).map f) 0) :
    Nonempty (Homotopy f 0) := by
  choose g hg using fun n m => hglue (K.X n) (L.X m) fun r => (H r).hom n m
  refine ⟨{ hom := fun n m => if (ComplexShape.up ℤ).Rel m n then g n m else 0,
            zero := fun n m hnm => ite_eq_right hnm
            comm := fun n => ?_ }⟩
  refine sub_eq_zero.mp (hinj _ fun r => ?_)
  have hc := (H r).comm n
  rw [Functor.map_sub, sub_eq_zero]
  simp only [HomologicalComplex.zero_f, add_zero, Functor.mapHomologicalComplex_map_f] at hc ⊢
  rw [hc, Functor.map_add]
  have h₁ : (ComplexShape.up ℤ).Rel n (n + 1) := by simp
  have h₂ : (ComplexShape.up ℤ).Rel (n - 1) n := by simp
  congr 1
  · rw [dNext_eq _ h₁, dNext_eq _ h₁, Functor.map_comp, ite_eq_left h₁, hg]
    rfl
  · rw [prevD_eq _ h₂, prevD_eq _ h₂, Functor.map_comp, ite_eq_left h₂, hg]
    rfl

/-- **A morphism of `D(A)` killed by a jointly faithful family of exact functors vanishes.** Let
the exact functors `F r : A ⥤ B r` carry K-injective complexes to K-injective complexes, let every
complex of `A` have a K-injective resolution, and let the family be jointly faithful with gluing.
A morphism of `D(A)` whose images in all the `D(B r)` vanish is zero. -/
theorem eq_zero_of_forall_mapDerivedCategory_map_eq_zero
    (hK : ∀ r (I : CochainComplex A ℤ), I.IsKInjective →
      CochainComplex.IsKInjective (((F r).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
    (hres : ∀ Y : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (_ : I.IsKInjective) (q : Y ⟶ I), QuasiIso q)
    (hglue : ∀ (M N : A) (h : ∀ r, (F r).obj M ⟶ (F r).obj N), ∃ g : M ⟶ N, ∀ r, (F r).map g = h r)
    (hinj : ∀ {M N : A} (g : M ⟶ N), (∀ r, (F r).map g = 0) → g = 0)
    {X Y : DerivedCategory A} (φ : X ⟶ Y) (hφ : ∀ r, (F r).mapDerivedCategory.map φ = 0) :
    φ = 0 := by
  obtain ⟨I, hI, q, hq⟩ := hres (Q.objPreimage Y)
  let eX := Q.objObjPreimageIso X
  let eY : Q.obj I ≅ Y := (asIso (Q.map q)).symm ≪≫ Q.objObjPreimageIso Y
  obtain ⟨f, hf⟩ := Q_map_surjective_of_isKInjective (Q.objPreimage X) I (eX.hom ≫ φ ≫ eY.inv)
  suffices h : Q.map f = 0 by
    rw [show φ = eX.inv ≫ Q.map f ≫ eY.hom by simp [hf], h, zero_comp, comp_zero]
  have H : ∀ r, Homotopy (((F r).mapHomologicalComplex (ComplexShape.up ℤ)).map f) 0 := fun r => by
    have := hK r I hI
    have h₂ : (F r).mapDerivedCategoryFactors.hom.app _ ≫
        Q.map (((F r).mapHomologicalComplex (ComplexShape.up ℤ)).map f) = 0 := by
      rw [← (F r).mapDerivedCategoryFactors_hom_naturality f, hf]
      simp [hφ r]
    exact CochainComplex.homotopyOfQMapEq
      (((Preadditive.IsIso.comp_left_eq_zero _ _).mp h₂).trans (Q.map_zero _ _).symm)
  obtain ⟨h⟩ := nonempty_homotopy_zero_of_forall F hglue hinj f H
  rw [Q_map_eq_of_homotopy (C := A) h, Functor.map_zero]

end DerivedCategory
