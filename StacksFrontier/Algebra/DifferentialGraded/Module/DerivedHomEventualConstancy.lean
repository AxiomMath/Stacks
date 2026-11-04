module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomExactness
public import StacksFrontier.CategoryTheory.Functor.Derived.ValueReflection

/- Keep the admissible-sequence convention previously supplied by the global instance. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

/-!
# Eventual constancy of Deligne's ind-object for `Hom(K, -)`

Let `K` be a cochain complex in an abelian category `A` and let `E = End(K)` be its endomorphism
differential graded algebra. Tag 09LK assumes that the right derived functor of the
abelian-group-valued `Hom(K, -) : K(A) ⥤ D(Ab)` is everywhere defined and concludes the same for
the differential-graded-module-valued `Hom(K, -) : K(A) ⥤ D(E, d)`. The second statement implies
the first (`CochainComplex.isRightDerivable_homToDerivedCategoryForget`); the converse is the step
the source justifies by compatibility of the forgetful functor `D(E, d) ⥤ D(Ab)` with cohomology,
which supplies only conservativity, and
`StacksFrontier/CategoryTheory/Functor/Derived/ValueReflection.lean` shows that conservativity
reflects *eventual* constancy of a system
(`CategoryTheory.Functor.isEventuallyConstantFrom_of_comp`) but not *essential* constancy, which
is what being defined at an object asserts.

That left exactly one route to the converse open: were essential constancy in `D(Ab)` of the
particular systems that arise — Deligne's ind-object
`X/W ⟶ D(Ab)`, `(s : X ⟶ X') ↦ Hom(K, X')`
of Tag 05S9 — to force *eventual* constancy, conservativity would carry it back and the source's
hypothesis would imply the corrected one. This file closes that route, by a dichotomy for these
systems which has nothing to do with essential constancy at all.

Every transition morphism of the ind-object is `Hom(K, f)` for a quasi-isomorphism `f` of `K(A)`
(two-out-of-three in the index category), and `Hom(K, -) : K(A) ⥤ D(E, d)` is exact, so `f` sits
in a distinguished triangle whose third vertex is acyclic and `Hom(K, f)` is invertible exactly
when `Hom(K, -)` kills that vertex. Hence:

* if `Hom(K, -)` kills every acyclic object — as it does when `K` is K-projective — then *every*
  transition morphism of *every* one of these systems is invertible, so each is eventually
  constant from each of its indices, and both derivability hypotheses hold for trivial reasons;
* if some acyclic `Z` has `Hom(K, Z) ≠ 0` in `D(E, d)`, which by conservativity of the forgetful
  functor happens as soon as `K` is not K-projective, then out of *every* object `Y` of `K(A)`
  there is a quasi-isomorphism `Y ⟶ C` that `Hom(K, -)` does not invert, namely the second arrow
  of a distinguished triangle on `Z ⟶ Y`. It is a transition morphism out of any prescribed
  index, so *no* system of this shape, at *no* object `X` and from *no* index, is eventually
  constant.

The second case is the one Tag 09LK is about: if `K` were K-projective the functor being derived
would already invert the quasi-isomorphisms and no derivation would be needed. So for these
systems eventual constancy fails identically, while essential constancy does not: at a zero
object of `K(A)` the ind-object is essentially constant with value a zero object, in `D(E, d)` and
hence in `D(Ab)`. That is a system of exactly Tag 05S9's shape, for an actual object of `K(A)`,
whose image in `D(Ab)` is essentially constant and which is eventually constant from no index.
The implication to be upgraded is therefore false, and the route through
`CategoryTheory.Functor.isEventuallyConstantFrom_of_comp` is closed.

## Main results

* `HomotopyCategory.quasiIso_right_of_under`: every transition morphism of the index category
  `X/W` of Tag 05S9, for `W` the quasi-isomorphisms, is itself a quasi-isomorphism.
* `CochainComplex.isIso_homToDerivedCategory_map_of_quasiIso`: if `Hom(K, -) : K(A) ⥤ D(E, d)`
  kills every acyclic object then it inverts every quasi-isomorphism.
* `CochainComplex.exists_quasiIso_not_isIso_map_homToDerivedCategory`: conversely, an acyclic `Z`
  with `Hom(K, Z) ≠ 0` produces, out of *every* object of `K(A)`, a quasi-isomorphism that
  `Hom(K, -)` does not invert.
* `CochainComplex.isEventuallyConstantFrom_homToDerivedCategory` and
  `CochainComplex.not_isEventuallyConstantFrom_homToDerivedCategory`: the two halves of the
  dichotomy for Deligne's ind-object, and
  `CochainComplex.not_isEventuallyConstantFrom_homToDerivedCategoryForget` for the second half
  read in `D(Ab)`, where conservativity of the forgetful functor transports it.
* `CochainComplex.exists_isRightDerivedValueAt_homToDerivedCategory_of_isZero`: the right derived
  functor of the `D(E, d)`-valued `Hom(K, -)` is defined at every zero object of `K(A)`, with
  value a zero object.
* `CochainComplex.isEssentiallyConstantInd_and_not_isEventuallyConstantFrom`: **the refutation.**
  For `K` admitting an acyclic `Z` with `Hom(K, Z) ≠ 0`, and `X` a zero object of `K(A)`,
  Deligne's ind-object at `X` has an essentially constant image in `D(Ab)` and is eventually
  constant from no index.

## Implementation notes

*What the witness settles, and what it does not.* It settles the question asked: for the systems
of Tag 05S9 attached to `Hom(K, -)`, essential constancy of the image in `D(Ab)` does not force
eventual constancy, so `CategoryTheory.Functor.isEventuallyConstantFrom_of_comp` cannot carry the
source's hypothesis back to the corrected one. It does *not* refute Tag 09LK's own implication:
at a zero object the ind-object is essentially constant in `D(E, d)` as well — that is how its
image in `D(Ab)` is seen to be essentially constant — so the witness is consistent with the
converse. What it removes is the last route to the converse identified in the implementation
notes of `StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomVariant.lean`; the deviation
recorded there therefore stands.

*Why eventual constancy is hopeless here, and not by accident.* The second half of the dichotomy
is proved out of *every* object, so it is not a statement about a special `X` or a special index:
under Tag 09LK's own hypothesis the ind-object is essentially constant at every object of `K(A)`
and eventually constant at none. The reason is visible in the proof: a transition morphism is a
quasi-isomorphism, and `Hom(K, -)` inverts a quasi-isomorphism exactly when it kills the acyclic
third vertex of a triangle on it, so invertibility of transitions is not a property of the system
but of `K` alone. The index category can always be enlarged by an acyclic complex that `Hom(K, -)`
does not kill — the two-periodic witness of
`StacksFrontier/CategoryTheory/Functor/Derived/ValueReflection.lean` is of that kind — and essential
constancy, which only demands a retraction, survives such an enlargement while eventual constancy
cannot.

*Why the hypothesis is non-vacuous.* `Hom(K, Z) ≠ 0` for some acyclic `Z` says precisely that `K`
is not K-projective, and this is elementary: over `A = ModuleCat ℤ`, for `K` the complex `ℤ/2` in
degree `0` and `Z` the acyclic complex `ℤ → ℤ → ℤ/2` with first map multiplication by `2`, the
Hom complex `Hom(K, Z)` is `ℤ/2` in degree `2`, so it is not acyclic, and by conservativity of
the forgetful functor its class in `D(E, d)` is nonzero. That computation is classical and is not
formalized here, exactly as for the Ext computation underlying the witnesses of
`StacksFrontier/CategoryTheory/Functor/Derived/ValueReflection.lean`; the hypothesis is carried as
an argument instead. The complementary case is harmless rather than exceptional: a K-projective
`K` makes `Hom(K, -) : K(A) ⥤ D(E, d)` invert the quasi-isomorphisms, so it factors through
`D(A)` and Tag 09LK has no content for it.

*Why two-out-of-three is proved again here.* `HomotopyCategory.quasiIso_right_of_under` rests on
the two-out-of-three property of the quasi-isomorphisms of a homotopy category, which is
also proved in `StacksFrontier/Algebra/Homology/DerivedCategory/KInjective.lean` as
`hasTwoOutOfThreeProperty_quasiIso`. That lemma is `private`, hence unusable from here, and the
property is not an instance in Mathlib for `HomotopyCategory.quasiIso`; the three lines are
repeated rather than the other file being edited, and this note records the duplication so that a
later consolidation can remove one of the two.

*Why the zero object, rather than a K-injective resolution.* The cheapest object at which the
ind-object is essentially constant is a zero object of `K(A)`: the cone on the identity of any
`X'` is a zero object of `K(A)`, the transition into it is carried to a morphism with zero target,
and `CategoryTheory.EssentiallyConstantInd.exists_isEssentiallyConstantWith_isZero` turns that
cofinal vanishing into the witness. Nothing is lost by this choice: the refutation needs one
system that is essentially constant in `D(Ab)` and is not eventually constant, and the second half
of the dichotomy applies to every object, so any other essentially constant instance would do as
well.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), the statement whose
  hypothesis is at issue; being defined at an object is
  [Tag 05S9](https://stacks.math.columbia.edu/tag/05S9) and essential constancy is
  [Tag 05PU](https://stacks.math.columbia.edu/tag/05PU).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w u

namespace HomotopyCategory

variable {A : Type u} [Category.{0} A] [Preadditive A] [CategoryWithHomology A]

/-- **Every transition morphism of the index category `X/W` of Tag 05S9 is a quasi-isomorphism**,
for `W` the quasi-isomorphisms of `K(A)`. A morphism of `X/W` is an arbitrary morphism `u` of
`K(A)` under `X`, so `i.hom ≫ u.right = j.hom` with both structure morphisms quasi-isomorphisms,
and two-out-of-three — here the cancellation of an invertible left factor, applied to each
cohomology functor, which detects the quasi-isomorphisms — leaves `u.right` a
quasi-isomorphism. -/
theorem quasiIso_right_of_under {X : HomotopyCategory A (ComplexShape.up ℤ)}
    {i j : (quasiIso A (ComplexShape.up ℤ)).Under ⊤ X} (u : i ⟶ j) :
    quasiIso A (ComplexShape.up ℤ) u.right := by
  intro n
  have hi := i.prop n
  have hj := j.prop n
  rw [← MorphismProperty.Under.w u, Functor.map_comp] at hj
  exact IsIso.of_isIso_comp_left ((homologyFunctor A (ComplexShape.up ℤ) n).map i.hom) _

end HomotopyCategory

namespace CochainComplex

variable (A : Type u) [Category.{0} A] [Abelian A] (K : CochainComplex A ℤ)

/-- **If `Hom(K, -) : K(A) ⥤ D(E, d)` kills every acyclic object then it inverts every
quasi-isomorphism.** A quasi-isomorphism is the first arrow of a distinguished triangle whose
third vertex is acyclic, the functor is exact, and in a distinguished triangle the first arrow is
invertible exactly when the third vertex is zero. -/
theorem isIso_homToDerivedCategory_map_of_quasiIso
    (hK : ∀ Z : HomotopyCategory A (ComplexShape.up ℤ), HomotopyCategory.subcategoryAcyclic A Z →
      IsZero ((homToDerivedCategory A K).obj Z))
    {Y Y' : HomotopyCategory A (ComplexShape.up ℤ)} (f : Y ⟶ Y')
    (hf : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) f) :
    IsIso ((homToDerivedCategory A K).map f) := by
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at hf
  obtain ⟨Z, g, h, hT, hZ⟩ := hf
  exact (Triangle.isZero₃_iff_isIso₁ _
    ((homToDerivedCategory A K).map_distinguished _ hT)).1 (hK Z hZ)

/-- **An acyclic object that `Hom(K, -)` does not kill blocks the inversion of a
quasi-isomorphism out of every object.** If `Z` is acyclic and `Hom(K, Z)` is nonzero in
`D(E, d)`, then every object `Y` of `K(A)` admits a quasi-isomorphism `Y ⟶ C` that
`Hom(K, -) : K(A) ⥤ D(E, d)` does not invert: complete `0 : Z ⟶ Y` to a distinguished triangle
`Z ⟶ Y ⟶ C ⟶ Z[1]`; its second arrow is a quasi-isomorphism because its first vertex is acyclic,
and were its image invertible the image of the triangle would have zero first vertex. -/
theorem exists_quasiIso_not_isIso_map_homToDerivedCategory
    {Z : HomotopyCategory A (ComplexShape.up ℤ)}
    (hZac : HomotopyCategory.subcategoryAcyclic A Z)
    (hZ : ¬ IsZero ((homToDerivedCategory A K).obj Z))
    (Y : HomotopyCategory A (ComplexShape.up ℤ)) :
    ∃ (C : HomotopyCategory A (ComplexShape.up ℤ)) (g : Y ⟶ C),
      HomotopyCategory.quasiIso A (ComplexShape.up ℤ) g ∧
        ¬ IsIso ((homToDerivedCategory A K).map g) := by
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle (0 : Z ⟶ Y)
  refine ⟨C, g, ?_, fun hiso => hZ (Triangle.isZero₁_of_isIso₂ _
    ((homToDerivedCategory A K).map_distinguished _ hT) hiso)⟩
  have h' : (HomotopyCategory.subcategoryAcyclic A).trW g := ObjectProperty.trW.mk' _ hT hZac
  rwa [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at h'

/-- **The harmless half of the dichotomy.** If `Hom(K, -) : K(A) ⥤ D(E, d)` kills every acyclic
object — as it does when `K` is K-projective — then Deligne's ind-object
`(s : X ⟶ X') ↦ Hom(K, X')` is eventually constant from every one of its indices, at every object
`X`: every transition morphism is a quasi-isomorphism, and the functor inverts those. In this case
the functor being derived inverts the quasi-isomorphisms outright, so it factors through `D(A)`
and both derivability hypotheses of Tag 09LK hold for trivial reasons. -/
theorem isEventuallyConstantFrom_homToDerivedCategory
    (hK : ∀ Z : HomotopyCategory A (ComplexShape.up ℤ), HomotopyCategory.subcategoryAcyclic A Z →
      IsZero ((homToDerivedCategory A K).obj Z))
    (X : HomotopyCategory A (ComplexShape.up ℤ))
    (i₀ : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ X) :
    (MorphismProperty.Under.forget (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ X ⋙
        Under.forget X ⋙ homToDerivedCategory A K).IsEventuallyConstantFrom i₀ := by
  intro j u
  exact isIso_homToDerivedCategory_map_of_quasiIso A K hK u.right
    (HomotopyCategory.quasiIso_right_of_under u)

/-- A functor whose isomorphisms are among those of `Hom(K, -) : K(A) ⥤ D(E, d)` is eventually
constant on no ind-object of Tag 05S9 as soon as an acyclic `Z` has `Hom(K, Z)` nonzero. -/
private theorem not_isEventuallyConstantFrom_comp {T : Type*} [Category T]
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ T)
    (hF : ∀ {Y Y' : HomotopyCategory A (ComplexShape.up ℤ)} (g : Y ⟶ Y'),
      IsIso (F.map g) → IsIso ((homToDerivedCategory A K).map g))
    {Z : HomotopyCategory A (ComplexShape.up ℤ)}
    (hZac : HomotopyCategory.subcategoryAcyclic A Z)
    (hZ : ¬ IsZero ((homToDerivedCategory A K).obj Z))
    {X : HomotopyCategory A (ComplexShape.up ℤ)}
    (i₀ : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ X) :
    ¬ (MorphismProperty.Under.forget (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ X ⋙
        Under.forget X ⋙ F).IsEventuallyConstantFrom i₀ := by
  obtain ⟨C, g, hg, hgiso⟩ :=
    exists_quasiIso_not_isIso_map_homToDerivedCategory A K hZac hZ i₀.right
  exact Functor.not_isEventuallyConstantFrom_of_not_isIso_map i₀ g
    (MorphismProperty.comp_mem _ _ _ i₀.prop hg) fun hiso => hgiso (hF g hiso)

/-- **The other half of the dichotomy: Deligne's ind-object is never eventually constant.** If
some acyclic `Z` has `Hom(K, Z)` nonzero in `D(E, d)` — as happens whenever `K` is not
K-projective, by conservativity of the forgetful functor — then at no object `X` of `K(A)` and
from no index is the ind-object
`(s : X ⟶ X') ↦ Hom(K, X')` eventually constant: the quasi-isomorphism out of `i₀.right` supplied
by `CochainComplex.exists_quasiIso_not_isIso_map_homToDerivedCategory` is a transition morphism
out of `i₀`, since the index category inverts nothing and `W` is multiplicative, and its image is
not invertible. -/
theorem not_isEventuallyConstantFrom_homToDerivedCategory
    {Z : HomotopyCategory A (ComplexShape.up ℤ)}
    (hZac : HomotopyCategory.subcategoryAcyclic A Z)
    (hZ : ¬ IsZero ((homToDerivedCategory A K).obj Z))
    (X : HomotopyCategory A (ComplexShape.up ℤ))
    (i₀ : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ X) :
    ¬ (MorphismProperty.Under.forget (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ X ⋙
        Under.forget X ⋙ homToDerivedCategory A K).IsEventuallyConstantFrom i₀ :=
  not_isEventuallyConstantFrom_comp A K _ (fun _ h => h) hZac hZ i₀

/-- **The right derived functor of the `D(E, d)`-valued `Hom(K, -)` is defined at every zero
object**, with value a zero object. For any index `s : X ⟶ X'`, the cone on `𝟙 X'` is a zero
object of `K(A)`, the structure morphism into it is a quasi-isomorphism because it is a morphism
between zero objects, and `Hom(K, -)` carries the transition into it to a morphism whose target is
a zero object, hence to zero; so the transition morphisms vanish cofinally, and
`CategoryTheory.EssentiallyConstantInd.exists_isEssentiallyConstantWith_isZero` turns that into
the essential-constancy witness. -/
theorem exists_isRightDerivedValueAt_homToDerivedCategory_of_isZero
    (X : HomotopyCategory A (ComplexShape.up ℤ)) (hX : IsZero X) :
    ∃ c, (homToDerivedCategory A K).IsRightDerivedValueAt
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) X c := by
  rw [Functor.exists_isRightDerivedValueAt_iff]
  have hcof : ∀ j : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ X,
      ∃ (k : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ X) (τ : j ⟶ k),
        (homToDerivedCategory A K).map τ.right = 0 := by
    intro j
    obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle (𝟙 j.right)
    have hC : IsZero C :=
      Triangle.isZero₃_of_isIso₁ _ hT (inferInstanceAs (IsIso (𝟙 j.right)))
    have hFC : IsZero ((homToDerivedCategory A K).obj C) := Functor.map_isZero _ hC
    have hiso : IsIso (j.hom ≫ g) := by
      rw [hX.eq_of_src (j.hom ≫ g) (hX.iso hC).hom]
      infer_instance
    have hq : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) (j.hom ≫ g) := fun n =>
      inferInstance
    exact ⟨MorphismProperty.Under.mk ⊤ (j.hom ≫ g) hq, MorphismProperty.Under.homMk g rfl,
      hFC.eq_of_tgt _ _⟩
  obtain ⟨t, i, r, -, hw⟩ := EssentiallyConstantInd.exists_isEssentiallyConstantWith_isZero
    (MorphismProperty.Under.forget (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ X ⋙
      Under.forget X ⋙ homToDerivedCategory A K) hcof
  exact ⟨t, i, r, hw⟩

variable [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]

/-- **Deligne's ind-object is never eventually constant, read in `D(Ab)`.** The same conclusion
for the abelian-group-valued functor the source right derives: conservativity of the forgetful
functor `D(E, d) ⥤ D(Ab)`
(`DifferentialGradedModule.isIso_iff_isIso_derivedForget_map`) carries the non-invertibility back,
so the system whose essential constancy is Tag 09LK's hypothesis is eventually constant from no
index either. -/
theorem not_isEventuallyConstantFrom_homToDerivedCategoryForget
    {Z : HomotopyCategory A (ComplexShape.up ℤ)}
    (hZac : HomotopyCategory.subcategoryAcyclic A Z)
    (hZ : ¬ IsZero ((homToDerivedCategory A K).obj Z))
    (X : HomotopyCategory A (ComplexShape.up ℤ))
    (i₀ : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ X) :
    ¬ (MorphismProperty.Under.forget (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ X ⋙
        Under.forget X ⋙ homToDerivedCategoryForget A K).IsEventuallyConstantFrom i₀ :=
  not_isEventuallyConstantFrom_comp A K _
    (fun _ h => (DifferentialGradedModule.isIso_iff_isIso_derivedForget_map (endAlgebra A K) _).2 h)
    hZac hZ i₀

/-- **The refutation.** Let `K` be a cochain complex that is not K-projective, in the form in
which the proofs above use it: some acyclic `Z` has `Hom(K, Z)` nonzero in `D(E, d)`. Let `X` be a
zero object of `K(A)`. Then Deligne's ind-object of Tag 05S9 at `X`, read through the forgetful
functor in `D(Ab)` as the source reads it, is essentially constant — so Tag 09LK's hypothesis
holds at `X` — and is eventually constant from no index.

Essential constancy in `D(Ab)` therefore does not force eventual constancy for the systems that
Tag 09LK's hypothesis is about, and
`CategoryTheory.Functor.isEventuallyConstantFrom_of_comp` cannot be used to carry that hypothesis
back along the forgetful functor. The second clause is not vacuous: the index category always has
`𝟙 X` as an object, the quasi-isomorphisms containing the identities. The witness does not
contradict Tag 09LK: at a zero object the ind-object is essentially constant in `D(E, d)` too,
which is how the first clause is proved. -/
theorem isEssentiallyConstantInd_and_not_isEventuallyConstantFrom
    {Z : HomotopyCategory A (ComplexShape.up ℤ)}
    (hZac : HomotopyCategory.subcategoryAcyclic A Z)
    (hZ : ¬ IsZero ((homToDerivedCategory A K).obj Z))
    (X : HomotopyCategory A (ComplexShape.up ℤ)) (hX : IsZero X) :
    EssentiallyConstantInd.IsEssentiallyConstantInd
        (MorphismProperty.Under.forget (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ X ⋙
          Under.forget X ⋙ homToDerivedCategoryForget A K) ∧
      ∀ i₀ : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ X,
        ¬ (MorphismProperty.Under.forget (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ X ⋙
            Under.forget X ⋙ homToDerivedCategoryForget A K).IsEventuallyConstantFrom i₀ := by
  refine ⟨?_, not_isEventuallyConstantFrom_homToDerivedCategoryForget A K hZac hZ X⟩
  obtain ⟨c, hc⟩ := exists_isRightDerivedValueAt_homToDerivedCategory_of_isZero A K X hX
  rw [← Functor.exists_isRightDerivedValueAt_iff]
  exact ⟨_, isRightDerivedValueAt_homToDerivedCategoryForget A K _ hc⟩

end CochainComplex

end
