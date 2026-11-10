module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated
public import StacksFrontier.RingTheory.LocalCohomology.Sweep.ClosedSupportColimit

/-!
# Derived sections with support are a triangulated functor

Let `A` be a commutative ring and `T ⊆ Spec(A)` a subset. The total right derived functor
`RΓ_T : D(A) ⥤ D(A)` of sections with support in `T`, namely
`Stacks.LocalCohomology.derivedSectionsWithSupportIn`, is shown here to commute
with the shift and to send distinguished triangles to distinguished triangles. Consequently a
short exact sequence of `A`-modules

`0 → M₁ → M₂ → M₃ → 0`

gives rise to a long exact sequence of local cohomology modules

`⋯ → H^i_T(M₁) → H^i_T(M₂) → H^i_T(M₃) → H^{i+1}_T(M₁) → ⋯`

with all of its maps, including the connecting map. This is the long exact sequence used
throughout the Faltings induction of [Stacks, Tag 0AW8] and in the depth computations of
[Stacks, Tag 0AVZ].

## Main definitions

* `Stacks.LocalCohomology.localCohomologyMap` — the map `H^i_T(M) ⟶ H^i_T(N)` induced by a map of
  modules `M ⟶ N`.
* `Stacks.LocalCohomology.localCohomologyTriangle` — the distinguished triangle in `D(A)` obtained
  by applying `RΓ_T` to the triangle of a short exact sequence of modules.
* `Stacks.LocalCohomology.localCohomologyδ` — the connecting map
  `H^i_T(M₃) ⟶ H^{i+1}_T(M₁)`.

## Main results

* `Stacks.LocalCohomology.derivedSectionsWithSupportIn_isTriangulated` — `RΓ_T` is triangulated.
* `Stacks.LocalCohomology.localCohomologyTriangle_distinguished` — the triangle of a short exact
  sequence is distinguished.
* `Stacks.LocalCohomology.localCohomology_exact₁`,
  `Stacks.LocalCohomology.localCohomology_exact₂`,
  `Stacks.LocalCohomology.localCohomology_exact₃` — the three exactness assertions that make up
  the long exact sequence.
* `Stacks.LocalCohomology.epi_localCohomologyMap_g_iff`,
  `Stacks.LocalCohomology.mono_localCohomologyMap_f_iff` — the two degeneration criteria, which
  say that the connecting map vanishes.

## Implementation notes

Triangulatedness is obtained from Mathlib's `Functor.isTriangulated_of_leftExtension`, which
reduces the statement to producing, for every morphism `f` of `D(A)`, a distinguished triangle of
`K(A)` whose first map represents `f` and on whose three vertices the canonical comparison
`derivedSectionsWithSupportInUnit` is invertible. The vertices on which that comparison is
invertible are the K-injective complexes
(`Stacks.LocalCohomology.isIso_derivedSectionsWithSupportInUnit_app`), and K-injective complexes
are stable under mapping cones (Tag 090X, proved as
`CochainComplex.isKInjective_two_out_of_three_of_distTriang`), so it suffices to represent `f`
by a morphism of K-injective complexes. That is possible because `Qh` is bijective on morphisms
into a K-injective complex (`CochainComplex.IsKInjective.Qh_map_bijective`) and because the
homotopy-category quotient functor is full.

The shift-compatibility is Mathlib's `Functor.IsRightDerivedFunctor.commShift`; it has to be
provided explicitly because `derivedSectionsWithSupportIn` is a definition wrapping
`Functor.totalRightDerived` and instance search does not unfold it.

No Stacks attribute is placed. Triangulatedness of `RΓ_T` is not a tagged statement of the
Stacks project: it is part of what the source means by "by construction of `RΓ_T`" in
[Stacks, Remark 0EF4], and the tagged statements that consume it — Tags 0AW8 and 0AVZ — are not
proved here.

## References

* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
* [Stacks Project, Tag 0AW8](https://stacks.math.columbia.edu/tag/0AW8)
* [Stacks Project, Tag 090X](https://stacks.math.columbia.edu/tag/090X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))

/-! ### The triangulated structure -/

/-- Derived sections with support in `T` commute with the shift. This is Mathlib's general
construction for a right derived functor, made available by naming the canonical comparison. -/
instance derivedSectionsWithSupportIn_commShift :
    (derivedSectionsWithSupportIn.{u, v} A T).CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift (derivedSectionsWithSupportIn.{u, v} A T)
    (derivedSectionsWithSupportInUnit.{u, v} A T)
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) ℤ

/-- Every morphism of `D(A)` is represented by the first map of a distinguished triangle of `K(A)`
all three of whose vertices are K-injective complexes, hence vertices at which the canonical
comparison `derivedSectionsWithSupportInUnit` is invertible.

Choose K-injective representatives of the source and the target; a morphism between them in `D(A)`
lifts uniquely to `K(A)` because the target is K-injective, and the homotopy-category quotient is
full, so the lift comes from a morphism of cochain complexes. Its mapping-cone triangle is
distinguished, and its third vertex is K-injective by Tag 090X. -/
private lemma exists_distTriang_isIso_derivedSectionsWithSupportInUnit
    {X Y : DerivedCategory (ModuleCat.{max u v} A)} (f : X ⟶ Y) :
    ∃ (Tr : Triangle (HomotopyCategory (ModuleCat.{max u v} A) (ComplexShape.up ℤ)))
      (_ : Tr ∈ distTriang _)
      (_ : IsIso ((derivedSectionsWithSupportInUnit.{u, v} A T).app Tr.obj₁))
      (_ : IsIso ((derivedSectionsWithSupportInUnit.{u, v} A T).app Tr.obj₂))
      (_ : IsIso ((derivedSectionsWithSupportInUnit.{u, v} A T).app Tr.obj₃)),
      Nonempty (Arrow.mk (DerivedCategory.Qh.map Tr.mor₁) ≅ Arrow.mk f) := by
  have key : ∀ Z : DerivedCategory (ModuleCat.{max u v} A),
      ∃ (Z' : CochainComplex (ModuleCat.{max u v} A) ℤ) (_ : Z'.IsKInjective),
        Nonempty (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
          (ComplexShape.up ℤ)).obj Z') ≅ Z) := fun Z ↦ by
    obtain ⟨Z', q, hZ', hq⟩ :=
      exists_quasiIso_isKInjective_moduleCat.{u, v} (A := A) (DerivedCategory.Q.objPreimage Z)
    have := hq
    exact ⟨Z', hZ', ⟨(DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app Z' ≪≫
      (asIso (DerivedCategory.Q.map q)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso Z⟩⟩
  obtain ⟨X', hX', ⟨eX⟩⟩ := key X
  obtain ⟨Y', hY', ⟨eY⟩⟩ := key Y
  obtain ⟨gh, hgh⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj X')
      Y').surjective (eX.hom ≫ f ≫ eY.inv)
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient (ModuleCat.{max u v} A)
    (ComplexShape.up ℤ)).map_surjective gh
  have hcone : (CochainComplex.mappingCone φ).IsKInjective :=
    (CochainComplex.isKInjective_two_out_of_three_of_distTriang
      (CochainComplex.mappingCone.triangleh φ).mor₁
      (CochainComplex.mappingCone.triangleh φ).mor₂
      (CochainComplex.mappingCone.triangleh φ).mor₃
      (HomotopyCategory.mappingCone_triangleh_distinguished φ)).2.2 hX' hY'
  refine ⟨CochainComplex.mappingCone.triangleh φ,
    HomotopyCategory.mappingCone_triangleh_distinguished φ, ?_, ?_, ?_,
    ⟨Arrow.isoMk eX eY ?_⟩⟩
  · exact isIso_derivedSectionsWithSupportInUnit_app T X'
  · exact isIso_derivedSectionsWithSupportInUnit_app T Y'
  · exact isIso_derivedSectionsWithSupportInUnit_app T (CochainComplex.mappingCone φ)
  · have hg : DerivedCategory.Qh.map (CochainComplex.mappingCone.triangleh φ).mor₁ =
        eX.hom ≫ f ≫ eY.inv := hgh
    rw [hg]
    change eX.hom ≫ f = (eX.hom ≫ f ≫ eY.inv) ≫ eY.hom
    simp

/-- **Derived sections with support in `T` are a triangulated functor.** The total right derived
functor `RΓ_T : D(A) ⥤ D(A)` sends distinguished triangles to distinguished triangles. -/
instance derivedSectionsWithSupportIn_isTriangulated :
    (derivedSectionsWithSupportIn.{u, v} A T).IsTriangulated :=
  Functor.isTriangulated_of_leftExtension _ (derivedSectionsWithSupportInUnit.{u, v} A T)
    (fun {_ _} f ↦ exists_distTriang_isIso_derivedSectionsWithSupportInUnit.{u, v} A T f)

/-! ### The long exact sequence of a short exact sequence of modules -/

section LongExactSequence

variable {A T} {S : ShortComplex (ModuleCat.{max u v} A)}

/-- The map on local cohomology with support in `T` induced by a map of `A`-modules. -/
def localCohomologyMap (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A)) (i : ℤ)
    {M N : ModuleCat.{max u v} A} (f : M ⟶ N) :
    localCohomologyWithSupportIn A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i ⟶
      localCohomologyWithSupportIn A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N) i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
    ((derivedSectionsWithSupportIn A T).map
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).map f))

/-- The triangle in `D(A)` obtained by applying derived sections with support in `T` to the
triangle of a short exact sequence of `A`-modules. -/
def localCohomologyTriangle (T : Set (PrimeSpectrum A)) (hS : S.ShortExact) :
    Triangle (DerivedCategory (ModuleCat.{max u v} A)) :=
  (derivedSectionsWithSupportIn.{u, v} A T).mapTriangle.obj hS.singleTriangle

/-- The triangle of local cohomology attached to a short exact sequence of modules is
distinguished. -/
lemma localCohomologyTriangle_distinguished (T : Set (PrimeSpectrum A)) (hS : S.ShortExact) :
    localCohomologyTriangle.{u, v} T hS ∈ distTriang (DerivedCategory (ModuleCat.{max u v} A)) :=
  (derivedSectionsWithSupportIn.{u, v} A T).map_distinguished _ hS.singleTriangle_distinguished

/-- **The connecting map of the long exact sequence of local cohomology.** For a short exact
sequence `0 → M₁ → M₂ → M₃ → 0` of `A`-modules this is the map
`H^i_T(M₃) ⟶ H^{i+1}_T(M₁)`. -/
def localCohomologyδ (T : Set (PrimeSpectrum A)) (hS : S.ShortExact) (i j : ℤ)
    (h : i + 1 = j) :
    localCohomologyWithSupportIn A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj S.X₃) i ⟶
      localCohomologyWithSupportIn A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj S.X₁) j :=
  DerivedCategory.HomologySequence.δ (localCohomologyTriangle.{u, v} T hS) i j h

/-- `H^i_T(M₂) → H^i_T(M₃) → H^{i+1}_T(M₁)` is a complex. -/
@[reassoc]
lemma localCohomologyMap_comp_localCohomologyδ (T : Set (PrimeSpectrum A)) (hS : S.ShortExact)
    (i j : ℤ) (h : i + 1 = j) :
    localCohomologyMap.{u, v} A T i S.g ≫ localCohomologyδ.{u, v} T hS i j h = 0 :=
  DerivedCategory.HomologySequence.comp_δ _ (localCohomologyTriangle_distinguished T hS) i j h

/-- `H^i_T(M₃) → H^{i+1}_T(M₁) → H^{i+1}_T(M₂)` is a complex. -/
@[reassoc]
lemma localCohomologyδ_comp_localCohomologyMap (T : Set (PrimeSpectrum A)) (hS : S.ShortExact)
    (i j : ℤ) (h : i + 1 = j) :
    localCohomologyδ.{u, v} T hS i j h ≫ localCohomologyMap.{u, v} A T j S.f = 0 :=
  DerivedCategory.HomologySequence.δ_comp _ (localCohomologyTriangle_distinguished T hS) i j h

/-- The first map of the triangle of local cohomology is the derived functor applied to the
first map of the short exact sequence. -/
lemma localCohomologyTriangle_mor₁ (T : Set (PrimeSpectrum A)) (hS : S.ShortExact) :
    (localCohomologyTriangle.{u, v} T hS).mor₁ =
      (derivedSectionsWithSupportIn.{u, v} A T).map
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).map S.f) := rfl

/-- The second map of the triangle of local cohomology is the derived functor applied to the
second map of the short exact sequence. -/
lemma localCohomologyTriangle_mor₂ (T : Set (PrimeSpectrum A)) (hS : S.ShortExact) :
    (localCohomologyTriangle.{u, v} T hS).mor₂ =
      (derivedSectionsWithSupportIn.{u, v} A T).map
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).map S.g) := rfl

/-- `H^i_T(M₁) → H^i_T(M₂) → H^i_T(M₃)` is a complex. -/
@[reassoc]
lemma localCohomologyMap_comp_localCohomologyMap (T : Set (PrimeSpectrum A)) (hS : S.ShortExact)
    (i : ℤ) :
    localCohomologyMap.{u, v} A T i S.f ≫ localCohomologyMap.{u, v} A T i S.g = 0 :=
  (Functor.map_comp _ _ _).symm.trans
    ((congrArg (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
      (comp_distTriang_mor_zero₁₂ _ (localCohomologyTriangle_distinguished.{u, v} T hS))).trans
      (Functor.map_zero _ _ _))

/-- **Exactness of `H^i_T(M₃) → H^{i+1}_T(M₁) → H^{i+1}_T(M₂)`.** -/
lemma localCohomology_exact₁ (T : Set (PrimeSpectrum A)) (hS : S.ShortExact) (i j : ℤ)
    (h : i + 1 = j) :
    (ShortComplex.mk (localCohomologyδ.{u, v} T hS i j h) (localCohomologyMap.{u, v} A T j S.f)
      (localCohomologyδ_comp_localCohomologyMap T hS i j h)).Exact :=
  DerivedCategory.HomologySequence.exact₁ _
    (localCohomologyTriangle_distinguished T hS) i j h

/-- **Exactness of `H^i_T(M₁) → H^i_T(M₂) → H^i_T(M₃)`.** -/
lemma localCohomology_exact₂ (T : Set (PrimeSpectrum A)) (hS : S.ShortExact) (i : ℤ) :
    (ShortComplex.mk (localCohomologyMap.{u, v} A T i S.f) (localCohomologyMap.{u, v} A T i S.g)
      (localCohomologyMap_comp_localCohomologyMap T hS i)).Exact :=
  DerivedCategory.HomologySequence.exact₂ _
    (localCohomologyTriangle_distinguished T hS) i

/-- **Exactness of `H^i_T(M₂) → H^i_T(M₃) → H^{i+1}_T(M₁)`.** -/
lemma localCohomology_exact₃ (T : Set (PrimeSpectrum A)) (hS : S.ShortExact) (i j : ℤ)
    (h : i + 1 = j) :
    (ShortComplex.mk (localCohomologyMap.{u, v} A T i S.g) (localCohomologyδ.{u, v} T hS i j h)
      (localCohomologyMap_comp_localCohomologyδ T hS i j h)).Exact :=
  DerivedCategory.HomologySequence.exact₃ _
    (localCohomologyTriangle_distinguished T hS) i j h

/-- The map `H^i_T(M₂) → H^i_T(M₃)` is surjective exactly when the connecting map out of
`H^i_T(M₃)` vanishes. -/
lemma epi_localCohomologyMap_g_iff (T : Set (PrimeSpectrum A)) (hS : S.ShortExact) (i j : ℤ)
    (h : i + 1 = j) :
    Epi (localCohomologyMap.{u, v} A T i S.g) ↔ localCohomologyδ.{u, v} T hS i j h = 0 :=
  DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _
    (localCohomologyTriangle_distinguished T hS) i j h

/-- The map `H^{i+1}_T(M₁) → H^{i+1}_T(M₂)` is injective exactly when the connecting map into
`H^{i+1}_T(M₁)` vanishes. -/
lemma mono_localCohomologyMap_f_iff (T : Set (PrimeSpectrum A)) (hS : S.ShortExact) (i j : ℤ)
    (h : i + 1 = j) :
    Mono (localCohomologyMap.{u, v} A T j S.f) ↔ localCohomologyδ.{u, v} T hS i j h = 0 :=
  DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _
    (localCohomologyTriangle_distinguished T hS) i j h

/-- **The vanishing form of the long exact sequence.** If `H^i_T(M₂) = 0` and `H^{i+1}_T(M₁) = 0`
then `H^i_T(M₃) = 0`. -/
lemma isZero_localCohomology_X₃ (T : Set (PrimeSpectrum A)) (hS : S.ShortExact) (i j : ℤ)
    (h : i + 1 = j)
    (h₂ : IsZero (localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj S.X₂) i))
    (h₁ : IsZero (localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj S.X₁) j)) :
    IsZero (localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj S.X₃) i) :=
  (localCohomology_exact₃.{u, v} T hS i j h).isZero_X₂ (h₂.eq_of_src _ _) (h₁.eq_of_tgt _ _)

/-- **The vanishing form of the long exact sequence.** If `H^i_T(M₃) = 0` and `H^{i+1}_T(M₂) = 0`
then `H^{i+1}_T(M₁) = 0`. -/
lemma isZero_localCohomology_X₁ (T : Set (PrimeSpectrum A)) (hS : S.ShortExact) (i j : ℤ)
    (h : i + 1 = j)
    (h₃ : IsZero (localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj S.X₃) i))
    (h₂ : IsZero (localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj S.X₂) j)) :
    IsZero (localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj S.X₁) j) :=
  (localCohomology_exact₁.{u, v} T hS i j h).isZero_X₂ (h₃.eq_of_src _ _) (h₂.eq_of_tgt _ _)

/-- **The vanishing form of the long exact sequence.** If `H^i_T(M₁) = 0` and `H^i_T(M₃) = 0`
then `H^i_T(M₂) = 0`. -/
lemma isZero_localCohomology_X₂ (T : Set (PrimeSpectrum A)) (hS : S.ShortExact) (i : ℤ)
    (h₁ : IsZero (localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj S.X₁) i))
    (h₃ : IsZero (localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj S.X₃) i)) :
    IsZero (localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj S.X₂) i) :=
  (localCohomology_exact₂.{u, v} T hS i).isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

end LongExactSequence

end Stacks.LocalCohomology

end
