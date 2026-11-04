module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.BoundedCohomologicalDimensionPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfModuleOverObjectEssentiallySmall

/-!
# Truncation from below and derived sections over an object, on a site with large objects

Let `(C, J)` be a site whose objects form a type in an arbitrary universe while its morphisms,
its sheaf of rings `R` and its modules live in one universe `u`, and assume `C` is essentially
`u`-small. Let `U` be an object of `C` and let `P` be a class of `R`-modules whose cohomology over
`U` vanishes above a bound `d`. For an object `K` of `D(R)` with all cohomology in `P` which is a
derived limit of its truncation tower (Stacks 0D6S), the map

`Hʲ(U, K) ⟶ Hʲ(U, τ_{≥ -m}K)`

is an isomorphism for `m ≥ 1 - j` and `m ≥ d - j + 1`; and for `K` bounded below the cohomology
over `U` is computed by the single cohomology module in that degree once `d = 0`.

These are the local lemmas of Stacks 0D6W at a site with large objects, read for the unbounded
derived sections functor
`Stacks.Cohomology.Localization.OfEssentiallySmall.derivedSectionsOverObject`.
The single-universe versions are
`Stacks.Cohomology.OlssonLaszlo.isIso_homologyMap_derivedSectionsOverObject_truncGEπ` and its
companions, whose arguments are reproduced here; the universe of the objects of the site plays no
part in them.

## Main results

* `OfEssentiallySmall.isIso_homologyMap_derivedSectionsOverObject_truncGEπ`:
  the truncation comparison on cohomology over an object.
* `OfEssentiallySmall.isIso_homologyMap_derivedSectionsOverObject_natTransTruncGEOfLE`:
  one step of the truncation tower is invertible on cohomology over an object above the bound.

## References

* [Stacks Project, Tag 0D6W](https://stacks.math.columbia.edu/tag/0D6W)
* [Stacks Project, Tag 0D6K](https://stacks.math.columbia.edu/tag/0D6K)
* [Stacks Project, Tag 0D6S](https://stacks.math.columbia.edu/tag/0D6S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace Stacks.Cohomology.OlssonLaszlo.OfEssentiallySmall

universe u c


open Stacks.Cohomology.Localization.OfEssentiallySmall (sectionsOverObject
  homotopySectionsOverObject derivedSectionsOverObject)

variable {C : Type c} [Category.{u} C] [EssentiallySmall.{u} C]
  (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [IsGrothendieckAbelian.{u} (SheafOfModules.{u} R)]
  [EnoughInjectives (SheafOfModules.{u} R)]

attribute [local instance] HasDerivedCategory.standard in
/-- The unit exhibiting `derivedSectionsOverObject` as a right derived functor. -/
abbrev derivedSectionsOverObjectUnit (U : C) :
    homotopySectionsOverObject J R U ⟶ DerivedCategory.Qh ⋙ derivedSectionsOverObject J R U :=
  (homotopySectionsOverObject J R U).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} R) (ComplexShape.up ℤ))

omit [EssentiallySmall.{u} C] [IsGrothendieckAbelian.{u} (SheafOfModules.{u} R)] in
/-- **Cohomology of a module over an object computes the right derived functors of sections.**
If the cohomology module `Hᵖ(U, M)` vanishes then so does the `p`-th right derived functor of
sections over `U` with values in abelian groups, the forgetful functor being exact. -/
lemma isZero_rightDerived_sectionsOverObject (U : C) (M : SheafOfModules.{u} R) (p : ℕ)
    (h : IsZero (moduleCohomology R U p M)) :
    IsZero (((sectionsOverObject J R U).rightDerived p).obj M) := by
  let E := _root_.SheafOfModules.evaluation R (Opposite.op U)
  let G := forget₂ (ModuleCat.{u} (R.obj.obj (Opposite.op U))) AddCommGrpCat.{u}
  let _ : E.Additive := ⟨rfl⟩
  exact (G.map_isZero h).of_iso (rightDerivedExactPostcompositionIso E G M p).symm

attribute [local instance] HasDerivedCategory.standard in
/-- **Derived sections over an object of a module placed in a single degree are concentrated in a
band of width the cohomological bound.** -/
lemma isZero_homology_derivedSectionsOverObject_single (U : C) (M : SheafOfModules.{u} R) (d : ℤ)
    (hM : ∀ p : ℕ, d < (p : ℤ) → IsZero (moduleCohomology R U p M))
    (a m : ℤ) (ham : a < m) (hd : a + d < m) :
    IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
      ((derivedSectionsOverObject J R U).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} R) a).obj M))) := by
  refine IsZero.of_iso ?_ (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso
    (sectionsOverObject J R U) (derivedSectionsOverObject J R U)
    (derivedSectionsOverObjectUnit J R U)
    Stacks.Cohomology.Localization.enoughKInjectives M a m (m - a).toNat (by omega))
  exact isZero_rightDerived_sectionsOverObject J R U M (m - a).toNat (hM _ (by omega))

attribute [local instance] HasDerivedCategory.standard in
/-- **The derived sections over an object of a one-step interval truncation are concentrated in a
band of width the cohomological bound.** -/
lemma isZero_homology_derivedSectionsOverObject_truncLTGE (U : C)
    (K : DerivedCategory (SheafOfModules.{u} R)) (d a b : ℤ) (hb : a + 1 = b)
    (hK : ∀ p : ℕ, d < (p : ℤ) → IsZero (moduleCohomology R U p
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} R) a).obj K)))
    (i : ℤ) (hi : a < i) (hid : a + d < i) :
    IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
      ((derivedSectionsOverObject J R U).obj
        ((DerivedCategory.TStructure.t.truncLTGE a b).obj K))) := by
  subst hb
  obtain ⟨e⟩ := Stacks.TruncationLevel.nonempty_iso_singleFunctor_truncLTGE a K
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).mapIso
    ((derivedSectionsOverObject J R U).mapIso e))
  exact isZero_homology_derivedSectionsOverObject_single J R U _ d hK a i hi hid

omit [EnoughInjectives (SheafOfModules.{u} R)] in
attribute [local instance] HasDerivedCategory.standard in
/-- Derived sections over an object form a triangulated functor. -/
lemma isTriangulated_derivedSectionsOverObject (U : C) :
    letI := Functor.IsRightDerivedFunctor.commShift (derivedSectionsOverObject J R U)
      (derivedSectionsOverObjectUnit J R U)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} R) (ComplexShape.up ℤ)) ℤ
    (derivedSectionsOverObject J R U).IsTriangulated :=
  Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
    Stacks.Cohomology.Localization.enoughKInjectives (homotopySectionsOverObject J R U)
    (derivedSectionsOverObject J R U) (derivedSectionsOverObjectUnit J R U)

attribute [local instance] HasDerivedCategory.standard in
/-- **One step of the truncation tower is invertible on the cohomology of derived sections over an
object, above the cohomological bound.** The fibre of `τ_{≥ a}K ⟶ τ_{≥ a + 1}K` is `H^a(K)`
placed in degree `a`, whose derived sections over `U` have no cohomology in degrees `> a + d`. -/
lemma isIso_homologyMap_derivedSectionsOverObject_natTransTruncGEOfLE (U : C)
    (K : DerivedCategory (SheafOfModules.{u} R)) (d a b : ℤ) (hb : a + 1 = b)
    (hab : a ≤ b)
    (hK : ∀ p : ℕ, d < (p : ℤ) → IsZero (moduleCohomology R U p
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} R) a).obj K)))
    (j : ℤ) (hj : a < j) (hjd : a + d < j) :
    IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).map
      ((derivedSectionsOverObject J R U).map
        ((DerivedCategory.TStructure.t.natTransTruncGEOfLE a b hab).app K))) := by
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedSectionsOverObject J R U)
    (derivedSectionsOverObjectUnit J R U)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} R) (ComplexShape.up ℤ)) ℤ
  have htri : (derivedSectionsOverObject J R U).IsTriangulated :=
    isTriangulated_derivedSectionsOverObject J R U
  obtain ⟨δ, hδ⟩ := Stacks.TruncationLevel.exists_distTriang_truncGE
    DerivedCategory.TStructure.t a b hab K
  exact Stacks.TruncationLevel.isIso_homologyMap_mor₂ _
    ((derivedSectionsOverObject J R U).map_distinguished _ hδ) j
    (isZero_homology_derivedSectionsOverObject_truncLTGE J R U K d a b hb hK j hj hjd)
    (isZero_homology_derivedSectionsOverObject_truncLTGE J R U K d a b hb hK (j + 1)
      (by omega) (by omega))

attribute [local instance] HasDerivedCategory.standard in
/-- **The transition maps of the truncation tower are invertible on the cohomology of derived
sections over an object, once the index is large compared with the degree and the bound.** -/
lemma isIso_homologyMap_derivedSectionsOverObject_truncGETower_succ (U : C)
    (P : ObjectProperty (SheafOfModules.{u} R))
    (K : DerivedCategory (SheafOfModules.{u} R))
    (hK : DerivedCategoryB.derivedCategoryB P K) (d : ℤ)
    (hvan : ∀ p : ℕ, d < (p : ℤ) → ∀ F : SheafOfModules.{u} R, P F →
      IsZero (moduleCohomology R U p F))
    (j : ℤ) (k : ℕ) (hk : -j ≤ (k : ℤ)) (hkd : d - j ≤ (k : ℤ)) :
    IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).map
      ((derivedSectionsOverObject J R U).map
        ((Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} R) K).map
          (homOfLE (Nat.le_succ k)).op))) := by
  rw [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ]
  exact isIso_homologyMap_derivedSectionsOverObject_natTransTruncGEOfLE J R U K d
    (-((k + 1 : ℕ) : ℤ)) (-(k : ℤ)) (by omega) (by omega)
    (fun p hp ↦ hvan p hp _ (hK _)) j (by omega) (by omega)

attribute [local instance] HasDerivedCategory.standard in
/-- **Truncation from below does not change the cohomology of derived sections over an object, in
the range allowed by the local cohomological bound.** Let `K` be an object of the derived category
whose cohomology modules all satisfy `P`, let the cohomology over `U` of every module satisfying
`P` vanish above `d`, and assume `K` is a derived limit of its truncation tower in the strong sense
that every comparison map to such a derived limit is invertible (which is Stacks 0D6S in the
Olsson--Laszlo situation). Then `H^j(U, K) ⟶ H^j(U, τ_{≥ -m}K)` is an isomorphism as soon as
`m ≥ 1 - j` and `m ≥ d - j + 1`. -/
theorem isIso_homologyMap_derivedSectionsOverObject_truncGEπ (U : C)
    (P : ObjectProperty (SheafOfModules.{u} R))
    (K : DerivedCategory (SheafOfModules.{u} R))
    [HasProduct fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} R) K).obj ⟨n⟩]
    (hK : DerivedCategoryB.derivedCategoryB P K) (d : ℤ)
    (hvan : ∀ p : ℕ, d < (p : ℤ) → ∀ F : SheafOfModules.{u} R, P F →
      IsZero (moduleCohomology R U p F))
    (hconv : ∀ (L : DerivedCategory (SheafOfModules.{u} R)) (c : K ⟶ L)
      (pr : L ⟶ ∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} R) K).obj ⟨n⟩)
      (δ : (∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} R) K).obj ⟨n⟩) ⟶
          L⟦(1 : ℤ)⟧),
      Triangle.mk pr (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} R) K).obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} R) K).obj ⟨n⟩)
            (n + 1) ≫
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} R) K).map
            (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang (DerivedCategory (SheafOfModules.{u} R)) →
        (∀ n : ℕ, c ≫ pr ≫ Pi.π (fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} R) K).obj ⟨n⟩) n =
          (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K) → IsIso c)
    (j : ℤ) (m : ℕ) (hm : 1 - j ≤ (m : ℤ)) (hmd : d - j + 1 ≤ (m : ℤ)) :
    IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).map
      ((derivedSectionsOverObject J R U).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(m : ℤ))).app K))) := by
  obtain ⟨δ, hδ⟩ := Stacks.InverseSystem.exists_distTriang_milnor_of_isIso
    (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} R) K)
    (fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)
    (fun n ↦ by
      rw [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ]
      exact DerivedCategory.TStructure.t.π_natTransTruncGEOfLE_app
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega) K)
    hconv
  have : PreservesLimitsOfShape (Discrete ℕ)
      (_root_.SheafOfModules.evaluation.{u} R (op U)) :=
    _root_.SheafOfModules.evaluationPreservesLimitsOfShape.{u} (R := R) (D := Discrete ℕ) (op U)
  obtain ⟨_, _, _, _, _, _, _, r, _, _, _, hseq, hr⟩ :=
    Stacks.Cohomology.DerivedSectionsMilnor.exists_milnor_shortExact_of_rightDerived
      (sectionsOverObject J R U) (derivedSectionsOverObject J R U)
      (derivedSectionsOverObjectUnit J R U)
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} R) K) K
      (Pi.lift fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)
      ⟨δ, hδ⟩ j
  have hstep := isIso_homologyMap_derivedSectionsOverObject_truncGETower_succ J R U P K hK d hvan
  have hzero := Stacks.InverseSystem.isZero_cokernel_milnorDifference_functor
    ((Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} R) K ⋙
      derivedSectionsOverObject J R U) ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u} (j - 1)) m
    (fun n hn ↦ hstep (j - 1) n (by omega) (by omega))
  have hπlim : IsIso (limit.π ((Stacks.DerivedLimit.truncGETower
      (SheafOfModules.{u} R) K ⋙ derivedSectionsOverObject J R U) ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u} j) ⟨m⟩) :=
    (isEventuallyConstantTo_of_isIso_succ _ m fun n hn ↦
      hstep j n (by omega) (by omega)).isIso_π_of_isLimit (limit.isLimit _)
  have h3 := (hr m).symm
  erw [Pi.lift_π] at h3
  exact h3 ▸ IsIso.comp_isIso' (hseq.isIso_g_iff.mpr hzero) hπlim

end Stacks.Cohomology.OlssonLaszlo.OfEssentiallySmall

end
