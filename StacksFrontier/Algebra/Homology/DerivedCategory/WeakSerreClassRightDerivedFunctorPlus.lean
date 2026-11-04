module

public import StacksFrontier.Algebra.Homology.CartanEilenbergResolutions
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A weak Serre class and the total right derived functor on bounded below objects

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, `𝒜` with enough injectives.
Let `P` be an isomorphism-closed class of objects of `𝒜` and `Q` a weak Serre class of objects
of `ℬ`, and suppose that `R^p F` carries `P` into `Q` in every degree. Then for every object `K`
of `D⁺(𝒜)` all of whose cohomology objects lie in `P`, all cohomology objects of `RF(K)` lie in
`Q`.

## Main results

* `DerivedCategory.Plus.exists_iso_Q_obj`: every object of `D⁺(𝒜)` is isomorphic to the image of
  a bounded below cochain complex.
* `CategoryTheory.Functor.derivedCategoryBPlus_rightDerivedFunctorPlus_obj`: the statement above.

## References

* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
-/

@[expose] public noncomputable section

universe w w' v v' u u'

open CategoryTheory CategoryTheory.Limits Opposite

namespace DerivedCategory.Plus

/-- Every object of `D⁺(𝒜)` is isomorphic to the image of a bounded below cochain complex. -/
theorem exists_iso_Q_obj {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (Y : DerivedCategory.Plus A) :
    ∃ M : CochainComplex.Plus A, Nonempty (DerivedCategory.Plus.Q.obj M ≅ Y) := by
  obtain ⟨Y, n, K, e, h⟩ := Y
  exact ⟨⟨K, n, h⟩, ⟨DerivedCategory.Plus.ι.preimageIso e.symm⟩⟩

end DerivedCategory.Plus

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]

/-- **A weak Serre class is inherited by the cohomology of the total right derived functor.** Let
`F : 𝒜 ⥤ ℬ` be an additive functor, `𝒜` with enough injectives, let `P` be an isomorphism-closed
class of objects of `𝒜` and `Q` a weak Serre class of objects of `ℬ`, and assume `R^p F` carries
`P` into `Q` for every `p`. If `K` is an object of `D⁺(𝒜)` all of whose cohomology objects lie in
`P`, then `RF(K)` is bounded below and all its cohomology objects lie in `Q`. -/
@[sga "4 Vbis 2.4.1.1" "more general"]
theorem derivedCategoryBPlus_rightDerivedFunctorPlus_obj (F : A ⥤ B) [F.Additive]
    (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms]
    (Q : ObjectProperty B) [Q.IsWeakSerreClass]
    (hF : ∀ M : A, P M → ∀ p : ℕ, Q ((F.rightDerived p).obj M))
    (K : DerivedCategory.Plus A)
    (hK : ∀ q : ℤ, P ((DerivedCategory.Plus.homologyFunctor A q).obj K)) :
    DerivedCategoryB.derivedCategoryBPlus Q (F.rightDerivedFunctorPlus.obj K).obj := by
  obtain ⟨M, ⟨eM⟩⟩ := DerivedCategory.Plus.exists_iso_Q_obj K
  obtain ⟨n₀, _⟩ := M.property
  obtain ⟨I, _⟩ := M.obj.exists_cartanEilenbergResolution n₀
  let L : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I.bicomplex
  have hq : ∀ (p q : ℤ), q < 0 → IsZero ((L.X p).X q) := fun p q hq ↦
    F.map_isZero (CochainComplex.isZero_of_isStrictlyGE (I.bicomplex.X p) 0 q hq)
  have hp : ∀ (p : ℤ), p < n₀ → IsZero (L.X p) := fun p hp ↦
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE I.bicomplex n₀ p hp)
  have hfin := StacksDraft.TotalComplexQuasiIso.finite_not_isZero_of_bounded L n₀ hq hp
  have : L.HasTotal (ComplexShape.up ℤ) :=
    StacksDraft.TotalComplexQuasiIso.hasTotal_of_bounded L n₀ hq hp
  obtain ⟨-, h2, h3⟩ := I.exists_homologyIso_rightDerivedPlus F M.property
  have eH : ∀ q : ℤ, M.obj.homology q ≅
      (DerivedCategory.Plus.homologyFunctor A q).obj K :=
    fun q ↦ ((DerivedCategory.homologyFunctorFactors A q).app M.obj).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor A q).mapIso eM
  have hboundOut : DerivedCategoryB.IsBoundedBelow (F.rightDerivedFunctorPlus.obj K).obj := by
    let zOut := F.rightDerivedFunctorPlus.obj K
    obtain ⟨n, hn⟩ := zOut.property
    refine ⟨n, fun i hi ↦ ?_⟩
    let _ : DerivedCategory.Plus.IsGE zOut n :=
      (DerivedCategory.Plus.isGE_ι_obj_iff zOut n).1 hn
    exact DerivedCategory.Plus.isZero_homology_of_isGE zOut n i hi
  refine ⟨hboundOut, fun n ↦ ?_⟩
  let Fil : ∀ (_p n : ℤ), Subobject (L.totalFiltration₂.X.X n) :=
    fun p n ↦ Subobject.mk ((L.totalFiltration₂.filtration.ι.app (op p)).f n)
  let Z : ∀ (_r _p n : ℤ), Subobject (L.totalFiltration₂.X.X n) :=
    fun r p n ↦ Fil p n ⊓ (Subobject.pullback (L.totalFiltration₂.X.d n (n + 1))).obj
      (Fil (p + r) (n + 1))
  let D : ∀ (_r _p n : ℤ), Subobject (L.totalFiltration₂.X.X n) :=
    fun r p n ↦ Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (L.totalFiltration₂.X.d (n - 1) n)).obj
        (Z (r - 1) (p - r + 1) (n - 1))
  let FH : ∀ (n _p : ℤ), Subobject (L.totalFiltration₂.X.homology n) :=
    fun n p ↦ imageSubobject
      (HomologicalComplex.homologyMap (L.totalFiltration₂.filtration.ι.app (op p)) n)
  obtain ⟨E, e, -, hδ, -, -, -⟩ :=
    CochainComplex.exists_cohomologicalSpectralSequence L.totalFiltration₂ Fil
      (fun _ _ ↦ rfl) Z (fun _ _ _ ↦ rfl) D (fun _ _ _ ↦ rfl)
  obtain ⟨-, -, hE2⟩ := L.exists_iso_pages_totalFiltration₂ Fil (fun _ _ ↦ rfl)
    Z (fun _ _ _ ↦ rfl) D (fun _ _ _ ↦ rfl) E e hδ
  have hconv := L.isBounded_and_converges_totalFiltration₂ hfin Fil (fun _ _ ↦ rfl)
    Z (fun _ _ _ ↦ rfl) D (fun _ _ _ ↦ rfl) FH (fun _ _ ↦ rfl) E e
  have hPage : ∀ p q : ℤ, Q ((E.page 2 zero_le_two).X (p, q)) := by
    intro p q
    obtain ⟨e₂⟩ := hE2 p q
    obtain ⟨e₂'⟩ := h2 p q
    have hmember : Q ((F.rightDerivedPlus p).obj (M.obj.homology q)) := by
      by_cases hp : p < 0
      · have hneg :=
          (Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
            F F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnit).1 p hp
        exact Q.prop_of_isZero ((Functor.isZero_iff _).1 hneg (M.obj.homology q))
      · have hpNat : ((Int.toNat p : ℕ) : ℤ) = p := Int.toNat_of_nonneg (le_of_not_gt hp)
        simpa [hpNat] using Q.prop_of_iso
          ((Stacks.DerivedIndexing.rightDerivedIso F p.toNat).app (M.obj.homology q))
          (hF (M.obj.homology q) (P.prop_of_iso (eH q).symm (hK q)) p.toNat)
    exact Q.prop_of_iso e₂.symm (Q.prop_of_iso e₂'.symm hmember)
  obtain ⟨eN⟩ := h3 n
  exact Q.prop_of_iso
    (eN ≪≫ (DerivedCategory.Plus.homologyFunctor B n).mapIso
      (F.rightDerivedFunctorPlus.mapIso eM))
    (hconv.2.2.2.2 Q 2 zero_le_two hPage n)

end CategoryTheory.Functor

end
