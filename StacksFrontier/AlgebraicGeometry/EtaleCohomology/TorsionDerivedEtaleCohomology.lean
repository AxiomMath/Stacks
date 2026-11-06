module

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.GroupTheory.Torsion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.CartanEilenbergResolutions
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Torsion of étale cohomology in the derived category

This module carries the declarations that extend
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionEtaleCohomology`,
which is the base text, unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe w v u

namespace Stacks.Torsion

section SerreClass

/-- Torsion abelian groups, as a property of the objects of `AddCommGrpCat`. -/
def isAddTorsionProperty : ObjectProperty AddCommGrpCat.{w} := fun A ↦ IsAddTorsion A

/-- **Torsion abelian groups form a Serre subcategory of the category of abelian groups.** By
[Stacks, Tag 02MP] it suffices to produce one torsion group and to see that if `A₁ ⟶ A₂ ⟶ A₃` is
exact at `A₂` with `A₁` and `A₃` torsion then `A₂` is torsion: an element `x` of `A₂` has torsion
image in `A₃`, so `n • x` lies in the image of `A₁` for some `n > 0`, and a preimage of it is
killed by some `m > 0`, whence `(n * m) • x = 0`.

Being in particular a weak Serre subcategory, this is the class to which the convergence
statement [Stacks, Tag 0132] is applied in `derivedEtaleCohomology_isAddTorsion`. -/
instance isAddTorsionProperty_isSerreClass : (isAddTorsionProperty.{w}).IsSerreClass := by
  rw [ObjectProperty.isSerreClass_iff_prop_X₂_of_exact]
  refine ⟨⟨AddCommGrpCat.of PUnit.{w + 1}, fun _ ↦
    isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨1, Nat.one_pos, Subsingleton.elim _ _⟩⟩, ?_⟩
  intro S hS h₁ h₃ x
  obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (h₃ (S.g x))
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff S).1 hS (n • x) (by rw [map_nsmul, hnx])
  obtain ⟨m, hm, hmy⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (h₁ y)
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n * m, Nat.mul_pos hn hm, ?_⟩
  rw [mul_nsmul, ← hy, ← map_nsmul, hmy, map_zero]

end SerreClass

end Stacks.Torsion

namespace Stacks.EtaleCohomology

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

section Hypercohomology

attribute [local instance] HasDerivedCategory.standard

/-- **A weak Serre class containing every `R^p G` of every cohomology object contains every
`H^n(RG K)`**, for `K` in `D⁺` and `G` an additive functor out of a category with enough
injectives.

This is the spectral sequence of a Cartan–Eilenberg resolution. Represent `K` by a bounded below
cochain complex `M` and choose a Cartan–Eilenberg resolution `I` of `M`; applying `G` degreewise
gives a double complex `L` bounded in both directions, so its total complex exists and the
spectral sequence of the filtration of that total complex by the second coordinate converges
([Stacks, Tag 0132]). Its second page is `''E₂^{p,q} = R^p G (H^q(M))` by [Stacks, Tag 015J], so
it lies in `P` by hypothesis, and the abutment `H^n(Tot L) = H^n(RG K)` is built from that page by
the subquotients and extensions a weak Serre class is closed under. -/
theorem prop_homology_rightDerivedFunctorPlus
    {A : Type*} {B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (G : A ⥤ B) [G.Additive] (P : ObjectProperty B) [P.IsWeakSerreClass]
    (K : DerivedCategory.Plus A)
    (hP : ∀ (q : ℤ) (p : ℕ),
      P ((G.rightDerived p).obj ((DerivedCategory.Plus.homologyFunctor A q).obj K)))
    (n : ℤ) :
    P ((DerivedCategory.Plus.homologyFunctor B n).obj (G.rightDerivedFunctorPlus.obj K)) := by
  obtain ⟨M, ⟨eM⟩⟩ : ∃ M : CochainComplex.Plus A,
      Nonempty (DerivedCategory.Plus.Q.obj M ≅ K) := by
    obtain ⟨-, m, M, e, hM⟩ := K
    exact ⟨⟨M, m, hM⟩, ⟨DerivedCategory.Plus.ι.preimageIso e.symm⟩⟩
  obtain ⟨n₀, _⟩ := M.property
  obtain ⟨I, _⟩ := M.obj.exists_cartanEilenbergResolution n₀
  let L : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I.bicomplex
  have hq : ∀ p q : ℤ, q < 0 → IsZero ((L.X p).X q) := fun p q hq =>
    G.map_isZero (CochainComplex.isZero_of_isStrictlyGE (I.bicomplex.X p) 0 q hq)
  have hp : ∀ p : ℤ, p < n₀ → IsZero (L.X p) := fun p hp =>
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE I.bicomplex n₀ p hp)
  have hfin := StacksDraft.TotalComplexQuasiIso.finite_not_isZero_of_bounded L n₀ hq hp
  have : L.HasTotal (ComplexShape.up ℤ) :=
    StacksDraft.TotalComplexQuasiIso.hasTotal_of_bounded L n₀ hq hp
  obtain ⟨-, h2, h3⟩ := I.exists_homologyIso_rightDerivedPlus G M.property
  have eH : ∀ q : ℤ, M.obj.homology q ≅ (DerivedCategory.Plus.homologyFunctor A q).obj K :=
    fun q => ((DerivedCategory.homologyFunctorFactors A q).app M.obj).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor A q).mapIso eM
  let Fil : ∀ (_p n : ℤ), Subobject (L.totalFiltration₂.X.X n) :=
    fun p n => Subobject.mk ((L.totalFiltration₂.filtration.ι.app (op p)).f n)
  let Z : ∀ (_r _p n : ℤ), Subobject (L.totalFiltration₂.X.X n) :=
    fun r p n => Fil p n ⊓ (Subobject.pullback (L.totalFiltration₂.X.d n (n + 1))).obj
      (Fil (p + r) (n + 1))
  let D : ∀ (_r _p n : ℤ), Subobject (L.totalFiltration₂.X.X n) :=
    fun r p n => Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (L.totalFiltration₂.X.d (n - 1) n)).obj
        (Z (r - 1) (p - r + 1) (n - 1))
  let FH : ∀ (n _p : ℤ), Subobject (L.totalFiltration₂.X.homology n) :=
    fun n p => imageSubobject
      (HomologicalComplex.homologyMap (L.totalFiltration₂.filtration.ι.app (op p)) n)
  obtain ⟨E, e, -, hδ, -, -, -⟩ :=
    CochainComplex.exists_cohomologicalSpectralSequence L.totalFiltration₂ Fil
      (fun _ _ => rfl) Z (fun _ _ _ => rfl) D (fun _ _ _ => rfl)
  obtain ⟨-, -, hE2⟩ := L.exists_iso_pages_totalFiltration₂ Fil (fun _ _ => rfl)
    Z (fun _ _ _ => rfl) D (fun _ _ _ => rfl) E e hδ
  have hconv := L.isBounded_and_converges_totalFiltration₂ hfin Fil (fun _ _ => rfl)
    Z (fun _ _ _ => rfl) D (fun _ _ _ => rfl) FH (fun _ _ => rfl) E e
  have hPage : ∀ p q : ℤ, P ((E.page 2 zero_le_two).X (p, q)) := by
    intro p q
    obtain ⟨e₂⟩ := hE2 p q
    obtain ⟨e₂'⟩ := h2 p q
    refine P.prop_of_iso e₂.symm (P.prop_of_iso e₂'.symm ?_)
    by_cases hneg : p < 0
    · refine P.prop_of_isZero ((Functor.isZero_iff _).1 ?_ (M.obj.homology q))
      exact (Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
        G G.rightDerivedFunctorPlus G.rightDerivedFunctorPlusUnith).1 p hneg
    · have hcast : ((p.toNat : ℕ) : ℤ) = p := Int.toNat_of_nonneg (le_of_not_gt hneg)
      have := P.prop_of_iso
        ((Stacks.DerivedIndexing.rightDerivedIso G p.toNat).app (M.obj.homology q))
        (P.prop_of_iso ((G.rightDerived p.toNat).mapIso (eH q)).symm (hP q p.toNat))
      rwa [hcast] at this
  obtain ⟨eN⟩ := h3 n
  exact P.prop_of_iso (eN ≪≫ (DerivedCategory.Plus.homologyFunctor B n).mapIso
    (G.rightDerivedFunctorPlus.mapIso eM)) (hconv.2.2.2.2 P 2 zero_le_two hPage n)

/-- **Stacks 0DDC (2).** Let `X` be a quasi-compact and quasi-separated scheme. If `K` is an
object of `D⁺(X_étale)` all of whose cohomology sheaves are torsion, then the hypercohomology
`H^n_étale(X, K)` is a torsion abelian group for every `n : ℤ`.

This follows from part (1) by the spectral sequence of a Cartan–Eilenberg resolution: torsion
abelian groups are a Serre, hence a weak Serre, subcategory of `AddCommGrpCat`
(`Stacks.Torsion.isAddTorsionProperty_isSerreClass`), the `''E₂`-page of that spectral sequence is
`H^p_étale(X, H^q(K))`, which part (1) makes torsion, and a weak Serre subcategory containing a
whole page contains the abutment. -/
theorem derivedEtaleCohomology_isAddTorsion (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}))
    (hK : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) v} X.smallEtaleTopology K.obj)
    (n : ℤ) :
    IsAddTorsion
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max (u + 1) v} n).obj
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus.obj
          K)) :=
  prop_homology_rightDerivedFunctorPlus (Sheaf.Γ X.smallEtaleTopology _)
    Stacks.Torsion.isAddTorsionProperty K
    (fun q p => etaleCohomology_isAddTorsion.{v} X _ (hK q) p) n

/-- **Stacks 0DDC.** Let `X` be a quasi-compact and quasi-separated scheme.

1. If `𝓕` is a torsion abelian sheaf on `X_étale`, then `H^n_étale(X, 𝓕)` is a torsion abelian
   group for all `n`.
2. If `K` in `D⁺(X_étale)` has torsion cohomology sheaves, then `H^n_étale(X, K)` is a torsion
   abelian group for all `n`.

Part (1) is `etaleCohomology_isAddTorsion` and part (2) is `derivedEtaleCohomology_isAddTorsion`;
both hold under exactly the source's hypotheses on `X`, so the tag's assertion is their
conjunction. Here `H^n_étale(X, -)` is the right derived functor of global sections on the small
étale site, and `H^n_étale(X, K)` the homology of its total right derived functor on `D⁺`. -/
@[stacks 0DDC "parts (1) and (2), as the conjunction of the sheaf case and the `D⁺` case"]
theorem etaleCohomology_isAddTorsion_and_derivedEtaleCohomology_isAddTorsion (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    (∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}),
        Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F → ∀ n : ℕ,
        IsAddTorsion
          (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived n).obj F)) ∧
      ∀ (K : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})),
        Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) v} X.smallEtaleTopology K.obj →
        ∀ n : ℤ,
        IsAddTorsion
          ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max (u + 1) v} n).obj
            ((Sheaf.Γ X.smallEtaleTopology
              AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus.obj K)) :=
  ⟨fun F hF n => etaleCohomology_isAddTorsion X F hF n,
    fun K hK n => derivedEtaleCohomology_isAddTorsion X K hK n⟩

end Hypercohomology

end Stacks.EtaleCohomology

end
