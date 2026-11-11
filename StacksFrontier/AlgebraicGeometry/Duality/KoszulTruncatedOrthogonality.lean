module

public import StacksFrontier.AlgebraicGeometry.Duality.KoszulOrthogonality.Abstract
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulOrthogonality.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulVanishing.OpenComplement
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictAdjunction
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictCounit
import all StacksFrontier.CategoryTheory.Triangulated.BrownRepresentability

/-!
# Truncated orthogonality to an object killed by the left adjoint

Let `L ⊣ R` be an adjunction between the derived categories of two abelian categories, with `L`
triangulated, and let `K` be an object of the source killed by `L`. For an integer `a` and an
object `E` of the source consider the two conditions

1. the truncation `τ_{≤a}(E ⟶ R (L E))` of the unit is invertible, and
2. every morphism `K⟦-n⟧ ⟶ E` vanishes for every `n ≤ a`.

If `K` is concentrated in degrees `≤ 0`, then (1) at `a` implies (2) at `a`. If every object `M`
killed by `L` with no morphism from `K⟦-n⟧` for `n ≤ a` has vanishing homology in degrees `≤ a`,
then (2) at `a + 1` implies (1) at `a`.

For `j : U ⟶ X = Spec A` the inclusion of `U = ⋃ᵢ D(fᵢ)`, `L = j^*`, `R = Rj_*` and `K` the
sheafified Koszul complex of `f₁, …, f_r`, this gives [Stacks, Tag 0GEK] for `E ∈ D_QCoh(𝒪_X)`,
corrected per `errata.md`: (1) at `a` implies (2) at `a`, and (2) at `a + 1` implies (1) at `a`.
The published "(2) implies (1)" at the same index `a` is false
(`Stacks.Koszul.Errata.erratum_0GEK`); the published "(1) implies (2) with `a` replaced by
`a - 1`" follows from (1) at `a` implies (2) at `a`.

Both indices are sharp. Take `A = k[x]`, `f = (x)`, so that `U = D(x)` and `K = (A --x--> A)` is
concentrated in degrees `-1, 0`.

* For `E = 𝒪_X` the Hom-complex `Hom^•(K, A)` is `A --x--> A` in degrees `0, 1`, so its
  cohomology is `0` in degree `0` and `A/x` in degree `1`. Its terms are free, and `X` is affine,
  so these are the Hom-groups of `D(𝒪_X)`: every morphism `K⟦m⟧ ⟶ 𝒪_X` with `m ≥ 0` vanishes,
  and (2) holds at `a = 0`. But `Rj_*(𝒪_U) = A[1/x]` in degree `0` and
  `A ⟶ A[1/x]` is not invertible, so (1) fails at `a = 0`. Hence (2) at `a` does **not** imply
  (1) at `a`.
* For `E` the structure sheaf of the origin one has `E|_U = 0`, so (1) holds at `a = -1`; but
  `K ⟶ E` is the nonzero map onto `H^0(K) = A/x = E`, so (2) fails at `a = 0`. Hence (1) at `a`
  does **not** imply (2) at `a + 1`.

## Main results

* `Stacks.DerivedTruncation.subsingleton_hom_shift_one_of_subsingleton_hom`: shifting the target
  of a Hom-group by one is shifting its source by minus one.
* `Stacks.DerivedTruncation.subsingleton_hom_shift_of_isIso_truncLE_map_unit`: (1) at `a` implies
  (2) at `a`, for an abstract adjunction.
* `Stacks.DerivedTruncation.subsingleton_hom_shift_obj₃_of_subsingleton_hom_shift`: the cone of
  the unit is orthogonal to `K⟦-n⟧` for `n ≤ a` when `E` is orthogonal to it for `n ≤ a + 1`.
* `Stacks.DerivedTruncation.isIso_truncLE_map_unit_of_subsingleton_hom_shift`: (2) at `a + 1`
  implies (1) at `a`, for an abstract adjunction and under the detection hypothesis.
* `Stacks.DerivedTruncation.isZero_of_forall_isZero_homology`: an object of the derived category
  with no homology is zero.
* `Stacks.DerivedTruncation.isZero_of_rightOrthogonal_of_detectionLE`: the graded detection
  hypothesis implies that an object right orthogonal to all shifts of `K` is zero.
* `Stacks.Koszul.Truncation.hom_koszul_eq_zero_of_truncLE_restriction`: (1) at `a` gives (2) at
  `a` for the sheafified Koszul complex on an affine scheme and an arbitrary `E`.
* `Stacks.Koszul.Truncation.truncLE_restriction_of_hom_koszul_eq_zero_of_detection`: (2) at
  `a + 1` gives (1) at `a` on an affine scheme, under the detection hypothesis.
* `Stacks.Koszul.Truncation.truncLE_restriction_of_hom_koszul_eq_zero`: `(2) at a + 1 ⟹ (1) at
  a` for `E ∈ D_QCoh(𝒪_X)`.
* `Stacks.Koszul.Truncation.hom_koszul_eq_zero_of_truncLE_restriction_sub_one`: the printed
  `(1) at a ⟹ (2) at a - 1`.
* `Stacks.Koszul.Truncation.truncLE_restriction_koszul_criterion`: [Stacks, Tag 0GEK] corrected
  per `errata.md`, both directions for `E ∈ D_QCoh(𝒪_X)`: `(1) at a ⟹ (2) at a` and
  `(2) at a + 1 ⟹ (1) at a`.

## References

* [Stacks Project, Tag 0GEK](https://stacks.math.columbia.edu/tag/0GEK)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

namespace Stacks.DerivedTruncation

universe w₁ w₂ v₁ v₂ u₁ u₂

/-! ### Shifting a Hom-group -/

/-- If every morphism `K⟦m'⟧ ⟶ E` vanishes and `m' + 1 = m`, then every morphism
`K⟦m⟧ ⟶ E⟦1⟧` vanishes. -/
theorem subsingleton_hom_shift_one_of_subsingleton_hom {A : Type u₁} [Category.{v₁} A]
    [HasShift A ℤ] {K E : A} (m m' : ℤ) (hm : m' + 1 = m)
    (h : Subsingleton (K⟦m'⟧ ⟶ E)) : Subsingleton (K⟦m⟧ ⟶ E⟦(1 : ℤ)⟧) := by
  have hα := (shiftFunctorAdd' A m (-1) m' (by omega)).app K
  have hβ := (shiftFunctorCompIsoId A (1 : ℤ) (-1) (by omega)).app E
  exact ⟨fun u v ↦ (shiftFunctor A (-1 : ℤ)).map_injective <| (cancel_mono hβ.hom).mp
    ((cancel_epi hα.hom).mp (h.allEq (hα.hom ≫ (shiftFunctor A (-1 : ℤ)).map u ≫ hβ.hom)
      (hα.hom ≫ (shiftFunctor A (-1 : ℤ)).map v ≫ hβ.hom)))⟩

/-! ### The two implications of [Stacks, Tag 0GEK], abstractly -/

section Adjunction

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  {L : DerivedCategory C ⥤ DerivedCategory D} {R : DerivedCategory D ⥤ DerivedCategory C}
  (adj : L ⊣ R) [L.CommShift ℤ]

/-- If `K` is killed by `L`, every morphism `K⟦m⟧ ⟶ R (L E)` vanishes. -/
private theorem subsingleton_hom_shift_rightAdjoint_obj (adj : L ⊣ R) {K : DerivedCategory C}
    (hK : IsZero (L.obj K)) (m : ℤ) (E : DerivedCategory C) :
    Subsingleton (K⟦m⟧ ⟶ R.obj (L.obj E)) :=
  subsingleton_hom_rightAdjoint_obj_of_isZero adj (isZero_map_shift_of_isZero_map hK m) (L.obj E)

/-- Let `K` be killed by `L` and concentrated in degrees `≤ 0`. If the truncation `τ_{≤a}` of the
unit at `E` is invertible, then every morphism `K⟦-n⟧ ⟶ E` with `n ≤ a` vanishes. -/
theorem subsingleton_hom_shift_of_isIso_truncLE_map_unit {K E : DerivedCategory C}
    (hK : IsZero (L.obj K)) [K.IsLE 0] (a : ℤ)
    (h : IsIso ((DerivedCategory.TStructure.t.truncLE a).map (adj.unit.app E)))
    (n : ℤ) (hn : n ≤ a) : Subsingleton (K⟦-n⟧ ⟶ E) := by
  obtain ⟨N, g, i, hT⟩ := distinguished_cocone_triangle (adj.unit.app E)
  have hN : N.IsGE a := by
    rw [DerivedCategory.isGE_iff]
    exact fun m hm ↦ isZero_homology_obj₃_of_isIso_truncLE_map _ hT a h m (by omega)
  have hLE : DerivedCategory.TStructure.t.IsLE (K⟦-n⟧) n :=
    DerivedCategory.TStructure.t.isLE_shift K 0 (-n) n (by omega)
  have hGE : DerivedCategory.TStructure.t.IsGE (N⟦(-1 : ℤ)⟧) (a + 1) :=
    DerivedCategory.TStructure.t.isGE_shift N a (-1) (a + 1) (by omega)
  have hsub := subsingleton_hom_shift_rightAdjoint_obj adj hK (-n) E
  have key : ∀ u : K⟦-n⟧ ⟶ E, u = 0 := by
    intro u
    obtain ⟨v, hv⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hT) u
      (hsub.allEq _ 0)
    rw [hv, DerivedCategory.TStructure.t.zero_of_isLE_of_isGE v n (a + 1) (by omega) hLE hGE]
    exact zero_comp
  exact subsingleton_of_forall_eq 0 key

/-- Let `E ⟶ R (L E) ⟶ N ⟶ E⟦1⟧` be a distinguished triangle on the unit at `E`, with `K` killed
by `L`. If every morphism `K⟦-n⟧ ⟶ E` vanishes for `n ≤ a + 1`, then every morphism `K⟦-n⟧ ⟶ N`
vanishes for `n ≤ a`. -/
theorem subsingleton_hom_shift_obj₃_of_subsingleton_hom_shift {K E : DerivedCategory C}
    (hK : IsZero (L.obj K)) (a : ℤ)
    (h : ∀ n : ℤ, n ≤ a + 1 → Subsingleton (K⟦-n⟧ ⟶ E))
    {N : DerivedCategory C} {g : R.obj (L.obj E) ⟶ N} {i : N ⟶ E⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (adj.unit.app E) g i ∈ distTriang (DerivedCategory C))
    (n : ℤ) (hn : n ≤ a) : Subsingleton (K⟦-n⟧ ⟶ N) := by
  have hsub := subsingleton_hom_shift_rightAdjoint_obj adj hK (-n) E
  have hshift : Subsingleton (K⟦-n⟧ ⟶ E⟦(1 : ℤ)⟧) :=
    subsingleton_hom_shift_one_of_subsingleton_hom (-n) (-(n + 1)) (by omega)
      (h (n + 1) (by omega))
  have key : ∀ u : K⟦-n⟧ ⟶ N, u = 0 := by
    intro u
    obtain ⟨v, hv⟩ := Triangle.coyoneda_exact₃ _ hT u (hshift.allEq _ 0)
    rw [hv, hsub.allEq v 0, zero_comp]
  exact subsingleton_of_forall_eq 0 key

variable [L.IsTriangulated]

/-- If the counit is invertible at `L E`, the cone `N` of the unit at `E` is killed by `L`. -/
private theorem isZero_obj_obj₃_of_isIso_counit (adj : L ⊣ R)
    {E N : DerivedCategory C} {g : R.obj (L.obj E) ⟶ N} {i : N ⟶ E⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (adj.unit.app E) g i ∈ distTriang (DerivedCategory C))
    (hcounit : IsIso (adj.counit.app (L.obj E))) : IsZero (L.obj N) :=
  Triangle.isZero₃_of_isIso₁ _ (L.map_distinguished _ hT)
    (isIso_map_unit_of_isIso_counit adj E hcounit)

/-- Let `K` be killed by `L`, let the counit be invertible at `L E`, and suppose (`hdet`) that
every object `M` killed by `L` with no nonzero morphism from `K⟦-n⟧` for `n ≤ a` has vanishing
homology in degrees `≤ a`. If every morphism `K⟦-n⟧ ⟶ E` vanishes for `n ≤ a + 1`, then the
truncation `τ_{≤a}` of the unit at `E` is invertible. -/
theorem isIso_truncLE_map_unit_of_subsingleton_hom_shift {K E : DerivedCategory C}
    (hK : IsZero (L.obj K)) (hcounit : IsIso (adj.counit.app (L.obj E))) (a : ℤ)
    (hdet : ∀ M : DerivedCategory C, IsZero (L.obj M) →
      (∀ n : ℤ, n ≤ a → Subsingleton (K⟦-n⟧ ⟶ M)) →
      ∀ i : ℤ, i ≤ a → IsZero ((DerivedCategory.homologyFunctor C i).obj M))
    (h : ∀ n : ℤ, n ≤ a + 1 → Subsingleton (K⟦-n⟧ ⟶ E)) :
    IsIso ((DerivedCategory.TStructure.t.truncLE a).map (adj.unit.app E)) := by
  obtain ⟨N, g, i, hT⟩ := distinguished_cocone_triangle (adj.unit.app E)
  exact isIso_truncLE_map_of_isZero_homology_obj₃ _ hT a
    (hdet N (isZero_obj_obj₃_of_isIso_counit adj hT hcounit)
      (subsingleton_hom_shift_obj₃_of_subsingleton_hom_shift adj hK a h hT))

end Adjunction

/-! ### The graded detection hypothesis is no weaker than the ungraded one -/

section Detection

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]

/-- An object of the derived category with no homology in any degree is a zero object. -/
theorem isZero_of_forall_isZero_homology (M : DerivedCategory C)
    (h : ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor C i).obj M)) : IsZero M := by
  have hLE : M.IsLE 0 := by
    rw [DerivedCategory.isLE_iff]
    exact fun i _ ↦ h i
  have hGE : M.IsGE 1 := by
    rw [DerivedCategory.isGE_iff]
    exact fun i _ ↦ h i
  exact DerivedCategory.TStructure.t.isZero M 0 1 (by omega)

/-- If for every `a` the object `M`, when it has no morphisms from `K⟦-n⟧` for `n ≤ a`, has
vanishing homology in degrees `≤ a`, and `M` is right orthogonal to all shifts of `K`, then `M`
is zero. -/
theorem isZero_of_rightOrthogonal_of_detectionLE {K M : DerivedCategory C}
    (hdet : ∀ a : ℤ, (∀ n : ℤ, n ≤ a → Subsingleton (K⟦-n⟧ ⟶ M)) →
      ∀ i : ℤ, i ≤ a → IsZero ((DerivedCategory.homologyFunctor C i).obj M))
    (h : ((singleton K).shiftClosure ℤ).rightOrthogonal M) : IsZero M := by
  rw [rightOrthogonal_shiftClosure_ofObj_iff] at h
  exact isZero_of_forall_isZero_homology M fun i ↦
    hdet i (fun n _ ↦ subsingleton_of_forall_eq 0 (h () (-n))) i le_rfl

end Detection

end Stacks.DerivedTruncation

/-! ### [Stacks, Tag 0GEK] for the Koszul complex on an affine scheme -/

namespace Stacks.Koszul.Truncation

open Stacks.Duality.OpenImmersion

universe w u

section AnyModel

variable {A : Type u} [CommRing A] {r : ℕ}
  [HasDerivedCategory.{w} (Spec (CommRingCat.of A)).Modules] (f : Fin r → A)
  [HasDerivedCategory.{w} (openComplement f).toScheme.Modules]

/-- Let `f₁, …, f_r ∈ A`, let `U = ⋃ᵢ D(f_i) ⊆ Spec A`, let `j : U ⟶ Spec A` be the inclusion and
let `K` be the sheafified Koszul complex of the sequence. If the canonical map `E ⟶ Rj_*(E|_U)`
becomes invertible after truncation in degrees `≤ a`, then every morphism `K⟦-n⟧ ⟶ E` vanishes
for `n ≤ a`. -/
theorem hom_koszul_eq_zero_of_truncLE_restriction
    (E : DerivedCategory (Spec (CommRingCat.of A)).Modules) (a : ℤ)
    (h : IsIso ((DerivedCategory.TStructure.t.truncLE a).map
      ((derivedRestrictPushforwardAdjunction (openComplement f).ι).unit.app E))) :
    ∀ n : ℤ, n ≤ a → Subsingleton ((koszulObject f)⟦-n⟧ ⟶ E) :=
  Stacks.DerivedTruncation.subsingleton_hom_shift_of_isIso_truncLE_map_unit
    (derivedRestrictPushforwardAdjunction (openComplement f).ι)
    (Stacks.Koszul.OpenComplement.isZero_derivedRestrict_koszulObject f) a h

/-- Let `f₁, …, f_r ∈ A`, let `U = ⋃ᵢ D(f_i) ⊆ Spec A`, let `j : U ⟶ Spec A` be the inclusion and
let `K` be the sheafified Koszul complex of the sequence. Suppose (`hdet`) that every object of
`D(𝒪_{Spec A})` restricting to zero on `U` and receiving no nonzero morphism from `K⟦-n⟧` for
`n ≤ a` has vanishing homology in degrees `≤ a`. If every morphism `K⟦-n⟧ ⟶ E` vanishes for
`n ≤ a + 1`, then the canonical map `E ⟶ Rj_*(E|_U)` is invertible after truncation in degrees
`≤ a`. -/
theorem truncLE_restriction_of_hom_koszul_eq_zero_of_detection
    (E : DerivedCategory (Spec (CommRingCat.of A)).Modules) (a : ℤ)
    (hdet : ∀ M : DerivedCategory (Spec (CommRingCat.of A)).Modules,
      IsZero ((derivedRestrict (openComplement f).ι).obj M) →
      (∀ n : ℤ, n ≤ a → Subsingleton ((koszulObject f)⟦-n⟧ ⟶ M)) →
      ∀ i : ℤ, i ≤ a →
        IsZero ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules i).obj M))
    (h : ∀ n : ℤ, n ≤ a + 1 → Subsingleton ((koszulObject f)⟦-n⟧ ⟶ E)) :
    IsIso ((DerivedCategory.TStructure.t.truncLE a).map
      ((derivedRestrictPushforwardAdjunction (openComplement f).ι).unit.app E)) :=
  Stacks.DerivedTruncation.isIso_truncLE_map_unit_of_subsingleton_hom_shift
    (derivedRestrictPushforwardAdjunction (openComplement f).ι)
    (Stacks.Koszul.OpenComplement.isZero_derivedRestrict_koszulObject f) inferInstance a hdet h

end AnyModel

/-! ### The reverse implication of [Stacks, Tag 0GEK], unconditionally -/

section LocallySmall

variable {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)

/-- Let `f₁, …, f_r ∈ A`, let `U = ⋃ᵢ D(f_i) ⊆ X = Spec A`, let `j : U ⟶ X` be the inclusion and
let `K` be the sheafified Koszul complex of the sequence. Let `E` be an object of `D_QCoh(𝒪_X)`,
that is one whose cohomology sheaves are quasi-coherent. If every morphism `K⟦-n⟧ ⟶ E` vanishes
for `n ≤ a + 1`, then the canonical map `E ⟶ Rj_*(E|_U)` is invertible after truncation in
degrees `≤ a`. This is the second half of `truncLE_restriction_koszul_criterion`, which
carries [Stacks, Tag 0GEK] in its corrected form. -/
theorem truncLE_restriction_of_hom_koszul_eq_zero
    (E : DerivedCategory (Spec (CommRingCat.of A)).Modules)
    (hE : DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of A)).Modules)
      (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf) E)
    (a : ℤ)
    (h : ∀ n : ℤ, n ≤ a + 1 → Subsingleton ((koszulObject f)⟦-n⟧ ⟶ E)) :
    IsIso ((DerivedCategory.TStructure.t.truncLE a).map
      ((derivedRestrictPushforwardAdjunction (openComplement f).ι).unit.app E)) := by
  obtain ⟨N, g, i, hT⟩ := distinguished_cocone_triangle
    ((derivedRestrictPushforwardAdjunction (openComplement f).ι).unit.app E)
  have hLN := Stacks.DerivedTruncation.isZero_obj_obj₃_of_isIso_counit
    (derivedRestrictPushforwardAdjunction (openComplement f).ι) hT inferInstance
  have hQN := AlgebraicGeometry.derivedCategoryB_obj₃_of_distTriang _ hT hE
    (derivedCategoryB_derivedPushforward_openComplement f _
      (Stacks.Duality.OpenImmersion.derivedCategoryB_derivedRestrict
        (openComplement f).ι E hE))
  have hortho := Stacks.DerivedTruncation.subsingleton_hom_shift_obj₃_of_subsingleton_hom_shift
    (derivedRestrictPushforwardAdjunction (openComplement f).ι)
    (Stacks.Koszul.OpenComplement.isZero_derivedRestrict_koszulObject f) a h hT
  exact Stacks.DerivedTruncation.isIso_truncLE_map_of_isZero_homology_obj₃ _ hT a
    (fun j hj ↦ isZero_homology_of_forall_hom_koszulObject_eq_zero f N hQN hLN j
      (fun u ↦ (hortho j hj).allEq u 0))

/-- Let `f₁, …, f_r ∈ A`, let `U = ⋃ᵢ D(f_i) ⊆ X = Spec A`, let `j : U ⟶ X` be the inclusion and
let `K` be the sheafified Koszul complex of the sequence. Let `E` be an object of `D_QCoh(𝒪_X)`,
that is one whose cohomology sheaves are quasi-coherent. If the canonical map `E ⟶ Rj_*(E|_U)` is
invertible after truncation in degrees `≤ a`, then every morphism `K⟦-n⟧ ⟶ E` vanishes for
`n ≤ a - 1`. This is the printed implication "(1) implies (2) with `a` replaced by `a - 1`"
of [Stacks, Tag 0GEK]; the sharper `(1) at a ⟹ (2) at a` is the first half of
`truncLE_restriction_koszul_criterion`. -/
theorem hom_koszul_eq_zero_of_truncLE_restriction_sub_one
    (E : DerivedCategory (Spec (CommRingCat.of A)).Modules)
    (_hE : DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of A)).Modules)
      (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf) E)
    (a : ℤ)
    (h : IsIso ((DerivedCategory.TStructure.t.truncLE a).map
      ((derivedRestrictPushforwardAdjunction (openComplement f).ι).unit.app E))) :
    ∀ n : ℤ, n ≤ a - 1 → Subsingleton ((koszulObject f)⟦-n⟧ ⟶ E) :=
  fun n hn ↦ hom_koszul_eq_zero_of_truncLE_restriction f E a h n (by omega)

/-- Let `f₁, …, f_r ∈ A`, let `U = ⋃ᵢ D(f_i) ⊆ X = Spec A`, let `j : U ⟶ X` be the inclusion, let
`K` be the sheafified Koszul complex of the sequence, let `E` be an object of `D_QCoh(𝒪_X)` and let
`a ∈ ℤ`. Write (1) at `a` for "the canonical map `τ_{≤a}E ⟶ τ_{≤a}Rj_*(E|_U)` is an isomorphism"
and (2) at `a` for "every morphism `K⟦-n⟧ ⟶ E` with `n ≤ a` vanishes". Then (1) at `a` implies
(2) at `a`, and (2) at `a + 1` implies (1) at `a`.

This is [Stacks, Tag 0GEK] corrected per `errata.md` (entry 0GEK, false statement, wrong index):
the printed "(2) implies (1)" at the same `a` is false (`Stacks.Koszul.Errata.erratum_0GEK`, with
`A = k[x]`, `f = (x)`, `E = 𝒪_X`, `a = 0`, proved on the affine side `D(A) ≌ D_QCoh(𝒪_X)`),
and the printed "(1) implies (2) with `a` replaced by `a - 1`" is contained in the first
conjunct. -/
@[stacks 0GEK "Corrected per errata.md (0GEK, wrong index): for E in D_QCoh, (1) at a implies
(2) at a, and (2) at a+1 implies (1) at a. The printed '(2) implies (1)' at the same a is false
(Stacks.Koszul.Errata.erratum_0GEK: A = k[x], f = (x), E = 𝒪_X, a = 0); the printed
'(1) implies (2) with a replaced by a-1' follows from the first conjunct"]
theorem truncLE_restriction_koszul_criterion
    (E : DerivedCategory (Spec (CommRingCat.of A)).Modules)
    (hE : DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of A)).Modules)
      (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf) E)
    (a : ℤ) :
    (IsIso ((DerivedCategory.TStructure.t.truncLE a).map
        ((derivedRestrictPushforwardAdjunction (openComplement f).ι).unit.app E)) →
      ∀ n : ℤ, n ≤ a → Subsingleton ((koszulObject f)⟦-n⟧ ⟶ E)) ∧
    ((∀ n : ℤ, n ≤ a + 1 → Subsingleton ((koszulObject f)⟦-n⟧ ⟶ E)) →
      IsIso ((DerivedCategory.TStructure.t.truncLE a).map
        ((derivedRestrictPushforwardAdjunction (openComplement f).ι).unit.app E))) :=
  ⟨hom_koszul_eq_zero_of_truncLE_restriction f E a,
    truncLE_restriction_of_hom_koszul_eq_zero f E hE a⟩

end LocallySmall

end Stacks.Koszul.Truncation

end
