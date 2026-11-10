module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.FibreGens
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowEtaleInvertible

/-!
# The theorem of the cube: maximal ideals of a chart are rational points

Over an algebraically closed field, every maximal ideal of the ring of an affine open `V` of a
scheme locally of finite type is the kernel of evaluation at a rational point of `V`
(`Stacks.Cube.exists_point_of_isMaximal`), and the localizations of the ring of an affine open of a
smooth scheme at maximal ideals are regular (`Stacks.Cube.isRegularLocalRing_atPrime`).

## References

* [Stacks Project, Tag 00FV](https://stacks.math.columbia.edu/tag/00FV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace Stacks.Cube

open Stacks.KunnethCech

variable {k : Type u} [Field k] {A : Over (Spec (.of k))}

/-- The map on sections `Γ(A.left, V) ⟶ Γ(Spec k, ⊤)` induced by a rational point `z` with
`z ⁻¹ᵁ V = ⊤` is evaluation `evz z hzV` at `z` followed by the identification `k ≅ Γ(Spec k, ⊤)`.
-/
theorem evz_eq_of (z : Spec (.of k) ⟶ A.left) {V : A.left.Opens} (hzV : z ⁻¹ᵁ V = ⊤)
    (y : chartRing V) : z.appLE V ⊤ (le_top_preimage_z z hzV) y =
      (Scheme.ΓSpecIso (.of k)).inv (evz z hzV y) := by
  simp only [evz, RingHom.comp_apply]
  exact (Iso.hom_inv_id_apply _ _).symm

/-- A rational point is a section of the structure morphism as soon as evaluation at it is a
`k`-algebra map. -/
theorem hzk_of_evz (z : Spec (.of k) ⟶ A.left) {V : A.left.Opens} (hzV : z ⁻¹ᵁ V = ⊤)
    (h : ∀ c : k, evz z hzV ((Stacks.Cech.baseRingHom A.hom V).hom c) = c) :
    z ≫ A.hom = 𝟙 _ := by
  refine ext_of_isAffine ?_
  ext x
  change (z ≫ A.hom).appLE ⊤ ⊤ (Stacks.AffineProduct.le_preimage_top _ _) x = x
  rw [← appLE_comp A.hom z (Stacks.AffineProduct.le_preimage_top A.hom V)
    (le_top_preimage_z z hzV) x, evz_eq_of z hzV]
  have : A.hom.appLE ⊤ V (Stacks.AffineProduct.le_preimage_top A.hom V) x =
      (Stacks.Cech.baseRingHom A.hom V).hom ((Scheme.ΓSpecIso (.of k)).hom x) := by
    rw [Stacks.Cech.baseRingHom_eq_appLE A.hom V (Stacks.AffineProduct.le_preimage_top _ _)]
    change _ = A.hom.appLE ⊤ V _ ((Scheme.ΓSpecIso (.of k)).inv ((Scheme.ΓSpecIso (.of k)).hom x))
    rw [Iso.hom_inv_id_apply]
  rw [this, h, Iso.hom_inv_id_apply]

/-- Every point of the spectrum of the ring of an affine open maps into that open. -/
private theorem fromSpec_mem {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
    (y : PrimeSpectrum Γ(X, U)) : hU.fromSpec y ∈ U := by
  rw [← SetLike.mem_coe, ← hU.range_fromSpec]
  exact ⟨y, rfl⟩

variable [IsAlgClosed k] [LocallyOfFiniteType A.hom] {V : A.left.Opens} (hV : IsAffineOpen V)

include hV in
/-- **Every maximal ideal of the ring of an affine open is a rational point.** -/
theorem exists_point_of_isMaximal (m : Ideal (chartRing V)) [m.IsMaximal] :
    ∃ (z : Spec (.of k) ⟶ A.left) (_ : z ≫ A.hom = 𝟙 _) (hzV : z ⁻¹ᵁ V = ⊤),
      RingHom.ker (evz z hzV) = m := by
  let : Algebra k (chartRing V) := chartAlgebra V
  have hft : (Stacks.Cech.baseRingHom A.hom V).hom.FiniteType := by
    have h1 := A.hom.finiteType_appLE (isAffineOpen_top _) hV
      (Stacks.AffineProduct.le_preimage_top A.hom V)
    have h2 : (Scheme.ΓSpecIso (.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective
    rw [Stacks.Cech.baseRingHom_eq_appLE A.hom V (Stacks.AffineProduct.le_preimage_top _ _)]
    exact h1.comp h2
  let : Field (chartRing V ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k (chartRing V) := hft
  have : Algebra.FiniteType k (chartRing V ⧸ m) := Algebra.FiniteType.trans
    (S := chartRing V) inferInstance inferInstance
  have := finite_of_finite_type_of_isJacobsonRing k (chartRing V ⧸ m)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := chartRing V ⧸ m)
  let e := (RingEquiv.ofBijective (algebraMap k (chartRing V ⧸ m)) hb).symm
  let ev : chartRing V →+* k := e.toRingHom.comp (Ideal.Quotient.mk m)
  have hev : ∀ c : k, ev (algebraMap k (chartRing V) c) = c := fun c => by
    simp only [ev, RingHom.comp_apply]
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact e.apply_symm_apply c
  have hker : RingHom.ker ev = m := by
    ext x
    rw [RingHom.mem_ker]
    simp only [ev, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      map_eq_zero_iff _ e.injective, Ideal.Quotient.eq_zero_iff_mem]
  let z : Spec (.of k) ⟶ A.left := Spec.map (CommRingCat.ofHom ev) ≫ hV.fromSpec
  have hzV : z ⁻¹ᵁ V = ⊤ := by
    exact top_unique fun x _ => fromSpec_mem hV _
  have hzV' : zV z hzV = Spec.map (CommRingCat.ofHom ev) ≫ hV.isoSpec.inv := by
    rw [← cancel_mono V.ι, zV_ι, Category.assoc, IsAffineOpen.isoSpec_inv_ι]
  have hevz : evz z hzV = ev := by
    have h := SpecMap_evz z hV hzV
    rw [hzV', Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  refine ⟨z, hzk_of_evz z hzV fun c => by rw [hevz]; exact hev c, hzV, by rw [hevz, hker]⟩

omit [IsAlgClosed k] [LocallyOfFiniteType A.hom] in
/-- Evaluation at a rational point is onto. -/
theorem evz_surjective (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _) (hzV : z ⁻¹ᵁ V = ⊤) :
    Function.Surjective (evz z hzV) := fun c =>
  ⟨(Stacks.Cech.baseRingHom A.hom V).hom c, evz_algebraMap z hzk hzV c⟩

/-- The residue field at a rational point. -/
noncomputable def quotEquiv (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _)
    (hzV : z ⁻¹ᵁ V = ⊤) :
    letI : Algebra (chartRing V) k := (evz z hzV).toAlgebra
    (chartRing V ⧸ RingHom.ker (evz z hzV)) ≃ₐ[chartRing V] k :=
  letI : Algebra (chartRing V) k := (evz z hzV).toAlgebra
  Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId (chartRing V) k)
    (evz_surjective z hzk hzV)

omit [IsAlgClosed k] [LocallyOfFiniteType A.hom] in
include hV in
/-- **The ring of an affine open of a smooth scheme is regular at maximal ideals.** -/
theorem isRegularLocalRing_atPrime [Smooth A.hom] (m : Ideal (chartRing V)) [m.IsMaximal] :
    IsRegularLocalRing (Localization.AtPrime m) := by
  let y : PrimeSpectrum Γ(A.left, V) := ⟨m, inferInstance⟩
  have hy := fromSpec_mem hV y
  let : Algebra Γ(A.left, V) (A.left.presheaf.stalk (hV.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk A.left.presheaf ⟨hV.fromSpec y, hy⟩
  have : IsLocalization.AtPrime (A.left.presheaf.stalk (hV.fromSpec y)) m :=
    hV.isLocalization_stalk' y hy
  have hreg := isRegularLocalRing_stalk_of_smooth_over_field A.hom (hV.fromSpec y)
  let e : Localization.AtPrime m ≃+* A.left.presheaf.stalk (hV.fromSpec y) :=
    (IsLocalization.algEquiv m.primeCompl (Localization.AtPrime m)
      (A.left.presheaf.stalk (hV.fromSpec y))).toRingEquiv
  exact IsRegularLocalRing.of_ringEquiv e.symm

end Stacks.Cube

end
