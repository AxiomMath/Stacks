module

public import Mathlib.Algebra.Module.Torsion.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Torsion freeness of the quotient by the torsion subsheaf

Let `X` be an integral scheme and `F` a quasi-coherent `𝒪_X`-module. This file constructs the
quotient `F / F_tors` of `F` by its torsion subsheaf `torsionSubsheaf F` and proves that it is
torsion free, which is the second assertion of [Stacks, Tag 0AXT].

## Main definitions

* `torsionQuotient F`: the quotient `F / F_tors`, that is, the cokernel of the inclusion
  `torsionIncl F : F_tors ⟶ F`.

## Main results

* `isTorsionElement_of_smul`: over a domain, an element of a module which becomes torsion after
  multiplication by a nonzero scalar is already torsion.
* `isTorsionFree_torsionQuotient` is the second assertion of [Stacks, Tag 0AXT]: the quotient
  `F / F_tors` is torsion free.

## Implementation notes

The proof is a germ computation at a point `x`, run through the exactness of the stalk functor
on sheaves of modules (`AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact` and
`AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap`). The stalks of `F_tors ⟶ F` and
of `F ⟶ F / F_tors` identify the stalk of `F / F_tors` with the quotient of `F_x` by the image
of `(F_tors)_x`, and that image is exactly the set of torsion elements of `F_x`: a germ of a
torsion section is torsion, and conversely a torsion germ is annihilated by an honest function
whose germs are nonzero at every point of its domain, because on an integral scheme the germ
maps of the structure sheaf are injective.

The stalk functor of `StalkwiseExactness` takes values in modules over the `RingCat`-valued
stalk of the structure sheaf, whereas the torsion notions are stated over the `CommRingCat`
stalk `𝒪_{X, x}`; the two scalar actions agree but are not found by the same instance search,
so `stalkFn` records only the underlying map on stalks and its `𝒪_{X, x}`-linearity is proved
from the germ formula `stalkFn_germ`.

## References

* [Stacks Project, Tag 0AXT](https://stacks.math.columbia.edu/tag/0AXT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.TorsionSubsheaf

universe u

namespace Stacks.AlgebraicGeometry.TorsionQuasicoherent

/-! ### Torsion elements of a module over a domain -/

/-- Over a domain, an element of a module which becomes torsion after multiplication by a
nonzero scalar is already torsion: this is torsion freeness of `M ⧸ Submodule.torsion R M`. -/
theorem isTorsionElement_of_smul {R : Type*} [CommRing R] [IsDomain R] {M : Type*}
    [AddCommGroup M] [Module R M] {r : R} (hr : r ≠ 0) {m : M}
    (h : IsTorsionElement (R := R) (r • m)) : IsTorsionElement (R := R) m := by
  have hmem : ∀ y : M, IsTorsionElement (R := R) y ↔ y ∈ Submodule.torsion R M := fun y =>
    ⟨fun ⟨a, ha, hay⟩ =>
      (Submodule.mem_torsion_iff y).2 ⟨⟨a, mem_nonZeroDivisors_iff_ne_zero.2 ha⟩, hay⟩,
      fun hy => by
        obtain ⟨a, hay⟩ := (Submodule.mem_torsion_iff y).1 hy
        exact ⟨a, mem_nonZeroDivisors_iff_ne_zero.1 a.2, hay⟩⟩
  rw [hmem] at h ⊢
  have hq : r • (Submodule.Quotient.mk m : M ⧸ Submodule.torsion R M) = 0 := by
    rw [← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.mk_eq_zero _).2 h
  exact (Submodule.Quotient.mk_eq_zero _).1
    ((Module.isTorsionFree_iff_smul_eq_zero.1
      Submodule.QuotientTorsion.instIsTorsionFree r _ hq).resolve_left hr)

/-! ### The map induced on stalks -/

variable {X : Scheme.{u}}

/-- The map induced on the stalks at `x` by a morphism of `𝒪_X`-modules. -/
private noncomputable def stalkFn {M N : X.Modules} (f : M ⟶ N) (x : X) :
    M.presheaf.stalk x → N.presheaf.stalk x :=
  fun m => (SheafOfModules.stalkMap X.ringCatSheaf x f).hom m

/-- The stalk map sends the germ of a section to the germ of its image. -/
private lemma stalkFn_germ {M N : X.Modules} (f : M ⟶ N) {x : X} (U : X.Opens) (hx : x ∈ U)
    (s : Γ(M, U)) :
    stalkFn f x (M.presheaf.germ U x hx s) = N.presheaf.germ U x hx (f.app U s) :=
  SheafOfModules.stalkMap_germ X.ringCatSheaf x f U hx s

/-- The stalk map is linear over the local ring. -/
private lemma stalkFn_smul {M N : X.Modules} (f : M ⟶ N) {x : X} (r : X.presheaf.stalk x)
    (m : M.presheaf.stalk x) : stalkFn f x (r • m) = r • stalkFn f x m := by
  obtain ⟨Ur, hxr, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨Um, hUm, hxm, s, rfl⟩ := M.presheaf.exists_le_germ_eq m hxr
  rw [← X.presheaf.germ_res_apply (homOfLE hUm) x hxm a, ← germ_smul M x hxm _ s, stalkFn_germ,
    stalkFn_germ, ← germ_smul N x hxm _ (f.app Um s)]
  congr 1
  exact Scheme.Modules.Hom.app_smul f _ s

/-! ### The quotient by the torsion subsheaf -/

variable [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]

/-- The inclusion of the torsion subsheaf `F_tors ⊆ F`, as a morphism of `𝒪_X`-modules. -/
@[ega "I 7.4.1" "special case"]
noncomputable def torsionIncl : torsionModule F ⟶ F :=
  (torsionSubsheaf F).ι

/-- The quotient `F / F_tors` of a quasi-coherent module on an integral scheme by its torsion
subsheaf, namely the cokernel of `torsionIncl F`. -/
noncomputable def torsionQuotient : X.Modules :=
  cokernel (torsionIncl F)

/-- At every point the stalk sequence of `F_tors ⟶ F ⟶ F / F_tors` is exact. -/
private lemma stalkFn_exact (x : X) :
    Function.Exact (stalkFn (torsionIncl F) x) (stalkFn (cokernel.π (torsionIncl F)) x) := by
  have h := (SheafOfModules.exact_iff_stalkFunctor_map_exact (O := X.ringCatSheaf)
    (ShortComplex.cokernelSequence (torsionIncl F))).1
    (ShortComplex.cokernelSequence_exact _) x
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h
  exact h

/-- The projection onto `F / F_tors` is surjective on stalks. -/
private lemma stalkFn_surjective (x : X) :
    Function.Surjective (stalkFn (cokernel.π (torsionIncl F)) x) :=
  (SheafOfModules.epi_iff_surjective_stalkMap (O := X.ringCatSheaf)
      (cokernel.π (torsionIncl F))).1
    (inferInstanceAs (Epi (C := X.Modules) (cokernel.π (torsionIncl F)))) x

/-- Every germ of the torsion subsheaf is a torsion element of the stalk of `F`. -/
private lemma isTorsionElement_stalkFn_torsionIncl (x : X)
    (z : (torsionModule F).presheaf.stalk x) :
    IsTorsionElement (R := X.presheaf.stalk x) (stalkFn (torsionIncl F) x z) := by
  obtain ⟨W, hxW, w, hw⟩ := (torsionModule F).presheaf.exists_germ_eq z
  rw [← hw, stalkFn_germ]
  exact isTorsionSection_val F w x hxW

/-- Every torsion element of the stalk of `F` comes from the torsion subsheaf. -/
private lemma exists_stalkFn_torsionIncl_eq (x : X) {m : F.presheaf.stalk x}
    (hm : IsTorsionElement (R := X.presheaf.stalk x) m) :
    ∃ z, stalkFn (torsionIncl F) x z = m := by
  obtain ⟨U, hxU, s, hs⟩ := F.presheaf.exists_germ_eq m
  obtain ⟨W, hWU, hxW, a, hane, has⟩ :=
    ReflexiveModules.exists_annihilator_of_isTorsionSection hxU (by rw [hs]; exact hm)
  have ha0 : a ≠ 0 := fun h => hane (by rw [h, map_zero])
  have htors : IsTorsionSection F (F.presheaf.map (homOfLE hWU).op s) := by
    intro y hy
    refine ⟨X.presheaf.germ W y hy a, ?_, ?_⟩
    · exact fun h0 => ha0 (germ_injective_of_isIntegral X y hy (by rw [h0, map_zero]))
    · rw [← germ_smul F y hy a _, has, map_zero]
  refine ⟨(torsionModule F).presheaf.germ W x hxW (mk F _ htors), ?_⟩
  rw [stalkFn_germ]
  show F.presheaf.germ W x hxW (F.presheaf.map (homOfLE hWU).op s) = m
  rw [F.presheaf.germ_res_apply]
  exact hs

/-- **The second assertion of [Stacks, Tag 0AXT].** The quotient of a quasi-coherent module on
an integral scheme by its torsion subsheaf is torsion free. -/
@[stacks 0AXT "the quotient F/F_tors is torsion free", ega "I 7.4.1" "special case"]
theorem isTorsionFree_torsionQuotient :
    ReflexiveModules.IsTorsionFree (torsionQuotient F) := by
  intro U t ht
  refine TopCat.Presheaf.section_ext ⟨(torsionQuotient F).presheaf, (torsionQuotient F).isSheaf⟩
    U t 0 fun x hx => ?_
  rw [map_zero]
  obtain ⟨m, hm⟩ :=
    stalkFn_surjective F x ((torsionQuotient F).presheaf.germ U x hx t)
  obtain ⟨r, hr, hrt⟩ := ht x hx
  have hrm : stalkFn (cokernel.π (torsionIncl F)) x (r • m) = 0 := by
    rw [stalkFn_smul, hm]
    exact hrt
  obtain ⟨z, hz⟩ := (stalkFn_exact F x _).1 hrm
  have htors : IsTorsionElement (R := X.presheaf.stalk x) m :=
    isTorsionElement_of_smul hr (hz ▸ isTorsionElement_stalkFn_torsionIncl F x z)
  obtain ⟨z', hz'⟩ := exists_stalkFn_torsionIncl_eq F x htors
  rw [← hm, ← hz']
  exact (stalkFn_exact F x _).2 ⟨z', rfl⟩

end Stacks.AlgebraicGeometry.TorsionQuasicoherent

end
