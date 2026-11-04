module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Abelian.Refinements
public import StacksFrontier.RingTheory.Flat.LocalCriterionVariant
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local criterion for flatness

Let `R → S` be a local homomorphism of Noetherian local rings, let `𝔪` be the maximal ideal of `R`
and `κ = R/𝔪` its residue field, and let `M` be a finite `S`-module. The local criterion for
flatness says that `M` is flat over `R` as soon as `Tor₁^R(κ, M) = 0`.

The proof goes through the short exact sequence `0 → 𝔪 → R → κ → 0`. Since `R` is projective,
the vanishing of `Tor₁^R(κ, M)` says exactly that `𝔪 ⊗_R M → R ⊗_R M` is injective (Remark 00M6):
this is the syzygy description of the first left derived functor of the right exact functor
`- ⊗_R M`. The variant 00ML of the local criterion, applied to the ideal `I = 𝔪`, then gives
flatness of `M`, its second hypothesis — flatness of `M/𝔪M` over `R/𝔪` — holding because `R/𝔪` is
a field.

## Main results

* `Module.Flat.of_isZero_Tor'_one_residueField`: Stacks 00MK, the local criterion for flatness.

## Implementation notes

`Tor₁^R(κ, M)` is `((Tor' (ModuleCat R) 1).obj κ).obj M`, the first left derived functor of
`- ⊗_R M` evaluated at `κ`, as in 00MJ: it is the residue field that is resolved. Forming it in
`ModuleCat R` puts `M` in the universe of `R`; the ring `S` is unconstrained.

The source argues directly: by 00MJ the map `J ⊗_R M → M` is injective for every ideal `J` of
finite colength, and an Artin–Rees argument, together with the faithful flatness of the
`𝔪S`-adic completion of `S`, extends this to every ideal. That Artin–Rees argument is the one
carried out in the proof of 00ML, which uses neither 00MK nor completions, so that here 00MK is
the special case `I = 𝔪` of 00ML.

## References

* [StacksProject 00MK](https://stacks.math.columbia.edu/tag/00MK)
* [StacksProject 00ML](https://stacks.math.columbia.edu/tag/00ML)
* [StacksProject 00M6](https://stacks.math.columbia.edu/tag/00M6)
-/

@[expose] public section

universe u v

open CategoryTheory Limits MonoidalCategory IsLocalRing

namespace Stacks.LocalCriterionForFlatness

section LeftDerived

variable {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]

/-- If `g : Y ⟶ Z` is an epimorphism with `f ≫ g = 0` and `X ⟶ Y ⟶ W` is exact for some
`i : Z ⟶ W`, then `i` is a monomorphism. -/
private lemma mono_of_exact_comp {X Y Z W : C} {f : X ⟶ Y} {g : Y ⟶ Z} (i : Z ⟶ W) [Epi g]
    (h : f ≫ g = 0) (h' : f ≫ (g ≫ i) = 0)
    (hE : (ShortComplex.mk f (g ≫ i) h').Exact) : Mono i := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro T y hy
  obtain ⟨T', e, he, x, hx⟩ := surjective_up_to_refinements_of_epi g y
  have hxz : x ≫ (g ≫ i) = 0 := by
    rw [← Category.assoc, ← hx, Category.assoc, hy, comp_zero]
  obtain ⟨T'', e', he', z, hz⟩ := hE.exact_up_to_refinements x hxz
  have hzero : (e' ≫ e) ≫ y = 0 := by
    rw [Category.assoc, hx, ← Category.assoc, hz, Category.assoc, h, comp_zero]
  exact zero_of_epi_comp (e' ≫ e) hzero

variable [EnoughProjectives C]

/-- The first left derived functor of a right exact additive functor `F` vanishes at `X` only if
`F` remains injective on the first syzygy of a projective resolution of `X`. -/
private lemma mono_map_kernel_ι_of_isZero_leftDerived_one {X : C} (P : ProjectiveResolution X)
    (hX : IsZero ((F.leftDerived 1).obj X)) : Mono (F.map (kernel.ι (P.π.f 0))) := by
  have hz0 : P.complex.d 1 0 ≫ P.π.f 0 = 0 := P.complex_d_comp_π_f_zero
  set q := kernel.lift (P.π.f 0) (P.complex.d 1 0) hz0 with hqdef
  have hqι : q ≫ kernel.ι (P.π.f 0) = P.complex.d 1 0 := kernel.lift_ι _ _ _
  have hex₀ : (ShortComplex.mk (P.complex.d 1 0) (P.π.f 0) hz0).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ P.isColimitCokernelCofork
  have hq : Epi q := hex₀.epi_kernelLift
  have hd2q : P.complex.d 2 1 ≫ q = 0 := by
    rw [← cancel_mono (kernel.ι (P.π.f 0)), Category.assoc, hqι, zero_comp]
    simp
  have hex₁ : (ShortComplex.mk (P.complex.d 2 1) q hd2q).Exact :=
    (Stacks.CategoryHomology.LeftDerivedVanishing.exact_iff_exact_of_eq_comp_mono
      _ hqι.symm).mp (P.exact_succ 0)
  have hFex₁ := hex₁.map_of_epi_of_preservesCokernel F hq inferInstance
  have hFd : F.map (P.complex.d 1 0) = F.map q ≫ F.map (kernel.ι (P.π.f 0)) := by
    rw [← F.map_comp, hqι]
  have hz1 : F.map (P.complex.d 2 1) ≫ (F.map q ≫ F.map (kernel.ι (P.π.f 0))) = 0 := by
    rw [← hFd, ← F.map_comp]
    simp
  rw [Iso.isZero_iff (P.isoLeftDerivedObj F 1)] at hX
  simp only [HomologicalComplex.homologyFunctor_obj] at hX
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)] at hX
  have hX'' : (ShortComplex.mk (F.map (P.complex.d 2 1)) (F.map (P.complex.d 1 0))
      (by rw [← F.map_comp]; simp)).Exact := hX
  have key : ∀ (g : F.obj (P.complex.X 1) ⟶ F.obj (P.complex.X 0))
      (_ : g = F.map (P.complex.d 1 0)) (hz : F.map (P.complex.d 2 1) ≫ g = 0),
      (ShortComplex.mk (F.map (P.complex.d 2 1)) g hz).Exact := by
    rintro g rfl hz
    exact hX''
  exact mono_of_exact_comp (F.map (kernel.ι (P.π.f 0)))
    (by rw [← F.map_comp, hd2q, F.map_zero]) hz1 (key _ hFd.symm hz1)

/-- The syzygy criterion: if `0 → K → P → X → 0` is exact with `P` projective and the first left
derived functor of a right exact additive functor `F` vanishes at `X`, then `F` remains injective
on `K ⟶ P`. -/
private lemma mono_map_of_isZero_leftDerived_one {X K P : C} {ι : K ⟶ P} {π : P ⟶ X}
    [Projective P] [Mono ι] [Epi π] {h : ι ≫ π = 0} (hex : (ShortComplex.mk ι π h).Exact)
    (hX : IsZero ((F.leftDerived 1).obj X)) : Mono (F.map ι) := by
  have PR := projectiveResolution X
  have hepi : Epi (PR.π.f 0) := inferInstance
  have hex₀ : (ShortComplex.mk (kernel.ι (PR.π.f 0)) (PR.π.f 0) (kernel.condition _)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  exact Stacks.CategoryHomology.LeftDerivedVanishing.mono_map_of_mono_map F hepi ‹Epi π› hex₀ hex
    (mono_map_kernel_ι_of_isZero_leftDerived_one F PR hX)

end LeftDerived

/-- **Remark 00M6**, in the direction used here: over a local ring `R` with maximal ideal `𝔪`,
if `Tor₁^R(κ, M) = 0` then `𝔪 ⊗_R M → R ⊗_R M` is injective. -/
private lemma rTensor_subtype_injective_of_isZero_Tor'_one {R : Type u} [CommRing R]
    [IsLocalRing R] (M : Type u) [AddCommGroup M] [Module R M]
    (hTor : IsZero (((Tor' (ModuleCat.{u} R) 1).obj
      (ModuleCat.of R (ResidueField R))).obj (ModuleCat.of R M))) :
    Function.Injective ((maximalIdeal R).subtype.rTensor M) := by
  let e : (R ⧸ maximalIdeal R) ≃ₗ[R] ResidueField R := LinearEquiv.refl R _
  have hTor' : IsZero (((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R M)).leftDerived 1
      |>.obj (ModuleCat.of R (R ⧸ maximalIdeal R))) :=
    hTor.of_iso (((Tor' (ModuleCat.{u} R) 1).mapIso e.toModuleIso).app (ModuleCat.of R M))
  have hzero : ModuleCat.ofHom (maximalIdeal R).subtype ≫ ModuleCat.ofHom (maximalIdeal R).mkQ
      = 0 := by
    ext x
    exact Ideal.Quotient.eq_zero_iff_mem.mpr x.2
  have hSE := ModuleCat.shortComplex_shortExact
    (ShortComplex.mk (ModuleCat.ofHom (maximalIdeal R).subtype)
      (ModuleCat.ofHom (maximalIdeal R).mkQ) hzero)
    (LinearMap.exact_subtype_mkQ _) (Submodule.injective_subtype _)
    (Submodule.mkQ_surjective _)
  have := hSE.mono_f
  have := hSE.epi_g
  have hm := mono_map_of_isZero_leftDerived_one
    ((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R M)) hSE.exact hTor'
  rw [ModuleCat.mono_iff_injective] at hm
  exact hm

end Stacks.LocalCriterionForFlatness

namespace Module.Flat

/-- **Stacks 00MK** (local criterion for flatness). Let `R → S` be a local homomorphism of
Noetherian local rings, let `κ` be the residue field of `R` and let `M` be a finite `S`-module.
If `Tor₁^R(κ, M) = 0`, then `M` is flat over `R`. Here `Tor₁^R(κ, M)` is
`((Tor' (ModuleCat R) 1).obj κ).obj M`, the first left derived functor of `- ⊗_R M` at `κ`. -/
@[stacks 00MK "`Tor₁^R(κ, M)` is `Tor'`, the left derived functor of `- ⊗_R M` evaluated at `κ`;
forming it in `ModuleCat R` puts `M` in the universe of `R`.",
  ega "0 10.1.3" "(d)⇒(c), case (ii)",
  ega "0 10.2.2" "Tor₁^A(M, special case",
  ega "IV 11.3.12" "b⇒a, special case",
  sga "1 IV 4.3" "case (b): (iv) ⇒ (iii)",
  sga "1 IV 5.6" "(ii)⇒(i), special case"]
theorem of_isZero_Tor'_one_residueField {R : Type u} (S : Type v) (M : Type u) [CommRing R]
    [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite S M]
    (hTor : IsZero (((Tor' (ModuleCat.{u} R) 1).obj
      (ModuleCat.of R (ResidueField R))).obj (ModuleCat.of R M))) :
    Module.Flat R M :=
  of_rTensor_subtype_injective_of_flat_quotient S M (maximalIdeal R)
    (maximalIdeal.isMaximal R).ne_top
    (Stacks.LocalCriterionForFlatness.rTensor_subtype_injective_of_isZero_Tor'_one M hTor)
    (by let := Ideal.Quotient.field (maximalIdeal R); exact Module.Flat.of_free)

end Module.Flat
