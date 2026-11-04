module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Abelian.Projective.Horseshoe
public import StacksFrontier.RingTheory.Tor.Balancing

/-!
# Second Tor of a quotient ring with itself

For a surjective homomorphism of commutative rings `P → B` with kernel `J`, the two dimension
shifts attached to the short exact sequence `0 → J → P → B → 0` identify

`Tor₂^P(B, B) = Tor₁^P(J, B) = Ker(J ⊗_P J → J²)`.

This is the first assertion of Stacks Tag 09D6, applied there to the terms `P_n → B` of a
simplicial resolution of `B` over `A`; every such `P_n → B` is a surjection, and the
identification uses nothing else about it.

## Main definitions

* `Stacks.Cotangent.kerShortComplex`: the short exact sequence `0 → J → P → B → 0`.

## Main results

* `Stacks.Cotangent.torTwoSelfIsoTorOneIdeal`: `Tor₂^P(B, B) = Tor₁^P(J, B)`.
* `Stacks.Cotangent.torOneIdealIsoMulKernel`: `Tor₁^P(J, B) = Ker(J ⊗_P J → J²)`.
* `Stacks.Cotangent.torTwoSelfIsoMulKernel`: the composite `Tor₂^P(B, B) = Ker(J ⊗_P J → J²)`.
* `Stacks.Cotangent.ker_mulMap'_eq`: the kernel of `J ⊗_P J → J²` is the kernel of
  multiplication read in `P`.

## Implementation notes

`Tor'` rather than `Tor`. The source defines `Tor_i^P(M, N)` as `H_i(F_• ⊗_P N)` for a free
resolution `F_•` of `M`, so it derives the *first* variable; that functor is Mathlib's
`CategoryTheory.Tor'`, while `CategoryTheory.Tor` derives the second. All three results above are
therefore stated with `Tor'`, in the source's variable order. The balancing isomorphism
`Tor_iso_Tor'` (Tag 00M1) is used once, internally: the first dimension shift is the connecting
map of `0 → J → P → B → 0` for the functor `- ⊗ B`, whose left derived functors are `Tor'`,
while the second is the connecting map of the same sequence for the functor `J ⊗ -`, whose left
derived functors are `Tor`.

Both shifts are the connecting homomorphism `Functor.leftDerivedδ` of the long exact sequence of
left derived functors, not an unspecified isomorphism: the flanking terms are the derived functors
at `P`, which vanish in positive degrees because `P` is projective over itself, so the connecting
map is simultaneously mono and epi.

The source writes the last term as `Ker(J ⊗_P J → J²)`, the kernel of multiplication read into
`J²`; that is `Submodule.mulMap'`. Its kernel coincides with the kernel of `J ⊗_P J → J ⊗_P P`,
the map actually appearing in the long exact sequence (`ker_lTensor_subtype`), and with the
kernel of multiplication read in `P` (`ker_mulMap'_eq`).

Mathlib's monoidal structure on `ModuleCat`, hence `Tor`, requires the modules to live in the
universe of the scalars, so `P` and `B` are in one universe.

## References

* [Stacks Project, Tag 09D6](https://stacks.math.columbia.edu/tag/09D6)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits
open scoped TensorProduct

universe u

namespace Stacks.Cotangent

variable {P B : Type u} [CommRing P] [CommRing B] [Algebra P B]

/-- The short exact sequence `0 → J → P → B → 0` attached to a surjection `P → B` with kernel
`J`, as a short complex of `P`-modules. -/
noncomputable abbrev kerShortComplex (P B : Type u) [CommRing P] [CommRing B] [Algebra P B] :
    ShortComplex (ModuleCat.{u} P) :=
  ShortComplex.mk (ModuleCat.ofHom (RingHom.ker (algebraMap P B)).subtype)
    (ModuleCat.ofHom (Algebra.linearMap P B)) (by ext x; exact x.2)

/-- For a surjection `P → B` the sequence `0 → J → P → B → 0` is short exact. -/
theorem kerShortComplex_shortExact (hf : Function.Surjective (algebraMap P B)) :
    (kerShortComplex P B).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ ?_
    (RingHom.ker (algebraMap P B)).injective_subtype hf
  refine LinearMap.exact_iff.mpr (Submodule.ext fun x => ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, ?_⟩)
  rintro ⟨y, rfl⟩
  exact y.2

/-- The functor `- ⊗ B` on `P`-modules; its `n`-th left derived functor at `M` is
`Tor_n^P(M, B)` in the source's convention. -/
noncomputable abbrev tensorRightTarget (P B : Type u) [CommRing P] [CommRing B] [Algebra P B] :
    ModuleCat.{u} P ⥤ ModuleCat.{u} P :=
  (tensoringRight (ModuleCat.{u} P)).obj (ModuleCat.of P B)

/-- The functor `J ⊗ -` on `P`-modules, where `J = Ker(P → B)`; its `n`-th left derived functor
at `N` is `Tor_n^P(J, N)` in Mathlib's second-variable convention. -/
noncomputable abbrev tensorLeftIdeal (P B : Type u) [CommRing P] [CommRing B] [Algebra P B] :
    ModuleCat.{u} P ⥤ ModuleCat.{u} P :=
  (tensoringLeft (ModuleCat.{u} P)).obj
    (ModuleCat.of P (RingHom.ker (algebraMap P B)))

/-- **Stacks 09D6**, first identification. For a surjection `P → B` with kernel `J`, the
connecting homomorphism of `0 → J → P → B → 0` for the functor `- ⊗ B` is an isomorphism
`Tor₂^P(B, B) ≅ Tor₁^P(J, B)`: the two flanking terms are `Tor_i^P(P, B)` for `i = 1, 2`, which
vanish because `P` is projective over itself. -/
@[stacks 09D6 "Tor₂^P(B, B) = Tor₁^P(J, B)"]
noncomputable def torTwoSelfIsoTorOneIdeal (hf : Function.Surjective (algebraMap P B)) :
    ((Tor' (ModuleCat.{u} P) 2).obj (ModuleCat.of P B)).obj (ModuleCat.of P B) ≅
      ((Tor' (ModuleCat.{u} P) 1).obj
          (ModuleCat.of P (RingHom.ker (algebraMap P B)))).obj (ModuleCat.of P B) := by
  have hS := kerShortComplex_shortExact hf
  set F := tensorRightTarget P B with hF
  set δ := F.leftDerivedδ hS 1 with hδ
  haveI : Mono δ :=
    (F.leftDerived_exact_δ₁ hS 1).mono_g
      (IsZero.eq_of_src
        (F.isZero_leftDerived_obj_projective_succ 1 (kerShortComplex P B).X₂) _ _)
  haveI : Epi δ :=
    (F.leftDerived_exact_δ₂ hS 1).epi_f
      (IsZero.eq_of_tgt
        (F.isZero_leftDerived_obj_projective_succ 0 (kerShortComplex P B).X₂) _ _)
  haveI : IsIso δ := isIso_of_mono_of_epi δ
  have e := asIso δ
  exact e

/-- The value of multiplication `J ⊗_P J → J²`, read in `P`. -/
theorem val_mulMap' (J : Ideal P) (x : ↥J ⊗[P] ↥J) :
    ((Submodule.mulMap' J J x : ↥(J * J)) : P) = Submodule.mulMap J J x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

/-- Multiplication `J ⊗_P J → J²` and multiplication read in `P` have the same kernel, so the
codomain `J²` of the source's map may equally be taken to be `P`. -/
theorem ker_mulMap'_eq (J : Ideal P) :
    LinearMap.ker (Submodule.mulMap' J J) = LinearMap.ker (Submodule.mulMap J J) := by
  ext x
  simp [← val_mulMap']

/-- The kernel of `J ⊗_P J → J ⊗_P P` is the kernel of multiplication `J ⊗_P J → J²`. -/
theorem ker_lTensor_subtype (J : Ideal P) :
    LinearMap.ker (LinearMap.lTensor (↥J) J.subtype) =
      LinearMap.ker (Submodule.mulMap' J J) := by
  have hcomp : (J.subtype ∘ₗ (TensorProduct.rid P (↥J)).toLinearMap) ∘ₗ
      LinearMap.lTensor (↥J) J.subtype = Submodule.mulMap J J := by
    refine TensorProduct.ext' fun a b => ?_
    simp [mul_comm]
  rw [ker_mulMap'_eq, ← hcomp, LinearMap.ker_comp_of_ker_eq_bot]
  rw [LinearMap.ker_comp, Submodule.ker_subtype, Submodule.comap_bot, LinearEquiv.ker]

/-- **Stacks 09D6**, second identification. For a surjection `P → B` with kernel `J`, the
connecting homomorphism of `0 → J → P → B → 0` for the functor `J ⊗ -` identifies
`Tor₁^P(J, B)` with the kernel of the multiplication map `J ⊗_P J → J²`. -/
@[stacks 09D6 "Tor₁^P(J, B) = Ker(J ⊗_P J → J²)"]
noncomputable def torOneIdealIsoMulKernel (hf : Function.Surjective (algebraMap P B)) :
    ((Tor' (ModuleCat.{u} P) 1).obj
          (ModuleCat.of P (RingHom.ker (algebraMap P B)))).obj (ModuleCat.of P B) ≅
      ModuleCat.of P ↥(LinearMap.ker (Submodule.mulMap' (RingHom.ker (algebraMap P B))
        (RingHom.ker (algebraMap P B)))) := by
  have hS := kerShortComplex_shortExact hf
  -- `G = J ⊗ -`, so `(G.leftDerived n).obj N = Tor_n^P(J, N)` in Mathlib's convention
  set G := tensorLeftIdeal P B
  set z₁ := G.leftDerivedZeroIsoSelf.app (kerShortComplex P B).X₁
  set z₂ := G.leftDerivedZeroIsoSelf.app (kerShortComplex P B).X₂
  set δ := G.leftDerivedδ hS 0 with hδ
  have hnat : (G.leftDerived 0).map (kerShortComplex P B).f ≫ z₂.hom =
      z₁.hom ≫ G.map (kerShortComplex P B).f :=
    G.leftDerivedZeroIsoSelf.hom.naturality (kerShortComplex P B).f
  have hzero : (δ ≫ z₁.hom) ≫ G.map (kerShortComplex P B).f = 0 := by
    rw [Category.assoc, ← hnat, ← Category.assoc, hδ, G.leftDerivedδ_comp_map_f hS 0, zero_comp]
  -- the segment `Tor₁^P(J, B) → J ⊗ J → J ⊗ P` is exact
  have hex : (ShortComplex.mk (δ ≫ z₁.hom) (G.map (kerShortComplex P B).f) hzero).Exact := by
    refine ShortComplex.exact_of_iso ?_ (G.leftDerived_exact_δ₂ hS 0)
    exact ShortComplex.isoMk (Iso.refl _) z₁ z₂ (by simp [hδ]) hnat.symm
  -- `J ⊗ J → J ⊗ P` has the kernel of multiplication as its kernel
  have hfex : Function.Exact (δ ≫ z₁.hom).hom (G.map (kerShortComplex P B).f).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hex
  have hmap : (G.map (kerShortComplex P B).f).hom =
      LinearMap.lTensor (↥(RingHom.ker (algebraMap P B)))
        (RingHom.ker (algebraMap P B)).subtype := rfl
  have hker : LinearMap.range (δ ≫ z₁.hom).hom =
      LinearMap.ker (Submodule.mulMap' (RingHom.ker (algebraMap P B))
        (RingHom.ker (algebraMap P B))) := by
    rw [← LinearMap.exact_iff.mp hfex, hmap, ker_lTensor_subtype]
  -- `δ ≫ z₁` is injective
  haveI : Mono δ :=
    (G.leftDerived_exact_δ₁ hS 0).mono_g
      (IsZero.eq_of_src
        (G.isZero_leftDerived_obj_projective_succ 0 (kerShortComplex P B).X₂) _ _)
  have hinj : Function.Injective (δ ≫ z₁.hom).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  -- corestrict to the kernel: injective and, by exactness, surjective
  have hmem : ∀ x, (δ ≫ z₁.hom).hom x ∈
      LinearMap.ker (Submodule.mulMap' (RingHom.ker (algebraMap P B))
        (RingHom.ker (algebraMap P B))) := fun x => by
    rw [← hker]; exact LinearMap.mem_range_self _ x
  set θ := ModuleCat.ofHom (LinearMap.codRestrict
    (LinearMap.ker (Submodule.mulMap' (RingHom.ker (algebraMap P B))
      (RingHom.ker (algebraMap P B)))) (δ ≫ z₁.hom).hom hmem) with hθ
  haveI : IsIso θ := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun y => ?_⟩
    have hy : (y : ↥(RingHom.ker (algebraMap P B)) ⊗[P] ↥(RingHom.ker (algebraMap P B))) ∈
        LinearMap.range (δ ≫ z₁.hom).hom := by rw [hker]; exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have e := asIso θ
  exact (((Tor_iso_Tor' P 1).app (ModuleCat.of P (RingHom.ker (algebraMap P B)))).app
      (ModuleCat.of P B)).symm.trans e

/-- **Stacks 09D6**, the composite identification
`Tor₂^P(B, B) = Ker(J ⊗_P J → J²)` for a surjection `P → B` with kernel `J`. -/
@[stacks 09D6 "Tor₂^P(B, B) = Tor₁^P(J, B) = Ker(J ⊗_P J → J²)"]
noncomputable def torTwoSelfIsoMulKernel (hf : Function.Surjective (algebraMap P B)) :
    ((Tor' (ModuleCat.{u} P) 2).obj (ModuleCat.of P B)).obj (ModuleCat.of P B) ≅
      ModuleCat.of P ↥(LinearMap.ker (Submodule.mulMap' (RingHom.ker (algebraMap P B))
        (RingHom.ker (algebraMap P B)))) :=
  (torTwoSelfIsoTorOneIdeal hf).trans (torOneIdealIsoMulKernel hf)

end Stacks.Cotangent

end
