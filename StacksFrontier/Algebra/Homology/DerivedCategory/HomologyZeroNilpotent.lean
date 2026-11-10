module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# Morphisms vanishing on cohomology compose to zero on a bounded window

A morphism of the derived category which induces zero on every cohomology object need not be
zero. On objects whose cohomology lives in a window of finitely many degrees, however, such
morphisms are nilpotent: a composite of more of them than the width of the window is zero. The
main result here is that statement, `Stacks.DerivedTruncation.chainComp_eq_zero`.

The proof is the truncation triangle `τ_{≤a}X ⟶ X ⟶ τ_{>a}X`. For `f : X ⟶ Y` with `X` and `Y`
both `≥ a`, the truncation `τ_{≤a}f` is a morphism between objects concentrated in the single
degree `a`, and its effect on `H^a` is that of `f`, so it is zero as soon as `H^a(f)` is; hence
`f` kills `τ_{≤a}X` and the composite of the first `ℓ` morphisms of a chain, pushed into
`τ_{>a}` of its target, is the corresponding composite for the chain of `τ_{>a}`'s, which lives
in the window shortened by one and so vanishes by induction. The composite therefore factors
through `τ_{≤a}` of its target, where the next morphism of the chain kills it.

## Main definitions

* `Stacks.DerivedTruncation.chainComp` — the composite of the first `ℓ` morphisms of a chain
  `X 0 ⟶ X 1 ⟶ ⋯`.

## Main results

* `Stacks.DerivedTruncation.eq_zero_of_homologyFunctor_map_eq_zero` — a morphism between objects
  concentrated in one degree which vanishes on the cohomology in that degree is zero.
* `Stacks.DerivedTruncation.mono_homologyFunctor_map_truncLEι`,
  `Stacks.DerivedTruncation.epi_homologyFunctor_map_truncGTπ` — the truncation maps are injective
  respectively surjective on cohomology in the degrees where the truncation is an isomorphism.
* `Stacks.DerivedTruncation.truncLE_map_eq_zero` — `τ_{≤a}f = 0` for `f` vanishing on `H^a`
  between objects `≥ a`.
* `Stacks.DerivedTruncation.chainComp_eq_zero` — the nilpotence statement.

## Implementation notes

A chain is given as a family `X : ℕ → DerivedCategory C` together with `f : ∀ i, X i ⟶ X (i + 1)`;
`chainComp X f ℓ : X 0 ⟶ X ℓ` is built by recursion on the right, and
`Stacks.DerivedTruncation.chainComp_succ_left` rewrites it as the first morphism followed by the
composite of the shifted chain, which is the form the induction uses.

The boundedness hypotheses are `t.IsGE` and `t.IsLE` for the canonical t-structure, passed as
explicit arguments rather than instances because they are quantified over the chain.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace Stacks.DerivedTruncation

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-! ### Morphisms between objects concentrated in a single degree -/

/-- **A morphism between objects concentrated in degree `n` is determined by `H^n`.** If `X` and
`Y` are both `≤ n` and `≥ n` for the canonical t-structure and `H^n(f) = 0`, then `f = 0`.

Such objects are isomorphic to objects of the abelian category placed in degree `n`, and the
functor placing an object in degree `n` is fully faithful with `H^n` as a retraction. -/
theorem eq_zero_of_homologyFunctor_map_eq_zero {X Y : DerivedCategory C} (n : ℤ)
    (hXLE : X.IsLE n) (hXGE : X.IsGE n) (hYLE : Y.IsLE n) (hYGE : Y.IsGE n)
    (f : X ⟶ Y) (hf : (DerivedCategory.homologyFunctor C n).map f = 0) : f = 0 := by
  obtain ⟨M, ⟨eX⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  obtain ⟨N, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Y n
  have h1 : (DerivedCategory.homologyFunctor C n).map (eX.inv ≫ f ≫ eY.hom) = 0 := by
    rw [Functor.map_comp, Functor.map_comp, hf, zero_comp, comp_zero]
  have hmap := (DerivedCategory.singleFunctor C n).map_preimage (eX.inv ≫ f ≫ eY.hom)
  have hnatε := (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).hom.naturality
    ((DerivedCategory.singleFunctor C n).preimage (eX.inv ≫ f ≫ eY.hom))
  rw [Functor.id_map] at hnatε
  have h2 : (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).hom.app M ≫
      (DerivedCategory.singleFunctor C n).preimage (eX.inv ≫ f ≫ eY.hom) = 0 := by
    rw [← hnatε]
    change (DerivedCategory.homologyFunctor C n).map
        ((DerivedCategory.singleFunctor C n).map
          ((DerivedCategory.singleFunctor C n).preimage (eX.inv ≫ f ≫ eY.hom))) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).hom.app N = 0
    rw [hmap, h1, zero_comp]
  have h3 : (DerivedCategory.singleFunctor C n).preimage (eX.inv ≫ f ≫ eY.hom) = 0 :=
    (cancel_epi ((DerivedCategory.singleFunctorCompHomologyFunctorIso C n).hom.app M)).mp
      (h2.trans comp_zero.symm)
  have h4 : eX.inv ≫ f ≫ eY.hom = 0 := by
    rw [← hmap, h3, Functor.map_zero]
  exact (cancel_mono eY.hom).mp
    (((cancel_epi eX.inv).mp (h4.trans comp_zero.symm)).trans zero_comp.symm)

/-! ### The truncation maps on cohomology -/

/-- **The inclusion of the `≤ a` truncation is injective on `H^a`.** The connecting map of the
truncation triangle into `H^a((t.truncLE a).obj Y)` starts at `H^{a-1}` of an object which is
`≥ a + 1`, hence at a zero object. -/
theorem mono_homologyFunctor_map_truncLEι (a : ℤ) (Y : DerivedCategory C) :
    Mono ((DerivedCategory.homologyFunctor C a).map
      ((DerivedCategory.TStructure.t.truncLEι a).app Y)) := by
  have hT := DerivedCategory.TStructure.t.triangleLEGT_distinguished a Y
  have hsrc : IsZero ((DerivedCategory.homologyFunctor C (a - 1)).obj
      ((DerivedCategory.TStructure.t.truncGT a).obj Y)) :=
    DerivedCategory.isZero_of_isGE _ (a + 1) (a - 1) (by omega)
  exact ((DerivedCategory.homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff
    _ hT (a - 1) a (by omega)).mpr (hsrc.eq_zero_of_src _)

/-- **The projection to the `> a` truncation is surjective on `H^n` for `n > a`.** The connecting
map of the truncation triangle out of `H^n((t.truncGT a).obj X)` lands in `H^{n+1}` of an object
which is `≤ a`, hence in a zero object. -/
theorem epi_homologyFunctor_map_truncGTπ (a n : ℤ) (h : a < n) (X : DerivedCategory C) :
    Epi ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncGTπ a).app X)) := by
  have hT := DerivedCategory.TStructure.t.triangleLEGT_distinguished a X
  have htgt : IsZero ((DerivedCategory.homologyFunctor C (n + 1)).obj
      ((DerivedCategory.TStructure.t.truncLE a).obj X)) :=
    DerivedCategory.isZero_of_isLE _ a (n + 1) (by omega)
  exact ((DerivedCategory.homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff
    _ hT n (n + 1) rfl).mpr (htgt.eq_zero_of_tgt _)

/-! ### The truncations of a morphism vanishing on cohomology -/

/-- Naturality of the inclusion of the `≤ a` truncation. -/
private theorem truncLEι_app_comp {X Y : DerivedCategory C} (a : ℤ) (f : X ⟶ Y) :
    (DerivedCategory.TStructure.t.truncLEι a).app X ≫ f =
      (DerivedCategory.TStructure.t.truncLE a).map f ≫
        (DerivedCategory.TStructure.t.truncLEι a).app Y :=
  ((DerivedCategory.TStructure.t.truncLEι a).naturality f).symm

/-- Naturality of the projection to the `> a` truncation. -/
private theorem truncGTπ_app_comp {X Y : DerivedCategory C} (a : ℤ) (f : X ⟶ Y) :
    (DerivedCategory.TStructure.t.truncGTπ a).app X ≫ (DerivedCategory.TStructure.t.truncGT a).map f
      = f ≫ (DerivedCategory.TStructure.t.truncGTπ a).app Y :=
  ((DerivedCategory.TStructure.t.truncGTπ a).naturality f).symm

/-- **The `≤ a` truncation of a morphism vanishing on `H^a` is zero**, provided its source and
target are both `≥ a`: both truncations are then concentrated in degree `a`, and the effect of
the truncated morphism on `H^a` is determined by that of the morphism, because the inclusion of
the truncation is injective on `H^a`. -/
theorem truncLE_map_eq_zero (a : ℤ) {X Y : DerivedCategory C}
    (hXGE : X.IsGE a) (hYGE : Y.IsGE a) (f : X ⟶ Y)
    (hf : (DerivedCategory.homologyFunctor C a).map f = 0) :
    (DerivedCategory.TStructure.t.truncLE a).map f = 0 := by
  have h1 : (DerivedCategory.homologyFunctor C a).map
        ((DerivedCategory.TStructure.t.truncLE a).map f) ≫
      (DerivedCategory.homologyFunctor C a).map
        ((DerivedCategory.TStructure.t.truncLEι a).app Y) = 0 := by
    rw [← Functor.map_comp, ← truncLEι_app_comp, Functor.map_comp, hf, comp_zero]
  have := mono_homologyFunctor_map_truncLEι a Y
  have h2 : (DerivedCategory.homologyFunctor C a).map
      ((DerivedCategory.TStructure.t.truncLE a).map f) = 0 :=
    (cancel_mono ((DerivedCategory.homologyFunctor C a).map
      ((DerivedCategory.TStructure.t.truncLEι a).app Y))).mp (h1.trans zero_comp.symm)
  exact eq_zero_of_homologyFunctor_map_eq_zero a inferInstance inferInstance inferInstance
    inferInstance _ h2

/-- **A morphism vanishing on all cohomology kills the `≤ a` truncation of its source**, when
source and target are `≥ a`. -/
theorem truncLEι_comp_eq_zero (a : ℤ) {X Y : DerivedCategory C}
    (hXGE : X.IsGE a) (hYGE : Y.IsGE a) (f : X ⟶ Y)
    (hf : (DerivedCategory.homologyFunctor C a).map f = 0) :
    (DerivedCategory.TStructure.t.truncLEι a).app X ≫ f = 0 := by
  rw [truncLEι_app_comp, truncLE_map_eq_zero a hXGE hYGE f hf, zero_comp]

/-- **The `> a` truncation of a morphism vanishing on all cohomology again vanishes on all
cohomology.** Below `a + 1` the source of the truncated morphism is a zero object; above `a` the
projection to the truncation is surjective on cohomology. -/
theorem homologyFunctor_map_truncGT_map_eq_zero (a : ℤ) {X Y : DerivedCategory C} (f : X ⟶ Y)
    (hf : ∀ n : ℤ, (DerivedCategory.homologyFunctor C n).map f = 0) (n : ℤ) :
    (DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncGT a).map f) = 0 := by
  by_cases hn : a < n
  · have h1 : (DerivedCategory.homologyFunctor C n).map
          ((DerivedCategory.TStructure.t.truncGTπ a).app X) ≫
        (DerivedCategory.homologyFunctor C n).map
          ((DerivedCategory.TStructure.t.truncGT a).map f) = 0 := by
      rw [← Functor.map_comp, truncGTπ_app_comp, Functor.map_comp, hf n, zero_comp]
    have := epi_homologyFunctor_map_truncGTπ a n hn X
    exact (cancel_epi ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncGTπ a).app X))).mp (h1.trans comp_zero.symm)
  · exact (DerivedCategory.isZero_of_isGE
      ((DerivedCategory.TStructure.t.truncGT a).obj X) (a + 1) n (by omega)).eq_zero_of_src _

/-! ### Composites along a chain -/

/-- The composite of the first `ℓ` morphisms of a chain `X 0 ⟶ X 1 ⟶ ⋯`. -/
def chainComp (X : ℕ → DerivedCategory C) (f : ∀ i : ℕ, X i ⟶ X (i + 1)) :
    ∀ ℓ : ℕ, X 0 ⟶ X ℓ
  | 0 => 𝟙 (X 0)
  | ℓ + 1 => chainComp X f ℓ ≫ f ℓ

/-- The composite of the first `ℓ + 1` morphisms of a chain is the first morphism followed by the
composite of the first `ℓ` morphisms of the chain shifted by one. -/
theorem chainComp_succ_left (X : ℕ → DerivedCategory C) (f : ∀ i : ℕ, X i ⟶ X (i + 1)) (ℓ : ℕ) :
    chainComp X f (ℓ + 1) =
      f 0 ≫ chainComp (fun i => X (i + 1)) (fun i => f (i + 1)) ℓ := by
  induction ℓ with
  | zero => simp [chainComp]
  | succ ℓ ih =>
    change chainComp X f (ℓ + 1) ≫ f (ℓ + 1) = _
    rw [ih, Category.assoc]
    rfl

/-- **Morphisms vanishing on cohomology are nilpotent on a bounded window.** Let `X 0 ⟶ X 1 ⟶ ⋯`
be a chain in the derived category whose objects are all `≥ a` and all `≤ b`, and whose morphisms
all vanish on every cohomology object. If `b < a + ℓ` then the composite of the first `ℓ`
morphisms is zero.

*Argument.* For `ℓ = 0` the window is empty, so `X 0` is a zero object and its identity vanishes.
For the inductive step, the `> a` truncations of the objects form a chain in the window shortened
to `[a + 1, b]` whose morphisms again vanish on cohomology, so by induction the composite of the
first `ℓ` of them is zero; the naturality of the projection to the truncation then shows that the
composite `c` of the first `ℓ` morphisms of the original chain becomes zero in `τ_{>a}(X ℓ)`, so
`c` factors through `τ_{≤a}(X ℓ)`, which the next morphism of the chain kills. -/
theorem chainComp_eq_zero (a b : ℤ) :
    ∀ (ℓ : ℕ) (X : ℕ → DerivedCategory C) (f : ∀ i : ℕ, X i ⟶ X (i + 1)),
      (∀ i, (X i).IsGE a) → (∀ i, (X i).IsLE b) →
      (∀ (i : ℕ) (n : ℤ), (DerivedCategory.homologyFunctor C n).map (f i) = 0) →
      b < a + ℓ → chainComp X f ℓ = 0 := by
  intro ℓ
  induction ℓ generalizing a with
  | zero =>
    intro X f hGE hLE hf hb
    have := hGE 0
    have := hLE 0
    exact DerivedCategory.TStructure.t.zero_of_isLE_of_isGE (𝟙 (X 0)) b a
      (by simpa using hb) (hLE 0) (hGE 0)
  | succ ℓ ih =>
    intro X f hGE hLE hf hb
    -- the chain of `> a` truncations, in the shortened window
    have hGE' : ∀ i, ((DerivedCategory.TStructure.t.truncGT a).obj (X i)).IsGE (a + 1) :=
      fun i => inferInstance
    have hLE' : ∀ i, ((DerivedCategory.TStructure.t.truncGT a).obj (X i)).IsLE b := fun i => by
      have := hLE i
      infer_instance
    have hind := ih (a + 1) (fun i => (DerivedCategory.TStructure.t.truncGT a).obj (X i))
      (fun i => (DerivedCategory.TStructure.t.truncGT a).map (f i)) hGE' hLE'
      (fun i n => homologyFunctor_map_truncGT_map_eq_zero a (f i) (hf i) n) (by omega)
    -- the composite of the first `ℓ` morphisms becomes zero in the truncation
    have hpush : ∀ k : ℕ, chainComp X f k ≫
        (DerivedCategory.TStructure.t.truncGTπ a).app (X k) =
          (DerivedCategory.TStructure.t.truncGTπ a).app (X 0) ≫
            chainComp (fun i => (DerivedCategory.TStructure.t.truncGT a).obj (X i))
              (fun i => (DerivedCategory.TStructure.t.truncGT a).map (f i)) k := by
      intro k
      induction k with
      | zero => simp [chainComp]
      | succ k ihk =>
        change (chainComp X f k ≫ f k) ≫
            (DerivedCategory.TStructure.t.truncGTπ a).app (X (k + 1)) =
          (DerivedCategory.TStructure.t.truncGTπ a).app (X 0) ≫
            (chainComp (fun i => (DerivedCategory.TStructure.t.truncGT a).obj (X i))
                (fun i => (DerivedCategory.TStructure.t.truncGT a).map (f i)) k ≫
              (DerivedCategory.TStructure.t.truncGT a).map (f k))
        rw [Category.assoc, ← truncGTπ_app_comp, ← Category.assoc, ihk, Category.assoc]
    have hzero : chainComp X f ℓ ≫
        (DerivedCategory.TStructure.t.truncGTπ a).app (X ℓ) = 0 := by
      rw [hpush ℓ, hind, comp_zero]
    -- so it factors through the `≤ a` truncation, which the next morphism kills
    obtain ⟨c, hc⟩ := Triangle.coyoneda_exact₂ _
      (DerivedCategory.TStructure.t.triangleLEGT_distinguished a (X ℓ)) (chainComp X f ℓ) hzero
    have hc' : chainComp X f ℓ =
        (show X 0 ⟶ (DerivedCategory.TStructure.t.truncLE a).obj (X ℓ) from c) ≫
          (DerivedCategory.TStructure.t.truncLEι a).app (X ℓ) := hc
    change chainComp X f ℓ ≫ f ℓ = 0
    rw [hc', Category.assoc,
      truncLEι_comp_eq_zero a (hGE ℓ) (hGE (ℓ + 1)) (f ℓ) (hf ℓ a), comp_zero]

end Stacks.DerivedTruncation

end
