module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Infinitesimal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Universal
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickening

/-!
# The universal first order thickening of an immersion is its first order neighbourhood

Let `S` be a scheme and let `i : Z ⟶ X` be an immersion of algebraic spaces over `S`, presented
as the source presents it: an open subspace `U ⊆ X` in which `Z` is a closed subspace.  Let
`N ⊆ U` be the first order infinitesimal neighbourhood of `Z`, that is the closed subspace of
`U` cut out by the square of the ideal sheaf of `Z`, in the chart-level spelling of
Stacks 05ZV that this library uses.

This file proves **the second clause of Stacks 0608**: `Z ⊂ N` over `X` is a *universal* first
order thickening of `Z` over `X` in the sense of Stacks 0602.  Since the universal property
determines the thickening up to a unique isomorphism — that is the content of the `∃!` in
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening` — this says exactly that the
universal first order thickening of `Z` over `X` *is* the first order infinitesimal
neighbourhood of `Z` in `X`, which is what the source asserts.

## Main results

* `AlgebraicGeometry.Space.definingIdealAt_preimage_pow_eq_bot`: **the order of the thickening
  `Z ⊂ Z_n`, read with the neighbourhood as the ambient space.** The defining ideal of `Z`
  inside its `n`th order infinitesimal neighbourhood has vanishing `(n+1)`st power on every
  object of the small étale site of the neighbourhood.
* `AlgebraicGeometry.Space.surjective_pointsMap_of_ker_eq_ker_pow` and
  `AlgebraicGeometry.Space.isThickening_preimage_of_ker_eq_ker_pow`: `Z` and its `n`th order
  infinitesimal neighbourhood have the same points, so the inclusion is a thickening in the
  sense of Stacks 05ZK part (1).
* `AlgebraicGeometry.Space.isNthOrderThickening_preimage_of_ker_eq_ker_pow`: the two together,
  `Z ⊂ Z_n` is an `n`th order thickening of `Z_n`.
* `AlgebraicGeometry.Space.isUniversalFirstOrderThickening_infinitesimalNeighbourhood`:
  **the second clause of Stacks 0608.**

## Implementation notes

**The neighbourhood is described, not constructed.**  The neighbourhood enters as a second closed
subspace `N` of `U` together with the hypothesis that on every étale scheme chart of `U` the
kernel ideal sheaf of the chart-level closed immersion of `N` is the `(n+1)`st power of that of
`Z`.  This is the same hypothesis, in the same spelling, that
`AlgebraicGeometry.Space.existsUnique_lift_of_isFirstOrderThickening` (Stacks 05ZW) takes, and
`AlgebraicGeometry.Space.eq_of_ker_eq_ker_pow` shows at most one closed subspace satisfies it, so
it characterises the neighbourhood rather than choosing one.  Cutting `𝓘²` out of `U` directly
would need the surjectivity half of Stacks 03MB.

**`Z` inside `N` is the inverse image of `Z` along the inclusion of `N`.**  This development has
no composition of closed subspaces, so `Z`, a closed subspace of `U` contained in `N`, is read
as a subfunctor of `N` through `CategoryTheory.Subfunctor.preimage` along `N.ι`, which is the
shape `AlgebraicGeometry.Space.preimageSubspace` already takes elsewhere.  Passing between the
two readings is `CategoryTheory.Subfunctor.fromPreimage_ι`.

## References

* [Stacks Project, Tag 0608](https://stacks.math.columbia.edu/tag/0608)
* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 05ZV](https://stacks.math.columbia.edu/tag/05ZV)
* [Stacks Project, Tag 05ZW](https://stacks.math.columbia.edu/tag/05ZW)
* [Stacks Project, Tag 05ZX](https://stacks.math.columbia.edu/tag/05ZX)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Order

variable {X : AlgebraicSpaces B S hS}

/-- **The defining ideal of the whole of an algebraic space vanishes.** -/
theorem definingIdealAt_top (X : AlgebraicSpaces B S hS)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    definingIdealAt B S hS X ⟨⊤, isClosedSubspace_top B S hS X⟩ U = ⊥ := by
  have hret : (ObjectProperty.homMk (inv (⊤ : Subfunctor X.1).ι) :
      X ⟶ (⟨(⊤ : Subfunctor X.1).toFunctor, (isClosedSubspace_top B S hS X).1⟩ :
        AlgebraicSpaces B S hS)) ≫ ObjectProperty.homMk (⊤ : Subfunctor X.1).ι = 𝟙 X :=
    ObjectProperty.hom_ext _ (IsIso.inv_hom_id _)
  exact definingIdealAt_eq_bot_of_retraction B S hS X
    ⟨⊤, isClosedSubspace_top B S hS X⟩ _ hret U

/-- **On an affine étale chart the defining ideal of a closed subspace is the global ideal of
the kernel ideal sheaf of its chart-level closed immersion.** -/
theorem definingIdealAt_eq_ker_ideal_top (Z : ClosedSubspaces B S hS X.1)
    (V : SmallEtale B S hS X.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left)] :
    definingIdealAt B S hS X Z (op V) =
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).ker.ideal
        ⟨⊤, isAffineOpen_top _⟩ := by
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)) :=
    Z.2.2.property V.1.hom _ _ (Z.2.2.rep.isPullback V.1.hom)
  rw [definingIdealAt_eq_ker B S hS X Z V, Scheme.Γ_map_op, Scheme.Hom.ker_apply]
  exact rfl

variable (Z N : ClosedSubspaces B S hS X.1)

/-- **The ideal relation defining an infinitesimal neighbourhood, read on the defining
ideals.**  If on every étale chart of `X` the kernel ideal sheaf of `N` is the `(n+1)`st power of
that of `Z`, then on every affine étale chart the defining ideal of `N` is the `(n+1)`st power of
the defining ideal of `Z`. -/
theorem definingIdealAt_eq_pow_of_ker_eq_ker_pow {n : ℕ}
    (hN : ∀ V : SmallEtale B S hS X.1,
      ((BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd V.1.hom)).ker =
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).ker ^ (n + 1))
    (V : SmallEtale B S hS X.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left)] :
    definingIdealAt B S hS X N (op V) = definingIdealAt B S hS X Z (op V) ^ (n + 1) := by
  rw [definingIdealAt_eq_ker_ideal_top B S hS N V,
    definingIdealAt_eq_ker_ideal_top B S hS Z V, hN V,
    Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
  rfl

/-- **A closed subspace is contained in each of its infinitesimal neighbourhoods.** -/
theorem le_of_ker_eq_ker_pow {n : ℕ}
    (hN : ∀ V : SmallEtale B S hS X.1,
      ((BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd V.1.hom)).ker =
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).ker ^ (n + 1)) :
    Z.1 ≤ N.1 := by
  refine le_of_forall_definingIdealAt_le B S hS X Z N fun V hV => ?_
  have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) := hV
  rw [definingIdealAt_eq_pow_of_ker_eq_ker_pow B S hS Z N hN V]
  exact Ideal.pow_le_self (by simp)

/-- **The defining ideal of a closed subspace inside its `n`th order infinitesimal
neighbourhood has vanishing `(n+1)`st power.**  This is the order of the thickening `Z ⊂ Z_n`
of Stacks 05ZV, read with the neighbourhood as the ambient space rather than on a chart of the
ambient space of the immersion. -/
theorem definingIdealAt_preimage_pow_eq_bot {n : ℕ}
    (hN : ∀ V : SmallEtale B S hS X.1,
      ((BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd V.1.hom)).ker =
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).ker ^ (n + 1))
    (V : SmallEtale B S hS
      (⟨N.1.toFunctor, N.2.1⟩ : AlgebraicSpaces B S hS).1) :
    definingIdealAt B S hS (⟨N.1.toFunctor, N.2.1⟩ : AlgebraicSpaces B S hS)
        (preimageSubspace B S hS (subspaceInclusion B S hS X N) Z) (op V) ^ (n + 1) = ⊥ := by
  obtain ⟨J, W, a, d, hdU, hWaff, hVaff, hcov⟩ :=
    exists_affine_chartDiagram_ofArrows B S hS (subspaceInclusion B S hS X N) V
  refine definingIdealAt_pow_eq_bot_of_ofArrows B S hS
    (⟨N.1.toFunctor, N.2.1⟩ : AlgebraicSpaces B S hS) _ n V W a hcov fun i => ?_
  have hVa : IsAffine ((BigFppfOver.toScheme B S hS).obj (d i).V.1.left) := hVaff i
  have hUa : IsAffine ((BigFppfOver.toScheme B S hS).obj (d i).U.1.left) := by
    rw [hdU i]; exact hWaff i
  have hZside := definingIdealAt_preimage_eq_map B S hS
    (subspaceInclusion B S hS X N) Z (d i).V (d i).U (d i).g (d i).comm.symm
  have hNside := definingIdealAt_preimage_eq_map B S hS
    (subspaceInclusion B S hS X N) N (d i).V (d i).U (d i).g (d i).comm.symm
  have htop : N.1.preimage (subspaceInclusion B S hS X N).hom = ⊤ :=
    (Subfunctor.preimage_eq_top_iff N.1 (subspaceInclusion B S hS X N).hom).2
      (le_of_eq (Subfunctor.range_ι N.1))
  have hNbot : definingIdealAt B S hS (⟨N.1.toFunctor, N.2.1⟩ : AlgebraicSpaces B S hS)
      (preimageSubspace B S hS (subspaceInclusion B S hS X N) N) (op (d i).U) = ⊥ := by
    rw [show preimageSubspace B S hS (subspaceInclusion B S hS X N) N =
      ⟨⊤, isClosedSubspace_top B S hS (⟨N.1.toFunctor, N.2.1⟩ : AlgebraicSpaces B S hS)⟩ from
      Subtype.ext htop]
    exact definingIdealAt_top B S hS _ _
  have hNbot' := hNside.symm.trans hNbot
  rw [definingIdealAt_eq_pow_of_ker_eq_ker_pow B S hS Z N hN (d i).V] at hNbot'
  have hmp := Ideal.map_pow ((BigFppfOver.toScheme B S hS).map (d i).g).appTop.hom
    (definingIdealAt B S hS X Z (op (d i).V)) (n + 1)
  rw [← hdU i, hZside]
  exact hmp.symm.trans hNbot'

/-- **The support of the kernel ideal sheaf of a closed immersion is its range.** -/
private theorem coe_support_ker_eq_range {X Y : Scheme}
    (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsClosedImmersion f] :
    ((f.ker.support : TopologicalSpace.Closeds Y) : Set Y) = Set.range f := by
  rw [Scheme.Hom.support_ker]
  exact f.isClosedEmbedding.isClosed_range.closure_eq

/-- **Surjectivity on points passes from a composite to its second factor.** -/
theorem surjective_pointsMap_of_surjective_comp
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (g : G ⟶ H)
    (h : Function.Surjective (pointsMap B S hS F (f ≫ g))) :
    Function.Surjective (pointsMap B S hS G g) := by
  intro x
  obtain ⟨y, hy⟩ := h x
  refine ⟨pointsMap B S hS F f y, ?_⟩
  rw [pointsMap_comp] at hy
  exact hy

/-- **A closed subspace surjects onto its `n`th order infinitesimal neighbourhood on points.**
Let `Z` and `N` be closed subspaces of an algebraic space `X` with the kernel ideal sheaf of `N`
the `(n+1)`st power of that of `Z` on every étale chart, and let `ζ` be the inclusion of `Z` in
`N` — the unique morphism over `X`, `N.ι` being a monomorphism.  Then `ζ` is surjective on
points. -/
theorem surjective_pointsMap_of_ker_eq_ker_pow {n : ℕ}
    (hN : ∀ V : SmallEtale B S hS X.1,
      ((BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd V.1.hom)).ker =
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).ker ^ (n + 1))
    (ζ : Z.1.toFunctor ⟶ N.1.toFunctor) (hζ : ζ ≫ N.1.ι = Z.1.ι) :
    Function.Surjective (pointsMap B S hS Z.1.toFunctor ζ) := by
  obtain ⟨V, φ, hφS, hφE⟩ := X.2.exists_atlas
  have hNV : ((BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd φ)).ker =
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd φ)).ker ^ (n + 1) :=
    hN ⟨CostructuredArrow.mk φ, hφE⟩
  have hzci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd φ)) := Z.2.2.property_snd φ
  have hnci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd φ)) := N.2.2.property_snd φ
  have hkey : Set.range ((BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd φ)) =
      Set.range ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd φ)) := by
    rw [← coe_support_ker_eq_range, ← coe_support_ker_eq_range, hNV,
      Scheme.IdealSheafData.support_pow_succ]
  have hw : (Z.2.2.rep.fst φ ≫ ζ) ≫ N.1.ι = yoneda.map (Z.2.2.rep.snd φ) ≫ φ := by
    rw [Category.assoc, hζ]
    exact Z.2.2.rep.w φ
  set ℓ := (N.2.2.rep.isPullback φ).lift (Z.2.2.rep.fst φ ≫ ζ)
    (yoneda.map (Z.2.2.rep.snd φ)) hw with hℓ
  have hfst : ℓ ≫ N.2.2.rep.fst φ = Z.2.2.rep.fst φ ≫ ζ :=
    (N.2.2.rep.isPullback φ).lift_fst _ _ _
  have hsnd : ℓ ≫ yoneda.map (N.2.2.rep.snd φ) = yoneda.map (Z.2.2.rep.snd φ) :=
    (N.2.2.rep.isPullback φ).lift_snd _ _ _
  have hzn : yoneda.map (yoneda.preimage ℓ) = ℓ := yoneda.map_preimage ℓ
  have hsite : yoneda.preimage ℓ ≫ N.2.2.rep.snd φ = Z.2.2.rep.snd φ := by
    refine yoneda.map_injective ?_
    rw [Functor.map_comp, hzn]
    exact hsnd
  have hcomp : (BigFppfOver.toScheme B S hS).map (yoneda.preimage ℓ) ≫
      (BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd φ) =
      (BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd φ) := by
    rw [← Functor.map_comp, hsite]
  have hznsurj : AlgebraicGeometry.Surjective
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage ℓ)) := by
    refine (AlgebraicGeometry.surjective_iff _).2 fun y => ?_
    obtain ⟨z, hz⟩ : ((BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd φ)) y ∈
        Set.range ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd φ)) := by
      rw [← hkey]; exact ⟨y, rfl⟩
    refine ⟨z, ((BigFppfOver.toScheme B S hS).map
      (N.2.2.rep.snd φ)).isClosedEmbedding.injective ?_⟩
    have hz2 : ((BigFppfOver.toScheme B S hS).map (yoneda.preimage ℓ) ≫
        (BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd φ)) z =
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd φ)) z := by rw [hcomp]
    simpa using hz2.trans hz
  have h1 : Function.Surjective (pointsMap B S hS
      (yoneda.obj (N.2.2.rep.pullback φ)) (N.2.2.rep.fst φ)) := by
    have halgNV : IsAlgebraicSpace B S hS (yoneda.obj (N.2.2.rep.pullback φ)) :=
      isAlgebraicSpace_yoneda B S hS _
    have halgV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
    have hsq : IsPullback
        (ObjectProperty.homMk (yoneda.map (N.2.2.rep.snd φ)) :
          (⟨yoneda.obj (N.2.2.rep.pullback φ), halgNV⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨yoneda.obj V, halgV⟩)
        (ObjectProperty.homMk (N.2.2.rep.fst φ) :
          (⟨yoneda.obj (N.2.2.rep.pullback φ), halgNV⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨N.1.toFunctor, N.2.1⟩)
        (ObjectProperty.homMk φ : (⟨yoneda.obj V, halgV⟩ : AlgebraicSpaces B S hS) ⟶ X)
        (subspaceInclusion B S hS X N) :=
      IsPullback.of_map_of_faithful (ObjectProperty.ι _) (N.2.2.rep.isPullback φ).flip
    exact isSurjective_of_isPullback B S hS hsq
      ((surjective_iff_surjective_pointsMap B S hS X.1 X.2 V φ).1 hφS)
  have h2 : Function.Surjective (pointsMap B S hS
      (yoneda.obj (Z.2.2.rep.pullback φ)) ℓ) := by
    rw [← hzn]
    exact isSurjective_yoneda_map B S hS (yoneda.preimage ℓ) hznsurj
  have h3 : Function.Surjective (pointsMap B S hS
      (yoneda.obj (Z.2.2.rep.pullback φ)) (Z.2.2.rep.fst φ ≫ ζ)) := by
    rw [← hfst, pointsMap_comp]
    exact h1.comp h2
  exact surjective_pointsMap_of_surjective_comp B S hS _ ζ h3

/-- **A closed subspace is a thickening of its `n`th order infinitesimal neighbourhood**, in the
sense of Stacks 05ZK part (1): it is a closed subspace of it, and the two have the same points. -/
theorem isThickening_preimage_of_ker_eq_ker_pow {n : ℕ}
    (hN : ∀ V : SmallEtale B S hS X.1,
      ((BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd V.1.hom)).ker =
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).ker ^ (n + 1)) :
    IsThickening B S hS (⟨N.1.toFunctor, N.2.1⟩ : AlgebraicSpaces B S hS)
      (Z.1.preimage (subspaceInclusion B S hS X N).hom) := by
  refine ⟨(preimageSubspace B S hS (subspaceInclusion B S hS X N) Z).2, ?_⟩
  have hZN : Z.1 ≤ N.1 := le_of_ker_eq_ker_pow B S hS Z N hN
  have hc : Subfunctor.range (Subfunctor.homOfLe hZN) ≤
      Z.1.preimage (subspaceInclusion B S hS X N).hom := by
    rintro T x ⟨w, rfl⟩
    exact w.2
  refine surjective_pointsMap_of_surjective_comp B S hS
    (Subfunctor.lift (Subfunctor.homOfLe hZN) hc) _ ?_
  rw [Subfunctor.lift_ι]
  exact surjective_pointsMap_of_ker_eq_ker_pow B S hS Z N hN (Subfunctor.homOfLe hZN)
    (Subfunctor.homOfLe_ι hZN)

/-- **A closed subspace sits inside its `n`th order infinitesimal neighbourhood as an `n`th
order thickening**, in the sense of Stacks 05ZK part (4). -/
theorem isNthOrderThickening_preimage_of_ker_eq_ker_pow {n : ℕ}
    (hN : ∀ V : SmallEtale B S hS X.1,
      ((BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd V.1.hom)).ker =
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).ker ^ (n + 1)) :
    IsNthOrderThickening B S hS n (⟨N.1.toFunctor, N.2.1⟩ : AlgebraicSpaces B S hS)
      (Z.1.preimage (subspaceInclusion B S hS X N).hom) :=
  ⟨isThickening_preimage_of_ker_eq_ker_pow B S hS Z N hN,
    fun V => definingIdealAt_preimage_pow_eq_bot B S hS Z N hN V⟩

end Order

section Universal

variable {X : AlgebraicSpaces B S hS} {U : Subfunctor X.1}

/-- Let `Z` be a closed subspace of an open subspace `U` of an algebraic space `X` over `S`, so
that `Z` is immersed in `X`, and let `N` be the first order infinitesimal neighbourhood of `Z` in
`X`, that is the closed subspace of `U` whose kernel ideal sheaf is on every étale chart the
square of that of `Z`.  Then `Z ⊂ N` over `X` is a universal first order thickening of `Z` over
`X` in the sense of Stacks 0602.

The universal property determines the thickening up to a unique isomorphism, so this is the
assertion of the source that *the* universal first order thickening of `Z` over `X` is the first
order infinitesimal neighbourhood of `Z` in `X`.

The structure morphism to `X` is the inclusion of `N` in `U` followed by the inclusion of `U` in
`X`, and `Z` is read inside `N` as the inverse image of `Z` along the former. -/
@[stacks 0608 "part (2): the universal first order thickening is the neighbourhood"]
theorem isUniversalFirstOrderThickening_infinitesimalNeighbourhood
    (hU : IsOpenSubspace B S hS U)
    (Z N : ClosedSubspaces B S hS (⟨U.toFunctor, hU.1⟩ : AlgebraicSpaces B S hS).1)
    (hN : ∀ V : SmallEtale B S hS U.toFunctor,
      ((BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd V.1.hom)).ker =
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).ker ^ 2) :
    IsUniversalFirstOrderThickening B S hS (Z.1.preimage N.1.ι)
      (ObjectProperty.homMk (N.1.ι ≫ U.ι) :
        (⟨N.1.toFunctor, N.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X) where
  firstOrder := isNthOrderThickening_preimage_of_ker_eq_ker_pow B S hS Z N hN
  existsUnique_lift := by
    intro T' T hT a b hab
    have hfp : Z.1.fromPreimage N.1.ι ≫ Z.1.ι = (Z.1.preimage N.1.ι).ι ≫ N.1.ι :=
      Subfunctor.fromPreimage_ι Z.1 N.1.ι
    have hab' : T.ι ≫ b = (a ≫ Z.1.fromPreimage N.1.ι) ≫ Z.1.ι ≫ U.ι := by
      simp only [Category.assoc]
      exact hab
    obtain ⟨c, ⟨hc1, hc2⟩, huniq⟩ :=
      existsUnique_lift_of_isFirstOrderThickening B S hS hU Z N hN hT
        (a ≫ Z.1.fromPreimage N.1.ι) b hab'
    refine ⟨c, ⟨?_, hc2⟩, fun c' hc' => huniq c' ⟨?_, hc'.2⟩⟩
    · refine (cancel_mono N.1.ι).1 ?_
      simp only [Category.assoc]
      rw [hc1]
      simp only [Category.assoc, hfp]
    · simp only [Category.assoc]
      rw [← Category.assoc T.ι c' N.1.ι, hc'.1]
      simp only [Category.assoc, hfp]

end Universal

end AlgebraicGeometry.Space

end
