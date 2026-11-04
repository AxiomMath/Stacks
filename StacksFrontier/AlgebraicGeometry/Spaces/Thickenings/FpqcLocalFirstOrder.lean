module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesOnAffineSite
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# The order of a thickening of algebraic spaces is fpqc local on the base

Let `f : X ⟶ X'` be a morphism of algebraic spaces over a scheme `S` and let `{gᵢ : X'ᵢ ⟶ X'}` be
an fpqc covering of its target. If every base change `Xᵢ ⟶ X'ᵢ` is an `n`th-order thickening then
so is `f`. Conversely every base change of a thickening, or of a first-order thickening, is one
again, along an arbitrary morphism.

## Main definitions

* `AlgebraicGeometry.Space.IsFirstOrderThickeningHom`: being a first-order thickening, as a
  property of morphisms of algebraic spaces.
* `AlgebraicGeometry.Space.firstOrderThickeningMorphismProperty`: the same, as a property of
  morphisms of the category of algebraic spaces over `S`.

## Main results

* `AlgebraicGeometry.Space.isNthOrderThickening_of_isFpqcCovering`: the order of a thickening
  descends along an fpqc covering, at the level of closed subspaces.
* `AlgebraicGeometry.Space.isFirstOrderThickening_of_isFpqcCovering`: the first-order case.
* `AlgebraicGeometry.Space.isFirstOrderThickeningHom_of_isFpqcCovering`: a morphism whose base
  changes along an fpqc covering are first-order thickenings is a first-order thickening.
* `AlgebraicGeometry.Space.firstOrderThickening_isLocalAtTarget_fpqc`: being a first-order
  thickening is local on the target for the fpqc topology.
* `AlgebraicGeometry.Space.isThickeningHom_and_isFirstOrderThickeningHom_of_isFpqcCovering`:
  thickenings and first-order thickenings both descend along an fpqc covering.
* `AlgebraicGeometry.Space.IsThickeningHom.of_isPullback_hom` and
  `AlgebraicGeometry.Space.IsFirstOrderThickeningHom.of_isPullback`: a base change of a
  thickening, respectively of a first-order thickening, is one again.
* `AlgebraicGeometry.Space.isThickeningHom_iff_forall_of_isFpqcCovering` and
  `AlgebraicGeometry.Space.isFirstOrderThickeningHom_iff_forall_of_isFpqcCovering`: a morphism is
  a thickening, respectively a first-order thickening, if and only if all its base changes along
  an fpqc covering are.

## References

* [Stacks Project, Tag 0BPI](https://stacks.math.columbia.edu/tag/0BPI)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Defining ideals at the tautological étale chart -/

/-- **The defining ideal of an inverse image at a tautological chart.** For a morphism
`f : W ⟶ X` of algebraic spaces over `S` whose source is the algebraic space of an object of
the site, the defining ideal of the inverse image of a closed subspace `Z ⊆ X` at the
tautological chart of `W` is the kernel of pullback of regular functions along the canonical
base change `Z ×_X W ⟶ W`. -/
theorem definingIdealAt_selfChart_preimage {X : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS X.1) {W : BigFppfOver B S hS} (f : schemeSpace W ⟶ X) :
    definingIdealAt B S hS (schemeSpace W)
        (⟨Z.1.preimage f.hom,
          isClosedSubspace_preimage B S hS f.hom Z.1 X.2 (schemeSpace W).2 Z.2⟩ :
          ClosedSubspaces B S hS (schemeSpace W).1)
        (op (selfChart B S hS W)) =
      RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (Z.2.2.rep.snd f.hom)).op).hom := by
  have hid : (selfChart B S hS W).1.hom ≫ f.hom = f.hom := Category.id_comp _
  refine (definingIdealAt_preimage B S hS f Z (selfChart B S hS W)).trans ?_
  exact congrArg (fun k ↦ RingHom.ker (Scheme.Γ.map
    ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd k)).op).hom) hid

/-! ### Descent of the order along an fpqc covering, on an affine chart -/

/-- **The defining ideal at a chart, read on the tautological chart of its scheme.** The
defining ideal of a closed subspace `Z ⊆ X'` at an étale chart `T` is the defining ideal of
the inverse image of `Z` in the algebraic space of `T` at the tautological chart. -/
theorem definingIdealAt_eq_definingIdealAt_selfChart {X' : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS X'.1) (T : SmallEtale B S hS X'.1)
    (hZT : IsClosedSubspace B S hS (Z.1.preimage T.1.hom)) :
    definingIdealAt B S hS X' Z (op T) =
      definingIdealAt B S hS (schemeSpace T.1.left)
        (⟨Z.1.preimage T.1.hom, hZT⟩ : ClosedSubspaces B S hS (schemeSpace T.1.left).1)
        (op (selfChart B S hS T.1.left)) :=
  (definingIdealAt_eq_ker B S hS X' Z T).trans
    (definingIdealAt_selfChart_preimage B S hS Z
      (ObjectProperty.homMk T.1.hom : schemeSpace T.1.left ⟶ X')).symm

/-- **The defining ideal on an affine object over an affine chart is the extension.** For an
affine étale chart `T` of `X'` and an affine object `V` of the site over `T`, the defining
ideal of the inverse image of `Z ⊆ X'` on the tautological chart of `V` is generated by the
image of the defining ideal of `Z` at `T`. -/
theorem definingIdealAt_selfChart_eq_map {X' : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS X'.1) (T : SmallEtale B S hS X'.1)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.1.left))
    {V : BigFppfOver B S hS} (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (r : V ⟶ T.1.left)
    (hcl : IsClosedSubspace B S hS ((Z.1.preimage T.1.hom).preimage (yoneda.map r))) :
    definingIdealAt B S hS (schemeSpace V)
        (⟨(Z.1.preimage T.1.hom).preimage (yoneda.map r), hcl⟩ :
          ClosedSubspaces B S hS (schemeSpace V).1) (op (selfChart B S hS V)) =
      Ideal.map ((BigFppfOver.toScheme B S hS).map r).appTop.hom
        (definingIdealAt B S hS X' Z (op T)) := by
  have hZT : IsClosedSubspace B S hS (Z.1.preimage T.1.hom) :=
    isClosedSubspace_preimage B S hS T.1.hom Z.1 X'.2 (schemeSpace T.1.left).2 Z.2
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    (selfChart B S hS T.1.left).1.left) := hT
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (selfChart B S hS V).1.left) := hV
  have hmap := definingIdealAt_preimage_eq_map B S hS
    (X := schemeSpace T.1.left) (Y := schemeSpace V) (schemeSpaceMap r)
    (⟨Z.1.preimage T.1.hom, hZT⟩ : ClosedSubspaces B S hS (schemeSpace T.1.left).1)
    (selfChart B S hS T.1.left) (selfChart B S hS V) r
    (by
      change yoneda.map r ≫ 𝟙 (yoneda.obj T.1.left) = 𝟙 (yoneda.obj V) ≫ yoneda.map r
      rw [Category.comp_id, Category.id_comp])
  exact hmap.trans
    (congrArg (fun K ↦ Ideal.map ((BigFppfOver.toScheme B S hS).map r).appTop.hom K)
      (definingIdealAt_eq_definingIdealAt_selfChart B S hS Z T hZT).symm)

/-- **The inverse image on an object factoring through a member of the covering is of order
`n`.** If the structure morphism of `V` to `X'` factors through a morphism `q : Q ⟶ X'` along
which the inverse image of `Z` is an `n`th-order thickening, then the power of the defining
ideal of the inverse image of `Z` on the tautological chart of `V` vanishes. -/
theorem definingIdealAt_selfChart_pow_eq_bot_of_factor {n : ℕ}
    {X' Q : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X'.1)
    (T : SmallEtale B S hS X'.1) {V : BigFppfOver B S hS} (r : V ⟶ T.1.left)
    {q : Q ⟶ X'} (a : yoneda.obj V ⟶ Q.1) (ha : a ≫ q.hom = yoneda.map r ≫ T.1.hom)
    (hord : IsNthOrderThickening B S hS n Q (Z.1.preimage q.hom))
    (hcl : IsClosedSubspace B S hS ((Z.1.preimage T.1.hom).preimage (yoneda.map r))) :
    definingIdealAt B S hS (schemeSpace V)
        (⟨(Z.1.preimage T.1.hom).preimage (yoneda.map r), hcl⟩ :
          ClosedSubspaces B S hS (schemeSpace V).1)
        (op (selfChart B S hS V)) ^ (n + 1) = ⊥ := by
  obtain ⟨hth, hpow⟩ := isNthOrderThickening_preimage B S hS (Z.1.preimage q.hom)
    (ObjectProperty.homMk a : schemeSpace V ⟶ Q) hord
  have hsubeq : (Z.1.preimage q.hom).preimage
        (ObjectProperty.homMk a : schemeSpace V ⟶ Q).hom =
      (Z.1.preimage T.1.hom).preimage (yoneda.map r) := by
    change (Z.1.preimage q.hom).preimage a = _
    rw [← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp, ha]
  have hcs : (⟨(Z.1.preimage q.hom).preimage
          (ObjectProperty.homMk a : schemeSpace V ⟶ Q).hom, hth.1⟩ :
        ClosedSubspaces B S hS (schemeSpace V).1) =
      ⟨(Z.1.preimage T.1.hom).preimage (yoneda.map r), hcl⟩ := Subtype.ext hsubeq
  rw [← hcs]
  exact hpow (selfChart B S hS V)

/-- **One member of the refinement kills the power of the ideal.** Let `Z ⊆ X'` be a closed
subspace, `T` an affine étale chart of `X'`, and `V` an affine object of the site over `T`
whose structure morphism to `X'` factors through a morphism `q : Q ⟶ X'` along which the
inverse image of `Z` is an `n`th-order thickening. Then the extension to `V` of the
`(n+1)`st power of the defining ideal `J` of `Z` at `T` vanishes. -/
theorem map_pow_eq_bot_of_factor {n : ℕ} {X' Q : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS X'.1) (T : SmallEtale B S hS X'.1)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.1.left))
    {V : BigFppfOver B S hS} (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (r : V ⟶ T.1.left) {q : Q ⟶ X'} (a : yoneda.obj V ⟶ Q.1)
    (ha : a ≫ q.hom = yoneda.map r ≫ T.1.hom)
    (hord : IsNthOrderThickening B S hS n Q (Z.1.preimage q.hom))
    (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj T.1.left, ⊤))
    (hJ : J = definingIdealAt B S hS X' Z (op T)) :
    Ideal.map ((BigFppfOver.toScheme B S hS).map r).appTop.hom (J ^ (n + 1)) = ⊥ := by
  have hcl : IsClosedSubspace B S hS ((Z.1.preimage T.1.hom).preimage (yoneda.map r)) :=
    isClosedSubspace_preimage B S hS (yoneda.map r) (Z.1.preimage T.1.hom)
      (schemeSpace T.1.left).2 (schemeSpace V).2
      (isClosedSubspace_preimage B S hS T.1.hom Z.1 X'.2 (schemeSpace T.1.left).2 Z.2)
  have h1 : Ideal.map ((BigFppfOver.toScheme B S hS).map r).appTop.hom J =
      definingIdealAt B S hS (schemeSpace V)
        (⟨(Z.1.preimage T.1.hom).preimage (yoneda.map r), hcl⟩ :
          ClosedSubspaces B S hS (schemeSpace V).1) (op (selfChart B S hS V)) :=
    (congrArg (fun K ↦ Ideal.map
        ((BigFppfOver.toScheme B S hS).map r).appTop.hom K) hJ).trans
      (definingIdealAt_selfChart_eq_map B S hS Z T hT hV r hcl).symm
  exact (Ideal.map_pow _ _ _).trans ((congrArg (fun K ↦ K ^ (n + 1)) h1).trans
    (definingIdealAt_selfChart_pow_eq_bot_of_factor B S hS Z T r a ha hord hcl))

/-- **The vanishing of a power of the defining ideal descends along an fpqc covering, on an
affine chart.** If the inverse image of `Z ⊆ X'` in every member of an fpqc covering
`{gᵢ : X'ᵢ ⟶ X'}` is an `n`th-order thickening, then the `(n+1)`st power of the defining ideal of
`Z` at an affine étale chart `T` of `X'` vanishes. -/
theorem definingIdealAt_pow_eq_bot_of_isFpqcCovering_isAffine {n : ℕ} {I : Type v}
    {X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X'.1)
    {X'i : I → AlgebraicSpaces B S hS} (g : ∀ i, X'i i ⟶ X')
    (hg : IsFpqcCovering B S hS fun i ↦ (g i).hom)
    (h : ∀ i, IsNthOrderThickening B S hS n (X'i i) (Z.1.preimage (g i).hom))
    (T : SmallEtale B S hS X'.1)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.1.left)) :
    definingIdealAt B S hS X' Z (op T) ^ (n + 1) = ⊥ := by
  classical
  let T₀ : BigAffineFppf B S hS := ⟨T.1.left, hT⟩
  obtain ⟨𝒱, hfin, hmem, hrefine⟩ := hg.2 T₀ T.1.hom
  have hmem' : Presieve.ofArrows
      (fun j ↦ (BigAffineFppf.toScheme B S hS).obj (𝒱.X j))
      (fun j ↦ (BigAffineFppf.toScheme B S hS).map (𝒱.f j)) ∈
      Scheme.fpqcPrecoverage ((BigAffineFppf.toScheme B S hS).obj T₀) := by
    rwa [show 𝒱.presieve₀ = Presieve.ofArrows 𝒱.X 𝒱.f from rfl, Presieve.map_ofArrows] at hmem
  obtain ⟨hcov, hflat⟩ := (Scheme.ofArrows_mem_precoverage_iff
      (P := @AlgebraicGeometry.Flat.{u})).mp
    (Scheme.propQCPrecoverage_le_precoverage (P := @AlgebraicGeometry.Flat.{u}) _ hmem')
  have : Finite 𝒱.I₀ := hfin
  have hfl : ∀ j, AlgebraicGeometry.Flat
      ((BigAffineFppf.toScheme B S hS).map (𝒱.f j)) := hflat
  have hff := Scheme.faithfullyFlat_pi_appTop
    (U := (BigAffineFppf.toScheme B S hS).obj T₀)
    (fun j ↦ (BigAffineFppf.toScheme B S hS).obj (𝒱.X j))
    (fun j ↦ (BigAffineFppf.toScheme B S hS).map (𝒱.f j))
    (fun x ↦ by obtain ⟨j, y, hy⟩ := hcov x; exact ⟨j, y, hy⟩)
  have hkey : ∀ j : 𝒱.I₀, Ideal.map ((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (𝒱.f j))).appTop.hom
      (definingIdealAt B S hS X' Z (op T) ^ (n + 1)) = ⊥ := by
    intro j
    obtain ⟨i, a, ha⟩ := hrefine j
    exact map_pow_eq_bot_of_factor B S hS Z T hT (𝒱.X j).property
      ((BigAffineFppf.inclusion B S hS).map (𝒱.f j)) a ha (h i)
      (definingIdealAt B S hS X' Z (op T)) rfl
  let : Algebra Γ((BigAffineFppf.toScheme B S hS).obj T₀, ⊤)
      (∀ j : 𝒱.I₀, Γ((BigAffineFppf.toScheme B S hS).obj (𝒱.X j), ⊤)) :=
    (RingHom.pi fun j ↦
      ((BigAffineFppf.toScheme B S hS).map (𝒱.f j)).appTop.hom).toAlgebra
  have : Module.FaithfullyFlat Γ((BigAffineFppf.toScheme B S hS).obj T₀, ⊤)
      (∀ j : 𝒱.I₀, Γ((BigAffineFppf.toScheme B S hS).obj (𝒱.X j), ⊤)) := hff
  have hbot : Ideal.map (algebraMap Γ((BigAffineFppf.toScheme B S hS).obj T₀, ⊤)
        (∀ j : 𝒱.I₀, Γ((BigAffineFppf.toScheme B S hS).obj (𝒱.X j), ⊤)))
      (definingIdealAt B S hS X' Z (op T) ^ (n + 1)) = ⊥ := by
    refine le_bot_iff.mp (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_)
    refine Ideal.mem_comap.mpr (Ideal.mem_bot.mpr ?_)
    refine funext fun j ↦ ?_
    change ((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (𝒱.f j))).appTop.hom x = 0
    exact Ideal.mem_bot.mp (le_of_eq (hkey j) (Ideal.mem_map_of_mem _ hx))
  exact Ideal.map_injective_of_faithfullyFlat
    (A := Γ((BigAffineFppf.toScheme B S hS).obj T₀, ⊤))
    (B := ∀ j : 𝒱.I₀, Γ((BigAffineFppf.toScheme B S hS).obj (𝒱.X j), ⊤))
    (hbot.trans Ideal.map_bot.symm)

/-! ### Descent of the order along an fpqc covering -/

/-- **The order of a thickening descends along an fpqc covering.** Let `Z ⊆ X'` be a thickening of
algebraic spaces over `S` and let `{gᵢ : X'ᵢ ⟶ X'}` be an arbitrary fpqc covering of `X'`. If the
inverse image of `Z` in every member of the covering is an `n`th-order thickening then so is
`Z ⊆ X'`. -/
theorem isNthOrderThickening_of_isFpqcCovering {n : ℕ} {I : Type v}
    {X' : AlgebraicSpaces B S hS} (Z : Subfunctor X'.1)
    (hZ : IsThickening B S hS X' Z)
    {X'i : I → AlgebraicSpaces B S hS} (g : ∀ i, X'i i ⟶ X')
    (hg : IsFpqcCovering B S hS fun i ↦ (g i).hom)
    (h : ∀ i, IsNthOrderThickening B S hS n (X'i i) (Z.preimage (g i).hom)) :
    IsNthOrderThickening B S hS n X' Z := by
  refine ⟨hZ, fun U ↦ ?_⟩
  obtain ⟨J, W, a, -, -, hWaff, -, hcovU⟩ :=
    exists_affine_chartDiagram_ofArrows B S hS (𝟙 X') U
  refine definingIdealAt_pow_eq_bot_of_ofArrows B S hS X' ⟨Z, hZ.1⟩ n U W a hcovU fun i ↦ ?_
  exact definingIdealAt_pow_eq_bot_of_isFpqcCovering_isAffine B S hS ⟨Z, hZ.1⟩ g hg h
    (W i) (hWaff i)

/-- Let `Z ⊆ X'` be a thickening of algebraic spaces over `S` and let `{gᵢ : X'ᵢ ⟶ X'}` be an
fpqc covering of `X'`. If the inverse image of `Z` in every member of the covering is a
first-order thickening then so is `Z ⊆ X'`. -/
theorem isFirstOrderThickening_of_isFpqcCovering {I : Type v}
    {X' : AlgebraicSpaces B S hS} (Z : Subfunctor X'.1)
    (hZ : IsThickening B S hS X' Z)
    {X'i : I → AlgebraicSpaces B S hS} (g : ∀ i, X'i i ⟶ X')
    (hg : IsFpqcCovering B S hS fun i ↦ (g i).hom)
    (h : ∀ i, IsFirstOrderThickening B S hS (X'i i) (Z.preimage (g i).hom)) :
    IsFirstOrderThickening B S hS X' Z :=
  isNthOrderThickening_of_isFpqcCovering B S hS Z hZ g hg h

/-! ### The morphism form -/

/-- A morphism of algebraic spaces over `S` *is a first-order thickening* when it identifies
its source with a first-order thickening subspace of its target: it is an isomorphism onto its
range, and that range is a first-order thickening of the target. -/
def IsFirstOrderThickeningHom {X X' : AlgebraicSpaces B S hS} (i : X ⟶ X') : Prop :=
  IsIso (Subfunctor.toRange i.hom) ∧
    IsFirstOrderThickening B S hS X' (Subfunctor.range i.hom)

/-- A first-order thickening of algebraic spaces is a thickening. -/
theorem IsFirstOrderThickeningHom.isThickeningHom {X X' : AlgebraicSpaces B S hS} {i : X ⟶ X'}
    (hi : IsFirstOrderThickeningHom B S hS i) : IsThickeningHom B S hS i :=
  ⟨hi.1, hi.2.isThickening⟩

/-! ### Base change -/

/-- A base change of a thickening of algebraic spaces, presented by a cartesian square, is a
thickening. -/
theorem IsThickeningHom.of_isPullback_hom {X X' Xi X'i : AlgebraicSpaces B S hS} {f : X ⟶ X'}
    {g : X'i ⟶ X'} {fi : Xi ⟶ X'i} {p : Xi ⟶ X}
    (hsq : IsPullback p.hom fi.hom f.hom g.hom) (hf : IsThickeningHom B S hS f) :
    IsThickeningHom B S hS fi := by
  have : Mono f.hom := hf.mono
  have : Mono fi.hom := hsq.mono_snd_of_mono
  refine ⟨inferInstance, ?_⟩
  rw [Subfunctor.range_eq_preimage_of_isPullback hsq.flip]
  exact isThickening_preimage B S hS (Subfunctor.range f.hom) g hf.2

/-- A base change of a first-order thickening of algebraic spaces, presented by a cartesian
square, is a first-order thickening. -/
theorem IsFirstOrderThickeningHom.of_isPullback {X X' Xi X'i : AlgebraicSpaces B S hS}
    {f : X ⟶ X'} {g : X'i ⟶ X'} {fi : Xi ⟶ X'i} {p : Xi ⟶ X}
    (hsq : IsPullback p.hom fi.hom f.hom g.hom)
    (hf : IsFirstOrderThickeningHom B S hS f) :
    IsFirstOrderThickeningHom B S hS fi := by
  refine ⟨(IsThickeningHom.of_isPullback_hom B S hS hsq hf.isThickeningHom).1, ?_⟩
  rw [Subfunctor.range_eq_preimage_of_isPullback hsq.flip]
  exact isFirstOrderThickening_preimage B S hS (Subfunctor.range f.hom) g hf.2

/-! ### Descent along the covering -/

/-- **Thickenings descend along an fpqc covering, on explicit cartesian squares.** Let
`f : X ⟶ X'` be a morphism of algebraic spaces over `S` and let `{gᵢ : X'ᵢ ⟶ X'}` be an fpqc
covering of `X'` by algebraic spaces. If every base change `fᵢ : Xᵢ ⟶ X'ᵢ` of `f`, presented
by a cartesian square rather than by the chosen pullback, is a thickening then `f` is a
thickening. -/
theorem isThickeningHom_of_isFpqcCovering {I : Type v}
    {X X' : AlgebraicSpaces B S hS} (f : X ⟶ X')
    {Xi X'i : I → AlgebraicSpaces B S hS} (g : ∀ i, X'i i ⟶ X')
    (fi : ∀ i, Xi i ⟶ X'i i) (p : ∀ i, Xi i ⟶ X)
    (hsq : ∀ i, IsPullback (p i).hom (fi i).hom f.hom (g i).hom)
    (hg : IsFpqcCovering B S hS fun i ↦ (g i).hom)
    (h : ∀ i, IsThickeningHom B S hS (fi i)) :
    IsThickeningHom B S hS f := by
  have := thickening_isLocalAtTarget_fpqc.{u, v} B S hS
  refine (isThickeningHom_iff_of_isFpqcCovering B S hS f X'i g hg).mpr fun i ↦ ?_
  have hsqS : IsPullback (p i) (fi i) f (g i) :=
    IsPullback.of_map_of_faithful
      (ObjectProperty.ι
        (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)) (hsq i)
  have hP : thickeningMorphismProperty B S hS (fi i) := h i
  rw [← hsqS.isoPullback_hom_snd] at hP
  exact ((thickeningMorphismProperty B S hS).cancel_left_of_respectsIso
    hsqS.isoPullback.hom (pullback.snd f (g i))).mp hP

/-- Let `f : X ⟶ X'` be a morphism of algebraic spaces over `S` and let `{gᵢ : X'ᵢ ⟶ X'}` be an
fpqc covering of `X'` by algebraic spaces. If every base change `fᵢ : Xᵢ ⟶ X'ᵢ` of `f` is a
first-order thickening then `f` is a first-order thickening. -/
@[stacks 0BPI "first-order clause, for an arbitrary fpqc covering"]
theorem isFirstOrderThickeningHom_of_isFpqcCovering {I : Type v}
    {X X' : AlgebraicSpaces B S hS} (f : X ⟶ X')
    {Xi X'i : I → AlgebraicSpaces B S hS} (g : ∀ i, X'i i ⟶ X')
    (fi : ∀ i, Xi i ⟶ X'i i) (p : ∀ i, Xi i ⟶ X)
    (hsq : ∀ i, IsPullback (p i).hom (fi i).hom f.hom (g i).hom)
    (hg : IsFpqcCovering B S hS fun i ↦ (g i).hom)
    (h : ∀ i, IsFirstOrderThickeningHom B S hS (fi i)) :
    IsFirstOrderThickeningHom B S hS f := by
  have hf : IsThickeningHom B S hS f :=
    isThickeningHom_of_isFpqcCovering B S hS f g fi p hsq hg fun i ↦ (h i).isThickeningHom
  refine ⟨hf.1, isFirstOrderThickening_of_isFpqcCovering B S hS (Subfunctor.range f.hom) hf.2
    g hg fun i ↦ ?_⟩
  rw [← Subfunctor.range_eq_preimage_of_isPullback (hsq i).flip]
  exact (h i).2

/-! ### Locality on the base -/

/-- Being a first-order thickening, as a property of morphisms of the category of algebraic
spaces over `S`: the morphism identifies its source with a first-order thickening subspace of
its target. -/
abbrev firstOrderThickeningMorphismProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun ⦃_ _ : AlgebraicSpaces B S hS⦄ f => IsFirstOrderThickeningHom B S hS f

/-- Being a first-order thickening respects isomorphisms. -/
instance firstOrderThickeningMorphismProperty_respectsIso :
    (firstOrderThickeningMorphismProperty B S hS).RespectsIso :=
  MorphismProperty.RespectsIso.mk _
    (fun {_ _ Z} e f hf ↦ IsFirstOrderThickeningHom.of_isPullback B S hS
      (AlgebraicSpaces.isPullback_hom B S hS
        (IsPullback.of_horiz_isIso ⟨by simp⟩ :
          IsPullback e.hom (e.hom ≫ f) f (𝟙 Z))) hf)
    (fun {X _ _} e f hf ↦ IsFirstOrderThickeningHom.of_isPullback B S hS
      (AlgebraicSpaces.isPullback_hom B S hS
        (IsPullback.of_horiz_isIso ⟨by simp⟩ :
          IsPullback (𝟙 X) (f ≫ e.hom) f e.inv)) hf)

/-- Being a first-order thickening is fpqc local on the base for morphisms of algebraic spaces
over `S`: a morphism whose base change to every member of some fpqc covering of its target is a
first-order thickening is itself one, and conversely. -/
@[stacks 0BPI "first order thickenings"]
instance firstOrderThickening_isLocalAtTarget_fpqc :
    (firstOrderThickeningMorphismProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff
    (P := firstOrderThickeningMorphismProperty B S hS)
    (K := Topology.precoverage.{u, v} .fpqc B S hS) fun X X' f R hR ↦
      ⟨fun hf {_} g _ _ ↦ IsFirstOrderThickeningHom.of_isPullback B S hS
        (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback f g)) hf, fun h ↦ ?_⟩
  obtain ⟨I, X'i, g, hRe, ⟨-, -, hcov⟩⟩ := hR
  exact isFirstOrderThickeningHom_of_isFpqcCovering B S hS f g
    (fun i ↦ pullback.snd f (g i)) (fun i ↦ pullback.fst f (g i))
    (fun i ↦ AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback f (g i)))
    hcov fun i ↦ h (g i) (by rw [hRe]; exact ⟨i⟩)

/-! ### Thickenings and first-order thickenings together -/

/-- Being a thickening is fpqc local, and similarly for first order thickenings. Let
`f : X ⟶ X'` be a morphism of algebraic spaces over `S` and let `{gᵢ : X'ᵢ ⟶ X'}` be an fpqc
covering of `X'` by algebraic spaces, with `fᵢ : Xᵢ ⟶ X'ᵢ` the base change of `f` along `gᵢ`.
Then: if every `fᵢ` is a thickening so is `f`, and if every `fᵢ` is a first-order thickening so
is `f`. -/
@[stacks 0BPI]
theorem isThickeningHom_and_isFirstOrderThickeningHom_of_isFpqcCovering {I : Type v}
    {X X' : AlgebraicSpaces B S hS} (f : X ⟶ X')
    {Xi X'i : I → AlgebraicSpaces B S hS} (g : ∀ i, X'i i ⟶ X')
    (fi : ∀ i, Xi i ⟶ X'i i) (p : ∀ i, Xi i ⟶ X)
    (hsq : ∀ i, IsPullback (p i).hom (fi i).hom f.hom (g i).hom)
    (hg : IsFpqcCovering B S hS fun i ↦ (g i).hom) :
    ((∀ i, IsThickeningHom B S hS (fi i)) → IsThickeningHom B S hS f) ∧
      ((∀ i, IsFirstOrderThickeningHom B S hS (fi i)) →
        IsFirstOrderThickeningHom B S hS f) :=
  ⟨fun h ↦ isThickeningHom_of_isFpqcCovering B S hS f g fi p hsq hg h,
    fun h ↦ isFirstOrderThickeningHom_of_isFpqcCovering B S hS f g fi p hsq hg h⟩

/-- A morphism `f : X ⟶ X'` of
algebraic spaces over `S` is a thickening if and only if its base change along every member of
an fpqc covering `{gᵢ : X'ᵢ ⟶ X'}` is a thickening. -/
@[stacks 0BPI "thickenings, as an equivalence along an fpqc covering"]
theorem isThickeningHom_iff_forall_of_isFpqcCovering {I : Type v}
    {X X' : AlgebraicSpaces B S hS} (f : X ⟶ X')
    {Xi X'i : I → AlgebraicSpaces B S hS} (g : ∀ i, X'i i ⟶ X')
    (fi : ∀ i, Xi i ⟶ X'i i) (p : ∀ i, Xi i ⟶ X)
    (hsq : ∀ i, IsPullback (p i).hom (fi i).hom f.hom (g i).hom)
    (hg : IsFpqcCovering B S hS fun i ↦ (g i).hom) :
    IsThickeningHom B S hS f ↔ ∀ i, IsThickeningHom B S hS (fi i) :=
  ⟨fun hf i ↦ IsThickeningHom.of_isPullback_hom B S hS (hsq i) hf,
    isThickeningHom_of_isFpqcCovering B S hS f g fi p hsq hg⟩

/-- A morphism `f : X ⟶ X'` of
algebraic spaces over `S` is a first-order thickening if and only if its base change along
every member of an fpqc covering `{gᵢ : X'ᵢ ⟶ X'}` is a first-order thickening. -/
@[stacks 0BPI "first-order clause, as an equivalence along an fpqc covering"]
theorem isFirstOrderThickeningHom_iff_forall_of_isFpqcCovering {I : Type v}
    {X X' : AlgebraicSpaces B S hS} (f : X ⟶ X')
    {Xi X'i : I → AlgebraicSpaces B S hS} (g : ∀ i, X'i i ⟶ X')
    (fi : ∀ i, Xi i ⟶ X'i i) (p : ∀ i, Xi i ⟶ X)
    (hsq : ∀ i, IsPullback (p i).hom (fi i).hom f.hom (g i).hom)
    (hg : IsFpqcCovering B S hS fun i ↦ (g i).hom) :
    IsFirstOrderThickeningHom B S hS f ↔
      ∀ i, IsFirstOrderThickeningHom B S hS (fi i) :=
  ⟨fun hf i ↦ IsFirstOrderThickeningHom.of_isPullback B S hS (hsq i) hf,
    isFirstOrderThickeningHom_of_isFpqcCovering B S hS f g fi p hsq hg⟩

end AlgebraicGeometry.Space

end
