module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Henselian
public import StacksFrontier.RingTheory.Flat.MittagLefflerFilteredColimitPresentation
public import StacksFrontier.RingTheory.Flat.MittagLefflerLocal

/-!
# Flat finite modules over essentially finite type local algebras are Mittag-Leffler

Let `A → B` be an essentially finite type local homomorphism of local rings with `A` henselian,
and let `N` be a finite `B`-module which is flat over `A`. Stacks 05U7 asserts two things: that
`N` is a filtered colimit of free `A`-modules whose transition maps stay injective modulo
`𝔪_A`, and that `N` is a Mittag-Leffler `A`-module.

The second assertion is deduced here from the first. The deduction already available in
`StacksFrontier.RingTheory.Flat.MittagLefflerLocal` concludes
`IsMittagLeffler.{u, v, v, v, v}`, with the finitely presented test module, the finitely
presented witness and the test module all in the single universe `v` of the members of the
system. The Mittag-Leffler condition of Stacks 059F quantifies over *all* finitely presented
modules and *all* test modules, so that single-universe conclusion is not the condition itself.
The content of this file is to remove the three universe restrictions, which is what makes the
deduction actually give the source's statement.

## Main definitions

There are no new definitions.

## Main results

* `TensorProduct.exists_fg_lTensor_eq_zero`: an element of `M ⊗ N₀`, for `N₀` a finitely
  generated submodule of `N`, which dies in `M ⊗ N` already dies in `M ⊗ N₁` for some finitely
  generated `N₁` with `N₀ ≤ N₁ ≤ N`. This is the statement that `M ⊗ -` turns the union of the
  finitely generated submodules of `N` into a colimit, and it is what makes the test module in
  the domination relation reducible to a small one.
* `Dominates.of_small`, `DominateEachOther.of_small`: domination tested on the modules of one
  universe `v` with `Small.{v} R` is domination tested on the modules of every universe.
* `IsMittagLeffler.of_small_univ`: the Mittag-Leffler condition with all three auxiliary
  universes equal to a single `v` with `Small.{v} R` implies the condition with the universe of
  the finitely presented source and the universe of the test module arbitrary, and the universe
  of the finitely presented witness `max uR uQ`.
* `Module.isMittagLeffler_of_colimit_free_of_injective_mapQ_maximalIdeal`: a module linearly
  equivalent to the colimit of a directed system of free modules over a local ring with
  injective reductions modulo the maximal ideal is Mittag-Leffler, in the universe-general form
  of Stacks 059F.
* `isMittagLeffler_of_flat_finite_essFiniteType_local`: the Mittag-Leffler half of
  Stacks 05U7, reduced to its filtered-colimit half.

## Implementation notes

The universe reductions all rest on the same two facts: a finitely presented — indeed any
finitely generated — `R`-module is `Small.{v}` as soon as `R` is (`Module.Finite.small`), and a
module which is `Small.{v}` is linearly equivalent to one in `Type v` (`Shrink.linearEquiv`).
For the finitely presented source `P` and the finitely presented witness `Q` of Stacks 059F that
is immediate, since both are finitely presented by hypothesis. The test module `N` is arbitrary,
so it is not small; what replaces smallness is that only finitely many elements of `N` occur in
any one element of `P ⊗ N`, and that the finitely generated submodules they generate detect
vanishing in `M ⊗ N`. The latter is `TensorProduct.exists_fg_lTensor_eq_zero`, proved from a free
presentation `F ↠ M`: right exactness of `- ⊗ N` writes the lift of the vanishing element as a
combination of finitely many elements of `ker(F → M)` tensored with finitely many elements of
`N`, and flatness of the free module `F` transports that identity back down to the finitely
generated submodule of `N` those elements generate.

The deduction of the Mittag-Leffler conclusion from the colimit presentation is available with
the index a nonempty directed preorder, as in Stacks 0AS7
(`ModuleCat.mittagLeffler_pt_of_forall_mittagLeffler_of_forall_rTensor_injective`) and as in
`Module.isMittagLeffler_pt_of_free_of_injective_mapQ_maximalIdeal`. Stacks 05U7 asserts its
presentation over a *filtered* index category, which is strictly weaker: a filtered category need
not be a preorder at all. The index is brought back to a directed preorder by Deligne's theorem
(Stacks 0032, `CategoryTheory.IsFiltered.exists_directed`), which gives every small filtered
category a final functor `G : α ⥤ I` from a nonempty directed partial order. A final functor does
not change colimits, and the stages and transition maps of `G ⋙ F` are stages and transition
maps of `F`, so freeness and the injectivity of the reductions modulo `𝔪_A` are inherited by the
restricted system. This is why
`isMittagLeffler_of_flat_finite_essFiniteType_local` can assume the source's
filtered presentation verbatim.

## References

* [Stacks Project, Tag 05U7](https://stacks.math.columbia.edu/tag/05U7)
* [Stacks Project, Tag 059F](https://stacks.math.columbia.edu/tag/059F)
* [Stacks Project, Tag 0AS7](https://stacks.math.columbia.edu/tag/0AS7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing TensorProduct

universe uR uP uP' uM uQ uQ' uN u v w

/-- Tensoring a map on the left and a map on the right commute. -/
private theorem rTensor_lTensor_comm_apply {R : Type*} [CommRing R] {P M N N' : Type*}
    [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] (f : P →ₗ[R] M) (u : N →ₗ[R] N') (x : P ⊗[R] N) :
    LinearMap.rTensor N' f (LinearMap.lTensor P u x)
      = LinearMap.lTensor M u (LinearMap.rTensor N f x) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
    LinearMap.lTensor_comp_rTensor]

namespace TensorProduct

/-- Let `M` and `N` be `R`-modules and let `N₀` be a finitely generated submodule of `N`. An
element of `M ⊗ N₀` whose image in `M ⊗ N` is zero already has zero image in `M ⊗ N₁` for some
finitely generated submodule `N₁` with `N₀ ≤ N₁ ≤ N`.

This is the statement that `M ⊗ -` carries the presentation of `N` as the union of its finitely
generated submodules into a colimit presentation of `M ⊗ N`. -/
theorem exists_fg_lTensor_eq_zero {R : Type uR} [CommRing R] {M : Type uM} [AddCommGroup M]
    [Module R M] {N : Type uN} [AddCommGroup N] [Module R N] {N₀ : Submodule R N} (hN₀ : N₀.FG)
    (z : M ⊗[R] N₀) (hz : LinearMap.lTensor M N₀.subtype z = 0) :
    ∃ (N₁ : Submodule R N) (h : N₀ ≤ N₁), N₁.FG ∧
      LinearMap.lTensor M (Submodule.inclusion h) z = 0 := by
  let F := M →₀ R
  let φ : F →ₗ[R] M := Finsupp.linearCombination R id
  have hφ : Function.Surjective φ :=
    Finsupp.linearCombination_surjective R Function.surjective_id
  set K := LinearMap.ker φ
  obtain ⟨w, hw⟩ := LinearMap.rTensor_surjective (R := R) (N₀ : Type _) hφ z
  have key : LinearMap.rTensor N φ (LinearMap.lTensor F N₀.subtype w) = 0 := by
    rw [rTensor_lTensor_comm_apply, hw, hz]
  have hex : Function.Exact (LinearMap.rTensor N K.subtype) (LinearMap.rTensor N φ) :=
    rTensor_exact N (LinearMap.exact_subtype_ker_map φ) hφ
  obtain ⟨t, ht⟩ := (hex _).mp key
  obtain ⟨k, m, n, rfl⟩ := TensorProduct.exists_sum_tmul_eq t
  set N₁ := N₀ ⊔ Submodule.span R (Set.range n)
  have h : N₀ ≤ N₁ := le_sup_left
  refine ⟨N₁, h, hN₀.sup (Submodule.fg_span (Set.finite_range n)), ?_⟩
  let n' : Fin k → N₁ := fun j =>
    ⟨n j, Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)⟩
  set t₁ : K ⊗[R] N₁ := ∑ j, m j ⊗ₜ[R] n' j with ht₁
  have hlift : LinearMap.lTensor F (Submodule.inclusion h) w
      = LinearMap.rTensor (N₁ : Type _) K.subtype t₁ := by
    have hinj : Function.Injective (LinearMap.lTensor F N₁.subtype) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    apply hinj
    have e1 : LinearMap.lTensor F N₁.subtype (LinearMap.lTensor F (Submodule.inclusion h) w)
        = LinearMap.lTensor F N₀.subtype w := by
      rw [← LinearMap.lTensor_comp_apply, Submodule.subtype_comp_inclusion]
    have e2 : LinearMap.lTensor F N₁.subtype (LinearMap.rTensor (N₁ : Type _) K.subtype t₁)
        = LinearMap.rTensor N K.subtype (∑ j, m j ⊗ₜ[R] n j) := by
      simp [ht₁, n', LinearMap.lTensor_tmul, LinearMap.rTensor_tmul]
    rw [e1, e2, ht]
  have hcomp : φ ∘ₗ K.subtype = 0 := by
    ext x
    exact x.2
  calc LinearMap.lTensor M (Submodule.inclusion h) z
      = LinearMap.lTensor M (Submodule.inclusion h)
          (LinearMap.rTensor (N₀ : Type _) φ w) := by rw [hw]
    _ = LinearMap.rTensor (N₁ : Type _) φ
          (LinearMap.lTensor F (Submodule.inclusion h) w) :=
        (rTensor_lTensor_comm_apply φ _ w).symm
    _ = LinearMap.rTensor (N₁ : Type _) (φ ∘ₗ K.subtype) t₁ := by
        rw [hlift, LinearMap.rTensor_comp, LinearMap.coe_comp, Function.comp_apply]
    _ = 0 := by rw [hcomp, LinearMap.rTensor_zero, LinearMap.zero_apply]

end TensorProduct

namespace LinearMap

variable {R : Type uR} [CommRing R] {P : Type uP} {M : Type uM} {Q : Type uQ}
  [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]

/-- Tensoring a map on the left and a map on the right commute. -/
theorem rTensor_lTensor_comm {N N' : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] (f : P →ₗ[R] M) (u : N →ₗ[R] N') (x : P ⊗[R] N) :
    LinearMap.rTensor N' f (LinearMap.lTensor P u x)
      = LinearMap.lTensor M u (LinearMap.rTensor N f x) :=
  rTensor_lTensor_comm_apply f u x

/-- Containment of the kernels of two maps tensored with a test module transports along a linear
equivalence of test modules. -/
theorem ker_rTensor_le_of_testEquiv {f : P →ₗ[R] M} {g : P →ₗ[R] Q}
    {N N' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (e : N ≃ₗ[R] N')
    (h : LinearMap.ker (LinearMap.rTensor N f) ≤ LinearMap.ker (LinearMap.rTensor N g)) :
    LinearMap.ker (LinearMap.rTensor N' f) ≤ LinearMap.ker (LinearMap.rTensor N' g) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have hy : LinearMap.rTensor N f (LinearMap.lTensor P e.symm.toLinearMap x) = 0 := by
    rw [rTensor_lTensor_comm, hx, map_zero]
  have hgy := h (LinearMap.mem_ker.mpr hy)
  rw [LinearMap.mem_ker] at hgy
  have hx' : LinearMap.lTensor P e.toLinearMap (LinearMap.lTensor P e.symm.toLinearMap x) = x := by
    rw [← LinearMap.lTensor_comp_apply]
    simp
  rw [← hx', rTensor_lTensor_comm, hgy, map_zero]

/-- Precomposing both maps with one linear equivalence does not change the containment of the
kernels of their tensorings with a test module. -/
theorem ker_rTensor_comp_equiv_le_iff {P' : Type uP'} [AddCommGroup P'] [Module R P']
    (e : P' ≃ₗ[R] P) (f : P →ₗ[R] M) (g : P →ₗ[R] Q)
    (N : Type uN) [AddCommGroup N] [Module R N] :
    LinearMap.ker (LinearMap.rTensor N (f ∘ₗ e.toLinearMap)) ≤
        LinearMap.ker (LinearMap.rTensor N (g ∘ₗ e.toLinearMap)) ↔
      LinearMap.ker (LinearMap.rTensor N f) ≤ LinearMap.ker (LinearMap.rTensor N g) := by
  rw [LinearMap.rTensor_comp, LinearMap.rTensor_comp, LinearMap.ker_comp, LinearMap.ker_comp]
  exact Submodule.comap_le_comap_iff_of_surjective
    (f := LinearMap.rTensor N e.toLinearMap) (e.rTensor N).surjective

/-- Postcomposing with a linear equivalence does not change the kernel of the tensoring with a
test module. -/
theorem ker_rTensor_equiv_comp {Q' : Type uQ'} [AddCommGroup Q'] [Module R Q']
    (e : Q ≃ₗ[R] Q') (g : P →ₗ[R] Q) (N : Type uN) [AddCommGroup N] [Module R N] :
    LinearMap.ker (LinearMap.rTensor N (e.toLinearMap ∘ₗ g))
      = LinearMap.ker (LinearMap.rTensor N g) := by
  have hinj : Function.Injective (LinearMap.rTensor N e.toLinearMap) := (e.rTensor N).injective
  rw [LinearMap.rTensor_comp, LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr hinj,
    Submodule.comap_bot]

end LinearMap

section Domination

variable {R : Type uR} [CommRing R] {P : Type uP} {M : Type uM} {Q : Type uQ}
  [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]

/-- **The test module in the domination relation can be shrunk.** If `g : P → Q` dominates
`f : P → M` when tested against every `R`-module in one universe `v` with `Small.{v} R`, then it
dominates `f` when tested against every `R`-module in every universe. -/
theorem Dominates.of_small [Small.{v} R] {f : P →ₗ[R] M} {g : P →ₗ[R] Q}
    (h : Dominates.{uR, uP, uM, uQ, v} f g) : Dominates.{uR, uP, uM, uQ, uN} f g := by
  intro N _ _
  show LinearMap.ker (LinearMap.rTensor N f) ≤ LinearMap.ker (LinearMap.rTensor N g)
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  obtain ⟨k, p, nn, rfl⟩ := TensorProduct.exists_sum_tmul_eq (R := R) (M := P) (N := N) x
  set N₀ := Submodule.span R (Set.range nn)
  let nn' : Fin k → N₀ := fun j => ⟨nn j, Submodule.subset_span ⟨j, rfl⟩⟩
  set x₀ : P ⊗[R] N₀ := ∑ j, p j ⊗ₜ[R] nn' j with hx₀
  have hpush : LinearMap.lTensor P N₀.subtype x₀ = ∑ j, p j ⊗ₜ[R] nn j := by
    simp [hx₀, nn']
  have hz : LinearMap.lTensor M N₀.subtype (LinearMap.rTensor (N₀ : Type _) f x₀) = 0 := by
    rw [← LinearMap.rTensor_lTensor_comm, hpush, hx]
  obtain ⟨N₁, hle, hN₁, hzero⟩ := TensorProduct.exists_fg_lTensor_eq_zero
    (Submodule.fg_span (Set.finite_range nn)) _ hz
  set x₁ : P ⊗[R] N₁ := LinearMap.lTensor P (Submodule.inclusion hle) x₀ with hx₁
  have hfx₁ : LinearMap.rTensor (N₁ : Type _) f x₁ = 0 := by
    rw [hx₁, LinearMap.rTensor_lTensor_comm, hzero]
  have : Module.Finite R (N₁ : Type _) := Module.Finite.iff_fg.mpr hN₁
  have : Small.{v} (N₁ : Type _) := Module.Finite.small.{v} R _
  have hdom := LinearMap.ker_rTensor_le_of_testEquiv (f := f) (g := g)
    (Shrink.linearEquiv R (N₁ : Type _)) (h (Shrink.{v} (N₁ : Type _)))
  have hx₁push : LinearMap.lTensor P N₁.subtype x₁ = ∑ j, p j ⊗ₜ[R] nn j := by
    rw [hx₁, ← LinearMap.lTensor_comp_apply, Submodule.subtype_comp_inclusion, hpush]
  rw [← hx₁push, LinearMap.rTensor_lTensor_comm,
    LinearMap.mem_ker.mp (hdom (LinearMap.mem_ker.mpr hfx₁)), map_zero]

/-- **The test module in the mutual domination relation can be shrunk.** -/
theorem DominateEachOther.of_small [Small.{v} R] {f : P →ₗ[R] M} {g : P →ₗ[R] Q}
    (h : DominateEachOther.{uR, uP, uM, uQ, v} f g) :
    DominateEachOther.{uR, uP, uM, uQ, uN} f g :=
  ⟨Dominates.of_small h.1, Dominates.of_small h.2⟩

end Domination

/-- **The three auxiliary universes in the Mittag-Leffler condition can be enlarged.** If `M` is
Mittag-Leffler when the finitely presented source, the finitely presented witness and the test
module are all taken in one universe `v` with `Small.{v} R`, then `M` is Mittag-Leffler with the
universe of the finitely presented source and the universe of the test module arbitrary.

The witness is produced in `Type (max uR uQ)`: a finitely presented module over `R` is
`Small.{uR}`, hence can be modelled in any universe containing `uR`, but not in an arbitrary
universe smaller than that of `R`. -/
theorem IsMittagLeffler.of_small_univ {R : Type uR} [CommRing R] [Small.{v} R] {M : Type uM}
    [AddCommGroup M] [Module R M] (h : IsMittagLeffler.{uR, v, uM, v, v} R M) :
    IsMittagLeffler.{uR, uP, uM, max uR uQ, uN} R M := by
  intro P _ _ _ f
  have : Small.{v} P := Module.Finite.small.{v} R P
  let eP : Shrink.{v} P ≃ₗ[R] P := Shrink.linearEquiv R P
  have : Module.FinitePresentation R (Shrink.{v} P) :=
    Module.FinitePresentation.of_equiv eP.symm
  obtain ⟨Q₀, hQa, hQm, hQfp, g₀, hd₁, hd₂⟩ := h (Shrink.{v} P) (f ∘ₗ eP.toLinearMap)
  have : Small.{max uR uQ} Q₀ := Module.Finite.small.{max uR uQ} R Q₀
  let eQ : Shrink.{max uR uQ} Q₀ ≃ₗ[R] Q₀ := Shrink.linearEquiv R Q₀
  have hd₁' : Dominates.{uR, v, uM, v, uN} (f ∘ₗ eP.toLinearMap) g₀ := Dominates.of_small hd₁
  have hd₂' : Dominates.{uR, v, v, uM, uN} g₀ (f ∘ₗ eP.toLinearMap) := Dominates.of_small hd₂
  have hfold : (g₀ ∘ₗ eP.symm.toLinearMap) ∘ₗ eP.toLinearMap = g₀ := by
    ext x
    simp [eP]
  refine ⟨Shrink.{max uR uQ} Q₀, inferInstance, inferInstance,
    Module.FinitePresentation.of_equiv eQ.symm,
    eQ.symm.toLinearMap ∘ₗ g₀ ∘ₗ eP.symm.toLinearMap, ?_, ?_⟩
  · intro N _ _
    show LinearMap.ker (LinearMap.rTensor N f) ≤
      LinearMap.ker (LinearMap.rTensor N (eQ.symm.toLinearMap ∘ₗ g₀ ∘ₗ eP.symm.toLinearMap))
    rw [LinearMap.ker_rTensor_equiv_comp,
      ← LinearMap.ker_rTensor_comp_equiv_le_iff eP f (g₀ ∘ₗ eP.symm.toLinearMap) N, hfold]
    exact hd₁' N
  · intro N _ _
    show LinearMap.ker
        (LinearMap.rTensor N (eQ.symm.toLinearMap ∘ₗ g₀ ∘ₗ eP.symm.toLinearMap)) ≤
      LinearMap.ker (LinearMap.rTensor N f)
    rw [LinearMap.ker_rTensor_equiv_comp,
      ← LinearMap.ker_rTensor_comp_equiv_le_iff eP (g₀ ∘ₗ eP.symm.toLinearMap) f N, hfold]
    exact hd₂' N

namespace Module

/-- **The second half of the proof of Stacks 05U7, in the universes of Stacks 059F.** Let
`(A, 𝔪)` be a local ring and let `(F i, u_{i i'})` be a directed system of free `A`-modules
indexed by a nonempty directed preorder, such that every transition map induces an injective map
`F i / 𝔪 F i → F i' / 𝔪 F i'`. Then any `A`-module linearly equivalent to the colimit of the
system is a Mittag-Leffler `A`-module, with the universe of the finitely presented source and the
universe of the test module arbitrary. -/
theorem isMittagLeffler_of_colimit_free_of_injective_mapQ_maximalIdeal {A : Type u} [CommRing A]
    [IsLocalRing A] {J : Type w} [Preorder J] [IsDirectedOrder J] [Nonempty J]
    {F : J ⥤ ModuleCat.{max u uM} A} {c : Cocone F}
    (hfree : ∀ i, Module.Free A (F.obj i))
    (hinj : ∀ {i j : J} (u : i ⟶ j), Function.Injective
      (Submodule.mapQ
        (maximalIdeal A • (⊤ : Submodule A (F.obj i)))
        (maximalIdeal A • (⊤ : Submodule A (F.obj j)))
        (F.map u).hom
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (F.map u).hom)))
    (hc : IsColimit c) {N : Type uM} [AddCommGroup N] [Module A N]
    (e : (c.pt : Type (max u uM)) ≃ₗ[A] N) :
    IsMittagLeffler.{u, uP, uM, max u uQ, uN} A N :=
  IsMittagLeffler.of_small_univ
    ((Module.isMittagLeffler_pt_of_free_of_injective_mapQ_maximalIdeal
      hfree hinj hc).of_linearEquiv e)

end Module

/-- Let `A → B` be an essentially finite type local homomorphism of local rings with `A`
henselian, and let `N` be a finite `B`-module which is flat over `A`. Then `N` is a
Mittag-Leffler `A`-module. -/
@[stacks 05U7 "the Mittag-Leffler conclusion"]
theorem isMittagLeffler_of_flat_finite_essFiniteType_local
    {A : Type u} {B : Type v} {N : Type uM} [CommRing A] [CommRing B]
    [IsLocalRing B] [HenselianLocalRing A]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hB : Algebra.EssFiniteType A B)
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [Module.Finite B N] [Module.Flat A N] :
    IsMittagLeffler.{u, uP, uM, max u uQ, uN} A N := by
  obtain ⟨I, _, _, F, c, hfree, hinj, ⟨hc⟩, ⟨eiso⟩⟩ :=
    exists_filteredColimit_free_with_injective_reduction (A := A) (B := B) (N := N) hB
  obtain ⟨α, _, _, _, G, _⟩ := IsFiltered.exists_directed I
  exact Module.isMittagLeffler_of_colimit_free_of_injective_mapQ_maximalIdeal
    (F := G ⋙ F) (c := c.whisker G) (fun i => hfree (G.obj i))
    (fun {_ _} u => hinj (G.map u))
    ((Functor.Final.isColimitWhiskerEquiv G c).symm hc)
    (eiso.toLinearEquiv ≪≫ₗ ULift.moduleEquiv)

/-- Let `A → B` be an essentially finite type local homomorphism of local rings with `A`
henselian, and let `N` be a finite `B`-module which is flat over `A`. If `N` is the colimit of a
directed system of free `A`-modules whose transition maps induce injective maps on the reductions
modulo `𝔪_A`, then `N` is a Mittag-Leffler `A`-module. -/
theorem isMittagLeffler_of_flat_finite_essentiallyFiniteType_local
    {A : Type u} {B : Type v} {N : Type uM} [CommRing A] [CommRing B]
    [IsLocalRing B] [HenselianLocalRing A]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (_hB : Algebra.EssFiniteType A B)
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [Module.Finite B N] [Module.Flat A N]
    (hcolim : ∃ (I : Type (max u uM)) (_ : Preorder I) (_ : IsDirectedOrder I) (_ : Nonempty I)
      (F : I ⥤ ModuleCat.{max u uM} A) (c : Cocone F),
      (∀ i, Module.Free A (F.obj i)) ∧
      (∀ {i j : I} (f : i ⟶ j), Function.Injective
        (Submodule.mapQ
          (maximalIdeal A • (⊤ : Submodule A (F.obj i)))
          (maximalIdeal A • (⊤ : Submodule A (F.obj j)))
          (F.map f).hom
          (Submodule.smul_top_le_comap_smul_top (maximalIdeal A)
            (F.map f).hom))) ∧
      Nonempty (IsColimit c) ∧
      Nonempty (c.pt ≅ ModuleCat.of A (ULift.{u} N))) :
    IsMittagLeffler.{u, uP, uM, max u uQ, uN} A N := by
  obtain ⟨I, _, _, _, F, c, hfree, hinj, ⟨hc⟩, ⟨eiso⟩⟩ := hcolim
  exact Module.isMittagLeffler_of_colimit_free_of_injective_mapQ_maximalIdeal
    hfree hinj hc (eiso.toLinearEquiv ≪≫ₗ ULift.moduleEquiv)

end
