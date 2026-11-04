module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientComparisonPinned
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CompleteShift
public import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# The pinned comparison is invertible when the cone of the map it pins kills the complete objects

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals and `K ↦ K^∧` a derived completion
functor. `AdicQuotientComparisonPinned.lean` attaches to a derived-complete `L` and a map
`u : K ⟶ L` the unique `c = pinnedAdicComparison X I hL u : K^∧ ⟶ L` with
`(K ⟶ K^∧) ≫ c = u`, and reduces part (1) of [Stacks, Tag 0A0K] to `IsIso c`. This file gives a
criterion for `IsIso c` **in terms of the cone of `u` alone**:

`IsIso c` as soon as every map from the cone of `u` into a derived-complete object is zero,

i.e. as soon as the cone of `u` lies in `CategoryTheory.ObjectProperty.leftOrthogonal` of the
derived-complete objects — equivalently, by
`CategoryTheory.ObjectProperty.leftOrthogonal_iff_isZero_reflection` of
`Completion/ReflectionAlongTriangulatedFunctor.lean`, as soon as the derived completion of that
cone **vanishes**.

## Why this is the useful shape

The other criterion the library has for the same conclusion is
`Stacks.Algebraization.isIso_of_isDerivedLimitWithProjections_of_comp_proj` of
`Completion/AdicQuotientCanonicalComparison.lean`, which compares two derived-limit presentations
of one tower whose projections `c` matches. That comparison is **not** a consequence of matching
projections: the third square of the morphism of Milnor triangles is undetermined, with
indeterminacy `Hom(K^∧, (∏ₙ Tₙ)⟦-1⟧)`, and that theorem buys the missing input with two degree
bounds — `IsGE 0` on the terms of the tower and `IsLE 0` on the derived limit, with
`Stacks.Algebraization.hom_ext_of_comp_proj` consuming a third (`IsLE 0` on the source of the
completion unit). An arbitrary object of `D(𝒪)` satisfies none of them.

The criterion below carries **no degree bound at all**, and nothing about a tower: it asks a
vanishing of a single object. Only two things are used — the long exact sequences of the
distinguished triangle on `u`, and the fact that derived completeness is stable under the shift
(`AlgebraicGeometry.RingedSite.isDerivedComplete_shiftFunctor_obj` of `CompleteShift.lean`), which
is what makes the left orthogonal of the complete objects shift-stable and so lets the
surjectivity half read the triangle one step to the left.

## The converse holds

`CategoryTheory.ObjectProperty.leftOrthogonal_cone_unit` of
`Completion/ReflectionAlongTriangulatedFunctor.lean` says the cone of a reflection unit is left
orthogonal to the reflected class, at the generality of an arbitrary reflection. When `c` is
invertible, `u` is a completion unit for `K` up to that isomorphism, so its cone is left
orthogonal. Hence the hypothesis below is not merely sufficient but **equivalent** to `IsIso c`,
and therefore equivalent to part (1) of [Stacks, Tag 0A0K] at the `K` in question: it is a
restatement of the open input, not a strengthening of the hypotheses. That file is not imported
here — it imports `Mathlib` wholesale — so the equivalence is recorded rather than stated.

## What the Koszul route through this criterion does **not** buy, and why

On a chart the Čech completion of *any* object is `R lim (- ⊗^𝐋 (Kⁿ)^∨)` with no hypothesis
([Stacks, Tag 0A0E],
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem_completion`
of `KoszulPerfectDual.lean`), so the hypothesis below follows from the *per-term* vanishing
`cone(u) ⊗^𝐋 (Kⁿ)^∨ = 0` for every `n` — a statement about one map after tensoring with a perfect
complex, with no derived-limit comparison in it and no third square of a triangle morphism to
determine. **That per-term vanishing is nevertheless equivalent to the conclusion rather than
weaker than it**, so it is a third shape of the same open input and not a handle on it. The
cancellation is exact:

* write `u = η ≫ c` with `η` the completion unit and `c` the pinned comparison; the
  octahedral axiom gives a distinguished triangle `cone(η) ⟶ cone(u) ⟶ cone(c)`;
* `cone(η) ⊗^𝐋 (Kⁿ)^∨ = 0` for every `n`, and non-circularly so: `cone(η)` is `R𝑆heafHom` out of
  the non-extended part of the Čech complex, each of whose terms `𝒪_{f_S}` has some `f_i` acting
  invertibly, while `(Kⁿ)^∨` is an iterated cone of the `f_i^{n+1}` and so annihilates any object
  on which one of them is invertible;
* hence `cone(u) ⊗^𝐋 (Kⁿ)^∨ ≅ cone(c) ⊗^𝐋 (Kⁿ)^∨`, and the per-term vanishing is a statement
  about `cone(c)` alone;
* `cone(c)` is derived complete, `K^∧` and `L` being so and the derived-complete objects forming
  a triangulated subcategory
  (`AlgebraicGeometry.RingedSite.isTriangulated_isDerivedComplete` of
  `ClosureProductsAndFibres.lean`);
* and on a derived-complete object the hypothesis below has no slack whatsoever —
  `AlgebraicGeometry.RingedSite.leftOrthogonal_iff_isZero_of_isDerivedComplete`. By [Stacks,
  Tag 0A0E] again the per-term vanishing forces `Z^∧ = 0` for such a `Z`, hence `Z = 0` since its
  unit is invertible.

So the per-term Koszul vanishing says exactly `cone(c) = 0`, i.e. `IsIso c`. The only
non-circular input it admits — the vanishing of `cone(η) ⊗^𝐋 (Kⁿ)^∨` — cancels precisely the
summand of `cone(u)` whose orthogonality was free to begin with. **The failure of this route is
circularity, and not the indeterminacy that defeats the Milnor-square route**; the two are
independent, so neither diagnosis supersedes the other.

The Koszul pro-vanishing proved on the affine slice,
`Stacks.KoszulProZero.exists_koszulDualSystemOn_over_homologyMap_eq_zero_of_section` of
`KoszulAdicAffineSliceDerivedLimit.lean`, is not the missing input and would not supply it: it is
pro-vanishing of `AlgebraicGeometry.RingedSite.koszulDualSystemOn` in the Koszul index below the
top degree, and it is already spent, in
`AlgebraicGeometry.RingedSite.hasEventualInverses_koszulShiftedDualToTopSingle`. What this route
would need is a statement about `m ↦ (Kⁿ)^∨ ⊗^𝐋 𝒪/ℐᵐ⁺¹` at **fixed** `n` — a different tower, in
the adic index rather than the Koszul one, about which nothing in this library says anything.

## The adic tower at fixed Koszul index: the pro-isomorphism holds

That statement is **true**, so this is a live lead and not a fourth closed route. Write
`V = (Kⁿ)^∨` and `φ : (Functor.const ℕᵒᵖ).obj V ⟶ (m ↦ V ⊗^𝐋 𝒪/ℐᵐ⁺¹)` for the augmentation.
`NoetherianAdicCompletion.HasEventualInverses φ` holds, and the proof is the following.

By `NoetherianAdicCompletion.hasEventualInverses_const_of_triangles` of
`Homology/DerivedComplete/ConstantTowerEventualInverses.lean`, applied to the derived tensor of
`V` with `ℐᵐ⁺¹ ⟶ 𝒪 ⟶ 𝒪/ℐᵐ⁺¹`, the whole pro-isomorphism reduces to two maps being zero for
arbitrarily large `m`:

* `V ⊗^𝐋 ℐᵐ⁺¹ ⟶ V`, which is split-monicity of the reduction `V ⟶ V ⊗^𝐋 𝒪/ℐᵐ⁺¹`; and
* `V ⊗^𝐋 ℐᵐ⁺¹ ⟶ V ⊗^𝐋 ℐⁿ⁺¹`, the complementary component of the transition map.

The first of these is **not** the implausible statement it looks like. `(Kⁿ)^∨` is not the unit:
a split mono `𝒪 ⟶ 𝒪/ℐᵐ⁺¹` would indeed make `𝒪` a summand of `𝒪/ℐᵐ⁺¹` and is impossible
wherever `ℐᵐ⁺¹ ≠ 0`, but `(Kⁿ)^∨` is an iterated cone of the `f_i^{n+1}` and multiplication by
each `f_i^{n+1}` is **null-homotopic** on a Koszul complex
(`Koszul.koszulSeq_smul_nullHomotopic_and_span_le_annihilator`, in sheaf form
`Stacks.Sheaves.KoszulGlobalSections.koszulSmulNullHomotopic`). So the ideal `J` generated by the
`f_i^{n+1}` annihilates `𝟙_V` in `D(𝒪)`, every cohomology sheaf of `V` is `J`-torsion, and — since
`ℐ^{r(n+1)} ⊆ J` by pigeonhole on monomials — `ℐ`-power-torsion.

Both vanishings then follow from one standard fact. For any `X`, the cohomology of
`E := R𝑆heafHom(V, X)` is annihilated by `J`, because `g · α = (g · 𝟙_V) ≫ α = 0`; a bounded
complex with `ℐ`-power-torsion cohomology is derived `ℐ`-torsion, i.e. `RΓ_ℐ E ≅ E`, and
`RΓ_ℐ E = colim_m R𝑆heafHom(𝒪/ℐᵐ⁺¹, E)`. Hence

`colim_m Hom(𝒪/ℐᵐ⁺¹, E) ≅ H⁰(E)`, and therefore `colim_m Hom(ℐᵐ⁺¹, E) = 0`,

the second from the first and the long exact sequences of `ℐᵐ⁺¹ ⟶ 𝒪 ⟶ 𝒪/ℐᵐ⁺¹`, in which the
outer two comparison maps are then isomorphisms. By tensor-hom the first map above is
`ι^*(𝟙_V)` for `E = R𝑆heafHom(V, V)` and the second is the restriction of the canonical element
for `E = R𝑆heafHom(V, V ⊗^𝐋 ℐⁿ⁺¹)`; each lies in a group whose colimit over `m` is zero, so each
vanishes for `m` large.

Two sanity checks of the shape of this argument, both independent of the colimit fact. When the
`f_i^{n+1}` are a regular sequence `V` is a shift of `𝒪/J` alone, `ℐᵐ⁺¹ ⊆ J` makes
`H⁰(V ⊗^𝐋 𝒪/ℐᵐ⁺¹) = 𝒪/J` with the reduction the identity on it, and the truncation
`V ⊗^𝐋 𝒪/ℐᵐ⁺¹ ⟶ τ^{≥0}` is already a retraction. And for `r = 1` on `𝒪 = k[x]`, `ℐ = (x)`, the
reduction is `k[x]/x ⟶ (k[x]/x^{m+1} --x--> k[x]/x^{m+1})`, which splits because the obstruction
to splitting a two-term complex into its cohomologies lies in `Ext²` and `k[x]` has global
dimension one.

## What closing part (1) still needs

The derived-`ℐ`-torsion colimit identification `RΓ_ℐ E = colim_m R𝑆heafHom(𝒪/ℐᵐ⁺¹, E)`, for a
bounded `E` in `D(𝒪)` on a ringed site, is the one input the argument above uses and this library
does not have. It is the only gap: the reduction of part (1) to a chart statement is already
local with an arbitrary index type, in (namespace `AlgebraicGeometry`)
`RingedSite.isDerivedLimit_derivedCompletion_adicReductionTower_of_coversTop_slice` of
`AdicMilnorComparisonSliceRestriction.lean`, whose `hloc` hypothesis carries no finiteness — so
unlike the registered Koszul route of `Completion/KoszulAdicDerivedTensorLimit.lean`, this one
does not need `[CompactSpace Y]` and would reach the tag's own hypotheses. The other half of the
chart statement, invertibility of the Milnor comparison map at a pro-isomorphism, is proved but
privately and for the other Milnor functor, as `isIso_milnorMap_of_proIso` of
`Homology/DerivedComplete/NoetherianCompletePrincipalIdeal.lean`.

## Main results

* `AlgebraicGeometry.RingedSite.bijective_precomp_of_leftOrthogonal_cone` — precomposition with
  `u` is bijective on maps into every derived-complete object, given that the cone of `u` admits
  no nonzero map into a derived-complete object.
* `AlgebraicGeometry.RingedSite.leftOrthogonal_iff_isZero_of_isDerivedComplete` — the hypothesis
  is vacuous on a derived-complete object, where it says only that the object vanishes.
* `AlgebraicGeometry.RingedSite.isIso_pinnedAdicComparison_of_leftOrthogonal_cone` — hence the
  pinned comparison at `u` is invertible.

## References

* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)

* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
  {K L : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}

/-- **Precomposition with a map whose cone kills the derived-complete objects is bijective on
maps into a derived-complete object.** Let `K ⟶ L ⟶ Cn ⟶ K⟦1⟧` be distinguished and suppose
every map from `Cn` into a derived-complete object is zero. Then for every derived-complete `M`,

`Hom(L, M) ⟶ Hom(K, M)`, `g ↦ u ≫ g`,

is bijective.

Injectivity is exactness at `Hom(L, M)`: the difference of two maps agreeing on `K` factors
through `Cn`, and that factor is zero. Surjectivity is the same exactness one step to the left,
on the inverse rotation, whose first term is `Hom(Cn⟦-1⟧, M)`; that group vanishes because the
left orthogonal of a shift-stable class of objects is shift-stable
(`AlgebraicGeometry.RingedSite.isDerivedComplete_shiftFunctor_obj` supplies the
shift-stability). -/
theorem bijective_precomp_of_leftOrthogonal_cone (u : K ⟶ L)
    {Cn : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (v : L ⟶ Cn) (w : Cn ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk u v w ∈
      distTriang
        (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))))
    (hCn : ObjectProperty.leftOrthogonal (IsDerivedComplete.{u, u, u, u} X I) Cn)
    (M : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hM : IsDerivedComplete.{u, u, u, u} X I M) :
    Function.Bijective (fun g : L ⟶ M ↦ u ≫ g) := by
  refine ⟨fun g g' hgg ↦ ?_, fun a ↦ ?_⟩
  · obtain ⟨h, hh⟩ := (Triangle.mk u v w).yoneda_exact₂ hT (g - g') (by
      rw [Preadditive.comp_sub, sub_eq_zero]
      exact hgg)
    rw [hCn h hM, comp_zero] at hh
    exact sub_eq_zero.mp hh
  · obtain ⟨g, hg⟩ := (Triangle.mk u v w).invRotate.yoneda_exact₂ (inv_rot_of_distTriang _ hT) a
      (ObjectProperty.le_shift
        (ObjectProperty.leftOrthogonal (IsDerivedComplete.{u, u, u, u} X I)) (-1 : ℤ) _ hCn _ hM)
    exact ⟨g, hg.symm⟩

/-- **The hypothesis of this file is vacuous on a derived-complete object**: a derived-complete
object admits no nonzero map into a derived-complete object exactly when it is zero.

One direction is the hypothesis at the object itself, where it reads `𝟙 = 0`. This is what
measures how much slack the criterion has: none at all wherever the object it is applied to is
itself derived complete. See the module documentation for what that costs the route through
`n ↦ cone(u) ⊗^𝐋 (Kⁿ)^∨`. -/
theorem leftOrthogonal_iff_isZero_of_isDerivedComplete
    {Z : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (hZ : IsDerivedComplete.{u, u, u, u} X I Z) :
    ObjectProperty.leftOrthogonal (IsDerivedComplete.{u, u, u, u} X I) Z ↔ IsZero Z :=
  ⟨fun h ↦ (IsZero.iff_id_eq_zero Z).mpr (h (𝟙 Z) hZ), fun h _ g _ ↦ h.eq_of_src g 0⟩

variable [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).IsRightAdjoint]

/-- **The pinned comparison is invertible when the cone of the map it pins admits no nonzero map
into a derived-complete object.** With `L` derived complete and `K ⟶ L ⟶ Cn ⟶ K⟦1⟧`
distinguished, if every map from `Cn` into a derived-complete object is zero then
`AlgebraicGeometry.RingedSite.pinnedAdicComparison` at `u` is an isomorphism.

This is `AlgebraicGeometry.RingedSite.isIso_pinnedAdicComparison_of_bijective` — invertibility of
the pinned comparison is exactly `u` being a derived-completion unit — fed by
`AlgebraicGeometry.RingedSite.bijective_precomp_of_leftOrthogonal_cone`. No bound on the
amplitude of `K`, of `L` or of any tower appears, in contrast to the route through a uniqueness
statement for maps into a derived limit; see the module documentation. -/
theorem isIso_pinnedAdicComparison_of_leftOrthogonal_cone
    (hL : IsDerivedComplete.{u, u, u, u} X I L) (u : K ⟶ L)
    {Cn : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (v : L ⟶ Cn) (w : Cn ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk u v w ∈
      distTriang
        (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))))
    (hCn : ObjectProperty.leftOrthogonal (IsDerivedComplete.{u, u, u, u} X I) Cn) :
    IsIso (pinnedAdicComparison X I hL u) :=
  isIso_pinnedAdicComparison_of_bijective X I hL u fun M hM ↦
    bijective_precomp_of_leftOrthogonal_cone X I u v w hT hCn M hM

end AlgebraicGeometry.RingedSite

end
