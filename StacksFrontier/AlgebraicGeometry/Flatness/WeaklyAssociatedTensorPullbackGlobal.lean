module

public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackFibre

/-!
# Bourbaki's formula for weakly associated points of a flat tensor product

Let `f : X ⟶ S` be a morphism of schemes locally of finite type, let `F` be a finite-type
quasi-coherent `𝒪_X`-module which is flat over `S`, and let `G` be a quasi-coherent
`𝒪_S`-module. Stacks tag 05IJ asserts

`WeakAss_X(F ⊗_{𝒪_X} f^*G) = ⋃_{s ∈ WeakAss_S(G)} Ass_{X_s}(F_s)`,

the union being taken inside `X` along the fibre inclusions `X_s ⟶ X`. The source proves it as
an immediate consequence of its pointwise form, Stacks tag 05IH, and that is how it is proved
here: the only extra content is the passage from the pointwise statement to the set equality,
which is `Stacks.Divisors.mem_iUnion_fiberι_associatedPoints_iff` below.

Two forms are given. The first is the full equality, taking the algebraic input
`Stacks.Divisors.LocalWeaklyAssociatedTensorFormula` of tag 05II as an argument. That input is
proved, as `Stacks.Divisors.weaklyAssociatedPrimesTensorFormula`, in
`StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackFormula`, which supplies
it and states tag 05IJ itself as `Stacks.Divisors.weaklyAssociatedPoints_tensorPullback_eq`.
The second is the inclusion `⊆` from the forward implication of tag 05IH of
`StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackFibre`, under that
implication's extra hypothesis of finitely generated maximal ideals on the local rings of `S`.

## Main results

* `Stacks.Divisors.mem_iUnion_fiberι_associatedPoints_iff`: a point lies in the union over a
  set `T` of points of `S` of the fibrewise associated points exactly when its image lies in
  `T` and the point it determines on its own fibre is associated there. A point of `X` lies
  over only one point of `S`, so only the fibre through it contributes.
* `Stacks.Divisors.iUnion_fiberι_associatedPoints_eq`: that union is the part of the relative
  assassin of tag 05AT lying over `T`.
* `Stacks.Divisors.weaklyAssociatedPoints_tensorPullback_eq_of_localFormula` and
  `Stacks.Divisors.weaklyAssociatedPoints_tensorPullback_eq_of_formula`: the full equality of
  tag 05IJ, from the local and from the global form of the algebraic input of tag 05II.
* `Stacks.Divisors.weaklyAssociatedPoints_tensorPullback_subset`: the inclusion `⊆` of tag
  05IJ, with no algebraic input, under the tag's own hypotheses together with finitely
  generated maximal ideals on `S`.

## Implementation notes

The union is written out as a union of images under the fibre inclusions `f.fiberι s`, indexed
by `WeakAss_S(G)`, rather than through `Stacks.Divisors.relativeAssassin`, because the source's
index set is `WeakAss_S(G)` and not all of `S`; this is the convention of
`AlgebraicGeometry.associatedPoints_tensor_pullback_eq_relativeAssassin`, the analogous
statement of tag 05DB for associated points. The comparison with the relative assassin is
`Stacks.Divisors.iUnion_fiberι_associatedPoints_eq`.

The inclusion `⊆` asks for flatness of `F` over `S` at every point, as the tag does, even
though only flatness at the point being tested is used; stating it pointwise would be the
forward implication of tag 05IH again rather than tag 05IJ.

## References

* [Stacks Project, Tag 05IJ](https://stacks.math.columbia.edu/tag/05IJ)
* [Stacks Project, Tag 05IH](https://stacks.math.columbia.edu/tag/05IH)
* [Stacks Project, Tag 05II](https://stacks.math.columbia.edu/tag/05II)
* [Stacks Project, Tag 05AT](https://stacks.math.columbia.edu/tag/05AT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Divisors

/-- A point `x` of `X` lies in the union, over the points `s` of a set `T ⊆ S`, of the images
of the associated points of the restriction of `F` to the fibre `X_s`, exactly when `f x` lies
in `T` and the point `x` determines on its own fibre is associated to the restriction of `F` to
that fibre.

Only the fibre through `x` can contribute, a point of `X` lying over exactly one point
of `S`. -/
theorem mem_iUnion_fiberι_associatedPoints_iff {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (T : Set S) (x : X) :
    x ∈ (⋃ s ∈ T, f.fiberι s ''
        associatedPoints ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ↔
      f x ∈ T ∧
        IsAssociatedPoint ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) (f.asFiber x) := by
  simp only [Set.mem_iUnion, Set.mem_image]
  refine ⟨?_, fun h => ⟨f x, h.1, f.asFiber x, h.2, f.fiberι_asFiber x⟩⟩
  rintro ⟨s, hs, y, hy, hxy⟩
  have hfs : f x = s := by
    rw [← hxy]
    exact Set.mem_preimage.mp ((f.range_fiberι s) ▸ Set.mem_range_self y)
  subst hfs
  have hyx : y = f.asFiber x :=
    (f.fiberι (f x)).isEmbedding.injective (hxy.trans (f.fiberι_asFiber x).symm)
  exact ⟨hs, hyx ▸ hy⟩

/-- The union, over the points of a set `T ⊆ S`, of the fibrewise associated points of `F` is
the part of the relative assassin `Ass_{X/S}(F)` of tag 05AT lying over `T`. -/
theorem iUnion_fiberι_associatedPoints_eq {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (T : Set S) :
    (⋃ s ∈ T, f.fiberι s ''
        associatedPoints ((Scheme.Modules.pullback (f.fiberι s)).obj F)) =
      relativeAssassin f F ∩ f ⁻¹' T := by
  ext x
  rw [mem_iUnion_fiberι_associatedPoints_iff, Set.mem_inter_iff,
    mem_relativeAssassin_iff_isAssociatedPoint_asFiber, Set.mem_preimage]
  exact and_comm

/-- Tag 05IJ from the local form of the algebraic formula of tag 05II, taken as an argument. Let
`f : X ⟶ S` be locally of finite type, let `F` be a finite-type quasi-coherent `𝒪_X`-module
flat over `S`, and let `G` be a quasi-coherent `𝒪_S`-module. The weakly associated points of
`F ⊗_{𝒪_X} f^*G` are the points of the fibres `X_s` over weakly associated points `s` of `G`
that are associated to the restriction of `F` to `X_s`.

This is the source's own proof: the pointwise statement is tag 05IH, available here as
`Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_localFormula`, and the passage
to the set equality is `Stacks.Divisors.mem_iUnion_fiberι_associatedPoints_iff`. The input is
proved as `Stacks.Divisors.weaklyAssociatedPrimesTensorFormula`, and the tag itself is
`Stacks.Divisors.weaklyAssociatedPoints_tensorPullback_eq`. -/
theorem weaklyAssociatedPoints_tensorPullback_eq_of_localFormula
    (hformula : LocalWeaklyAssociatedTensorFormula.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) (G : S.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] [G.IsQuasicoherent]
    (hF : IsFlatOver f.toLRSHom.toShHom F) :
    weaklyAssociatedPoints
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toLocallyRingedSpace.toRingedSpace)).presheaf,
              ((X.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj
          (((Scheme.Modules.pullback f).obj G)))) =
      ⋃ s ∈ weaklyAssociatedPoints G,
        f.fiberι s '' associatedPoints ((Scheme.Modules.pullback (f.fiberι s)).obj F) := by
  rw [iUnion_fiberι_associatedPoints_eq]
  exact Set.ext fun x =>
    (isWeaklyAssociatedPoint_tensorPullback_iff_of_localFormula hformula f F G x (hF x)).trans
      and_comm

/-- Tag 05IJ from the algebraic formula of tag 05II itself, taken as an argument. The formula is
`Stacks.Divisors.weaklyAssociatedPrimesTensorFormula`, and
`Stacks.Divisors.weaklyAssociatedPoints_tensorPullback_eq` applies this to it. -/
theorem weaklyAssociatedPoints_tensorPullback_eq_of_formula
    (hformula : WeaklyAssociatedPrimesTensorFormula.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) (G : S.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] [G.IsQuasicoherent]
    (hF : IsFlatOver f.toLRSHom.toShHom F) :
    weaklyAssociatedPoints
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toLocallyRingedSpace.toRingedSpace)).presheaf,
              ((X.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj
          (((Scheme.Modules.pullback f).obj G)))) =
      ⋃ s ∈ weaklyAssociatedPoints G,
        f.fiberι s '' associatedPoints ((Scheme.Modules.pullback (f.fiberι s)).obj F) :=
  weaklyAssociatedPoints_tensorPullback_eq_of_localFormula
    (localWeaklyAssociatedTensorFormula_of_formula hformula) f F G hF

/-- The inclusion `⊆` of tag 05IJ under finitely generated maximal ideals on `S`. Let `f : X ⟶ S` be locally of finite type,
let `F` be a quasi-coherent `𝒪_X`-module of finite type which is flat over `S`, and let `G` be
an `𝒪_S`-module. If the maximal ideals of the local rings of `S` are finitely generated, then
every weakly associated point of `F ⊗_{𝒪_X} f^*G` lies on the fibre over a weakly associated
point of `G` and is associated to the restriction of `F` to that fibre.

No algebraic input is assumed: this is the forward implication of tag 05IH,
`Stacks.Divisors.isWeaklyAssociatedPoint_and_mem_relativeAssassin_of_tensorPullback_of_finiteType`,
read as a statement about sets. Its one restriction is inherited: finite generation of the
maximal ideal at the image point, which replaces the prime avoidance the source runs after
making the stalk of `F` projective over the base by the étale-local structure theorem of
tag 05ID. The full tag, with no such hypothesis, is
`Stacks.Divisors.weaklyAssociatedPoints_tensorPullback_eq`. -/
theorem weaklyAssociatedPoints_tensorPullback_subset
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) (G : S.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hF : IsFlatOver f.toLRSHom.toShHom F)
    (hfg : ∀ s : S, (IsLocalRing.maximalIdeal (S.presheaf.stalk s)).FG) :
    weaklyAssociatedPoints
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toLocallyRingedSpace.toRingedSpace)).presheaf,
              ((X.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj
          (((Scheme.Modules.pullback f).obj G)))) ⊆
      ⋃ s ∈ weaklyAssociatedPoints G,
        f.fiberι s '' associatedPoints ((Scheme.Modules.pullback (f.fiberι s)).obj F) := by
  rw [iUnion_fiberι_associatedPoints_eq]
  exact fun x hx =>
    (isWeaklyAssociatedPoint_and_mem_relativeAssassin_of_tensorPullback_of_finiteType
      f F G x (hF x) (hfg (f x)) hx).symm

end Stacks.Divisors

end
