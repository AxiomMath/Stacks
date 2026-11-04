module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FibreSumTerm
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Weighting
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksCore.Tactic.StacksAttribute

/-!
# The fibre integral of a section supported on a finite part

Let `f : X ⟶ Y` be locally quasi-finite and let `w` be a weighting of `f`. Let `V` be étale over
`Y`, let `U` be an open subscheme of `X_V = X ×_Y V` and let `s : U → ℤ` be a locally constant
function whose nonvanishing locus is contained in a closed subscheme `Z ⊆ U` finite over `V`.
Decomposing `s` into the open-and-closed level sets `U_n = {s = n}`, the *fibre integral* of `s`
is the function

`v ↦ ∑_{n ≠ 0} n · ∫_{U_n → V} w|_{U_n}`

on `V`, where `∫` is the separable-degree weighted fibre sum
`AlgebraicGeometry.separableDegreeWeightedFiberSum`. This file constructs that function and
proves it locally constant, which is what makes it a section of the constant sheaf `ℤ` over `V`.

This is step 4 of the proof of Stacks 0GKG, the construction out of which the trace map
`Tr_{f, w}` of that lemma is built.

## Main definitions

* `AlgebraicGeometry.levelOpens` — the open-and-closed locus where a locally constant
  integer-valued function on a scheme takes a given value.
* `AlgebraicGeometry.fibreIntegralTerm` — the summand `n · ∫_{U_n → V} w|_{U_n}` of the fibre
  integral.
* `AlgebraicGeometry.fibreIntegral` — the fibre integral itself, the sum of those summands over
  all `n`.

## Main results

* `AlgebraicGeometry.isFinite_of_isClosedImmersion_surjective` — finiteness over a base descends
  along a surjective closed immersion, for a locally quasi-finite morphism locally of finite
  type.
* `AlgebraicGeometry.isFinite_levelOpens_comp` — the level set `U_n` of a section supported on a
  part finite over `V` is finite over `V`, for `n ≠ 0`. This is what lets the defining property
  of a weighting be applied to it.
* `AlgebraicGeometry.isLocallyConstant_fibreIntegralTerm` — each summand of the fibre integral is
  locally constant on `V`.
* `AlgebraicGeometry.exists_isOpen_fibreIntegral_eq_finsetSum` — near any point of the base the
  defining sum has only finitely many nonzero summands, so it is a well-defined integer.
* `AlgebraicGeometry.isLocallyConstant_fibreIntegral` — **the fibre integral is locally
  constant**, that is, it is a section of the constant sheaf `ℤ` over `V`.
* `AlgebraicGeometry.fibreIntegral_eq_separableDegreeWeightedFiberSum` — **the fibre integral is
  the weighted fibre sum of `s · w`.** The level-set sum of the source is the single weighted
  fibre integral of the function `x ↦ s(x) · w(x)` over all of `U`. In particular it does not
  depend on the part `Z` the section was taken to be supported on, which is what the colimit
  over supports in Stacks 0F6M needs.
* `AlgebraicGeometry.fibreIntegral_add` — **the fibre integral is additive in the section**,
  which is the verification Stacks 0GKG omits and what makes it a homomorphism of abelian
  groups on sections.

## Implementation notes

**Why the level set is finite over the base.** The source asserts in one line that `U_n → V` is
finite for `n ≠ 0`. The reason is not that `U_n` is contained in `Z`: `U_n` carries the open
subscheme structure from `U`, which is a thickening of the closed subscheme it induces on `Z`.
What is true is that `U_n` is open *and closed* in `U`, so the part `T` of `Z` lying over it is
open and closed in `Z` and hence finite over `V`, and `T → U_n` is a surjective closed
immersion. Finiteness then descends: universal closedness along
`AlgebraicGeometry.UniversallyClosed.of_comp_surjective`, separatedness along
`AlgebraicGeometry.isSeparated_of_surjective_universallyClosed`, and finally
`AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`. That is
`AlgebraicGeometry.isFinite_of_isClosedImmersion_surjective`.

**Why the sum is locally finite.** Fix `v₀` in `V`. The fibre of `Z` over `v₀` is finite, so
`s` takes only finitely many values `S` on it. The locus of `Z` where `s` avoids `S` is closed,
and `Z → V` is a closed map, so its image misses an open neighbourhood `W` of `v₀`. For `v` in
`W` and `n ∉ S` the level set `U_n` has empty fibre over `v`, because a point of it would lie in
`Z` — this is where the hypothesis on the support of `s` is used — and would put `v` in that
image. So on `W` only the finitely many `n ∈ S` contribute, and the fibre integral is a finite
sum of locally constant functions there.

**The summand at `n = 0`.** It is `0 · ∫ = 0`, so the sum over all `n` agrees with the sum over
`n ≠ 0` of the source and no index set has to be carried. This is why
`AlgebraicGeometry.fibreIntegralTerm` is defined for every `n`, even though `U_0 → V` need not be
finite and the weighting says nothing about it.

**What is here and what is assembled elsewhere.** This is the fibre integral of *one* section
supported on *one* part finite over the base, which is the construction the source performs; the
morphism of presheaves `f_{p!}ℤ ⟶ ℤ` that Stacks 0GKG assembles out of it is
`AlgebraicGeometry.SmallEtale.integralTracePresheafMap` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.IntegralTracePresheaf`. Two things
beyond this file go into that assembly. First, the sections of the constant sheaf `ℤ` as an
object of `Sheaf (SmallEtale.topology B Y hY) AddCommGrpCat` have to be identified with locally
constant integer-valued functions *as abelian groups*: Stacks 03P5 in that form is
`AlgebraicGeometry.constantSheafIsoLocallyConstantMapsAb_smallEtale` of
`StacksFrontier.AlgebraicGeometry.Topologies.Etale.ConstantSheafAbelian`, the earlier
`AlgebraicGeometry.constantSheafIsoLocallyConstantMaps_smallEtale` being `Type`-valued through
`forget GrpCat` while `f_{p!}` of Stacks 0F6M is `AddCommGrpCat`-valued. Second, the fibre
integral has to be compatible with base change `V' ⟶ V`, which is the naturality of the presheaf
map: `AlgebraicGeometry.separableDegreeWeightedFiberSum_comp_of_isPullback` is that statement for
the weighted fibre sum but it assumes the *fibres* of the morphism are finite, and `U ⟶ V` here
has none — only the support of the section is finite over `V`, so the base-change statement is
proved one level set at a time, each of which *is* finite over `V`, in
`AlgebraicGeometry.fibreIntegral_comp_of_isPullback` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.FibreIntegralBaseChange`.

## References

* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0F3A](https://stacks.math.columbia.edu/tag/0F3A)
* [Stacks Project, Tag 0F39](https://stacks.math.columbia.edu/tag/0F39)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section Descent

/-- **Finiteness descends along a surjective closed immersion.** If `T → U` is a surjective
closed immersion and `T` is finite over `V`, then a locally quasi-finite `U → V` locally of
finite type is finite.

The point is that `U` may be a thickening of `T`, so `U → V` does not factor through `T`; what
survives is that `U → V` is universally closed and separated because `T → V` is, and a proper
locally quasi-finite morphism is finite. -/
public theorem isFinite_of_isClosedImmersion_surjective {T U V : Scheme.{u}}
    (q : T ⟶ U) (π : U ⟶ V) [IsClosedImmersion q] [Surjective q]
    [IsFinite (q ≫ π)] [LocallyOfFiniteType π] [LocallyQuasiFinite π] :
    IsFinite π := by
  have hsep : IsSeparated π := by
    let e : (Over.mk (q ≫ π) : Over V) ⟶ Over.mk π := Over.homMk q rfl
    have : Surjective e.left := show Surjective q from inferInstance
    have : UniversallyClosed e.left := show UniversallyClosed q from inferInstance
    have : IsSeparated (Over.mk (q ≫ π) : Over V).hom :=
      show IsSeparated (q ≫ π) from inferInstance
    exact isSeparated_of_surjective_universallyClosed e
  have : IsProper π := (isProper_iff π).2
    ⟨hsep, UniversallyClosed.of_comp_surjective q π, inferInstance⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite π

end Descent

section LevelOpens

variable {U : Scheme.{u}} {s : U → ℤ}

/-- The locus where a locally constant integer-valued function on a scheme takes the value `n`,
as an open subscheme. It is also closed, by `AlgebraicGeometry.isClosed_levelOpens`. -/
public def levelOpens (hs : IsLocallyConstant s) (n : ℤ) : U.Opens :=
  ⟨{x | s x = n}, hs.isOpen_fiber n⟩

/-- A point lies in `levelOpens hs n` if and only if `s` takes the value `n` there. -/
@[simp]
public theorem mem_levelOpens (hs : IsLocallyConstant s) (n : ℤ) (x : U) :
    x ∈ levelOpens hs n ↔ s x = n := Iff.rfl

/-- A level set of a locally constant function is closed as well as open. -/
public theorem isClosed_levelOpens (hs : IsLocallyConstant s) (n : ℤ) :
    IsClosed (levelOpens hs n : Set U) := hs.isClosed_fiber n

end LevelOpens

section Vanishing

/-- The weighted fibre sum vanishes at a point of the target which is not in the image. -/
public theorem separableDegreeWeightedFiberSum_eq_zero_of_notMem_range {U V : Scheme.{u}}
    (π : U ⟶ V) (w : U → ℤ) (v : V) (hv : ∀ u : U, π u ≠ v) :
    separableDegreeWeightedFiberSum π w v = 0 := by
  classical
  simp [separableDegreeWeightedFiberSum, hv, finsum_zero]

/-- The term of a weighted fibre sum is linear in the weight. -/
public theorem separableDegreeWeightedFiberTerm_const_mul {P U : Scheme.{u}} (g : P ⟶ U)
    (c : ℤ) (w : P → ℤ) (u : U) (x : P) :
    separableDegreeWeightedFiberTerm g (fun y => c * w y) u x =
      c * separableDegreeWeightedFiberTerm g w u x := by
  by_cases hx : g x = u
  · rw [separableDegreeWeightedFiberTerm_of_mem_fiber g _ hx,
      separableDegreeWeightedFiberTerm_of_mem_fiber g w hx, mul_assoc]
  · rw [separableDegreeWeightedFiberTerm_of_notMem_fiber g _ hx,
      separableDegreeWeightedFiberTerm_of_notMem_fiber g w hx, mul_zero]

/-- The term of a weighted fibre sum is additive in the weight. -/
public theorem separableDegreeWeightedFiberTerm_add {P U : Scheme.{u}} (g : P ⟶ U)
    (w₁ w₂ : P → ℤ) (u : U) (x : P) :
    separableDegreeWeightedFiberTerm g (fun y => w₁ y + w₂ y) u x =
      separableDegreeWeightedFiberTerm g w₁ u x +
        separableDegreeWeightedFiberTerm g w₂ u x := by
  by_cases hx : g x = u
  · rw [separableDegreeWeightedFiberTerm_of_mem_fiber g _ hx,
      separableDegreeWeightedFiberTerm_of_mem_fiber g w₁ hx,
      separableDegreeWeightedFiberTerm_of_mem_fiber g w₂ hx, add_mul]
  · rw [separableDegreeWeightedFiberTerm_of_notMem_fiber g _ hx,
      separableDegreeWeightedFiberTerm_of_notMem_fiber g w₁ hx,
      separableDegreeWeightedFiberTerm_of_notMem_fiber g w₂ hx, add_zero]

/-- Scaling the weight scales the weighted fibre sum. -/
public theorem separableDegreeWeightedFiberSum_const_mul {P U : Scheme.{u}} (g : P ⟶ U)
    (c : ℤ) (w : P → ℤ) (u : U) :
    separableDegreeWeightedFiberSum g (fun y => c * w y) u =
      c * separableDegreeWeightedFiberSum g w u := by
  rw [separableDegreeWeightedFiberSum_eq_finsum_term,
    separableDegreeWeightedFiberSum_eq_finsum_term,
    mul_finsum _ c]
  exact finsum_congr fun x => separableDegreeWeightedFiberTerm_const_mul g c w u x

/-- The weighted fibre sum is additive in the weight, when both sums are finite ones. -/
public theorem separableDegreeWeightedFiberSum_add {P U : Scheme.{u}} (g : P ⟶ U)
    (w₁ w₂ : P → ℤ) (u : U)
    (hfin₁ : Function.HasFiniteSupport (separableDegreeWeightedFiberTerm g w₁ u))
    (hfin₂ : Function.HasFiniteSupport (separableDegreeWeightedFiberTerm g w₂ u)) :
    separableDegreeWeightedFiberSum g (fun y => w₁ y + w₂ y) u =
      separableDegreeWeightedFiberSum g w₁ u + separableDegreeWeightedFiberSum g w₂ u := by
  rw [separableDegreeWeightedFiberSum_eq_finsum_term,
    separableDegreeWeightedFiberSum_eq_finsum_term,
    separableDegreeWeightedFiberSum_eq_finsum_term, ← finsum_add_distrib hfin₁ hfin₂]
  exact finsum_congr fun x => separableDegreeWeightedFiberTerm_add g w₁ w₂ u x

end Vanishing

section FibreIntegral

variable {X Y U V : Scheme.{u}}

/-- The summand of the fibre integral indexed by `n`: the weighted fibre integral of `w` over
the level set `U_n = {s = n}`, multiplied by `n`. -/
public def fibreIntegralTerm (h : U ⟶ X) (π : U ⟶ V) (w : X → ℤ) {s : U → ℤ}
    (hs : IsLocallyConstant s) (n : ℤ) (v : V) : ℤ :=
  n * separableDegreeWeightedFiberSum ((levelOpens hs n).ι ≫ π)
    (w ∘ ⇑((levelOpens hs n).ι ≫ h)) v

/-- **The fibre integral.** A locally constant `s : U → ℤ` supported on a part of `U` finite over
`V` is sent to the sum over `n` of `n` times the weighted fibre integral of `w` over the level
set `{s = n}`. The summand at `n = 0` vanishes, so this is the sum over `n ≠ 0` of the source. -/
public def fibreIntegral (h : U ⟶ X) (π : U ⟶ V) (w : X → ℤ) {s : U → ℤ}
    (hs : IsLocallyConstant s) : V → ℤ :=
  fun v => ∑ᶠ n : ℤ, fibreIntegralTerm h π w hs n v

/-- The summand of the fibre integral at `n = 0` is zero. -/
@[simp]
public theorem fibreIntegralTerm_zero (h : U ⟶ X) (π : U ⟶ V) (w : X → ℤ) {s : U → ℤ}
    (hs : IsLocallyConstant s) (v : V) : fibreIntegralTerm h π w hs 0 v = 0 := by
  simp [fibreIntegralTerm]

variable {f : X ⟶ Y} {w : X → ℤ} {Z : Scheme.{u}}

/-- **The level sets of a section supported on a finite part are finite over the base.** For
`n ≠ 0` the level set `U_n = {s = n}` lies inside `Z`, is open and closed in `U`, and is
therefore finite over `V`. This is the hypothesis the defining property of a weighting needs. -/
public theorem isFinite_levelOpens_comp {π : U ⟶ V} [LocallyOfFiniteType π]
    [LocallyQuasiFinite π] {s : U → ℤ} (hs : IsLocallyConstant s) (i : Z ⟶ U)
    [IsClosedImmersion i] (hZ : IsFinite (i ≫ π))
    (hsupp : ∀ x : U, s x ≠ 0 → x ∈ Set.range i.base) {n : ℤ} (hn : n ≠ 0) :
    IsFinite ((levelOpens hs n).ι ≫ π) := by
  have hZ' : IsFinite (i ≫ π) := hZ
  -- the part of `Z` lying over the level set, an open and closed subscheme of `Z`
  have hTι : IsClosedImmersion (i ⁻¹ᵁ levelOpens hs n : Z.Opens).ι :=
    IsClosedImmersion.of_isPreimmersion _ (by
      rw [Scheme.Opens.range_ι]
      exact (isClosed_levelOpens hs n).preimage i.continuous)
  have hcomp : (i ∣_ levelOpens hs n) ≫ ((levelOpens hs n).ι ≫ π) =
      (i ⁻¹ᵁ levelOpens hs n : Z.Opens).ι ≫ (i ≫ π) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  have hqsurj : Surjective (i ∣_ levelOpens hs n) := by
    refine ⟨fun y => ?_⟩
    have hy2 : s ((levelOpens hs n).ι y) = n := y.2
    obtain ⟨z, hz⟩ := hsupp _ (hy2 ▸ hn)
    have hzT : z ∈ Set.range (i ⁻¹ᵁ levelOpens hs n : Z.Opens).ι.base := by
      rw [Scheme.Opens.range_ι]
      show i.base z ∈ (levelOpens hs n : Set U)
      rw [hz]
      exact hy2
    obtain ⟨z', hz'⟩ := hzT
    refine ⟨z', ?_⟩
    have hmr : ((i ∣_ levelOpens hs n) ≫ (levelOpens hs n).ι).base z' =
        ((i ⁻¹ᵁ levelOpens hs n : Z.Opens).ι ≫ i).base z' := by
      rw [morphismRestrict_ι]
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at hmr
    refine (levelOpens hs n).ι.isOpenEmbedding.injective ?_
    rw [hmr, hz', hz]
  have hfin : IsFinite ((i ∣_ levelOpens hs n) ≫ ((levelOpens hs n).ι ≫ π)) := by
    rw [hcomp]
    exact inferInstance
  exact isFinite_of_isClosedImmersion_surjective (i ∣_ levelOpens hs n) ((levelOpens hs n).ι ≫ π)

/-- **Each summand of the fibre integral is locally constant.** For `n ≠ 0` this is the defining
property of a weighting, applied to the level set `U_n`, which is an open subscheme of `X_V`
finite over `V`. For `n = 0` the summand is zero. -/
public theorem isLocallyConstant_fibreIntegralTerm (hw : IsWeighting f w)
    {h : U ⟶ X} {π : U ⟶ V} {g : V ⟶ Y} (comm : h ≫ f = π ≫ g) (hg : Etale g)
    (hU : IsOpenImmersion (pullback.lift h π comm))
    [LocallyOfFiniteType π] [LocallyQuasiFinite π] {s : U → ℤ} (hs : IsLocallyConstant s)
    (i : Z ⟶ U) [IsClosedImmersion i] (hZ : IsFinite (i ≫ π))
    (hsupp : ∀ x : U, s x ≠ 0 → x ∈ Set.range i.base) (n : ℤ) :
    IsLocallyConstant (fibreIntegralTerm h π w hs n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [show fibreIntegralTerm h π w hs 0 = fun _ => 0 from
      funext (fibreIntegralTerm_zero h π w hs)]
    exact IsLocallyConstant.const 0
  have hcomm : ((levelOpens hs n).ι ≫ h) ≫ f = ((levelOpens hs n).ι ≫ π) ≫ g := by
    rw [Category.assoc, Category.assoc, comm]
  have hopen : IsOpenImmersion
      (pullback.lift ((levelOpens hs n).ι ≫ h) ((levelOpens hs n).ι ≫ π) hcomm) := by
    have heq : pullback.lift ((levelOpens hs n).ι ≫ h) ((levelOpens hs n).ι ≫ π) hcomm =
        (levelOpens hs n).ι ≫ pullback.lift h π comm := by
      refine pullback.hom_ext ?_ ?_ <;>
        simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]
    rw [heq]
    have : IsOpenImmersion (pullback.lift h π comm) := hU
    infer_instance
  exact (hw ((levelOpens hs n).ι ≫ h) ((levelOpens hs n).ι ≫ π) g hcomm hg hopen
    (isFinite_levelOpens_comp hs i hZ hsupp hn)).comp fun z => n * z

/-- A point of `U` over `v` where `s` is nonzero comes from a point of `Z` over `v`. -/
private theorem mem_image_fibre_of_ne_zero {π : U ⟶ V} {s : U → ℤ} (i : Z ⟶ U)
    (hsupp : ∀ x : U, s x ≠ 0 → x ∈ Set.range i.base) {x : U} {v : V} (hx : π.base x = v)
    (hsx : s x ≠ 0) : x ∈ i.base '' ((i ≫ π).base ⁻¹' {v}) := by
  obtain ⟨z, hz⟩ := hsupp x hsx
  exact ⟨z, (hz ▸ hx : π.base (i.base z) = v), hz⟩

/-- The fibre integral over `v` is the sum over a finite set `S` if every level set indexed
outside `S` has no nonvanishing point over `v`. -/
private theorem fibreIntegral_eq_sum_of_forall {h : U ⟶ X} {π : U ⟶ V} {s : U → ℤ}
    (hs : IsLocallyConstant s) (S : Finset ℤ) (v : V)
    (hv : ∀ n ∉ S, ∀ x : U, s x = n → s x ≠ 0 → π.base x ≠ v) :
    fibreIntegral h π w hs v = ∑ n ∈ S, fibreIntegralTerm h π w hs n v := by
  refine finsum_eq_sum_of_support_subset _ fun n hn => ?_
  by_contra hnS
  refine hn ?_
  rcases eq_or_ne n 0 with rfl | hn0
  · exact fibreIntegralTerm_zero h π w hs v
  refine mul_eq_zero_of_right _ (separableDegreeWeightedFiberSum_eq_zero_of_notMem_range _ _ _
    fun y hy => ?_)
  have hy' : s ((levelOpens hs n).ι y) = n := y.2
  exact hv n (by simpa using hnS) _ hy' (by rw [hy']; exact hn0) hy

/-- The fibre integral is, near any point of the base, the finite sum of the summands indexed by
the values that the section takes on the fibre there. This is the local finiteness that makes
the defining sum meaningful. -/
public theorem exists_isOpen_fibreIntegral_eq_finsetSum {h : U ⟶ X} {π : U ⟶ V}
    [LocallyOfFiniteType π] [LocallyQuasiFinite π] {s : U → ℤ} (hs : IsLocallyConstant s)
    (i : Z ⟶ U) [IsClosedImmersion i] (hZ : IsFinite (i ≫ π))
    (hsupp : ∀ x : U, s x ≠ 0 → x ∈ Set.range i.base) (v₀ : V) :
    ∃ (W : Set V) (S : Finset ℤ), IsOpen W ∧ v₀ ∈ W ∧
      ∀ v ∈ W, fibreIntegral h π w hs v = ∑ n ∈ S, fibreIntegralTerm h π w hs n v := by
  classical
  have hZ' : IsFinite (i ≫ π) := hZ
  set t : Z → ℤ := fun z => s (i.base z)
  have htlc : IsLocallyConstant t := hs.comp_continuous i.continuous
  set S : Set ℤ := t '' (((i ≫ π).base) ⁻¹' {v₀})
  have hSfin : S.Finite := ((i ≫ π).finite_preimage_singleton v₀).image t
  set Zbad : Set Z := (t ⁻¹' S)ᶜ with hZbad
  have hZbadClosed : IsClosed Zbad := (htlc S).isClosed_compl
  have himg : IsClosed ((i ≫ π).base '' Zbad) :=
    (Scheme.Hom.isClosedMap (i ≫ π)) Zbad hZbadClosed
  refine ⟨((i ≫ π).base '' Zbad)ᶜ, hSfin.toFinset, himg.isOpen_compl, ?_, ?_⟩
  · rintro ⟨z, hz, hzv⟩
    exact hz ⟨z, hzv, rfl⟩
  · intro v hv
    refine fibreIntegral_eq_sum_of_forall hs _ v fun n hnS x hxn hsx hπx => ?_
    obtain ⟨z, hzv, hz⟩ := mem_image_fibre_of_ne_zero i hsupp hπx hsx
    refine hv ⟨z, ?_, hzv⟩
    have htz : t z = n := by
      show s (i.base z) = n
      rw [hz]
      exact hxn
    show t z ∉ S
    rw [htz]
    exact fun hmem => hnS (hSfin.mem_toFinset.2 hmem)

/-- The terms of the weighted fibre sum of `s · w` have finite support, because `s` vanishes
off a part finite over the base. -/
public theorem hasFiniteSupport_term_smul_weight {h : U ⟶ X} {π : U ⟶ V} {s : U → ℤ}
    (i : Z ⟶ U) (hZ : IsFinite (i ≫ π))
    (hsupp : ∀ x : U, s x ≠ 0 → x ∈ Set.range i.base) (v : V) :
    Function.HasFiniteSupport
      (separableDegreeWeightedFiberTerm π (fun x => s x * w (h x)) v) := by
  have hZ' : IsFinite (i ≫ π) := hZ
  refine Set.Finite.subset (((i ≫ π).finite_preimage_singleton v).image i.base) fun x hx => ?_
  have hterm : separableDegreeWeightedFiberTerm π (fun x => s x * w (h x)) v x ≠ 0 := hx
  have hπx : π.base x = v := by
    by_contra hne
    exact hterm (separableDegreeWeightedFiberTerm_of_notMem_fiber π _ hne)
  have hsx : s x ≠ 0 := by
    intro h0
    refine hterm ?_
    rw [separableDegreeWeightedFiberTerm_of_mem_fiber π _ hπx, h0, zero_mul, zero_mul]
  exact mem_image_fibre_of_ne_zero i hsupp hπx hsx

/-- **The fibre integral is the weighted fibre sum of `s · w`.** Summing `n` times the integral
of `w` over the level set `{s = n}` over all `n` is the same as integrating the single function
`x ↦ s x · w(x)` over the whole of `U`: both count each point of the fibre once, with the
weight `s(x) · w(x)` and the multiplicity its separable residue degree.

This is the formula the source's level-set description computes, and it is what makes the
fibre integral additive in `s`. -/
public theorem fibreIntegral_eq_separableDegreeWeightedFiberSum {h : U ⟶ X} {π : U ⟶ V}
    [LocallyOfFiniteType π] [LocallyQuasiFinite π] {s : U → ℤ} (hs : IsLocallyConstant s)
    (i : Z ⟶ U) [IsClosedImmersion i] (hZ : IsFinite (i ≫ π))
    (hsupp : ∀ x : U, s x ≠ 0 → x ∈ Set.range i.base) :
    fibreIntegral h π w hs = separableDegreeWeightedFiberSum π (fun x => s x * w (h x)) := by
  classical
  have hZ' : IsFinite (i ≫ π) := hZ
  funext v
  -- the finite set of nonzero values that `s` takes on the fibre over `v`
  have hFfin : (i.base '' (((i ≫ π).base) ⁻¹' {v})).Finite :=
    ((i ≫ π).finite_preimage_singleton v).image i.base
  set N : Finset ℤ := (hFfin.toFinset.image s).erase 0 with hNdef
  have hmemN : ∀ x : U, π.base x = v → s x ≠ 0 → s x ∈ N := by
    intro x hx hsx
    exact Finset.mem_erase.2 ⟨hsx, Finset.mem_image.2 ⟨x,
      hFfin.mem_toFinset.2 (mem_image_fibre_of_ne_zero i hsupp hx hsx), rfl⟩⟩
  -- the level sets indexed by `N`, together with everything they miss
  have hRopen : IsOpen ((⋃ n ∈ (N : Set ℤ), (levelOpens hs n : Set U))ᶜ) :=
    (N.finite_toSet.isClosed_biUnion fun n _ => isClosed_levelOpens hs n).isOpen_compl
  have hRmem : ∀ x : U,
      x ∈ ((⋃ n ∈ (N : Set ℤ), (levelOpens hs n : Set U))ᶜ) ↔ s x ∉ N := by
    intro x
    constructor
    · intro hx hsx
      exact hx (Set.mem_biUnion hsx (show s x = s x from rfl))
    · intro hx hmem
      obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.1 hmem
      exact hx ((show s x = n from hxn) ▸ hn)
  obtain ⟨D, hDnone, hDsome⟩ :
      ∃ D : Option {n : ℤ // n ∈ N} → U.Opens,
        D none = ⟨(⋃ n ∈ (N : Set ℤ), (levelOpens hs n : Set U))ᶜ, hRopen⟩ ∧
        ∀ n : {n : ℤ // n ∈ N}, D (some n) = levelOpens hs n.1 :=
    ⟨fun o => o.elim ⟨_, hRopen⟩ fun n => levelOpens hs n.1, rfl, fun _ => rfl⟩
  have hdisj : ∀ a b : Option {n : ℤ // n ∈ N}, a ≠ b →
      Disjoint (D a : Set U) (D b : Set U) := by
    rintro (_ | n) (_ | m) hab <;> rw [Set.disjoint_left] <;> intro x hxa hxb
    · exact hab rfl
    · rw [hDnone] at hxa
      rw [hDsome] at hxb
      exact (hRmem x).1 hxa ((show s x = m.1 from hxb) ▸ m.2)
    · rw [hDsome] at hxa
      rw [hDnone] at hxb
      exact (hRmem x).1 hxb ((show s x = n.1 from hxa) ▸ n.2)
    · rw [hDsome] at hxa hxb
      exact hab (congrArg some
        (Subtype.ext ((show s x = n.1 from hxa).symm.trans (show s x = m.1 from hxb))))
  have hcover : ∀ x : U, ∃ o, x ∈ D o := by
    intro x
    by_cases hx : s x ∈ N
    · exact ⟨some ⟨s x, hx⟩, by rw [hDsome]; exact (rfl : s x = s x)⟩
    · exact ⟨none, by rw [hDnone]; exact (hRmem x).2 hx⟩
  have hsupport : ∀ u : V, Function.HasFiniteSupport
      (separableDegreeWeightedFiberTerm π (fun x => s x * w (h x)) u) :=
    fun u => hasFiniteSupport_term_smul_weight (w := w) i hZ hsupp u
  have hsplit := separableDegreeWeightedFiberSum_eq_sum_opens_of_hasFiniteSupport
    π (fun x => s x * w (h x)) D hdisj hcover hsupport
  have hsplitv : separableDegreeWeightedFiberSum π (fun x => s x * w (h x)) v =
      ∑ o : Option {n : ℤ // n ∈ N},
        separableDegreeWeightedFiberSum ((D o).ι ≫ π)
          ((fun x => s x * w (h x)) ∘ ⇑(D o).ι) v := by
    rw [hsplit, Finset.sum_apply]
  -- the contribution of everything the chosen level sets miss is zero over `v`
  have hnone : separableDegreeWeightedFiberSum ((D none).ι ≫ π)
      ((fun x => s x * w (h x)) ∘ ⇑(D none).ι) v = 0 := by
    rw [← finsum_mem_separableDegreeWeightedFiberTerm π (D none) (fun x => s x * w (h x)) v]
    refine finsum_mem_of_eqOn_zero fun x hx => ?_
    show separableDegreeWeightedFiberTerm π (fun x => s x * w (h x)) v x = 0
    by_cases hπx : π.base x = v
    · have hsx : s x = 0 := by
        by_contra hsx0
        rw [hDnone] at hx
        exact (hRmem x).1 hx (hmemN x hπx hsx0)
      rw [separableDegreeWeightedFiberTerm_of_mem_fiber π _ hπx, hsx, zero_mul, zero_mul]
    · exact separableDegreeWeightedFiberTerm_of_notMem_fiber π _ hπx
  have hsum_fin := fibreIntegral_eq_sum_of_forall (h := h) (w := w) hs N v
    fun n hn x hxn hsx hπx => hn (hxn ▸ hmemN x hπx hsx)
  rw [hsplitv, Fintype.sum_option, hnone, zero_add,
    hsum_fin, ← Finset.sum_coe_sort N (fun n => fibreIntegralTerm h π w hs n v)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hDsome a]
  have hfun : (fun x => s x * w (h x)) ∘ ⇑(levelOpens hs a.1).ι =
      fun y => a.1 * (w ∘ ⇑((levelOpens hs a.1).ι ≫ h)) y := by
    funext y
    have hy : s ((levelOpens hs a.1).ι y) = a.1 := y.2
    simp only [Function.comp_apply, Scheme.Hom.comp_apply, hy]
  rw [hfun, separableDegreeWeightedFiberSum_const_mul]
  rfl

/-- **The fibre integral is additive in the section.** -/
public theorem fibreIntegral_add {h : U ⟶ X} {π : U ⟶ V}
    [LocallyOfFiniteType π] [LocallyQuasiFinite π] {s₁ s₂ : U → ℤ}
    (hs₁ : IsLocallyConstant s₁) (hs₂ : IsLocallyConstant s₂)
    (hs : IsLocallyConstant (fun x => s₁ x + s₂ x))
    (i : Z ⟶ U) [IsClosedImmersion i] (hZ : IsFinite (i ≫ π))
    (hsupp₁ : ∀ x : U, s₁ x ≠ 0 → x ∈ Set.range i.base)
    (hsupp₂ : ∀ x : U, s₂ x ≠ 0 → x ∈ Set.range i.base) :
    fibreIntegral h π w hs =
      fun v => fibreIntegral h π w hs₁ v + fibreIntegral h π w hs₂ v := by
  have hsupp : ∀ x : U, s₁ x + s₂ x ≠ 0 → x ∈ Set.range i.base := by
    intro x hx
    rcases eq_or_ne (s₁ x) 0 with h1 | h1
    · exact hsupp₂ x fun h2 => hx (by rw [h1, h2, add_zero])
    · exact hsupp₁ x h1
  rw [fibreIntegral_eq_separableDegreeWeightedFiberSum hs i hZ hsupp,
    fibreIntegral_eq_separableDegreeWeightedFiberSum hs₁ i hZ hsupp₁,
    fibreIntegral_eq_separableDegreeWeightedFiberSum hs₂ i hZ hsupp₂]
  funext v
  simp_rw [add_mul]
  exact separableDegreeWeightedFiberSum_add π _ _ v
    (hasFiniteSupport_term_smul_weight (w := w) i hZ hsupp₁ v)
    (hasFiniteSupport_term_smul_weight (w := w) i hZ hsupp₂ v)

/-- A finite sum of locally constant functions is locally constant. -/
private theorem isLocallyConstant_finsetSum {α : Type*} [TopologicalSpace α] (S : Finset ℤ)
    (F : ℤ → α → ℤ) (hF : ∀ n, IsLocallyConstant (F n)) :
    IsLocallyConstant (fun a => ∑ n ∈ S, F n a) := by
  classical
  induction S using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsLocallyConstant.const 0
  | insert n S hn ih =>
    have heq : (fun a => ∑ m ∈ insert n S, F m a) = fun a => F n a + ∑ m ∈ S, F m a := by
      funext a
      rw [Finset.sum_insert hn]
    rw [heq]
    exact (hF n).comp₂ ih (· + ·)

/-- **The fibre integral is locally constant.** This is the construction of Stacks 0GKG at the
level of a single section supported on a part of `X_V` finite over `V`: the sum defining it is
locally finite, and its value is a locally constant function on `V`, that is, a section of the
constant sheaf `ℤ` over `V`. -/
public theorem isLocallyConstant_fibreIntegral (hw : IsWeighting f w)
    {h : U ⟶ X} {π : U ⟶ V} {g : V ⟶ Y} (comm : h ≫ f = π ≫ g) (hg : Etale g)
    (hU : IsOpenImmersion (pullback.lift h π comm))
    [LocallyOfFiniteType π] [LocallyQuasiFinite π] {s : U → ℤ} (hs : IsLocallyConstant s)
    (i : Z ⟶ U) [IsClosedImmersion i] (hZ : IsFinite (i ≫ π))
    (hsupp : ∀ x : U, s x ≠ 0 → x ∈ Set.range i.base) :
    IsLocallyConstant (fibreIntegral h π w hs) := by
  classical
  rw [IsLocallyConstant.iff_exists_open]
  intro v₀
  obtain ⟨W, S, hWopen, hv₀, hWeq⟩ :=
    exists_isOpen_fibreIntegral_eq_finsetSum (w := w) hs i hZ hsupp v₀
  have hsum : IsLocallyConstant (fun v => ∑ n ∈ S, fibreIntegralTerm h π w hs n v) :=
    isLocallyConstant_finsetSum S _ fun n =>
      isLocallyConstant_fibreIntegralTerm hw comm hg hU hs i hZ hsupp n
  obtain ⟨W', hW'open, hv₀', hW'const⟩ := (IsLocallyConstant.iff_exists_open _).1 hsum v₀
  refine ⟨W ∩ W', hWopen.inter hW'open, ⟨hv₀, hv₀'⟩, fun v hv => ?_⟩
  rw [hWeq v hv.1, hW'const v hv.2, ← hWeq v₀ hv₀]

end FibreIntegral

end AlgebraicGeometry

end
