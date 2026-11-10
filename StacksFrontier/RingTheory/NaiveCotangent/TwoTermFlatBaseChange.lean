module

public import StacksFrontier.RingTheory.NaiveCotangent.LocalizationBaseAndTarget

/-!
# Flat base change of a two-term complex and of a quasi-isomorphism

A two-term complex of `S`-modules `X₁ --d--> X₀` can be base changed along a ring map `S → T`,
giving `T ⊗_S X₁ --d ⊗ T--> T ⊗_S X₀`, and a chain map base changes with it.  When `T` is flat
over `S` this operation preserves quasi-isomorphy.

The degree-`0` half needs no flatness: the cokernel of a map is the cokernel of its base change,
because the tensor product is right exact.  The degree-`1` half is where flatness enters: it
says that `ker (d ⊗ T)` is the image of `T ⊗_S ker d`, so that the kernels base change as well,
and a bijection `ker d_A ≅ ker d_B` therefore base changes to a bijection.

## Main definitions

* `NaiveCotangent.TwoTerm.baseChange`: the base change `T ⊗_S C` of a two-term complex of
  `S`-modules along `S → T`.
* `NaiveCotangent.ChainMap.baseChange`: the base change of a chain map.

## Main results

* `NaiveCotangent.ker_baseChange_eq_range_baseChange_subtype`: for `T` flat over `S`, the kernel
  of `d ⊗ T` is the range of the base change of the inclusion `ker d ↪ X₁`.
* `NaiveCotangent.ker_baseChange_mkQ`: without any flatness, the kernel of the base change of the
  projection onto the cokernel of `d` is the range of `d ⊗ T`.
* `NaiveCotangent.IsQuasiIso.baseChange`: **flat base change preserves quasi-isomorphy** of
  chain maps of two-term complexes.

## Implementation notes

`LinearMap.baseChange` and `LinearMap.lTensor` are the same function
(`LinearMap.baseChange_eq_ltensor`) but are not the same term, and the exactness and flatness
API of Mathlib is stated for the second while the `T`-linearity needed here is carried only by
the first.  Every statement below is therefore phrased with `LinearMap.baseChange`, and the
bridge between the two is crossed once and for all in `NaiveCotangent.exact_baseChange`,
`NaiveCotangent.exact_baseChange_of_flat`, `NaiveCotangent.surjective_baseChange` and
`NaiveCotangent.injective_baseChange_of_flat`.

The compatibility squares are stated on elements rather than as identities of composites: the
middle term of a composite through `NaiveCotangent.H₁` is the coercion of a submodule which is
only definitionally the kernel of the differential, so `LinearMap.coe_comp` does not fire on it
and a proof by `TensorProduct.inductionOn` does not reduce the right-hand side.

## References

* [Stacks Project, Tag 00HD](https://stacks.math.columbia.edu/tag/00HD), flatness and exactness.
* [Stacks Project, Tag 00DE](https://stacks.math.columbia.edu/tag/00DE), right exactness of the
  tensor product.
-/

@[expose] public section

namespace NaiveCotangent

open TensorProduct

/-!
## Base change of linear maps: exactness, injectivity and bijectivity
-/

section Linear

variable {S : Type*} [CommRing S] (T : Type*) [CommRing T] [Algebra S T]
  {M N P : Type*} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  [AddCommGroup P] [Module S P]

/-- The base change of a surjective linear map is surjective. -/
theorem surjective_baseChange {g : N →ₗ[S] P} (hg : Function.Surjective g) :
    Function.Surjective (LinearMap.baseChange T g) :=
  LinearMap.lTensor_surjective T hg

/-- **Right exactness of the tensor product**, in the `LinearMap.baseChange` spelling: a piece
`M → N → P` which is exact and whose right-hand map is surjective stays exact after base
change. -/
theorem exact_baseChange {f : M →ₗ[S] N} {g : N →ₗ[S] P} (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Function.Exact (LinearMap.baseChange T f) (LinearMap.baseChange T g) :=
  lTensor_exact (f := f) (g := g) T hfg hg

/-- **Flat base change of an exact sequence is exact.** -/
theorem exact_baseChange_of_flat [Module.Flat S T] {f : M →ₗ[S] N} {g : N →ₗ[S] P}
    (hfg : Function.Exact f g) :
    Function.Exact (LinearMap.baseChange T f) (LinearMap.baseChange T g) :=
  Module.Flat.lTensor_exact (M := T) hfg

/-- **Flat base change preserves injectivity.** -/
theorem injective_baseChange_of_flat [Module.Flat S T] {f : M →ₗ[S] N}
    (hf : Function.Injective f) : Function.Injective (LinearMap.baseChange T f) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := T) f hf

/-- The base change of a bijective linear map is bijective: it is the base change of the linear
equivalence that the map underlies. -/
theorem bijective_baseChange {g : M →ₗ[S] N} (hg : Function.Bijective g) :
    Function.Bijective (LinearMap.baseChange T g) := by
  have he : LinearMap.baseChange T g =
      (LinearEquiv.baseChange S T M N (LinearEquiv.ofBijective g hg)).toLinearMap := rfl
  rw [he]
  exact (LinearEquiv.baseChange S T M N (LinearEquiv.ofBijective g hg)).bijective

end Linear

/-!
## Base change of a two-term complex and of a chain map
-/

section BaseChange

variable {S : Type*} [CommRing S]

/-- **The base change of a two-term complex** of `S`-modules along a ring map `S → T`: the
complex `T ⊗_S X₁ ⟶ T ⊗_S X₀` of `T`-modules with differential `d ⊗ T`. -/
noncomputable def TwoTerm.baseChange (C : TwoTerm S) (T : Type*) [CommRing T] [Algebra S T] :
    TwoTerm T where
  X₁ := T ⊗[S] C.X₁
  X₀ := T ⊗[S] C.X₀
  d := LinearMap.baseChange T C.d

variable {A B : TwoTerm S} (T : Type*) [CommRing T] [Algebra S T]

/-- **The base change of a chain map**: in each degree the base change of the component, the
commuting square base changing with them. -/
noncomputable def ChainMap.baseChange (f : ChainMap A B) :
    ChainMap (A.baseChange T) (B.baseChange T) where
  f₁ := LinearMap.baseChange T f.f₁
  f₀ := LinearMap.baseChange T f.f₀
  comm := by
    change LinearMap.baseChange T B.d ∘ₗ LinearMap.baseChange T f.f₁
      = LinearMap.baseChange T f.f₀ ∘ₗ LinearMap.baseChange T A.d
    refine LinearMap.ext fun z => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    induction z using TensorProduct.inductionOn with
    | tmul t x =>
      simp only [LinearMap.baseChange_tmul]
      exact congrArg (fun y => t ⊗ₜ[S] y) (chainMap_comm_apply f x)
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The degree-one component of the base change of a chain map is the base change of `f.f₁`. -/
@[simp] lemma ChainMap.baseChange_f₁ (f : ChainMap A B) :
    (f.baseChange T).f₁ = LinearMap.baseChange T f.f₁ := rfl

/-- The degree-zero component of the base change of a chain map is the base change of `f.f₀`. -/
@[simp] lemma ChainMap.baseChange_f₀ (f : ChainMap A B) :
    (f.baseChange T).f₀ = LinearMap.baseChange T f.f₀ := rfl

end BaseChange

/-!
## Flatness and the kernel of a base changed differential
-/

section Flat

variable {S : Type*} [CommRing S] {A B : TwoTerm S} (T : Type*) [CommRing T] [Algebra S T]

/-- **For a flat base change the kernel of the base changed differential is the base change of
the kernel**: the range of the base change of the inclusion `ker d ↪ X₁`.  This is exactness of
`T ⊗_S ker d ⟶ T ⊗_S X₁ ⟶ T ⊗_S X₀`, which is flatness of `T`. -/
theorem ker_baseChange_eq_range_baseChange_subtype [Module.Flat S T] (C : TwoTerm S) :
    LinearMap.ker (LinearMap.baseChange T C.d) =
      LinearMap.range (LinearMap.baseChange T (H₁ C).subtype) :=
  (exact_baseChange_of_flat T (LinearMap.exact_subtype_ker_map C.d)).linearMap_ker_eq

/-- **The cokernel of a differential base changes without any flatness**: the kernel of the base
change of the projection `X₀ ⟶ coker d` is the range of `d ⊗ T`.  This is right exactness of the
tensor product. -/
theorem ker_baseChange_mkQ (C : TwoTerm S) :
    LinearMap.ker (LinearMap.baseChange T (LinearMap.range C.d).mkQ) =
      LinearMap.range (LinearMap.baseChange T C.d) :=
  (exact_baseChange T (LinearMap.exact_map_mkQ_range C.d)
    (Submodule.mkQ_surjective _)).linearMap_ker_eq

/-- The base changed inclusion of the kernel intertwines the base changed degree-`1` component
of a chain map with the base change of the map it induces on `H₁ = ker d`. -/
theorem baseChange_f₁_baseChange_subtype (f : ChainMap A B) (w : T ⊗[S] (H₁ A)) :
    LinearMap.baseChange T f.f₁ (LinearMap.baseChange T (H₁ A).subtype w) =
      LinearMap.baseChange T (H₁ B).subtype (LinearMap.baseChange T f.onH₁ w) := by
  induction w using TensorProduct.inductionOn with
  | tmul t x => simp only [LinearMap.baseChange_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The base changed projections onto the cokernels intertwine the base changed degree-`0`
component of a chain map with the base change of the map it induces on `H₀ = coker d`. -/
theorem baseChange_mkQ_comp_baseChange_f₀ (f : ChainMap A B) :
    LinearMap.baseChange T (LinearMap.range B.d).mkQ ∘ₗ (f.baseChange T).f₀ =
      LinearMap.baseChange T f.onH₀ ∘ₗ LinearMap.baseChange T (LinearMap.range A.d).mkQ := by
  refine LinearMap.ext fun z => ?_
  change LinearMap.baseChange T (LinearMap.range B.d).mkQ (LinearMap.baseChange T f.f₀ z) =
    LinearMap.baseChange T f.onH₀ (LinearMap.baseChange T (LinearMap.range A.d).mkQ z)
  induction z using TensorProduct.inductionOn with
  | tmul t x =>
    simp only [LinearMap.baseChange_tmul, Submodule.mkQ_apply]
    exact congrArg (fun y => t ⊗ₜ[S] y) (onH₀_mk f x).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Flat base change preserves quasi-isomorphy.**  If `T` is flat over `S` and `f` is a
quasi-isomorphism of two-term complexes of `S`-modules, then `f ⊗ T` is a quasi-isomorphism of
two-term complexes of `T`-modules.

In degree `0` no flatness is needed: the cokernel of `d ⊗ T` is `T ⊗_S coker d` by right
exactness of the tensor product, and the base change of a bijection is a bijection.  In degree
`1` flatness identifies `ker (d ⊗ T)` with the range of `T ⊗_S ker d`, by
`ker_baseChange_eq_range_baseChange_subtype`, and the base change of the inclusion of the kernel
stays injective, which is what turns the bijection on `H₁` into a bijection between the kernels
of the base changed differentials. -/
theorem IsQuasiIso.baseChange [Module.Flat S T] {f : ChainMap A B} (hf : IsQuasiIso f) :
    IsQuasiIso (f.baseChange T) := by
  have hkerA := ker_baseChange_eq_range_baseChange_subtype T A
  have hkerB := ker_baseChange_eq_range_baseChange_subtype T B
  have hinjB : Function.Injective (LinearMap.baseChange T (H₁ B).subtype) :=
    injective_baseChange_of_flat T Subtype.coe_injective
  have hbijH₁ : Function.Bijective (LinearMap.baseChange T f.onH₁) :=
    bijective_baseChange T hf.1
  have hsq := baseChange_f₁_baseChange_subtype T f
  have hbij : Set.BijOn (LinearMap.baseChange T f.f₁)
      (LinearMap.range (LinearMap.baseChange T (H₁ A).subtype) : Set (T ⊗[S] A.X₁))
      (LinearMap.range (LinearMap.baseChange T (H₁ B).subtype) : Set (T ⊗[S] B.X₁)) := by
    refine ⟨fun z hz => ?_, fun z hz z' hz' hzz' => ?_, fun y hy => ?_⟩
    · obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp (SetLike.mem_coe.mp hz)
      exact SetLike.mem_coe.mpr
        (LinearMap.mem_range.mpr ⟨LinearMap.baseChange T f.onH₁ w, (hsq w).symm⟩)
    · obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp (SetLike.mem_coe.mp hz)
      obtain ⟨w', rfl⟩ := LinearMap.mem_range.mp (SetLike.mem_coe.mp hz')
      exact congrArg (LinearMap.baseChange T (H₁ A).subtype)
        (hbijH₁.injective (hinjB (((hsq w).symm.trans hzz').trans (hsq w'))))
    · obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp (SetLike.mem_coe.mp hy)
      obtain ⟨w, rfl⟩ := hbijH₁.surjective v
      exact ⟨LinearMap.baseChange T (H₁ A).subtype w,
        SetLike.mem_coe.mpr (LinearMap.mem_range.mpr ⟨w, rfl⟩), hsq w⟩
  refine ⟨bijective_onH₁_of_bijOn _ ?_, ?_⟩
  · change Set.BijOn (LinearMap.baseChange T f.f₁)
      (LinearMap.ker (LinearMap.baseChange T A.d) : Set (T ⊗[S] A.X₁))
      (LinearMap.ker (LinearMap.baseChange T B.d) : Set (T ⊗[S] B.X₁))
    rw [hkerA, hkerB]
    exact hbij
  · exact bijective_onH₀_of_surjective_square (T ⊗[S] H₀ A) (T ⊗[S] H₀ B) (f.baseChange T)
      (LinearMap.baseChange T (LinearMap.range A.d).mkQ)
      (LinearMap.baseChange T (LinearMap.range B.d).mkQ)
      (LinearMap.baseChange T f.onH₀)
      (surjective_baseChange T (Submodule.mkQ_surjective _))
      (ker_baseChange_mkQ T A) (ker_baseChange_mkQ T B)
      (baseChange_mkQ_comp_baseChange_f₀ T f) (bijective_baseChange T hf.2)

end Flat

end NaiveCotangent

end
