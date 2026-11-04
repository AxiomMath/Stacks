module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatQuotientPullbackMono
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.Basic

/-!
# Base change of a flat family of quotients of `𝒪^{⊕ r}` on `ℙⁿ_T`

Let `K ⊆ 𝒪^{⊕ r}` on `ℙⁿ_T` be a submodule whose quotient `Q = 𝒪^{⊕ r}/K` is of finite
presentation and flat over `T`, that is `K ∈ AlgebraicGeometry.ProjectiveQuot.families n r T`.
For every morphism `g : T' ⟶ T`, with `g' : ℙⁿ_{T'} ⟶ ℙⁿ_T` the induced morphism, the
pulled-back sequence

`0 → (g')^*K → 𝒪^{⊕ r} → (g')^*Q → 0`

is again short exact: `(g')^*K → (g')^*𝒪^{⊕ r} = 𝒪^{⊕ r}` is still a monomorphism, because
`Tor_1^{𝒪_T}(Q, 𝒪_{T'})` vanishes for `Q` flat over `T`. Consequently the base change
`AlgebraicGeometry.ProjectiveQuot.baseChange g K` is the subobject `(g')^*K` itself.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.mono_pullback_map_arrow_of_mem_families`:
  `(g')^*K → (g')^*𝒪^{⊕ r}` is a monomorphism.
* `AlgebraicGeometry.ProjectiveQuot.shortExact_baseChange_of_mem_families`: the pulled-back
  sequence `0 → (g')^*K → 𝒪^{⊕ r} → (g')^*Q → 0` is short exact.
* `AlgebraicGeometry.ProjectiveQuot.baseChange_eq_mk_of_mem_families`: the base change of `K`
  along `g` is `(g')^*K`, embedded in `𝒪^{⊕ r}` through `freeModulePullbackIso`.
* The `hilbertFamilies` forms of the first two.

## Implementation notes

The work is done by
`AlgebraicGeometry.Scheme.Modules.mono_pullback_map_of_shortExact_of_isFlatOver`, applied to the
cokernel sequence of `K.arrow` and to the cartesian square
`AlgebraicGeometry.isPullback_projectiveSpaceOverMap`. Exactness in the middle and on the right
is right exactness of the inverse image, a left adjoint.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 00HL](https://stacks.math.columbia.edu/tag/00HL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveQuot

variable {n r : ℕ}

/-- The cokernel sequence of the inclusion of a subobject is short exact. -/
private theorem shortExact_cokernelSequence_arrow {T : Scheme.{u}}
    (K : Subobject (freeModule n r T)) : (ShortComplex.cokernelSequence K.arrow).ShortExact :=
  .mk' (ShortComplex.cokernelSequence_exact K.arrow) (inferInstanceAs (Mono K.arrow))
    (inferInstanceAs (Epi (cokernel.π K.arrow)))

/-- **The inverse image of a flat family's kernel is still a submodule.** If the quotient
`𝒪^{⊕ r}/K` on `ℙⁿ_T` is flat over `T` (and of finite presentation), then for every
`g : T' ⟶ T` the pullback of `K ⟶ 𝒪^{⊕ r}` along `ℙⁿ_{T'} ⟶ ℙⁿ_T` is a monomorphism. -/
theorem mono_pullback_map_arrow_of_mem_families {T' T : Scheme.{u}} (g : T' ⟶ T)
    {K : Subobject (freeModule n r T)} (hK : K ∈ families n r T) :
    Mono ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map K.arrow) := by
  exact Scheme.Modules.mono_pullback_map_of_shortExact_of_isFlatOver
    (isPullback_projectiveSpaceOverMap n g) (shortExact_cokernelSequence_arrow K) hK.2

/-- The `hilbertFamilies` form of
`AlgebraicGeometry.ProjectiveQuot.mono_pullback_map_arrow_of_mem_families`. -/
theorem mono_pullback_map_arrow_of_mem_hilbertFamilies {P : Polynomial ℚ} {T' T : Scheme.{u}}
    (g : T' ⟶ T) {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) :
    Mono ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map K.arrow) :=
  mono_pullback_map_arrow_of_mem_families g hK.1

/-- The pulled-back sequence `(g')^*K → 𝒪^{⊕ r} → (g')^*(𝒪^{⊕ r}/K)`, read on the free module
of `ℙⁿ_{T'}` through `freeModulePullbackIso`. -/
abbrev baseChangeSequence {T' T : Scheme.{u}} (g : T' ⟶ T) (K : Subobject (freeModule n r T)) :
    ShortComplex (projectiveSpaceOver n T').Modules :=
  ShortComplex.mk
    ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map K.arrow ≫
      (freeModulePullbackIso n r g).hom)
    (baseChangeQuotientMap g K) (by
      rw [baseChangeQuotientMap, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
        cokernel.condition, Functor.map_zero])

/-- **Base change of a flat family is short exact.** For `K ∈ families n r T` and any
`g : T' ⟶ T`, the sequence `0 → (g')^*K → 𝒪^{⊕ r} → (g')^*(𝒪^{⊕ r}/K) → 0` on `ℙⁿ_{T'}` is
short exact. -/
theorem shortExact_baseChange_of_mem_families {T' T : Scheme.{u}} (g : T' ⟶ T)
    {K : Subobject (freeModule n r T)} (hK : K ∈ families n r T) :
    (baseChangeSequence g K).ShortExact := by
  have _ := mono_pullback_map_arrow_of_mem_families g hK
  have _ : Mono (baseChangeSequence g K).f := inferInstanceAs (Mono (_ ≫ _))
  have _ : Epi (baseChangeSequence g K).g := inferInstanceAs (Epi (baseChangeQuotientMap g K))
  have hmap : ((ShortComplex.cokernelSequence K.arrow).map
      (Scheme.Modules.pullback (projectiveSpaceOverMap n g))).Exact :=
    (shortExact_cokernelSequence_arrow K).exact.map_of_epi_of_preservesCokernel _
      (shortExact_cokernelSequence_arrow K).epi_g inferInstance
  let e : (ShortComplex.cokernelSequence K.arrow).map
      (Scheme.Modules.pullback (projectiveSpaceOverMap n g)) ≅ baseChangeSequence g K :=
    ShortComplex.isoMk (Iso.refl _) (freeModulePullbackIso n r g) (Iso.refl _)
      (Category.id_comp _) ((Iso.hom_inv_id_assoc _ _).trans (Category.comp_id _).symm)
  exact { exact := (ShortComplex.exact_iff_of_iso e).1 hmap }

/-- The `hilbertFamilies` form of
`AlgebraicGeometry.ProjectiveQuot.shortExact_baseChange_of_mem_families`. -/
theorem shortExact_baseChange_of_mem_hilbertFamilies {P : Polynomial ℚ} {T' T : Scheme.{u}}
    (g : T' ⟶ T) {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) :
    (baseChangeSequence g K).ShortExact :=
  shortExact_baseChange_of_mem_families g hK.1

/-- **The base change of a flat family is the inverse image of its kernel.** For
`K ∈ families n r T` and `g : T' ⟶ T`, `AlgebraicGeometry.ProjectiveQuot.baseChange g K` is the
subobject `(g')^*K ⟶ (g')^*𝒪^{⊕ r} ≅ 𝒪^{⊕ r}`. -/
theorem baseChange_eq_mk_of_mem_families {T' T : Scheme.{u}} (g : T' ⟶ T)
    {K : Subobject (freeModule n r T)} (hK : K ∈ families n r T) :
    haveI := (shortExact_baseChange_of_mem_families g hK).mono_f
    baseChange g K = Subobject.mk
      ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map K.arrow ≫
        (freeModulePullbackIso n r g).hom) := by
  have hS := shortExact_baseChange_of_mem_families g hK
  have _ := hS.mono_f
  let i := IsLimit.conePointUniqueUpToIso (kernelIsKernel (baseChangeQuotientMap g K))
    hS.fIsKernel
  refine Subobject.mk_eq_mk_of_comm _ _ i ?_
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

end AlgebraicGeometry.ProjectiveQuot
