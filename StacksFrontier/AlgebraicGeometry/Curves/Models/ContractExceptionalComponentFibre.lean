module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ContractExceptionalComponent
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtension
public import StacksFrontier.AlgebraicGeometry.Divisors.PrimeDivisorStalk
public import StacksFrontier.RingTheory.Length.RingEquiv

/-!
# The components of the special fibre after contracting a component

In the situation of [Stacks, Tag 0C61] let `f : X ⟶ X'` contract an irreducible component `C_n`
of the special fibre, and let `X'` be the regular proper model of
`Stacks.Models.RegularProperModelSituation.contractedSituation`. This file identifies the special
fibre of `X'` with that of `X` away from `C_n`: the components of `X'_k` are the images
`C'_i = f(C_i)`, `i < n`, and their multiplicities are `m'_i = m_i`.

## Main definitions

* `Stacks.Models.RegularProperModelSituation.contractionSpecialFiberMap` — the morphism
  `X_k ⟶ X'_k` induced by the contraction.
* `Stacks.Models.RegularProperModelSituation.contractedComponentEquiv` — the bijection
  `i ↦ C'_i` between the components of `X_k` other than `C_n` and the components of `X'_k`.

## Main results

* `Stacks.Models.RegularProperModelSituation.exists_contractedComponentEquiv` — [Stacks, Tag 0C6C],
  the components `C'_i = f(C_i)`, `i < n`, of `X'_k` and their multiplicities `m'_i = m_i`.
* `Stacks.Models.RegularProperModelSituation.image_contractedComponentEquiv` — `C'_i = f(C_i)`.
* `Stacks.Models.RegularProperModelSituation.specialFiberMultiplicity_contractedComponentEquiv`
  — `m'_i = m_i`.
* `Stacks.Models.RegularProperModelSituation.exists_contractedComponentMap` — [Stacks, Tag 0C6C]
  (2): the morphisms `C_i ⟶ C'_i` and, when `C_i` meets `C_n`, `C_n ⟶ C'_i` compatible with `f`,
  whose maps of global sections are the maps `κ_i ← κ'_i → κ_n`.

## References

* [Stacks Project, Tag 0C6C](https://stacks.math.columbia.edu/tag/0C6C)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

/-! ### Generic points along open embeddings -/

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The closure of the image of an irreducible component under an open embedding is an
irreducible component. -/
public theorem closure_image_mem_irreducibleComponents_of_isOpenEmbedding {f : X → Y}
    (hf : Topology.IsOpenEmbedding f) {Z : Set X} (hZ : Z ∈ irreducibleComponents X) :
    closure (f '' Z) ∈ irreducibleComponents Y := by
  obtain ⟨W, hW, hZW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure (f '' Z)) (hZ.1.image f hf.continuous.continuousOn).closure
  have hpre : Z ⊆ f ⁻¹' W := fun x hx => hZW (subset_closure ⟨x, hx, rfl⟩)
  have hmeet : (W ∩ Set.range f).Nonempty := by
    obtain ⟨x, hx⟩ := hZ.1.1
    exact ⟨f x, hpre hx, ⟨x, rfl⟩⟩
  have heq : f ⁻¹' W = Z :=
    Set.Subset.antisymm (hZ.2 (preimage_mem_irreducibleComponents hW hf hmeet).1 hpre) hpre
  rwa [← heq, closure_image_preimage_of_isPreirreducible f hf.isOpenMap W
    (heq.symm ▸ hZ.1.1) hW.1.2 (isClosed_of_mem_irreducibleComponents W hW)]

/-- A point is a generic point of an irreducible component exactly when its image under an open
embedding is. -/
public theorem mem_genericPoints_iff_of_isOpenEmbedding {f : X → Y}
    (hf : Topology.IsOpenEmbedding f) (x : X) :
    f x ∈ genericPoints Y ↔ x ∈ genericPoints X := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · change closure ({x} : Set X) ∈ irreducibleComponents X
    rw [hf.isEmbedding.closure_eq_preimage_closure_image]
    simpa only [Set.image_singleton] using preimage_mem_irreducibleComponents hx hf
      ⟨f x, subset_closure (by simp), ⟨x, rfl⟩⟩
  · have hp := closure_image_mem_irreducibleComponents_of_isOpenEmbedding hf hx
    have hg := (isGenericPoint_closure (x := x)).image hf.continuous
    change closure ({f x} : Set Y) ∈ irreducibleComponents Y
    rwa [hg.def]

/-- The generic point of an irreducible component lies outside another irreducible component
exactly when the two components differ. -/
public theorem genericPoints.ofComponent_mem_compl_iff [QuasiSober X]
    (Z W : irreducibleComponents X) :
    (genericPoints.ofComponent Z).1 ∈ (W.1 : Set X)ᶜ ↔ Z ≠ W := by
  rw [Set.mem_compl_iff, (genericPoints.isGenericPoint_ofComponent Z).mem_closed_set_iff
    (isClosed_of_mem_irreducibleComponents W.1 W.2)]
  exact ⟨fun h e => h (by rw [e]),
    fun h hsub => h (Subtype.ext (Set.Subset.antisymm hsub (Z.2.2 W.2.1 hsub)))⟩

end Topology

/-- If `b` restricts to an isomorphism over an open `U`, so does any base change of `b`, over the
preimage of `U`. -/
public theorem isIso_morphismRestrict_of_isPullback {X Y A Z : Scheme.{u}} {b : X ⟶ Y}
    {q : Z ⟶ Y} {p : A ⟶ X} {g : A ⟶ Z} (H : IsPullback p g b q) (U : Y.Opens)
    [IsIso (b ∣_ U)] : IsIso (g ∣_ (q ⁻¹ᵁ U)) := by
  let V := q ⁻¹ᵁ U
  have hpb := ((isPullback_morphismRestrict g V).paste_vert H.flip).flip
  have : IsIso (pullback.snd b (V.ι ≫ q)) :=
    isIso_pullback_snd_of_isIso_morphismRestrict b _ U inferInstance fun z => z.2
  rw [← hpb.isoPullback_hom_snd]
  infer_instance

/-- **The colength of the inverse image of an ideal sheaf at a point where the morphism is a local
isomorphism.** If `φ : X ⟶ Y` induces an isomorphism of local rings at `x`, the local ring of `X`
at `x` modulo the inverse image of `I` has the length of the local ring of `Y` at `φ x` modulo
`I`. -/
public theorem length_quotient_stalk_comap_of_isIso_stalkMap {X Y : Scheme.{u}} (φ : X ⟶ Y)
    (I : Y.IdealSheafData) (x : X) [IsIso (φ.stalkMap x)] :
    Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ IdealSheafData.stalk (I.comap φ) x) =
      Module.length (Y.presheaf.stalk (φ x))
        (Y.presheaf.stalk (φ x) ⧸ IdealSheafData.stalk I (φ x)) := by
  rw [stalk_comap]
  exact (Module.quotient_length_eq_of_ringEquiv
    (asIso (φ.stalkMap x)).commRingCatIsoToRingEquiv _).symm

namespace Stacks.Models

namespace RegularModelSituation

variable (S : RegularModelSituation.{u})

/-- The generic point of an irreducible component of the special fibre, viewed in the model, is
the generic point of the prime divisor of that component. -/
public theorem specialFiberι_ofComponent (Z : irreducibleComponents S.specialFiber) :
    S.specialFiberι (genericPoints.ofComponent Z).1 =
      (S.specialFiberComponentPrimeDivisor Z).genericPoint := by
  have h := (genericPoints.isGenericPoint_ofComponent Z).image S.specialFiberι.continuous
  rw [(S.isClosed_image_specialFiberComponent Z).closure_eq] at h
  exact h.eq (S.closure_singleton_genericPoint_specialFiberComponent Z)

end RegularModelSituation

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u}) {N : irreducibleComponents S.specialFiber}
  {X' : Scheme.{u}} {f : S.X ⟶ X'}

/-- The special fibre of the contracted model has finitely many irreducible components. -/
public instance fintypeIrreducibleComponentsContractedSpecialFiber
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    Fintype (irreducibleComponents (S.contractedSituation hf).specialFiber) :=
  (S.contractedSituation hf).toRegularModelSituation.fintypeIrreducibleComponentsSpecialFiber

/-! ### The induced morphism of special fibres -/

/-- **The morphism of special fibres induced by the contraction**, `X_k ⟶ X'_k`. -/
public def contractionSpecialFiberMap
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    S.specialFiber ⟶ (S.contractedSituation hf).specialFiber :=
  pullback.map S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))
    (S.contractionToBase hf) (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))) f (𝟙 _) (𝟙 _)
    (by simp) (by simp)

/-- The morphism of special fibres is compatible with the contraction. -/
@[reassoc]
public theorem contractionSpecialFiberMap_specialFiberι
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    S.contractionSpecialFiberMap hf ≫ (S.contractedSituation hf).specialFiberι =
      S.specialFiberι ≫ f :=
  pullback.lift_fst _ _ _

/-- The morphism of special fibres is compatible with the contraction, pointwise. -/
public theorem specialFiberι_contractionSpecialFiberMap_apply
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (x : S.specialFiber) :
    (S.contractedSituation hf).specialFiberι (S.contractionSpecialFiberMap hf x) =
      f (S.specialFiberι x) :=
  congrArg (fun φ : S.specialFiber ⟶ X' => φ x) (S.contractionSpecialFiberMap_specialFiberι hf)

/-- The special fibre of `X` is the base change of that of `X'` along the contraction. -/
public theorem isPullback_contractionSpecialFiberMap
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    IsPullback S.specialFiberι (S.contractionSpecialFiberMap hf) f
      (S.contractedSituation hf).specialFiberι := by
  let k := Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))
  have hsnd : S.contractionSpecialFiberMap hf ≫ pullback.snd (S.contractionToBase hf) k =
      pullback.snd S.X_to_R k := by
    simp only [contractionSpecialFiberMap, pullback.map]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hfull :
      IsPullback (S.contractionSpecialFiberMap hf ≫ pullback.snd (S.contractionToBase hf) k)
      (pullback.fst S.X_to_R k) k (f ≫ S.contractionToBase hf) := by
    rw [hsnd, S.contraction_comp_contractionToBase hf]
    exact (IsPullback.of_hasPullback S.X_to_R k).flip
  exact (hfull.of_right (S.contractionSpecialFiberMap_specialFiberι hf)
    (IsPullback.of_hasPullback (S.contractionToBase hf) k).flip).flip

/-- A point of `X_k` maps to the centre `z` under the contraction exactly when it lies on `C_n`. -/
private theorem apply_specialFiberι_eq_iff_mem {z : X'}
    (hsupp : ∀ x : S.X, x ∈ (S.specialFiberComponentIdeal N).support ↔ f x = z)
    (x : S.specialFiber) : f (S.specialFiberι x) = z ↔ x ∈ (N.1 : Set S.specialFiber) := by
  rw [← hsupp, ← SetLike.mem_coe, S.coe_support_specialFiberComponentIdeal,
    S.specialFiberι.isClosedEmbedding.injective.mem_set_image]

/-- **The contraction is an isomorphism of special fibres away from `C_n`.** There is an open
`V ⊆ X'_k` containing every generic point of `X'_k`, whose preimage in `X_k` is the complement of
`C_n`, over which the morphism of special fibres is an isomorphism. -/
public theorem exists_isIso_contractionSpecialFiberMap_restrict
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    ∃ V : (S.contractedSituation hf).specialFiber.Opens,
      IsIso (S.contractionSpecialFiberMap hf ∣_ V) ∧
      (∀ x : S.specialFiber, S.contractionSpecialFiberMap hf x ∈ V ↔ x ∉ (N.1 : Set _)) ∧
      genericPoints (S.contractedSituation hf).specialFiber ⊆ V := by
  let T := S.contractedSituation hf
  obtain ⟨z, hz, -, hzdim, hsupp, hiso⟩ := hf.exists_centre
  let U : X'.Opens := ⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩
  refine ⟨T.specialFiberι ⁻¹ᵁ U,
    isIso_morphismRestrict_of_isPullback (S.isPullback_contractionSpecialFiberMap hf) U,
    fun x => ?_, fun η hη => ?_⟩
  · change T.specialFiberι (S.contractionSpecialFiberMap hf x) ≠ z ↔ _
    have h1 := S.specialFiberι_contractionSpecialFiberMap_apply hf x
    have key := S.apply_specialFiberι_eq_iff_mem hsupp x
    exact ⟨fun h hx => h (h1.trans (key.2 hx)), fun h e => h (key.1 (h1.symm.trans e))⟩
  · change T.specialFiberι η ≠ z
    intro hηz
    have hgen : T.specialFiberι η =
        (T.specialFiberComponentPrimeDivisor (genericPoints.component ⟨η, hη⟩)).genericPoint := by
      rw [← T.specialFiberι_ofComponent, genericPoints.ofComponent_component]
    have h1 := (T.specialFiberComponentPrimeDivisor
      (genericPoints.component ⟨η, hη⟩)).ringKrullDim_stalk_genericPoint_eq_one
    rw [← hgen, hηz] at h1
    change ringKrullDim (X'.presheaf.stalk z) = 1 at h1
    rw [hzdim] at h1
    norm_num at h1

/-- The morphism of special fibres carries the generic point of a component `C_i ≠ C_n` to a
generic point of `X'_k`, and is an isomorphism of local rings there. -/
public theorem contractionSpecialFiberMap_ofComponent_mem_genericPoints
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    S.contractionSpecialFiberMap hf (genericPoints.ofComponent Z.1).1 ∈
        genericPoints (S.contractedSituation hf).specialFiber ∧
      IsIso ((S.contractionSpecialFiberMap hf).stalkMap (genericPoints.ofComponent Z.1).1) := by
  obtain ⟨V, hV, hmem, -⟩ := S.exists_isIso_contractionSpecialFiberMap_restrict hf
  let g := S.contractionSpecialFiberMap hf
  have hx : g (genericPoints.ofComponent Z.1).1 ∈ V :=
    (hmem _).2 ((genericPoints.ofComponent_mem_compl_iff Z.1 N).2 Z.2)
  refine ⟨?_, isIso_stalkMap_of_isIso_morphismRestrict g hV hx⟩
  let xU : (g ⁻¹ᵁ V).toScheme := ⟨_, hx⟩
  have h1 : xU ∈ genericPoints (g ⁻¹ᵁ V).toScheme :=
    (mem_genericPoints_iff_of_isOpenEmbedding (g ⁻¹ᵁ V).ι.isOpenEmbedding xU).1
      (genericPoints.ofComponent Z.1).2
  have h3 := (mem_genericPoints_iff_of_isOpenEmbedding V.ι.isOpenEmbedding ((g ∣_ V) xU)).2
    ((mem_genericPoints_iff_of_isOpenEmbedding (g ∣_ V).homeomorph.isOpenEmbedding xU).2 h1)
  change ((g ∣_ V) xU).1 ∈ _ at h3
  rwa [morphismRestrict_base_coe] at h3

/-- Distinct components `C_i ≠ C_n` of `X_k` give distinct components of `X'_k`, through the
images of their generic points. -/
private theorem injective_contractedComponent
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    Function.Injective fun Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N} =>
      genericPoints.component
        ⟨_, (S.contractionSpecialFiberMap_ofComponent_mem_genericPoints hf Z).1⟩ := by
  obtain ⟨V, hV, hmem, -⟩ := S.exists_isIso_contractionSpecialFiberMap_restrict hf
  let g := S.contractionSpecialFiberMap hf
  have hV' (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
      g (genericPoints.ofComponent Z.1).1 ∈ V :=
    (hmem _).2 ((genericPoints.ofComponent_mem_compl_iff Z.1 N).2 Z.2)
  intro Z W hZW
  let xZ : (g ⁻¹ᵁ V).toScheme := ⟨_, hV' Z⟩
  let xW : (g ⁻¹ᵁ V).toScheme := ⟨_, hV' W⟩
  have heq : (g ∣_ V) xZ = (g ∣_ V) xW :=
    Subtype.ext (by
      simpa only [morphismRestrict_base_coe] using
        congrArg Subtype.val (genericPoints.component_injective hZW))
  have hpt : (genericPoints.ofComponent Z.1).1 = (genericPoints.ofComponent W.1).1 :=
    congrArg (fun q : (g ⁻¹ᵁ V).toScheme => (q.1 : S.specialFiber))
      ((g ∣_ V).homeomorph.injective heq)
  exact Subtype.ext (by
    simpa only [genericPoints.component_ofComponent] using
      congrArg genericPoints.component (Subtype.ext hpt))

/-- Every component of `X'_k` comes from a component `C_i ≠ C_n` of `X_k`, through the image of
its generic point. -/
private theorem surjective_contractedComponent
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    Function.Surjective fun Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N} =>
      genericPoints.component
        ⟨_, (S.contractionSpecialFiberMap_ofComponent_mem_genericPoints hf Z).1⟩ := by
  obtain ⟨V, hV, hmem, hgen⟩ := S.exists_isIso_contractionSpecialFiberMap_restrict hf
  let g := S.contractionSpecialFiberMap hf
  intro W
  let η := (genericPoints.ofComponent W).1
  have hη : η ∈ V := hgen (genericPoints.ofComponent W).2
  let ηV : V.toScheme := ⟨η, hη⟩
  obtain ⟨xV, hxV⟩ := (g ∣_ V).homeomorph.surjective ηV
  change (g ∣_ V) xV = ηV at hxV
  have hgenV : ηV ∈ genericPoints V.toScheme :=
    (mem_genericPoints_iff_of_isOpenEmbedding V.ι.isOpenEmbedding ηV).1
      (genericPoints.ofComponent W).2
  have hgenXv : xV ∈ genericPoints (g ⁻¹ᵁ V).toScheme :=
    (mem_genericPoints_iff_of_isOpenEmbedding (g ∣_ V).homeomorph.isOpenEmbedding xV).1
      (by
        change (g ∣_ V) xV ∈ _
        rwa [hxV])
  have hgenX : xV.1 ∈ genericPoints S.specialFiber :=
    (mem_genericPoints_iff_of_isOpenEmbedding (g ⁻¹ᵁ V).ι.isOpenEmbedding xV).2 hgenXv
  have hxη : g xV.1 = η := by
    simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hxV
  let Z : irreducibleComponents S.specialFiber := genericPoints.component ⟨xV.1, hgenX⟩
  have hpoint : (genericPoints.ofComponent Z).1 = xV.1 :=
    congrArg Subtype.val (genericPoints.ofComponent_component ⟨xV.1, hgenX⟩)
  have hnotN : Z ≠ N := by
    intro hZN
    have hxN : xV.1 ∈ (N.1 : Set S.specialFiber) := by
      rw [← hpoint, ← hZN]
      exact (genericPoints.isGenericPoint_ofComponent Z).mem
    exact (hmem xV.1).1 (by rwa [hxη]) hxN
  have hval : g (genericPoints.ofComponent Z).1 = η := by rw [hpoint, hxη]
  exact ⟨⟨Z, hnotN⟩, (congrArg genericPoints.component (Subtype.ext hval)).trans
    (genericPoints.component_ofComponent W)⟩

/-- The components of `X_k` other than `C_n` correspond bijectively to the components of `X'_k`,
through the images of their generic points. -/
public theorem bijective_contractedComponent
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    Function.Bijective fun Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N} =>
      genericPoints.component
        ⟨_, (S.contractionSpecialFiberMap_ofComponent_mem_genericPoints hf Z).1⟩ :=
  ⟨S.injective_contractedComponent hf, S.surjective_contractedComponent hf⟩

/-- **The components `C'_i` of the contracted special fibre.** The component of `X'_k`
corresponding to a component `C_i ≠ C_n` of `X_k`: the closure of the image of the generic point
of `C_i`. By `Stacks.Models.RegularProperModelSituation.image_contractedComponentEquiv` it is
`f(C_i)`. -/
public def contractedComponentEquiv
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    {Z : irreducibleComponents S.specialFiber // Z ≠ N} ≃
      irreducibleComponents (S.contractedSituation hf).specialFiber :=
  Equiv.ofBijective _ (S.bijective_contractedComponent hf)

/-- The morphism of special fibres carries the generic point of `C_i` to that of `C'_i`. -/
public theorem contractionSpecialFiberMap_ofComponent
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    S.contractionSpecialFiberMap hf (genericPoints.ofComponent Z.1).1 =
      (genericPoints.ofComponent (S.contractedComponentEquiv hf Z)).1 :=
  congrArg Subtype.val (genericPoints.ofComponent_component
    ⟨_, (S.contractionSpecialFiberMap_ofComponent_mem_genericPoints hf Z).1⟩).symm

/-- The contraction carries the generic point of `C_i` in `X` to the generic point of `C'_i` in
`X'`. -/
public theorem contraction_genericPoint_specialFiberComponentPrimeDivisor
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    f (S.specialFiberComponentPrimeDivisor Z.1).genericPoint =
      ((S.contractedSituation hf).specialFiberComponentPrimeDivisor
        (S.contractedComponentEquiv hf Z)).genericPoint := by
  rw [← S.specialFiberι_ofComponent, ← (S.contractedSituation hf).specialFiberι_ofComponent,
    ← S.contractionSpecialFiberMap_ofComponent hf Z]
  exact (S.specialFiberι_contractionSpecialFiberMap_apply hf _).symm

/-- **`C'_i = f(C_i)`.** The component of `X'_k` corresponding to `C_i` is the image of `C_i`
under the contraction, as subsets of `X'`. -/
public theorem image_contractedComponentEquiv
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    (S.contractedSituation hf).specialFiberι.base ''
        ((S.contractedComponentEquiv hf Z).1 : Set (S.contractedSituation hf).specialFiber) =
      f.base '' (S.specialFiberι.base '' (Z.1.1 : Set S.specialFiber)) := by
  have := hf.isProper
  rw [← (S.contractedSituation hf).closure_singleton_genericPoint_specialFiberComponent
    (S.contractedComponentEquiv hf Z), ← S.closure_singleton_genericPoint_specialFiberComponent Z.1]
  change closure {((S.contractedSituation hf).specialFiberComponentPrimeDivisor
    (S.contractedComponentEquiv hf Z)).genericPoint} =
      f.base '' closure {(S.specialFiberComponentPrimeDivisor Z.1).genericPoint}
  rw [← S.contraction_genericPoint_specialFiberComponentPrimeDivisor hf Z, ← Set.image_singleton,
    f.isClosedMap.closure_image_eq_of_continuous f.continuous]

/-- The special fibre of `X` is the inverse image of the special fibre of `X'` under the
contraction. -/
public theorem specialFiberIdeal_eq_comap_contraction
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    S.specialFiberIdeal = (S.contractedSituation hf).specialFiberIdeal.comap f := by
  let jk := Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))
  have : IsClosedImmersion jk :=
    IsClosedImmersion.spec_of_surjective _ S.surjective_algebraMap_residueField
  change (pullback.fst S.X_to_R jk).ker = (pullback.fst (S.contractionToBase hf) jk).ker.comap f
  rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← Scheme.IdealSheafData.comap_comp,
    S.contraction_comp_contractionToBase hf]

/-- The contraction is an isomorphism of local rings at the generic point of every component
`C_i ≠ C_n`. -/
public theorem isIso_stalkMap_genericPoint_specialFiberComponentPrimeDivisor
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    IsIso (f.stalkMap (S.specialFiberComponentPrimeDivisor Z.1).genericPoint) :=
  hf.isIso_stalkMap fun hmem =>
    S.genericPoint_specialFiberComponent_notMem_support (Ne.symm Z.2) hmem

/-- **`m'_i = m_i`.** The multiplicity of `C'_i` in `X'_k` is the multiplicity of `C_i` in
`X_k`. -/
public theorem specialFiberMultiplicity_contractedComponentEquiv
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    (S.contractedSituation hf).specialFiberMultiplicity (S.contractedComponentEquiv hf Z) =
      S.specialFiberMultiplicity Z.1 := by
  simp only [RegularModelSituation.specialFiberMultiplicity, effectiveCartierMultiplicity]
  have := S.isIso_stalkMap_genericPoint_specialFiberComponentPrimeDivisor hf Z
  rw [S.specialFiberIdeal_eq_comap_contraction hf, length_quotient_stalk_comap_of_isIso_stalkMap,
    S.contraction_genericPoint_specialFiberComponentPrimeDivisor hf Z]

/-- **The components and multiplicities of the contracted model.** Let
`f : X ⟶ X'` contract the component `C_n` of the special fibre of a regular proper model `X`,
and let `X'` be the regular proper model of
`Stacks.Models.RegularProperModelSituation.contractedSituation`. Then `f` lies over `Spec R` and
over the identification of both generic fibres with `C`, and the images `C'_i = f(C_i)` of the
components `C_i ≠ C_n` are exactly the `n - 1` irreducible components of `X'_k`, with
multiplicities `m'_i = m_i`. -/
@[stacks 0C6C "the components C'_i = f(C_i), i < n, of X'_k and their multiplicities m'_i = m_i"]
public theorem exists_contractedComponentEquiv
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    f ≫ (S.contractedSituation hf).X_to_R = S.X_to_R ∧
      (S.contractedSituation hf).genericFiberIso.hom ≫
          pullback.fst (S.contractedSituation hf).X_to_R
            (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))) =
        S.genericFiberIso.hom ≫ pullback.fst S.X_to_R _ ≫ f ∧
      Fintype.card (irreducibleComponents (S.contractedSituation hf).specialFiber) + 1 =
        Fintype.card (irreducibleComponents S.specialFiber) ∧
      ∃ σ : {Z : irreducibleComponents S.specialFiber // Z ≠ N} ≃
          irreducibleComponents (S.contractedSituation hf).specialFiber,
        ∀ Z, (S.contractedSituation hf).specialFiberι.base ''
              ((σ Z).1 : Set (S.contractedSituation hf).specialFiber) =
            f.base '' (S.specialFiberι.base '' (Z.1.1 : Set S.specialFiber)) ∧
          (S.contractedSituation hf).specialFiberMultiplicity (σ Z) =
            S.specialFiberMultiplicity Z.1 := by
  classical
  refine ⟨S.contraction_comp_contractionToBase hf, S.contractedGenericFiberIso_hom_fst hf, ?_,
    S.contractedComponentEquiv hf, fun Z => ⟨S.image_contractedComponentEquiv hf Z,
      S.specialFiberMultiplicity_contractedComponentEquiv hf Z⟩⟩
  rw [← Fintype.card_congr (S.contractedComponentEquiv hf), Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]
  have := Fintype.card_pos_iff.mpr ⟨N⟩
  omega

/-- The kernel of `C ⟶ X ⟶ X'` is the vanishing ideal of the closure of the image of `C`. -/
private theorem ker_specialFiberComponentIdeal_subschemeι_comp_eq_vanishingIdeal
    (Z : irreducibleComponents S.specialFiber) :
    ((S.specialFiberComponentIdeal Z).subschemeι ≫ f).ker =
      Scheme.IdealSheafData.vanishingIdeal
        (⟨closure (f.base '' (S.specialFiberι.base '' (Z.1 : Set S.specialFiber))),
          isClosed_closure⟩ : Closeds X') := by
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  ext1
  change closure (f.base '' closure (S.specialFiberι.base '' (Z.1 : Set S.specialFiber))) = _
  rw [(S.isClosed_image_specialFiberComponent Z).closure_eq]
  rfl

/-- The reduced ideal sheaf of `C'_i` is the kernel of `C_i ⟶ X ⟶ X'`. -/
public theorem ker_specialFiberComponentIdeal_subschemeι_comp_contraction
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    ((S.specialFiberComponentIdeal Z.1).subschemeι ≫ f).ker =
      (S.contractedSituation hf).specialFiberComponentIdeal (S.contractedComponentEquiv hf Z) := by
  rw [S.ker_specialFiberComponentIdeal_subschemeι_comp_eq_vanishingIdeal]
  congr 1
  ext1
  change closure (f.base '' (S.specialFiberι.base '' (Z.1.1 : Set S.specialFiber))) =
    closure ((S.contractedSituation hf).specialFiberι.base ''
      ((S.contractedComponentEquiv hf Z).1 : Set (S.contractedSituation hf).specialFiber))
  rw [S.image_contractedComponentEquiv hf Z]

/-- **The morphism `C_i ⟶ C'_i`** induced by the contraction. -/
public def contractedComponentMap
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    (S.specialFiberComponentIdeal Z.1).subscheme ⟶
      ((S.contractedSituation hf).specialFiberComponentIdeal
        (S.contractedComponentEquiv hf Z)).subscheme :=
  IsClosedImmersion.lift ((S.contractedSituation hf).specialFiberComponentIdeal
    (S.contractedComponentEquiv hf Z)).subschemeι
    ((S.specialFiberComponentIdeal Z.1).subschemeι ≫ f) (by
    rw [Scheme.IdealSheafData.ker_subschemeι,
      S.ker_specialFiberComponentIdeal_subschemeι_comp_contraction hf Z])

/-- The morphism `C_i ⟶ C'_i` is compatible with the contraction. -/
@[reassoc (attr := simp)]
public theorem contractedComponentMap_subschemeι
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    S.contractedComponentMap hf Z ≫ ((S.contractedSituation hf).specialFiberComponentIdeal
        (S.contractedComponentEquiv hf Z)).subschemeι =
      (S.specialFiberComponentIdeal Z.1).subschemeι ≫ f :=
  IsClosedImmersion.lift_fac _ _ _

/-- **The maps `κ_i ← κ'_i → κ_n`.** If `C_i` meets `C_n`, there are morphisms `C_i ⟶ C'_i` and
`C_n ⟶ C'_i` compatible with the contraction and with the closed immersions into `X` and `X'`,
and their maps of global sections are ring maps `κ_i ← κ'_i → κ_n`, where `κ_i`, `κ'_i`, `κ_n`
are the rings of global functions on `C_i`, `C'_i`, `C_n`. -/
@[stacks 0C6C "part (2): maps κ_i ← κ'_i → κ_n when C_i meets C_n"]
public theorem exists_contractedComponentMap
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N})
    (hmeet : ((Z.1.1 : Set S.specialFiber) ∩ N.1).Nonempty) :
    ∃ (φ : Γ(((S.contractedSituation hf).specialFiberComponentIdeal
          (S.contractedComponentEquiv hf Z)).subscheme, ⊤) ⟶
          Γ((S.specialFiberComponentIdeal Z.1).subscheme, ⊤))
      (ψ : Γ(((S.contractedSituation hf).specialFiberComponentIdeal
          (S.contractedComponentEquiv hf Z)).subscheme, ⊤) ⟶
          Γ((S.specialFiberComponentIdeal N).subscheme, ⊤))
      (g : (S.specialFiberComponentIdeal Z.1).subscheme ⟶
        ((S.contractedSituation hf).specialFiberComponentIdeal
          (S.contractedComponentEquiv hf Z)).subscheme)
      (h : (S.specialFiberComponentIdeal N).subscheme ⟶
        ((S.contractedSituation hf).specialFiberComponentIdeal
          (S.contractedComponentEquiv hf Z)).subscheme),
      g ≫ ((S.contractedSituation hf).specialFiberComponentIdeal
          (S.contractedComponentEquiv hf Z)).subschemeι =
          (S.specialFiberComponentIdeal Z.1).subschemeι ≫ f ∧
        h ≫ ((S.contractedSituation hf).specialFiberComponentIdeal
          (S.contractedComponentEquiv hf Z)).subschemeι =
          (S.specialFiberComponentIdeal N).subschemeι ≫ f ∧
        g.appTop = φ ∧ h.appTop = ψ := by
  let T := S.contractedSituation hf
  let W := S.contractedComponentEquiv hf Z
  obtain ⟨z, hz, -, -, hsupp, -⟩ := hf.exists_centre
  have hN (y : S.specialFiber) := (S.apply_specialFiberι_eq_iff_mem hsupp y).2
  have hzW : z ∈ T.specialFiberι.base '' (W.1 : Set T.specialFiber) := by
    obtain ⟨y, hyZ, hyN⟩ := hmeet
    rw [S.image_contractedComponentEquiv hf Z]
    exact ⟨S.specialFiberι y, ⟨y, hyZ, rfl⟩, hN y hyN⟩
  have hker : ((S.specialFiberComponentIdeal N).subschemeι ≫ f).ker =
      Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X') := by
    rw [S.ker_specialFiberComponentIdeal_subschemeι_comp_eq_vanishingIdeal]
    congr 1
    ext1
    change closure (f.base '' (S.specialFiberι.base '' (N.1 : Set S.specialFiber))) = {z}
    refine (closure_mono ?_).trans hz.closure_eq.le |>.antisymm ?_
    · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact hN y hy
    · rintro _ rfl
      obtain ⟨y, hy⟩ := N.2.1.1
      exact subset_closure ⟨_, ⟨y, hy, rfl⟩, hN y hy⟩
  have hle : (T.specialFiberComponentIdeal W).subschemeι.ker ≤
      ((S.specialFiberComponentIdeal N).subschemeι ≫ f).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hker,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    intro y hy
    rwa [Set.mem_singleton_iff.mp hy, ← SetLike.mem_coe,
      T.coe_support_specialFiberComponentIdeal W]
  exact ⟨_, _, S.contractedComponentMap hf Z, IsClosedImmersion.lift _ _ hle,
    S.contractedComponentMap_subschemeι hf Z, IsClosedImmersion.lift_fac _ _ _, rfl, rfl⟩

end RegularProperModelSituation

end Stacks.Models

end
