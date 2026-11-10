module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.DenseElementaryFibration
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections

/-!
# Elementary fibrations from one closed fibre

Let `T` be a normal integral scheme smooth over a field `k`, let `π : X̄ ⟶ T` be projective with a
section, let `U ⊆ X̄` be an irreducible open with reduced boundary `Z = X̄ ∖ U`, and let `s ∈ T` be
a point over which `U` has a point. If `π` is smooth with fibres of dimension `1` along the fibre
`C = π⁻¹(s)`, and `Z` is étale over `T` at its points over `s` and has one there, then `π`
restricts to an elementary fibration over an affine neighbourhood of `s`. This gives the pointwise
form of Artin's good neighbourhoods (SGA 4, Exposé XI, Proposition 3.3): an elementary fibration on
a neighbourhood of a *given* closed point.

## Main results

* `AlgebraicGeometry.isIso_globalSections_of_isIntegral_of_section`: an integral scheme proper
  over a field `K` with a `K`-rational point has `Γ(C, 𝒪) = K`.
* `AlgebraicGeometry.irreducibleSpace_fiber_genericPoint_of_isOpenImmersion`: the generic fibre
  of a smooth family of curves is irreducible if it is the union of the generic fibre of an
  irreducible open and of a quasi-finite boundary.
* `AlgebraicGeometry.isElementaryFibration_of_smoothOfRelativeDimension_of_etale_of_isIso`:
  the elementary fibration criterion with `H⁰(C_η, 𝒪) = κ(η)` as its input.
* `AlgebraicGeometry.exists_isElementaryFibration_of_closedFibre`: the spreading out from one
  fibre.
* `AlgebraicGeometry.exists_elementaryFibrationNeighbourhood_of_closedFibre`: the conclusion in
  the shape of `Stacks.EtaleCohomology.ExistsElementaryFibrationNeighbourhood`.

## References

* SGA 4, Tome 3, Exposé XI, Proposition 3.3.
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

/-- **An integral proper scheme over a field with a rational point has only constant global
functions**: for `C` integral and proper over a field `K` with a `K`-rational point, the structure
map `K → Γ(C, 𝒪)` is an isomorphism. -/
theorem isIso_globalSections_of_isIntegral_of_section (K : Type u) [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsProper f] [IsIntegral C] (s : Spec (.of K) ⟶ C)
    (hs : s ≫ f = 𝟙 _) :
    IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop) := by
  let φ := (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop
  let ψ := s.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    have h : f.appTop ≫ s.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, hs, Scheme.Hom.id_appTop]
    simp only [φ, ψ, Category.assoc]
    rw [reassoc_of% h, Iso.inv_hom_id]
  let : Algebra K Γ(C, ⊤) := φ.hom.toAlgebra
  have hfin : Module.Finite K Γ(C, ⊤) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.moduleFinite_globalSections_of_isProper K f
  have hinj : Function.Injective (algebraMap K Γ(C, ⊤)) := (algebraMap K Γ(C, ⊤)).injective
  have hfield : IsField Γ(C, ⊤) :=
    (Algebra.IsIntegral.isField_iff_isField hinj).1 (Field.toIsField K)
  have hψinj : Function.Injective ψ.hom := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra hne
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hne
    have h1 : ψ.hom (a * b) = 1 := by rw [hb, map_one]
    rw [map_mul, ha, zero_mul] at h1
    exact zero_ne_one h1
  have hφψ' : ∀ a : K, ψ.hom (φ.hom a) = a := fun a => by
    rw [← CommRingCat.comp_apply, hφψ, CommRingCat.id_apply]
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun a b hab => by rw [← hφψ' a, ← hφψ' b]; exact congrArg ψ.hom hab, fun a => ?_⟩
  exact ⟨ψ.hom a, hψinj (hφψ' (ψ.hom a))⟩

/-- **The generic fibre of a smooth family of curves is irreducible when the complement of an
irreducible open is quasi-finite.** Let `π : X̄ ⟶ T` be smooth of relative dimension `1` over an
irreducible `T`, `j : U ⟶ X̄` an open immersion of an irreducible scheme, and `i : Z ⟶ X̄` a closed
immersion onto the complement of `j(U)`, quasi-finite over `T`. Then the generic fibre of `π` is
irreducible. -/
theorem irreducibleSpace_fiber_genericPoint_of_isOpenImmersion {T Xt U Z : Scheme.{u}}
    [IrreducibleSpace T] (π : Xt ⟶ T) [SmoothOfRelativeDimension 1 π]
    (j : U ⟶ Xt) [IsOpenImmersion j] [IrreducibleSpace U]
    (i : Z ⟶ Xt) [IsClosedImmersion i] [LocallyQuasiFinite (i ≫ π)]
    (hZ : Set.range i.base = (Set.range j.base)ᶜ) :
    IrreducibleSpace (π.fiber (genericPoint T)) := by
  have hηT := genericPoint_spec T
  have hηs : ∀ t : T, genericPoint T ⤳ t := genericPoint_specializes
  generalize genericPoint T = η at hηT hηs ⊢
  have : Smooth π := SmoothOfRelativeDimension.smooth 1 π
  obtain ⟨u, hu⟩ : ∃ u : U, π (j u) = η := by
    have ho : IsOpen (π.base '' Set.range j.base) :=
      π.isOpenMap _ j.isOpenEmbedding.isOpen_range
    have hne : (Set.univ ∩ π.base '' Set.range j.base).Nonempty :=
      ⟨_, trivial, ⟨_, ⟨genericPoint U, rfl⟩, rfl⟩⟩
    obtain ⟨_, ⟨u, rfl⟩, h⟩ := (hηT.mem_open_set_iff ho).2 hne
    exact ⟨u, h⟩
  set g := j (genericPoint U)
  have hg : π g = η := by
    have h₁ : π g ⤳ π (j u) :=
      ((genericPoint_specializes u).map j.continuous).map π.continuous
    rw [hu] at h₁
    exact (h₁.antisymm (hηs _)).eq
  let P : Set Xt := π.base ⁻¹' {η}
  have hdisc : _root_.IsDiscrete (i.base '' ((i ≫ π).base ⁻¹' {η})) :=
    ((i ≫ π).isDiscrete_preimage_singleton η).image i.isClosedEmbedding.isInducing
  have hA : ∀ y ∈ P, y ∈ Set.range j.base → y ∈ closure ({g} : Set Xt) := by
    rintro _ - ⟨v, rfl⟩
    exact specializes_iff_mem_closure.1 ((genericPoint_specializes v).map j.continuous)
  have hP : P ⊆ closure ({g} : Set Xt) := by
    intro y hy
    by_cases hyj : y ∈ Set.range j.base
    · exact hA y hy hyj
    · have hyZ : y ∈ Set.range i.base := by rw [hZ]; exact hyj
      refine closure_minimal (s := P ∩ Set.range j.base) (fun z hz => hA z hz.1 hz.2)
        isClosed_closure ?_
      by_contra hcl
      set W : Set P := {p | p.1 ∉ closure (P ∩ Set.range j.base)}
      have hWo : IsOpen W := isClosed_closure.isOpen_compl.preimage continuous_subtype_val
      have hyW : (⟨y, hy⟩ : P) ∈ W := hcl
      have hWsub : ∀ p ∈ W, p.1 ∈ i.base '' ((i ≫ π).base ⁻¹' {η}) := by
        intro p hp
        have hpj : p.1 ∉ Set.range j.base := fun h => hp (subset_closure ⟨p.2, h⟩)
        rw [← Set.mem_compl_iff, ← hZ] at hpj
        obtain ⟨z, hz⟩ := hpj
        refine ⟨z, ?_, hz⟩
        change π (i z) = η
        rw [hz]
        exact p.2
      have hWd : DiscreteTopology W := by
        have : DiscreteTopology (i.base '' ((i ≫ π).base ⁻¹' {η})) := hdisc.to_subtype
        let f : W → (i.base '' ((i ≫ π).base ⁻¹' {η})) := fun w => ⟨w.1.1, hWsub w.1 w.2⟩
        have hf : IsEmbedding f := by
          rw [← IsEmbedding.subtypeVal.of_comp_iff]
          exact (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal :
            IsEmbedding (fun w : W => (w.1.1 : Xt)))
        exact hf.discreteTopology
      have h₁ : topologicalKrullDimAt P ⟨y, hy⟩ = ((1 : ℕ) : WithBot ℕ∞) := by
        have h := fiberDimensionAt_eq_of_smoothOfRelativeDimension π 1 y
        rw [topologicalKrullDimAt_eq_of_homeomorph (π.fiberHomeo (π y)) (π.asFiber y)] at h
        have hpt : (π.fiberHomeo (π y) (π.asFiber y) : Xt) = y := by
          rw [Scheme.Hom.fiberHomeo_apply, Scheme.Hom.fiberι_asFiber]
        have key : ∀ (S : Set Xt) (hS : S = P) (hyS : y ∈ S),
            topologicalKrullDimAt S ⟨y, hyS⟩ = topologicalKrullDimAt P ⟨y, hy⟩ := by
          rintro S rfl hyS
          rfl
        have hS : π.base ⁻¹' {π y} = P := by
          change π.base ⁻¹' {π y} = π.base ⁻¹' {η}
          rw [show π y = η from hy]
        rw [← key _ hS (by simp)]
        rw [← h]
        congr 1
        exact Subtype.ext hpt.symm
      have h₂ : topologicalKrullDimAt P ⟨y, hy⟩ ≤ 0 := by
        refine (topologicalKrullDimAt_isLeast P ⟨y, hy⟩).2 ⟨W, hyW, hWo, rfl⟩ |>.trans ?_
        exact topologicalKrullDim_zero_of_discreteTopology W
      rw [h₁] at h₂
      exact absurd h₂ (by norm_num)
  have hirr : IsIrreducible P := by
    have hgP : g ∈ P := hg
    have hcl : closure P = closure ({g} : Set Xt) :=
      le_antisymm (closure_minimal hP isClosed_closure)
        (closure_mono (Set.singleton_subset_iff.2 hgP))
    rw [← isIrreducible_iff_closure, hcl]
    exact isIrreducible_singleton.closure
  have : IrreducibleSpace P := Subtype.irreducibleSpace hirr
  have h := (IrreducibleSpace.isIrreducible_univ P).image (π.fiberHomeo η).symm
    (π.fiberHomeo η).symm.continuous.continuousOn
  rw [Set.image_univ, Homeomorph.range_coe] at h
  exact (irreducibleSpace_def _).2 h

/-- **A criterion for an elementary fibration, from the global functions on the generic fibre.**
Let `T` be a normal integral scheme, smooth over a field `k`, and let `π : X̄ ⟶ T` be projective
and smooth of relative dimension `1`, with `H⁰(X̄_η, 𝒪) = κ(η)` on the generic fibre. Let
`j : U ⟶ X̄` be an open immersion and `i : Z ⟶ X̄` a reduced closed subscheme with support the
complement of the image of `j`, nonempty and étale over `T`. Then `j ≫ π` is an elementary
fibration. -/
theorem isElementaryFibration_of_smoothOfRelativeDimension_of_etale_of_isIso (k : Type u)
    [Field k] {T : Scheme.{u}} (τ : T ⟶ Spec (.of k)) [IsIntegral T] [IsNormal T] [Smooth τ]
    {Xt : Scheme.{u}} (π : Xt ⟶ T) (hπ : IsProjectiveMorphism π) [SmoothOfRelativeDimension 1 π]
    (hΓ : IsIso ((Scheme.ΓSpecIso (T.residueField (genericPoint T))).inv ≫
      (π.fiberToSpecResidueField (genericPoint T)).appTop))
    {U : Scheme.{u}} (j : U ⟶ Xt) [IsOpenImmersion j]
    {Z : Scheme.{u}} (i : Z ⟶ Xt) [IsClosedImmersion i] [IsReduced Z]
    (hZ : Set.range i.base = (Set.range j.base)ᶜ) [Etale (i ≫ π)] [Nonempty Z] :
    IsElementaryFibration (j ≫ π) := by
  have : IsProper π := isProper_of_isProjectiveMorphism π hπ
  have : Smooth π := SmoothOfRelativeDimension.smooth 1 π
  have : IsReduced Xt :=
    Stacks.SectionsVanishingOnSubscheme.isReduced_of_smooth_over_field k (π ≫ τ)
  have hgen : ∀ x : Xt, x ∈ genericPoints Xt → π x = genericPoint T := fun x hx => by
    have h := mem_genericPoints_of_flat π hx
    rwa [genericPoints_eq_singleton] at h
  have hgc := Stacks.SteinFactorization.geometricallyConnected_of_isNormal π hgen hΓ
  have hgi' : GeometricallyIrreducible π :=
    geometricallyIrreducible_of_geometricallyConnected_of_smooth π hgc
  have : IsFinite (i ≫ π) := IsFinite.of_isProper_of_locallyQuasiFinite _
  have hsurj : Surjective (i ≫ π) := ⟨Set.range_eq_univ.mp <| IsClopen.eq_univ
    ⟨(i ≫ π).isClosedMap.isClosed_range, (i ≫ π).isOpenMap.isOpen_range⟩ (Set.range_nonempty _)⟩
  exact ⟨⟨Xt, Z, j, π, i, inferInstance, rfl, inferInstance, hπ, hgi', inferInstance,
    inferInstance, hZ, inferInstance, inferInstance, hsurj⟩⟩

/-- **Spreading out an elementary fibration from one fibre.** Let `T` be a normal integral scheme,
smooth over a field `k`, let `π : X̄ ⟶ T` be projective with a section `σ`, and let `s ∈ T`. Let
`j : U ⟶ X̄` be an open immersion of an irreducible scheme meeting the fibre over `s`, and
`i : Z ⟶ X̄` a reduced closed subscheme with support the complement of the image of `j`. If `π`
is smooth with fibres of dimension `1` at every point over `s`, and `Z ⟶ T` is étale at its
points over `s`, some of which exist, then there are an affine open `S₀ ∋ s` of `T`, the open
`U₀ = (j ≫ π)⁻¹(S₀)` of `U` and an elementary fibration `U₀ ⟶ S₀` lying over `j ≫ π`. -/
theorem exists_isElementaryFibration_of_closedFibre (k : Type u) [Field k]
    {T : Scheme.{u}} (τ : T ⟶ Spec (.of k)) [IsIntegral T] [IsNormal T] [Smooth τ]
    {Xt : Scheme.{u}} (π : Xt ⟶ T) (hπ : IsProjectiveMorphism π) [LocallyOfFinitePresentation π]
    (σ : T ⟶ Xt) (hσ : σ ≫ π = 𝟙 T)
    {U : Scheme.{u}} (j : U ⟶ Xt) [IsOpenImmersion j] [IrreducibleSpace U]
    {Z : Scheme.{u}} (i : Z ⟶ Xt) [IsClosedImmersion i] [IsReduced Z]
    (hZ : Set.range i.base = (Set.range j.base)ᶜ) (s : T)
    (hsm : ∀ y : Xt, π y = s → y ∈ π.smoothLocus ∧
      topologicalKrullDimAt (π.fiber (π y)) (π.asFiber y) = ((1 : ℕ) : WithBot ℕ∞))
    (het : ∀ z : Z, π (i z) = s → EtaleAt (i ≫ π) z)
    (hne : ∃ z : Z, π (i z) = s) (hU : ∃ u : U, π (j u) = s) :
    ∃ (S₀ : T.Opens) (U₀ : Scheme.{u}) (e : U₀ ⟶ U) (f₀ : U₀ ⟶ S₀.toScheme),
      IsAffineOpen S₀ ∧ s ∈ S₀ ∧ IsOpenImmersion e ∧ IsElementaryFibration f₀ ∧
        f₀ ≫ S₀.ι = e ≫ j ≫ π ∧ Set.range e.base = (j ≫ π).base ⁻¹' (S₀ : Set T) := by
  have : IsProper π := isProper_of_isProjectiveMorphism π hπ
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian τ
  let G := {x : Xt | x ∈ π.smoothLocus ∧
    topologicalKrullDimAt (π.fiber (π x)) (π.asFiber x) = ((1 : ℕ) : WithBot ℕ∞)}
  have hGo : IsOpen G := isOpen_setOf_mem_smoothLocus_fiberDimensionAt_eq π 1
  let E := {z : Z | EtaleAt (i ≫ π) z}
  have hEo : IsOpen E := isOpen_setOf_etaleAt (i ≫ π)
  have h₁ : IsClosed (π.base '' Gᶜ) := π.isClosedMap _ hGo.isClosed_compl
  have h₂ : IsClosed ((i ≫ π).base '' Eᶜ) := (i ≫ π).isClosedMap _ hEo.isClosed_compl
  have hs₁ : s ∉ π.base '' Gᶜ := by
    rintro ⟨x, hx, hxs⟩
    exact hx (hsm x hxs)
  have hs₂ : s ∉ (i ≫ π).base '' Eᶜ := by
    rintro ⟨z, hz, hzs⟩
    exact hz (het z hzs)
  obtain ⟨S₀, hS₀, hsS₀, hS₀O⟩ : ∃ S₀ : T.Opens, IsAffineOpen S₀ ∧ s ∈ S₀ ∧
      (S₀ : Set T) ⊆ (π.base '' Gᶜ)ᶜ ∩ ((i ≫ π).base '' Eᶜ)ᶜ := by
    obtain ⟨_, ⟨S₀, hS₀, rfl⟩, hsS₀, hS₀O⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_inter hs₁ hs₂) (h₁.isOpen_compl.inter h₂.isOpen_compl)
    exact ⟨S₀, hS₀, hsS₀, hS₀O⟩
  have hgood : ∀ t ∈ (S₀ : Set T), t ∉ π.base '' Gᶜ ∧ t ∉ (i ≫ π).base '' Eᶜ :=
    fun t ht => hS₀O ht
  let ε := pullback.fst π S₀.ι
  let π₀ := pullback.snd π S₀.ι
  have hP : IsPullback ε π₀ π S₀.ι := IsPullback.of_hasPullback _ _
  have hnonempty : ∀ {W : Scheme.{u}} (g : W ⟶ Xt) (w : W), π (g w) = s →
      Nonempty ↥(pullback g ε) := fun g w hw => by
    obtain ⟨x₀, hx₀⟩ : g.base w ∈ Set.range ε.base := by
      rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι, Set.mem_preimage, hw]; exact hsS₀
    obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback w x₀ hx₀.symm
    exact ⟨w⟩
  have hεmem : ∀ x₀, π (ε x₀) ∈ (S₀ : Set T) := fun x₀ => by
    rw [← Scheme.Hom.comp_apply, hP.w, Scheme.Hom.comp_apply]
    exact (Scheme.Opens.range_ι S₀).le ⟨_, rfl⟩
  have hεG : ∀ x₀, ε x₀ ∈ G := fun x₀ => by
    by_contra h
    exact (hgood _ (hεmem x₀)).1 ⟨ε x₀, h, rfl⟩
  have : Smooth π₀ := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff,
      Scheme.Hom.smoothLocus_eq_preimage_of_isPullback hP (Or.inr inferInstance)]
    exact eq_top_iff.2 fun x₀ _ => (hεG x₀).1
  have : SmoothOfRelativeDimension 1 π₀ := by
    refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq π₀ 1 fun x₀ => ?_
    rw [fiberDimensionAt_eq_of_open_square ε π π₀ S₀.ι hP.w x₀]
    exact (hεG x₀).2
  have hπ₀ : IsProjectiveMorphism π₀ := hπ.baseChange S₀.ι
  have : Nonempty S₀ := ⟨⟨s, hsS₀⟩⟩
  have : IsAffine S₀.toScheme := hS₀
  have : IsIntegral S₀.toScheme := isIntegral_of_isOpenImmersion S₀.ι
  have : IsNormal S₀.toScheme := isNormal_of_isOpenImmersion S₀.ι
  let ζ := pullback.fst i ε
  let i₀ := pullback.snd i ε
  have hQ : IsPullback ζ i₀ i ε := IsPullback.of_hasPullback _ _
  have hQP : IsPullback ζ (i₀ ≫ π₀) (i ≫ π) S₀.ι := hQ.paste_vert hP
  have : Etale (i₀ ≫ π₀) := by
    rw [etale_iff_forall_etaleAt]
    intro z₀
    rw [← etaleAt_iff_of_isPullback hQP (Or.inr inferInstance)]
    by_contra h
    refine (hgood _ ?_).2 ⟨ζ z₀, h, rfl⟩
    rw [← Scheme.Hom.comp_apply, hQP.w, Scheme.Hom.comp_apply]
    exact (Scheme.Opens.range_ι S₀).le ⟨_, rfl⟩
  have : Nonempty ↥(pullback i ε) := hne.elim (hnonempty i)
  have : IsReduced (pullback i ε) := isReduced_of_isOpenImmersion ζ
  let e := pullback.fst j ε
  let j₀ := pullback.snd j ε
  have hR : IsPullback e j₀ j ε := IsPullback.of_hasPullback _ _
  have hrange : Set.range i₀.base = (Set.range j₀.base)ᶜ := by
    rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, hZ, Set.preimage_compl]
  have : Nonempty ↥(pullback j ε) := hU.elim (hnonempty j)
  have : IrreducibleSpace ↥(pullback j ε) := e.isOpenEmbedding.irreducibleSpace
  let σ₀ : S₀.toScheme ⟶ pullback π S₀.ι :=
    pullback.lift (S₀.ι ≫ σ) (𝟙 _) (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  have hσ₀ : σ₀ ≫ π₀ = 𝟙 _ := pullback.lift_snd _ _ _
  set η₀ := genericPoint S₀.toScheme
  have : IrreducibleSpace (π₀.fiber η₀) :=
    irreducibleSpace_fiber_genericPoint_of_isOpenImmersion π₀ j₀ i₀ hrange
  have hfsm : Smooth (π₀.fiberToSpecResidueField η₀) :=
    inferInstanceAs (Smooth (pullback.snd π₀ (S₀.toScheme.fromSpecResidueField η₀)))
  have : IsReduced (π₀.fiber η₀) :=
    Stacks.SectionsVanishingOnSubscheme.isReduced_of_smooth_over_field
      (S₀.toScheme.residueField η₀) (π₀.fiberToSpecResidueField η₀)
  have : IsIntegral (π₀.fiber η₀) := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsProper (π₀.fiberToSpecResidueField η₀) :=
    inferInstanceAs (IsProper (pullback.snd π₀ (S₀.toScheme.fromSpecResidueField η₀)))
  let s₀ : Spec (S₀.toScheme.residueField η₀) ⟶ π₀.fiber η₀ :=
    pullback.lift (S₀.toScheme.fromSpecResidueField η₀ ≫ σ₀) (𝟙 _)
      (by rw [Category.assoc, hσ₀, Category.comp_id, Category.id_comp])
  have hs₀ : s₀ ≫ π₀.fiberToSpecResidueField η₀ = 𝟙 _ := pullback.lift_snd _ _ _
  have hΓ₀ := isIso_globalSections_of_isIntegral_of_section (S₀.toScheme.residueField η₀)
    (π₀.fiberToSpecResidueField η₀) s₀ hs₀
  have hfib := isElementaryFibration_of_smoothOfRelativeDimension_of_etale_of_isIso k
    (S₀.ι ≫ τ) π₀ hπ₀ hΓ₀ j₀ i₀ hrange
  refine ⟨S₀, pullback j ε, e, j₀ ≫ π₀, hS₀, hsS₀, inferInstance, hfib, ?_, ?_⟩
  · rw [Category.assoc, ← hP.w, ← Category.assoc, ← hR.w, Category.assoc]
  · rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    rfl

/-- **An elementary fibration neighbourhood of a point from one fibre.** Let `X` be an irreducible
scheme over a field `k` and `x ∈ X`. Let `T` be a normal integral scheme smooth of relative
dimension `d - 1` over `k`, and `π : X̄ ⟶ T` projective with a section. Let `V ⊆ X` be an open
containing `x` with an open immersion `j : V ⟶ X̄` over `k`, and `i : Z ⟶ X̄` a reduced closed
subscheme with support the complement of the image of `j`. If `π` is smooth with fibres of
dimension `1` along the fibre through `j x`, and `Z` is étale over `T` along that fibre and meets
it, then some open `U ∋ x` of `X` is an elementary fibration over an irreducible affine scheme
smooth of relative dimension `d - 1` over `k`, compatibly with the structure morphisms: the
conclusion of `Stacks.EtaleCohomology.ExistsElementaryFibrationNeighbourhood` at `x`. -/
theorem exists_elementaryFibrationNeighbourhood_of_closedFibre (k : Type u) [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) (d : ℕ) [IrreducibleSpace X]
    {T : Scheme.{u}} (τ : T ⟶ Spec (.of k)) [IsIntegral T] [IsNormal T]
    [SmoothOfRelativeDimension (d - 1) τ]
    {Xt : Scheme.{u}} (π : Xt ⟶ T) (hπ : IsProjectiveMorphism π) [LocallyOfFinitePresentation π]
    (σ : T ⟶ Xt) (hσ : σ ≫ π = 𝟙 T)
    (V : X.Opens) (j : V.toScheme ⟶ Xt) [IsOpenImmersion j] (hj : j ≫ π ≫ τ = V.ι ≫ p)
    {Z : Scheme.{u}} (i : Z ⟶ Xt) [IsClosedImmersion i] [IsReduced Z]
    (hZ : Set.range i.base = (Set.range j.base)ᶜ) (x : X) (hx : x ∈ V)
    (hsm : ∀ y : Xt, π y = π (j ⟨x, hx⟩) → y ∈ π.smoothLocus ∧
      topologicalKrullDimAt (π.fiber (π y)) (π.asFiber y) = ((1 : ℕ) : WithBot ℕ∞))
    (het : ∀ z : Z, π (i z) = π (j ⟨x, hx⟩) → EtaleAt (i ≫ π) z)
    (hne : ∃ z : Z, π (i z) = π (j ⟨x, hx⟩)) :
    ∃ (U : X.Opens) (S : Scheme.{u}) (q : S ⟶ Spec (.of k)) (f : U.toScheme ⟶ S),
      x ∈ U ∧ IsElementaryFibration f ∧ SmoothOfRelativeDimension (d - 1) q ∧
        IsAffine S ∧ IrreducibleSpace S ∧ f ≫ q = U.ι ≫ p := by
  have : Smooth τ := SmoothOfRelativeDimension.smooth (d - 1) τ
  have : Nonempty V.toScheme := ⟨⟨x, hx⟩⟩
  have : IrreducibleSpace V.toScheme := V.ι.isOpenEmbedding.irreducibleSpace
  obtain ⟨S₀, U₀, e, f₀, hS₀, hsS₀, he, hf₀, hcomm, hrange⟩ :=
    exists_isElementaryFibration_of_closedFibre k τ π hπ σ hσ j i hZ (π (j ⟨x, hx⟩)) hsm het hne
      ⟨⟨x, hx⟩, rfl⟩
  have : IsOpenImmersion e := he
  let φ := (e ≫ V.ι).isoOpensRange
  have : IsAffine S₀.toScheme := hS₀
  have : Nonempty S₀ := ⟨⟨_, hsS₀⟩⟩
  have : IsIntegral S₀.toScheme := isIntegral_of_isOpenImmersion S₀.ι
  have hq : SmoothOfRelativeDimension (d - 1) (S₀.ι ≫ τ) := by
    have h : SmoothOfRelativeDimension (0 + (d - 1)) (S₀.ι ≫ τ) := inferInstance
    rwa [zero_add] at h
  refine ⟨(e ≫ V.ι).opensRange, S₀.toScheme, S₀.ι ≫ τ, φ.inv ≫ f₀, ?_, hf₀.precomp_iso φ.symm, hq,
    inferInstance, inferInstance, ?_⟩
  · have hv : (⟨x, hx⟩ : V.toScheme) ∈ Set.range e.base := by
      rw [hrange]
      change π (j ⟨x, hx⟩) ∈ (S₀ : Set T)
      exact hsS₀
    obtain ⟨u₀, hu₀⟩ := hv
    exact ⟨u₀, by rw [Scheme.Hom.comp_apply, hu₀]; rfl⟩
  · calc (φ.inv ≫ f₀) ≫ S₀.ι ≫ τ = φ.inv ≫ (f₀ ≫ S₀.ι) ≫ τ := by
          simp only [Category.assoc]
      _ = φ.inv ≫ e ≫ j ≫ π ≫ τ := by rw [hcomm]; simp only [Category.assoc]
      _ = φ.inv ≫ (e ≫ V.ι) ≫ p := by rw [hj, Category.assoc]
      _ = (e ≫ V.ι).opensRange.ι ≫ p := Scheme.Hom.isoOpensRange_inv_comp_assoc _ _

end AlgebraicGeometry

end
