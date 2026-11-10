module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.StalkIdeal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FibreStalkBridges
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ComponentDiscreteValuation
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ConormalDegree
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.IdealSheafStalkSupport

/-!
# The ideal of a component of the special fibre in a local ring of the source

In Situation [Stacks, Tag 0AX8], let `x` be a point of the `i`-th component `C_i` of the special
fibre lying on no other component, and let `Z = V(ℐ)` be a closed subscheme of `X` contained set
theoretically in the special fibre. Near `x` the support of `Z` lies inside `C_i`, so the ideal
`𝔭` of `C_i` in the local ring `𝒪_{X,x}` lies in the radical of the ideal `ℐ_x` that `Z` cuts out
there; and `𝔭` is a nonzero prime, `C_i` being an integral closed subscheme which is not the whole
of the integral scheme `X`.

These are the geometric inputs of the step "the section `s_i` has a zero at `x_i`" in the proof of
[Stacks, Tag 0AXA]: together with Krull's principal ideal theorem they show that the function of
Lemma 0AX9 is not a local generator of `ℐ_x` at the point `x_i` that lemma provides.

## Main results

* `AlgebraicGeometry.VanishingSituation.ker_stalkMap_componentι_le_radical`: `𝔭 ⊆ √ℐ_x`, with
  `ℐ_x` the kernel of the stalk map of `Z ⟶ X`.
* `AlgebraicGeometry.VanishingSituation.ker_stalkMap_componentι_le_radical_stalkIdeal`: the same
  for the stalk `I.stalkIdeal x` of the ideal sheaf, for every point of `C_i` on no other
  component.
* `AlgebraicGeometry.VanishingSituation.ker_stalkMap_componentι_ne_bot`: `𝔭 ≠ 0`.
* `AlgebraicGeometry.VanishingSituation.isPrime_ker_stalkMap_componentι`: `𝔭` is prime.

No `@[stacks]` attribute is placed here: these are steps of the proof of [Stacks, Tag 0AXA].

## References

* [Stacks Project, Tag 0AXA](https://stacks.math.columbia.edu/tag/0AXA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.VanishingSituation

variable (V : VanishingSituation.{u})

/-- The special fibre is covered by its irreducible components: every point of `X` over the closed
point of the base lies on the image of some component. -/
theorem exists_mem_componentInSource {x : V.X}
    (hx : x ∈ Set.range (V.f.fiberι V.closedPoint)) :
    ∃ j : Fin V.numberOfComponents, x ∈ componentInSource V j := by
  obtain ⟨p, rfl⟩ := hx
  obtain ⟨Z, hZ, hpZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({p} : Set V.specialFiber) isIrreducible_singleton
  obtain ⟨j, rfl⟩ := V.exists_component_eq Z hZ
  exact ⟨j, p, hpZ rfl, rfl⟩

/-- A point of the `i`-th component, read in `X`, lies on the support of the ideal of that
component. -/
theorem mem_support_componentι (i : Fin V.numberOfComponents) (y : componentScheme V i) :
    componentι V i y ∈ (componentIdeal V i).support := by
  have h : componentι V i y ∈ Set.range (componentIdeal V i).subschemeι := ⟨y, rfl⟩
  rwa [Scheme.IdealSheafData.range_subschemeι] at h

/-- **Near a point of `C_i` on no other component, a closed subscheme contained in the special
fibre lies inside `C_i`**: there is an affine open around the point meeting the support only in
`C_i`. -/
theorem exists_isAffineOpen_supportSet_inter_subset (I : V.X.IdealSheafData)
    (hZs : I.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint)) (i : Fin V.numberOfComponents)
    {x : V.X} (hx : ∀ j, j ≠ i → x ∉ componentInSource V j) :
    ∃ U : V.X.affineOpens, x ∈ U.1 ∧ (I.support : Set V.X) ∩ U.1 ⊆ componentInSource V i := by
  let T : Set V.X := ⋃ j : {j : Fin V.numberOfComponents // j ≠ i}, componentInSource V j
  have hT : IsClosed T := isClosed_iUnion_of_finite fun j => isClosed_componentInSource V j
  have hxT : x ∈ Tᶜ := by
    simp only [T, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    exact fun j => hx j.1 j.2
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUT⟩ :=
    V.X.isBasis_affineOpens.exists_subset_of_mem_open hxT hT.isOpen_compl
  refine ⟨⟨U, hU⟩, hxU, fun z ⟨hzI, hzU⟩ => ?_⟩
  obtain ⟨j, hj⟩ := exists_mem_componentInSource V (hZs hzI)
  by_cases hji : j = i
  · exact hji ▸ hj
  · exact absurd (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩) (hUT hzU)

/-- On an affine open meeting the support of `I` only in `C_i`, the ideal of `C_i` lies in the
radical of the ideal of `I`. -/
theorem ideal_componentIdeal_le_radical (I : V.X.IdealSheafData) (i : Fin V.numberOfComponents)
    (U : V.X.affineOpens) (hU : (I.support : Set V.X) ∩ U.1 ⊆ componentInSource V i) :
    (componentIdeal V i).ideal U ≤ (I.ideal U).radical := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal,
    ← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
  refine PrimeSpectrum.vanishingIdeal_anti_mono fun p hp => ?_
  have h1 : U.2.fromSpec p ∈ V.X.zeroLocus (U := U.1) (I.ideal U) ∩ U.1 := by
    rw [← U.2.fromSpec_image_zeroLocus]
    exact ⟨p, hp, rfl⟩
  rw [← Scheme.IdealSheafData.coe_support_inter] at h1
  change U.2.fromSpec p ∈ (componentClosed V i : Set V.X)
  rw [coe_componentClosed]
  exact hU h1

/-- **The ideal of `C_i` in the local ring at a point of `C_i` on no other component lies in the
radical of the ideal cut out there by a closed subscheme contained in the special fibre.** Both
ideals are kernels of stalk maps of closed immersions. -/
theorem ker_stalkMap_componentι_le_radical (I : V.X.IdealSheafData)
    (hZs : I.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint)) (i : Fin V.numberOfComponents)
    (y : componentScheme V i) (hy : ∀ j, j ≠ i → componentι V i y ∉ componentInSource V j)
    (hx : componentι V i y ∈ I.support) :
    RingHom.ker ((componentι V i).stalkMap y).hom ≤
      (Stacks.AlgebraicGeometry.stalkIdeal I (componentι V i y) hx).radical := by
  obtain ⟨U, hxU, hU⟩ := exists_isAffineOpen_supportSet_inter_subset V I hZs i hy
  have hk : RingHom.ker ((componentι V i).stalkMap y).hom =
      Stacks.AlgebraicGeometry.stalkIdeal (componentIdeal V i) (componentι V i y)
        (mem_support_componentι V i y) := rfl
  rw [hk, Stacks.AlgebraicGeometry.stalkIdeal_eq_map_germ (componentIdeal V i) _ _ U.2 hxU,
    Stacks.AlgebraicGeometry.stalkIdeal_eq_map_germ I _ _ U.2 hxU]
  exact (Ideal.map_mono (ideal_componentIdeal_le_radical V I i U hU)).trans
    (Ideal.map_radical_le _)

/-- **The ideal of `C_i` in the local ring at a point of `C_i` on no other component lies in the
radical of the stalk of the ideal sheaf of a closed subscheme contained in the special fibre**,
the stalk being `Scheme.IdealSheafData.stalkIdeal`. Off the support that stalk is the unit
ideal. -/
theorem ker_stalkMap_componentι_le_radical_stalkIdeal (I : V.X.IdealSheafData)
    (hZs : I.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint)) (i : Fin V.numberOfComponents)
    (y : componentScheme V i) (hy : ∀ j, j ≠ i → componentι V i y ∉ componentInSource V j) :
    RingHom.ker ((componentι V i).stalkMap y).hom ≤ (I.stalkIdeal (componentι V i y)).radical := by
  by_cases hx : componentι V i y ∈ I.support
  · have he : Stacks.AlgebraicGeometry.stalkIdeal I (componentι V i y) hx =
        I.stalkIdeal (componentι V i y) :=
      I.ker_stalkMap_subschemeι (⟨componentι V i y, hx⟩ : I.subscheme)
    exact he ▸ ker_stalkMap_componentι_le_radical V I hZs i y hy hx
  · rw [I.stalkIdeal_eq_top_of_notMem_support hx, Ideal.radical_top]
    exact le_top

/-- **The ideal of `C_i` in a local ring of `X` at a point of `C_i` is nonzero**: otherwise the
ideal of `C_i` would vanish on an affine open of the integral scheme `X`, so that open, and with
it the generic point of `X`, would lie in `C_i` and hence over the closed point of the base,
whereas the generic point of `X` lies over the generic point of the base. -/
theorem ker_stalkMap_componentι_ne_bot (i : Fin V.numberOfComponents) (y : componentScheme V i) :
    RingHom.ker ((componentι V i).stalkMap y).hom ≠ ⊥ := by
  intro h0
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    V.X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (componentι V i y))
      isOpen_univ
  have hk : RingHom.ker ((componentι V i).stalkMap y).hom =
      Stacks.AlgebraicGeometry.stalkIdeal (componentIdeal V i) (componentι V i y)
        (mem_support_componentι V i y) := rfl
  rw [hk, Stacks.AlgebraicGeometry.stalkIdeal_eq_map_germ _ _ _ hU hxU] at h0
  have hbot : (componentIdeal V i).ideal ⟨U, hU⟩ = ⊥ := by
    refine eq_bot_iff.mpr fun a ha => ?_
    have hmem : (V.X.presheaf.germ U _ hxU).hom a ∈ (⊥ : Ideal _) :=
      h0 ▸ Ideal.mem_map_of_mem _ ha
    exact (map_eq_zero_iff _ (germ_injective_of_isIntegral V.X _ hxU)).mp hmem
  have hgen : genericPoint V.X ∈ U :=
    ((genericPoint_spec V.X).mem_open_set_iff U.2).mpr ⟨_, Set.mem_univ _, hxU⟩
  have hsupp : genericPoint V.X ∈ (componentIdeal V i).support := by
    refine (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hgen).mpr ?_
    rw [Scheme.mem_zeroLocus_iff]
    intro a ha
    rw [hbot] at ha
    rw [show a = 0 from ha, Scheme.basicOpen_zero]
    exact fun h => h
  have hsupp' : genericPoint V.X ∈ ((componentIdeal V i).support : Set V.X) := hsupp
  rw [coe_support_componentIdeal] at hsupp'
  obtain ⟨p, -, hp⟩ := hsupp'
  have hfp : V.f (genericPoint V.X) = V.closedPoint := by
    have h : genericPoint V.X ∈ Set.range (V.f.fiberι V.closedPoint) := ⟨p, hp⟩
    rwa [Scheme.Hom.range_fiberι] at h
  rw [IsBirational.genericPoint_eq V.f V.modification.isBirational] at hfp
  exact V.genericPoint_base_ne_closedPoint hfp

/-- The ideal of `C_i` in a local ring of `X` at a point of `C_i` is prime, `C_i` being an
integral scheme. -/
instance isPrime_ker_stalkMap_componentι (i : Fin V.numberOfComponents)
    (y : componentScheme V i) : (RingHom.ker ((componentι V i).stalkMap y).hom).IsPrime :=
  RingHom.ker_isPrime _

end AlgebraicGeometry.VanishingSituation

end
