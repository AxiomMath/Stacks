module

public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibrewiseDenseRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.DenseFlatLocus

/-!
# Generic flatness with constant relative dimension

A dominant morphism locally of finite type between integral schemes becomes, after shrinking the
source and the target to suitable nonempty opens, flat of some relative dimension `d`.

## Main results

* `AlgebraicGeometry.exists_nonempty_opens_flat_relativeDimension`: nonempty opens `U' ⊆ U` and
  `V' ⊆ V` with `h(U') ⊆ V'` such that `U' ⟶ V'` is flat and of relative dimension `d`.

## Implementation notes

After shrinking to nonempty affine opens the morphism is of finite type, so generic flatness
gives a dense open of the target over which it is flat and of finite presentation. A flat
morphism locally of finite presentation has open pieces of each relative dimension whose union
is dense in every fibre, and since the source is nonempty one of these pieces is nonempty.

## References

* [Stacks Project, Tag 052A](https://stacks.math.columbia.edu/tag/052A)
* [Stacks Project, Tag 052B](https://stacks.math.columbia.edu/tag/052B)
* [Stacks Project, Tag 054T](https://stacks.math.columbia.edu/tag/054T)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Relative dimension in the sense of Tag 02NJ is preserved by composing with an open immersion
of the target: each fibre of the composite is empty or homeomorphic to a fibre of the original
morphism. -/
private theorem RelativeDimension.comp_isOpenImmersion_right {X S T : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (i : S ⟶ T) [IsOpenImmersion i] {d : ℕ}
    (hf : RelativeDimension f d) : RelativeDimension (f ≫ i) d := by
  intro t hne
  obtain ⟨w⟩ := hne
  set v : S := f ((f ≫ i).fiberι t w)
  have hmem : (f ≫ i).fiberι t w ∈ (f ≫ i) ⁻¹' {t} := by
    rw [← (f ≫ i).range_fiberι t]
    exact ⟨w, rfl⟩
  have hiv : i v = t := by
    simpa [v, Scheme.Hom.comp_apply] using hmem
  have hset : ((f ≫ i) ⁻¹' {t} : Set X) = f ⁻¹' {v} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.comp_apply, ← hiv]
    exact i.isOpenEmbedding.injective.eq_iff
  let e : (f ≫ i).fiber t ≃ₜ f.fiber v :=
    ((f ≫ i).fiberHomeo t).trans ((Homeomorph.setCongr hset).trans (f.fiberHomeo v).symm)
  obtain ⟨heq, hdim⟩ := hf v ⟨e w⟩
  exact ⟨heq.of_homeomorph e, (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).trans hdim⟩

/-- The range of an open immersion `j` into `U` lies over the range of an open immersion `i`
through which `j ≫ h` factors. -/
theorem Scheme.Hom.opensRange_le_preimage_opensRange {P U W V : Scheme.{u}} (h : U ⟶ V)
    (j : P ⟶ U) [IsOpenImmersion j] (i : W ⟶ V) [IsOpenImmersion i] (k : P ⟶ W)
    (hcomm : j ≫ h = k ≫ i) : j.opensRange ≤ h ⁻¹ᵁ i.opensRange := by
  rintro _ ⟨z, rfl⟩
  exact ⟨k z, by rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply]⟩

/-- The restriction of `h` to the ranges of open immersions `j` and `i` with `j ≫ h = k ≫ i` is
`k`, up to the isomorphisms onto the ranges. -/
theorem Scheme.Hom.resLE_opensRange_eq {P U W V : Scheme.{u}} (h : U ⟶ V)
    (j : P ⟶ U) [IsOpenImmersion j] (i : W ⟶ V) [IsOpenImmersion i] (k : P ⟶ W)
    (hcomm : j ≫ h = k ≫ i) (hle : j.opensRange ≤ h ⁻¹ᵁ i.opensRange) :
    h.resLE i.opensRange j.opensRange hle = j.isoOpensRange.inv ≫ k ≫ i.isoOpensRange.hom := by
  rw [← cancel_mono i.opensRange.ι, Scheme.Hom.resLE_comp_ι]
  simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  rw [← hcomm, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]

/-- **Generic flatness with relative dimension.** A morphism `h : U ⟶ V` locally of finite type
between integral schemes, with `V` locally Noetherian, mapping the generic point of `U` to the
generic point of `V`, restricts over suitable nonempty opens `U' ⊆ h ⁻¹ V'` to a flat morphism
`U' ⟶ V'` of some relative dimension `d`. -/
public theorem exists_nonempty_opens_flat_relativeDimension {U V : Scheme.{u}} [IsIntegral U]
    [IsIntegral V] (h : U ⟶ V) [LocallyOfFiniteType h]
    (hdom : h (genericPoint U) = genericPoint V) :
    ∃ (U' : U.Opens) (V' : V.Opens) (hle : U' ≤ h ⁻¹ᵁ V') (d : ℕ),
      (U' : Set U).Nonempty ∧ Flat (h.resLE V' U' hle) ∧
      AlgebraicGeometry.RelativeDimension (h.resLE V' U' hle) d := by
  obtain ⟨V₀ : V.Opens, hV₀, hxV₀, -⟩ :=
    Opens.isBasis_iff_nbhd.mp V.isBasis_affineOpens (Opens.mem_top (genericPoint V))
  have hxU : genericPoint U ∈ h ⁻¹ᵁ V₀ := by
    change h (genericPoint U) ∈ V₀
    rwa [hdom]
  obtain ⟨U₀ : U.Opens, hU₀, hxU₀, hU₀le⟩ :=
    Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens hxU
  have : IsAffine V₀ := hV₀
  have : IsAffine U₀ := hU₀
  have : Nonempty V₀ := ⟨⟨_, hxV₀⟩⟩
  have : Nonempty U₀ := ⟨⟨_, hxU₀⟩⟩
  let g : (U₀ : Scheme) ⟶ V₀ := h.resLE V₀ U₀ hU₀le
  have : LocallyOfFiniteType g := inferInstance
  have : QuasiCompact g := inferInstance
  obtain ⟨W, hW, hflat, hfp⟩ := exists_dense_open_flat_finitePresentation_structureSheaf g
  have hgx : g ⟨genericPoint U, hxU₀⟩ = ⟨genericPoint V, hxV₀⟩ := by
    apply Subtype.ext
    simp [g, hdom]
  obtain ⟨w, hw, hwV⟩ : genericPoint V ∈ V₀.ι ''ᵁ W := by
    obtain ⟨w, hw⟩ := hW.nonempty
    exact ((genericPoint_spec V).mem_open_set_iff (V₀.ι ''ᵁ W).isOpen).mpr
      ⟨_, trivial, w, hw, rfl⟩
  have hx₀ : g ⟨genericPoint U, hxU₀⟩ ∈ W := by
    rwa [hgx, ← show w = ⟨genericPoint V, hxV₀⟩ from Subtype.ext hwV]
  let k : (g ⁻¹ᵁ W : Scheme) ⟶ W := g.resLE W (g ⁻¹ᵁ W) le_rfl
  have : LocallyOfFinitePresentation k := hfp.locallyOfFinitePresentation
  obtain ⟨P, hdense, hrel⟩ := exists_open_relativeDimension_fiberwise_dense k
  let x₀ : (g ⁻¹ᵁ W : Scheme) := ⟨⟨genericPoint U, hxU₀⟩, hx₀⟩
  have : Nonempty (k.fiber (k x₀)) := ⟨k.asFiber x₀⟩
  obtain ⟨y, hy⟩ := (hdense (k x₀)).nonempty
  obtain ⟨d, hd⟩ := (Opens.mem_iSup (s := P)).mp hy
  let j : (P d : Scheme) ⟶ U := (P d).ι ≫ (g ⁻¹ᵁ W).ι ≫ U₀.ι
  let iW : (W : Scheme) ⟶ V := W.ι ≫ V₀.ι
  let k' : (P d : Scheme) ⟶ W := (P d).ι ≫ k
  have hcomm : j ≫ h = k' ≫ iW := by
    simp only [j, iW, k', k, g, Category.assoc, Scheme.Hom.resLE_comp_ι_assoc,
      Scheme.Hom.resLE_comp_ι]
  have hle := Scheme.Hom.opensRange_le_preimage_opensRange h j iW k' hcomm
  have hρ := Scheme.Hom.resLE_opensRange_eq h j iW k' hcomm hle
  refine ⟨j.opensRange, iW.opensRange, hle, d, ⟨j ⟨_, hd⟩, ⟨_, hd⟩, rfl⟩, ?_, ?_⟩
  · rw [hρ]
    infer_instance
  · convert RelativeDimension.comp_isOpenImmersion j.isoOpensRange.inv _
      (RelativeDimension.comp_isOpenImmersion_right k' iW.isoOpensRange.hom (hrel d))

end AlgebraicGeometry

end
