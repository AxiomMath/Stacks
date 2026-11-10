module

public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.PointwiseEtale

/-!
# A reduced closed subscheme is étale where an étale one with the same support is

Let `g : P ⟶ T` with `T` reduced, `i : Z ⟶ P` a reduced closed subscheme, and `J` a closed
subscheme of `P` with the same support as `Z` near a point. If `V(J) ⟶ T` is étale at that point,
then so is `Z ⟶ T`: near the point `V(J)` is étale over the reduced `T`, hence reduced, and two
reduced closed subschemes with the same support coincide ([Stacks, Tag 01J3], uniqueness of the
reduced structure). In SGA 4, Exposé XI, Proposition 3.3 this is how the reduced boundary
`Z = X̄_T ∖ X` of the incidence family is seen to be étale over the base: near each point of the
fibre it is cut out by explicit equations (`Y × T` or `V(w₀)` intersected with the family) whose
étaleness is the fibrewise smoothness criterion.

## Main results

* `AlgebraicGeometry.GoodNeighbourhood.etaleAt_of_inter_eq_support`.

## References

* SGA 4, Tome 3, Exposé XI, Proposition 3.3.
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

/-- **A reduced closed subscheme with the support of an étale one is étale there.** Let
`g : P ⟶ T` with `T` reduced, `i : Z ⟶ P` a closed immersion of a reduced scheme, `J` an ideal
sheaf on `P` and `U ⊆ P` open with `range i ∩ U = V(J) ∩ U`. If `V(J) ⟶ T` is étale at a point
`z'` lying over `i z ∈ U`, then `Z ⟶ T` is étale at `z`. -/
theorem etaleAt_of_inter_eq_support {P T Z : Scheme.{u}} (g : P ⟶ T) [IsReduced T]
    (i : Z ⟶ P) [IsClosedImmersion i] [IsReduced Z] (J : P.IdealSheafData) (U : P.Opens)
    (hU : Set.range i.base ∩ (U : Set P) = (J.support : Set P) ∩ (U : Set P)) (z : Z)
    (hzU : i z ∈ U) (z' : J.subscheme) (hz' : J.subschemeι z' = i z)
    (het : EtaleAt (J.subschemeι ≫ g) z') : EtaleAt (i ≫ g) z := by
  -- an étale open of `V(J)` around `z'`
  obtain ⟨U₀, hU₀, hzU₀, V₀, hV₀, hUV, hEt⟩ := het
  have hEt₀ : Etale (U₀.ι ≫ J.subschemeι ≫ g) := by
    have := etale_resLE_of_appLE_etale _ U₀ hU₀ V₀ hV₀ hUV hEt
    rw [← Scheme.Hom.resLE_comp_ι _ hUV]
    infer_instance
  obtain ⟨O', hO', hO'eq⟩ := isOpen_induced_iff.mp
    (show IsOpen (U₀ : Set J.subscheme) from U₀.isOpen)
  let U' : P.Opens := U ⊓ ⟨O', hO'⟩
  have hzU' : i z ∈ U' := ⟨hzU, by
    rw [← hz']
    change J.subschemeι z' ∈ O'
    have : z' ∈ (U₀ : Set J.subscheme) := hzU₀
    rw [← hO'eq] at this
    exact this⟩
  let JU := J.subschemeι ⁻¹ᵁ U'
  have hJU : JU ≤ U₀ := fun y hy => by
    change y ∈ (U₀ : Set J.subscheme)
    rw [← hO'eq]
    exact hy.2
  have : Etale (JU.ι ≫ J.subschemeι ≫ g) := by
    rw [← J.subscheme.homOfLE_ι hJU, Category.assoc]
    infer_instance
  have : IsReduced JU.toScheme := isReduced_of_etale (JU.ι ≫ J.subschemeι ≫ g)
  let ZU := i ⁻¹ᵁ U'
  -- `ZU ⟶ V(J)`
  obtain ⟨m₁, hm₁⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support J
    (ZU.ι ≫ i)).2 (by
      rintro _ ⟨y, rfl⟩
      have h : i (ZU.ι y) ∈ Set.range i.base ∩ (U : Set P) := ⟨⟨_, rfl⟩, y.2.1⟩
      rw [hU] at h
      exact h.1)
  have hm₁r : Set.range m₁.base ⊆ Set.range JU.ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    change J.subschemeι (m₁ y) ∈ U'
    rw [← Scheme.Hom.comp_apply, hm₁]
    exact y.2
  let m₁' : ZU.toScheme ⟶ JU.toScheme := IsOpenImmersion.lift JU.ι m₁ hm₁r
  have hm₁' : m₁' ≫ JU.ι = m₁ := IsOpenImmersion.lift_fac _ _ _
  -- `JU ⟶ Z`
  obtain ⟨m, hm⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support i.ker
    (JU.ι ≫ J.subschemeι)).2 (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
      have h : J.subschemeι (JU.ι y) ∈ (J.support : Set P) ∩ (U : Set P) :=
        ⟨by rw [← J.range_subschemeι]; exact ⟨_, rfl⟩, y.2.1⟩
      rw [← hU] at h
      exact h.1)
  have hk : i.ker ≤ (JU.ι ≫ J.subschemeι).ker := by
    calc i.ker = i.ker.subschemeι.ker := i.ker.ker_subschemeι.symm
      _ ≤ (m ≫ i.ker.subschemeι).ker := Scheme.Hom.le_ker_comp _ _
      _ = (JU.ι ≫ J.subschemeι).ker := by rw [hm]
  let m₂ : JU.toScheme ⟶ Z := IsClosedImmersion.lift i (JU.ι ≫ J.subschemeι) hk
  have hm₂ : m₂ ≫ i = JU.ι ≫ J.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have hm₂r : Set.range m₂.base ⊆ Set.range ZU.ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    change i (m₂ y) ∈ U'
    rw [← Scheme.Hom.comp_apply, hm₂]
    exact y.2
  let m₂' : JU.toScheme ⟶ ZU.toScheme := IsOpenImmersion.lift ZU.ι m₂ hm₂r
  have hm₂' : m₂' ≫ ZU.ι = m₂ := IsOpenImmersion.lift_fac _ _ _
  have h12 : m₁' ≫ m₂' = 𝟙 _ := by
    rw [← cancel_mono (ZU.ι ≫ i), Category.assoc, reassoc_of% hm₂', hm₂, reassoc_of% hm₁', hm₁,
      Category.id_comp]
  have h21 : m₂' ≫ m₁' = 𝟙 _ := by
    rw [← cancel_mono (JU.ι ≫ J.subschemeι), Category.assoc, reassoc_of% hm₁', hm₁,
      reassoc_of% hm₂', hm₂, Category.id_comp]
  have : IsIso m₁' := ⟨⟨m₂', h12, h21⟩⟩
  have hZU : ZU.ι ≫ i ≫ g = m₁' ≫ JU.ι ≫ J.subschemeι ≫ g := by
    rw [reassoc_of% hm₁', reassoc_of% hm₁]
  have : Etale (ZU.ι ≫ i ≫ g) := by rw [hZU]; infer_instance
  have h := (etale_iff_forall_etaleAt (ZU.ι ≫ i ≫ g)).1 inferInstance ⟨z, hzU'⟩
  exact Stacks.FundamentalGroup.ExtendedEtaleFold.etaleAt_of_etaleAt_isOpenImmersion_comp ZU.ι
    (i ≫ g) ⟨z, hzU'⟩ h

end AlgebraicGeometry.GoodNeighbourhood

end
