module

public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.Functoriality

/-!
# The canonical composite of conormal algebras of a nested pair vanishes above degree zero

Let `Z ⊆ Y ⊆ X` be a chain of closed immersions, written `p : Z ⟶ Y`, `iY : Y ⟶ X` and
`iZ = p ≫ iY`. [Stacks, Tag 0634] attaches a canonical map of conormal graded algebras to each of
the two commutative squares

```
Z --iZ--> X        Z --p--> Y
|         |        |        |
p         𝟙 X      𝟙 Z      iY
v         v        v        v
Y --iY--> X        Z --iZ-> X
```

the first a map `𝒞_{Y/X,*} ⟶ p_* 𝒞_{Z/X,*}` and the second a map `𝒞_{Z/X,*} ⟶ 𝒞_{Z/Y,*}`. This
file proves that **their composite `𝒞_{Y/X,n} ⟶ 𝒞_{Z/X,n} ⟶ 𝒞_{Z/Y,n}` is zero for every
`n ≠ 0`.**

This is the scheme-level input of [Stacks, Tag 0FEB] that the conormal sequence of
[Stacks, Tag 06AE] supplies only in degree one: the composite
`𝒞_{Y/X}|_Z ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` of that sequence is zero, and the statement below is the same
vanishing in every degree, proved directly from the chart description rather than transported from
the degree-one sequence.

## Main results

* `AlgebraicGeometry.conormalAlgebraHom_comp_map_eq_zero`: **the composite vanishes.**

## Implementation notes

**Why the chart computation and not the conormal sequence.** On an affine chart the canonical map
is computed by `AlgebraicGeometry.ConormalAlgebraHom.IsCanonical` as *reduction of a
representative*: a degree-`n` section of `𝒞_{Y/X,*}` over a chart is the class of an element
`a ∈ ℐ_Y^n`, and the composite sends it to the class of the image of `a` under
`iY^♯ : 𝒪_X ⟶ 𝒪_Y` read on `Z`. For `n ≠ 0` that image is `0`, because `ℐ_Y^n ⊆ ℐ_Y` and
`ℐ_Y` is by definition the kernel of `iY^♯` on the chart. The formula is uniform in `n`, so
degree one is no easier than degree `n`, and identifying the degree-one component of
`AlgebraicGeometry.conormalAlgebraHom` with `Stacks.Immersion.conormalSequenceLeftMap` and
`Stacks.Immersion.conormalSequenceRightMap` — which would be needed to read the vanishing off the
conormal sequence — is strictly more work than the chart computation.

**The two charts.** The two canonical maps are canonical for *different* squares, so their chart
descriptions are indexed differently: the map out of `𝒞_{Y/X,*}` is described at a pair of affine
opens of `X` (its ambient morphism is `𝟙 X`), while the map into `𝒞_{Z/Y,*}` is described at an
affine open of `Y` lying over one of `X` (its ambient morphism is `iY`). Matching them is what the
proof below does, and it is why a single application of either description does not suffice: the
cover used is the chart cover of the *composite* square, whose charts are an affine `U ⊆ Y` over
an affine `U' ⊆ X`, and the common open on which the two descriptions are compared is `iZ⁻¹U'`.
That comparison is available only because the statement is read on `V := p⁻¹W`, for which
`iZ⁻¹U' ≤ V` follows from `iY⁻¹U' ≤ W`; on a general `V ≤ p⁻¹W` the two charts have no common
refinement among the charts of one square.

## References

* [Stacks Project, Tag 0634](https://stacks.math.columbia.edu/tag/0634)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 06AE](https://stacks.math.columbia.edu/tag/06AE)
* [Stacks Project, Tag 0FEB](https://stacks.math.columbia.edu/tag/0FEB)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace TopologicalSpace.Opens

universe u

namespace AlgebraicGeometry

/-- The coborder of the range of a closed immersion is everything, its range being closed. -/
private theorem coborderRange_eq_top_of_isClosedImmersion {A B : Scheme.{u}} (i : A ⟶ B)
    [IsClosedImmersion i] : i.coborderRange = ⊤ := by
  ext x
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  show x ∈ coborder (Set.range i.base)
  rw [IsClosed.coborder_eq i.isClosedEmbedding.isClosed_range]
  trivial

/-- A closed immersion restricts to a closed immersion over every open of the target. -/
private theorem isClosedImmersion_resLE_of_isClosedImmersion {A B : Scheme.{u}} (i : A ⟶ B)
    [IsClosedImmersion i] (U : B.Opens) :
    IsClosedImmersion (i.resLE U (i ⁻¹ᵁ U) le_rfl) :=
  isClosedImmersion_resLE_of_le_coborderRange i U
    ((coborderRange_eq_top_of_isClosedImmersion i) ▸ le_top)

section

variable {Z Y X : Scheme.{u}} (iY : Y ⟶ X) (p : Z ⟶ Y)
  [IsClosedImmersion iY] [IsClosedImmersion p]

omit [IsClosedImmersion iY] [IsClosedImmersion p] in
/-- **The chart ideal of the larger subscheme is contained in that of the smaller one.** On an
affine open `U ⊆ X` the ideal of `Y` is the kernel of `iY^♯` and the ideal of `Z` the kernel of
`(p ≫ iY)^♯`, which factors through it. -/
private theorem chartIdeal_le_chartIdeal_comp (U : X.affineOpens) :
    Stacks.Conormal.chartIdeal iY U ≤ Stacks.Conormal.chartIdeal (p ≫ iY) U := by
  intro a ha
  have h : (iY.app U.1).hom a = 0 := RingHom.mem_ker.mp ha
  show ((p ≫ iY).app U.1).hom a = 0
  have h2 : ((p ≫ iY).app U.1).hom a =
      (p.app (iY ⁻¹ᵁ U.1)).hom ((iY.app U.1).hom a) := rfl
  rw [h2, h, map_zero]
  rfl


/-- Restricting the image of a section under a canonical map of conormal algebras equals the image
of the restricted section, on any smaller source and target opens. -/
private theorem map_restrict_map_eq_map_restrict {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X}
    {i' : Z' ⟶ X'} {f : Z ⟶ Z'} [IsImmersion i] [IsImmersion i'] (H : ConormalAlgebraHom i i' f)
    (n : ℤ) {V V' : Z.Opens} {W W' : Z'.Opens} (hV'V : V' ≤ V) (hW'W : W' ≤ W)
    (hVW : V ≤ f ⁻¹ᵁ W) (hV'W : V' ≤ f ⁻¹ᵁ W) (hV'W' : V' ≤ f ⁻¹ᵁ W')
    (a : ((Stacks.Conormal.conormalAlgebra i').algebra.piece n).val.obj (op W)) :
    ((Stacks.Conormal.conormalAlgebra i).algebra.piece n).val.map (homOfLE hV'V).op
        (H.map n V W hVW a) =
      H.map n V' W' hV'W'
        (((Stacks.Conormal.conormalAlgebra i').algebra.piece n).val.map (homOfLE hW'W).op a) :=
  (H.map_restrict_target n V V' hV'V W hVW a).trans
    (H.map_restrict_source n V' W W' hW'W hV'W' hV'W a).symm

/-- **The composite of the two canonical maps of conormal graded algebras of a chain of closed
immersions `Z ⊆ Y ⊆ X` vanishes in every nonzero degree.**

The first map is the canonical `𝒞_{Y/X,*} ⟶ p_* 𝒞_{Z/X,*}` of [Stacks, Tag 0634] for the square
with `p` on the left and `𝟙 X` on the right; the second is the canonical
`𝒞_{Z/X,*} ⟶ 𝒞_{Z/Y,*}` for the square with `𝟙 Z` on the left and `iY` on the right. On an
affine chart the composite is reduction of a representative along `iY^♯`, and a representative of
a degree-`n` section with `n ≠ 0` lies in the ideal of `Y`, which is the kernel of `iY^♯`. -/
theorem conormalAlgebraHom_comp_map_eq_zero {iZ : Z ⟶ X} [IsClosedImmersion iZ]
    (hp : p ≫ iY = iZ) (n : ℕ) (hn : n ≠ 0) (W : Y.Opens)
    (hle : p ⁻¹ᵁ W ≤ (𝟙 Z) ⁻¹ᵁ (p ⁻¹ᵁ W))
    (x : ((Stacks.Conormal.conormalAlgebra iY).algebra.piece (n : ℤ)).val.obj (op W)) :
    (conormalAlgebraHom p iZ (𝟙 Z) iY ((Category.id_comp iZ).trans hp.symm)).hom.map
        (n : ℤ) (p ⁻¹ᵁ W) (p ⁻¹ᵁ W) hle
        ((conormalAlgebraHom iZ iY p (𝟙 X) (hp.trans (Category.comp_id iZ).symm)).hom.map
          (n : ℤ) (p ⁻¹ᵁ W) W le_rfl x) = 0 := by
  subst hp
  refine conormal_sections_ext_of_affineCharts p iY p iY rfl (n : ℤ) (p ⁻¹ᵁ W) W le_rfl _ 0
    fun U U' hU hU' hcob hcob' hg => ?_
  -- The closed-immersion charts.
  have hpU : IsClosedImmersion (p.resLE U.1 (p ⁻¹ᵁ U.1) le_rfl) :=
    isClosedImmersion_resLE_of_le_coborderRange p U.1 hcob
  have hiYU : IsClosedImmersion (iY.resLE U'.1 (iY ⁻¹ᵁ U'.1) le_rfl) :=
    isClosedImmersion_resLE_of_le_coborderRange iY U'.1 hcob'
  have hiZU : IsClosedImmersion
      ((p ≫ iY).resLE U'.1 ((p ≫ iY) ⁻¹ᵁ U'.1) le_rfl) :=
    isClosedImmersion_resLE_of_isClosedImmersion (p ≫ iY) U'.1
  -- The inclusions of opens.
  have hFU₂ : (p ≫ iY) ⁻¹ᵁ U'.1 ≤ p ⁻¹ᵁ (iY ⁻¹ᵁ U'.1) := le_of_eq (p.comp_preimage iY U'.1)
  have hVZ : (p ≫ iY) ⁻¹ᵁ U'.1 ≤ p ⁻¹ᵁ W :=
    le_trans hFU₂ (p.preimage_mono hU')
  have hFU₁ : p ⁻¹ᵁ U.1 ≤ (𝟙 Z) ⁻¹ᵁ ((p ≫ iY) ⁻¹ᵁ U'.1) := by
    refine le_trans (p.preimage_mono hg) ?_
    exact le_of_eq (p.comp_preimage iY U'.1).symm
  -- A representative of the restricted section.
  obtain ⟨a, ha⟩ := (Stacks.Conormal.conormalAlgebra iY).localMap_surjective U' hiYU n
    (((Stacks.Conormal.conormalAlgebra iY).algebra.piece (n : ℤ)).val.map
      (homOfLE hU').op x)
  have hGU : U'.1 ≤ (𝟙 X) ⁻¹ᵁ U'.1 := le_rfl
  -- Its image under the ambient identity is itself.
  have hid : ((𝟙 X : X ⟶ X).app U'.1 ≫ X.presheaf.map (homOfLE hGU).op) =
      X.presheaf.map (homOfLE (le_refl U'.1)).op := rfl
  have hid' : X.presheaf.map (homOfLE (le_refl U'.1)).op = 𝟙 _ := by
    have hone : (homOfLE (le_refl U'.1) : U'.1 ⟶ U'.1) = 𝟙 _ := Subsingleton.elim _ _
    rw [hone, op_id, X.presheaf.map_id]
  have hba : (X.presheaf.map (homOfLE hGU).op).hom
      (((𝟙 X : X ⟶ X).app U'.1).hom (a : Γ(X, U'.1))) = (a : Γ(X, U'.1)) := by
    rw [← ConcreteCategory.comp_apply, hid, hid']
    rfl
  -- The representative lies in the ideal of `Y`, hence dies under `iY`.
  have haY : (a : Γ(X, U'.1)) ∈ Stacks.Conormal.chartIdeal iY U' :=
    Ideal.pow_le_self hn a.2
  have hmem : (X.presheaf.map (homOfLE hGU).op).hom
      (((𝟙 X : X ⟶ X).app U'.1).hom (a : Γ(X, U'.1))) ∈
      Stacks.Conormal.chartIdeal (p ≫ iY) U' ^ n := by
    rw [hba]
    exact pow_le_pow_left' (chartIdeal_le_chartIdeal_comp iY p U') n a.2
  -- The two chart descriptions.
  have hcan₂ := (conormalAlgebraHom (p ≫ iY) iY p (𝟙 X)
      (Category.comp_id (p ≫ iY)).symm).chart U' U' hGU hiZU hiYU hFU₂ n a
    ⟨_, hmem⟩ rfl
  have hker : (iY.app U'.1).hom
      ((show ↥(Stacks.Conormal.chartIdeal (p ≫ iY) U' ^ n) from ⟨_, hmem⟩ :
        Γ(X, U'.1))) = 0 := by
    show (iY.app U'.1).hom ((X.presheaf.map (homOfLE hGU).op).hom
      (((𝟙 X : X ⟶ X).app U'.1).hom (a : Γ(X, U'.1)))) = 0
    rw [hba]
    exact RingHom.mem_ker.mp haY
  have hc : ((0 : ↥(Stacks.Conormal.chartIdeal p U ^ n)) : Γ(Y, U.1)) =
      Y.presheaf.map (homOfLE hg).op
        ((iY.app U'.1).hom
          ((show ↥(Stacks.Conormal.chartIdeal (p ≫ iY) U' ^ n) from ⟨_, hmem⟩ :
            Γ(X, U'.1)))) := by
    rw [hker]
    exact (map_zero _).symm
  have hcan₁ := (conormalAlgebraHom p (p ≫ iY) (𝟙 Z) iY
      (Category.id_comp (p ≫ iY))).chart U U' hg hpU hiZU hFU₁ n
    ⟨_, hmem⟩ 0 hc
  -- Assemble.
  rw [map_restrict_map_eq_map_restrict (conormalAlgebraHom p (p ≫ iY) (𝟙 Z) iY
      (Category.id_comp (p ≫ iY))).hom (n : ℤ) hU hVZ hle (le_trans hU hle) hFU₁,
    map_restrict_map_eq_map_restrict (conormalAlgebraHom (p ≫ iY) iY p (𝟙 X)
      (Category.comp_id (p ≫ iY)).symm).hom (n : ℤ) hVZ hU' le_rfl hVZ hFU₂,
    ← ha, hcan₂, hcan₁, map_zero, map_zero]
  rfl


end

end AlgebraicGeometry

end
