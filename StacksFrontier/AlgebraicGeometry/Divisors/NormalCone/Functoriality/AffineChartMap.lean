module

public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.ConormalSections

/-!
# Functoriality of the conormal algebra: affine charts and the chart-level map

A commutative square

```
Z  --i-->  X
|          |
f          g
v          v
Z' --i'--> X'
```

of schemes with `i` and `i'` immersions has affine charts: pairs of affine opens
`Spec R = U ⊆ X` and `Spec R' = U' ⊆ X'` with `g(U) ⊆ U'` on which `i` and `i'` restrict to
closed immersions, with kernel ideals `I ⊆ R` and `I' ⊆ R'`.  This file constructs these charts,
shows that they cover any open of `Z` (`conormalChart_cover`) and that two of them are refined by
a common family of charts (`conormalChartRefinement_cover`), and builds on each chart the map
`⨁ₙ (I')ⁿ/(I')ⁿ⁺¹ ⟶ ⨁ₙ Iⁿ/Iⁿ⁺¹` induced by `g^♯ : R' ⟶ R` (`chartConormalMap`), together with
its compatibility with restriction, products, the unit and scalars.

## Main results

* `AlgebraicGeometry.isClosedImmersion_resLE_of_le_coborderRange`: an immersion restricts to a
  closed immersion over any open inside the coborder of its range, which is what makes the
  affine charts available.

## References

* [Stacks Project, Tag 0634](https://stacks.math.columbia.edu/tag/0634)
* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace TopologicalSpace.Opens

universe u

namespace AlgebraicGeometry

private lemma square_sections_map_eq {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (comm : f ≫ i' = i ≫ g) (U : X.Opens) (U' : X'.Opens)
    (hGU : U ≤ g ⁻¹ᵁ U')
    (hFU : i ⁻¹ᵁ U ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U')) :
    i'.app U' ≫ f.appLE (i' ⁻¹ᵁ U') (i ⁻¹ᵁ U) hFU =
      g.appLE U' U hGU ≫ i.app U := by
  simp only [i'.app_eq_appLE, i.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE, comm]

/-- **An immersion restricts to a closed immersion over any open contained in the coborder of
its range.** -/
lemma isClosedImmersion_resLE_of_le_coborderRange {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (U : X.Opens) (hU : U ≤ i.coborderRange) :
    IsClosedImmersion (i.resLE U (i ⁻¹ᵁ U) le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  apply IsClosedImmersion.of_isPreimmersion
  rw [morphismRestrict_base]
  convert! (isClosed_preimage_val_coborder (s := Set.range i)).preimage
    (continuous_inclusion hU) using 1
  ext z
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w.val, congrArg Subtype.val hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨⟨w, by change i w ∈ U; rw [hw]; exact z.property⟩, Subtype.ext hw⟩

/-- The commutative square sends `z` to the same point of `X'` along both paths. -/
private lemma comm_apply_eq {Z X Z' X' : Scheme.{u}}
    {i : Z ⟶ X} {i' : Z' ⟶ X'} {f : Z ⟶ Z'} {g : X ⟶ X'}
    (comm : f ≫ i' = i ≫ g) (z : Z) : i' (f z) = g (i z) := by
  rw [← Scheme.Hom.comp_apply, comm, Scheme.Hom.comp_apply]


lemma square_chart_preimage_le {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (comm : f ≫ i' = i ≫ g) (U : X.Opens) (U' : X'.Opens)
    (hGU : U ≤ g ⁻¹ᵁ U') : i ⁻¹ᵁ U ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U') := by
  intro z hz
  change i' (f z) ∈ U'
  rw [comm_apply_eq comm]
  exact hGU hz

private lemma exists_open_chart_neighborhood {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsImmersion i] (V : Z.Opens) :
    ∃ O : X.Opens, O ≤ i.coborderRange ∧ i ⁻¹ᵁ O = V := by
  let c : Z ⟶ i.coborderRange.toScheme := i.liftCoborder
  let k : i.coborderRange.toScheme ⟶ X := i.coborderRange.ι
  have hc : Topology.IsInducing c.base := c.isClosedEmbedding.isEmbedding.isInducing
  obtain ⟨T, hT, hTc⟩ := hc.isOpen_iff.mp V.2
  have hk : Topology.IsInducing k.base := k.isOpenEmbedding.isEmbedding.isInducing
  obtain ⟨S, hS, hSk⟩ := hk.isOpen_iff.mp hT
  let O : X.Opens := i.coborderRange ⊓ ⟨S, hS⟩
  refine ⟨O, inf_le_left, ?_⟩
  apply TopologicalSpace.Opens.ext
  ext z
  change i z ∈ O ↔ z ∈ V
  change (i z ∈ i.coborderRange ∧ i z ∈ S) ↔ z ∈ V
  have hfac : k (c z) = i z := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun q : Z ⟶ X => q z) i.liftCoborder_ι
  constructor
  · rintro ⟨_, hzS⟩
    have hzT : c z ∈ T := by
      have h : c z ∈ k.base ⁻¹' S := by
        change k (c z) ∈ S
        simpa [hfac] using hzS
      rw [hSk] at h
      exact h
    have hzV : z ∈ c.base ⁻¹' T := hzT
    rw [hTc] at hzV
    exact hzV
  · intro hzV
    have hzT : c z ∈ T := by
      have h : z ∈ c.base ⁻¹' T := by rw [hTc]; exact hzV
      exact h
    have hzS : k (c z) ∈ S := by
      have h : c z ∈ k.base ⁻¹' S := by
        rw [hSk]
        exact hzT
      simpa only [Set.mem_preimage] using h
    exact ⟨subset_coborder ⟨z, rfl⟩, by simpa [hfac] using hzS⟩

/-- Around any point of `V`, there are affine charts `U ⊆ X` and `U' ⊆ X'` as in
`ConormalChartRefinement`, so that `U ⊆ A` and `U' ⊆ A'`. -/
private lemma exists_chart_pair {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (comm : f ≫ i' = i ≫ g)
    (V : Z.Opens) (W : Z'.Opens) (A : X.Opens) (A' : X'.Opens)
    (hVA : V ≤ i ⁻¹ᵁ A) (hWA' : W ≤ i' ⁻¹ᵁ A') (hVW : V ≤ f ⁻¹ᵁ W) {z : Z} (hz : z ∈ V) :
    ∃ (U : X.affineOpens) (U' : X'.affineOpens), z ∈ i ⁻¹ᵁ U.1 ∧ i ⁻¹ᵁ U.1 ≤ V ∧
      i' ⁻¹ᵁ U'.1 ≤ W ∧ U.1 ≤ i.coborderRange ∧ U'.1 ≤ i'.coborderRange ∧
      U.1 ≤ g ⁻¹ᵁ U'.1 ∧ U.1 ≤ A ∧ U'.1 ≤ A' := by
  obtain ⟨O'₀, hO'₀cob, hO'₀pre⟩ := exists_open_chart_neighborhood i' W
  have hx'O' : i' (f z) ∈ O'₀ ⊓ A' :=
    ⟨by change f z ∈ i' ⁻¹ᵁ O'₀; rw [hO'₀pre]; exact hVW hz, hWA' (hVW hz)⟩
  obtain ⟨U'₀, hU'₀, hx'U', hU'sub⟩ := exists_isAffineOpen_mem_and_subset hx'O'
  obtain ⟨O₀, hO₀cob, hO₀pre⟩ := exists_open_chart_neighborhood i V
  have hxO : i z ∈ O₀ ⊓ A ⊓ g ⁻¹ᵁ U'₀ :=
    ⟨⟨by change z ∈ i ⁻¹ᵁ O₀; rw [hO₀pre]; exact hz, hVA hz⟩,
      by change g (i z) ∈ U'₀; rw [← comm_apply_eq comm]; exact hx'U'⟩
  obtain ⟨U₀, hU₀, hxU, hUsub⟩ := exists_isAffineOpen_mem_and_subset hxO
  refine ⟨⟨U₀, hU₀⟩, ⟨U'₀, hU'₀⟩, hxU, fun y hy => ?_, fun y hy => ?_,
    fun y hy => hO₀cob (hUsub hy).1.1, fun y hy => hO'₀cob (hU'sub hy).1,
    fun y hy => (hUsub hy).2, fun y hy => (hUsub hy).1.2, fun y hy => (hU'sub hy).2⟩
  · have hy' : y ∈ i ⁻¹ᵁ O₀ := (hUsub hy).1.1
    rwa [hO₀pre] at hy'
  · have hy' : y ∈ i' ⁻¹ᵁ O'₀ := (hU'sub hy).1
    rwa [hO'₀pre] at hy'

/-- **An affine chart of the commutative square, adapted to a pair of opens.** It is a pair of
affine opens `U ⊆ X` and `U' ⊆ X'` on which both immersions restrict to closed immersions and
which the ambient morphism `g` is compatible with, cut down so that `i⁻¹U` lies in `V` and
`i'⁻¹U'` lies in `W`. These charts cover `V` (`AlgebraicGeometry.conormalChart_cover`), which is
what makes the chartwise description of the conormal functoriality determine it. -/
structure ConormalChartIndex {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (V : Z.Opens) (W : Z'.Opens) where
  /-- The affine open of the ambient scheme of `i`. -/
  U : X.affineOpens
  /-- The affine open of the ambient scheme of `i'`. -/
  U' : X'.affineOpens
  /-- The chart of `Z` cut out by `U` lies in `V`. -/
  source_subset : i ⁻¹ᵁ U.1 ≤ V
  /-- The chart of `Z'` cut out by `U'` lies in `W`. -/
  target_subset : i' ⁻¹ᵁ U'.1 ≤ W
  /-- `U` lies in the coborder of the range of `i`, so `i` restricts to a closed immersion
  over it. -/
  source_coborder : U.1 ≤ i.coborderRange
  /-- `U'` lies in the coborder of the range of `i'`, so `i'` restricts to a closed immersion
  over it. -/
  target_coborder : U'.1 ≤ i'.coborderRange
  /-- The ambient morphism carries `U` into `U'`. -/
  ambient_compatible : U.1 ≤ g ⁻¹ᵁ U'.1

def conormalChartOpen {Z X Z' X' : Scheme.{u}}
    {i : Z ⟶ X} {i' : Z' ⟶ X'} {f : Z ⟶ Z'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i']
    {V : Z.Opens} {W : Z'.Opens} (j : ConormalChartIndex i i' f g V W) : Z.Opens :=
  i ⁻¹ᵁ j.U.1

theorem conormalChart_cover {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (comm : f ≫ i' = i ≫ g)
    (V : Z.Opens) (W : Z'.Opens) (hVW : V ≤ f ⁻¹ᵁ W) :
    V ≤ ⨆ j : ConormalChartIndex i i' f g V W, conormalChartOpen j := by
  classical
  classical
  intro z hz
  obtain ⟨U, U', hzU, h1, h2, h3, h4, h5, -⟩ :=
    exists_chart_pair i i' f g comm V W ⊤ ⊤ (fun _ _ => trivial) (fun _ _ => trivial) hVW hz
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, U', h1, h2, h3, h4, h5⟩, hzU⟩

structure ConormalChartRefinement {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (V : Z.Opens) (W : Z'.Opens)
    (A : X.Opens) (A' : X'.Opens) where
  U : X.affineOpens
  U' : X'.affineOpens
  source_subset : i ⁻¹ᵁ U.1 ≤ V
  target_subset : i' ⁻¹ᵁ U'.1 ≤ W
  source_coborder : U.1 ≤ i.coborderRange
  target_coborder : U'.1 ≤ i'.coborderRange
  ambient_compatible : U.1 ≤ g ⁻¹ᵁ U'.1
  source_refines : U.1 ≤ A
  target_refines : U'.1 ≤ A'

def conormalChartRefinementOpen {Z X Z' X' : Scheme.{u}}
    {i : Z ⟶ X} {i' : Z' ⟶ X'} {f : Z ⟶ Z'} {g : X ⟶ X'}
    [IsImmersion i] [IsImmersion i'] {V : Z.Opens} {W : Z'.Opens}
    {A : X.Opens} {A' : X'.Opens}
    (j : ConormalChartRefinement i i' f g V W A A') : Z.Opens := i ⁻¹ᵁ j.U.1

theorem conormalChartRefinement_cover {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (comm : f ≫ i' = i ≫ g)
    (V : Z.Opens) (W : Z'.Opens) (A : X.Opens) (A' : X'.Opens)
    (hVA : V ≤ i ⁻¹ᵁ A) (hWA' : W ≤ i' ⁻¹ᵁ A')
    (hVW : V ≤ f ⁻¹ᵁ W) :
    V ≤ ⨆ j : ConormalChartRefinement i i' f g V W A A',
      conormalChartRefinementOpen j := by
  classical
  intro z hz
  obtain ⟨U, U', hzU, h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_chart_pair i i' f g comm V W A A' hVA hWA' hVW hz
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, U', h1, h2, h3, h4, h5, h6, h7⟩, hzU⟩

private lemma chartIdeal_map_le {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (comm : f ≫ i' = i ≫ g) (U : X.affineOpens) (U' : X'.affineOpens)
    (hGU : U.1 ≤ g ⁻¹ᵁ U'.1)
    (hFU : i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U'.1)) :
    Ideal.map (g.appLE U'.1 U.1 hGU).hom (Stacks.Conormal.chartIdeal i' U') ≤
      Stacks.Conormal.chartIdeal i U := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  change (i.app U.1).hom ((g.appLE U'.1 U.1 hGU).hom r) = 0
  change (i'.app U'.1).hom r = 0 at hr
  have hval := congrArg (fun q : Γ(X', U'.1) ⟶ Γ(Z, i ⁻¹ᵁ U.1) => q.hom r)
    (square_sections_map_eq i i' f g comm U.1 U'.1 hGU hFU)
  change (f.appLE (i' ⁻¹ᵁ U'.1) (i ⁻¹ᵁ U.1) hFU).hom
      ((i'.app U'.1).hom r) =
    (i.app U.1).hom ((g.appLE U'.1 U.1 hGU).hom r) at hval
  rw [← hval, hr, map_zero]

lemma chartIdealPow_map_le {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (comm : f ≫ i' = i ≫ g) (U : X.affineOpens) (U' : X'.affineOpens)
    (hGU : U.1 ≤ g ⁻¹ᵁ U'.1)
    (hFU : i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U'.1)) (n : ℕ) :
    Ideal.map (g.appLE U'.1 U.1 hGU).hom (Stacks.Conormal.chartIdeal i' U' ^ n) ≤
      Stacks.Conormal.chartIdeal i U ^ n := by
  rw [Ideal.map_pow]
  exact pow_le_pow_left' (chartIdeal_map_le i i' f g comm U U' hGU hFU) n

lemma chartIdealPow_map_mem {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (comm : f ≫ i' = i ≫ g) (U : X.affineOpens) (U' : X'.affineOpens)
    (hGU : U.1 ≤ g ⁻¹ᵁ U'.1)
    (hFU : i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U'.1)) (n : ℕ)
    (a : ↥(Stacks.Conormal.chartIdeal i' U' ^ n)) :
    X.presheaf.map (homOfLE hGU).op ((g.app U'.1).hom (a : Γ(X', U'.1))) ∈
      Stacks.Conormal.chartIdeal i U ^ n := by
  change (g.appLE U'.1 U.1 hGU).hom (a : Γ(X', U'.1)) ∈ _
  exact (chartIdealPow_map_le i i' f g comm U U' hGU hFU n)
    (Ideal.mem_map_of_mem (g.appLE U'.1 U.1 hGU).hom a.property)

noncomputable def associatedGradedPieceMap
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (I : Ideal A) (J : Ideal B)
    (hpow : ∀ n, Ideal.map φ (I ^ n) ≤ J ^ n) (n : ℕ) :
    AssociatedGraded.piece (M := A) I n →+ AssociatedGraded.piece (M := B) J n := by
  letI : Module A B := Module.compHom B φ
  let P := AssociatedGraded.power (M := A) I n
  let Q := AssociatedGraded.power (M := B) J n
  let f : P →ₛₗ[φ] Q := {
    toFun x := ⟨φ (x : A), by
      have hx := x.property
      change (x : A) ∈ AssociatedGraded.power (M := A) I n at hx
      rw [AssociatedGraded.ring_power_eq] at hx
      have hy : φ (x : A) ∈ J ^ n := hpow n (Ideal.mem_map_of_mem φ hx)
      change φ (x : A) ∈ AssociatedGraded.power (M := B) J n
      rw [AssociatedGraded.ring_power_eq]
      exact hy⟩
    map_add' x y := by ext; exact map_add φ (x : A) y
    map_smul' a x := by ext; exact map_mul φ a (x : A)
  }
  let p := (AssociatedGraded.power (M := A) I (n + 1)).comap
    (Submodule.subtype P)
  let q := (AssociatedGraded.power (M := B) J (n + 1)).comap
    (Submodule.subtype Q)
  have hf : p ≤ Submodule.comap f q := by
    intro x hx
    have hx' : (x : A) ∈ I ^ (n + 1) := by
      change (Submodule.subtype P x) ∈
        AssociatedGraded.power (M := A) I (n + 1) at hx
      rw [AssociatedGraded.ring_power_eq] at hx
      exact hx
    have hy : φ (x : A) ∈ J ^ (n + 1) :=
      hpow (n + 1) (Ideal.mem_map_of_mem φ hx')
    change (Submodule.subtype Q (f x)) ∈
      AssociatedGraded.power (M := B) J (n + 1)
    rw [AssociatedGraded.ring_power_eq]
    exact hy
  exact (Submodule.mapQ p q f hf).toAddMonoidHom

noncomputable def chartConormalMap {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i']
    (comm : f ≫ i' = i ≫ g) (U : X.affineOpens) (U' : X'.affineOpens)
    (hGU : U.1 ≤ g ⁻¹ᵁ U'.1)
    (hZU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (hZ'U' : IsClosedImmersion (i'.resLE U'.1 (i' ⁻¹ᵁ U'.1) le_rfl))
    (hFU : i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U'.1)) (n : ℕ) :
    ((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.obj
      (op (i' ⁻¹ᵁ U'.1)) →+
    ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.obj
      (op (i ⁻¹ᵁ U.1)) := by
  let es := affineSectionsEquiv
    i' U' hZ'U'
  let et := affineSectionsEquiv
    i U hZU
  exact et.equiv n |>.toAddMonoidHom.comp
    ((associatedGradedPieceMap (g.appLE U'.1 U.1 hGU).hom
      (Stacks.Conormal.chartIdeal i' U') (Stacks.Conormal.chartIdeal i U)
      (fun k => chartIdealPow_map_le i i' f g comm U U' hGU hFU k) n).comp
      (es.equiv n).symm.toAddMonoidHom)

private theorem associatedGradedPieceMap_mk
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (I : Ideal A) (J : Ideal B)
    (hpow : ∀ k, Ideal.map φ (I ^ k) ≤ J ^ k) (n : ℕ)
    (a : AssociatedGraded.power (M := A) I n) :
    associatedGradedPieceMap φ I J hpow n (AssociatedGraded.mk I n a) =
      AssociatedGraded.mk J n
        ⟨φ (a : A), by
          rw [AssociatedGraded.ring_power_eq]
          exact hpow n (Ideal.mem_map_of_mem φ
            (by simpa only [AssociatedGraded.ring_power_eq] using a.property))⟩ := by
  simp [associatedGradedPieceMap, Submodule.mapQ_apply, AssociatedGraded.mk,
    ]

private theorem associatedGradedPieceMap_mul_mk
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (I : Ideal A) (J : Ideal B)
    (hpow : ∀ k, Ideal.map φ (I ^ k) ≤ J ^ k) (n m : ℕ)
    (a : ↥(I ^ n)) (b : ↥(I ^ m)) :
    associatedGradedPieceMap φ I J hpow (n + m)
      (AssociatedGraded.homogeneousSMul I
        (AssociatedGraded.mk I n
          ⟨(a : A), by simpa only [AssociatedGraded.ring_power_eq] using a.property⟩)
        (AssociatedGraded.mk I m
          ⟨(b : A), by simpa only [AssociatedGraded.ring_power_eq] using b.property⟩)) =
    AssociatedGraded.homogeneousSMul J
        (AssociatedGraded.mk J n
          ⟨φ (a : A), by
            rw [AssociatedGraded.ring_power_eq]
            exact hpow n (Ideal.mem_map_of_mem φ a.property)⟩)
        (AssociatedGraded.mk J m
          ⟨φ (b : A), by
            rw [AssociatedGraded.ring_power_eq]
            exact hpow m (Ideal.mem_map_of_mem φ b.property)⟩) := by
  simp only [AssociatedGraded.homogeneousSMul_mk, smul_eq_mul]
  rw [associatedGradedPieceMap_mk]
  simp only [map_mul]

private theorem associatedGradedPieceMap_smul
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (I : Ideal A) (J : Ideal B)
    (hpow : ∀ k, Ideal.map φ (I ^ k) ≤ J ^ k) (n : ℕ)
    (r : A) (x : AssociatedGraded.piece (M := A) I n) :
    associatedGradedPieceMap φ I J hpow n (r • x) =
      φ r • associatedGradedPieceMap φ I J hpow n x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    simp [associatedGradedPieceMap]

theorem chartConormalMap_localMap {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (comm : f ≫ i' = i ≫ g)
    (U : X.affineOpens) (U' : X'.affineOpens)
    (hGU : U.1 ≤ g ⁻¹ᵁ U'.1)
    (hZU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (hZ'U' : IsClosedImmersion (i'.resLE U'.1 (i' ⁻¹ᵁ U'.1) le_rfl))
    (hFU : i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U'.1)) (n : ℕ)
    (a : ↥(Stacks.Conormal.chartIdeal i' U' ^ n)) :
    chartConormalMap i i' f g comm U U' hGU hZU hZ'U' hFU n
      ((Stacks.Conormal.conormalAlgebra i').localMap U' hZ'U' n a) =
    (Stacks.Conormal.conormalAlgebra i).localMap U hZU n
      ⟨(g.appLE U'.1 U.1 hGU).hom (a : Γ(X', U'.1)),
        chartIdealPow_map_mem i i' f g comm U U' hGU hFU n a⟩ := by
  let es := affineSectionsEquiv
    i' U' hZ'U'
  let et := affineSectionsEquiv
    i U hZU
  let a' : AssociatedGraded.power (M := Γ(X', U')) (Stacks.Conormal.chartIdeal i' U') n :=
    ⟨(a : Γ(X', U'.1)), by simp only [AssociatedGraded.ring_power_eq]; exact a.property⟩
  have hs := es.map_mk n a'
  have ht := et.map_mk n
    ⟨(g.appLE U'.1 U.1 hGU).hom (a : Γ(X', U'.1)), by
      rw [AssociatedGraded.ring_power_eq]
      simpa only [Scheme.Hom.appLE, ConcreteCategory.comp_apply] using
        chartIdealPow_map_mem i i' f g comm U U' hGU hFU n a⟩
  dsimp [chartConormalMap]
  rw [← hs, AddEquiv.symm_apply_apply, associatedGradedPieceMap_mk]
  exact ht

private theorem chartConormalMap_smul_localMap
    {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (comm : f ≫ i' = i ≫ g)
    (U : X.affineOpens) (U' : X'.affineOpens)
    (hGU : U.1 ≤ g ⁻¹ᵁ U'.1)
    (hZU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (hZ'U' : IsClosedImmersion (i'.resLE U'.1 (i' ⁻¹ᵁ U'.1) le_rfl))
    (hFU : i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U'.1)) (n : ℕ)
    (r : Γ(X', U'.1)) (a : ↥(Stacks.Conormal.chartIdeal i' U' ^ n)) :
    chartConormalMap i i' f g comm U U' hGU hZU hZ'U' hFU n
        ((show Z'.ringCatSheaf.obj.obj (op (i' ⁻¹ᵁ U'.1)) from
            (i'.app U'.1).hom r) •
          (Stacks.Conormal.conormalAlgebra i').localMap U' hZ'U' n a) =
      (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)) from
        (i.app U.1).hom ((g.appLE U'.1 U.1 hGU).hom r)) •
        chartConormalMap i i' f g comm U U' hGU hZU hZ'U' hFU n
          ((Stacks.Conormal.conormalAlgebra i').localMap U' hZ'U' n a) := by
  let c : ↥(Stacks.Conormal.chartIdeal i' U' ^ n) :=
    ⟨r * (a : Γ(X', U'.1)), (Stacks.Conormal.chartIdeal i' U' ^ n).smul_mem r a.property⟩
  let a' : ↥(Stacks.Conormal.chartIdeal i U ^ n) :=
    ⟨(g.appLE U'.1 U.1 hGU).hom (a : Γ(X', U'.1)),
      chartIdealPow_map_mem i i' f g comm U U' hGU hFU n a⟩
  let c' : ↥(Stacks.Conormal.chartIdeal i U ^ n) :=
    ⟨(g.appLE U'.1 U.1 hGU).hom r *
        (g.appLE U'.1 U.1 hGU).hom (a : Γ(X', U'.1)),
      (Stacks.Conormal.chartIdeal i U ^ n).smul_mem
        ((g.appLE U'.1 U.1 hGU).hom r) a'.property⟩
  have hc : (c : Γ(X', U'.1)) = r * (a : Γ(X', U'.1)) := rfl
  have hc' : (c' : Γ(X, U.1)) =
      (g.appLE U'.1 U.1 hGU).hom r * (a' : Γ(X, U.1)) := rfl
  rw [← (Stacks.Conormal.conormalAlgebra i').localMap_smul U' hZ'U' n r a c hc,
    chartConormalMap_localMap, chartConormalMap_localMap,
    ← (Stacks.Conormal.conormalAlgebra i).localMap_smul U hZU n
      ((g.appLE U'.1 U.1 hGU).hom r) a' c' hc']
  congr 1
  apply Subtype.ext
  simp [c, c', map_mul]

private theorem chartConormalMap_restrict_target
    {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (comm : f ≫ i' = i ≫ g)
    (U : X.affineOpens) (U₁' U₂' : X'.affineOpens)
    (hU₂U₁ : U₂'.1 ≤ U₁'.1)
    (hGU₁ : U.1 ≤ g ⁻¹ᵁ U₁'.1) (hGU₂ : U.1 ≤ g ⁻¹ᵁ U₂'.1)
    (hZU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (hZ'U₁ : IsClosedImmersion (i'.resLE U₁'.1 (i' ⁻¹ᵁ U₁'.1) le_rfl))
    (hZ'U₂ : IsClosedImmersion (i'.resLE U₂'.1 (i' ⁻¹ᵁ U₂'.1) le_rfl))
    (hFU₁ : i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U₁'.1))
    (hFU₂ : i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U₂'.1)) (n : ℕ)
    (x : ((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.obj
      (op (i' ⁻¹ᵁ U₁'.1))) :
    chartConormalMap i i' f g comm U U₁' hGU₁ hZU hZ'U₁ hFU₁ n x =
      chartConormalMap i i' f g comm U U₂' hGU₂ hZU hZ'U₂ hFU₂ n
        (((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.map
          (homOfLE (show i' ⁻¹ᵁ U₂'.1 ≤ i' ⁻¹ᵁ U₁'.1 from
            fun _ hz => hU₂U₁ hz)).op x) := by
  obtain ⟨a, rfl⟩ :=
    (Stacks.Conormal.conormalAlgebra i').localMap_surjective U₁' hZ'U₁ n x
  let hZU₂ : i' ⁻¹ᵁ U₂'.1 ≤ i' ⁻¹ᵁ U₁'.1 := fun _ hz => hU₂U₁ hz
  let b : ↥(Stacks.Conormal.chartIdeal i' U₂' ^ n) :=
    ⟨X'.presheaf.map (homOfLE hU₂U₁).op (a : Γ(X', U₁'.1)), by
      have hpow := chartIdealPow_map_le i' i' (𝟙 Z' : Z' ⟶ Z')
        (𝟙 X' : X' ⟶ X') (by simp)
        U₂' U₁' hU₂U₁ hZU₂ n
      change X'.presheaf.map (homOfLE hU₂U₁).op
          (a : Γ(X', U₁'.1)) ∈ Stacks.Conormal.chartIdeal i' U₂' ^ n
      exact hpow (Ideal.mem_map_of_mem _ a.property)⟩
  have hb := (Stacks.Conormal.conormalAlgebra i').localMap_naturality
    U₁' U₂' hU₂U₁ hZU₂ hZ'U₁ hZ'U₂ n a b rfl
  rw [chartConormalMap_localMap, hb, chartConormalMap_localMap]
  congr 1
  apply Subtype.ext
  change (g.appLE U₁'.1 U.1 hGU₁).hom (a : Γ(X', U₁'.1)) =
    (g.appLE U₂'.1 U.1 hGU₂).hom
      (X'.presheaf.map (homOfLE hU₂U₁).op (a : Γ(X', U₁'.1)))
  have hcomp := g.map_appLE hGU₂ (homOfLE hU₂U₁).op
  simpa only [ConcreteCategory.comp_apply] using
    (congrArg (fun q : Γ(X', U₁'.1) ⟶ Γ(X, U.1) => q.hom
      (a : Γ(X', U₁'.1))) hcomp).symm

private theorem chartConormalMap_restrict {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (comm : f ≫ i' = i ≫ g)
    (U V : X.affineOpens) (U' : X'.affineOpens) (hVU : V.1 ≤ U.1)
    (hGU : U.1 ≤ g ⁻¹ᵁ U'.1)
    (hZU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (hZV : IsClosedImmersion (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl))
    (hZ'U' : IsClosedImmersion (i'.resLE U'.1 (i' ⁻¹ᵁ U'.1) le_rfl))
    (hFU : i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U'.1)) (n : ℕ)
    (x : ((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.obj
      (op (i' ⁻¹ᵁ U'.1))) :
    ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.map
        (homOfLE (show i ⁻¹ᵁ V.1 ≤ i ⁻¹ᵁ U.1 from fun _ hx => hVU hx)).op
        (chartConormalMap i i' f g comm U U' hGU hZU hZ'U' hFU n x) =
      chartConormalMap i i' f g comm V U' (le_trans hVU hGU) hZV hZ'U'
        (fun z hz => hFU (show z ∈ i ⁻¹ᵁ U.1 from hVU hz)) n x := by
  obtain ⟨a, rfl⟩ := (Stacks.Conormal.conormalAlgebra i').localMap_surjective U' hZ'U' n x
  let aU : ↥(Stacks.Conormal.chartIdeal i U ^ n) :=
    ⟨(g.appLE U'.1 U.1 hGU).hom (a : Γ(X', U'.1)),
      chartIdealPow_map_mem i i' f g comm U U' hGU hFU n a⟩
  let aV : ↥(Stacks.Conormal.chartIdeal i V ^ n) :=
    ⟨(g.appLE U'.1 V.1 (le_trans hVU hGU)).hom (a : Γ(X', U'.1)), by
      exact chartIdealPow_map_mem i i' f g comm V U' (le_trans hVU hGU)
        (fun z hz => hFU (hVU hz)) n a⟩
  have hRestr : (aV : Γ(X, V.1)) =
      X.presheaf.map (homOfLE hVU).op (aU : Γ(X, U.1)) := by
    change (g.appLE U'.1 V.1 (le_trans hVU hGU)).hom (a : Γ(X', U'.1)) =
      X.presheaf.map (homOfLE hVU).op
        ((g.appLE U'.1 U.1 hGU).hom (a : Γ(X', U'.1)))
    have heq := g.appLE_map hGU (homOfLE hVU).op
    change (g.appLE U'.1 V.1 (le_trans hVU hGU)).hom (a : Γ(X', U'.1)) =
      ((g.appLE U'.1 U.1 hGU) ≫ X.presheaf.map (homOfLE hVU).op).hom
        (a : Γ(X', U'.1))
    rw [← heq]
  rw [chartConormalMap_localMap, chartConormalMap_localMap]
  exact (Stacks.Conormal.conormalAlgebra i).localMap_naturality U V hVU
    (fun _ hz => hVU hz) hZU hZV n aU aV hRestr

theorem chartConormalMap_restrict_both {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (comm : f ≫ i' = i ≫ g)
    (U V : X.affineOpens) (U' V' : X'.affineOpens)
    (hVU : V.1 ≤ U.1) (hV'U' : V'.1 ≤ U'.1)
    (hGU : U.1 ≤ g ⁻¹ᵁ U'.1) (hGV : V.1 ≤ g ⁻¹ᵁ V'.1)
    (hZU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (hZV : IsClosedImmersion (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl))
    (hZ'U' : IsClosedImmersion (i'.resLE U'.1 (i' ⁻¹ᵁ U'.1) le_rfl))
    (hZ'V' : IsClosedImmersion (i'.resLE V'.1 (i' ⁻¹ᵁ V'.1) le_rfl))
    (hFU : i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U'.1))
    (hFV : i ⁻¹ᵁ V.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ V'.1)) (n : ℕ)
    (x : ((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.obj
      (op (i' ⁻¹ᵁ U'.1))) :
    ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.map
        (homOfLE (show i ⁻¹ᵁ V.1 ≤ i ⁻¹ᵁ U.1 from fun _ hx => hVU hx)).op
        (chartConormalMap i i' f g comm U U' hGU hZU hZ'U' hFU n x) =
      chartConormalMap i i' f g comm V V' hGV hZV hZ'V' hFV n
        (((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.map
          (homOfLE (show i' ⁻¹ᵁ V'.1 ≤ i' ⁻¹ᵁ U'.1 from
            fun _ hz => hV'U' hz)).op x) := by
  have hGVU' : V.1 ≤ g ⁻¹ᵁ U'.1 := fun _ hz => hV'U' (hGV hz)
  have hFVU' : i ⁻¹ᵁ V.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U'.1) :=
    fun _ hz => hFU (hVU hz)
  have hs := chartConormalMap_restrict i i' f g comm U V U' hVU hGU
    hZU hZV hZ'U' hFU n x
  have ht := chartConormalMap_restrict_target i i' f g comm V U' V'
    hV'U' hGVU' hGV hZV hZ'U' hZ'V' hFVU' hFV n x
  rw [hs, ht]

private theorem chartConormalMap_mul_localMap
    {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (comm : f ≫ i' = i ≫ g)
    (U : X.affineOpens) (U' : X'.affineOpens)
    (hGU : U.1 ≤ g ⁻¹ᵁ U'.1)
    (hZU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (hZ'U' : IsClosedImmersion (i'.resLE U'.1 (i' ⁻¹ᵁ U'.1) le_rfl))
    (hFU : i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U'.1))
    (n m : ℕ) (a : ↥(Stacks.Conormal.chartIdeal i' U' ^ n))
    (b : ↥(Stacks.Conormal.chartIdeal i' U' ^ m)) :
    chartConormalMap i i' f g comm U U' hGU hZU hZ'U' hFU (n + m)
      ((Stacks.Conormal.conormalAlgebra i').algebra.mul (n : ℤ) (m : ℤ) |>.app
        (op (i' ⁻¹ᵁ U'.1))
        ((Stacks.Conormal.conormalAlgebra i').localMap U' hZ'U' n a)
        ((Stacks.Conormal.conormalAlgebra i').localMap U' hZ'U' m b)) =
    ((Stacks.Conormal.conormalAlgebra i).algebra.mul (n : ℤ) (m : ℤ) |>.app
      (op (i ⁻¹ᵁ U.1))
      (chartConormalMap i i' f g comm U U' hGU hZU hZ'U' hFU n
        ((Stacks.Conormal.conormalAlgebra i').localMap U' hZ'U' n a))
      (chartConormalMap i i' f g comm U U' hGU hZU hZ'U' hFU m
        ((Stacks.Conormal.conormalAlgebra i').localMap U' hZ'U' m b))) := by
  let c : ↥(Stacks.Conormal.chartIdeal i' U' ^ (n + m)) :=
    ⟨(a : Γ(X', U'.1)) * (b : Γ(X', U'.1)), by
      rw [pow_add]
      exact Ideal.mul_mem_mul a.property b.property⟩
  let a' : ↥(Stacks.Conormal.chartIdeal i U ^ n) :=
    ⟨(g.appLE U'.1 U.1 hGU).hom (a : Γ(X', U'.1)),
      chartIdealPow_map_mem i i' f g comm U U' hGU hFU n a⟩
  let b' : ↥(Stacks.Conormal.chartIdeal i U ^ m) :=
    ⟨(g.appLE U'.1 U.1 hGU).hom (b : Γ(X', U'.1)),
      chartIdealPow_map_mem i i' f g comm U U' hGU hFU m b⟩
  let c' : ↥(Stacks.Conormal.chartIdeal i U ^ (n + m)) :=
    ⟨(g.appLE U'.1 U.1 hGU).hom (a : Γ(X', U'.1)) *
        (g.appLE U'.1 U.1 hGU).hom (b : Γ(X', U'.1)), by
      rw [pow_add]
      exact Ideal.mul_mem_mul a'.property b'.property⟩
  rw [← (Stacks.Conormal.conormalAlgebra i').localMap_mul U' hZ'U' n m a b c rfl]
  rw [chartConormalMap_localMap]
  rw [chartConormalMap_localMap]
  rw [chartConormalMap_localMap]
  have hc' : (⟨(g.appLE U'.1 U.1 hGU).hom (c : Γ(X', U'.1)),
      chartIdealPow_map_mem i i' f g comm U U' hGU hFU (n + m) c⟩ :
      ↥(Stacks.Conormal.chartIdeal i U ^ (n + m))) = c' := by
    apply Subtype.ext
    change (g.appLE U'.1 U.1 hGU).hom
      ((a : Γ(X', U'.1)) * (b : Γ(X', U'.1))) = _
    simp [c', map_mul]
  have ha' : (⟨(g.appLE U'.1 U.1 hGU).hom (a : Γ(X', U'.1)),
      chartIdealPow_map_mem i i' f g comm U U' hGU hFU n a⟩ :
      ↥(Stacks.Conormal.chartIdeal i U ^ n)) = a' := rfl
  have hb' : (⟨(g.appLE U'.1 U.1 hGU).hom (b : Γ(X', U'.1)),
      chartIdealPow_map_mem i i' f g comm U U' hGU hFU m b⟩ :
      ↥(Stacks.Conormal.chartIdeal i U ^ m)) = b' := rfl
  rw [hc', ha', hb']
  rw [Stacks.Conormal.conormalAlgebra i |>.localMap_mul U hZU n m a' b' c' rfl]

theorem chartConormalMap_mul
    {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (comm : f ≫ i' = i ≫ g)
    (U : X.affineOpens) (U' : X'.affineOpens)
    (hGU : U.1 ≤ g ⁻¹ᵁ U'.1)
    (hZU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (hZ'U' : IsClosedImmersion (i'.resLE U'.1 (i' ⁻¹ᵁ U'.1) le_rfl))
    (hFU : i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U'.1))
    (n m : ℕ)
    (x : ((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.obj
      (op (i' ⁻¹ᵁ U'.1)))
    (y : ((Stacks.Conormal.conormalAlgebra i').algebra.piece (m : ℤ)).val.obj
      (op (i' ⁻¹ᵁ U'.1))) :
    chartConormalMap i i' f g comm U U' hGU hZU hZ'U' hFU (n + m)
      (((Stacks.Conormal.conormalAlgebra i').algebra.mul (n : ℤ) (m : ℤ)).app
        (op (i' ⁻¹ᵁ U'.1)) x y) =
    ((Stacks.Conormal.conormalAlgebra i).algebra.mul (n : ℤ) (m : ℤ)).app
      (op (i ⁻¹ᵁ U.1))
      (chartConormalMap i i' f g comm U U' hGU hZU hZ'U' hFU n x)
      (chartConormalMap i i' f g comm U U' hGU hZU hZ'U' hFU m y) := by
  obtain ⟨a, rfl⟩ :=
    (Stacks.Conormal.conormalAlgebra i').localMap_surjective U' hZ'U' n x
  obtain ⟨b, rfl⟩ :=
    (Stacks.Conormal.conormalAlgebra i').localMap_surjective U' hZ'U' m y
  exact chartConormalMap_mul_localMap i i' f g comm U U' hGU hZU hZ'U' hFU n m a b

theorem chartConormalMap_one
    {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (comm : f ≫ i' = i ≫ g)
    (U : X.affineOpens) (U' : X'.affineOpens)
    (hGU : U.1 ≤ g ⁻¹ᵁ U'.1)
    (hZU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (hZ'U' : IsClosedImmersion (i'.resLE U'.1 (i' ⁻¹ᵁ U'.1) le_rfl))
    (hFU : i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U'.1)) :
    chartConormalMap i i' f g comm U U' hGU hZU hZ'U' hFU 0
      ((Stacks.Conormal.conormalAlgebra i').algebra.one.eval
        (op (i' ⁻¹ᵁ U'.1))) =
      (Stacks.Conormal.conormalAlgebra i).algebra.one.eval (op (i ⁻¹ᵁ U.1)) := by
  let es := affineSectionsEquiv
    i' U' hZ'U'
  let et := affineSectionsEquiv
    i U hZU
  rw [← es.map_one]
  dsimp [chartConormalMap]
  rw [AddEquiv.symm_apply_apply, associatedGradedPieceMap_mk]
  simpa only [map_one] using et.map_one

theorem chartConormalMap_smul
    {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (comm : f ≫ i' = i ≫ g)
    (U : X.affineOpens) (U' : X'.affineOpens)
    (hGU : U.1 ≤ g ⁻¹ᵁ U'.1)
    (hZU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (hZ'U' : IsClosedImmersion (i'.resLE U'.1 (i' ⁻¹ᵁ U'.1) le_rfl))
    (hFU : i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U'.1)) (n : ℕ)
    (r : Γ(Z', i' ⁻¹ᵁ U'.1))
    (x : ((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.obj
      (op (i' ⁻¹ᵁ U'.1))) :
    chartConormalMap i i' f g comm U U' hGU hZU hZ'U' hFU n
        ((show Z'.ringCatSheaf.obj.obj (op (i' ⁻¹ᵁ U'.1)) from r) • x) =
      (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)) from
        Z.presheaf.map (homOfLE hFU).op ((f.app (i' ⁻¹ᵁ U'.1)).hom r)) •
        chartConormalMap i i' f g comm U U' hGU hZU hZ'U' hFU n x := by
  obtain ⟨a, ha⟩ :=
    (Stacks.Conormal.conormalAlgebra i').localMap_surjective U' hZ'U' n x
  subst x
  obtain ⟨r', hr'⟩ := app_surjective_of_closedRestriction i' U' hZ'U' r
  have hs : Z.presheaf.map (homOfLE hFU).op
        ((f.app (i' ⁻¹ᵁ U'.1)).hom ((i'.app U'.1).hom r')) =
      (i.app U.1).hom ((g.appLE U'.1 U.1 hGU).hom r') := by
    change (f.appLE (i' ⁻¹ᵁ U'.1) (i ⁻¹ᵁ U.1) hFU).hom
        ((i'.app U'.1).hom r') = _
    exact congrArg (fun q : Γ(X', U'.1) ⟶ Γ(Z, i ⁻¹ᵁ U.1) => q.hom r')
      (square_sections_map_eq i i' f g comm U.1 U'.1 hGU hFU)
  simpa only [← hr', hs] using
    (chartConormalMap_smul_localMap i i' f g comm U U' hGU hZU hZ'U' hFU n r' a)

end AlgebraicGeometry

end
