module

public import StacksFrontier.AlgebraicGeometry.Conormal.CommonChartCompatibility
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ConormalApproximationBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Size.Pullback

/-!
# The sub-family of common charts over which Stacks 0CAY compares

Let `p : Y ⟶ T`, let `t ∈ T` and let `b : W ⟶ T`, `b' : W' ⟶ T` be two morphisms into which the
fibre `Y_t` embeds as in `Stacks.ConormalApproximation.HasFibreImmersion`. The chart-by-chart
comparison of the two conormal algebras is available only over the charts of the two base changes
of the form `pr₁⁻¹U ⊓ pr₂⁻¹W₀` for `U` an affine open of `Y` above the chosen affine open `T₀` of
`T`, because only for those is the chart ring a base change of `Γ(Y, U)`; this is the shape
`Stacks.ConormalApproximation.chartQuotientPresentationOfPullbackChart` produces. This file
exhibits those charts as a sub-family of the common charts of the two closed immersions, shows
that the opens they cut out in the fibre form a basis of it, and assembles the comparison.

## Main definitions

* `Stacks.ConormalApproximation.chartAlgebra`: the `C`-algebra structure on the sections over an
  affine open of `Y` above `T₀`.
* `Stacks.ConormalApproximation.PresentedChart`: **the index of the sub-family** — an affine open
  `U` of `Y` above `T₀` together with a finite presentation of `Γ(Y, U)` over `C`. The
  presentation is part of the index and not a function of `U`, which is what makes the refinement
  condition of `Stacks.Conormal.CommonChartAssociatedGradedEquiv` satisfiable: a member refining
  two given ones carries a presentation chosen to absorb the generators of *both*.
* `Stacks.ConormalApproximation.pullbackChart`: the chart `pr₁⁻¹U ⊓ pr₂⁻¹W₀` of the base change,
  as an affine open.
* `Stacks.ConormalApproximation.commonChartOfPresentedChart`: the member of
  `Stacks.Conormal.CommonChart` that a member of the index cuts out.

## Main results

* `Stacks.ConormalApproximation.preimage_pullbackChart`: the preimage of the chart in the fibre is
  `Y_t ∩ U`, independently of `W₀` — the chart of `W` disappears because the fibre maps into it.
* `Stacks.ConormalApproximation.isBasis_preimage_fiberι` and
  `Stacks.ConormalApproximation.isBasis_commonChartOfPresentedChart`: **the opens of the
  sub-family form a basis of the fibre.** The map `Y_t ⟶ Y` is a topological embedding
  (`AlgebraicGeometry.Scheme.Hom.fiberι` is an `IsPreimmersion`), so every open of `Y_t` is cut
  out by an open of `Y`, and the affine opens of `Y` inside `p⁻¹T₀` form a basis of `p⁻¹T₀`, which
  contains the whole fibre.

## References

* [Stacks Project, Tag 0CAY](https://stacks.math.columbia.edu/tag/0CAY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.ConormalApproximation

/-- **The map on sections of a morphism depends on the morphism only through its value.** The
containment is a proposition, so the two maps are the same once the two morphisms are. This is the
form in which an equation between morphisms — such as the compatibility of a fibre immersion with
a projection — is used inside `AlgebraicGeometry.Scheme.Hom.appLE`, where rewriting is blocked by
the containment's dependence on the morphism. -/
theorem appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h
  rfl

/-- The map on sections of `g`, followed by the restriction along `j`, is the map on sections of
any composite `k = j ≫ g`. -/
private theorem appLE_comp_app_of_comp_eq {X Y Z : Scheme.{u}} (j : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (h : j ≫ g = k) (U : Z.Opens) (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ U)
    (hk : j ⁻¹ᵁ V ≤ k ⁻¹ᵁ U) : g.appLE U V hV ≫ j.app V = k.appLE U (j ⁻¹ᵁ V) hk := by
  subst h
  rw [Scheme.Hom.app_eq_appLE]
  exact Scheme.Hom.appLE_comp_appLE j g U V _ hV le_rfl

/-! ### The index of the sub-family -/

/-- **The `C`-algebra structure on the sections over an affine open of `Y` above `T₀`** that `p`
and the identification `eC : Γ(T, T₀) ≃+* C` put on it. It is not an instance: it depends on the
containment `U ≤ p ⁻¹ᵁ T₀`, which is data. -/
@[instance_reducible]
def chartAlgebra {T Y : Scheme.{u}} (p : Y ⟶ T) {T₀ : T.Opens} {U : Y.Opens}
    (hUT : U ≤ p ⁻¹ᵁ T₀) {C : Type u} [CommRing C] (eC : Γ(T, T₀) ≃+* C) :
    Algebra C Γ(Y, U) :=
  ((p.appLE T₀ U hUT).hom.comp (eC.symm : C →+* Γ(T, T₀))).toAlgebra

/-- Under `Stacks.ConormalApproximation.chartAlgebra`, the image of `eC x` in `Γ(Y, U)` is the
pullback of `x` along `p`. -/
theorem algebraMap_chartAlgebra {T Y : Scheme.{u}} (p : Y ⟶ T) {T₀ : T.Opens} {U : Y.Opens}
    (hUT : U ≤ p ⁻¹ᵁ T₀) {C : Type u} [CommRing C] (eC : Γ(T, T₀) ≃+* C) (x : Γ(T, T₀)) :
    letI := chartAlgebra p hUT eC
    algebraMap C Γ(Y, U) (eC x) = (p.appLE T₀ U hUT).hom x := by
  let := chartAlgebra p hUT eC
  change ((p.appLE T₀ U hUT).hom.comp (eC.symm : C →+* Γ(T, T₀))) (eC x) = _
  simp

/-- **The chart algebra is of finite type over `C`** when `p` is locally of finite type: the map
`Γ(T, T₀) ⟶ Γ(Y, U)` is of finite type by
`AlgebraicGeometry.LocallyOfFiniteType.finiteType_appLE`, and precomposing with the surjection
`C ≃+* Γ(T, T₀)` keeps it so. -/
theorem finiteType_chartAlgebra {T Y : Scheme.{u}} (p : Y ⟶ T) [LocallyOfFiniteType p]
    {T₀ : T.Opens} (hT₀ : IsAffineOpen T₀) {U : Y.Opens} (hU : IsAffineOpen U)
    (hUT : U ≤ p ⁻¹ᵁ T₀) {C : Type u} [CommRing C] (eC : Γ(T, T₀) ≃+* C) :
    letI := chartAlgebra p hUT eC
    Algebra.FiniteType C Γ(Y, U) :=
  (p.finiteType_appLE hT₀ hU hUT).comp
    (RingHom.FiniteType.of_surjective (eC.symm : C →+* Γ(T, T₀)) eC.symm.surjective)

/-- **`C` is Noetherian** when `T` is a Noetherian scheme and `T₀` is affine. -/
theorem isNoetherianRing_of_isAffineOpen {T : Scheme.{u}} [IsNoetherian T] {T₀ : T.Opens}
    (hT₀ : IsAffineOpen T₀) {C : Type u} [CommRing C] (eC : Γ(T, T₀) ≃+* C) :
    IsNoetherianRing C :=
  have : IsNoetherianRing Γ(T, T₀) := IsLocallyNoetherian.component_noetherian ⟨T₀, hT₀⟩
  isNoetherianRing_of_ringEquiv _ eC

/-- **The index of the sub-family of charts over which Stacks 0CAY compares**: an affine open `U`
of `Y` lying over the chosen affine open `T₀` of `T`, together with a finite presentation of
`Γ(Y, U)` over `C`.

The presentation is carried by the index rather than chosen as a function of `U`. This is what
makes the refinement condition of `Stacks.Conormal.CommonChartAssociatedGradedEquiv` satisfiable:
the comparison of the chart presentations of two nested charts is a renaming of the variables
(`Stacks.ConormalApproximation.chartQuotientPresentationHomOfRename`), a condition on the pair, so
a member refining two given members must carry a presentation whose variables absorb the
generators of *both* — which `Stacks.exists_presentation_val_eq_of_finiteType` supplies because it
takes an arbitrary finite family of elements. -/
structure PresentedChart {T Y : Scheme.{u}} (p : Y ⟶ T) (T₀ : T.Opens) (C : Type u) [CommRing C]
    (eC : Γ(T, T₀) ≃+* C) : Type u where
  /-- The affine open of `Y`. -/
  U : Y.Opens
  /-- It is affine. -/
  isAffineOpen : IsAffineOpen U
  /-- It lies over `T₀`. -/
  le_preimage : U ≤ p ⁻¹ᵁ T₀
  /-- The number of variables of the presentation. -/
  n : ℕ
  /-- The number of relations of the presentation. -/
  m : ℕ
  /-- The presentation of `Γ(Y, U)` over `C`. -/
  presentation :
    letI := chartAlgebra p le_preimage eC
    Algebra.Presentation C Γ(Y, U) (Fin n) (Fin m)

namespace PresentedChart

variable {T Y : Scheme.{u}} {p : Y ⟶ T} {T₀ : T.Opens} {C : Type u} [CommRing C]
  {eC : Γ(T, T₀) ≃+* C}

/-- The generators of the presentation carried by a member of the index. -/
def val (a : PresentedChart p T₀ C eC) : Fin a.n → Γ(Y, a.U) :=
  letI := chartAlgebra p a.le_preimage eC
  a.presentation.val

/-- The relations of the presentation carried by a member of the index. -/
def relation (a : PresentedChart p T₀ C eC) : Fin a.m → MvPolynomial (Fin a.n) C :=
  letI := chartAlgebra p a.le_preimage eC
  a.presentation.relation

/-- The generators of a member of the index built from a presentation `P` are those of `P`. -/
@[simp]
theorem val_mk {U : Y.Opens} (hU : IsAffineOpen U) (hUT : U ≤ p ⁻¹ᵁ T₀) {n m : ℕ}
    (P : letI := chartAlgebra p hUT eC; Algebra.Presentation C Γ(Y, U) (Fin n) (Fin m)) :
    (PresentedChart.mk U hU hUT n m P).val =
      (letI := chartAlgebra p hUT eC; P.val) :=
  rfl

/-- The relations of a member of the index built from a presentation `P` are those of `P`. -/
@[simp]
theorem relation_mk {U : Y.Opens} (hU : IsAffineOpen U) (hUT : U ≤ p ⁻¹ᵁ T₀) {n m : ℕ}
    (P : letI := chartAlgebra p hUT eC; Algebra.Presentation C Γ(Y, U) (Fin n) (Fin m)) :
    (PresentedChart.mk U hU hUT n m P).relation =
      (letI := chartAlgebra p hUT eC; P.relation) :=
  rfl

end PresentedChart

/-- **The restriction map between the sections over two nested affine opens of `Y` above `T₀`, as
a map of `C`-algebras.** It is `C`-linear because restriction commutes with the pullback along `p`
from `T₀`, `AlgebraicGeometry.Scheme.Hom.appLE_map`. This is the `res` that
`Stacks.ConormalApproximation.equiv_restrict_chartQuotientPresentationOfPullbackChart` asks
for. -/
def restrictAlgHom {T Y : Scheme.{u}} (p : Y ⟶ T) {T₀ : T.Opens} {C : Type u} [CommRing C]
    (eC : Γ(T, T₀) ≃+* C) {U U' : Y.Opens} (hUT : U ≤ p ⁻¹ᵁ T₀) (hU'T : U' ≤ p ⁻¹ᵁ T₀)
    (hUU : U' ≤ U) :
    letI := chartAlgebra p hUT eC
    letI := chartAlgebra p hU'T eC
    Γ(Y, U) →ₐ[C] Γ(Y, U') :=
  letI := chartAlgebra p hUT eC
  letI := chartAlgebra p hU'T eC
  AlgHom.mk (Y.presheaf.map (homOfLE hUU).op).hom fun c => by
    have h1 := algebraMap_chartAlgebra p hUT eC (eC.symm c)
    have h2 := algebraMap_chartAlgebra p hU'T eC (eC.symm c)
    rw [eC.apply_symm_apply] at h1 h2
    change (Y.presheaf.map (homOfLE hUU).op).hom (algebraMap C Γ(Y, U) c) = algebraMap C Γ(Y, U') c
    rw [h1, h2, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/-! ### The chart of a base change that a member of the index cuts out -/

section Chart

variable {T Y W : Scheme.{u}} (p : Y ⟶ T) (b : W ⟶ T) {T₀ : T.Opens} {W₀ : W.Opens} {U : Y.Opens}

/-- **The chart `pr₁⁻¹U ⊓ pr₂⁻¹W₀` of the base change is an affine open**, being the fibre product
of two affine opens over an affine open, `AlgebraicGeometry.isAffineOpen_inf_preimage`. -/
theorem isAffineOpen_pullbackChart (hT₀ : IsAffineOpen T₀) (hW₀ : IsAffineOpen W₀)
    (hU : IsAffineOpen U) (hW₀T : W₀ ≤ b ⁻¹ᵁ T₀) (hUT : U ≤ p ⁻¹ᵁ T₀) :
    IsAffineOpen (pullback.fst p b ⁻¹ᵁ U ⊓ pullback.snd p b ⁻¹ᵁ W₀) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine W₀.toScheme := hW₀
  have : IsAffine T₀.toScheme := hT₀
  exact isAffineOpen_inf_preimage p b hUT hW₀T

/-- The chart `pr₁⁻¹U ⊓ pr₂⁻¹W₀` of the base change, as an affine open. -/
def pullbackChart (hT₀ : IsAffineOpen T₀) (hW₀ : IsAffineOpen W₀) (hU : IsAffineOpen U)
    (hW₀T : W₀ ≤ b ⁻¹ᵁ T₀) (hUT : U ≤ p ⁻¹ᵁ T₀) : (pullback p b).affineOpens :=
  ⟨pullback.fst p b ⁻¹ᵁ U ⊓ pullback.snd p b ⁻¹ᵁ W₀,
    isAffineOpen_pullbackChart p b hT₀ hW₀ hU hW₀T hUT⟩

/-- The chart lies over the chart of `W`. Stated rather than written as `inf_le_right` at each use
so that the containment carried by `AlgebraicGeometry.Scheme.Hom.appLE` is always the same term. -/
theorem pullbackChart_le_right (hT₀ : IsAffineOpen T₀) (hW₀ : IsAffineOpen W₀)
    (hU : IsAffineOpen U) (hW₀T : W₀ ≤ b ⁻¹ᵁ T₀) (hUT : U ≤ p ⁻¹ᵁ T₀) :
    (pullbackChart p b hT₀ hW₀ hU hW₀T hUT).1 ≤ pullback.snd p b ⁻¹ᵁ W₀ :=
  inf_le_right

/-- The chart lies over the affine open of `Y`. -/
theorem pullbackChart_le_left (hT₀ : IsAffineOpen T₀) (hW₀ : IsAffineOpen W₀)
    (hU : IsAffineOpen U) (hW₀T : W₀ ≤ b ⁻¹ᵁ T₀) (hUT : U ≤ p ⁻¹ᵁ T₀) :
    (pullbackChart p b hT₀ hW₀ hU hW₀T hUT).1 ≤ pullback.fst p b ⁻¹ᵁ U :=
  inf_le_left

/-- **Shrinking the affine open of `Y` shrinks the chart of the base change.** This is the
containment *in the ambient scheme* that the naturality of the chart presentations needs, and the
reason the refining member of the family is found by shrinking `U` inside `Y` rather than by
shrinking the open it cuts out in the fibre. -/
theorem pullbackChart_mono {U' : Y.Opens} (hT₀ : IsAffineOpen T₀) (hW₀ : IsAffineOpen W₀)
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hW₀T : W₀ ≤ b ⁻¹ᵁ T₀) (hUT : U ≤ p ⁻¹ᵁ T₀)
    (hU'T : U' ≤ p ⁻¹ᵁ T₀) (hUU : U' ≤ U) :
    (pullbackChart p b hT₀ hW₀ hU' hW₀T hU'T).1 ≤ (pullbackChart p b hT₀ hW₀ hU hW₀T hUT).1 :=
  inf_le_inf_right _ ((pullback.fst p b).preimage_mono hUU)

/-- The underlying open of `Stacks.ConormalApproximation.pullbackChart` is `pr₁⁻¹U ⊓ pr₂⁻¹W₀`. -/
@[simp]
theorem pullbackChart_coe (hT₀ : IsAffineOpen T₀) (hW₀ : IsAffineOpen W₀) (hU : IsAffineOpen U)
    (hW₀T : W₀ ≤ b ⁻¹ᵁ T₀) (hUT : U ≤ p ⁻¹ᵁ T₀) :
    (pullbackChart p b hT₀ hW₀ hU hW₀T hUT).1 =
      pullback.fst p b ⁻¹ᵁ U ⊓ pullback.snd p b ⁻¹ᵁ W₀ :=
  rfl

end Chart

/-! ### The preimage of the chart in the fibre -/

section Preimage

variable {T Y W : Scheme.{u}} (p : Y ⟶ T) (t : T) (b : W ⟶ T)
  {r : Spec (CommRingCat.of (T.residueField t)) ⟶ W} {j : p.fiber t ⟶ pullback p b}

/-- **The preimage in the fibre of a chart of the base change is the part of the fibre over the
affine open of `Y`.** The chart of `W` contributes nothing: the fibre maps into it, by
`hrW`, because the second projection of `j` factors through the chosen point `r` of `W`. -/
theorem preimage_pullbackChart {W₀ : W.Opens} {U : Y.Opens}
    (hfst : j ≫ pullback.fst p b = p.fiberι t)
    (hsnd : j ≫ pullback.snd p b = p.fiberToSpecResidueField t ≫ r)
    (hrW : (⊤ : (Spec (CommRingCat.of (T.residueField t))).Opens) ≤ r ⁻¹ᵁ W₀) :
    j ⁻¹ᵁ (pullback.fst p b ⁻¹ᵁ U ⊓ pullback.snd p b ⁻¹ᵁ W₀) = p.fiberι t ⁻¹ᵁ U := by
  have hleft : j ⁻¹ᵁ (pullback.fst p b ⁻¹ᵁ U) = p.fiberι t ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, hfst]
  have hright : j ⁻¹ᵁ (pullback.snd p b ⁻¹ᵁ W₀) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, hsnd, Scheme.Hom.comp_preimage, top_le_iff.mp hrW,
      Scheme.Hom.preimage_top]
  rw [Scheme.Hom.preimage_inf, hleft, hright, inf_top_eq]

end Preimage

/-! ### The opens of the sub-family form a basis of the fibre -/

section Basis

variable {T Y : Scheme.{u}} (p : Y ⟶ T) (t : T)

/-- A point of the fibre lies over `t`. -/
theorem base_fiberι (x : p.fiber t) : p (p.fiberι t x) = t := by
  have hx : p.fiberι t x ∈ Set.range (p.fiberι t) := ⟨x, rfl⟩
  rw [Scheme.Hom.range_fiberι] at hx
  exact hx

/-- **Every point of the fibre lying over an open of `Y` has an affine open of `Y` above `T₀`
around it inside that open.** This is the refining step: the containment `U ≤ O` is a containment
in `Y`, which is what makes the chart of the base change cut out by `U` contained in the one cut
out by `O`. -/
theorem exists_affineOpen_le_preimage_fiberι {T₀ : T.Opens} (ht : t ∈ T₀) (O : Y.Opens)
    (x : p.fiber t) (hx : x ∈ p.fiberι t ⁻¹ᵁ O) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ U ≤ p ⁻¹ᵁ T₀ ∧ U ≤ O ∧ x ∈ p.fiberι t ⁻¹ᵁ U := by
  have hxT : p.fiberι t x ∈ (p ⁻¹ᵁ T₀ : Set Y) := by
    change p (p.fiberι t x) ∈ T₀
    rw [base_fiberι p t x]
    exact ht
  obtain ⟨V, ⟨A, hA, rfl⟩, hxA, hAO⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show p.fiberι t x ∈ (O : Set Y) ∩ (p ⁻¹ᵁ T₀ : Set Y) from ⟨hx, hxT⟩)
      (O.2.inter (p ⁻¹ᵁ T₀).2)
  exact ⟨A, hA, fun z hz => (hAO hz).2, fun z hz => (hAO hz).1, hxA⟩

/-- **Every point of an open of the fibre has an affine open of `Y` above `T₀` around it whose
part of the fibre is inside that open.** The map `Y_t ⟶ Y` is a topological embedding, so the
given open of the fibre is cut out by an open of `Y`, and
`Stacks.ConormalApproximation.exists_affineOpen_le_preimage_fiberι` shrinks the latter. -/
theorem exists_affineOpen_preimage_fiberι {T₀ : T.Opens} (ht : t ∈ T₀) (Ω : (p.fiber t).Opens)
    (x : p.fiber t) (hx : x ∈ Ω) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ U ≤ p ⁻¹ᵁ T₀ ∧ x ∈ p.fiberι t ⁻¹ᵁ U ∧
      p.fiberι t ⁻¹ᵁ U ≤ Ω := by
  obtain ⟨O, hO, hpre⟩ := (p.fiberι t).isEmbedding.isInducing.isOpen_iff.mp Ω.2
  have hxO : x ∈ p.fiberι t ⁻¹ᵁ (⟨O, hO⟩ : Y.Opens) := by
    have : (x : p.fiber t) ∈ p.fiberι t ⁻¹' O := by rwa [hpre]
    exact this
  obtain ⟨A, hA, hAT, hAO, hxA⟩ :=
    exists_affineOpen_le_preimage_fiberι p t ht ⟨O, hO⟩ x hxO
  refine ⟨A, hA, hAT, hxA, fun z hz => ?_⟩
  have : (z : p.fiber t) ∈ p.fiberι t ⁻¹' O := hAO hz
  rwa [hpre] at this

end Basis

/-! ### The sub-family of common charts -/

section Family

variable {T Y W W' : Scheme.{u}} (p : Y ⟶ T) (t : T) (b : W ⟶ T) (b' : W' ⟶ T)
  {r : Spec (CommRingCat.of (T.residueField t)) ⟶ W}
  {r' : Spec (CommRingCat.of (T.residueField t)) ⟶ W'}
  {j : p.fiber t ⟶ pullback p b} {j' : p.fiber t ⟶ pullback p b'}
  [IsClosedImmersion j] [IsClosedImmersion j']
  (hfst : j ≫ pullback.fst p b = p.fiberι t)
  (hsnd : j ≫ pullback.snd p b = p.fiberToSpecResidueField t ≫ r)
  (hfst' : j' ≫ pullback.fst p b' = p.fiberι t)
  (hsnd' : j' ≫ pullback.snd p b' = p.fiberToSpecResidueField t ≫ r')
  {T₀ : T.Opens} {W₀ : W.Opens} {W₀' : W'.Opens}
  (hT₀ : IsAffineOpen T₀) (hW₀ : IsAffineOpen W₀) (hW₀' : IsAffineOpen W₀')
  (hW₀T : W₀ ≤ b ⁻¹ᵁ T₀) (hW₀'T : W₀' ≤ b' ⁻¹ᵁ T₀)
  (hrW : (⊤ : (Spec (CommRingCat.of (T.residueField t))).Opens) ≤ r ⁻¹ᵁ W₀)
  (hrW' : (⊤ : (Spec (CommRingCat.of (T.residueField t))).Opens) ≤ r' ⁻¹ᵁ W₀')
  {C : Type u} [CommRing C] (eC : Γ(T, T₀) ≃+* C)

include hfst hsnd hfst' hsnd' hrW hrW' in
/-- **The member of `Stacks.Conormal.CommonChart` that a member of the index cuts out**: the chart
`pr₁⁻¹U ⊓ pr₂⁻¹W₀` of the one base change and the chart `pr₁⁻¹U ⊓ pr₂'⁻¹W₀'` of the other, whose
preimages in the fibre are both `Y_t ∩ U` by
`Stacks.ConormalApproximation.preimage_pullbackChart`. Both are charts of the respective closed
immersion because every affine open is, `Stacks.Conormal.coborderRange_eq_top`. -/
def commonChartOfPresentedChart (a : PresentedChart p T₀ C eC) : Stacks.Conormal.CommonChart j j'
    where
  left := Stacks.Conormal.conormalChartOfIsClosedImmersion j
    (pullbackChart p b hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage)
  right := Stacks.Conormal.conormalChartOfIsClosedImmersion j'
    (pullbackChart p b' hT₀ hW₀' a.isAffineOpen hW₀'T a.le_preimage)
  preimage_eq := by
    rw [Stacks.Conormal.conormalChartOfIsClosedImmersion_coe,
      Stacks.Conormal.conormalChartOfIsClosedImmersion_coe, pullbackChart_coe, pullbackChart_coe,
      preimage_pullbackChart p t b hfst hsnd hrW, preimage_pullbackChart p t b' hfst' hsnd' hrW']

include hfst hsnd hfst' hsnd' hrW hrW' in
/-- The open of the fibre cut out by a member of the sub-family is `Y_t ∩ U`. -/
theorem commonChartOpens_commonChartOfPresentedChart (a : PresentedChart p T₀ C eC) :
    Stacks.Conormal.commonChartOpens j j'
        (commonChartOfPresentedChart p t b b' hfst hsnd hfst' hsnd' hT₀ hW₀ hW₀' hW₀T hW₀'T
          hrW hrW' eC a) =
      p.fiberι t ⁻¹ᵁ a.U :=
  preimage_pullbackChart p t b hfst hsnd hrW

variable [LocallyOfFiniteType p] [IsNoetherian T]

include hT₀ in
/-- **Every affine open of `Y` above `T₀` is the open of a member of the index, with a
presentation whose variables include any prescribed finite family of sections.** This is
`Stacks.exists_presentation_val_eq_of_finiteType`, and it is the whole reason the index carries
the presentation: the family of elements may be the images of the generators of the presentations
of *two* larger charts at once. -/
theorem exists_presentedChart_val_eq {U : Y.Opens} (hU : IsAffineOpen U) (hUT : U ≤ p ⁻¹ᵁ T₀)
    {k : ℕ} (z : Fin k → Γ(Y, U)) :
    ∃ (n m : ℕ) (P : letI := chartAlgebra p hUT eC;
        Algebra.Presentation C Γ(Y, U) (Fin n) (Fin m)) (ι : Fin k → Fin n),
      ∀ i, (letI := chartAlgebra p hUT eC; P.val) (ι i) = z i := by
  let := chartAlgebra p hUT eC
  have := finiteType_chartAlgebra p hT₀ hU hUT eC
  have := isNoetherianRing_of_isAffineOpen hT₀ eC
  obtain ⟨n, m, P, ι, -, hval⟩ := Stacks.exists_presentation_val_eq_of_finiteType C Γ(Y, U) z
  exact ⟨n, m, P, ι, hval⟩

include hfst hsnd hfst' hsnd' hrW hrW' in
/-- **The opens of the sub-family form a basis of the topology of the fibre.** Around any point of
any open of the fibre there is an affine open `U` of `Y` above `T₀` whose part of the fibre lies
inside it, by `Stacks.ConormalApproximation.exists_affineOpen_preimage_fiberι`, and `U` carries a
presentation, so it is the open of a member of the index. This is the field `isBasis` of
`Stacks.Conormal.CommonChartAssociatedGradedEquiv`. -/
theorem isBasis_commonChartOfPresentedChart (ht : t ∈ T₀) :
    Opens.IsBasis (Set.range fun a : PresentedChart p T₀ C eC =>
      Stacks.Conormal.commonChartOpens j j'
        (commonChartOfPresentedChart p t b b' hfst hsnd hfst' hsnd' hT₀ hW₀ hW₀' hW₀T hW₀'T
          hrW hrW' eC a)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro Ω x hx
  obtain ⟨U, hU, hUT, hxU, hUΩ⟩ := exists_affineOpen_preimage_fiberι p t ht Ω x hx
  obtain ⟨n, m, P, -, -⟩ :=
    exists_presentedChart_val_eq p hT₀ eC hU hUT (k := 0) (fun i => i.elim0)
  refine ⟨_, ⟨⟨U, hU, hUT, n, m, P⟩, rfl⟩, ?_, ?_⟩
  · simpa only [commonChartOpens_commonChartOfPresentedChart] using hxU
  · simpa only [commonChartOpens_commonChartOfPresentedChart] using hUΩ

end Family

/-! ### The chart presentation attached to a member of the index

The data below is given once and used twice, for the two base changes: the `C`-algebra structure
of `D` is an argument, so the two calls differ in the ring map `C → D` they supply —
`σ` on one side and `σ'` on the other — which is exactly the pair of structure maps that the
affine comparison
`Stacks.ConormalApproximation.exists_finiteType_coefficients_associatedGraded_equiv` compares
across. The *same* presentation of `Γ(Y, U)` is used on both sides, so the two ambient rings are
literally the same `D[x_1, …, x_n]`, which is what
`Stacks.Conormal.commonChartAssociatedGradedEquivOfPresentations` requires. -/

section ChartPresentation

variable {T Y W : Scheme.{u}} (p : Y ⟶ T) (t : T) (b : W ⟶ T)
  {r : Spec (CommRingCat.of (T.residueField t)) ⟶ W} {j : p.fiber t ⟶ pullback p b}
  (hr : r ≫ b = T.fromSpecResidueField t)
  (hfst : j ≫ pullback.fst p b = p.fiberι t)
  (hsnd : j ≫ pullback.snd p b = p.fiberToSpecResidueField t ≫ r)
  {T₀ : T.Opens} {W₀ : W.Opens} (hT₀ : IsAffineOpen T₀) (hW₀ : IsAffineOpen W₀)
  (hW₀T : W₀ ≤ b ⁻¹ᵁ T₀)
  (hrW : (⊤ : (Spec (CommRingCat.of (T.residueField t))).Opens) ≤ r ⁻¹ᵁ W₀)
  {C : Type u} [CommRing C] (eC : Γ(T, T₀) ≃+* C)
  {D : Type u} [CommRing D] (sigma : C →+* D) (eD : Γ(W, W₀) ≃+* D)
  (hD : ∀ x : Γ(T, T₀), eD ((b.appLE T₀ W₀ hW₀T).hom x) = sigma (eC x))
  (I : Ideal D)
  (hI : (RingHom.ker (r.appLE W₀ ⊤ hrW).hom).map (eD : Γ(W, W₀) →+* D) = I)
  (hsurj : Function.Surjective (r.appLE W₀ ⊤ hrW).hom)

include hr hfst hsnd hT₀ hW₀ hW₀T hrW eC hD hI hsurj in
/-- **A chart of a base change, presented as a quotient of the polynomial ring over `D`**, for a
member of the index: `Stacks.ConormalApproximation.chartQuotientPresentationOfPullbackChart` at
the chart `pr₁⁻¹U ⊓ pr₂⁻¹W₀` and the presentation the index carries, with `Γ(Y, U)` taken as its
own identification of itself.

The structure map `σ : C → D` is an argument rather than an `Algebra C D` instance, because the
two base changes of Stacks 0CAY put *two* `C`-algebra structures on the same ring `D`, and the
ambient polynomial ring over which they are compared must be the same `D[x_1, …, x_n]`. -/
def chartPresentationOfHom (a : PresentedChart p T₀ C eC) :
    Stacks.Conormal.ChartQuotientPresentation j
      (pullbackChart p b hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage)
      (I.map (MvPolynomial.C : D →+* MvPolynomial (Fin a.n) D))
      (LinearMap.range (relationMapOfHom sigma a.relation)) :=
  letI := chartAlgebra p a.le_preimage eC
  letI := sigma.toAlgebra
  chartQuotientPresentationOfPullbackChart p t b r j hr hfst hsnd hT₀ hW₀ a.isAffineOpen hW₀T
    a.le_preimage hrW (pullbackChart p b hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage) rfl
    eC eD (RingEquiv.refl Γ(Y, a.U)) hD
    (fun x => (algebraMap_chartAlgebra p a.le_preimage eC x).symm)
    a.presentation I hI hsurj

include hr hfst hsnd hT₀ hW₀ hW₀T hrW eC hD hI hsurj in
/-- **The function on the fibre chart that a constant presents**: the section of `W₀` that `eD`
identifies with it, pulled back. -/
theorem toSourceHom_chartPresentationOfHom_C (a : PresentedChart p T₀ C eC) (d : D) :
    (chartPresentationOfHom p t b hr hfst hsnd hT₀ hW₀ hW₀T hrW eC sigma eD hD I hI hsurj
          a).toSourceHom (MvPolynomial.C d) =
      (j.app (pullbackChart p b hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage).1).hom
        (((pullback.snd p b).appLE W₀
            (pullbackChart p b hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage).1
            (pullbackChart_le_right p b hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage)).hom
          (eD.symm d)) := by
  let := chartAlgebra p a.le_preimage eC
  let := sigma.toAlgebra
  exact toSourceHom_chartQuotientPresentationOfPullbackChart_C p t b r j hr hfst hsnd hT₀ hW₀
    a.isAffineOpen hW₀T a.le_preimage hrW
    (pullbackChart p b hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage) rfl eC eD
    (RingEquiv.refl Γ(Y, a.U)) hD
    (fun x => (algebraMap_chartAlgebra p a.le_preimage eC x).symm) a.presentation I hI hsurj d

include hr hfst hsnd hT₀ hW₀ hW₀T hrW eC hD hI hsurj in
/-- **The function on the fibre chart that a variable presents**: the generator of `Γ(Y, U)` it
names, pulled back. -/
theorem toSourceHom_chartPresentationOfHom_X (a : PresentedChart p T₀ C eC) (i : Fin a.n) :
    (chartPresentationOfHom p t b hr hfst hsnd hT₀ hW₀ hW₀T hrW eC sigma eD hD I hI hsurj
          a).toSourceHom (MvPolynomial.X i) =
      (j.app (pullbackChart p b hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage).1).hom
        (((pullback.fst p b).appLE a.U
            (pullbackChart p b hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage).1
            (pullbackChart_le_left p b hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage)).hom
          (a.val i)) := by
  let := chartAlgebra p a.le_preimage eC
  let := sigma.toAlgebra
  exact toSourceHom_chartQuotientPresentationOfPullbackChart_X p t b r j hr hfst hsnd hT₀ hW₀
    a.isAffineOpen hW₀T a.le_preimage hrW
    (pullbackChart p b hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage) rfl eC eD
    (RingEquiv.refl Γ(Y, a.U)) hD
    (fun x => (algebraMap_chartAlgebra p a.le_preimage eC x).symm) a.presentation I hI hsurj i

end ChartPresentation

/-! ### The two presentations present the same functions on the fibre chart -/

section AppLE

variable {T Y W : Scheme.{u}} (p : Y ⟶ T) (t : T) (b : W ⟶ T)
  {r : Spec (CommRingCat.of (T.residueField t)) ⟶ W} {j : p.fiber t ⟶ pullback p b}
  (hfst : j ≫ pullback.fst p b = p.fiberι t)
  (hsnd : j ≫ pullback.snd p b = p.fiberToSpecResidueField t ≫ r)
  {T₀ : T.Opens} {W₀ : W.Opens} {U : Y.Opens}
  (hT₀ : IsAffineOpen T₀) (hW₀ : IsAffineOpen W₀) (hU : IsAffineOpen U)
  (hW₀T : W₀ ≤ b ⁻¹ᵁ T₀) (hUT : U ≤ p ⁻¹ᵁ T₀)
  (hrW : (⊤ : (Spec (CommRingCat.of (T.residueField t))).Opens) ≤ r ⁻¹ᵁ W₀)

include hsnd in
/-- **A section of the chart of `W`, pulled back to the fibre chart, is pulled back through the
chosen point `r` of `W`.** The second projection restricted to the fibre factors as
`Y_t ⟶ Spec κ(t) ⟶ W`, which is the whole reason the two base changes present the same functions
on the fibre: the chart of `W` enters only through `Γ(W, W₀) ⟶ κ(t)`. -/
theorem appLE_chart_right :
    (pullback.snd p b).appLE W₀ (pullbackChart p b hT₀ hW₀ hU hW₀T hUT).1
          (pullbackChart_le_right p b hT₀ hW₀ hU hW₀T hUT) ≫
        j.app (pullbackChart p b hT₀ hW₀ hU hW₀T hUT).1 =
      r.appLE W₀ ⊤ hrW ≫
        (p.fiberToSpecResidueField t).appLE ⊤
          (j ⁻¹ᵁ (pullbackChart p b hT₀ hW₀ hU hW₀T hUT).1)
          le_top := by
  have e : j ⁻¹ᵁ (pullbackChart p b hT₀ hW₀ hU hW₀T hUT).1 ≤
      (j ≫ pullback.snd p b) ⁻¹ᵁ W₀ :=
    j.preimage_mono (pullbackChart_le_right p b hT₀ hW₀ hU hW₀T hUT)
  rw [appLE_comp_app_of_comp_eq j _ _ hsnd _ _ _ (hsnd ▸ e)]
  exact (Scheme.Hom.appLE_comp_appLE (p.fiberToSpecResidueField t) r W₀ ⊤ _ hrW le_top).symm

include hfst in
/-- **A section of the affine open of `Y`, pulled back to the fibre chart, is pulled back along
`Y_t ⟶ Y`**, the first projection restricted to the fibre being that map. -/
theorem appLE_chart_left
    (hle : j ⁻¹ᵁ (pullbackChart p b hT₀ hW₀ hU hW₀T hUT).1 ≤ p.fiberι t ⁻¹ᵁ U) :
    (pullback.fst p b).appLE U (pullbackChart p b hT₀ hW₀ hU hW₀T hUT).1
          (pullbackChart_le_left p b hT₀ hW₀ hU hW₀T hUT) ≫
        j.app (pullbackChart p b hT₀ hW₀ hU hW₀T hUT).1 =
      (p.fiberι t).appLE U (j ⁻¹ᵁ (pullbackChart p b hT₀ hW₀ hU hW₀T hUT).1) hle := by
  exact appLE_comp_app_of_comp_eq j _ _ hfst _ _ _ hle

end AppLE

section Comparison

variable {T Y W W' : Scheme.{u}} (p : Y ⟶ T) (t : T) (b : W ⟶ T) (b' : W' ⟶ T)
  {r : Spec (CommRingCat.of (T.residueField t)) ⟶ W}
  {r' : Spec (CommRingCat.of (T.residueField t)) ⟶ W'}
  {j : p.fiber t ⟶ pullback p b} {j' : p.fiber t ⟶ pullback p b'}
  [IsClosedImmersion j] [IsClosedImmersion j']
  (hr : r ≫ b = T.fromSpecResidueField t) (hr' : r' ≫ b' = T.fromSpecResidueField t)
  (hfst : j ≫ pullback.fst p b = p.fiberι t)
  (hsnd : j ≫ pullback.snd p b = p.fiberToSpecResidueField t ≫ r)
  (hfst' : j' ≫ pullback.fst p b' = p.fiberι t)
  (hsnd' : j' ≫ pullback.snd p b' = p.fiberToSpecResidueField t ≫ r')
  {T₀ : T.Opens} {W₀ : W.Opens} {W₀' : W'.Opens}
  (hT₀ : IsAffineOpen T₀) (hW₀ : IsAffineOpen W₀) (hW₀' : IsAffineOpen W₀')
  (hW₀T : W₀ ≤ b ⁻¹ᵁ T₀) (hW₀'T : W₀' ≤ b' ⁻¹ᵁ T₀)
  (hrW : (⊤ : (Spec (CommRingCat.of (T.residueField t))).Opens) ≤ r ⁻¹ᵁ W₀)
  (hrW' : (⊤ : (Spec (CommRingCat.of (T.residueField t))).Opens) ≤ r' ⁻¹ᵁ W₀')
  {C : Type u} [CommRing C] (eC : Γ(T, T₀) ≃+* C)
  {D : Type u} [CommRing D] (sigma sigma' : C →+* D)
  (eD : Γ(W, W₀) ≃+* D) (eD' : Γ(W', W₀') ≃+* D)
  (hD : ∀ x : Γ(T, T₀), eD ((b.appLE T₀ W₀ hW₀T).hom x) = sigma (eC x))
  (hD' : ∀ x : Γ(T, T₀), eD' ((b'.appLE T₀ W₀' hW₀'T).hom x) = sigma' (eC x))
  (I : Ideal D)
  (hI : (RingHom.ker (r.appLE W₀ ⊤ hrW).hom).map (eD : Γ(W, W₀) →+* D) = I)
  (hI' : (RingHom.ker (r'.appLE W₀' ⊤ hrW').hom).map (eD' : Γ(W', W₀') →+* D) = I)
  (hsurj : Function.Surjective (r.appLE W₀ ⊤ hrW).hom)
  (hsurj' : Function.Surjective (r'.appLE W₀' ⊤ hrW').hom)
  (hsource : ∀ d : D,
    (r.appLE W₀ ⊤ hrW).hom (eD.symm d) = (r'.appLE W₀' ⊤ hrW').hom (eD'.symm d))

include hr hr' hfst hsnd hfst' hsnd' hT₀ hW₀ hW₀' hW₀T hW₀'T hrW hrW' eC hD hD' hI hI'
  hsurj hsurj' hsource in
/-- **The two chart presentations present the same functions on the open of the fibre.** This is
the compatibility `hcompat` of
`Stacks.Conormal.commonChartAssociatedGradedEquivOfPresentations`, and the only place where the
two base changes are compared *before* their associated graded algebras are.

Both sides are ring maps out of `D[x_1, …, x_n]`, so it is enough to compare them on constants and
on variables. On a variable they are literally equal: the first projection restricted to the fibre
is `Y_t ⟶ Y` on both sides, and the two presentations use the same generators of `Γ(Y, U)`. On a
constant they are equal because the second projection restricted to the fibre factors through
`Spec κ(t)` on both sides, and the two identifications of the chart ring of `W` with `D` induce
the same map `D → κ(t)`, which is the hypothesis `hsource`. -/
theorem toSourceHom_cast_eq (a : PresentedChart p T₀ C eC) (z : MvPolynomial (Fin a.n) D) :
    (AddEquiv.cast (M := fun S : (p.fiber t).Opens => Γ(p.fiber t, S))
        (commonChartOfPresentedChart p t b b' hfst hsnd hfst' hsnd' hT₀ hW₀ hW₀' hW₀T hW₀'T
          hrW hrW' eC a).preimage_eq.symm)
        ((chartPresentationOfHom p t b' hr' hfst' hsnd' hT₀ hW₀' hW₀'T hrW' eC sigma' eD' hD'
          I hI' hsurj' a).toSourceHom z) =
      (chartPresentationOfHom p t b hr hfst hsnd hT₀ hW₀ hW₀T hrW eC sigma eD hD I hI hsurj
        a).toSourceHom z := by
  have hpre : j' ⁻¹ᵁ (pullbackChart p b' hT₀ hW₀' a.isAffineOpen hW₀'T a.le_preimage).1 =
      j ⁻¹ᵁ (pullbackChart p b hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage).1 :=
    (commonChartOfPresentedChart p t b b' hfst hsnd hfst' hsnd' hT₀ hW₀ hW₀' hW₀T hW₀'T
      hrW hrW' eC a).preimage_eq.symm
  have hleL : j ⁻¹ᵁ (pullbackChart p b hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage).1 ≤
      p.fiberι t ⁻¹ᵁ a.U := le_of_eq (preimage_pullbackChart p t b hfst hsnd hrW)
  have hleR : j' ⁻¹ᵁ (pullbackChart p b' hT₀ hW₀' a.isAffineOpen hW₀'T a.le_preimage).1 ≤
      p.fiberι t ⁻¹ᵁ a.U := le_of_eq (preimage_pullbackChart p t b' hfst' hsnd' hrW')
  have key : ((p.fiber t).presheaf.map (homOfLE hpre.ge).op).hom.comp
        ((chartPresentationOfHom p t b' hr' hfst' hsnd' hT₀ hW₀' hW₀'T hrW' eC sigma' eD' hD'
          I hI' hsurj' a).toSourceHom) =
      (chartPresentationOfHom p t b hr hfst hsnd hT₀ hW₀ hW₀T hrW eC sigma eD hD I hI hsurj
        a).toSourceHom := by
    refine MvPolynomial.ringHom_ext (fun d => ?_) (fun i => ?_)
    · change ((p.fiber t).presheaf.map (homOfLE hpre.ge).op).hom
          ((chartPresentationOfHom p t b' hr' hfst' hsnd' hT₀ hW₀' hW₀'T hrW' eC sigma' eD' hD'
            I hI' hsurj' a).toSourceHom (MvPolynomial.C d)) = _
      have hmorR :
          ((pullback.snd p b').appLE W₀'
                (pullbackChart p b' hT₀ hW₀' a.isAffineOpen hW₀'T a.le_preimage).1
                (pullbackChart_le_right p b' hT₀ hW₀' a.isAffineOpen hW₀'T a.le_preimage) ≫
              j'.app (pullbackChart p b' hT₀ hW₀' a.isAffineOpen hW₀'T a.le_preimage).1 ≫
                (p.fiber t).presheaf.map (homOfLE hpre.ge).op) =
            r'.appLE W₀' ⊤ hrW' ≫
              (p.fiberToSpecResidueField t).appLE ⊤
                (j ⁻¹ᵁ (pullbackChart p b hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage).1)
                  le_top := by
        rw [← Category.assoc,
          appLE_chart_right p t b' hsnd' hT₀ hW₀' a.isAffineOpen hW₀'T a.le_preimage hrW',
          Category.assoc, (p.fiberToSpecResidueField t).appLE_map (U := ⊤) (e := le_top)]
      have hR : ((p.fiber t).presheaf.map (homOfLE hpre.ge).op).hom
            ((chartPresentationOfHom p t b' hr' hfst' hsnd' hT₀ hW₀' hW₀'T hrW' eC sigma' eD' hD'
              I hI' hsurj' a).toSourceHom (MvPolynomial.C d)) =
          ((p.fiberToSpecResidueField t).appLE ⊤
              (j ⁻¹ᵁ (pullbackChart p b hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage).1)
                le_top).hom
            ((r'.appLE W₀' ⊤ hrW').hom (eD'.symm d)) := by
        rw [toSourceHom_chartPresentationOfHom_C, ← CommRingCat.comp_apply,
          ← CommRingCat.comp_apply, hmorR, CommRingCat.comp_apply]
      have hL : (chartPresentationOfHom p t b hr hfst hsnd hT₀ hW₀ hW₀T hrW eC sigma eD hD
              I hI hsurj a).toSourceHom (MvPolynomial.C d) =
          ((p.fiberToSpecResidueField t).appLE ⊤
              (j ⁻¹ᵁ (pullbackChart p b hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage).1)
                le_top).hom
            ((r.appLE W₀ ⊤ hrW).hom (eD.symm d)) := by
        rw [toSourceHom_chartPresentationOfHom_C, ← CommRingCat.comp_apply,
          appLE_chart_right p t b hsnd hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage hrW,
          CommRingCat.comp_apply]
      rw [hR, hL, hsource d]
    · change ((p.fiber t).presheaf.map (homOfLE hpre.ge).op).hom
          ((chartPresentationOfHom p t b' hr' hfst' hsnd' hT₀ hW₀' hW₀'T hrW' eC sigma' eD' hD'
            I hI' hsurj' a).toSourceHom (MvPolynomial.X i)) = _
      have hmorR :
          ((pullback.fst p b').appLE a.U
                (pullbackChart p b' hT₀ hW₀' a.isAffineOpen hW₀'T a.le_preimage).1
                (pullbackChart_le_left p b' hT₀ hW₀' a.isAffineOpen hW₀'T a.le_preimage) ≫
              j'.app (pullbackChart p b' hT₀ hW₀' a.isAffineOpen hW₀'T a.le_preimage).1 ≫
                (p.fiber t).presheaf.map (homOfLE hpre.ge).op) =
            (p.fiberι t).appLE a.U
              (j ⁻¹ᵁ (pullbackChart p b hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage).1) hleL := by
        rw [← Category.assoc,
          appLE_chart_left p t b' hfst' hT₀ hW₀' a.isAffineOpen hW₀'T a.le_preimage hleR,
          Scheme.Hom.appLE_map]
      rw [toSourceHom_chartPresentationOfHom_X, toSourceHom_chartPresentationOfHom_X,
        ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, hmorR, ← CommRingCat.comp_apply,
        appLE_chart_left p t b hfst hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage hleL]
  exact Eq.trans (Stacks.Conormal.sectionsCast_eq_map _ _) (RingHom.congr_fun key z)

variable [LocallyOfFiniteType p] [IsNoetherian T]

include hT₀ in
/-- **Two members of the index and a point of both their opens admit a refining member whose
presentation absorbs the generators of both.** This is the crux of the instantiation, and the
reason the refinement condition of `Stacks.Conormal.CommonChartAssociatedGradedEquiv` is asked
for only at a refining member: the comparison of two chart presentations is a renaming of the
variables, so the refining presentation must have a variable for each generator of each of the two
given ones, and `Stacks.exists_presentation_val_eq_of_finiteType` provides exactly that because it
takes an *arbitrary* finite family of elements — here the `n₁ + n₂` restrictions of the two
generator families at once.

The affine open is shrunk inside `Y`, by
`Stacks.ConormalApproximation.exists_affineOpen_le_preimage_fiberι`, so the containment obtained is
a containment in `Y` and hence gives containments of the charts in the two ambient schemes,
`Stacks.ConormalApproximation.pullbackChart_mono`. -/
theorem exists_refining_presentedChart (ht : t ∈ T₀) (a₁ a₂ : PresentedChart p T₀ C eC)
    (x : p.fiber t) (hx₁ : x ∈ p.fiberι t ⁻¹ᵁ a₁.U) (hx₂ : x ∈ p.fiberι t ⁻¹ᵁ a₂.U) :
    ∃ (k : PresentedChart p T₀ C eC) (_ : x ∈ p.fiberι t ⁻¹ᵁ k.U)
      (h₁ : k.U ≤ a₁.U) (h₂ : k.U ≤ a₂.U)
      (ι₁ : Fin a₁.n → Fin k.n) (ι₂ : Fin a₂.n → Fin k.n),
      (∀ i, k.val (ι₁ i) = (Y.presheaf.map (homOfLE h₁).op).hom (a₁.val i)) ∧
        ∀ i, k.val (ι₂ i) = (Y.presheaf.map (homOfLE h₂).op).hom (a₂.val i) := by
  obtain ⟨U, hU, hUT, hUle, hxU⟩ :=
    exists_affineOpen_le_preimage_fiberι p t ht (a₁.U ⊓ a₂.U) x ⟨hx₁, hx₂⟩
  have h₁ : U ≤ a₁.U := hUle.trans inf_le_left
  have h₂ : U ≤ a₂.U := hUle.trans inf_le_right
  obtain ⟨n, m, P, ι, hval⟩ :=
    exists_presentedChart_val_eq p hT₀ eC hU hUT
      (Fin.addCases (fun i : Fin a₁.n => (Y.presheaf.map (homOfLE h₁).op).hom (a₁.val i))
        (fun i : Fin a₂.n => (Y.presheaf.map (homOfLE h₂).op).hom (a₂.val i)))
  refine ⟨⟨U, hU, hUT, n, m, P⟩, hxU, h₁, h₂, ι ∘ Fin.castAdd a₂.n, ι ∘ Fin.natAdd a₁.n,
    fun i => ?_, fun i => ?_⟩
  · exact (hval (Fin.castAdd a₂.n i)).trans (Fin.addCases_left i)
  · exact (hval (Fin.natAdd a₁.n i)).trans (Fin.addCases_right i)

include hr hr' hfst hsnd hfst' hsnd' hT₀ hW₀ hW₀' hW₀T hW₀'T hrW hrW' eC hD hD' hI hI'
  hsurj hsurj' in
/-- **The comparison of the two pairs of chart presentations at a refining member**, from the
renaming of the variables: `Stacks.ConormalApproximation.chartQuotientPresentationHomOfRename`,
whose two commutation laws are
`Stacks.ConormalApproximation.equiv_restrict_chartQuotientPresentationOfPullbackChart` for the one
base change and for the other. The *same* ring map `MvPolynomial.rename ι` serves both, because a
renaming does not mention the structure map `C → D`, and the two base changes put two different
such maps on `D`. -/
def chartQuotientPresentationHomOfPresentedCharts (a k : PresentedChart p T₀ C eC)
    (hUU : k.U ≤ a.U) (ιa : Fin a.n → Fin k.n)
    (hι : ∀ i, k.val (ιa i) = (Y.presheaf.map (homOfLE hUU).op).hom (a.val i)) :
    Stacks.Conormal.ChartQuotientPresentationHom
      (pullbackChart_mono p b hT₀ hW₀ a.isAffineOpen k.isAffineOpen hW₀T a.le_preimage
        k.le_preimage hUU)
      (pullbackChart_mono p b' hT₀ hW₀' a.isAffineOpen k.isAffineOpen hW₀'T a.le_preimage
        k.le_preimage hUU)
      (chartPresentationOfHom p t b hr hfst hsnd hT₀ hW₀ hW₀T hrW eC sigma eD hD I hI hsurj a)
      (chartPresentationOfHom p t b' hr' hfst' hsnd' hT₀ hW₀' hW₀'T hrW' eC sigma' eD' hD'
        I hI' hsurj' a)
      (chartPresentationOfHom p t b hr hfst hsnd hT₀ hW₀ hW₀T hrW eC sigma eD hD I hI hsurj k)
      (chartPresentationOfHom p t b' hr' hfst' hsnd' hT₀ hW₀' hW₀'T hrW' eC sigma' eD' hD'
        I hI' hsurj' k) :=
  letI := chartAlgebra p a.le_preimage eC
  letI := chartAlgebra p k.le_preimage eC
  chartQuotientPresentationHomOfRename ιa _ _ _ _
    (fun z => by
      let := sigma.toAlgebra
      exact equiv_restrict_chartQuotientPresentationOfPullbackChart p t b r j hr hfst hsnd
        hT₀ hW₀ a.isAffineOpen k.isAffineOpen hW₀T a.le_preimage k.le_preimage hrW
        (pullbackChart p b hT₀ hW₀ a.isAffineOpen hW₀T a.le_preimage)
        (pullbackChart p b hT₀ hW₀ k.isAffineOpen hW₀T k.le_preimage) rfl rfl hUU
        (pullbackChart_mono p b hT₀ hW₀ a.isAffineOpen k.isAffineOpen hW₀T a.le_preimage
          k.le_preimage hUU)
        eC eD (RingEquiv.refl Γ(Y, a.U)) (RingEquiv.refl Γ(Y, k.U)) hD
        (fun y => (algebraMap_chartAlgebra p a.le_preimage eC y).symm)
        (fun y => (algebraMap_chartAlgebra p k.le_preimage eC y).symm)
        (restrictAlgHom p eC a.le_preimage k.le_preimage hUU) (fun _ => rfl)
        a.presentation k.presentation ιa hι I hI hsurj z)
    (fun z => by
      let := sigma'.toAlgebra
      exact equiv_restrict_chartQuotientPresentationOfPullbackChart p t b' r' j' hr' hfst' hsnd'
        hT₀ hW₀' a.isAffineOpen k.isAffineOpen hW₀'T a.le_preimage k.le_preimage hrW'
        (pullbackChart p b' hT₀ hW₀' a.isAffineOpen hW₀'T a.le_preimage)
        (pullbackChart p b' hT₀ hW₀' k.isAffineOpen hW₀'T k.le_preimage) rfl rfl hUU
        (pullbackChart_mono p b' hT₀ hW₀' a.isAffineOpen k.isAffineOpen hW₀'T a.le_preimage
          k.le_preimage hUU)
        eC eD' (RingEquiv.refl Γ(Y, a.U)) (RingEquiv.refl Γ(Y, k.U)) hD'
        (fun y => (algebraMap_chartAlgebra p a.le_preimage eC y).symm)
        (fun y => (algebraMap_chartAlgebra p k.le_preimage eC y).symm)
        (restrictAlgHom p eC a.le_preimage k.le_preimage hUU) (fun _ => rfl)
        a.presentation k.presentation ιa hι I hI' hsurj' z)

include hr hr' hfst hsnd hfst' hsnd' hT₀ hW₀ hW₀' hW₀T hW₀'T hrW hrW' eC hD hD' hI hI'
  hsurj hsurj' hsource in
/-- **The comparison of the associated graded algebras of the two fibre immersions, over the
sub-family of charts Stacks 0CAY compares.** This is the instantiation of
`Stacks.Conormal.CommonChartAssociatedGradedEquiv` with 0CAY's sub-family: the index carries an
affine open `U` of `Y` above `T₀` together with a presentation of `Γ(Y, U)` over `C`, the chart of
each base change is `pr₁⁻¹U ⊓ pr₂⁻¹W₀`, and the chart-local comparison is the one the affine
statement `Stacks.ConormalApproximation.exists_finiteType_coefficients_associatedGraded_equiv`
produces — supplied here as the hypothesis `e` together with its disclosure `hind` that it is
induced by the identity of `D[x_1, …, x_n]`, which is what makes it compatible with restriction.

The three fields: the opens form a basis by
`Stacks.ConormalApproximation.isBasis_commonChartOfPresentedChart`; the chart-local comparison is
`e`; and the refinement is
`Stacks.ConormalApproximation.exists_refining_presentedChart` followed by
`Stacks.ConormalApproximation.chartQuotientPresentationHomOfPresentedCharts`. -/
def commonChartAssociatedGradedEquivOfPresentedCharts (ht : t ∈ T₀)
    (e : ∀ a : PresentedChart p T₀ C eC,
      AssociatedGraded.GradedAlgEquiv
        (I.map (MvPolynomial.C : D →+* MvPolynomial (Fin a.n) D))
        (MvPolynomial (Fin a.n) D ⧸ LinearMap.range (relationMapOfHom sigma a.relation))
        (MvPolynomial (Fin a.n) D ⧸ LinearMap.range (relationMapOfHom sigma' a.relation)))
    (hind : ∀ a, (e a).IsInducedByIdentity) :
    Stacks.Conormal.CommonChartAssociatedGradedEquiv j j'
      (commonChartOfPresentedChart p t b b' hfst hsnd hfst' hsnd' hT₀ hW₀ hW₀' hW₀T hW₀'T
        hrW hrW' eC) :=
  Stacks.Conormal.commonChartAssociatedGradedEquivOfPresentations j j' _
    (isBasis_commonChartOfPresentedChart p t b b' hfst hsnd hfst' hsnd' hT₀ hW₀ hW₀' hW₀T hW₀'T
      hrW hrW' eC ht)
    (fun a => MvPolynomial (Fin a.n) D)
    (fun a => I.map (MvPolynomial.C : D →+* MvPolynomial (Fin a.n) D))
    (fun a => LinearMap.range (relationMapOfHom sigma a.relation))
    (fun a => LinearMap.range (relationMapOfHom sigma' a.relation))
    (fun a => chartPresentationOfHom p t b hr hfst hsnd hT₀ hW₀ hW₀T hrW eC sigma eD hD
      I hI hsurj a)
    (fun a => chartPresentationOfHom p t b' hr' hfst' hsnd' hT₀ hW₀' hW₀'T hrW' eC sigma' eD' hD'
      I hI' hsurj' a)
    e hind
    (fun a z => toSourceHom_cast_eq p t b b' hr hr' hfst hsnd hfst' hsnd' hT₀ hW₀ hW₀' hW₀T hW₀'T
      hrW hrW' eC sigma sigma' eD eD' hD hD' I hI hI' hsurj hsurj' hsource a z)
    (fun a₁ a₂ x hx₁ hx₂ => by
      rw [commonChartOpens_commonChartOfPresentedChart] at hx₁ hx₂
      obtain ⟨k, hxk, h₁, h₂, ι₁, ι₂, hι₁, hι₂⟩ :=
        exists_refining_presentedChart p t hT₀ eC ht a₁ a₂ x hx₁ hx₂
      refine ⟨k, ?_,
        pullbackChart_mono p b hT₀ hW₀ a₁.isAffineOpen k.isAffineOpen hW₀T a₁.le_preimage
          k.le_preimage h₁,
        pullbackChart_mono p b' hT₀ hW₀' a₁.isAffineOpen k.isAffineOpen hW₀'T a₁.le_preimage
          k.le_preimage h₁,
        pullbackChart_mono p b hT₀ hW₀ a₂.isAffineOpen k.isAffineOpen hW₀T a₂.le_preimage
          k.le_preimage h₂,
        pullbackChart_mono p b' hT₀ hW₀' a₂.isAffineOpen k.isAffineOpen hW₀'T a₂.le_preimage
          k.le_preimage h₂,
        ⟨chartQuotientPresentationHomOfPresentedCharts p t b b' hr hr' hfst hsnd hfst' hsnd'
          hT₀ hW₀ hW₀' hW₀T hW₀'T hrW hrW' eC sigma sigma' eD eD' hD hD' I hI hI' hsurj hsurj'
          a₁ k h₁ ι₁ hι₁⟩,
        ⟨chartQuotientPresentationHomOfPresentedCharts p t b b' hr hr' hfst hsnd hfst' hsnd'
          hT₀ hW₀ hW₀' hW₀T hW₀'T hrW hrW' eC sigma sigma' eD eD' hD hD' I hI hI' hsurj hsurj'
          a₂ k h₂ ι₂ hι₂⟩⟩
      rw [commonChartOpens_commonChartOfPresentedChart]
      exact hxk)

include hr hr' hfst hsnd hfst' hsnd' hT₀ hW₀ hW₀' hW₀T hW₀'T hrW hrW' eC hD hD' hI hI'
  hsurj hsurj' hsource in
/-- **The conormal algebras of the two fibre immersions are isomorphic.** This is the conclusion
`Stacks.ConormalApproximation.HasConormalIso` asks for, obtained from the comparison over the
sub-family by `Stacks.Conormal.nonempty_conormalAlgebra_iso_of_commonChartAssociatedGradedEquiv`.

What remains to supply, for the particular `W = W' = Spec(𝒪^∧_{S,s})` of Stacks 0CAY, is the
chart-local comparison `e` with its disclosure `hind`, and nothing else: all the geometric input
is discharged here. -/
theorem nonempty_conormalAlgebra_iso_of_presentedCharts (ht : t ∈ T₀)
    (e : ∀ a : PresentedChart p T₀ C eC,
      AssociatedGraded.GradedAlgEquiv
        (I.map (MvPolynomial.C : D →+* MvPolynomial (Fin a.n) D))
        (MvPolynomial (Fin a.n) D ⧸ LinearMap.range (relationMapOfHom sigma a.relation))
        (MvPolynomial (Fin a.n) D ⧸ LinearMap.range (relationMapOfHom sigma' a.relation)))
    (hind : ∀ a, (e a).IsInducedByIdentity) :
    Nonempty ((Stacks.Conormal.conormalAlgebra j).algebra ≅
      (Stacks.Conormal.conormalAlgebra j').algebra) :=
  Stacks.Conormal.nonempty_conormalAlgebra_iso_of_commonChartAssociatedGradedEquiv j j'
    (commonChartAssociatedGradedEquivOfPresentedCharts p t b b' hr hr' hfst hsnd hfst' hsnd'
      hT₀ hW₀ hW₀' hW₀T hW₀'T hrW hrW' eC sigma sigma' eD eD' hD hD' I hI hI' hsurj hsurj'
      hsource ht e hind)

include hrW hrW' hsource in
omit [AlgebraicGeometry.IsNoetherian T] in
/-- **The ideal `I` is the same on both sides.** The hypothesis `hI'` of the comparison is not an
extra condition: both `(ker Γ(W, W₀) ⟶ κ(t)).map eD` and `(ker Γ(W', W₀') ⟶ κ(t)).map eD'` are the
kernel of the *one* map `D ⟶ κ(t)` that `hsource` says the two identifications induce. -/
theorem map_ker_appLE_eq :
    (RingHom.ker (r.appLE W₀ ⊤ hrW).hom).map (eD : Γ(W, W₀) →+* D) =
      (RingHom.ker (r'.appLE W₀' ⊤ hrW').hom).map (eD' : Γ(W', W₀') →+* D) := by
  rw [Ideal.map_comap_of_equiv eD, Ideal.map_comap_of_equiv eD']
  exact Ideal.ext fun d => by
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    rw [hsource d]

include hr hr' hfst hsnd hfst' hsnd' hT₀ hW₀ hW₀' hW₀T hW₀'T hrW hrW' eC hD hD' hI
  hsurj hsurj' hsource in
/-- **The conormal algebras of the two fibre immersions are isomorphic, with the ideal named only
once.** The same statement as
`Stacks.ConormalApproximation.nonempty_conormalAlgebra_iso_of_presentedCharts`, with the
hypothesis `hI'` discharged by `Stacks.ConormalApproximation.map_ker_appLE_eq`: the geometric
input left to a caller is the pair of fibre immersions, the compatibility `hsource` of the two
identifications of the chart ring of the base with `D`, the naming `hI` of the ideal, and the
chart-local comparison `e` with its disclosure `hind`. -/
theorem nonempty_conormalAlgebra_iso_of_presentedCharts_of_eq_on (ht : t ∈ T₀)
    (e : ∀ a : PresentedChart p T₀ C eC,
      AssociatedGraded.GradedAlgEquiv
        (I.map (MvPolynomial.C : D →+* MvPolynomial (Fin a.n) D))
        (MvPolynomial (Fin a.n) D ⧸ LinearMap.range (relationMapOfHom sigma a.relation))
        (MvPolynomial (Fin a.n) D ⧸ LinearMap.range (relationMapOfHom sigma' a.relation)))
    (hind : ∀ a, (e a).IsInducedByIdentity) :
    Nonempty ((Stacks.Conormal.conormalAlgebra j).algebra ≅
      (Stacks.Conormal.conormalAlgebra j').algebra) :=
  nonempty_conormalAlgebra_iso_of_presentedCharts p t b b' hr hr' hfst hsnd hfst' hsnd'
    hT₀ hW₀ hW₀' hW₀T hW₀'T hrW hrW' eC sigma sigma' eD eD' hD hD' I hI
    ((map_ker_appLE_eq t hrW hrW' eD eD' hsource).symm.trans hI) hsurj hsurj' hsource
    ht e hind

end Comparison

end Stacks.ConormalApproximation

end
