module

public import StacksFrontier.AlgebraicGeometry.Conormal.SplitCotangentFibre
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness

/-!
# Towards exactness at the middle term of the conormal sequence

For immersions `Z --i--→ Y --j--→ X` of schemes, [Stacks Project, Tag 062S] asserts that the
canonical sequence `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` is exact. The first arrow is
`Stacks.AlgebraicGeometry.conormalSequenceLeftMap`, the second is
`Stacks.Immersion.conormalSequenceRightMap`, and exactness at `𝒞_{Z/Y}` — that the second arrow
is an epimorphism — is `Stacks.Immersion.epi_conormalSequenceRightMap`.

This file collects three independent ingredients of the other two clauses, namely the vanishing
of the composite and exactness at the middle term `𝒞_{Z/X}`. Both of those clauses are proved in
`StacksFrontier.AlgebraicGeometry.Conormal.ConormalSequenceExact`, which does not import this file:
it assembles them from the variants `Stacks.Conormal.exact_mapCotangent_comap` and
`Stacks.Immersion.exact_of_chartwise` of
`StacksFrontier.AlgebraicGeometry.Conormal.ConormalSequenceMiddle`.

## Main results

* `Stacks.AlgebraicGeometry.immersionConormalSheafMap_self_eq_zero`: the canonical map of
  [Stacks Project, Tag 01R4] attached to the degenerate square `i ≫ j = i ≫ j` is zero. Its
  ambient ring map is `j^♯`, which kills the ideal cutting out `Y`, so the affine
  characterisation `Stacks.Immersion.IsInducedConormalSheafMap` is satisfied by the zero map and
  `Stacks.Immersion.immersionConormalSheafMap_unique` identifies the two. This is the
  morphism-level reason the composite of the two arrows of the conormal sequence vanishes.
* `Stacks.AlgebraicGeometry.cotangent_exact_of_surjective_quotient`: the commutative-algebra
  content of exactness at the middle term. For a surjection `q : R ⟶ S` and an ideal `K ⊆ S`,
  writing `J = ker q` and `I = q⁻¹K`, the sequence `J/J² ⟶ I/I² ⟶ K/K²` of
  [Stacks Project, Tag 065V] is exact at `I/I²`. Over an affine chart `V ⊆ X` with `J ⊆ I` the
  ideals cutting out `Y` and `Z`, this is the exactness of
  `J/(J² + IJ) ⟶ I/I² ⟶ I/(J + I²)` that [Stacks Project, Tag 062S] reduces to.
* `Stacks.AlgebraicGeometry.exact_of_app_exact_nbhd`: the local-to-global criterion. A short
  complex of sheaves of modules whose sections sequence is exact over arbitrarily small opens
  around every point is exact. This is the exactness counterpart of the monomorphy criterion
  `Stacks.ConormalSequenceTwoImmersions.mono_of_app_injective_nbhd`, and the only such criterion
  in the library: exactness is stalkwise by
  `AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact`, and a stalk class killed
  by the second map is the germ of a section whose image already vanishes on a smaller open.

## Implementation notes

The affine bookkeeping that joins the three results above into exactness at the middle term —
a family of compatible affine charts `V ⊆ X` with `j ⁻¹ᵁ V` affine and `j.app V` surjective,
together with quotient-spectrum presentations of the three scheme-theoretic intersections,
cofinal at every point of `Z`, and the two generator formulas reading each arrow of the sequence
on such a chart as `Ideal.mapCotangent` — is
`Stacks.Immersion.ConormalChart` of
`StacksFrontier.AlgebraicGeometry.Conormal.ConormalSequenceMiddle`.

The two clauses cannot be stated in
`StacksFrontier.AlgebraicGeometry.Conormal.ConormalSequence`, which defines only the second arrow:
the first arrow lives in `StacksFrontier.AlgebraicGeometry.Conormal.SplitSequence`, which imports
that file. `ConormalSequenceExact` therefore states them with its own spelling
`Stacks.Immersion.conormalLeftMap` of the first arrow, which
`Stacks.AlgebraicGeometry.conormalSequenceLeftMap_eq` identifies with
`Stacks.AlgebraicGeometry.conormalSequenceLeftMap`.

## References

* [Stacks Project, Tag 062S](https://stacks.math.columbia.edu/tag/062S)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 065V](https://stacks.math.columbia.edu/tag/065V)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.ClosedImmersion Stacks.Immersion

universe u

namespace Stacks.AlgebraicGeometry

variable {Z Y X : Scheme.{u}}

/-- The zero morphism of sheaves of modules is the zero map on sections over every open. -/
private theorem zero_val_app {T : TopCat.{u}}
    {O : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    {M N : SheafOfModules.{u} O} (W : (Opens T)ᵒᵖ) :
    (0 : M ⟶ N).val.app W = 0 := rfl

/-- The zero morphism of sheaves of modules sends every section to zero. -/
@[simp]
private theorem zero_val_app_apply {T : TopCat.{u}}
    {O : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    {M N : SheafOfModules.{u} O} (W : (Opens T)ᵒᵖ) (x : M.val.obj W) :
    ConcreteCategory.hom ((0 : M ⟶ N).val.app W) x = 0 := by
  rw [zero_val_app]
  exact LinearMap.zero_apply x

/-- The zero map satisfies the affine characterisation for the degenerate square
`i ≫ j = i ≫ j`: the ambient ring map there is `j^♯`, which kills the ideal of `Y`. -/
theorem isInducedConormalSheafMap_zero (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] :
    Stacks.Immersion.IsInducedConormalSheafMap i j i j rfl 0 := by
  intro U hU V hV hUV I J eZ heZ eW heW a b hab
  have hJ : RingHom.ker (j.app V).hom = J := by
    have hker := Stacks.Conormal.ker_appLE_eq_of_affineModel j V hV J eW heW
    rwa [Scheme.Hom.appLE_eq_app] at hker
  have ha0 : (j.app V).hom (a : Γ(X, V)) = 0 := RingHom.mem_ker.mp (hJ.ge a.2)
  have hb0 : (b : Γ(Y, U)) = 0 := by
    rw [hab, Scheme.Hom.appLE, CommRingCat.comp_apply, ha0, map_zero]
  rw [show b = 0 from Subtype.ext hb0]
  simp only [map_zero]
  rw [Adjunction.homEquiv_unit]
  simp only [Functor.map_zero, Limits.comp_zero, zero_val_app]
  exact map_zero _

/-- **The conormal map of the degenerate square `i ≫ j = i ≫ j` vanishes.** The ambient ring map
of that square is `j^♯`, which kills the ideal cutting out `Y`, so the affine characterisation of
[Stacks Project, Tag 01R4] forces the map to send every generator to zero; by
`Stacks.Immersion.immersionConormalSheafMap_unique` it is therefore the zero map.

This is the morphism-level reason the composite of the two maps of the conormal sequence of
[Stacks Project, Tag 062S] vanishes. -/
theorem immersionConormalSheafMap_self_eq_zero (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] :
    Stacks.Immersion.immersionConormalSheafMap i j i j
        (Stacks.Immersion.toShHom_square (rfl : i ≫ j = i ≫ j)) = 0 :=
  (Stacks.Immersion.immersionConormalSheafMap_unique i j i j rfl 0
    (isInducedConormalSheafMap_zero i j)).symm

/-! ### The commutative-algebra core

Over an affine chart the conormal sequence is the sequence of cotangent modules of a nested pair
of ideals, and its exactness at the middle term is the lemma below. -/

/-- **The affine content of exactness at the middle term of the conormal sequence.** Let
`q : R ⟶ S` be a surjective ring map, let `K ⊆ S` be an ideal, let `J = ker q` and let
`I = q⁻¹K`, so that `J ≤ I`. Then

`J/J² ⟶ I/I² ⟶ K/K²`

is exact at `I/I²`, the maps being those of [Stacks Project, Tag 065V].

Writing `S = R/J`, the identification `K/K² = I/(J + I²)` turns this into the exactness of
`J/(J² + IJ) ⟶ I/I² ⟶ I/(J + I²)` which [Stacks Project, Tag 062S] asserts over an affine chart.
The kernel of the second map is computed by `Ideal.mapCotangent_ker_of_surjective`; the choice of
its hypothesis `K.comap q = ker q ⊔ I` is available here precisely because `ker q ≤ I`. -/
theorem cotangent_exact_of_surjective_quotient
    {R S : Type*} [CommRing R] [CommRing S]
    (q : R →+* S) (hq : Function.Surjective q) (K : Ideal S) :
    letI : Algebra R S := q.toAlgebra
    let J : Ideal R := RingHom.ker q
    let I : Ideal R := K.comap q
    Function.Exact
      (Ideal.mapCotangent J I (Algebra.ofId R R) (by
        intro x hx
        change q x ∈ K
        change q x = 0 at hx
        rw [hx]
        exact K.zero_mem))
      (Ideal.mapCotangent I K (Algebra.ofId R S) (by intro x hx; exact hx)) := by
  classical
  let : Algebra R S := q.toAlgebra
  intro J I
  have hJI : J ≤ I := (RingHom.ker_eq_comap_bot q).le.trans (Ideal.comap_mono bot_le)
  let f := Ideal.mapCotangent J I (Algebra.ofId R R)
    (show J ≤ I.comap (Algebra.ofId R R) from fun x hx => hJI hx)
  let g := Ideal.mapCotangent I K (Algebra.ofId R S)
    (show I ≤ K.comap (Algebra.ofId R S) from fun _ hx => hx)
  change Function.Exact f g
  rw [LinearMap.exact_iff, Ideal.mapCotangent_ker_of_surjective hq (sup_eq_right.mpr hJI).symm]
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_range]
    rcases Submodule.mem_map.mp hx with ⟨z, hz, rfl⟩
    have hzker : (z : R) ∈ RingHom.ker q := (Submodule.mem_inf.mp (Submodule.mem_comap.mp hz)).1
    refine ⟨J.toCotangent ⟨(z : R), by simpa [J] using hzker⟩, ?_⟩
    simp [f, Ideal.mapCotangent_toCotangent]
  · intro x hx
    rw [LinearMap.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    obtain ⟨a, rfl⟩ := J.toCotangent_surjective y
    refine Submodule.mem_map.mpr ⟨⟨(a : R), hJI a.2⟩, ?_, ?_⟩
    · exact Submodule.mem_comap.mpr (Submodule.mem_inf.mpr ⟨a.2, hJI a.2⟩)
    · simp [f, Ideal.mapCotangent_toCotangent]

/-! ### Exactness from exactness of sections over arbitrarily small opens -/

/-- **Exactness of a short complex of sheaves of modules is a local condition on sections.** If
around every point there are arbitrarily small opens over which the sequence of sections is
exact — every section of the middle term killed by the second map is the image of a section of
the first — then the short complex is exact.

Exactness is stalkwise by
`AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact`; a stalk class killed by the
second map is the germ of a section whose image already vanishes on a smaller open, and shrinking
further to an open on which the sections are exact produces a section whose germ is the class
wanted.

This is the exactness counterpart of the monomorphy criterion
`Stacks.ConormalSequenceTwoImmersions.mono_of_app_injective_nbhd`. -/
theorem exact_of_app_exact_nbhd {T : TopCat.{u}}
    {O : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    (S : ShortComplex (_root_.SheafOfModules.{u} O))
    (h : ∀ (x : T) (W : Opens T), x ∈ W → ∃ W' : Opens T, W' ≤ W ∧ x ∈ W' ∧
      ∀ β : ToType (S.X₂.val.obj (op W')),
        (S.g.val.app (op W')).hom β = 0 →
        ∃ α : ToType (S.X₁.val.obj (op W')), (S.f.val.app (op W')).hom α = β) :
    S.Exact := by
  rw [AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.moduleCat_exact_iff]
  intro m hm
  obtain ⟨W₀, hxW₀, s, hs⟩ := TopCat.Presheaf.exists_germ_eq S.X₂.val.presheaf m
  have hgs : (TopCat.Presheaf.germ S.X₃.val.presheaf W₀ x hxW₀).hom
      ((S.g.val.app (op W₀)).hom s) = 0 := by
    rw [← AlgebraicGeometry.SheafOfModules.stalkMap_germ O x S.g W₀ hxW₀ s, hs]
    exact hm
  obtain ⟨W₁, hxW₁, i₁, i₂, hW₁⟩ := TopCat.Presheaf.germ_eq S.X₃.val.presheaf x hxW₀ hxW₀
    ((S.g.val.app (op W₀)).hom s) 0 (by rw [hgs, map_zero])
  obtain ⟨W', hW'W₁, hxW', hex⟩ := h x W₁ hxW₁
  have hle : W' ≤ W₀ := le_trans hW'W₁ i₁.le
  have hW₁0 : (S.X₃.val.map i₁.op).hom ((S.g.val.app (op W₀)).hom s) = 0 :=
    hW₁.trans (map_zero _)
  have hβ : (S.g.val.app (op W'))
      ((S.X₂.val.map (homOfLE hle).op) s) = 0 := by
    rw [PresheafOfModules.naturality_apply S.g.val (homOfLE hle).op s,
      show (homOfLE hle).op = i₁.op ≫ (homOfLE hW'W₁).op from Subsingleton.elim _ _,
      PresheafOfModules.map_comp_apply, hW₁0]
    exact map_zero _
  obtain ⟨α, hα⟩ := hex _ hβ
  refine ⟨(TopCat.Presheaf.germ S.X₁.val.presheaf W' x hxW').hom α, ?_⟩
  have key : (AlgebraicGeometry.SheafOfModules.stalkMap O x S.f).hom
      ((TopCat.Presheaf.germ S.X₁.val.presheaf W' x hxW').hom α) = m := by
    rw [AlgebraicGeometry.SheafOfModules.stalkMap_germ O x S.f W' hxW' α, hα]
    exact (TopCat.Presheaf.germ_res_apply S.X₂.val.presheaf (homOfLE hle) x hxW' s).trans hs
  exact key

end Stacks.AlgebraicGeometry

end
