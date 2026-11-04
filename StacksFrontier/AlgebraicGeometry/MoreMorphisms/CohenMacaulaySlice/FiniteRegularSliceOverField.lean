module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.RegularSliceThroughPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Locus
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocusOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.OpenSubschemeRankBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ClosedPointResidueField

/-!
# A regularly immersed finite point of a scheme over a field

Let `W` be a nonempty scheme which is flat and locally of finite presentation over a field `k`.
Then `W` contains a regularly immersed subscheme `Z` which is finite locally free of positive
degree over `k`. The Cohen–Macaulay locus of `W ⟶ Spec k` is open (Stacks 045U) and dense in
the fibre, hence nonempty; since `W` is Jacobson it contains a closed point `v` there; Stacks 0570
produces a regular immersion `Z ⟶ W` through `v` which is flat, locally of finite presentation
and locally quasi-finite over `k` and whose fibre over the unique point of `Spec k` is `{v}`. So
`Z` is a single point, quasi-compact and locally quasi-finite over the Artinian scheme `Spec k`,
hence finite over it, and finite flat of finite presentation means finite locally free
(Stacks 02KB), of degree at least one because `Z` is nonempty.

## Main results

* `AlgebraicGeometry.exists_regularImmersion_isFiniteLocallyFreeOfRank_of_field`: the regularly
  immersed finite subscheme.
* `Stacks.AlgebraicGeometry.exists_isClosed_isCohenMacaulayAt`: a morphism which is flat, locally
  of finite presentation and has nonempty source and Jacobson target is Cohen-Macaulay at some
  point of the source which is closed there.
* `Stacks.AlgebraicGeometry.exists_isRegularImmersion_isFiniteLocallyFreeOfRank_of_field`: the
  finite regular slice of a nonempty scheme locally of finite presentation over a field, with no
  flatness hypothesis (every scheme over a field is flat over it).

## Implementation notes

The Cohen-Macaulay locus is dense in the *scheme-theoretic* fibre rather than in the source, so
density alone does not place a closed point of the source in it; what is used in
`Stacks.AlgebraicGeometry.exists_isClosed_isCohenMacaulayAt` is only that the locus is nonempty,
which the fibrewise density gives, together with openness and the density of the closed points of
the source. This is why that result holds over any Jacobson base and not just over a field.

In `Stacks.AlgebraicGeometry.exists_isRegularImmersion_isFiniteLocallyFreeOfRank_of_field`
positivity of the degree is read off the global sections rather than from the point of the slice:
`AlgebraicGeometry.finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank` identifies the degree
with the dimension of `Γ(Z, ⊤)` over `k`, and `Γ(Z, ⊤)` is nontrivial because `Z` is nonempty.

## References

* [Stacks Project, Tag 00PJ](https://stacks.math.columbia.edu/tag/00PJ)
* [Stacks Project, Tag 01TB](https://stacks.math.columbia.edu/tag/01TB)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 045U](https://stacks.math.columbia.edu/tag/045U)
* [Stacks Project, Tag 0570](https://stacks.math.columbia.edu/tag/0570)
* [Stacks Project, Tag 06DA](https://stacks.math.columbia.edu/tag/06DA)
-/

@[expose] public section

open CategoryTheory Stacks.AlgebraicGeometry Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace AlgebraicGeometry

/-- A flat morphism locally of finite presentation with nonempty source and Jacobson target is
Cohen-Macaulay at a point closed in its source. -/
private theorem exists_isClosed_isCohenMacaulayAt_aux {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [JacobsonSpace S] (hne : Nonempty X) :
    ∃ x : X, IsClosed ({x} : Set X) ∧
      Scheme.Hom.IsCohenMacaulayAt f
        (fun y ↦ isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f y) x := by
  have hf : ∀ y : S, IsLocallyNoetherian (f.fiber y) := fun y ↦
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f y
  have hopen : IsOpen {x : X | Scheme.Hom.IsCohenMacaulayAt f hf x} :=
    isOpen_setOf_isCohenMacaulayAt f
  obtain ⟨x₀⟩ := hne
  have _hfibne : Nonempty (f.fiber (f x₀)) := ⟨f.asFiber x₀⟩
  obtain ⟨w, hw⟩ := (dense_cohenMacaulayAt_fiber f (f x₀)).nonempty
  have _hjac : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hxCM, hxcl⟩ :=
    nonempty_inter_closedPoints ⟨f.fiberι (f x₀) w, hw⟩ hopen.isLocallyClosed
  exact ⟨x, hxcl, hxCM⟩

/-- If the fibre of `i ≫ f` over a point is a single point `z` and the target of `f` is
a single point, then the source of `i` is a subsingleton. -/
private theorem subsingleton_of_preimage_singleton {Z X S : Scheme.{u}} [Subsingleton S]
    (i : Z ⟶ X) (f : X ⟶ S) (z : Z) (x : X) (hfib : (i ≫ f) ⁻¹' {f x} = {z}) :
    Subsingleton Z := by
  refine ⟨fun z₁ z₂ ↦ ?_⟩
  have h₁ : z₁ ∈ ({z} : Set Z) := hfib ▸ Subsingleton.elim ((i ≫ f) z₁) (f x)
  have h₂ : z₂ ∈ ({z} : Set Z) := hfib ▸ Subsingleton.elim ((i ≫ f) z₂) (f x)
  exact h₁.trans h₂.symm

/-- **A regularly immersed finite point of a scheme over a field.** A nonempty scheme which is
flat and locally of finite presentation over a field `k` admits a regular immersion `Z ⟶ W`
with `Z` finite locally free of some positive degree over `k`. -/
theorem exists_regularImmersion_isFiniteLocallyFreeOfRank_of_field {k : Type u} [Field k]
    {W : Scheme.{u}} (g : W ⟶ Spec (.of k)) [Flat g] [LocallyOfFinitePresentation g]
    [Nonempty W] :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ W) (_ : IsImmersion i), IsRegularImmersion i ∧
      ∃ d : ℕ, 0 < d ∧ Stacks.Morphisms.IsFiniteLocallyFreeOfRank (i ≫ g) d := by
  classical
  obtain ⟨v, hvcl, hvCM⟩ := exists_isClosed_isCohenMacaulayAt_aux g ‹Nonempty W›
  obtain ⟨Z, i, z, hi, -, hreg, hflatZ, hlfpZ, hlqfZ, hfibZ⟩ :=
    exists_regularImmersion_flat_locallyQuasiFinite_singleton_fiber_of_isCohenMacaulayAt
      g v ⟨_, hvCM⟩ (isClosed_asFiber_of_isClosed g hvcl)
  have hpt : ∀ a b : Spec (.of k), a = b := fun a b =>
    Subsingleton.elim (α := PrimeSpectrum k) a b
  have : Subsingleton Z := subsingleton_of_preimage_singleton i g z v hfibZ
  have : Finite Z := Finite.of_subsingleton
  have : QuasiCompact (i ≫ g) := ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩
  have : IsLocallyArtinian (Spec (.of k)) := Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  have : IsFinite (i ≫ g) := IsFinite.of_locallyQuasiFinite _
  have : Stacks.Morphisms.IsFiniteLocallyFree (i ≫ g) :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).2
      ⟨inferInstance, hflatZ, hlfpZ⟩
  refine ⟨Z, i, hi, hreg, (i ≫ g).finrank (g v), ?_, ?_⟩
  · exact hpt ((i ≫ g) z) (g v) ▸ Scheme.Hom.one_le_finrank_map (i ≫ g) z
  · rw [Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq]
    intro s
    rw [hpt s (g v)]

end AlgebraicGeometry

open AlgebraicGeometry

namespace Stacks.AlgebraicGeometry

/-! ### A Cohen-Macaulay point closed in the source -/

/-- **A flat morphism locally of finite presentation with nonempty source and Jacobson target is
Cohen-Macaulay at a point closed in its source.**

The Cohen-Macaulay locus is open by Stacks 045U and nonempty because it is dense in the
scheme-theoretic fibre through any point of the source, which is nonempty. The source is a
Jacobson space because the morphism is locally of finite type, so its closed points are dense
and meet that open. -/
theorem exists_isClosed_isCohenMacaulayAt {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [JacobsonSpace S] (hne : Nonempty X) :
    ∃ x : X, IsClosed ({x} : Set X) ∧
      Scheme.Hom.IsCohenMacaulayAt f
        (fun y ↦ isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f y) x := by
  exact exists_isClosed_isCohenMacaulayAt_aux f hne

/-! ### The slice over a field -/

/-- **A nonempty scheme locally of finite presentation over a field carries a regular immersion
whose source is finite locally free of positive degree over the field.** -/
theorem exists_isRegularImmersion_isFiniteLocallyFreeOfRank_of_field (k : Type u) [Field k]
    {V : Scheme.{u}} (f : V ⟶ Spec (CommRingCat.of k)) [LocallyOfFinitePresentation f]
    (hne : Nonempty V) :
    ∃ (d : ℕ) (_ : 0 < d) (Z : Scheme.{u}) (i : Z ⟶ V) (hi : IsImmersion i),
      letI := hi
      IsRegularImmersion i ∧ Stacks.Morphisms.IsFiniteLocallyFreeOfRank (i ≫ f) d := by
  obtain ⟨x, hxcl, hxCM⟩ := exists_isClosed_isCohenMacaulayAt_aux f hne
  obtain ⟨Z, i, z, hi, -, hreg, -, -, hqf, hfib⟩ :=
    exists_regularImmersion_flat_locallyQuasiFinite_singleton_fiber_of_isCohenMacaulayAt
      f x ⟨_, hxCM⟩ (isClosed_asFiber_of_isClosed f hxcl)
  have hsub : Subsingleton Z := subsingleton_of_preimage_singleton i f z x hfib
  have _hZne : Nonempty Z := ⟨z⟩
  have _hZfin : Finite Z := Finite.of_subsingleton
  have _hqc : QuasiCompact (i ≫ f) := inferInstance
  have _hfinite : IsFinite (i ≫ f) := IsFinite.of_locallyQuasiFinite (i ≫ f)
  obtain ⟨d, hd⟩ := exists_isFiniteLocallyFreeOfRank_of_isFinite (i ≫ f)
  refine ⟨d, ?_, Z, i, hi, hreg, hd⟩
  have _hpa : IsAffineHom (i ≫ f) := hd.toIsAffineHom
  let _ : Algebra k ↑Γ(Z, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (i ≫ f).appTop).hom.toAlgebra
  obtain ⟨hfin, hrank⟩ :=
    finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank (i ≫ f) d (h := hd)
  have _hopne : Nonempty ↥(⊤ : Z.Opens) := ⟨⟨z, trivial⟩⟩
  have _hnt : Nontrivial ↑Γ(Z, ⊤) := inferInstance
  exact hrank ▸ Module.finrank_pos

end Stacks.AlgebraicGeometry

end
