module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Pushout.IntegralFibre

/-!
# Compatible affine opens for a closed immersion and an integral morphism

Let `i : Z ⟶ X` be a closed immersion and `j : Z ⟶ Y` an integral morphism, and assume the
fibrewise condition of [Stacks Project, Tag 0ECI]: every fibre of `j` maps under `i` into a
single affine open of `X`.  [Stacks Project, Tag 0ECJ] then produces, for every `y : Y`, affine
opens `U ⊆ X` and `V ⊆ Y` with `y ∈ V` and `i ⁻¹ᵁ U = j ⁻¹ᵁ V`.  These compatible charts are
what the construction of the pushout `Y ⨿_Z X` of [Stacks Project, Tag 0E25] glues over.

## Main results

* `Stacks.Pushout.exists_isAffineOpen_preimage_le`: around any point whose fibre under a
  universally closed morphism lies in a given open, there is an affine neighbourhood whose whole
  preimage does.
* `Stacks.Pushout.exists_basicOpen_image_fibre_le`: the geometric form of the basic-open
  separation of `StacksFrontier.AlgebraicGeometry.Pushout.IntegralFibre`.
* `Stacks.Pushout.exists_affineOpens_preimage_eq` is Tag 0ECJ.

## Implementation notes

The source proves the separation step by citing [Stacks Project, Tag 0E21], a statement about a
scheme carrying an ample invertible sheaf whose proof writes the scheme as a limit of schemes of
finite type over `ℤ`.  Tag 0ECJ only ever uses it for an *affine* scheme with the structure
sheaf, and that case is proved elementarily in
`StacksFrontier.AlgebraicGeometry.Pushout.IntegralFibre`; `exists_basicOpen_image_fibre_le` is the
translation of `Stacks.Pushout.exists_basicOpen_image_fibre` from prime spectra to opens of
schemes.  So none of the ample-sheaf machinery is needed here.

Both the shrinking steps use that `j` is a closed map, which holds because an integral morphism
is universally closed.  The translation between points of an affine open `U` and primes of
`Γ(X, U)` is `AlgebraicGeometry.IsAffineOpen.primeIdealOf` together with
`AlgebraicGeometry.IsAffineOpen.fromSpec`; the two compatibilities that carry the whole argument
are `AlgebraicGeometry.IsAffineOpen.comap_primeIdealOf_appLE`, which says that the prime of a
point is natural in a morphism, and `AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec`,
which says the same for the map back.

The statement of Tag 0ECJ is given for a bare pair of morphisms with the fibre hypothesis as an
explicit argument, rather than for a bundled record of the data of Situation 0ECI; the bundled
form follows by supplying the record's fields.

## References

* [Stacks Project, Tag 0E21](https://stacks.math.columbia.edu/tag/0E21)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
* [Stacks Project, Tag 0ECJ](https://stacks.math.columbia.edu/tag/0ECJ)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Pushout

variable {X Y Z : Scheme.{u}}

/-- For a closed map `f` and an open `Ω`, there is an open `W` containing every point whose fibre
lies in `Ω`, with `f ⁻¹ᵁ W ≤ Ω`. -/
private theorem exists_opens_preimage_le {A B : Scheme.{u}} (f : A ⟶ B) (hf : IsClosedMap f)
    (Ω : A.Opens) :
    ∃ W : B.Opens, (∀ b, (∀ a, f a = b → a ∈ Ω) → b ∈ W) ∧ f ⁻¹ᵁ W ≤ Ω :=
  ⟨⟨(f '' (Ω : Set A)ᶜ)ᶜ, isOpen_compl_iff.mpr (hf _ (isClosed_compl_iff.mpr Ω.2))⟩,
    fun _ hb ⟨a, ha, hab⟩ ↦ ha (hb a hab),
    fun a ha ↦ Classical.byContradiction fun hnot ↦
      (ha : f a ∈ (f '' (Ω : Set A)ᶜ)ᶜ) ⟨a, hnot, rfl⟩⟩

/-- **An affine neighbourhood whose whole preimage is small.**  Let `j : Z ⟶ Y` be universally
closed and let `Ω` be an open of `Z` containing the fibre of `j` over `y`.  Then `y` has an
affine open neighbourhood `V` with `j ⁻¹ᵁ V ≤ Ω`.

The complement of the image of `Ωᶜ` is such a neighbourhood, and an affine open inside it is
found by `AlgebraicGeometry.exists_isAffineOpen_mem_and_subset`. -/
theorem exists_isAffineOpen_preimage_le (j : Z ⟶ Y) [UniversallyClosed j] {y : Y} {Ω : Z.Opens}
    (hΩ : ∀ z : Z, j z = y → z ∈ Ω) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ y ∈ V ∧ j ⁻¹ᵁ V ≤ Ω := by
  obtain ⟨V₀, hmem, hle⟩ := exists_opens_preimage_le j j.isClosedMap Ω
  obtain ⟨V, hV, hyV, hVle⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := V₀) (hmem y hΩ)
  exact ⟨V, hV, hyV, (j.preimage_mono hVle).trans hle⟩

/-- **A basic open separating a fibre, geometrically.**  Let `i : Z ⟶ X` and `j : Z ⟶ Y` with `j`
integral, let `U` be an affine open of `X` and `V` an affine open of `Y` containing `y`, and
suppose `j ⁻¹ᵁ V ≤ i ⁻¹ᵁ U`.  If an open `W` of `X` contains the image under `i` of the fibre of
`j` over `y`, then some basic open of `U` contains that image and is contained in `W`.

This is `Stacks.Pushout.exists_basicOpen_image_fibre` read through
`AlgebraicGeometry.IsAffineOpen.fromSpec`: the ring `S` is the sections over the affine open
`j ⁻¹ᵁ V` of `Z`, integral over `Γ(Y, V)`, and the map `ψ` is the restriction
`Γ(X, U) ⟶ Γ(Z, j ⁻¹ᵁ V)`. -/
theorem exists_basicOpen_image_fibre_le (i : Z ⟶ X) (j : Z ⟶ Y) [IsIntegralHom j]
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) {y : Y} (hy : y ∈ V)
    (hle : j ⁻¹ᵁ V ≤ i ⁻¹ᵁ U) {W : X.Opens} (hW : ∀ z : Z, j z = y → i z ∈ W) :
    ∃ f : Γ(X, U), (∀ z : Z, j z = y → i z ∈ X.basicOpen f) ∧ X.basicOpen f ≤ W := by
  have hΩ : IsAffineOpen (j ⁻¹ᵁ V) := hV.preimage j
  let _ : Algebra Γ(Y, V) Γ(Z, j ⁻¹ᵁ V) := (j.app V).hom.toAlgebra
  have halg : algebraMap Γ(Y, V) Γ(Z, j ⁻¹ᵁ V) = (j.app V).hom := rfl
  have : Algebra.IsIntegral Γ(Y, V) Γ(Z, j ⁻¹ᵁ V) :=
    algebraMap_isIntegral_iff.mp (IsIntegralHom.isIntegral_app j V hV)
  -- The prime of `Γ(Z, j ⁻¹ᵁ V)` attached to a point `x` lies over the prime of `y` exactly when
  -- `j x = y`.
  have hover : ∀ x : (j ⁻¹ᵁ V : Z.Opens),
      (hΩ.primeIdealOf x).comap (algebraMap Γ(Y, V) Γ(Z, j ⁻¹ᵁ V)) =
        hV.primeIdealOf ⟨j x.1, x.2⟩ := by
    intro x
    rw [halg, Scheme.Hom.app_eq_appLE]
    exact hV.comap_primeIdealOf_appLE V (j ⁻¹ᵁ V) hΩ le_rfl x.2
  -- The point of `X` under the prime of `Γ(X, U)` attached to a point `x` of `j ⁻¹ᵁ V` is `i x`.
  have himage : ∀ x : (j ⁻¹ᵁ V : Z.Opens),
      hU.fromSpec ((hΩ.primeIdealOf x).comap (i.appLE U (j ⁻¹ᵁ V) hle).hom) = i x.1 := fun x ↦
    (congrArg (fun m : Spec Γ(Z, j ⁻¹ᵁ V) ⟶ X ↦ m.base (hΩ.primeIdealOf x))
      (hU.SpecMap_appLE_fromSpec i hΩ hle)).trans (congrArg i (hΩ.fromSpec_primeIdealOf x))
  -- Every prime of `Γ(Z, j ⁻¹ᵁ V)` comes from a point.
  have hsurj : ∀ q : PrimeSpectrum Γ(Z, j ⁻¹ᵁ V), ∃ x, q = hΩ.primeIdealOf x := fun q ↦
    ⟨hΩ.isoSpec.inv q,
      (congrArg (fun m : Spec Γ(Z, j ⁻¹ᵁ V) ⟶ Spec Γ(Z, j ⁻¹ᵁ V) ↦ m.base q)
        hΩ.isoSpec.inv_hom_id).symm⟩
  -- A point of `j ⁻¹ᵁ V` whose prime lies over the prime of `y` maps to `y`.
  have hmemfibre : ∀ (z : Z) (hz : z ∈ j ⁻¹ᵁ V), j z = y → hΩ.primeIdealOf ⟨z, hz⟩ ∈
      PrimeSpectrum.comap (algebraMap Γ(Y, V) Γ(Z, j ⁻¹ᵁ V)) ⁻¹'
        {hV.primeIdealOf ⟨y, hy⟩} := fun z hz hjz ↦
    (hover ⟨z, hz⟩).trans (congrArg hV.primeIdealOf (Subtype.ext hjz))
  have hfibremem : ∀ x : (j ⁻¹ᵁ V : Z.Opens), hΩ.primeIdealOf x ∈
      PrimeSpectrum.comap (algebraMap Γ(Y, V) Γ(Z, j ⁻¹ᵁ V)) ⁻¹'
        {hV.primeIdealOf ⟨y, hy⟩} → j x.1 = y := fun x hx ↦ by
    simpa only [hV.fromSpec_primeIdealOf] using congrArg hV.fromSpec ((hover x).symm.trans hx)
  -- The image of the fibre lands in the open of `Spec Γ(X, U)` matching `W`.
  have hr : PrimeSpectrum.comap (i.appLE U (j ⁻¹ᵁ V) hle).hom ''
      (PrimeSpectrum.comap (algebraMap Γ(Y, V) Γ(Z, j ⁻¹ᵁ V)) ⁻¹'
        {hV.primeIdealOf ⟨y, hy⟩}) ⊆ {x : PrimeSpectrum Γ(X, U) | hU.fromSpec x ∈ W} := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨z, rfl⟩ := hsurj q
    change hU.fromSpec _ ∈ W
    rw [himage z]
    exact hW z.1 (hfibremem z hq)
  obtain ⟨f, hf₁, hf₂⟩ := exists_basicOpen_image_fibre (hV.primeIdealOf ⟨y, hy⟩)
    (i.appLE U (j ⁻¹ᵁ V) hle).hom (hU.fromSpec ⁻¹ᵁ W).2 hr
  refine ⟨f, fun z hjz ↦ ?_, ?_⟩
  · have hz : z ∈ j ⁻¹ᵁ V := show j z ∈ V from hjz ▸ hy
    rw [← himage ⟨z, hz⟩, ← hU.fromSpec_image_basicOpen f]
    exact ⟨_, hf₁ ⟨_, hmemfibre z hz hjz, rfl⟩, rfl⟩
  · rw [← hU.fromSpec_image_basicOpen f]
    rintro _ ⟨q, hq, rfl⟩
    exact hf₂ hq

/-- **Stacks Project, Tag 0ECJ.**  Let `i : Z ⟶ X` be a closed immersion and `j : Z ⟶ Y` an
integral morphism such that every fibre of `j` maps under `i` into an affine open of `X`.  Then
every `y : Y` has an affine open neighbourhood `V` whose preimage under `j` is the preimage under
`i` of an affine open `U` of `X`.

The argument of the source, run twice.  Shrinking `Y` around `y` makes `j ⁻¹ᵁ V₀` land inside
`i ⁻¹ᵁ U₀`; separating the fibre by a basic open of `U₀` inside the open `W` with
`i ⁻¹ᵁ W ≤ j ⁻¹ᵁ V₀` reverses that inclusion.  Shrinking a second time and pulling the resulting
function on `V₀` back along the closed immersion makes the two preimages equal, because the basic
open of the pullback of `g` is cut out of `i ⁻¹ᵁ U₁` by `j ⁻¹ᵁ (Y.basicOpen g)`. -/
@[stacks 0ECJ]
theorem exists_affineOpens_preimage_eq (i : Z ⟶ X) (j : Z ⟶ Y) [IsClosedImmersion i]
    [IsIntegralHom j]
    (hfib : ∀ y : Y, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ z : Z, j z = y → i z ∈ U) (y : Y) :
    ∃ (U : X.Opens) (V : Y.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧ y ∈ V ∧
      i ⁻¹ᵁ U = j ⁻¹ᵁ V := by
  obtain ⟨U₀, hU₀, hfib₀⟩ := hfib y
  obtain ⟨V₀, hV₀, hyV₀, hV₀le⟩ := exists_isAffineOpen_preimage_le j (Ω := i ⁻¹ᵁ U₀) hfib₀
  -- The open `W` of `X` cut out by removing the image of the points of `Z` outside `j ⁻¹ᵁ V₀`.
  obtain ⟨W, hWmem, hWle⟩ := exists_opens_preimage_le i i.isClosedMap (j ⁻¹ᵁ V₀)
  have hfibW : ∀ z : Z, j z = y → i z ∈ W := fun z hjz ↦
    hWmem _ fun z' hz' ↦ show j z' ∈ V₀ from i.isClosedEmbedding.injective hz' ▸ hjz ▸ hyV₀
  -- First separation: a basic open `U₁` of `U₀` containing the fibre and contained in `W`.
  obtain ⟨f, hf₁, hf₂⟩ :=
    exists_basicOpen_image_fibre_le i j hU₀ hV₀ hyV₀ hV₀le hfibW
  have hU₁ : IsAffineOpen (X.basicOpen f) := hU₀.basicOpen f
  have hU₁le : i ⁻¹ᵁ X.basicOpen f ≤ j ⁻¹ᵁ V₀ := (i.preimage_mono hf₂).trans hWle
  -- Second shrinking, and a basic open of `V₀` inside the open it produces.
  obtain ⟨V₂, hV₂, hyV₂, hV₂le⟩ :=
    exists_isAffineOpen_preimage_le j (Ω := i ⁻¹ᵁ X.basicOpen f) hf₁
  obtain ⟨g, hgle, hyg⟩ := hV₀.exists_basicOpen_le (V := V₂ ⊓ V₀) ⟨y, hyV₂, hyV₀⟩ hyV₀
  have hpreV : j ⁻¹ᵁ Y.basicOpen g ≤ i ⁻¹ᵁ X.basicOpen f := fun z hz ↦
    hV₂le (show j z ∈ V₂ from (hgle hz).1)
  -- Pull `g` back along the closed immersion and take the corresponding basic open of `U₁`.
  obtain ⟨f', hf'⟩ :=
    i.app_surjective (X.basicOpen f) hU₁ (j.appLE V₀ (i ⁻¹ᵁ X.basicOpen f) hU₁le g)
  refine ⟨X.basicOpen f', Y.basicOpen g, hU₁.basicOpen f', hV₀.basicOpen g, hyg, ?_⟩
  calc i ⁻¹ᵁ X.basicOpen f' = i ⁻¹ᵁ X.basicOpen f ⊓ j ⁻¹ᵁ Y.basicOpen g := by
        rw [Scheme.preimage_basicOpen, hf', Scheme.basicOpen_appLE]
    _ = j ⁻¹ᵁ Y.basicOpen g := inf_eq_right.mpr hpreV

end Stacks.Pushout

end
