module

public import StacksFrontier.AlgebraicGeometry.Smooth.CechTorsorAssembly

/-!
# The conormal module of a thickening is separated for the Zariski topology

Let `i : T ⟶ T'` be a first-order thickening with `T'` affine. The conormal module of `i`
restricted to an affine open `U'` of `T'` is, by construction, the ideal
`RingHom.ker (i ∣_ U').appTop` of `Γ(U', ⊤)`, and `Stacks.Smooth.conormalResLE` restricts it to a
smaller affine open by restricting sections of `𝒪_{T'}`. Consequently the family of those
restriction maps attached to an open covering of `U'` is **jointly injective**: that is the
content of `Stacks.Smooth.eq_of_conormalResLE_eq`, and it is nothing but the separatedness of the
structure sheaf of `T'`, since the conormal module is a submodule of a module of sections.

This is the local-to-global input of the chart-independence step of the proof of the
infinitesimal lifting criterion [Stacks Project, Tag 02H6]: the chart-local difference of two
solutions of a lifting problem is only comparable across two affine charts of `X` after both
charts have been refined, which can be done only locally on the thickening, so the comparison has
to be glued back up from a covering. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Smooth.CechTorsorAssembly`.

## Main results

* `Stacks.Smooth.eq_of_conormalResLE_eq`: two elements of the conormal module of `i ∣_ U'` whose
  restrictions to the members of an open covering of `U'` by affine opens agree are equal.
* `Stacks.Smooth.linearMap_ext_of_conormalResLE`: the same, read as an extensionality principle
  for linear maps into the conormal module.
* `Stacks.Smooth.eq_of_conormalResLE_basicOpen_eq` and
  `Stacks.Smooth.linearMap_ext_of_conormalResLE_basicOpen`: the two statements above for a
  covering by basic opens of `T'`, which is the shape in which the Čech step uses them, because
  `Stacks.Smooth.homCompare_restrictₗ` is stated for an inclusion of basic opens.
* `Stacks.Smooth.exists_basicOpen_le_cover`: any open of an affine scheme is covered by basic
  opens subordinate to a prescribed family of neighbourhoods of its points.

## Implementation notes

Going through the localization description of the conormal module would need, for a covering
of a proper open `U'` of `T'`, a radical-membership refinement of `Ideal.span_pow_eq_top`. None
of that is necessary: `Stacks.Smooth.conormalResLE`
is defined through `AlgebraicGeometry.Scheme.homOfLE`, so `AlgebraicGeometry.Scheme.homOfLE_appTop`
rewrites it into a restriction map of the presheaf `𝒪_{T'}` and `TopCat.Sheaf.eq_of_locally_eq'`
applies directly, for an arbitrary open covering of an arbitrary open.

The one piece of bookkeeping is that `AlgebraicGeometry.Scheme.homOfLE_appTop` presents its source
and target as the sections over `U'.ι ''ᵁ ⊤` and `(U j).ι ''ᵁ ⊤` rather than over `U'` and `U j`.
Those are the *same* types as `Γ(U', ⊤)` and `Γ(U j, ⊤)` by
`AlgebraicGeometry.Scheme.Opens.toScheme_presheaf_obj`, which is a definitional equality, so the
covering hypothesis is the only thing that has to be transported, by
`AlgebraicGeometry.Scheme.Opens.ι_image_top`.

## References

* [Stacks Project, Tag 01EO](https://stacks.math.columbia.edu/tag/01EO)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.Smooth

/-! ### Coverings of an open of an affine scheme by basic opens -/

/-- **An open of an affine scheme is covered by basic opens subordinate to any prescribed family
of neighbourhoods of its points.** Let `T'` be affine, let `U'` be an open of `T'` and let `O t`
be an open neighbourhood of each point `t` of `U'`, contained in `U'`. Then there are global
sections `g t` of `𝒪_{T'}` with `T'.basicOpen (g t) ≤ O t` whose basic opens cover `U'`.

This is `AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le` applied at every point of `U'`, and
it is the covering that `Stacks.Smooth.eq_of_conormalResLE_basicOpen_eq` consumes. Unlike
`Stacks.Smooth.exists_finset_basicOpen_le` no finiteness is extracted, because separatedness needs
none. -/
theorem exists_basicOpen_le_cover {T' : Scheme.{u}} [IsAffine T'] (U' : T'.Opens)
    (O : ↥U' → T'.Opens) (hmem : ∀ t : ↥U', (t : T') ∈ O t) :
    ∃ g : ↥U' → Γ(T', (⊤ : T'.Opens)),
      (∀ t, T'.basicOpen (g t) ≤ O t) ∧ U' ≤ ⨆ t, T'.basicOpen (g t) := by
  have hbas : ∀ t : ↥U', ∃ g : Γ(T', (⊤ : T'.Opens)),
      T'.basicOpen g ≤ O t ∧ (t : T') ∈ T'.basicOpen g := fun t ↦
    (isAffineOpen_top T').exists_basicOpen_le (V := O t) ⟨(t : T'), hmem t⟩ trivial
  choose g hg₁ hg₂ using hbas
  exact ⟨g, hg₁, fun x hx ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hg₂ ⟨x, hx⟩⟩⟩

/-! ### Separatedness of the conormal module -/

section Separated

variable {T T' : Scheme.{u}} [IsAffine T'] {i : T ⟶ T'}
  (hi : Thickenings.IsFirstOrderThickening i)

/-- **The conormal module of a thickening is separated.** Let `i : T ⟶ T'` be a first-order
thickening with `T'` affine, let `U'` be an affine open of `T'` and let `U j` be a family of
affine opens of `T'` contained in `U'` and covering it. Two elements of the conormal module of
`i ∣_ U'` whose restrictions `Stacks.Smooth.conormalResLE` to every `U j` agree are equal.

The conormal module is an ideal of `Γ(U', ⊤) = Γ(T', U')` and `Stacks.Smooth.conormalResLE` is
restriction of sections of `𝒪_{T'}`, so this is `TopCat.Sheaf.eq_of_locally_eq'` for the structure
sheaf of `T'`. -/
theorem eq_of_conormalResLE_eq {U' : T'.Opens} [IsAffine (U' : Scheme.{u})]
    {ι : Type*} {U : ι → T'.Opens} [∀ j, IsAffine ((U j : T'.Opens) : Scheme.{u})]
    (hle : ∀ j, U j ≤ U') (hcover : U' ≤ ⨆ j, U j)
    {x y : RingHom.ker (i ∣_ U').appTop.hom}
    (h : ∀ j, conormalResLE hi (hle j) x = conormalResLE hi (hle j) y) : x = y := by
  refine Subtype.ext ?_
  have h' : ∀ j, (T'.homOfLE (hle j)).appTop.hom
        (x : Γ((U' : Scheme.{u}), (⊤ : (U' : Scheme.{u}).Opens)))
      = (T'.homOfLE (hle j)).appTop.hom
        (y : Γ((U' : Scheme.{u}), (⊤ : (U' : Scheme.{u}).Opens))) := fun j ↦ by
    rw [← conormalResLE_apply hi (hle j), ← conormalResLE_apply hi (hle j), h j]
  simp only [Scheme.homOfLE_appTop] at h'
  refine TopCat.Sheaf.eq_of_locally_eq' T'.sheaf (fun j ↦ (U j).ι ''ᵁ ⊤) (U'.ι ''ᵁ ⊤)
    (fun j ↦ homOfLE ?_) ?_ _ _ h'
  · simpa only [Scheme.Opens.ι_image_top] using hle j
  · simpa only [Scheme.Opens.ι_image_top] using hcover

/-- **Extensionality of linear maps into the conormal module.** Two linear maps into the conormal
module of `i ∣_ U'` whose composites with the restrictions `Stacks.Smooth.conormalResLE` to the
members of an affine open covering of `U'` agree are equal.

This is `Stacks.Smooth.eq_of_conormalResLE_eq` read for the values of a linear map, which is how
the chart-independence step of [Stacks Project, Tag 02H6] uses it: the two maps being compared are
the chart-local differences of two solutions of a lifting problem taken in two different affine
charts of `X`, and they are only known to agree locally on the thickening. -/
theorem linearMap_ext_of_conormalResLE {U' : T'.Opens} [IsAffine (U' : Scheme.{u})]
    {ι : Type*} {U : ι → T'.Opens} [∀ j, IsAffine ((U j : T'.Opens) : Scheme.{u})]
    (hle : ∀ j, U j ≤ U') (hcover : U' ≤ ⨆ j, U j)
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    (hmod : Module R (RingHom.ker (i ∣_ U').appTop.hom))
    {θ₁ θ₂ : M →ₗ[R] RingHom.ker (i ∣_ U').appTop.hom}
    (h : ∀ (j : ι) (m : M), conormalResLE hi (hle j) (θ₁ m) = conormalResLE hi (hle j) (θ₂ m)) :
    θ₁ = θ₂ :=
  LinearMap.ext fun m ↦ eq_of_conormalResLE_eq hi hle hcover fun j ↦ h j m

/-- **The conormal module of a thickening is separated, for a covering by basic opens.** This is
`Stacks.Smooth.eq_of_conormalResLE_eq` for `U' = T'.basicOpen c` covered by basic opens
`T'.basicOpen (c' j)`, which is the shape the Čech step of [Stacks Project, Tag 02H6] produces:
`Stacks.Smooth.homCompare_restrictₗ` compares the localizations of the module of linear maps at an
inclusion of basic opens. -/
theorem eq_of_conormalResLE_basicOpen_eq (c : Γ(T', (⊤ : T'.Opens)))
    {ι : Type*} (c' : ι → Γ(T', (⊤ : T'.Opens)))
    (hle : ∀ j, T'.basicOpen (c' j) ≤ T'.basicOpen c)
    (hcover : T'.basicOpen c ≤ ⨆ j, T'.basicOpen (c' j))
    {x y : letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
        (isAffineOpen_top T').basicOpen c
      RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom}
    (h : letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
        (isAffineOpen_top T').basicOpen c
      letI : ∀ j, IsAffine ((T'.basicOpen (c' j) : T'.Opens) : Scheme.{u}) := fun j ↦
        (isAffineOpen_top T').basicOpen (c' j)
      ∀ j, conormalResLE hi (hle j) x = conormalResLE hi (hle j) y) : x = y :=
  let : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) := (isAffineOpen_top T').basicOpen c
  let : ∀ j, IsAffine ((T'.basicOpen (c' j) : T'.Opens) : Scheme.{u}) := fun j ↦
    (isAffineOpen_top T').basicOpen (c' j)
  eq_of_conormalResLE_eq hi hle hcover h

/-- **Extensionality of linear maps into the conormal module, for a covering by basic opens.**
This is `Stacks.Smooth.linearMap_ext_of_conormalResLE` for `U' = T'.basicOpen c` covered by basic
opens `T'.basicOpen (c' j)`. -/
theorem linearMap_ext_of_conormalResLE_basicOpen (c : Γ(T', (⊤ : T'.Opens)))
    {ι : Type*} (c' : ι → Γ(T', (⊤ : T'.Opens)))
    (hle : ∀ j, T'.basicOpen (c' j) ≤ T'.basicOpen c)
    (hcover : T'.basicOpen c ≤ ⨆ j, T'.basicOpen (c' j))
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    (hmod : letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
        (isAffineOpen_top T').basicOpen c
      Module R (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom))
    {θ₁ θ₂ : letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
        (isAffineOpen_top T').basicOpen c
      M →ₗ[R] RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom}
    (h : letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
        (isAffineOpen_top T').basicOpen c
      letI : ∀ j, IsAffine ((T'.basicOpen (c' j) : T'.Opens) : Scheme.{u}) := fun j ↦
        (isAffineOpen_top T').basicOpen (c' j)
      ∀ (j : ι) (m : M), conormalResLE hi (hle j) (θ₁ m) = conormalResLE hi (hle j) (θ₂ m)) :
    θ₁ = θ₂ :=
  LinearMap.ext fun m ↦ eq_of_conormalResLE_basicOpen_eq hi c c' hle hcover fun j ↦ h j m

end Separated

end Stacks.Smooth

end
