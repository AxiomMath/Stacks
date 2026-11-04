module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FaithfullyFlatSections
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Size of the target of a flat surjective morphism of schemes

A flat surjective morphism `f : W ⟶ V` of schemes satisfies
`size V ≤ max (2 ^ #W) (2 ^ size W)`, and hence `size V < κ` whenever `size W < κ` for a strong
prelimit cardinal `κ`.

## Main results

* `AlgebraicGeometry.Flat.injective_stalkMap`: the stalk maps of a flat morphism are injective.
* `AlgebraicGeometry.Scheme.Hom.injective_app_of_flat_of_surjective`: a flat surjective
  morphism is injective on sections over any open of the target.
* `AlgebraicGeometry.Scheme.sections_restrict_injective_of_cover`: restriction of sections to
  the members of an arbitrary open cover is injective.
* `AlgebraicGeometry.Scheme.mk_sections_le_two_pow_size`: `#Γ(X, U) ≤ 2 ^ size X` for an
  arbitrary, not necessarily affine, open `U`.
* `AlgebraicGeometry.Scheme.size_le_of_isOpenImmersion`: `size X ≤ size Y` for an open
  immersion `X ⟶ Y`.
* `AlgebraicGeometry.Scheme.size_le_of_flat_of_surjective`:
  `size V ≤ max (2 ^ #W) (2 ^ size W)`.
* `AlgebraicGeometry.Scheme.size_le_two_pow_two_pow_size_of_flat_of_surjective`: the coarser
  uniform form `size V ≤ 2 ^ 2 ^ size W`.
* `AlgebraicGeometry.Scheme.max_two_pow_mk_two_pow_size_lt_of_isStrongPrelimit` and
  `AlgebraicGeometry.Scheme.size_lt_of_flat_of_surjective_of_isStrongPrelimit`: if
  `size W < κ` for a strong prelimit cardinal `κ`, then this bound, and so `size V`, is below `κ`.
-/

@[expose] public section

open Cardinal CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Injectivity on sections -/

/-- The stalk maps `𝒪_{Y, f x} ⟶ 𝒪_{X, x}` of a flat morphism of schemes are injective. -/
theorem Flat.injective_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (x : X) :
    Function.Injective (f.stalkMap x).hom := by
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

/-- Two sections of `Y` over an open `U` which have the same germ at the image of every point
of `X` are equal, provided `f : X ⟶ Y` is surjective. -/
private theorem eq_of_germ_eq_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    (U : Y.Opens) {s t : Γ(Y, U)}
    (h : ∀ (x : X) (hx : f.base x ∈ U),
      Y.presheaf.germ U (f.base x) hx s = Y.presheaf.germ U (f.base x) hx t) :
    s = t := by
  refine TopCat.Presheaf.section_ext (C := CommRingCat) ⟨Y.presheaf, Y.IsSheaf⟩ U s t
    fun y hy => ?_
  obtain ⟨x, rfl⟩ := f.surjective y
  exact h x hy

/-- For `f : X ⟶ Y` flat and surjective and `U` an open of `Y`, the map
`Γ(Y, U) → Γ(X, f ⁻¹ᵁ U)` is injective. -/
alias Scheme.Hom.injective_app_of_flat_of_surjective :=
  AlgebraicGeometry.Scheme.Hom.app_injective_of_flat_of_surjective

/-! ### Sections over an arbitrary open -/

/-- If a family of opens `U i ≤ V` covers `V`, then the restriction map
`Γ(X, V) → Π i, Γ(X, U i)` is injective. -/
theorem Scheme.sections_restrict_injective_of_cover (X : Scheme.{u}) {ι : Type u}
    (U : ι → X.Opens) (V : X.Opens) (hle : ∀ i, U i ≤ V) (hcov : ∀ x ∈ V, ∃ i, x ∈ U i) :
    Function.Injective
      (fun (s : Γ(X, V)) (i : ι) => X.presheaf.map (op (homOfLE (hle i))) s) :=
  fun _ _ h => X.IsSheaf.section_ext fun p hp =>
    (hcov p hp).elim fun i hpi => ⟨U i, hle i, hpi, congrFun h i⟩

/-- The sections of a scheme `X` over an arbitrary, not necessarily affine, open `U` number at
most `2 ^ size X`. -/
theorem Scheme.mk_sections_le_two_pow_size (X : Scheme.{u}) (U : X.Opens) :
    #Γ(X, U) ≤ 2 ^ X.size := by
  have hcov : ∀ x ∈ U, ∃ A : {A : X.affineOpens // A.1 ≤ U}, x ∈ (A.1.1 : X.Opens) :=
    fun x hx => by
      obtain ⟨A, hA, hxA, hsub⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) hx
      exact ⟨⟨⟨A, hA⟩, hsub⟩, hxA⟩
  refine (mk_le_of_injective
    (X.sections_restrict_injective_of_cover _ U (fun A => A.2) hcov)).trans ?_
  rw [mk_pi]
  refine (Cardinal.prod_le_prod _ (fun _ => X.size)
    fun A : {A : X.affineOpens // A.1 ≤ U} => X.mk_sections_le_size A.1).trans ?_
  rw [Cardinal.prod_const']
  calc X.size ^ #{A : X.affineOpens // A.1 ≤ U}
      ≤ X.size ^ X.size :=
        power_le_power_left (aleph0_pos.trans_le (X.aleph0_le_size)).ne'
          ((mk_subtype_le _).trans (X.mk_affineOpens_le_size))
    _ ≤ (2 ^ X.size) ^ X.size := power_le_power_right (cantor _).le
    _ = 2 ^ (X.size * X.size) := (power_mul ..).symm
    _ = 2 ^ X.size := by rw [mul_eq_self X.aleph0_le_size]

/-- The size of the source of an open immersion is at most the size of its target. -/
theorem Scheme.size_le_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    X.size ≤ Y.size :=
  (Scheme.size_congr f.isoOpensRange).trans_le (Y.size_coe_opens_le f.opensRange)

/-! ### The size bound -/

/-- The target of a flat surjective morphism of schemes `f : W ⟶ V` satisfies
`size V ≤ max (2 ^ #W) (2 ^ size W)`. -/
theorem Scheme.size_le_of_flat_of_surjective {W V : Scheme.{u}} (f : W ⟶ V) [Flat f]
    [Surjective f] :
    V.size ≤ max (2 ^ #(W : Type u)) (2 ^ W.size) :=
  Scheme.size_le_of_bounds
    (le_max_of_le_right (W.aleph0_le_size.trans (cantor _).le))
    (le_max_of_le_left (V.mk_affineOpens_le_two_pow.trans
      (power_le_power_left two_ne_zero (mk_le_of_surjective f.surjective))))
    fun A => le_max_of_le_right
      ((mk_le_of_injective (f.injective_app_of_flat_of_surjective A.1)).trans
        (W.mk_sections_le_two_pow_size _))

/-- The target of a flat surjective morphism of schemes `f : W ⟶ V` satisfies
`size V ≤ 2 ^ 2 ^ size W`. -/
theorem Scheme.size_le_two_pow_two_pow_size_of_flat_of_surjective {W V : Scheme.{u}} (f : W ⟶ V)
    [Flat f] [Surjective f] :
    V.size ≤ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ W.size :=
  (Scheme.size_le_of_flat_of_surjective f).trans <| max_le
    (power_le_power_left two_ne_zero W.mk_le_two_pow_size)
    (power_le_power_left two_ne_zero (cantor _).le)

/-- If `size W < κ` for a strong prelimit cardinal `κ`, then `max (2 ^ #W) (2 ^ size W) < κ`. -/
theorem Scheme.max_two_pow_mk_two_pow_size_lt_of_isStrongPrelimit {κ : Cardinal.{u}}
    (hsl : Cardinal.IsStrongPrelimit κ) {W : Scheme.{u}} (hW : W.size < κ) :
    max (2 ^ #(W : Type u)) (2 ^ W.size) < κ :=
  max_lt (hsl (W.mk_le_two_pow_size.trans_lt (hsl hW))) (hsl hW)

/-- If `f : W ⟶ V` is a flat surjective morphism of schemes and `size W < κ` for a strong prelimit
cardinal `κ`, then `size V < κ`. -/
theorem Scheme.size_lt_of_flat_of_surjective_of_isStrongPrelimit {κ : Cardinal.{u}}
    (hsl : Cardinal.IsStrongPrelimit κ) {W V : Scheme.{u}} (f : W ⟶ V) [Flat f] [Surjective f]
    (hW : W.size < κ) :
    V.size < κ :=
  (Scheme.size_le_of_flat_of_surjective f).trans_lt
    (Scheme.max_two_pow_mk_two_pow_size_lt_of_isStrongPrelimit hsl hW)

end AlgebraicGeometry

end
