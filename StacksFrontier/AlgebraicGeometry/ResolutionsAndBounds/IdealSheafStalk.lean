module

public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafResolution

/-!
# The stalk of an ideal sheaf: one affine open suffices, and the algebra of products

Let `X` be a scheme and `I` an ideal sheaf on `X`, i.e. a family of ideals indexed by the
affine opens of `X` compatible with restriction to basic opens. Its stalk at a point `x`,
`AlgebraicGeometry.IdealSheafData.stalk I x`, is an ideal of the local ring `𝒪_{X,x}`, defined
as the supremum over all affine opens containing `x` of the image of the ideal there. The
supremum is redundant: a single affine open containing `x` computes it, because the two ideals
agree after restriction to a common basic open neighbourhood.

With that in hand, the stalk is a homomorphism for the semiring structure on ideal sheaves —
it takes products to products and powers to powers — and it takes an inverse image ideal sheaf
to the image of the stalk under the map of local rings. Together these compute the stalk of the
ideal sheaf `𝓙 = pr₁^*𝓘 · pr₂^*𝓘'` on a fibre product, and of its powers: at a point `z` of
`X ×_S Y` lying over `x` and `y`, the stalk of `𝓙ⁿ` is the product of the images of `𝓘ₓⁿ` and
of `𝓘'_yⁿ` in `𝒪_z`.

## Main results

* `AlgebraicGeometry.IdealSheafData.stalk_mul` and
  `AlgebraicGeometry.IdealSheafData.stalk_pow`: the stalk of a product, and of a power.
* `AlgebraicGeometry.IdealSheafData.stalk_comap`: the stalk of an inverse image ideal sheaf.
* `AlgebraicGeometry.IdealSheafData.stalk_externalProduct` and
  `AlgebraicGeometry.IdealSheafData.stalk_externalProduct_pow`: the stalk of the product ideal
  sheaf on a fibre product, and of its powers.

## Implementation notes

That a single affine open computes the stalk is
`stalk_eq_map_germ`, taken from
`StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic`. Given it, `stalk_mul`,
`stalk_pow` and `stalk_comap` are each a rewrite by it at one affine open together with
`Ideal.map_mul`, `Ideal.map_pow` and `Ideal.map_map`; for `stalk_comap` the affine open
downstairs is chosen first and the one upstairs is then taken inside its preimage, so that
`AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isAffineOpen` applies.

## References

* [Stacks Project, Tag 0FZ0](https://stacks.math.columbia.edu/tag/0FZ0)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.IdealSheafData

variable {X Y S : Scheme.{u}}

/-- An affine open contained in a given open and containing a given point of it. -/
private theorem exists_affineOpen_mem_le (V : X.Opens) (x : X) (hx : x ∈ V) :
    ∃ (U : X.affineOpens), x ∈ U.1 ∧ U.1 ≤ V := by
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hx
  exact ⟨⟨W, hW⟩, hxW, hWV⟩

/-! ### The stalk of a product, of a power, and of an inverse image -/

/-- **The stalk of a product of ideal sheaves** is the product of the stalks. -/
theorem stalk_mul (I J : X.IdealSheafData) (x : X) :
    stalk (I * J) x = stalk I x * stalk J x := by
  obtain ⟨U, hx, -⟩ := exists_affineOpen_mem_le ⊤ x trivial
  rw [stalk_eq_map_germ _ x U hx,
    stalk_eq_map_germ I x U hx,
    stalk_eq_map_germ J x U hx,
    show (I * J).ideal U = I.ideal U * J.ideal U from rfl, Ideal.map_mul]

/-- **The stalk of a power of an ideal sheaf** is the power of the stalk. -/
theorem stalk_pow (I : X.IdealSheafData) (n : ℕ) (x : X) :
    stalk (I ^ n) x = stalk I x ^ n := by
  obtain ⟨U, hx, -⟩ := exists_affineOpen_mem_le ⊤ x trivial
  rw [stalk_eq_map_germ _ x U hx,
    stalk_eq_map_germ I x U hx,
    show (I ^ n).ideal U = I.ideal U ^ n from rfl, Ideal.map_pow]

/-- **The stalk of an inverse image ideal sheaf** is the image of the stalk of the original
under the induced map of local rings. -/
theorem stalk_comap (I : Y.IdealSheafData) (f : X ⟶ Y) (x : X) :
    stalk (I.comap f) x = Ideal.map (f.stalkMap x).hom (stalk I (f.base x)) := by
  obtain ⟨V, hfx, -⟩ := exists_affineOpen_mem_le ⊤ (f.base x) trivial
  obtain ⟨U, hxU, hUV⟩ := exists_affineOpen_mem_le (f ⁻¹ᵁ V.1) x hfx
  have happ : (f.appLE V.1 U.1 hUV) ≫ X.presheaf.germ U.1 x hxU =
      Y.presheaf.germ V.1 (f.base x) hfx ≫ f.stalkMap x := by
    rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc,
      X.presheaf.germ_res (homOfLE hUV) x hxU]
  rw [stalk_eq_map_germ _ x U hxU,
    stalk_eq_map_germ I _ V hfx,
    Scheme.IdealSheafData.ideal_comap_of_isAffineOpen I f V U hUV, Ideal.map_map, Ideal.map_map,
    ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, happ]

/-! ### The product ideal sheaf on a fibre product -/

/-- **The stalk of the product ideal sheaf `𝓙 = pr₁^*𝓘 · pr₂^*𝓘'` on a fibre product.** At a
point `z` of `X ×_S Y` it is the product, inside `𝒪_z`, of the images of the stalks of `𝓘` and
of `𝓘'` at the two images of `z`. -/
theorem stalk_externalProduct (f : X ⟶ S) (g : Y ⟶ S) (I : X.IdealSheafData)
    (I' : Y.IdealSheafData) (z : ↥(pullback f g)) :
    stalk (Scheme.IdealSheafData.externalProduct f g I I') z =
      Ideal.map ((pullback.fst f g).stalkMap z).hom (stalk I ((pullback.fst f g).base z)) *
        Ideal.map ((pullback.snd f g).stalkMap z).hom
          (stalk I' ((pullback.snd f g).base z)) := by
  rw [Scheme.IdealSheafData.externalProduct, stalk_mul, stalk_comap, stalk_comap]

/-- **The stalk of a power of the product ideal sheaf on a fibre product.** This is the
local-ring identity `(𝓙ⁿ)_z = (𝓘ₓⁿ · 𝒪_z) · (𝓘'_yⁿ · 𝒪_z)` used by the proof of
[Stacks, Tag 0FZ0]. -/
theorem stalk_externalProduct_pow (f : X ⟶ S) (g : Y ⟶ S) (I : X.IdealSheafData)
    (I' : Y.IdealSheafData) (n : ℕ) (z : ↥(pullback f g)) :
    stalk (Scheme.IdealSheafData.externalProduct f g I I' ^ n) z =
      Ideal.map ((pullback.fst f g).stalkMap z).hom
          (stalk I ((pullback.fst f g).base z) ^ n) *
        Ideal.map ((pullback.snd f g).stalkMap z).hom
          (stalk I' ((pullback.snd f g).base z) ^ n) := by
  rw [stalk_pow, stalk_externalProduct, mul_pow, ← Ideal.map_pow, ← Ideal.map_pow]

end AlgebraicGeometry.IdealSheafData

end
