module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Sections of an inverse-image ideal sheaf vanish on its closed subscheme

Let `f : X ⟶ Y` be a morphism of schemes and let `L` be a sheaf of ideals on `Y`. The closed
subscheme cut out by the inverse-image ideal sheaf `L.comap f` is the fibre product
`X ×_Y V(L)` (`AlgebraicGeometry.Scheme.IdealSheafData.comapIso`), so the structure morphism of
`V(L.comap f)` over `Y` factors through `V(L)`. Consequently a global function on `Y` which
dies on `V(L)` has a pullback to `X` which dies on `V(L.comap f)`, and indeed on `V(K)` for any
sheaf of ideals `K` containing `L.comap f`.

Over an affine base `Y = Spec A` this is the statement that the inverse image of an ideal
`I ⊆ A` kills `I`: the hypothesis `hI` of
`Stacks.Blowup.Colength.length_globalSections_lt_length_quotient`, which is stated for an
arbitrary sheaf of ideals and is discharged with this lemma in
`AlgebraicGeometry.length_globalSections_lt_length_quotient_blowUp`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.appTop_subschemeι_comap_eq_zero` — a global function
  dying on `V(L)` pulls back to one dying on `V(K)` for `L.comap f ≤ K`.
* `AlgebraicGeometry.Scheme.IdealSheafData.appTop_subschemeι_eq_zero_of_mem` — over an affine
  base, the elements of the ideal die on the closed subscheme of its inverse image.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X Y : Scheme.{u}}

/-- **The closed subscheme of an inverse-image ideal sheaf lies over the closed subscheme of the
original.** The structure morphism of `V(L.comap f)` to `Y` factors through `V(L)`, by the
identification of `V(L.comap f)` with the fibre product `X ×_Y V(L)`. -/
public theorem subschemeι_comap_comp (L : Y.IdealSheafData) (f : X ⟶ Y) :
    (L.comap f).subschemeι ≫ f =
      ((L.comapIso f).hom ≫ pullback.snd f L.subschemeι) ≫ L.subschemeι := by
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, comapIso_hom_fst]

/-- **A global function dying on a closed subscheme pulls back to one dying on the closed
subscheme of the inverse image.** If `s ∈ Γ(Y, 𝒪_Y)` restricts to zero on `V(L)` and
`L.comap f ≤ K`, then `f^♯ s` restricts to zero on `V(K)`. -/
public theorem appTop_subschemeι_comap_eq_zero {L : Y.IdealSheafData} {K : X.IdealSheafData}
    (f : X ⟶ Y) (hK : L.comap f ≤ K) (s : Γ(Y, ⊤))
    (hs : (L.subschemeι.appTop).hom s = 0) :
    (K.subschemeι.appTop).hom (f.appTop.hom s) = 0 := by
  have hfac : K.subschemeι ≫ f =
      (inclusion hK ≫ (L.comapIso f).hom ≫ pullback.snd f L.subschemeι) ≫ L.subschemeι := by
    rw [← inclusion_subschemeι hK, Category.assoc, subschemeι_comap_comp]
    simp
  have := congrArg (fun g : Γ(Y, ⊤) ⟶ Γ(K.subscheme, ⊤) => g.hom s)
    (congrArg Scheme.Hom.appTop hfac)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at this
  rw [this, hs]
  simp

/-- **The elements of an ideal die on the closed subscheme of its inverse-image ideal sheaf.**
Let `f : X ⟶ Spec A`, let `I` be an ideal of `A` and let `K` be a sheaf of ideals on `X`
containing the inverse image of `I`. Then every element of `I`, pulled back to a global function
on `X`, restricts to zero on `V(K)`.

This discharges the hypothesis `hI` of
`Stacks.Blowup.Colength.length_globalSections_lt_length_quotient`, which asks exactly this of the
sheaf of ideals appearing in the factorization of [Stacks, Tag 0AGT]. -/
public theorem appTop_subschemeι_eq_zero_of_mem {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (I : Ideal A) {K : X.IdealSheafData}
    (hK : (ofIdealTop (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap f ≤ K)
    (a : A) (ha : a ∈ I) :
    (K.subschemeι.appTop).hom (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a) = 0 := by
  refine appTop_subschemeι_comap_eq_zero f hK ((Scheme.ΓSpecIso (.of A)).inv.hom a) ?_
  have hmem : (Scheme.ΓSpecIso (.of A)).inv.hom a ∈
      RingHom.ker ((ofIdealTop (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).subschemeι.app
        (⟨⊤, isAffineOpen_top (Spec (.of A))⟩ : (Spec (.of A)).affineOpens)).hom := by
    rw [ker_subschemeι_app]
    simpa using Ideal.mem_map_of_mem _ ha
  exact hmem

end AlgebraicGeometry.Scheme.IdealSheafData

end
