module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality
public import StacksFrontier.CategoryTheory.TwoFibreProductOverRelocalize

/-!
# The diagonal of a composite 1-morphism over a base

Fix a base category `𝒞` and categories `𝒮`, `𝒮'`, `𝒟` over `𝒞` with structure functors `q𝒮`,
`p𝒮'`, `p𝒟`. Let `H : 𝒮 ⥤ 𝒮'` and `b : 𝒮' ⥤ 𝒟` be 1-morphisms over `𝒞`. The diagonal of the
composite `H ⋙ b`,

`Δ_{H ⋙ b} : 𝒮 ⥤ 𝒮 ×_{H ⋙ b, 𝒟, H ⋙ b} 𝒮`,

factors as the diagonal of `H` followed by the comparison 1-morphism
`CategoryTheory.TwoFibreProductOver.mapBase` from the 2-fibre product over `𝒮'` to the one over
`𝒟`. Both send an object `x` of `𝒮` to the triple `(x, x, φ)`; the comparison isomorphisms `φ`
are `b` applied to the identity of `H x` on the one side and the identity of `b (H x)` on the
other, so the two agree by `CategoryTheory.Functor.mapIso_refl` and not on the nose.

## Main results

* `CategoryTheory.TwoFibreProductOver.ext_of_heq_iso`: two objects of a 2-fibre product over a
  base agree as soon as their base object, their two components and their comparison isomorphisms
  do.
* `CategoryTheory.TwoFibreProductOver.diagonal_comp_mapBase`: the factorization of the diagonal of
  a composite.

## Implementation notes

The factorization is an equality of functors whose object part is *not* a definitional equality,
so `CategoryTheory.Functor.ext` leaves a morphism goal mentioning two `eqToHom`s. Both are
discharged componentwise: the object equality is the identity on the `x`- and the `y`-component,
so the corresponding components of its `eqToHom` are identities, which
`CategoryTheory.TwoFibreProductOver.eqToHom_a` and
`CategoryTheory.TwoFibreProductOver.eqToHom_b` make available by cases on the equality.
-/

@[expose] public section

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- Two objects of the 2-fibre product over a base are equal as soon as their base objects, their
two components and their comparison isomorphisms are: the two remaining fields are proofs. -/
theorem ext_of_heq_iso {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (hbase : P.base = Q.base)
    (hx : P.x = Q.x) (hy : P.y = Q.y) (hiso : HEq P.iso Q.iso) : P = Q := by
  obtain ⟨bP, xP, yP, hxP, hyP, isoP, vP⟩ := P
  obtain ⟨bQ, xQ, yQ, hxQ, hyQ, isoQ, vQ⟩ := Q
  cases hbase
  cases hx
  cases hy
  cases hiso
  rfl

/- The two lemmas below restate `CategoryTheory.TwoFibreProductOver.eqToHom_a` and
`CategoryTheory.TwoFibreProductOver.eqToHom_b` with the congruence argument written as a lambda,
`congrArg (fun R => R.x) e` rather than `congrArg TwoFibreProductOver.x e`. -/

/-- The `𝒳`-component of the morphism induced by an equality of objects of the 2-fibre product is
the one induced by the equality of the `𝒳`-components. -/
theorem fibreEqToHom_a {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (h : P = Q) :
    (eqToHom h).a = eqToHom (congrArg (fun R : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G => R.x) h) := by
  cases h
  rfl

/-- The `𝒴`-component of the morphism induced by an equality of objects of the 2-fibre product is
the one induced by the equality of the `𝒴`-components. -/
theorem fibreEqToHom_b {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (h : P = Q) :
    (eqToHom h).b = eqToHom (congrArg (fun R : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G => R.y) h) := by
  cases h
  rfl

section Diagonal

variable {𝒮' : Type u₂} [Category.{v₂} 𝒮'] {𝒟 : Type u₃} [Category.{v₃} 𝒟]
  {q𝒮 : 𝒮 ⥤ 𝒞} {p𝒮' : 𝒮' ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞} {H : 𝒮 ⥤ 𝒮'} {b : 𝒮' ⥤ 𝒟}

/-- **The diagonal of a composite.** The diagonal of `H ⋙ b` is the diagonal of `H` followed by
the comparison 1-morphism of `CategoryTheory.TwoFibreProductOver.mapBase`: both send `x` to the
triple `(x, x, φ)` with `φ` an identity, read through `b` on one side. -/
theorem diagonal_comp_mapBase (hH : H ⋙ p𝒮' = q𝒮) (hb : b ⋙ p𝒟 = p𝒮')
    (hHb : (H ⋙ b) ⋙ p𝒟 = q𝒮) :
    diagonal hH ⋙ mapBase (pT := q𝒮) (p𝒜 := q𝒮) H H b hb = diagonal hHb := by
  have hobj : ∀ x : 𝒮,
      (diagonal hH ⋙ mapBase (pT := q𝒮) (p𝒜 := q𝒮) H H b hb).obj x = (diagonal hHb).obj x :=
    fun x => ext_of_heq_iso rfl rfl rfl (heq_of_eq (b.mapIso_refl (H.obj x)))
  refine Functor.ext hobj ?_
  intro x y φ
  refine Hom.ext' ?_ ?_
  · change φ = (eqToHom (hobj x)).a ≫ φ ≫ (eqToHom (hobj y).symm).a
    rw [eqToHom_a (hobj x), eqToHom_a (hobj y).symm]
    change φ = 𝟙 x ≫ φ ≫ 𝟙 y
    simp
  · change φ = (eqToHom (hobj x)).b ≫ φ ≫ (eqToHom (hobj y).symm).b
    rw [eqToHom_b (hobj x), eqToHom_b (hobj y).symm]
    change φ = 𝟙 x ≫ φ ≫ 𝟙 y
    simp

end Diagonal

end CategoryTheory.TwoFibreProductOver

end
