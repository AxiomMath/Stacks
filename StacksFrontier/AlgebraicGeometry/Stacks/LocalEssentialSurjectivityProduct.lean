module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalSquare

/-!
# A product of locally essentially surjective 1-morphisms is locally essentially surjective

Let `x : 𝒯₁ ⟶ 𝒳` and `y : 𝒯₂ ⟶ 𝒳` be 1-morphisms of categories fibred in groupoids over the big
fppf site of `S` with a common target, and let

```text
x × y : 𝒯₁ × 𝒯₂ ⟶ 𝒳 × 𝒳
```

be their product (`CategoryTheory.CatFiberedInGroupoids.productMap`). This file proves that
`x × y` is locally essentially surjective as soon as `x` and `y` are: every object of a fibre of
`𝒳 × 𝒳` becomes, after restriction to a covering sieve of the big fppf topology, isomorphic to
the image of an object of `𝒯₁ × 𝒯₂`.

The proof is the only one available and it uses no geometry: an object of `𝒳 × 𝒳` over `U` is a
pair of objects of `𝒳` over `U` together with a comparison of their images, so the two
hypotheses give two covering sieves of `U`, and the conclusion holds on their intersection,
which is covering because `AlgebraicGeometry.BigFppfOver.topology` is a Grothendieck topology.

## Main results

* `AlgebraicGeometry.Stack.localEssSurj_productMap`.

## Implementation notes

Local essential surjectivity is not a named predicate in this library — it is written out
longhand in the signature of every statement that consumes it, as in
`AlgebraicGeometry.Stack.hasRelativeProperty_of_baseChange` (**Stacks 045D**) and
`AlgebraicGeometry.Stack.localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation` —
so the two hypotheses and the conclusion here are spelled out in that same shape, and a consumer
can feed the conclusion straight to those statements.

No `@[stacks]` attribute is carried. The Stacks project states the geometric form of this step
inside the proof of **Stacks 06MB**, as the sentence "`W × W → 𝒳 × 𝒳` is also surjective, flat,
and locally of finite presentation"; that sentence asserts the three relative properties of
Stacks 03YK, which is strictly more than the local essential surjectivity proved here, and it
carries no tag of its own. The geometric form is reached from this statement by instantiating the
two hypotheses with
`AlgebraicGeometry.Stack.localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation`.

The comparison isomorphism of the object of `𝒯₁ × 𝒯₂` that the proof builds is forced to be an
`CategoryTheory.eqToHom`, by `CategoryTheory.TwoFibreProductOver.prodOver_iso_hom`: being
vertical for the identity structure functor of a product, it can be nothing else. That is also
why the comparison square of the morphism built alongside it is automatic, by
`CategoryTheory.TwoFibreProductOver.prodOver_w_eqToHom`.

The universes are pinned at `CatFiberedInGroupoids.{u, u, u + 1, u + 1}`, which is where the
2-category of algebraic stacks of **Stacks 03YP** and the statements of Stacks 045D over it live.

## References

* [Stacks Project, Tag 02XE](https://stacks.math.columbia.edu/tag/02XE)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 06MB](https://stacks.math.columbia.edu/tag/06MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒯₁ 𝒯₂ 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **A product of two locally essentially surjective 1-morphisms is locally essentially
surjective.** For 1-morphisms `x : 𝒯₁ ⟶ 𝒳` and `y : 𝒯₂ ⟶ 𝒳` of categories fibred in groupoids
over the big fppf site of `S` with a common target, if every object of a fibre of `𝒳` becomes
isomorphic to an image under `x`, resp. under `y`, after restriction to a covering sieve, then
every object of a fibre of `𝒳 × 𝒳` becomes isomorphic to an image under `x × y` after
restriction to a covering sieve.

Both components of an object of `𝒳 × 𝒳` over `U` lie over `U`, so each hypothesis supplies a
covering sieve of `U`; the intersection of the two is covering, and over any arrow of it the two
lifts assemble into an object of `𝒯₁ × 𝒯₂` and the two isomorphisms into a morphism to the given
object. -/
theorem localEssSurj_productMap (x : 𝒯₁ ⟶ 𝒳) (y : 𝒯₂ ⟶ 𝒳)
    (hx : ∀ (U : BigFppfOver B S hS) (t : 𝒳.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒯₁.val.obj, ∃ φ : (CatFiberedInGroupoids.homFunctor x).obj z ⟶ t.1,
            𝒳.val.p.IsHomLift k φ)
    (hy : ∀ (U : BigFppfOver B S hS) (t : 𝒳.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒯₂.val.obj, ∃ φ : (CatFiberedInGroupoids.homFunctor y).obj z ⟶ t.1,
            𝒳.val.p.IsHomLift k φ) :
    ∀ (U : BigFppfOver B S hS) (t : (CatFiberedInGroupoids.product 𝒳 𝒳).val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : (CatFiberedInGroupoids.product 𝒯₁ 𝒯₂).val.obj,
            ∃ φ : (CatFiberedInGroupoids.homFunctor
                (CatFiberedInGroupoids.productMap x y)).obj z ⟶ t.1,
              (CatFiberedInGroupoids.product 𝒳 𝒳).val.p.IsHomLift k φ := by
  intro U t
  obtain ⟨T, hT⟩ := t
  subst hT
  obtain ⟨R₁, hR₁, h₁⟩ := hx _ ⟨T.x, T.hx⟩
  obtain ⟨R₂, hR₂, h₂⟩ := hy _ ⟨T.y, T.hy⟩
  refine ⟨R₁ ⊓ R₂, (BigFppfOver.topology B S hS).intersection_covering hR₁ hR₂, ?_⟩
  intro V k hk
  obtain ⟨z₁, ψ₁, hψ₁⟩ := h₁ hk.1
  obtain ⟨z₂, ψ₂, hψ₂⟩ := h₂ hk.2
  -- the two lifts lie over `V`, because `x` and `y` are 1-morphisms over the site
  have hz₁ : 𝒯₁.val.p.obj z₁ = V :=
    (Functor.congr_obj x.hom.w z₁).symm.trans
      (@IsHomLift.domain_eq _ _ _ _ 𝒳.val.p _ _ _ _ k ψ₁ hψ₁)
  have hz₂ : 𝒯₂.val.p.obj z₂ = V :=
    (Functor.congr_obj y.hom.w z₂).symm.trans
      (@IsHomLift.domain_eq _ _ _ _ 𝒳.val.p _ _ _ _ k ψ₂ hψ₂)
  refine ⟨{ base := V, x := z₁, y := z₂, hx := hz₁, hy := hz₂
            iso := eqToIso (hz₁.trans hz₂.symm)
            vertical := isHomLift_id_eqToHom hz₁ hz₂ (hz₁.trans hz₂.symm) },
          { hbase := k, a := ψ₁, b := ψ₂, ha := hψ₁, hb := hψ₂
            w := ?_ }, ?_⟩
  · rw [prodOver_iso_hom T]
    exact prodOver_w_eqToHom (k := k)
      (obj_eq_of_comp_eq x.hom.w hz₁) (obj_eq_of_comp_eq y.hom.w hz₂)
      T.hx T.hy hψ₁ hψ₂
  · exact structureFunctor_isHomLift _ k hψ₁

end AlgebraicGeometry.Stack

end
