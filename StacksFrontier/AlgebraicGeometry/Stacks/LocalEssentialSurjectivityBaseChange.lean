module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalSquare

/-!
# Local essential surjectivity is stable under base change

Let `f : 𝒳 ⟶ 𝒵` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of categories fibred in groupoids over the big
fppf site of `S`. If `f` is locally essentially surjective — every object of a fibre of `𝒵`
becomes, after restriction to a covering sieve, isomorphic to the image of an object of `𝒳` —
then so is the second projection `𝒳 ×_𝒵 𝒴 ⟶ 𝒴` of the canonical 2-fibre product.

## Main results

* `AlgebraicGeometry.Stack.localEssSurj_twoFibreProductSquare_snd`.

## Implementation notes

Local essential surjectivity is written out longhand, in the shape consumed by
`AlgebraicGeometry.Stack.hasRelativeProperty_of_baseChange` (**Stacks 045D**).

Over an arrow `k : V ⟶ U` of the covering sieve supplied for the image `g y` of an object `y`
of `𝒴` over `U`, the hypothesis gives `x` and `φ : f x ⟶ g y` over `k`. A pullback `ψ : y' ⟶ y`
of `y` along `k` is mapped by `g` to a strongly cartesian arrow, so `φ` factors through `g ψ` by
a vertical arrow, which is invertible because the fibres of `𝒵` are groupoids. That vertical
isomorphism makes `(x, y')` an object of the 2-fibre product over `V`, and `ψ` is the required
arrow of `𝒴`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **The base change of a locally essentially surjective 1-morphism is locally essentially
surjective.** If `f : 𝒳 ⟶ 𝒵` is locally essentially surjective, so is the second projection
`𝒳 ×_𝒵 𝒴 ⟶ 𝒴` of the canonical 2-fibre product of `f` and any `g : 𝒴 ⟶ 𝒵`. -/
theorem localEssSurj_twoFibreProductSquare_snd (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵)
    (hf : ∀ (U : BigFppfOver B S hS) (t : 𝒵.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒳.val.obj, ∃ φ : (CatFiberedInGroupoids.homFunctor f).obj z ⟶ t.1,
            𝒵.val.p.IsHomLift k φ) :
    ∀ (U : BigFppfOver B S hS) (t : 𝒴.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt.val.obj,
            ∃ φ : (CatFiberedInGroupoids.homFunctor
                (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).snd).obj z ⟶
                t.1,
              𝒴.val.p.IsHomLift k φ := by
  intro U t
  have hgt : 𝒵.val.p.obj (g.hom.toFunctor.obj t.1) = U :=
    (Functor.congr_obj g.hom.w t.1).trans t.2
  obtain ⟨R, hR, hlift⟩ := hf U ⟨g.hom.toFunctor.obj t.1, hgt⟩
  refine ⟨R, hR, fun V k hk => ?_⟩
  obtain ⟨z, φ, hφ⟩ := hlift hk
  obtain ⟨y', ψ, hψ⟩ := 𝒴.isFiberedInGroupoids.exists_lift k t.1 t.2
  have hgψ : 𝒵.val.p.IsHomLift k (g.hom.toFunctor.map ψ) :=
    BasedFunctor.preserves_isHomLift (F := g.hom) (f := k) (φ := ψ)
  have hcart : 𝒵.val.p.IsStronglyCartesian k (g.hom.toFunctor.map ψ) :=
    𝒵.isFiberedInGroupoids.isStronglyCartesian_homLift k _
  have hφ' : 𝒵.val.p.IsHomLift (𝟙 V ≫ k) φ := by simpa using hφ
  obtain ⟨χ, ⟨hχ, hχφ⟩, -⟩ := IsStronglyCartesian.universal_property 𝒵.val.p k
    (g.hom.toFunctor.map ψ) (𝟙 V) (𝟙 V ≫ k) rfl φ
  have hχiso : IsIso χ := by
    have := 𝒵.isFiberedInGroupoids.isStronglyCartesian_homLift (𝟙 V) χ
    exact IsStronglyCartesian.isIso_of_base_isIso (p := 𝒵.val.p) (f := 𝟙 V) χ
  have hz : 𝒳.val.p.obj z = V :=
    (Functor.congr_obj f.hom.w z).symm.trans (IsHomLift.domain_eq 𝒵.val.p k φ)
  have hy' : 𝒴.val.p.obj y' = V := IsHomLift.domain_eq 𝒴.val.p k ψ
  refine ⟨{ base := V, x := z, y := y', hx := hz, hy := hy', iso := asIso χ
            vertical := hχ }, ψ, hψ⟩

end AlgebraicGeometry.Stack

end
