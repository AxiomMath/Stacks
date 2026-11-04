module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequenceSquare

/-!
# The identity square acts as the identity on the two terms of a conormal sequence

For a commutative square
```
B₁ ──β──▸ B₂
▲          ▲
φ₁         φ₂
│          │
A₁ ──ψ──▸ A₂
```
of sheaves of commutative rings on a site, `Stacks.Sites.Conormal.conormalSheafMapOfSquare` and
`Stacks.Sites.Conormal.tensorSheafMapOfSquare` are the induced maps `I₁/I₁² ⟶ I₂/I₂²` and
`B₁ ⊗_{A₁} Ω_{A₁/R₁} ⟶ B₂ ⊗_{A₂} Ω_{A₂/R₂}` of the two terms of the conormal sequences. For the
identity square both maps are the identity.

## Main results

* `Stacks.Sites.Conormal.conormalSheafMapOfSquare_eq_id`: the map of conormal sheaves attached
  to the identity square is the identity.
* `Stacks.Sites.Conormal.tensorSheafMapOfSquare_eq_id`: the same for the map of the scalar
  extensions of the differentials.

## References

* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal sequence.
* [Stacks Project, Tag 08TR](https://stacks.math.columbia.edu/tag/08TR), the functoriality of
  the sheaf of relative differentials.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe v u w z

namespace Stacks.Sites.Conormal

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable (R A B : Sheaf J CommRingCat.{w}) (a : R ⟶ A) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective J φ.hom]

/-- The map of conormal sheaves attached to a square whose two horizontal morphisms are the
identity is the identity of `I/I²`. -/
lemma conormalSheafMapOfSquare_eq_id (ψ : A ⟶ A) (hψ : ψ = 𝟙 A)
    (hsq : ψ ≫ φ = φ ≫ 𝟙 B) :
    conormalSheafMapOfSquare.{v, u, w, z} J A A B B φ φ ψ (𝟙 B) hsq = 𝟙 _ := by
  subst hψ
  apply sheafify_hom_ext.{v, u, w, z} J A B φ (conormalPresheaf φ.hom)
  intro X c
  obtain ⟨x, rfl⟩ := (kernelIdeal φ.hom X).toCotangent_surjective c
  show ((conormalSheafMapOfSquare.{v, u, w, z} J A A B B φ φ (𝟙 A) (𝟙 B) hsq).val.app X)
      (toAssociatedModule.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) X
        ((kernelIdeal φ.hom X).toCotangent x)) =
    toAssociatedModule.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) X
      (conormalMapOfSquare φ.hom φ.hom (𝟙 A : A ⟶ A).hom (𝟙 B : B ⟶ B).hom
        (hom_of_square hsq) X ((kernelIdeal φ.hom X).toCotangent x))
  apply sheafifyLiftDesc_toAssociatedModule.{v, u, w, z}

/-- The map of the scalar extensions of the differentials attached to a square whose horizontal
morphisms, including the one on the base rings, are the identity is the identity of
`B ⊗_A Ω_{A/R}`. -/
lemma tensorSheafMapOfSquare_eq_id (ψ : A ⟶ A) (hψ : ψ = 𝟙 A) (ρ : R ⟶ R) (hρ : ρ = 𝟙 R)
    (hsq : ψ ≫ φ = φ ≫ 𝟙 B) (ha : ρ ≫ a = a ≫ ψ) :
    tensorSheafMapOfSquare.{v, u, w, z} J R R A A B B a a φ φ ψ (𝟙 B) ρ hsq ha = 𝟙 _ := by
  subst hψ hρ
  have hs := hom_of_square hsq
  have ha' := hom_of_square ha
  have hquot : ∀ (X : Cᵒᵖ) (b : A.obj.obj X ⧸ kernelIdeal φ.hom X),
      quotientMapOfSquare φ.hom φ.hom (𝟙 A : A ⟶ A).hom (𝟙 B : B ⟶ B).hom hs X b = b := by
    intro X b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rfl
  let F := fun X ↦ tensorMapOfSquareₛₗ φ.hom φ.hom (𝟙 A : A ⟶ A).hom (𝟙 B : B ⟶ B).hom hs
    a.hom a.hom (𝟙 R : R ⟶ R).hom ha' X
  have htensor : ∀ (X : Cᵒᵖ) (t : (A.obj.obj X ⧸ kernelIdeal φ.hom X) ⊗[A.obj.obj X]
        ((differentialsPresheaf a.hom).obj X)), F X t = t := by
    intro X
    have hsmul : ∀ (r : (quotientPresheaf φ.hom).obj X)
        (t : (A.obj.obj X ⧸ kernelIdeal φ.hom X) ⊗[A.obj.obj X]
          ((differentialsPresheaf a.hom).obj X)), F X (r • t) = r • F X t := fun r t ↦
      (tensorMapOfSquareₛₗ_smul φ.hom φ.hom (𝟙 A : A ⟶ A).hom (𝟙 B : B ⟶ B).hom hs
        a.hom a.hom (𝟙 R : R ⟶ R).hom ha' X r t).trans (by rw [hquot])
    have key : (LinearMap.mk (AddHom.mk (fun t ↦ F X t) (map_add (F X))) hsmul :
        tensorObj φ.hom a.hom X →ₗ[(quotientPresheaf φ.hom).obj X]
          tensorObj φ.hom a.hom X) = LinearMap.id := by
      apply tensor_hom_ext φ.hom a.hom X
      intro b x
      show F X (b ⊗ₜ[A.obj.obj X] CommRingCat.KaehlerDifferential.d (f := a.hom.app X) x) =
        b ⊗ₜ[A.obj.obj X] CommRingCat.KaehlerDifferential.d (f := a.hom.app X) x
      refine (TensorProduct.map_tmul _ _ _ _).trans ?_
      exact congrArg₂ (fun b (ω : (differentialsPresheaf a.hom).obj X) ↦
          b ⊗ₜ[A.obj.obj X] ω) (hquot X b)
        (differentialsMapOfSquare_d (𝟙 A : A ⟶ A).hom a.hom a.hom (𝟙 R : R ⟶ R).hom ha' X x)
    exact LinearMap.congr_fun key
  apply sheafify_hom_ext.{v, u, w, z} J A B φ (tensorPresheaf φ.hom a.hom)
  intro X t
  exact (sheafifyLiftDesc_toAssociatedModule.{v, u, w, z} ..).trans
    (congrArg (toAssociatedModule.{v, u, w, z} J A B φ (tensorPresheaf φ.hom a.hom) X)
      (htensor X t))

end Stacks.Sites.Conormal

end
