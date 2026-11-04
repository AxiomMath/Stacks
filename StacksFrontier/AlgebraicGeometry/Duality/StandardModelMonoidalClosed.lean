module

public import StacksFrontier.AlgebraicGeometry.Duality.ParametrizedAdjointUniqueness
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageDuality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorMonoidalClosed
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedBiduality

/-!
# `D(𝒪_X)` at the standard model is closed symmetric monoidal

For a scheme `X`, the derived category `D(𝒪_X)` at `CategoryTheory.HasDerivedCategory.standard`
carries the symmetric monoidal structure of [Stacks, Tag 0FPT] whose tensor product is the
derived tensor product `- ⊗ᴸ -` on the nose, and the adjunctions `- ⊗ᴸ B ⊣ R𝓗om(B, -)` of
[Stacks, Tag 08J8] make it closed, with internal hom `R𝓗om(B, -)` on the nose.

## Main definitions

* `Stacks.Duality.TwistedInverseImageDuality.stdMonoidal`, `stdSymmetric` — the symmetric monoidal
  structure, with `curriedTensor = tensor X` by `rfl`.
* `Stacks.Duality.TwistedInverseImageDuality.tensorHomAdjunction₂` — the adjunctions of
  [Stacks, Tag 08J8] as one adjunction with a parameter, natural in `B`.
* `Stacks.Duality.TwistedInverseImageDuality.stdMonoidalClosed` — the closed structure, with
  `ihom B = R𝓗om(B, -)` by `rfl`.
* `Stacks.Duality.TwistedInverseImageDuality.internalHomIso` — the internal hom bifunctor of the
  closed structure is `sheafHom X`, as bifunctors, with identity components; its
  morphisms are `Stacks.Duality.TwistedInverseImageDuality.pre_app_std`.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite

universe u

namespace Stacks.Duality.TwistedInverseImageDuality

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : Scheme.{u})

/-- The monoidal structure of `D(𝒪_X)` at the standard model whose tensor product is the derived
tensor product `tensor X` ([Stacks, Tag 0FPT]). -/
@[instance_reducible]
def stdMonoidal : MonoidalCategory (Std X) :=
  RingedSite.derivedTensorMonoidal (Stacks.SheafOfModules.ringedSite X.sheaf)

/-- The symmetry of `stdMonoidal`, the Koszul symmetry of [Stacks, Tag 0FPT]. -/
@[instance_reducible]
def stdSymmetric : @SymmetricCategory (Std X) _ (stdMonoidal X) :=
  RingedSite.derivedTensorSymmetric (Stacks.SheafOfModules.ringedSite X.sheaf)

attribute [local instance] stdMonoidal stdSymmetric

/-- The tensor product of `stdMonoidal` is `tensor X`. -/
theorem curriedTensor_std : curriedTensor (Std X) = tensor X := rfl

/-- The braiding of `stdSymmetric` is the commutativity constraint of the derived tensor product
used by the biduality morphism. -/
theorem braiding_std (A B : Std X) :
    β_ A B = (RingedSite.derivedTensorBraiding (Stacks.SheafOfModules.ringedSite X.sheaf) A B :) :=
  rfl

/-- **[Stacks, Tag 08J8] with a parameter**: the adjunctions `- ⊗ᴸ B ⊣ R𝓗om(B, -)`, natural in
`B`. -/
def tensorHomAdjunction₂ : (tensor X).flip ⊣₂ sheafHom X :=
  ParametrizedAdjunction.mk' (fun B => tensorHomAdjunction X B) (by
    intro B' B l A Z g
    change (tensorHomAdjunction X B').homEquiv A Z (((tensor X).obj A).map l ≫ g) = _
    have h := curry_naturality_middle X A Z l ((tensorHomAdjunction X B).homEquiv A Z g)
    simp only [curry, Equiv.symm_apply_apply] at h
    rw [← h, Equiv.apply_symm_apply])

/-- The braiding identifies `(tensor X).flip`, the bifunctor `B ↦ (- ⊗ᴸ B)`, with
`curriedTensor`, the bifunctor `B ↦ (B ⊗ᴸ -)`. -/
def flipTensorIso : (tensor X).flip ≅ curriedTensor (Std X) :=
  RingedSite.derivedTensorFlipIso (Stacks.SheafOfModules.ringedSite X.sheaf)

/-- **`D(𝒪_X)` at the standard model is monoidal closed**, with internal hom `R𝓗om(B, -)`. -/
@[instance_reducible]
def stdMonoidalClosed : MonoidalClosed (Std X) where
  closed B :=
    { rightAdj := (sheafHom X).obj (op B)
      adj := (tensorHomAdjunction X B).ofNatIsoLeft ((flipTensorIso X).app B) }

attribute [local instance] stdMonoidalClosed

/-- The internal hom of `stdMonoidalClosed` is `R𝓗om(B, -)`. -/
theorem ihom_std (B : Std X) : ihom B = (sheafHom X).obj (op B) := rfl

/-- `MonoidalClosed.pre` of `stdMonoidalClosed` is the contravariant action of `R𝓗om`: both
are the adjunct of `g ▷ R𝓗om(B, Z) ≫ ev`. -/
theorem pre_app_std {A B : Std X} (g : A ⟶ B) (Z : Std X) :
    (MonoidalClosed.pre g).app Z = ((sheafHom X).map g.op).app Z := by
  have h :=
    (parametrizedOfNatIsoLeft (tensorHomAdjunction₂ X) (flipTensorIso X)).homEquiv_naturality_one
      g ((ihom.ev B).app Z)
  have h1 : (MonoidalClosed.pre g).app Z =
      MonoidalClosed.curry (g ▷ (ihom B).obj Z ≫ (ihom.ev B).app Z) := by
    rw [← MonoidalClosed.id_tensor_pre_app_comp_ev, ← MonoidalClosed.uncurry_eq,
      MonoidalClosed.curry_uncurry]
  have h3 : MonoidalClosed.curry ((ihom.ev B).app Z) = 𝟙 ((ihom B).obj Z) := by
    rw [← MonoidalClosed.uncurry_id_eq_ev, MonoidalClosed.curry_uncurry]
  refine h1.trans (h.trans ?_)
  show MonoidalClosed.curry ((ihom.ev B).app Z) ≫ _ = _
  rw [h3]
  exact Category.id_comp _

/-- **The biduality of `stdMonoidalClosed` is the biduality morphism of [Stacks, Tag 0A89].** -/
theorem closedBidualityApp_std (ω M : Std X) :
    MonoidalClosed.closedBidualityApp ω M = bidual X ω M := by
  have h := RingedSite.closedBidualityApp_eq_derivedBiduality
    (Stacks.SheafOfModules.ringedSite X.sheaf) ω M
  exact h

/-- **The internal hom bifunctor of `stdMonoidalClosed` is `R𝓗om`**, as bifunctors, with
identity components. -/
def internalHomIso : MonoidalClosed.internalHom (C := Std X) ≅ sheafHom X :=
  NatIso.ofComponents
    (fun B => NatIso.ofComponents (fun Z => Iso.refl (((sheafHom X).obj B).obj Z))
      (fun h => (Category.comp_id _).trans (Category.id_comp _).symm))
    (fun {B A} g => by
      ext Z
      exact (Category.comp_id _).trans ((pre_app_std X g.unop Z).trans (Category.id_comp _).symm))

end Stacks.Duality.TwistedInverseImageDuality

end
