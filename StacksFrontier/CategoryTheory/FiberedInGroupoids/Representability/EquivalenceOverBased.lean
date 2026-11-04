module

public import StacksFrontier.CategoryTheory.FiberedCategory.EquivalenceInvariance
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion

/-!
# An equivalence over the base, read in the 2-category of categories over the base

An equivalence over `𝒞` in the sense of `StacksRepresentableCFG.EquivalenceOver p q` consists of
two 1-morphisms over `𝒞` together with a unit and a counit whose whiskering with the structure
functor is an `eqToHom`. A `CategoryTheory.BasedCategory.Equivalence 𝒳 𝒴` is an equivalence in the
2-category `BasedCategory 𝒞`, whose unit and counit are isomorphisms of `BasedFunctor`s. Every
equivalence of the first kind is an equivalence of the second kind.

## Main definitions

* `CategoryTheory.StacksRepresentableCFG.EquivalenceOver.toBasedEquivalence`: an equivalence over
  `𝒞` in the sense of `StacksRepresentableCFG.EquivalenceOver`, as a
  `CategoryTheory.BasedCategory.Equivalence`.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- An equivalence over `𝒞` in the sense of `StacksRepresentableCFG.EquivalenceOver`, read as an
equivalence in the 2-category of categories over `𝒞`, that is as a
`CategoryTheory.BasedCategory.Equivalence`. The two categories over `𝒞` may live in different
object and morphism universes. Its functor and inverse are those of `e`, its unit is the inverse of
the unit of `e`, and its counit is the counit of `e`. -/
def StacksRepresentableCFG.EquivalenceOver.toBasedEquivalence
    {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : BasedCategory.{v₂, u₂} 𝒞}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒞}
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.p 𝒴.p) :
    BasedCategory.Equivalence 𝒳 𝒴 where
  functor := ⟨e.hom.functor, e.hom.w⟩
  inverse := ⟨e.inv.functor, e.inv.w⟩
  unitIso := BasedNatIso.mkNatIso e.unitIso.symm fun a ↦ e.isHomLift_unitIso_inv_app a
  counitIso := BasedNatIso.mkNatIso e.counitIso fun a ↦ e.isHomLift_counitIso_hom_app a

end CategoryTheory

end
