module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentDirectImage

/-!
# The coherator on a full subcategory of modules containing the quasi-coherent ones

Let `𝒳` be an algebraic stack and let `L` be a full subcategory of `Mod(𝒪_𝒳)` containing
`QCoh(𝒪_𝒳)`.  The coherator `Q : Mod(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` of **Stacks 0781** part (2), restricted to
`L`, is right adjoint to the inclusion `QCoh(𝒪_𝒳) ⥤ L`, and its composite with that inclusion is
the identity of `QCoh(𝒪_𝒳)`.  For `L = LQCoh^fbc(𝒪_𝒳)` this is **Stacks 0778**.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentToSubcategory`: the inclusion
  `QCoh(𝒪_𝒳) ⥤ L`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.subcategoryCoheratorOfSeparator`: the restricted
  coherator `L ⥤ QCoh(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.subcategoryCoheratorAdjunctionOfSeparator`: the
  adjunction.
* `AlgebraicGeometry.Stack.AlgebraicStacks.subcategoryCoheratorCompIsoOfSeparator`: `Q ∘ i ≅ id`.

## References

* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0781](https://stacks.math.columbia.edu/tag/0781)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS) (L : ObjectProperty (Stack.fppfModules B S hS 𝒳))
  (hL : ∀ M : quasicoherentModules B S hS 𝒳, L ((quasicoherentInclusion B S hS 𝒳).obj M))
  (hsep : HasSeparator (quasicoherentModules B S hS 𝒳))

/-- The inclusion `QCoh(𝒪_𝒳) ⥤ L` of the quasi-coherent modules into a full subcategory of
`Mod(𝒪_𝒳)` containing them. -/
abbrev quasicoherentToSubcategory : quasicoherentModules B S hS 𝒳 ⥤ L.FullSubcategory :=
  L.lift (quasicoherentInclusion B S hS 𝒳) hL

/-- The coherator restricted to a full subcategory `L` of `Mod(𝒪_𝒳)`. -/
abbrev subcategoryCoheratorOfSeparator : L.FullSubcategory ⥤ quasicoherentModules B S hS 𝒳 :=
  L.ι ⋙ coheratorOfSeparator B S hS 𝒳 hsep

/-- **The restricted coherator is right adjoint to the inclusion of `QCoh(𝒪_𝒳)` into `L`.** -/
def subcategoryCoheratorAdjunctionOfSeparator :
    quasicoherentToSubcategory B S hS 𝒳 L hL ⊣ subcategoryCoheratorOfSeparator B S hS 𝒳 L hsep :=
  Adjunction.restrictFullyFaithful (coheratorAdjunctionOfSeparator B S hS 𝒳 hsep)
    (Functor.FullyFaithful.id _) (ObjectProperty.fullyFaithfulι L)
    (Functor.leftUnitor _ ≪≫ (L.liftCompιIso (quasicoherentInclusion B S hS 𝒳) hL).symm)
    (Functor.rightUnitor _).symm

/-- **The restricted coherator composed with the inclusion is the identity of `QCoh(𝒪_𝒳)`.** -/
def subcategoryCoheratorCompIsoOfSeparator :
    quasicoherentToSubcategory B S hS 𝒳 L hL ⋙ subcategoryCoheratorOfSeparator B S hS 𝒳 L hsep ≅
      𝟭 (quasicoherentModules B S hS 𝒳) :=
  (asIso (subcategoryCoheratorAdjunctionOfSeparator B S hS 𝒳 L hL hsep).unit).symm

end AlgebraicGeometry.Stack.AlgebraicStacks

end
