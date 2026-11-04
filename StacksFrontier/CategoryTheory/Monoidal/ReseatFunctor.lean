module

public import StacksFrontier.CategoryTheory.Monoidal.Reseat

/-!
# Monoidal functors and re-seated monoidal structures

`CategoryTheory.MonoidalCategory.reseat e ε` is a monoidal structure on `C` whose tensor
bifunctor and unit are prescribed terms isomorphic to those of a given structure, and the identity
functor is monoidal from it to the given one (`CategoryTheory.MonoidalCategory.reseatMonoidal`).
This file records the converse and the consequence for a monoidal functor: a functor which is
monoidal for two given structures is monoidal for their re-seatings.

## Main definitions

* `CategoryTheory.MonoidalCategory.reseatMonoidalInverse` — the identity functor is monoidal from
  the given structure to the re-seated one.
* `CategoryTheory.MonoidalCategory.Functor.monoidalReseat` — a monoidal functor is monoidal for
  re-seatings of the structures of its source and target.
-/

@[expose] public noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MC : MonoidalCategory C] {T : C ⥤ C ⥤ C} {U : C}

/-- The identity functor is monoidal from a monoidal structure to its re-seating: the inverse
of the monoidal equivalence `CategoryTheory.MonoidalCategory.reseatMonoidal`. -/
@[instance_reducible]
def reseatMonoidalInverse (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) :
    @Functor.Monoidal C _ MC C _ (reseat e ε) (𝟭 C) :=
  @Equivalence.inverseMonoidal C _ (reseat e ε) C _ MC (Equivalence.refl)
    (MonoidalCategory.reseatMonoidal e ε)

variable {D : Type u₂} [Category.{v₂} D] [MD : MonoidalCategory D] {T' : D ⥤ D ⥤ D} {U' : D}

/-- **A monoidal functor is monoidal for re-seatings** of the monoidal structures of its source
and target: it is the composite of the identity, monoidal from the re-seated source to the
given one, the functor, and the identity, monoidal from the given target to its re-seating. -/
@[instance_reducible]
def Functor.monoidalReseat (F : C ⥤ D) [F.Monoidal] (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U)
    (e' : curriedTensor D ≅ T') (ε' : 𝟙_ D ≅ U') :
    @Functor.Monoidal C _ (reseat e ε) D _ (reseat e' ε') F :=
  @Functor.Monoidal.instComp C _ (reseat e ε) C _ MC D _ (reseat e' ε') (𝟭 C) (F ⋙ 𝟭 D)
    (MonoidalCategory.reseatMonoidal e ε)
    (@Functor.Monoidal.instComp C _ MC D _ MD D _ (reseat e' ε') F (𝟭 D) _
      (reseatMonoidalInverse e' ε'))

end CategoryTheory.MonoidalCategory
