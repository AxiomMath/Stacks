module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Restricting an adjunction to a reflective subcategory of the target

Let `L ⊣ R` be an adjunction between `C` and `D`, let `P` be a property of objects of `D` whose
full subcategory is reflective, with reflector `ρ`, and let `Q` be a property of objects of `C`
such that `R` carries objects satisfying `P` to objects satisfying `Q`. Then `R` restricts to a
functor `P ⥤ Q`, and it has the left adjoint `Q ⥤ C ⥤ D ⥤ P` given by `L` followed by `ρ`:

`Hom_Q(K, R M) = Hom_C(K, R M) = Hom_D(L K, M) = Hom_P(ρ L K, M)`.

## Main definitions

* `CategoryTheory.Adjunction.restrictReflective`: the adjunction
  `Q.ι ⋙ L ⋙ P.ι.leftAdjoint ⊣ Q.lift (P.ι ⋙ R) _`.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Adjunction

variable {C : Type*} [Category C] {D : Type*} [Category D] {L : C ⥤ D} {R : D ⥤ C}
  (adj : L ⊣ R) (P : ObjectProperty D) (Q : ObjectProperty C) [P.ι.IsRightAdjoint]
  (hR : ∀ M : P.FullSubcategory, Q (R.obj M.1))

/-- If `L ⊣ R`, the full subcategory `P` of `D` is reflective, and `R` carries `P` into `Q`, then
`L` followed by the reflector onto `P` is left adjoint to `R : P ⥤ Q`. -/
def restrictReflective :
    Q.ι ⋙ L ⋙ P.ι.leftAdjoint ⊣ Q.lift (P.ι ⋙ R) hR :=
  Adjunction.restrictFullyFaithful (adj.comp (Adjunction.ofIsRightAdjoint P.ι))
    Q.fullyFaithfulι (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    ((Functor.leftUnitor _).trans (Q.liftCompιIso (P.ι ⋙ R) hR).symm)

end CategoryTheory.Adjunction

end
