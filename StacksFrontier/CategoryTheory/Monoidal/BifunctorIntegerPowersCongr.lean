module

public import StacksFrontier.CategoryTheory.Monoidal.BifunctorIntegerPowersMap

/-!
# Integer tensor powers are invariant under isomorphisms of the factors

Let `T : C ⥤ C ⥤ C` be a bifunctor with a chosen unit object `𝟙`.  If `E ≅ E₁` and `E' ≅ E₁'`,
then the integer tensor powers `E^{⊗ n}` formed with the chosen dual `E'` and `E₁^{⊗ n}` formed
with the chosen dual `E₁'` are isomorphic for every `n ∈ ℤ`; and for families of isomorphisms
`E j ≅ E₁ j`, `E' j ≅ E₁' j` the products `E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}` are isomorphic.  No
coherence of `T` is used: the comparison is built entry by entry from the functoriality of `T`.

## Main definitions

* `CategoryTheory.Functor.intTensorPowCongrIso`: `E^{⊗ n} ≅ E₁^{⊗ n}`.
* `CategoryTheory.Functor.multiTensorPowCongrIso`:
  `E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r} ≅ E_{1,1}^{⊗ n_1} ⊗ ⋯ ⊗ E_{1,r}^{⊗ n_r}`.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] (T : C ⥤ C ⥤ C) (one : C)

/-- **Integer tensor powers are invariant under isomorphisms of the factor and of its chosen
dual**: `E ≅ E₁` and `E' ≅ E₁'` give `E^{⊗ n} ≅ E₁^{⊗ n}` for every `n ∈ ℤ`. -/
def intTensorPowCongrIso {E E₁ E' E₁' : C} (e : E ≅ E₁) (e' : E' ≅ E₁') :
    ∀ n : ℤ, T.intTensorPow one E E' n ≅ T.intTensorPow one E₁ E₁' n
  | .ofNat n =>
      eqToIso (by rw [List.map_replicate]; rfl) ≪≫
        tensorListCongrIso T one (f := fun _ : Unit => E) (g := fun _ => E₁) (fun _ => e)
          (List.replicate n ()) ≪≫
        eqToIso (by rw [List.map_replicate]; rfl)
  | .negSucc n =>
      eqToIso (by rw [List.map_replicate]; rfl) ≪≫
        tensorListCongrIso T one (f := fun _ : Unit => E') (g := fun _ => E₁') (fun _ => e')
          (List.replicate (n + 1) ()) ≪≫
        eqToIso (by rw [List.map_replicate]; rfl)

/-- **Products of integer tensor powers are invariant under isomorphisms of the factors and of
their chosen duals**: families of isomorphisms `E j ≅ E₁ j` and `E' j ≅ E₁' j` give
`E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r} ≅ E_{1,1}^{⊗ n_1} ⊗ ⋯ ⊗ E_{1,r}^{⊗ n_r}`. -/
def multiTensorPowCongrIso {r : ℕ} {E E₁ E' E₁' : Fin r → C} (e : ∀ j, E j ≅ E₁ j)
    (e' : ∀ j, E' j ≅ E₁' j) (n : Fin r → ℤ) :
    T.multiTensorPow one E E' n ≅ T.multiTensorPow one E₁ E₁' n :=
  eqToIso (by rw [multiTensorPow, List.ofFn_eq_map]) ≪≫
    tensorListCongrIso T one (fun j => intTensorPowCongrIso T one (e j) (e' j) (n j))
      (List.finRange r) ≪≫
    eqToIso (by rw [multiTensorPow, List.ofFn_eq_map])

end CategoryTheory.Functor

end
