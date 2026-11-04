module

public import StacksFrontier.CategoryTheory.Monoidal.BifunctorIntegerPowers
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.Data.List.FinRange

/-!
# Integer tensor powers along a functor compatible with the tensor products

Let `T : C ⥤ C ⥤ C` and `T' : D ⥤ D ⥤ D` be bifunctors with chosen unit objects `𝟙` and `𝟙'`,
and let `F : C ⥤ D` be a functor together with isomorphisms
`F(A ⊗ B) ≅ F A ⊗' F B` for all objects `A`, `B` and `F 𝟙 ≅ 𝟙'`; no coherence is asked of them.
Then `F` carries the tensor product of a list of objects to the tensor product of the list of
their images, the integer tensor powers `E^{⊗ n}` (for a chosen dual `E'` of `E`) to the integer
tensor powers of `F E` for any object `D'` with `F E' ≅ D'`, and the products
`E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}` to the corresponding products for the images.

## Main definitions

* `CategoryTheory.Functor.tensorListCongrIso`: the tensor product of a list is invariant, up to
  isomorphism, under replacing its entries by isomorphic ones.
* `CategoryTheory.Functor.tensorListMapIso`: `F(A₁ ⊗ ⋯ ⊗ A_r) ≅ F A₁ ⊗' ⋯ ⊗' F A_r`.
* `CategoryTheory.Functor.intTensorPowMapIso`: `F(E^{⊗ n}) ≅ (F E)^{⊗ n}`.
* `CategoryTheory.Functor.multiTensorPowMapIso`:
  `F(E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}) ≅ (F E_1)^{⊗ n_1} ⊗' ⋯ ⊗' (F E_r)^{⊗ n_r}`.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] (T : C ⥤ C ⥤ C) (one : C)
  (T' : D ⥤ D ⥤ D) (one' : D)

/-- **The tensor product of a list is invariant under replacing its entries by isomorphic
ones**: for families `f`, `g` indexed by `ι` with `f i ≅ g i`, the tensor products of the lists
`l.map f` and `l.map g` are isomorphic. -/
def tensorListCongrIso {ι : Type*} {f g : ι → D} (e : ∀ i, f i ≅ g i) :
    ∀ l : List ι, T'.tensorList one' (l.map f) ≅ T'.tensorList one' (l.map g)
  | [] => Iso.refl _
  | [i] => e i
  | i :: j :: l =>
      (T'.mapIso (e i)).app _ ≪≫ (T'.obj (g i)).mapIso (tensorListCongrIso e (j :: l))

variable {T one T' one'}

/-- **A functor compatible with the tensor products carries the tensor product of a list to the
tensor product of the list of images**: `F(A₁ ⊗ ⋯ ⊗ A_r) ≅ F A₁ ⊗' ⋯ ⊗' F A_r`. -/
def tensorListMapIso (F : C ⥤ D)
    (μ : ∀ A B, F.obj ((T.obj A).obj B) ≅ (T'.obj (F.obj A)).obj (F.obj B))
    (ε : F.obj one ≅ one') :
    ∀ l : List C, F.obj (T.tensorList one l) ≅ T'.tensorList one' (l.map F.obj)
  | [] => ε
  | [_] => Iso.refl _
  | A :: A' :: l => μ A _ ≪≫ (T'.obj (F.obj A)).mapIso (tensorListMapIso F μ ε (A' :: l))

/-- **A functor compatible with the tensor products carries integer tensor powers to integer
tensor powers**: `F(E^{⊗ n}) ≅ (F E)^{⊗ n}`, where the negative powers of `E` are formed with
the chosen dual `E'` and those of `F E` with any object `D'` isomorphic to `F E'`. -/
def intTensorPowMapIso (F : C ⥤ D)
    (μ : ∀ A B, F.obj ((T.obj A).obj B) ≅ (T'.obj (F.obj A)).obj (F.obj B))
    (ε : F.obj one ≅ one') (E E' : C) (D' : D) (eD : F.obj E' ≅ D') :
    ∀ n : ℤ, F.obj (T.intTensorPow one E E' n) ≅ T'.intTensorPow one' (F.obj E) D' n
  | .ofNat n =>
      tensorListMapIso F μ ε (List.replicate n E) ≪≫ eqToIso (by rw [List.map_replicate]; rfl)
  | .negSucc n =>
      tensorListMapIso F μ ε (List.replicate (n + 1) E') ≪≫
        eqToIso (by rw [List.map_replicate, List.map_replicate]) ≪≫
        tensorListCongrIso T' one' (f := fun _ : Unit => F.obj E') (g := fun _ => D')
          (fun _ => eD) (List.replicate (n + 1) ()) ≪≫
        eqToIso (by rw [List.map_replicate]; rfl)

/-- **A functor compatible with the tensor products carries the products of integer tensor
powers to the corresponding products**:
`F(E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}) ≅ (F E_1)^{⊗ n_1} ⊗' ⋯ ⊗' (F E_r)^{⊗ n_r}`, the negative powers
of `F E_j` being formed with objects `D' j` isomorphic to the images of the chosen duals. -/
def multiTensorPowMapIso (F : C ⥤ D)
    (μ : ∀ A B, F.obj ((T.obj A).obj B) ≅ (T'.obj (F.obj A)).obj (F.obj B))
    (ε : F.obj one ≅ one') {r : ℕ} (E E' : Fin r → C) (D' : Fin r → D)
    (eD : ∀ j, F.obj (E' j) ≅ D' j) (n : Fin r → ℤ) :
    F.obj (T.multiTensorPow one E E' n) ≅ T'.multiTensorPow one' (fun j => F.obj (E j)) D' n :=
  tensorListMapIso F μ ε _ ≪≫
    eqToIso (by rw [List.map_ofFn, List.ofFn_eq_map]; rfl) ≪≫
    tensorListCongrIso T' one' (fun j => intTensorPowMapIso F μ ε (E j) (E' j) (D' j) (eD j) (n j))
      (List.finRange r) ≪≫
    eqToIso (by rw [multiTensorPow, List.ofFn_eq_map])

end CategoryTheory.Functor

end
