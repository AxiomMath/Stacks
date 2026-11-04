module

public import StacksFrontier.Algebra.Polynomial.Numerical
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria

/-!
# Twisting a sheaf by integer powers of finitely many invertible sheaves

For a sheaf of modules `ℱ` on a scheme and invertible sheaves `𝓛_1, …, 𝓛_r`, the twist
`ℱ ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r}` depends only on the isomorphism class of `ℱ`, is `ℱ` for
the zero exponent vector, and raising one exponent by one tensors it by the corresponding
invertible sheaf.

## Main definitions

* `AlgebraicGeometry.twistedSheaf`: the iterated tensor product
  `ℱ ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r}`, bracketed from the left.
* `AlgebraicGeometry.twistList`: the same fold over an arbitrary list of indices, starting from
  an arbitrary sheaf.

## Main results

* `Stacks.SheafOfModules.Invertible.tensorProductSwapIso`: `(M ⊗ A) ⊗ B ≅ (M ⊗ B) ⊗ A`.
* `Stacks.SheafOfModules.Invertible.tensorProductPowerSuccIso`:
  `M ⊗ 𝓛^{⊗ (n + 1)} ≅ (M ⊗ 𝓛^{⊗ n}) ⊗ 𝓛`.
* `AlgebraicGeometry.twistedSheafIsoOfIso`: isomorphic sheaves have isomorphic twists.
* `AlgebraicGeometry.twistedSheafZeroIso`: the twist by the zero exponent vector is the sheaf
  itself.
* `AlgebraicGeometry.twistedSheafUpdateIso`: raising the `i`-th exponent by one tensors the twist
  by `𝓛_i`: `ℱ ⊗ ⋯ 𝓛_i^{⊗ (n_i + 1)} ⋯ ≅ (ℱ ⊗ ⋯ 𝓛_i^{⊗ n_i} ⋯) ⊗ 𝓛_i`.
* `AlgebraicGeometry.finrank_cohomologyOverField_twistedSheaf_update` and
  `AlgebraicGeometry.eulerCharacteristic_twistedSheaf_update`: the cohomology and the Euler
  characteristic of the twist with the `i`-th exponent raised by one are those of the twist
  tensored by `𝓛_i`.
* `AlgebraicGeometry.twistedSheaf_isCoherent_of_tensorSheaf_isCoherent`: every twist of a
  coherent sheaf is coherent, provided tensoring a coherent sheaf by an invertible sheaf is
  coherent.
* `AlgebraicGeometry.exists_eval_eq_eulerCharacteristic_twistedSheaf_of_forall_fwdDiff`: if every
  first difference of the Euler characteristic of the twists is given by a rational polynomial of
  total degree at most `d`, then the Euler characteristic itself is given by one of total degree
  at most `d + 1`.

## References

* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.SheafOfModules.TensorSheafification

universe v u w

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The isomorphism `(M ⊗ A) ⊗ B ≅ (M ⊗ B) ⊗ A`. -/
noncomputable def tensorProductSwapIso
    (M A B : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
        Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj
        (A))))).obj (B)) ≅ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
        Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj (B))))).obj (A)) :=
  tensorProductAssociator O hO M A B ≪≫
    tensorProductIso O hO (Iso.refl M) (tensorProductBraiding O hO A B) ≪≫
    (tensorProductAssociator O hO M B A).symm

/-- The isomorphism `M ⊗ L^{⊗ (n + 1)} ≅ (M ⊗ L^{⊗ n}) ⊗ L`. -/
noncomputable def tensorProductPowerSuccIso
    (M L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] (n : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj ((tensorPower O hO L (n + 1)))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
          (forget₂ CommRingCat RingCat) (hO)⟩).obj (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
          Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj
          ((tensorPower O hO L n)))))).obj (L)) :=
  tensorProductIso O hO (Iso.refl M) (tensorPowerSuccIso O hO L n).symm ≪≫
    (tensorProductAssociator O hO M (tensorPower O hO L n) L).symm

end Stacks.SheafOfModules.Invertible

namespace AlgebraicGeometry

open Stacks.SheafOfModules.Invertible

variable {X : Scheme.{u}} {r : ℕ}

/-- The successive twists of `ℱ` by integer tensor powers of a finite family of invertible
sheaves: `ℱ ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r}`, bracketed from the left and taken in the order of
the index. -/
noncomputable def twistedSheaf (F : X.Modules) (L : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)] (n : Fin r → ℤ) :
    X.Modules :=
  (List.finRange r).foldl
    (fun M i => (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.2)⟩).obj (M)).obj ((tensorPower X.presheaf X.ringCatSheaf.2 (L i)
        (n i))))) F

section TwistList

variable (L : Fin r → X.Modules)
  [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]

/-- The fold defining `AlgebraicGeometry.twistedSheaf`, over an arbitrary list of indices and
starting from an arbitrary sheaf. -/
noncomputable def twistList (e : Fin r → ℤ) (l : List (Fin r)) (M : X.Modules) :
    X.Modules :=
  l.foldl
    (fun M i => (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.2)⟩).obj (M)).obj ((tensorPower X.presheaf X.ringCatSheaf.2 (L i)
        (e i))))) M

/-- The fold of an isomorphism. -/
noncomputable def twistListIso (e : Fin r → ℤ) (l : List (Fin r)) :
    ∀ {M M' : X.Modules}, (M ≅ M') → (twistList L e l M ≅ twistList L e l M') := by
  induction l with
  | nil => exact fun ε => ε
  | cons i t ih => exact fun ε => ih (tensorProductIso X.presheaf X.ringCatSheaf.2 ε (Iso.refl _))

/-- Exponent vectors agreeing on the indices of the list give isomorphic folds. -/
noncomputable def twistListCongrIso {e₁ e₂ : Fin r → ℤ} (l : List (Fin r))
    (h : ∀ i ∈ l, e₁ i = e₂ i) : ∀ M : X.Modules, twistList L e₁ l M ≅ twistList L e₂ l M := by
  induction l with
  | nil => exact fun _ => Iso.refl _
  | cons i t ih =>
    exact fun M =>
      twistListIso L e₁ t (tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl M)
          (tensorPowerReindex X.presheaf X.ringCatSheaf.2 (L i)
            (h i (List.mem_cons_self ..)))) ≪≫
        ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) _

/-- A factor not twisted by the fold passes through it. -/
noncomputable def twistListTensorIso (e : Fin r → ℤ) (l : List (Fin r)) :
    ∀ M A : X.Modules, twistList L e l ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.2)⟩).obj (M)).obj (A))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
          (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩).obj
          ((twistList L e l M))).obj (A)) := by
  induction l with
  | nil => exact fun _ _ => Iso.refl _
  | cons i t ih =>
    exact fun M A => twistListIso L e t (tensorProductSwapIso _ _ M A _) ≪≫ ih _ A

/-- The fold with all exponents zero does nothing. -/
noncomputable def twistListZeroIso (l : List (Fin r)) :
    ∀ M : X.Modules, twistList L 0 l M ≅ M := by
  induction l with
  | nil => exact fun _ => Iso.refl _
  | cons i t ih =>
    exact fun M => ih _ ≪≫ tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 M

/-- If the list of indices has no repetitions and contains `i`, and the two exponent vectors
agree away from `i` while the first exceeds the second by one at `i`, then the first fold is the
second tensored by `𝓛_i`. -/
noncomputable def twistListUpdateIso {e₁ e₂ : Fin r → ℤ} (i : Fin r) (hi : e₁ i = e₂ i + 1) :
    ∀ l : List (Fin r), l.Nodup → i ∈ l → (∀ j ∈ l, j ≠ i → e₁ j = e₂ j) →
      ∀ M : X.Modules, twistList L e₁ l M ≅
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
            (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩).obj
            ((twistList L e₂ l M))).obj ((L i))) := by
  intro l
  induction l with
  | nil => exact fun _ h => absurd h (by simp)
  | cons a t ih =>
    intro hnd hmem hagree M
    by_cases ha : a = i
    · subst ha
      have hat : a ∉ t := (List.nodup_cons.1 hnd).1
      exact twistListCongrIso L t
            (fun j hj => hagree j (List.mem_cons_of_mem _ hj) fun h => hat (h ▸ hj)) _ ≪≫
          twistListIso L e₂ t
            (tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl M)
                (tensorPowerReindex X.presheaf X.ringCatSheaf.2 (L a) hi) ≪≫
              tensorProductPowerSuccIso X.presheaf X.ringCatSheaf.2 M (L a) (e₂ a)) ≪≫
        twistListTensorIso L e₂ t _ (L a)
    · have hat : i ∈ t := by
        rcases List.mem_cons.1 hmem with h | h
        · exact absurd h.symm ha
        · exact h
      exact ih (List.nodup_cons.1 hnd).2 hat
          (fun j hj => hagree j (List.mem_cons_of_mem _ hj)) _ ≪≫
        tensorProductIso X.presheaf X.ringCatSheaf.2
          (twistListIso L e₂ t
            (tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl M)
              (tensorPowerReindex X.presheaf X.ringCatSheaf.2 (L a)
                (hagree a (List.mem_cons_self ..) ha))))
          (Iso.refl (L i))

end TwistList

section Twists

variable (F : X.Modules) (L : Fin r → X.Modules)
  [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]

/-- Isomorphic sheaves have isomorphic twists. -/
noncomputable def twistedSheafIsoOfIso {F F' : X.Modules} (ε : F ≅ F') (n : Fin r → ℤ) :
    twistedSheaf F L n ≅ twistedSheaf F' L n :=
  twistListIso L n (List.finRange r) ε

/-- The twist by the zero exponent vector is the sheaf itself. -/
noncomputable def twistedSheafZeroIso : twistedSheaf F L 0 ≅ F :=
  twistListZeroIso L (List.finRange r) F

/-- Raising the `i`-th exponent by one tensors the twist by `𝓛_i`. -/
noncomputable def twistedSheafUpdateIso (n : Fin r → ℤ) (i : Fin r) :
    twistedSheaf F L (Function.update n i (n i + 1)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
          (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩).obj
          ((twistedSheaf F L n))).obj ((L i))) :=
  twistListUpdateIso L i (Function.update_self ..) (List.finRange r) (List.nodup_finRange r)
    (List.mem_finRange i) (fun _ _ hj => Function.update_of_ne hj _ _) F

/-- If tensoring a coherent sheaf by an invertible sheaf is coherent, then every twist of a
coherent sheaf is coherent. -/
theorem twistedSheaf_isCoherent_of_tensorSheaf_isCoherent [F.IsCoherent] (n : Fin r → ℤ)
    (htensor : ∀ M N : X.Modules, M.IsCoherent →
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N →
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
          (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩).obj (M)).obj
          (N)) : X.Modules).IsCoherent) :
    (twistedSheaf F L n).IsCoherent := by
  have key : ∀ (l : List (Fin r)) (M : X.Modules), M.IsCoherent →
      (twistList L n l M).IsCoherent := by
    intro l
    induction l with
    | nil => exact fun _ hM => hM
    | cons i t ih =>
      exact fun M hM =>
        ih _ (htensor M _ hM
          (tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 (L i) (n i)))
  exact key (List.finRange r) F ‹_›

end Twists

section EulerCharacteristic

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {r : ℕ}
  (F : X.Modules) (L : Fin r → X.Modules)
  [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]

/-- The cohomology of the twist with the `i`-th exponent raised by one has the same dimension
as that of the twist tensored by `𝓛_i`. -/
theorem finrank_cohomologyOverField_twistedSheaf_update (n : Fin r → ℤ) (i : Fin r) (m : ℕ) :
    Module.finrank k (cohomologyOverField k f (twistedSheaf F L (Function.update n i (n i + 1))) m)
      = Module.finrank k (cohomologyOverField k f
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
              Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
              (X.ringCatSheaf.2)⟩).obj ((twistedSheaf F L n))).obj ((L i)))) m) :=
  finrank_cohomologyOverField_eq_of_iso k f (twistedSheafUpdateIso F L n i) m

/-- The Euler characteristic of the twist with the `i`-th exponent raised by one is the Euler
characteristic of the twist tensored by `𝓛_i`. -/
theorem eulerCharacteristic_twistedSheaf_update [IsProper f] (n : Fin r → ℤ) (i : Fin r)
    (h₁ : (twistedSheaf F L (Function.update n i (n i + 1))).IsCoherent)
    (h₂ : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.2)⟩).obj ((twistedSheaf F L n))).obj ((L i))) :
      X.Modules).IsCoherent) :
    @eulerCharacteristic k _ X f _ (twistedSheaf F L (Function.update n i (n i + 1))) h₁ =
      @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
            (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩).obj
            ((twistedSheaf F L n))).obj ((L i)))) h₂ :=
  @eulerCharacteristic_eq_of_iso k _ X f _ _ _ h₁ h₂ (twistedSheafUpdateIso F L n i)

/-- Suppose every twist is coherent and, for each direction `i`, the first difference
`χ(ℱ ⊗ 𝓛^{⊗ (n + e_i)}) - χ(ℱ ⊗ 𝓛^{⊗ n})` is the value at `n` of a rational polynomial `Q i` of
total degree at most `d`. Then the Euler characteristic itself is the value of a rational
polynomial of total degree at most `d + 1`. -/
theorem exists_eval_eq_eulerCharacteristic_twistedSheaf_of_forall_fwdDiff [IsProper f]
    (hcoh : ∀ n : Fin r → ℤ, (twistedSheaf F L n).IsCoherent) (d : ℕ)
    (Q : Fin r → MvPolynomial (Fin r) ℚ) (hdeg : ∀ i, (Q i).totalDegree ≤ d)
    (hQ : ∀ (i : Fin r) (n : Fin r → ℤ),
      MvPolynomial.eval (fun j => (n j : ℚ)) (Q i) =
        (@eulerCharacteristic k _ X f _ (twistedSheaf F L (Function.update n i (n i + 1)))
            (hcoh _) : ℚ) -
          (@eulerCharacteristic k _ X f _ (twistedSheaf F L n) (hcoh n) : ℚ)) :
    ∃ P : MvPolynomial (Fin r) ℚ, P.totalDegree ≤ d + 1 ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
        (@eulerCharacteristic k _ X f _ (twistedSheaf F L n) (hcoh n) : ℚ) :=
  MvPolynomial.exists_totalDegree_le_of_forall_fwdDiff d
    (fun n => (@eulerCharacteristic k _ X f _ (twistedSheaf F L n) (hcoh n) : ℚ)) Q hdeg hQ

end EulerCharacteristic

end AlgebraicGeometry

end
