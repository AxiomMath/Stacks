module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import StacksFrontier.Homology.HomComplex.Basic
public import StacksFrontier.Homology.HomComplex.KoszulBraiding

/-!
# The tensor–Hom currying isomorphism and the closed structure on cochain complexes

Let `R` be a commutative ring and let `K`, `L`, `M` be cochain complexes of `R`-modules indexed
by `ℤ`. Currying degreewise linear maps identifies the iterated Hom complex
`Hom^•(K, Hom^•(L, M))` with the Hom complex `Hom^•(Tot(K ⊗_R L), M)` out of the total tensor
complex: a degree-`n` cochain `α` with components `K^r ⟶ Hom^n(L, M)` transposes to the cochain
whose component on the summand `K^r ⊗ L^s` sends `x ⊗ y` to `α^r(x)(y)`.

This transposition is the adjunction `- ⊗ L ⊣ Hom^•(L, -)`, so it exhibits
`CochainComplex (ModuleCat R) ℤ` as a symmetric monoidal closed category whose internal Hom is
the Hom complex. Mathlib's `MonoidalClosed` curries out of `L ⊗ K` rather than `K ⊗ L`, so the
comparison between the two adjunction maps inserts the Koszul symmetry `K ⊗ L ≅ L ⊗ K`.

## Main definitions

* `Stacks.HomComplex.Currying.curryCochain`, `Stacks.HomComplex.Currying.uncurryCochain`: the
  degreewise transposition maps and their inverse.
* `Stacks.HomComplex.Currying.curryIso`: the currying isomorphism
  `Hom^•(K, Hom^•(L, M)) ≅ Hom^•(Tot(K ⊗ L), M)`.
* `Stacks.HomComplex.MonoidalClosed.homComplexFunctor`: the functor `Hom^•(L, -)`.
* `Stacks.HomComplex.MonoidalClosed.homComplexMonoidalClosed`: the resulting `MonoidalClosed`
  structure on cochain complexes.

## Main results

* `Stacks.HomComplex.Currying.curryIso_hom_apply`: currying sends `x ⊗ y` to evaluation of the
  inner cochain at `y`; this pins the isomorphism down on every degree and every summand.
* `Stacks.HomComplex.Currying.curryIso_naturality_left`,
  `Stacks.HomComplex.Currying.curryIso_naturality_middle`,
  `Stacks.HomComplex.Currying.curryIso_naturality_right`: naturality of the currying isomorphism in
  each of the three complexes.
* `Stacks.HomComplex.MonoidalClosed.cochainComplex_symmetricMonoidalClosed`: cochain complexes of
  `R`-modules form a symmetric monoidal closed category, the Hom complexes with pre- and
  postcomposition form a bifunctor naturally isomorphic to `MonoidalClosed.internalHom`, a
  degree-zero cochain comes from a unique morphism of complexes exactly when its differential
  vanishes, and the closed adjunction agrees with `Stacks.HomComplex.Currying.curryIso` after
  braiding.

## Implementation notes

The Hom complex used throughout is `CochainComplex.HomComplexR`, whose degree-`n` term is
`Cochain L M n`; the total complex of a degreewise tensor product is the monoidal product on
`CochainComplex (ModuleCat R) ℤ`. Since currying is an isomorphism in each degree, the
isomorphism of complexes is assembled with `HomologicalComplex.Hom.isoOfComponents` from the
degreewise linear equivalences, the only real work being commutation with the differentials.

The symmetric structure on cochain complexes is the Koszul braiding, supplied by
`StacksFrontier.Homology.HomComplex.KoszulBraiding` as `CochainComplex.Koszul.koszulSymmetric` (the
source result is Stacks 0FNI); it is not a global instance, so it appears as an existentially
quantified datum in `Stacks.HomComplex.MonoidalClosed.cochainComplex_symmetricMonoidalClosed` and
as a hypothesis in the `Braided` section.

## References

* [Stacks: Tag 0A5Y](https://stacks.math.columbia.edu/tag/0A5Y)
* [Stacks: Tag 0GWQ](https://stacks.math.columbia.edu/tag/0GWQ)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory CochainComplex CochainComplex.HomComplex HomologicalComplex

universe u

namespace Stacks.HomComplex.Currying

variable {R : Type u} [CommRing R]

/-! ## Degreewise currying -/

/-- The transpose of a degree-`n` cochain `α : Hom^n(K, Hom^•(L, M))`: the degree-`n` cochain
out of the total complex `Tot(K ⊗ L)` whose component on the summand `K^r ⊗ L^s` sends `x ⊗ y`
to `α^r(x)(y)`. -/
noncomputable def curryCochainFn (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (α : Cochain K (HomComplexR R L M) n) : Cochain (K ⊗ L) M n :=
  Cochain.mk fun t p htp =>
    GradedObject.Monoidal.tensorObjDesc fun r s hrs =>
      ModuleCat.ofHom <| TensorProduct.lift <| LinearMap.mk₂ R
        (fun x y => (((α.v r (r + n) (by omega)).hom x).v s p (by omega)).hom y)
        (by intros; rw [map_add]; rfl) (by intros; rw [map_smul]; rfl)
        (by intros; simp only [map_add]) (by intros; simp only [map_smul])

/-- The defining formula for `curryCochainFn`: its value on the summand `K^r ⊗ L^s` of
`Tot^t(K ⊗ L)` is `x ⊗ y ↦ α^r(x)(y)`. -/
lemma curryCochainFn_apply (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n r s t p : ℤ)
    (hrs : r + s = t) (htp : t + n = p)
    (α : Cochain K (HomComplexR R L M) n) (x : K.X r) (y : L.X s) :
    (((curryCochainFn K L M n α).v t p htp).hom ((ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y))) =
      (((α.v r (r + n) (by omega)).hom x).v s p (by omega)).hom y := by
  let f := fun (r s : ℤ) (hrs : r + s = t) =>
    ModuleCat.ofHom <| TensorProduct.lift <| LinearMap.mk₂ R
      (fun x y => (((α.v r (r + n) (by omega)).hom x).v s p (by omega)).hom y)
      (by intros; rw [map_add]; rfl) (by intros; rw [map_smul]; rfl)
      (by intros; simp only [map_add]) (by intros; simp only [map_smul])
  have hι : ιTensorObj K L r s t hrs ≫ GradedObject.Monoidal.tensorObjDesc f = f r s hrs :=
    GradedObject.Monoidal.ι_tensorObjDesc f r s hrs
  change ((ιTensorObj K L r s t hrs ≫ GradedObject.Monoidal.tensorObjDesc f).hom
    (x ⊗ₜ[R] y)) = _
  rw [hι]
  rfl

/-- Two cochains out of `Tot(K ⊗ L)` agree if they agree on every pure tensor of every summand. -/
private theorem cochain_tensor_ext {K L M : CochainComplex (ModuleCat.{u} R) ℤ} {n : ℤ}
    {f g : Cochain (K ⊗ L) M n}
    (h : ∀ (r s t p : ℤ) (hrs : r + s = t) (htp : t + n = p) (x : K.X r) (y : L.X s),
      ((f.v t p htp).hom ((ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y))) =
        ((g.v t p htp).hom ((ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y)))) : f = g := by
  apply Cochain.ext; intro t p htp
  apply mapBifunctor.hom_ext; intro r s hrs
  change r + s = t at hrs
  apply ModuleCat.hom_ext; apply TensorProduct.ext'; intro x y
  exact h r s t p hrs htp x y

/-- Degreewise currying `Hom^n(K, Hom^•(L, M)) → Hom^n(Tot(K ⊗ L), M)`, as an `R`-linear map. -/
noncomputable def curryCochain (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Cochain K (HomComplexR R L M) n →ₗ[R] Cochain (K ⊗ L) M n where
  toFun := curryCochainFn K L M n
  map_add' α β := by
    apply Cochain.ext; intro t p htp
    apply mapBifunctor.hom_ext; intro r s hrs
    change r + s = t at hrs
    apply ModuleCat.hom_ext; apply TensorProduct.ext'; intro x y
    change (((curryCochainFn K L M n (α + β)).v t p htp).hom
      ((ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y))) =
      (((curryCochainFn K L M n α).v t p htp).hom
        ((ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y))) +
      (((curryCochainFn K L M n β).v t p htp).hom
        ((ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y)))
    rw [curryCochainFn_apply, curryCochainFn_apply, curryCochainFn_apply]
    rfl
  map_smul' a α := by
    apply Cochain.ext; intro t p htp
    apply mapBifunctor.hom_ext; intro r s hrs
    change r + s = t at hrs
    apply ModuleCat.hom_ext; apply TensorProduct.ext'; intro x y
    change (((curryCochainFn K L M n (a • α)).v t p htp).hom
      ((ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y))) =
      a • (((curryCochainFn K L M n α).v t p htp).hom
        ((ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y)))
    rw [curryCochainFn_apply, curryCochainFn_apply]
    rfl

/-- Degreewise currying evaluated on the summand `K^r ⊗ L^s` of `Tot^t(K ⊗ L)`. -/
lemma curryCochain_apply (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n r s t p : ℤ)
    (hrs : r + s = t) (htp : t + n = p)
    (α : Cochain K (HomComplexR R L M) n) (x : K.X r) (y : L.X s) :
    (((curryCochain K L M n α).v t p htp).hom ((ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y))) =
      (((α.v r (r + n) (by omega)).hom x).v s p (by omega)).hom y :=
  curryCochainFn_apply K L M n r s t p hrs htp α x y

/-- The same component formula with the intermediate degree `q = r + n` named. -/
lemma curryCochain_apply_degree (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n r s t p q : ℤ)
    (hrs : r + s = t) (htp : t + n = p) (hrq : r + n = q)
    (α : Cochain K (HomComplexR R L M) n) (x : K.X r) (y : L.X s) :
    ((curryCochain K L M n α).v t p htp).hom ((ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y)) =
      (((α.v r q hrq).hom x).v s p (by omega)).hom y := by
  subst q
  exact curryCochain_apply K L M n r s t p hrs htp α x y

/-- The transpose of a degree-`n` cochain out of the total complex: its component at `r` sends
`x ∈ K^r` to the cochain `y ↦ β(x ⊗ y)`. -/
noncomputable def uncurryCochainFn (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (β : Cochain (K ⊗ L) M n) : Cochain K (HomComplexR R L M) n :=
  Cochain.mk fun r q hrq => ModuleCat.ofHom
    { toFun := fun x => Cochain.mk fun s p hsp => ModuleCat.ofHom
        ((β.v (r + s) p (by omega)).hom.comp
          ((ιTensorObj K L r s (r + s) rfl).hom.comp (TensorProduct.mk R _ _ x)))
      map_add' := by
        intro x y; apply Cochain.ext; intro s p hsp
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro z
        change ((β.v (r + s) p _).hom
          ((ιTensorObj K L r s (r + s) rfl).hom ((x + y) ⊗ₜ[R] z))) =
          ((β.v (r + s) p _).hom ((ιTensorObj K L r s (r + s) rfl).hom (x ⊗ₜ[R] z))) +
          ((β.v (r + s) p _).hom ((ιTensorObj K L r s (r + s) rfl).hom (y ⊗ₜ[R] z)))
        rw [TensorProduct.add_tmul, map_add, map_add]
      map_smul' := by
        intro a x; apply Cochain.ext; intro s p hsp
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro z
        change ((β.v (r + s) p _).hom
          ((ιTensorObj K L r s (r + s) rfl).hom ((a • x) ⊗ₜ[R] z))) =
          a • ((β.v (r + s) p _).hom
            ((ιTensorObj K L r s (r + s) rfl).hom (x ⊗ₜ[R] z)))
        rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul, map_smul] }

/-- The defining formula for `uncurryCochainFn`: its value at `r` sends `x` to the cochain
`y ↦ β(x ⊗ y)`. -/
lemma uncurryCochainFn_apply (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n r s q p : ℤ)
    (hrq : r + n = q) (hsp : s + q = p)
    (β : Cochain (K ⊗ L) M n) (x : K.X r) (y : L.X s) :
    (((((uncurryCochainFn K L M n β).v r q hrq).hom x).v s p hsp).hom y) =
      ((β.v (r + s) p (by omega)).hom
        ((ιTensorObj K L r s (r + s) rfl).hom (x ⊗ₜ[R] y))) := rfl

/-- Degreewise uncurrying `Hom^n(Tot(K ⊗ L), M) → Hom^n(K, Hom^•(L, M))`, as an `R`-linear
map. -/
noncomputable def uncurryCochain (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Cochain (K ⊗ L) M n →ₗ[R] Cochain K (HomComplexR R L M) n where
  toFun := uncurryCochainFn K L M n
  map_add' α β := by
    apply Cochain.ext; intro r q hrq
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
    apply Cochain.ext; intro s p hsp
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro y
    change (((((uncurryCochainFn K L M n (α + β)).v r q hrq).hom x).v s p hsp).hom y) =
      (((((uncurryCochainFn K L M n α).v r q hrq).hom x).v s p hsp).hom y) +
      (((((uncurryCochainFn K L M n β).v r q hrq).hom x).v s p hsp).hom y)
    rw [uncurryCochainFn_apply, uncurryCochainFn_apply, uncurryCochainFn_apply]
    rfl
  map_smul' a α := by
    apply Cochain.ext; intro r q hrq
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
    apply Cochain.ext; intro s p hsp
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro y
    change (((((uncurryCochainFn K L M n (a • α)).v r q hrq).hom x).v s p hsp).hom y) =
      a • (((((uncurryCochainFn K L M n α).v r q hrq).hom x).v s p hsp).hom y)
    rw [uncurryCochainFn_apply, uncurryCochainFn_apply]
    rfl

/-- Degreewise uncurrying evaluated on a pure tensor. -/
lemma uncurryCochain_apply (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n r s q p : ℤ)
    (hrq : r + n = q) (hsp : s + q = p)
    (β : Cochain (K ⊗ L) M n) (x : K.X r) (y : L.X s) :
    (((((uncurryCochain K L M n β).v r q hrq).hom x).v s p hsp).hom y) =
      ((β.v (r + s) p (by omega)).hom
        ((ιTensorObj K L r s (r + s) rfl).hom (x ⊗ₜ[R] y))) :=
  uncurryCochainFn_apply K L M n r s q p hrq hsp β x y

/-- Currying and uncurrying are mutually inverse in each degree. -/
noncomputable def cochainCurryEquiv (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Cochain K (HomComplexR R L M) n ≃ₗ[R] Cochain (K ⊗ L) M n where
  toLinearMap := curryCochain K L M n
  invFun := uncurryCochain K L M n
  left_inv α := by
    apply Cochain.ext; intro r q hrq
    subst q
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
    apply Cochain.ext; intro s p hsp
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro y
    rw [uncurryCochain_apply]
    change (((curryCochainFn K L M n α).v (r + s) p _).hom
      ((ιTensorObj K L r s (r + s) rfl).hom (x ⊗ₜ[R] y))) = _
    rw [curryCochainFn_apply]
  right_inv β := by
    apply Cochain.ext; intro t p htp
    apply mapBifunctor.hom_ext; intro r s hrs
    change r + s = t at hrs
    apply ModuleCat.hom_ext; apply TensorProduct.ext'; intro x y
    change (((curryCochain K L M n (uncurryCochain K L M n β)).v t p htp).hom
      ((ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y))) = _
    rw [curryCochain_apply, uncurryCochain_apply]
    subst t
    rfl

/-! ## Compatibility with the differentials -/

/-- The value of `δ` on a homogeneous element, with the intermediate degree named. -/
lemma delta_v_apply (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n m : ℤ) (hnm : n + 1 = m)
    (α : Cochain K L n) (p q a : ℤ) (hpq : p + m = q) (ha : a = q - 1) (x : K.X p) :
    ((δ n m α).v p q hpq).hom x =
      (L.d a q).hom ((α.v p a (by omega)).hom x) +
        m.negOnePow • ((α.v (p + 1) q (by omega)).hom ((K.d p (p + 1)).hom x)) := by
  rw [δ_v n m hnm α p q hpq a (p + 1) ha rfl]
  rfl

/-- The differential of the total complex on a pure tensor in the summand `K^r ⊗ L^s`. -/
lemma tensor_d_apply (K L : CochainComplex (ModuleCat.{u} R) ℤ) (r s t : ℤ) (hrs : r + s = t)
    (x : K.X r) (y : L.X s) :
    ((K ⊗ L).d t (t + 1)).hom ((ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y)) =
      (ιTensorObj K L (r + 1) s (t + 1) (by omega)).hom (((K.d r (r + 1)).hom x) ⊗ₜ[R] y) +
      r.negOnePow • (ιTensorObj K L r (s + 1) (t + 1) (by omega)).hom
        (x ⊗ₜ[R] ((L.d s (s + 1)).hom y)) := by
  have h := congrArg (fun f => f.hom (x ⊗ₜ[R] y))
    (CochainComplex.ιTensorObj_d R K L r s t (t + 1) hrs rfl)
  simp only [Units.smul_def, ModuleCat.Hom.hom, ModuleCat.hom_comp, ModuleCat.hom_add,
    ModuleCat.hom_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.coe_comp,
    Function.comp_apply, ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply] at h ⊢
  convert h using 1 <;> rfl

/-- Currying commutes with the Hom-complex differentials. -/
lemma curryCochain_comm (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n m : ℤ)
    (h : (ComplexShape.up ℤ).Rel n m) :
    ModuleCat.ofHom (curryCochain K L M n) ≫ (HomComplexR R (K ⊗ L) M).d n m =
      (HomComplexR R K (HomComplexR R L M)).d n m ≫ ModuleCat.ofHom (curryCochain K L M m) := by
  rw [show m = n + 1 by simpa using h.symm]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  change δ n (n + 1) (curryCochain K L M n α) = curryCochain K L M (n + 1) (δ n (n + 1) α)
  refine cochain_tensor_ext fun r s t p hrs htp x y => ?_
  rw [delta_v_apply _ _ _ _ rfl _ _ _ (p - 1) _ rfl, tensor_d_apply]
  simp only [Units.smul_def, map_add, map_zsmul]
  rw [curryCochain_apply_degree K L M n r s t (p - 1) (r + n) hrs (by omega) rfl,
    curryCochain_apply_degree K L M n (r + 1) s (t + 1) p (r + (n + 1))
      (by omega) (by omega) (by omega),
    curryCochain_apply_degree K L M n r (s + 1) (t + 1) p (r + n)
      (by omega) (by omega) rfl,
    curryCochain_apply]
  rw [delta_v_apply _ _ _ _ rfl _ _ _ (r + n) _ (by omega)]
  change _ =
    ((δ (r + n) (r + (n + 1)) ((α.v r (r + n) (by omega)).hom x)).v s p (by omega)).hom y +
      (n + 1).negOnePow •
        (((α.v (r + 1) (r + (n + 1)) (by omega)).hom
          ((K.d r (r + 1)).hom x)).v s p (by omega)).hom y
  rw [delta_v_apply _ _ _ _ (by omega) _ _ _ (p - 1) _ rfl]
  simp only [Units.smul_def, smul_add, smul_smul, Int.negOnePow_add, Units.val_mul]
  simp only [mul_comm, mul_left_comm]
  abel

/-! ## The currying isomorphism -/

/-- **Stacks 0A5Y**.
The canonical tensor–Hom currying isomorphism of complexes of `R`-modules
`Hom^•(K, Hom^•(L, M)) ≅ Hom^•(Tot(K ⊗_R L), M)`, given in each degree by transposing a
degreewise linear map. -/
@[stacks 0A5Y]
noncomputable def curryIso (K L M : CochainComplex (ModuleCat.{u} R) ℤ) :
    HomComplexR R K (HomComplexR R L M) ≅ HomComplexR R (K ⊗ L) M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (cochainCurryEquiv K L M n).toModuleIso)
    (fun _ _ h => curryCochain_comm K L M _ _ h)

/-- The degree-`n` component of the currying isomorphism is degreewise currying. -/
@[simp] lemma curryIso_hom_f (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (curryIso K L M).hom.f n = ModuleCat.ofHom (curryCochain K L M n) := rfl

/-- **Stacks 0A5Y**.
The currying isomorphism sends a cochain `α` to the cochain whose value on the summand
`K^r ⊗ L^s` of `Tot^t(K ⊗ L)` is `x ⊗ y ↦ α^r(x)(y)`. This determines it in every degree and on
every summand. -/
@[stacks 0A5Y]
lemma curryIso_hom_apply (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n r s t p : ℤ)
    (hrs : r + s = t) (htp : t + n = p)
    (α : Cochain K (HomComplexR R L M) n) (x : K.X r) (y : L.X s) :
    ((((curryIso K L M).hom.f n).hom α).v t p htp).hom
        ((ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y)) =
      (((α.v r (r + n) (by omega)).hom x).v s p (by omega)).hom y :=
  curryCochain_apply K L M n r s t p hrs htp α x y

/-! ## Naturality -/

/-- The `(p, q)` component of `g^* z` is `g^p` followed by the `(p, q)` component of `z`. -/
lemma precomp_v {K K' L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K' ⟶ K) (n : ℤ)
    (z : Cochain K L n) (p q : ℤ) (hpq : p + n = q) :
    (((Stacks.HomComplex.TensorHomMap.precomp R K' K L f).f n).hom z).v p q hpq = f.f p ≫ z.v p q
      hpq := by
  rw [Stacks.HomComplex.TensorHomMap.precomp_f_apply,
    Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq, Cochain.ofHom_v]

/-- The `(p, q)` component of `h_* z` is the `(p, q)` component of `z` followed by `h^q`. -/
lemma postcomp_v {K L L' : CochainComplex (ModuleCat.{u} R) ℤ} (f : L ⟶ L') (n : ℤ)
    (z : Cochain K L n) (p q : ℤ) (hpq : p + n = q) :
    (((Stacks.HomComplex.TensorHomMap.postcomp R K L L' f).f n).hom z).v p q hpq = z.v p q hpq ≫ f.f
      q := by
  rw [Stacks.HomComplex.TensorHomMap.postcomp_f_apply,
    Cochain.comp_v _ _ (add_zero n) p q q hpq (add_zero q), Cochain.ofHom_v]

/-- On the summand `K'^r ⊗ L^s`, the morphism `f ▷ L` of total complexes restricts to
`f^r ▷ L^s`. This is `CochainComplex.ιTensorObj_tensorHom` for `f ⊗ₘ 𝟙 L`. -/
lemma ιTensorObj_comp_whiskerRight {K K' L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K' ⟶ K)
    (r s t : ℤ) (hrs : r + s = t) :
    ιTensorObj K' L r s t hrs ≫ (f ▷ L).f t
      = (f.f r ▷ L.X s) ≫ ιTensorObj K L r s t hrs := by
  rw [← tensorHom_id f L, CochainComplex.ιTensorObj_tensorHom, HomologicalComplex.id_f,
    tensorHom_id]

/-- On the summand `K^r ⊗ L'^s`, the morphism `K ◁ f` of total complexes restricts to
`K^r ◁ f^s`. This is `CochainComplex.ιTensorObj_tensorHom` for `𝟙 K ⊗ₘ f`. -/
lemma ιTensorObj_comp_whiskerLeft (K : CochainComplex (ModuleCat.{u} R) ℤ)
    {L L' : CochainComplex (ModuleCat.{u} R) ℤ} (f : L' ⟶ L)
    (r s t : ℤ) (hrs : r + s = t) :
    ιTensorObj K L' r s t hrs ≫ (K ◁ f).f t
      = (K.X r ◁ f.f s) ≫ ιTensorObj K L r s t hrs := by
  rw [← id_tensorHom K f, CochainComplex.ιTensorObj_tensorHom, HomologicalComplex.id_f,
    id_tensorHom]

/-- The morphism `f ▷ L` of total complexes on a pure tensor in the summand `K'^r ⊗ L^s`. -/
lemma tensor_whiskerRight_apply {K K' L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K' ⟶ K)
    (r s t : ℤ) (hrs : r + s = t) (x : K'.X r) (y : L.X s) :
    ((f ▷ L).f t).hom ((ιTensorObj K' L r s t hrs).hom (x ⊗ₜ[R] y)) =
      (ιTensorObj K L r s t hrs).hom (((f.f r).hom x) ⊗ₜ[R] y) := by
  have h := congrArg (fun g => g.hom (x ⊗ₜ[R] y))
    (ιTensorObj_comp_whiskerRight f r s t hrs)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply] at h
  convert h using 1 <;> rfl

/-- The morphism `K ◁ f` of total complexes on a pure tensor in the summand `K^r ⊗ L'^s`. -/
lemma tensor_whiskerLeft_apply {K L L' : CochainComplex (ModuleCat.{u} R) ℤ} (f : L' ⟶ L)
    (r s t : ℤ) (hrs : r + s = t) (x : K.X r) (y : L'.X s) :
    ((K ◁ f).f t).hom ((ιTensorObj K L' r s t hrs).hom (x ⊗ₜ[R] y)) =
      (ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] ((f.f s).hom y)) := by
  have h := congrArg (fun g => g.hom (x ⊗ₜ[R] y))
    (ιTensorObj_comp_whiskerLeft K f r s t hrs)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply] at h
  convert h using 1 <;> rfl

/-- **Stacks 0A5Y**.
Currying is contravariantly natural in the first complex: precomposing with `f : K' ⟶ K` inside
the iterated Hom complex corresponds to precomposing with `f ▷ L` on the total complex. -/
@[stacks 0A5Y]
lemma curryIso_naturality_left {K K' L M : CochainComplex (ModuleCat.{u} R) ℤ} (f : K' ⟶ K) :
    Stacks.HomComplex.TensorHomMap.precomp R K' K (HomComplexR R L M) f ≫ (curryIso K' L M).hom =
      (curryIso K L M).hom ≫ Stacks.HomComplex.TensorHomMap.precomp R (K' ⊗ L) (K ⊗ L) M (f ▷ L) :=
        by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  change curryCochain K' L M n
      (((Stacks.HomComplex.TensorHomMap.precomp R K' K (HomComplexR R L M) f).f n).hom α) =
    ((Stacks.HomComplex.TensorHomMap.precomp R (K' ⊗ L) (K ⊗ L) M (f ▷ L)).f n).hom (curryCochain K
      L M n α)
  refine cochain_tensor_ext fun r s t p hrs htp x y => ?_
  rw [curryCochain_apply, precomp_v, precomp_v]
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    tensor_whiskerRight_apply, curryCochain_apply]

/-- **Stacks 0A5Y**.
Currying is contravariantly natural in the middle complex: precomposing the inner Hom complex
with `f : L' ⟶ L` corresponds to precomposing with `K ◁ f` on the total complex. -/
@[stacks 0A5Y]
lemma curryIso_naturality_middle {K L L' M : CochainComplex (ModuleCat.{u} R) ℤ} (f : L' ⟶ L) :
    Stacks.HomComplex.TensorHomMap.postcomp R K (HomComplexR R L M) (HomComplexR R L' M)
        (Stacks.HomComplex.TensorHomMap.precomp R L' L M f) ≫ (curryIso K L' M).hom =
      (curryIso K L M).hom ≫ Stacks.HomComplex.TensorHomMap.precomp R (K ⊗ L') (K ⊗ L) M (K ◁ f) :=
        by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  change curryCochain K L' M n
      (((Stacks.HomComplex.TensorHomMap.postcomp R K (HomComplexR R L M) (HomComplexR R L' M)
        (Stacks.HomComplex.TensorHomMap.precomp R L' L M f)).f n).hom α) =
    ((Stacks.HomComplex.TensorHomMap.precomp R (K ⊗ L') (K ⊗ L) M (K ◁ f)).f n).hom (curryCochain K
      L M n α)
  refine cochain_tensor_ext fun r s t p hrs htp x y => ?_
  rw [curryCochain_apply, postcomp_v, precomp_v]
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rw [precomp_v]
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    tensor_whiskerLeft_apply, curryCochain_apply]

/-- **Stacks 0A5Y**.
Currying is covariantly natural in the target complex. -/
@[stacks 0A5Y]
lemma curryIso_naturality_right {K L M M' : CochainComplex (ModuleCat.{u} R) ℤ} (f : M ⟶ M') :
    Stacks.HomComplex.TensorHomMap.postcomp R K (HomComplexR R L M) (HomComplexR R L M')
        (Stacks.HomComplex.TensorHomMap.postcomp R L M M' f) ≫ (curryIso K L M').hom =
      (curryIso K L M).hom ≫ Stacks.HomComplex.TensorHomMap.postcomp R (K ⊗ L) M M' f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  change curryCochain K L M' n
      (((Stacks.HomComplex.TensorHomMap.postcomp R K (HomComplexR R L M) (HomComplexR R L M')
        (Stacks.HomComplex.TensorHomMap.postcomp R L M M' f)).f n).hom α) =
    ((Stacks.HomComplex.TensorHomMap.postcomp R (K ⊗ L) M M' f).f n).hom (curryCochain K L M n α)
  refine cochain_tensor_ext fun r s t p hrs htp x y => ?_
  rw [curryCochain_apply, postcomp_v, postcomp_v]
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rw [postcomp_v]
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, curryCochain_apply]

end Stacks.HomComplex.Currying

namespace Stacks.HomComplex.MonoidalClosed

section

variable {R : Type u} [CommRing R]

/-! ## The Hom complex as an internal Hom -/

/-- The functor `Hom^•(L, -)` on cochain complexes, acting on morphisms by postcomposition. -/
noncomputable def homComplexFunctor (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj M := HomComplexR R L M
  map f := Stacks.HomComplex.TensorHomMap.postcomp R L _ _ f
  map_id M := by
    ext n z
    change z.comp (Cochain.ofHom (𝟙 M)) (add_zero n) = z
    exact Cochain.comp_id z
  map_comp f g := by
    ext n z
    change z.comp (Cochain.ofHom (f ≫ g)) (add_zero n) =
      (z.comp (Cochain.ofHom f) (add_zero n)).comp (Cochain.ofHom g) (add_zero n)
    rw [Cochain.ofHom_comp]
    exact (Cochain.comp_assoc_of_second_is_zero_cochain _ _ _ _).symm

/-- A morphism of Hom complexes carries a morphism of complexes `A ⟶ B` to a morphism
`A' ⟶ B'`: it sends the degree-zero cocycle `Cochain.ofHom g` to a degree-zero cocycle, because
a morphism of complexes commutes with `δ`. -/
noncomputable def homMap {A B A' B' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : HomComplexR R A B ⟶ HomComplexR R A' B') (g : A ⟶ B) : A' ⟶ B' :=
  Cocycle.homOf (Cocycle.mk ((f.f 0).hom (Cochain.ofHom g)) 1 rfl (by
    have h := congrArg (fun k => k.hom (Cochain.ofHom g)) (f.comm 0 1)
    change δ 0 1 ((f.f 0).hom (Cochain.ofHom g)) = 0
    change δ 0 1 ((f.f 0).hom (Cochain.ofHom g)) =
      (f.f 1).hom (δ 0 1 (Cochain.ofHom g)) at h
    simpa only [δ_ofHom, map_zero] using h))

/-- The cochain of `homMap f g` is the image under `f` of the cochain of `g`. -/
lemma ofHom_homMap {A B A' B' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : HomComplexR R A B ⟶ HomComplexR R A' B') (g : A ⟶ B) :
    Cochain.ofHom (homMap f g) = (f.f 0).hom (Cochain.ofHom g) := by
  simp only [homMap, Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.mk_coe]

/-- An isomorphism of Hom complexes induces a bijection on morphisms of complexes. -/
noncomputable def homEquiv {A B A' B' : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : HomComplexR R A B ≅ HomComplexR R A' B') : (A ⟶ B) ≃ (A' ⟶ B') where
  toFun := homMap e.hom
  invFun := homMap e.inv
  left_inv g := Cochain.ofHom_injective <| by
    rw [ofHom_homMap, ofHom_homMap]
    exact congrArg (fun f => (f.f 0).hom (Cochain.ofHom g)) e.hom_inv_id
  right_inv g := Cochain.ofHom_injective <| by
    rw [ofHom_homMap, ofHom_homMap]
    exact congrArg (fun f => (f.f 0).hom (Cochain.ofHom g)) e.inv_hom_id

/-- The tensor–Hom adjunction bijection `(K ⟶ Hom^•(L, M)) ≃ (Tot(K ⊗ L) ⟶ M)`, induced by the
currying isomorphism of Stacks 0A5Y. -/
noncomputable abbrev tensorHomEquiv (K L M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (K ⟶ HomComplexR R L M) ≃ (K ⊗ L ⟶ M) :=
  homEquiv (Stacks.HomComplex.Currying.curryIso K L M)

/-- The cochain of the transpose of `g` is the currying isomorphism applied to the cochain
of `g`. -/
lemma ofHom_tensorHomEquiv (K L M : CochainComplex (ModuleCat.{u} R) ℤ)
    (g : K ⟶ HomComplexR R L M) :
    Cochain.ofHom (tensorHomEquiv K L M g) =
      ((Stacks.HomComplex.Currying.curryIso K L M).hom.f 0).hom (Cochain.ofHom g) :=
  ofHom_homMap _ _

/-- Precomposition acts on degree-zero cochains of morphisms by composition. -/
lemma precomp_ofHom {A B C : CochainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B) (g : B ⟶ C) :
    ((Stacks.HomComplex.TensorHomMap.precomp R A B C f).f 0).hom (Cochain.ofHom g) = Cochain.ofHom
      (f ≫ g) :=
  (Cochain.ofHom_comp f g).symm

/-- Postcomposition acts on degree-zero cochains of morphisms by composition. -/
lemma postcomp_ofHom {A B C : CochainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B) (g : B ⟶ C) :
    ((Stacks.HomComplex.TensorHomMap.postcomp R A B C g).f 0).hom (Cochain.ofHom f) = Cochain.ofHom
      (f ≫ g) :=
  (Cochain.ofHom_comp f g).symm

/-- The transpose bijection is natural in the source complex. -/
lemma tensorHomEquiv_naturality_left {K K' L M : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K' ⟶ K) (g : K ⟶ HomComplexR R L M) :
    tensorHomEquiv K' L M (f ≫ g) = f ▷ L ≫ tensorHomEquiv K L M g := Cochain.ofHom_injective <| by
  rw [ofHom_tensorHomEquiv, ← precomp_ofHom f g,
    ← precomp_ofHom (f ▷ L) (tensorHomEquiv K L M g), ofHom_tensorHomEquiv]
  exact congrArg (fun k => (k.f 0).hom (Cochain.ofHom g))
    (Stacks.HomComplex.Currying.curryIso_naturality_left f)

/-- The transpose bijection is natural in the target complex. -/
lemma tensorHomEquiv_naturality_right {K L M M' : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : K ⟶ HomComplexR R L M) (f : M ⟶ M') :
    tensorHomEquiv K L M' (g ≫ Stacks.HomComplex.TensorHomMap.postcomp R L M M' f) =
      tensorHomEquiv K L M g ≫ f := Cochain.ofHom_injective <| by
  rw [ofHom_tensorHomEquiv, ← postcomp_ofHom g,
    ← postcomp_ofHom (tensorHomEquiv K L M g) f, ofHom_tensorHomEquiv]
  exact congrArg (fun k => (k.f 0).hom (Cochain.ofHom g))
    (Stacks.HomComplex.Currying.curryIso_naturality_right f)

/-- The transpose bijection is natural in the complex being Hom'd out of. -/
lemma tensorHomEquiv_naturality_middle {K L L' M : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : K ⟶ HomComplexR R L M) (f : L' ⟶ L) :
    tensorHomEquiv K L' M (g ≫ Stacks.HomComplex.TensorHomMap.precomp R L' L M f) =
      K ◁ f ≫ tensorHomEquiv K L M g := Cochain.ofHom_injective <| by
  rw [ofHom_tensorHomEquiv, ← postcomp_ofHom g,
    ← precomp_ofHom (K ◁ f) (tensorHomEquiv K L M g), ofHom_tensorHomEquiv]
  exact congrArg (fun k => (k.f 0).hom (Cochain.ofHom g))
    (Stacks.HomComplex.Currying.curryIso_naturality_middle f)

/-! ## The closed structure

Mathlib's `MonoidalClosed` curries out of `L ⊗ K`, so passing from the tensor–Hom transpose of
Stacks 0A5Y to the closed structure requires a braiding. -/

section Braided

variable [BraidedCategory (CochainComplex (ModuleCat.{u} R) ℤ)]

/-- The adjunction bijection `(L ⊗ K ⟶ M) ≃ (K ⟶ Hom^•(L, M))` in Mathlib's convention: braid,
then untranspose. -/
noncomputable def closedHomEquiv (K L M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (L ⊗ K ⟶ M) ≃ (K ⟶ HomComplexR R L M) :=
  (β_ K L).symm.homFromEquiv.trans (tensorHomEquiv K L M).symm

/-- The inverse of `closedHomEquiv` is the braiding followed by the transpose. -/
lemma closedHomEquiv_symm_apply (K L M : CochainComplex (ModuleCat.{u} R) ℤ)
    (g : K ⟶ HomComplexR R L M) :
    (closedHomEquiv K L M).symm g = (β_ K L).inv ≫ tensorHomEquiv K L M g := rfl

/-- Naturality of `closedHomEquiv⁻¹` in the source complex. -/
lemma closedHomEquiv_naturality_left_symm {K K' L M : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K' ⟶ K) (g : K ⟶ HomComplexR R L M) :
    (closedHomEquiv K' L M).symm (f ≫ g) = L ◁ f ≫ (closedHomEquiv K L M).symm g := by
  simp only [closedHomEquiv_symm_apply, tensorHomEquiv_naturality_left]
  rw [BraidedCategory.braiding_inv_naturality_right_assoc]

/-- Naturality of `closedHomEquiv⁻¹` in the target complex. -/
lemma closedHomEquiv_naturality_right_symm {K L M M' : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : K ⟶ HomComplexR R L M) (f : M ⟶ M') :
    (closedHomEquiv K L M').symm (g ≫ Stacks.HomComplex.TensorHomMap.postcomp R L M M' f) =
      (closedHomEquiv K L M).symm g ≫ f := by
  simp only [closedHomEquiv_symm_apply, tensorHomEquiv_naturality_right, Category.assoc]

/-- The adjunction `L ⊗ - ⊣ Hom^•(L, -)`. -/
noncomputable def homComplexAdjunction (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorLeft L ⊣ homComplexFunctor L :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun K M => closedHomEquiv K L M
      homEquiv_naturality_left_symm := closedHomEquiv_naturality_left_symm
      homEquiv_naturality_right := by
        intro K M M' g f
        change L ⊗ K ⟶ M at g
        change closedHomEquiv K L M' (g ≫ f) =
          closedHomEquiv K L M g ≫ Stacks.HomComplex.TensorHomMap.postcomp R L M M' f
        apply (closedHomEquiv K L M').symm.injective
        rw [Equiv.symm_apply_apply, closedHomEquiv_naturality_right_symm,
          Equiv.symm_apply_apply] }

/-- Cochain complexes of `R`-modules are monoidal closed, with internal Hom the Hom complex. -/
@[instance_reducible]
noncomputable def homComplexMonoidalClosed :
    MonoidalClosed (CochainComplex (ModuleCat.{u} R) ℤ) where
  closed L := { rightAdj := homComplexFunctor L, adj := homComplexAdjunction L }

/-- Uncurrying in the closed structure is the braiding followed by the transpose of 0A5Y. -/
lemma homComplex_uncurry {K L M : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : K ⟶ HomComplexR R L M) :
    letI := homComplexMonoidalClosed (R := R)
    MonoidalClosed.uncurry g = (β_ K L).inv ≫ tensorHomEquiv K L M g := by
  change ((homComplexAdjunction L).homEquiv K M).symm g = _
  rw [homComplexAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact closedHomEquiv_symm_apply K L M g

/-- Uncurrying is compatible with precomposition in the Hom'd-out variable. -/
lemma homComplex_uncurry_precomp {K L L' M : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : K ⟶ HomComplexR R L M) (f : L' ⟶ L) :
    letI := homComplexMonoidalClosed (R := R)
    MonoidalClosed.uncurry (g ≫ Stacks.HomComplex.TensorHomMap.precomp R L' L M f) =
      f ▷ K ≫ MonoidalClosed.uncurry g := by
  rw [homComplex_uncurry, homComplex_uncurry, tensorHomEquiv_naturality_middle,
    BraidedCategory.braiding_inv_naturality_left_assoc]

/-- The structural map `MonoidalClosed.pre` of the closed structure is precomposition. -/
lemma homComplex_pre {L L' M : CochainComplex (ModuleCat.{u} R) ℤ} (f : L' ⟶ L) :
    letI := homComplexMonoidalClosed (R := R)
    (MonoidalClosed.pre f).app M = Stacks.HomComplex.TensorHomMap.precomp R L' L M f := by
  let := homComplexMonoidalClosed (R := R)
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre]
  have h := homComplex_uncurry_precomp (𝟙 (HomComplexR R L M)) f
  change MonoidalClosed.uncurry (Stacks.HomComplex.TensorHomMap.precomp R L' L M f) =
    f ▷ (ihom L).obj M ≫ MonoidalClosed.uncurry (𝟙 ((ihom L).obj M)) at h
  rw [MonoidalClosed.uncurry_id_eq_ev] at h
  exact h.symm

end Braided

end

/-- **Stacks 0GWQ**.
Cochain complexes of modules over a commutative ring form a symmetric monoidal closed category.
The concrete Hom complexes, with pre- and postcomposition on morphisms, form a bifunctor
naturally isomorphic to the internal Hom bifunctor. Under this isomorphism, the closed-structure
adjunction, after applying the symmetry `K ⊗ L ≅ L ⊗ K`, is the canonical currying isomorphism of
Hom complexes. Moreover, a degree-zero cochain is the cochain of a unique morphism of complexes
if and only if its differential vanishes. -/
@[stacks 0GWQ]
theorem cochainComplex_symmetricMonoidalClosed (R : Type u) [CommRing R] :
    ∃ (s : SymmetricCategory (CochainComplex (ModuleCat.{u} R) ℤ)),
      letI := s
      ∃ (closed : MonoidalClosed (CochainComplex (ModuleCat.{u} R) ℤ)),
        letI := closed
        ∃ (H : (CochainComplex (ModuleCat.{u} R) ℤ)ᵒᵖ ⥤
            CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ)
          (hObj : ∀ (L M : CochainComplex (ModuleCat.{u} R) ℤ),
            (H.obj (Opposite.op L)).obj M = HomComplexR R L M),
          (∀ (L M N : CochainComplex (ModuleCat.{u} R) ℤ) (f : M ⟶ N),
            (H.obj (Opposite.op L)).map f =
              eqToHom (hObj L M) ≫ Stacks.HomComplex.TensorHomMap.postcomp R L M N f ≫ eqToHom (hObj
                L N).symm) ∧
          (∀ (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (f : K ⟶ L),
            (H.map f.op).app M =
              eqToHom (hObj L M) ≫ Stacks.HomComplex.TensorHomMap.precomp R K L M f ≫ eqToHom (hObj
                K M).symm) ∧
          ∃ e : MonoidalClosed.internalHom ≅ H,
            (∀ (L M : CochainComplex (ModuleCat.{u} R) ℤ) (f : Cochain L M 0),
                (∃! φ : L ⟶ M, Cochain.ofHom φ = f) ↔ δ 0 1 f = 0) ∧
            ∀ (K L M : CochainComplex (ModuleCat.{u} R) ℤ)
                (φ : K ⟶ HomComplexR R L M),
              Cochain.ofHom
                  ((s.toBraidedCategory.braiding K L).hom ≫
                    MonoidalClosed.uncurry
                      (φ ≫ eqToHom (hObj L M).symm ≫ (e.app (Opposite.op L)).inv.app M)) =
                (Stacks.HomComplex.Currying.curryIso K L M).hom.f 0 (Cochain.ofHom φ) := by
  let s : SymmetricCategory (CochainComplex (ModuleCat.{u} R) ℤ) :=
    CochainComplex.Koszul.koszulSymmetric R
  clear_value s
  let := s
  refine ⟨s, homComplexMonoidalClosed (R := R), ?_⟩
  let := homComplexMonoidalClosed (R := R)
  refine ⟨MonoidalClosed.internalHom, (fun _ _ => rfl), ?_, ?_, Iso.refl _, ?_, ?_⟩
  · intro L M N f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · intro K L M f
    change (MonoidalClosed.pre f).app M = 𝟙 _ ≫ Stacks.HomComplex.TensorHomMap.precomp R K L M f ≫ 𝟙
      _
    rw [Category.id_comp, Category.comp_id]
    exact homComplex_pre f
  · refine fun L M f ↦ ⟨fun ⟨φ, hφ, _⟩ ↦ hφ ▸ δ_ofHom φ, fun hf ↦
      ⟨Cocycle.homOf (Cocycle.mk f 1 rfl hf), Cocycle.cochain_ofHom_homOf_eq_coe _,
        fun ψ hψ ↦ Cochain.ofHom_injective ?_⟩⟩
    rw [hψ, Cocycle.cochain_ofHom_homOf_eq_coe]
    rfl
  · intro K L M φ
    change Cochain.ofHom ((β_ K L).hom ≫ MonoidalClosed.uncurry φ) = _
    rw [homComplex_uncurry, Iso.hom_inv_id_assoc]
    exact ofHom_tensorHomEquiv K L M φ

end Stacks.HomComplex.MonoidalClosed
