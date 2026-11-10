module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPower
public import StacksFrontier.CategoryTheory.Equivalence.PowIntertwinerNaturality

/-!
# The intertwiner of integer iterates is compatible with the successor comparison

`StacksFrontier.CategoryTheory.Equivalence.PowIntertwiner` transports a comparison
`α M : R (e M) ≅ e' (R M)` to every integer iterate, as `Stacks.Equivalence.powIntertwineObj`,
and `StacksFrontier.CategoryTheory.Equivalence.PowIntertwinerNaturality` proves that the transport
is natural when `α` is. Neither relates the iterate at `n` to the iterate at `n + 1`.

The two iterates are compared by `Stacks.Equivalence.powSuccIso` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPower`, which identifies `e ((e ^ n) M)`
with `(e ^ (n + 1)) M`, and the statement proved below is that the square

```
R (e ((e ^ n) M)) ---- R (powSuccIso) ----> R ((e ^ (n + 1)) M)
      |                                              |
   α ≫ e' (comparison at n)                   comparison at n + 1
      v                                              v
e' ((e' ^ n) (R M)) -- powSuccIso at e' --> (e' ^ (n + 1)) (R M)
```

commutes in every integer degree.

A natural transformation `a : e.functor ⟶ 𝟭` induces, in each integer degree, a map
`(e ^ (n + 1)) M ⟶ (e ^ n) M` as `(powSuccIso e n M).inv ≫ a ((e ^ n) M)`, and
`powIntertwineObj_incl` below says that the transported comparison commutes with those maps,
given the compatibility of `α` with `a`.

## Main results

* `Stacks.Equivalence.powNatIntertwineObj_succIso`: the compatibility for natural-number
  iterates.
* `Stacks.Equivalence.powNatIntertwineObj_inverseSuccIso`: the compatibility for the iterates of
  the quasi-inverses, where one application of `e` cancels an inverse iterate and the comparison
  is the counit.
* `Stacks.Equivalence.powIntertwineObj_succIso`: **the compatibility in every integer degree.**
* `Stacks.Equivalence.powIntertwineObj_incl`: **the induced inclusions commute with the
  transported comparison**, given that `α` is compatible with the inducing natural
  transformation.

## Implementation notes

The two inductions mirror the recursions of `Stacks.Equivalence.powNatSuccIso` and
`Stacks.Equivalence.powNatInverseSuccIso` exactly: both reduce the exponent `n + 2` to `n + 1`
at a shifted object, so the statement is quantified over the object inside the induction and the
inductive hypothesis is used at `e M` (respectively `e⁻¹ M`). In each case the step closes with
the naturality of the successor comparison itself —
`Stacks.Equivalence.powNatSuccIso_naturality`, respectively
`Stacks.Equivalence.powNatInverseSuccIso_naturality` — applied to the component `α M`.

No naturality of `α` is needed anywhere: the statements are objectwise, as in
`Stacks.Equivalence.powIntertwineObj` itself. `powIntertwineObj_incl` does use naturality of
`a'`, which is part of the data of a natural transformation and is not an extra hypothesis.

The integer statement is assembled by matching on the constructor of `ℤ`, the same case split
`Stacks.Equivalence.powSuccIso` and `Stacks.Equivalence.powIntertwineObj` are defined by, so
each branch is the corresponding natural-number statement with no transport: `Int.negSucc 0` is
the degree `-1`, where the successor comparison is the counit and the iterate at `0` is the
identity.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace Stacks.Equivalence

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- If `x ≫ c` factors as `a ≫ F.map c' ≫ s₀` and `s₀ ≫ g` is `F.map g' ≫ s`, then `x ≫ c ≫ g`
factors as `a ≫ F.map (c' ≫ g') ≫ s`. -/
private theorem comp_comp_eq_of_naturality {C D : Type*} [Category C] [Category D] {F : D ⥤ C}
    {P Q R S : C} {U V W : D} (x : P ⟶ Q) (c : Q ⟶ R) (g : R ⟶ S) (a : P ⟶ F.obj U)
    (c' : U ⟶ V) (g' : V ⟶ W) (s₀ : F.obj V ⟶ R) (s : F.obj W ⟶ S)
    (ih : x ≫ c = a ≫ F.map c' ≫ s₀) (hnat : F.map g' ≫ s = s₀ ≫ g) :
    x ≫ c ≫ g = a ≫ F.map (c' ≫ g') ≫ s := by
  rw [← Category.assoc, ih]
  simp only [Category.assoc, Functor.map_comp]
  rw [← hnat]

/-- **The compatibility with the successor comparison, for natural-number iterates**: `R` of
the successor comparison of `e` followed by the transported comparison at `n + 1` is `α`,
followed by `e'` of the transported comparison at `n` and the successor comparison of `e'`. -/
theorem powNatIntertwineObj_succIso (e : A ≌ A) (e' : B ≌ B) (R : A ⥤ B)
    (α : ∀ M : A, R.obj (e.functor.obj M) ≅ e'.functor.obj (R.obj M)) :
    ∀ (n : ℕ) (M : A),
      R.map (powNatSuccIso e n M).hom ≫ (powNatIntertwineObj e e' R α (n + 1) M).hom =
        (α ((e.powNat n).functor.obj M)).hom ≫
          e'.functor.map (powNatIntertwineObj e e' R α n M).hom ≫
            (powNatSuccIso e' n (R.obj M)).hom
  | 0, M => by
      change R.map (𝟙 (e.functor.obj M)) ≫ (α M).hom =
        (α M).hom ≫ e'.functor.map (𝟙 (R.obj M)) ≫ 𝟙 (e'.functor.obj (R.obj M))
      simp
  | 1, M => by
      change R.map (𝟙 (e.functor.obj (e.functor.obj M))) ≫
          ((α (e.functor.obj M)).hom ≫ e'.functor.map (α M).hom) =
        (α (e.functor.obj M)).hom ≫
          e'.functor.map (α M).hom ≫ 𝟙 (e'.functor.obj (e'.functor.obj (R.obj M)))
      simp
  | n + 2, M => by
      have ih := powNatIntertwineObj_succIso e e' R α (n + 1) (e.functor.obj M)
      have hnat := powNatSuccIso_naturality e' (n + 1) (R.obj (e.functor.obj M))
        (e'.functor.obj (R.obj M)) (α M).hom
      exact comp_comp_eq_of_naturality _ _ _ _ _ _ _ _ ih hnat

/-- **The compatibility with the successor comparison, for the iterates of the quasi-inverses**,
transported along `Stacks.Equivalence.inverseIntertwineObj`. At exponent `0` one application of
`e` cancels a single inverse iterate, and the successor comparison is the counit. -/
theorem powNatIntertwineObj_inverseSuccIso (e : A ≌ A) (e' : B ≌ B) (R : A ⥤ B)
    (α : ∀ M : A, R.obj (e.functor.obj M) ≅ e'.functor.obj (R.obj M)) :
    ∀ (n : ℕ) (M : A),
      R.map (powNatInverseSuccIso e n M).hom ≫
          (powNatIntertwineObj e.symm e'.symm R (inverseIntertwineObj e e' R α) n M).hom =
        (α ((e.symm.powNat (n + 1)).functor.obj M)).hom ≫
          e'.functor.map (powNatIntertwineObj e.symm e'.symm R
            (inverseIntertwineObj e e' R α) (n + 1) M).hom ≫
            (powNatInverseSuccIso e' n (R.obj M)).hom
  | 0, M => by
      have key : (inverseIntertwineObj e e' R α M).hom =
          e'.unit.app (R.obj (e.inverse.obj M)) ≫
            e'.inverse.map ((α (e.inverse.obj M)).inv ≫ R.map (e.counit.app M)) := rfl
      change R.map (e.counit.app M) ≫ 𝟙 (R.obj M) =
        (α (e.inverse.obj M)).hom ≫
          e'.functor.map (inverseIntertwineObj e e' R α M).hom ≫ e'.counit.app (R.obj M)
      rw [key, Functor.map_comp, Category.assoc]
      rw [show e'.functor.map (e'.inverse.map ((α (e.inverse.obj M)).inv ≫
            R.map (e.counit.app M))) ≫ e'.counit.app (R.obj M) =
          e'.counit.app (e'.functor.obj (R.obj (e.inverse.obj M))) ≫
            ((α (e.inverse.obj M)).inv ≫ R.map (e.counit.app M)) from
        e'.counit.naturality _]
      simp
  | 1, M => by
      have hnat : e'.functor.map (e'.inverse.map (inverseIntertwineObj e e' R α M).hom) ≫
          e'.counit.app (e'.inverse.obj (R.obj M)) =
        e'.counit.app (R.obj (e.inverse.obj M)) ≫ (inverseIntertwineObj e e' R α M).hom :=
        e'.counit.naturality _
      have ih : R.map (e.counit.app (e.inverse.obj M)) =
          (α (e.inverse.obj (e.inverse.obj M))).hom ≫
            e'.functor.map (inverseIntertwineObj e e' R α (e.inverse.obj M)).hom ≫
              e'.counit.app (R.obj (e.inverse.obj M)) :=
        (Category.comp_id _).symm.trans
          (powNatIntertwineObj_inverseSuccIso e e' R α 0 (e.inverse.obj M))
      change R.map (e.counit.app (e.inverse.obj M)) ≫ (inverseIntertwineObj e e' R α M).hom =
        (α (e.inverse.obj (e.inverse.obj M))).hom ≫
          e'.functor.map ((inverseIntertwineObj e e' R α (e.inverse.obj M)).hom ≫
            e'.inverse.map (inverseIntertwineObj e e' R α M).hom) ≫
            e'.counit.app (e'.inverse.obj (R.obj M))
      rw [ih, Functor.map_comp]
      simp only [Category.assoc]
      rw [hnat]
  | n + 2, M => by
      have ih := powNatIntertwineObj_inverseSuccIso e e' R α (n + 1) (e.inverse.obj M)
      have hnat := powNatInverseSuccIso_naturality e' (n + 1) (R.obj (e.inverse.obj M))
        (e'.inverse.obj (R.obj M)) (inverseIntertwineObj e e' R α M).hom
      exact comp_comp_eq_of_naturality _ _ _ _ _ _ _ _ ih hnat

/-- **The transported comparison is compatible with the successor comparison in every integer
degree**: `R` of the successor comparison of `e` followed by the comparison at `n + 1` is `α`,
followed by `e'` of the comparison at `n` and the successor comparison of `e'`. -/
theorem powIntertwineObj_succIso (e : A ≌ A) (e' : B ≌ B) (R : A ⥤ B)
    (α : ∀ M : A, R.obj (e.functor.obj M) ≅ e'.functor.obj (R.obj M)) (n : ℤ) (M : A) :
    R.map (powSuccIso e n M).hom ≫ (powIntertwineObj e e' R α (n + 1) M).hom =
      (α ((e ^ n).functor.obj M)).hom ≫
        e'.functor.map (powIntertwineObj e e' R α n M).hom ≫
          (powSuccIso e' n (R.obj M)).hom := by
  match n with
  | Int.ofNat k => exact powNatIntertwineObj_succIso e e' R α k M
  | Int.negSucc 0 => exact powNatIntertwineObj_inverseSuccIso e e' R α 0 M
  | Int.negSucc (k + 1) => exact powNatIntertwineObj_inverseSuccIso e e' R α (k + 1) M

/-- **The inclusions induced by a natural transformation `a : e ⟶ 𝟭` commute with the
transported comparison.** In integer degree `n` the transformation induces
`(powSuccIso e n M).inv ≫ a ((e ^ n) M) : (e ^ (n + 1)) M ⟶ (e ^ n) M`, and likewise for `e'`
and `a'`; if `α` carries `a` to `a'` then `R` carries the one to the other through the
comparisons of `Stacks.Equivalence.powIntertwineObj`. -/
theorem powIntertwineObj_incl (e : A ≌ A) (e' : B ≌ B) (R : A ⥤ B)
    (α : ∀ M : A, R.obj (e.functor.obj M) ≅ e'.functor.obj (R.obj M))
    (a : e.functor ⟶ 𝟭 A) (a' : e'.functor ⟶ 𝟭 B)
    (ha : ∀ P : A, R.map (a.app P) = (α P).hom ≫ a'.app (R.obj P))
    (n : ℤ) (M : A) :
    R.map ((powSuccIso e n M).inv ≫ a.app ((e ^ n).functor.obj M)) ≫
        (powIntertwineObj e e' R α n M).hom =
      (powIntertwineObj e e' R α (n + 1) M).hom ≫
        (powSuccIso e' n (R.obj M)).inv ≫ a'.app ((e' ^ n).functor.obj (R.obj M)) := by
  have hnat : e'.functor.map (powIntertwineObj e e' R α n M).hom ≫
      a'.app ((e' ^ n).functor.obj (R.obj M)) =
    a'.app (R.obj ((e ^ n).functor.obj M)) ≫ (powIntertwineObj e e' R α n M).hom :=
    a'.naturality _
  have hsucc' : (α ((e ^ n).functor.obj M)).hom ≫
      e'.functor.map (powIntertwineObj e e' R α n M).hom =
    R.map (powSuccIso e n M).hom ≫ (powIntertwineObj e e' R α (n + 1) M).hom ≫
      (powSuccIso e' n (R.obj M)).inv := by
    rw [← Category.assoc, powIntertwineObj_succIso e e' R α n M]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [R.map_comp, ha]
  simp only [Category.assoc]
  rw [← hnat, ← Category.assoc ((α ((e ^ n).functor.obj M)).hom), hsucc']
  simp only [Category.assoc]
  rw [← Category.assoc (R.map (powSuccIso e n M).inv), ← R.map_comp, Iso.inv_hom_id, R.map_id,
    Category.id_comp]

end Stacks.Equivalence

end
