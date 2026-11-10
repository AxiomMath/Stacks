module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPower
public import StacksFrontier.CategoryTheory.Equivalence.PowObjIsoSelf

/-!
# The iterates of an autoequivalence isomorphic to the identity, naturally

`StacksFrontier.CategoryTheory.Equivalence.PowObjIsoSelf` transports a family of isomorphisms
`α M : e M ≅ M` to every integer iterate, as `Stacks.Equivalence.powObjIsoSelf`. That
construction is objectwise and proves nothing further, deliberately: its own implementation
notes record that naturality of the result needs naturality of `α`, which is a strictly stronger
input than the objectwise family.

This file supplies the two further facts a consumer that wants an isomorphism of *functors*
needs. First, naturality: if `α` is natural then so is every iterate. Second, the comparison of
consecutive iterates: the map `(e ^ (n + 1)) M ⟶ (e ^ n) M` induced by the natural
transformation `a : e.functor ⟶ 𝟭` whose components are the `α M`, namely
`(powSuccIso e n M).inv ≫ a ((e ^ n) M)`, is carried by the family at `n` to the family at
`n + 1`.

The second fact is the one that makes the family a *compatible* system. Its consumer is the
Berthelot–Ogus décalage `η_I` at an ideal `I` whose inclusion `I ⟶ 𝒪` is invertible: there the
induced maps are `Stacks.IdealTorsion.Eta.idealPowerIncl` and the system of isomorphisms
untwists each term of the décalage onto the corresponding term of the complex.

## Main results

* `Stacks.Equivalence.inverseObjIsoSelf_naturality`: the family for the quasi-inverse is
  natural. This is the step the negative iterates rest on, `Stacks.Equivalence.powObjIsoSelf`
  sending a negative exponent to an iterate of the quasi-inverse.
* `Stacks.Equivalence.powNatObjIsoSelf_naturality` and
  `Stacks.Equivalence.powObjIsoSelf_naturality`: **the family is natural**, for natural-number
  and then for integer exponents.
* `Stacks.Equivalence.powNatObjIsoSelf_succIso`,
  `Stacks.Equivalence.powNatObjIsoSelf_inverseSuccIso` and
  `Stacks.Equivalence.powObjIsoSelf_succIso`: **the family is compatible with the induced maps
  between consecutive iterates**, for natural-number exponents, for the iterates of the
  quasi-inverse, and then for integer exponents.

## Implementation notes

Naturality of `α` is an explicit hypothesis rather than a natural isomorphism
`e.functor ≅ 𝟭`, for the reason given in
`StacksFrontier.CategoryTheory.Equivalence.PowIntertwinerNaturality`: the `α` argument of
`powObjIsoSelf` is an objectwise family, so asking for the functor form would force every caller
to assemble a `NatIso.ofComponents` and then take it apart again.

Each induction is the one the definition it is about recurses along. `powNatObjIsoSelf` reduces
the exponent `n + 2` to `n + 1` at the object `e M`, so the statements are quantified over the
objects inside the induction and the inductive hypothesis is used at a shifted object;
`Stacks.Equivalence.powNatSuccIso` and `Stacks.Equivalence.powNatInverseSuccIso` recurse the
same way, which is what lets the two sides stay in step. The integer statements are then a plain
match on the constructor of `ℤ`, with no transport: that is the case split
`Stacks.Equivalence.powSuccIso` and `Stacks.Equivalence.powObjIsoSelf` are both defined by.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace Stacks.Equivalence

variable {A : Type u} [Category.{v} A]

/-! ### Naturality -/

/-- **The family for the quasi-inverse is natural.** Unfolding
`Stacks.Equivalence.inverseObjIsoSelf`, the claim is the naturality of `α` at
`e.inverse.map g`, read backwards, followed by the naturality of the counit of `e`. -/
theorem inverseObjIsoSelf_naturality (e : A ≌ A) (α : ∀ M : A, e.functor.obj M ≅ M)
    (hα : ∀ {M N : A} (g : M ⟶ N), e.functor.map g ≫ (α N).hom = (α M).hom ≫ g)
    {M N : A} (g : M ⟶ N) :
    e.inverse.map g ≫ (inverseObjIsoSelf e α N).hom =
      (inverseObjIsoSelf e α M).hom ≫ g := by
  have hinv : (α (e.inverse.obj M)).inv ≫ e.functor.map (e.inverse.map g) =
      e.inverse.map g ≫ (α (e.inverse.obj N)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact hα (e.inverse.map g)
  have hcounit : e.functor.map (e.inverse.map g) ≫ (e.counitIso.app N).hom =
      (e.counitIso.app M).hom ≫ g := e.counitIso.hom.naturality g
  change e.inverse.map g ≫ (α (e.inverse.obj N)).inv ≫ (e.counitIso.app N).hom =
    ((α (e.inverse.obj M)).inv ≫ (e.counitIso.app M).hom) ≫ g
  rw [← Category.assoc, ← hinv, Category.assoc, hcounit, Category.assoc]

/-- **The family for natural-number iterates is natural.** The induction is the one
`Stacks.Equivalence.powNatObjIsoSelf` recurses along: the exponent `n + 2` is reduced to `n + 1`
at the object `e M`, so the inductive hypothesis is used at `e.functor.map g`. -/
theorem powNatObjIsoSelf_naturality (e : A ≌ A) (α : ∀ M : A, e.functor.obj M ≅ M)
    (hα : ∀ {M N : A} (g : M ⟶ N), e.functor.map g ≫ (α N).hom = (α M).hom ≫ g) :
    ∀ (n : ℕ) {M N : A} (g : M ⟶ N),
      (e.powNat n).functor.map g ≫ (powNatObjIsoSelf e α n N).hom =
        (powNatObjIsoSelf e α n M).hom ≫ g
  | 0, _, _, g => by
      change g ≫ 𝟙 _ = 𝟙 _ ≫ g
      simp
  | 1, _, _, g => hα g
  | n + 2, M, N, g => by
      have ih := powNatObjIsoSelf_naturality e α hα (n + 1) (e.functor.map g)
      change (e.powNat (n + 1)).functor.map (e.functor.map g) ≫
          (powNatObjIsoSelf e α (n + 1) (e.functor.obj N)).hom ≫ (α N).hom =
        ((powNatObjIsoSelf e α (n + 1) (e.functor.obj M)).hom ≫ (α M).hom) ≫ g
      rw [← Category.assoc, ih, Category.assoc, Category.assoc, hα g]

/-- **The family for integer iterates is natural.** A negative exponent is an iterate of the
quasi-inverse, for which the previous result applies to `inverseObjIsoSelf`. -/
theorem powObjIsoSelf_naturality (e : A ≌ A) (α : ∀ M : A, e.functor.obj M ≅ M)
    (hα : ∀ {M N : A} (g : M ⟶ N), e.functor.map g ≫ (α N).hom = (α M).hom ≫ g)
    (n : ℤ) {M N : A} (g : M ⟶ N) :
    (e ^ n).functor.map g ≫ (powObjIsoSelf e α n N).hom =
      (powObjIsoSelf e α n M).hom ≫ g := by
  match n with
  | Int.ofNat k => exact powNatObjIsoSelf_naturality e α hα k g
  | Int.negSucc k =>
      exact powNatObjIsoSelf_naturality e.symm (inverseObjIsoSelf e α)
        (fun {_ _} h => inverseObjIsoSelf_naturality e α hα h) (k + 1) g

/-! ### Compatibility with the maps between consecutive iterates -/

/-- **The family is compatible with the induced maps, for natural-number iterates.** The
induction is the one `Stacks.Equivalence.powNatObjIsoSelf` and
`Stacks.Equivalence.powNatSuccIso` both recurse along; the two base cases are the ones at which
the successor comparison is the identity. -/
theorem powNatObjIsoSelf_succIso (e : A ≌ A) (α : ∀ M : A, e.functor.obj M ≅ M) :
    ∀ (n : ℕ) (M : A),
      (powNatSuccIso e n M).inv ≫ (α ((e.powNat n).functor.obj M)).hom ≫
          (powNatObjIsoSelf e α n M).hom =
        (powNatObjIsoSelf e α (n + 1) M).hom
  | 0, M => by
      change 𝟙 _ ≫ (α M).hom ≫ 𝟙 _ = (α M).hom
      simp
  | 1, M => by
      change 𝟙 _ ≫ (α (e.functor.obj M)).hom ≫ (α M).hom =
        (α (e.functor.obj M)).hom ≫ (α M).hom
      simp
  | n + 2, M => by
      have ih := powNatObjIsoSelf_succIso e α (n + 1) (e.functor.obj M)
      change (powNatSuccIso e (n + 1) (e.functor.obj M)).inv ≫
          (α ((e.powNat (n + 1)).functor.obj (e.functor.obj M))).hom ≫
            ((powNatObjIsoSelf e α (n + 1) (e.functor.obj M)).hom ≫ (α M).hom) =
        (powNatObjIsoSelf e α (n + 2) (e.functor.obj M)).hom ≫ (α M).hom
      rw [← Category.assoc ((α ((e.powNat (n + 1)).functor.obj (e.functor.obj M))).hom),
        ← Category.assoc, ih]

/-- **The family is compatible with the induced maps, for the iterates of the quasi-inverse.**
Here one application of `e` cancels an inverse iterate and the successor comparison is the
counit, against which the component of `α` that `inverseObjIsoSelf` carries cancels. -/
theorem powNatObjIsoSelf_inverseSuccIso (e : A ≌ A) (α : ∀ M : A, e.functor.obj M ≅ M) :
    ∀ (n : ℕ) (M : A),
      (powNatInverseSuccIso e n M).inv ≫
          (α ((e.symm.powNat (n + 1)).functor.obj M)).hom ≫
            (powNatObjIsoSelf e.symm (inverseObjIsoSelf e α) (n + 1) M).hom =
        (powNatObjIsoSelf e.symm (inverseObjIsoSelf e α) n M).hom
  | 0, M => by
      change (e.counitIso.app M).inv ≫ (α (e.inverse.obj M)).hom ≫
          ((α (e.inverse.obj M)).inv ≫ (e.counitIso.app M).hom) = 𝟙 M
      simp
  | 1, M => by
      change (e.counitIso.app (e.inverse.obj M)).inv ≫
          (α (e.inverse.obj (e.inverse.obj M))).hom ≫
            (((α (e.inverse.obj (e.inverse.obj M))).inv ≫
                (e.counitIso.app (e.inverse.obj M)).hom) ≫
              (inverseObjIsoSelf e α M).hom) =
        (inverseObjIsoSelf e α M).hom
      simp
  | n + 2, M => by
      have ih := powNatObjIsoSelf_inverseSuccIso e α (n + 1) (e.inverse.obj M)
      change (powNatInverseSuccIso e (n + 1) (e.inverse.obj M)).inv ≫
          (α ((e.symm.powNat (n + 2)).functor.obj (e.inverse.obj M))).hom ≫
            ((powNatObjIsoSelf e.symm (inverseObjIsoSelf e α) (n + 2)
                (e.inverse.obj M)).hom ≫ (inverseObjIsoSelf e α M).hom) =
        (powNatObjIsoSelf e.symm (inverseObjIsoSelf e α) (n + 1)
            (e.inverse.obj M)).hom ≫ (inverseObjIsoSelf e α M).hom
      rw [← Category.assoc ((α ((e.symm.powNat (n + 2)).functor.obj (e.inverse.obj M))).hom),
        ← Category.assoc, ih]

/-- **The family is compatible with the induced maps, in every integer degree.** A natural
transformation `a : e.functor ⟶ 𝟭` induces in degree `n` the map
`(powSuccIso e n M).inv ≫ a ((e ^ n) M) : (e ^ (n + 1)) M ⟶ (e ^ n) M`; if the components of `a`
are the isomorphisms `α`, that map is carried by the family at `n` to the family at `n + 1`.

The three branches are the three branches of the definitions of
`Stacks.Equivalence.powSuccIso` and `Stacks.Equivalence.powObjIsoSelf`: a non-negative exponent
is the natural-number statement, and a negative one the statement for the quasi-inverse. -/
theorem powObjIsoSelf_succIso (e : A ≌ A) (α : ∀ M : A, e.functor.obj M ≅ M) (n : ℤ) (M : A) :
    ((powSuccIso e n M).inv ≫ (α ((e ^ n).functor.obj M)).hom) ≫
        (powObjIsoSelf e α n M).hom =
      (powObjIsoSelf e α (n + 1) M).hom := by
  rw [Category.assoc]
  match n with
  | Int.ofNat k => exact powNatObjIsoSelf_succIso e α k M
  | Int.negSucc 0 => exact powNatObjIsoSelf_inverseSuccIso e α 0 M
  | Int.negSucc (k + 1) => exact powNatObjIsoSelf_inverseSuccIso e α (k + 1) M

end Stacks.Equivalence

end
