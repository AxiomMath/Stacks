module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceBaseChange

/-!
# Changing the module of a line-bundle situation by an isomorphism

Let `D` be a line-bundle situation: a morphism of schemes `f : X ⟶ S` together with an invertible
`𝒪_X`-module `L`. An isomorphism `α : L ≅ N` onto another invertible module produces an
isomorphism of total spaces `Tot(N) ≅ Tot(L)` over `X`, and that isomorphism carries the zero
section to the zero section.

Everything is read off the functor of points
`Stacks.LineBundle.Situation.totalSpaceHomEquiv`: a point of `Tot(L)` over a test scheme `W` is a
morphism `k : W ⟶ X` together with a fibrewise functional `L ⟶ k_* 𝒪_W`, so composing that
functional with `α` turns the points of `Tot(N)` into the points of `Tot(L)`, bijectively and
naturally in `W`.

## Main definitions

* `Stacks.LineBundle.Situation.changeModule`: the situation with the same morphism to the base and
  the module replaced by another one.
* `Stacks.LineBundle.Situation.totalSpaceHomEquivCongr`: **the functors of points of the two total
  spaces correspond** along an isomorphism of the two modules.
* `Stacks.LineBundle.Situation.totalSpaceIsoOfIso`: **the induced isomorphism of total spaces.**

## Main results

* `Stacks.LineBundle.Situation.totalSpaceHomEquiv_symm_comp`: the functor of points of the total
  space, read for the inverse bijection, where no projection of a dependent pair occurs.
* `Stacks.LineBundle.Situation.totalSpaceHomEquivCongr_comp`: the comparison of the two functors
  of points is natural in the test scheme.
* `Stacks.LineBundle.Situation.totalSpaceIsoOfIso_hom_comp_totalSpaceToBase`: **the induced
  isomorphism is one of schemes over the base.**
* `Stacks.LineBundle.Situation.zeroSection_comp_totalSpaceIsoOfIso_hom`: **the induced isomorphism
  carries the zero section to the zero section.**

## Implementation notes

The comparison is a morphism produced from a bijection of functors of points, so it is obtained by
evaluating that bijection at the identity, and the naturality statement
(`Stacks.LineBundle.Situation.totalSpaceHomEquivCongr_comp`) is what turns it into a morphism: the
two composites of the isomorphism are then two round trips of a bijection. Nothing about the
symmetric algebra is used.

The fibrewise functional of a pair depends on the pair's morphism to the base, so moving `𝟙 ≫ g`
to `g` in the first component of a pair is not a rewrite.
`Stacks.LineBundle.sigma_mk_zero_congr` performs that move for the pairs whose functional
vanishes, by substituting the equality of first components; `Stacks.LineBundle.sigma_mk_congr`
performs the complementary move at a fixed first component, and is stated so that the type family
of the dependent sum is never left to higher-order unification.

The comparison of the fibrewise functionals is `CategoryTheory.Iso.homFromEquiv` at the inverse
isomorphism, which is precomposition with `α.hom` on the nose, so the identity of pairs
`Stacks.LineBundle.Situation.totalSpaceHomEquiv_totalSpaceHomEquivCongr` is a round trip of a
bijection and nothing more.

## References

* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.LineBundle

/-! ### Change of test scheme for the functor of points -/

/-- Two pairs in the functor of points with the same morphism to the base and the same fibrewise
functional are equal. Stated separately so that the type family of the dependent sum is never
left to higher-order unification. -/
theorem sigma_mk_congr {W Z : Scheme.{u}} {N : Z.Modules} {k : W ⟶ Z}
    {ψ ψ' : N ⟶ (Scheme.Modules.pushforward k).obj (SheafOfModules.unit W.ringCatSheaf)}
    (e : ψ = ψ') :
    (⟨k, ψ⟩ : Σ j : W ⟶ Z,
        (N ⟶ (Scheme.Modules.pushforward j).obj (SheafOfModules.unit W.ringCatSheaf))) =
      ⟨k, ψ'⟩ :=
  congrArg (Sigma.mk k) e

/-- Two pairs in the functor of points with vanishing fibrewise functional and equal morphisms to
the base are equal. The substitution is needed because the type of the functional depends on that
morphism. -/
theorem sigma_mk_zero_congr {W Z : Scheme.{u}} (N : Z.Modules) {k k' : W ⟶ Z} (h : k = k') :
    (⟨k, 0⟩ : Σ j : W ⟶ Z,
        (N ⟶ (Scheme.Modules.pushforward j).obj (SheafOfModules.unit W.ringCatSheaf))) =
      ⟨k', 0⟩ := by
  subst h
  rfl

/-- `Stacks.LineBundle.Situation.totalSpaceHomEquiv_comp`, with the canonical map on pushed-forward
structure sheaves written as a map of module pushforwards. -/
theorem Situation.totalSpaceHomEquiv_comp' (D : Situation.{u}) {W W' : Scheme.{u}}
    (c : W' ⟶ W) (f : W ⟶ D.totalSpace) :
    D.totalSpaceHomEquiv W' (c ≫ f) =
      ⟨c ≫ (D.totalSpaceHomEquiv W f).1,
        (D.totalSpaceHomEquiv W f).2 ≫ structureComparison (D.totalSpaceHomEquiv W f).1 c⟩ :=
  D.totalSpaceHomEquiv_comp c f

/-- **The functor of points of the total space, read on a pair and precomposed with a morphism of
test schemes.** This is `Stacks.LineBundle.Situation.totalSpaceHomEquiv_comp` stated for the
inverse bijection, where no projection of a dependent pair occurs. -/
theorem Situation.totalSpaceHomEquiv_symm_comp (D : Situation.{u}) {W W' : Scheme.{u}}
    (c : W' ⟶ W)
    (p : Σ k : W ⟶ D.X, (D.L ⟶ (Scheme.Modules.pushforward k).obj
      (SheafOfModules.unit W.ringCatSheaf))) :
    c ≫ (D.totalSpaceHomEquiv W).symm p =
      (D.totalSpaceHomEquiv W').symm ⟨c ≫ p.1, p.2 ≫ structureComparison p.1 c⟩ := by
  refine (D.totalSpaceHomEquiv W').injective ?_
  rw [D.totalSpaceHomEquiv_comp', Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-! ### Changing the module of a situation by an isomorphism -/

variable (D : Situation.{u}) (N : D.X.Modules)
  [hN : AlgebraicGeometry.SheafOfModules.IsInvertible D.X.sheaf.obj D.X.ringCatSheaf.property N]

include hN in
/-- **The line-bundle situation with the same morphism to the base and the module replaced.** -/
def Situation.changeModule : Situation.{u} where
  X := D.X
  S := D.S
  f := D.f
  L := N

include hN in
/-- Replacing the module does not change the base. -/
@[simp] theorem Situation.changeModule_X : (D.changeModule N).X = D.X := rfl

include hN in
/-- Replacing the module replaces the module. -/
@[simp] theorem Situation.changeModule_L : (D.changeModule N).L = N := rfl

variable (α : D.L ≅ N)

include hN in
/-- **The functors of points of the two total spaces correspond**: a point of `Tot(N)` is a
morphism to the base together with a fibrewise functional on `N`, and composing that functional
with `α` makes it a functional on `L`. -/
def Situation.totalSpaceHomEquivCongr (W : Scheme.{u}) :
    (W ⟶ (D.changeModule N).totalSpace) ≃ (W ⟶ D.totalSpace) :=
  ((D.changeModule N).totalSpaceHomEquiv W).trans
    ((Equiv.sigmaCongrRight fun _ : W ⟶ D.X => Iso.homFromEquiv α.symm).trans
      (D.totalSpaceHomEquiv W).symm)

include hN in
/-- The comparison of the two functors of points, read as an identity of pairs. -/
theorem Situation.totalSpaceHomEquiv_totalSpaceHomEquivCongr {W : Scheme.{u}}
    (m : W ⟶ (D.changeModule N).totalSpace) :
    D.totalSpaceHomEquiv W (D.totalSpaceHomEquivCongr N α W m) =
      ⟨((D.changeModule N).totalSpaceHomEquiv W m).1,
        α.hom ≫ ((D.changeModule N).totalSpaceHomEquiv W m).2⟩ :=
  Equiv.apply_symm_apply _ _

/-- The comparison of the two functors of points, read as the inverse bijection applied to a
pair. -/
private theorem Situation.totalSpaceHomEquivCongr_eq_symm {W : Scheme.{u}}
    (m : W ⟶ (D.changeModule N).totalSpace) :
    D.totalSpaceHomEquivCongr N α W m =
      (D.totalSpaceHomEquiv W).symm
        ⟨((D.changeModule N).totalSpaceHomEquiv W m).1,
          α.hom ≫ ((D.changeModule N).totalSpaceHomEquiv W m).2⟩ :=
  rfl

include hN in
/-- **The comparison of the two functors of points is natural in the test scheme.** -/
theorem Situation.totalSpaceHomEquivCongr_comp {W W' : Scheme.{u}} (c : W' ⟶ W)
    (m : W ⟶ (D.changeModule N).totalSpace) :
    D.totalSpaceHomEquivCongr N α W' (c ≫ m) = c ≫ D.totalSpaceHomEquivCongr N α W m := by
  rw [D.totalSpaceHomEquivCongr_eq_symm N α, D.totalSpaceHomEquivCongr_eq_symm N α,
    D.totalSpaceHomEquiv_symm_comp, (D.changeModule N).totalSpaceHomEquiv_comp']
  exact congrArg _ (sigma_mk_congr (Category.assoc _ _ _).symm)

include hN in
/-- **The morphism `Tot(N) ⟶ Tot(L)` induced by an isomorphism `α : L ≅ N`.** -/
def Situation.totalSpaceMapOfIso : (D.changeModule N).totalSpace ⟶ D.totalSpace :=
  D.totalSpaceHomEquivCongr N α _ (CategoryTheory.CategoryStruct.id _)

include hN in
/-- The induced morphism, read on points, is the comparison of the functors of points. -/
theorem Situation.comp_totalSpaceMapOfIso {W : Scheme.{u}}
    (m : W ⟶ (D.changeModule N).totalSpace) :
    m ≫ D.totalSpaceMapOfIso N α = D.totalSpaceHomEquivCongr N α W m := by
  rw [Situation.totalSpaceMapOfIso, ← D.totalSpaceHomEquivCongr_comp N α m
    (CategoryTheory.CategoryStruct.id _), Category.comp_id]

include hN in
/-- **The morphism `Tot(L) ⟶ Tot(N)` induced by an isomorphism `α : L ≅ N`**, in the other
direction. -/
def Situation.totalSpaceInvMapOfIso : D.totalSpace ⟶ (D.changeModule N).totalSpace :=
  (D.totalSpaceHomEquivCongr N α _).symm (CategoryTheory.CategoryStruct.id _)

include hN in
/-- The morphism in the other direction, read on points, is the inverse comparison of the
functors of points. -/
theorem Situation.comp_totalSpaceInvMapOfIso {W : Scheme.{u}} (n : W ⟶ D.totalSpace) :
    n ≫ D.totalSpaceInvMapOfIso N α = (D.totalSpaceHomEquivCongr N α W).symm n := by
  refine (D.totalSpaceHomEquivCongr N α W).injective ?_
  rw [Equiv.apply_symm_apply, Situation.totalSpaceInvMapOfIso,
    D.totalSpaceHomEquivCongr_comp N α n ((D.totalSpaceHomEquivCongr N α D.totalSpace).symm
      (CategoryTheory.CategoryStruct.id _)),
    Equiv.apply_symm_apply, Category.comp_id]

include hN in
/-- **An isomorphism of the two modules induces an isomorphism of the two total spaces.** -/
def Situation.totalSpaceIsoOfIso : (D.changeModule N).totalSpace ≅ D.totalSpace where
  hom := D.totalSpaceMapOfIso N α
  inv := D.totalSpaceInvMapOfIso N α
  hom_inv_id := by
    rw [D.comp_totalSpaceInvMapOfIso N α (D.totalSpaceMapOfIso N α), Situation.totalSpaceMapOfIso,
      Equiv.symm_apply_apply]
  inv_hom_id := by
    rw [D.comp_totalSpaceMapOfIso N α (D.totalSpaceInvMapOfIso N α),
      Situation.totalSpaceInvMapOfIso, Equiv.apply_symm_apply]

include hN in
/-- **The induced isomorphism of total spaces is one of schemes over the base**: the morphism to
the base attached to a point is untouched by the comparison. -/
theorem Situation.totalSpaceIsoOfIso_hom_comp_totalSpaceToBase :
    (D.totalSpaceIsoOfIso N α).hom ≫ D.totalSpaceToBase =
      (D.changeModule N).totalSpaceToBase := by
  have h := congrArg (fun p => Sigma.fst p)
    (D.totalSpaceHomEquiv_totalSpaceHomEquivCongr N α
      (CategoryTheory.CategoryStruct.id (D.changeModule N).totalSpace))
  refine Eq.trans ?_ (Eq.trans h (Category.id_comp (D.changeModule N).totalSpaceToBase))
  rfl

include hN in
/-- **The induced isomorphism of total spaces carries the zero section to the zero section**: the
zero section is the point whose fibrewise functional vanishes, and composing the zero functional
with `α` leaves it zero. -/
theorem Situation.zeroSection_comp_totalSpaceIsoOfIso_hom :
    (D.changeModule N).zeroSection ≫ (D.totalSpaceIsoOfIso N α).hom = D.zeroSection := by
  refine (D.comp_totalSpaceMapOfIso N α _).trans ?_
  rw [D.totalSpaceHomEquivCongr_eq_symm N α, (D.changeModule N).totalSpaceHomEquiv_zeroSection]
  exact Eq.trans (congrArg (D.totalSpaceHomEquiv D.X).symm
    (sigma_mk_congr (Limits.comp_zero (f := α.hom))))
    (Eq.trans (congrArg (D.totalSpaceHomEquiv D.X).symm
      D.totalSpaceHomEquiv_zeroSection.symm) (Equiv.symm_apply_apply _ D.zeroSection))

end Stacks.LineBundle

end
