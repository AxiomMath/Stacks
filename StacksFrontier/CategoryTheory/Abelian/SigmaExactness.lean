module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-!
# Exactness of coproducts of short complexes

In an abelian category in which coproducts of a given shape are exact — Grothendieck's axiom
AB4 for that shape — a family of exact short complexes has exact coproduct. This file records
that statement in the form a family `A i ⟶ B i ⟶ D i` of short complexes needs it, together
with the bookkeeping that lets a coproduct indexed by `ℕ` be re-read after a shift of the
index.

## Main results

* `Stacks.SigmaExactness.exact_of_app`: a short complex of functors is exact as soon as all of
  its evaluations are, because the evaluation functors are jointly faithful.
* `Stacks.SigmaExactness.exact_sigmaMap`: the coproduct of a family of exact short complexes is
  exact.
* `Stacks.SigmaExactness.exact_comp_eqToHom`, `Stacks.SigmaExactness.exact_eqToHom_comp`:
  exactness is unaffected by transporting one end of a short complex along an equality of
  indices.
* `Stacks.SigmaExactness.exact_of_exact_map`: a faithful exact functor reflects exactness.

## Implementation notes

Exactness of the coproduct is read off Mathlib's `HasExactColimitsOfShape`, which says that
`colim : (J ⥤ C) ⥤ C` preserves finite limits and hence is exact. A family of short complexes
is assembled into a short complex of functors on `Discrete I`, where exactness is checked
evaluation by evaluation, and `CategoryTheory.Limits.colim.exact_mapShortComplex` transports it
to the coproduct cocones of the colimit API.

The transport lemmas are stated with the `eqToHom` on the left of the composite it meets, which
is the association in which a composite of a connecting morphism with such a transport is met.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace Stacks.SigmaExactness

/-- **A short complex of functors is exact if all of its evaluations are.** The evaluation
functors are jointly faithful, hence jointly reflect isomorphisms, and exactness of a short
complex is reflected by a jointly isomorphism-reflecting family of exact functors. -/
theorem exact_of_app {J C : Type*} [Category J] [Category C] [Abelian C]
    (S : ShortComplex (J ⥤ C))
    (h : ∀ j : J, (S.map ((evaluation J C).obj j)).Exact) : S.Exact := by
  have hfaith : JointlyFaithful (fun j : J => (evaluation J C).obj j) := by
    constructor
    intro X Y f g hfg
    ext j
    exact hfg j
  exact (hfaith.jointlyReflectsIsomorphisms.exact_iff S).2 h

/-- **Exact colimits carry a pointwise exact short complex of functors to an exact short
complex**, read at the colimit cocones of the colimit API, which is the shape in which
coproducts are met. -/
theorem exact_colimMap {J C : Type*} [Category J] [Category C] [Abelian C]
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] (S : ShortComplex (J ⥤ C))
    (h : ∀ j : J, (S.map ((evaluation J C).obj j)).Exact) :
    (colim.mapShortComplex S (colimit.isColimit S.X₁) (colimit.cocone S.X₂)
      (colimit.cocone S.X₃) (colimMap S.f) (colimMap S.g)
      (fun j => ι_colimMap S.f j) (fun j => ι_colimMap S.g j)).Exact :=
  colim.exact_mapShortComplex (exact_of_app S h) (colimit.isColimit S.X₁)
    (colimit.isColimit S.X₂) (colimit.isColimit S.X₃) (colimMap S.f) (colimMap S.g)
    (fun j => ι_colimMap S.f j) (fun j => ι_colimMap S.g j)

/-- **The coproduct of a family of exact short complexes is exact**, in an abelian category
whose coproducts of that shape are exact. -/
theorem exact_sigmaMap {I C : Type*} [Category C] [Abelian C]
    [HasCoproductsOfShape I C] [HasExactColimitsOfShape (Discrete I) C]
    (A B D : I → C) (f : ∀ i, A i ⟶ B i) (g : ∀ i, B i ⟶ D i)
    (hzero : ∀ i, f i ≫ g i = 0)
    (hexact : ∀ i, (ShortComplex.mk (f i) (g i) (hzero i)).Exact) :
    (ShortComplex.mk (Limits.Sigma.map f) (Limits.Sigma.map g) (by
      rw [Limits.Sigma.map_comp_map]
      exact Limits.Sigma.hom_ext _ _ fun i => by simp [hzero i])).Exact := by
  let S : ShortComplex (Discrete I ⥤ C) :=
    ShortComplex.mk
      (Discrete.natTrans (F := Discrete.functor A) (G := Discrete.functor B) fun i => f i.as)
      (Discrete.natTrans (F := Discrete.functor B) (G := Discrete.functor D) fun i => g i.as)
      (by ext i; simpa using hzero i.as)
  have hp (i : Discrete I) : (S.map ((evaluation (Discrete I) C).obj i)).Exact := by
    convert hexact i.as using 1; rfl
  convert exact_colimMap S hp using 1
  rfl

/-- The family `B` shifted up by one, with a zero object in degree `0`. Its coproduct is the
coproduct of `B` with one summand split off, and it is the index family in which a connecting
morphism landing one degree up is met. -/
noncomputable def shiftZero {C : Type*} [Category C] [HasZeroObject C] (B : ℕ → C) : ℕ → C :=
  fun n => match n with | 0 => (0 : C) | i + 1 => B i

/-- Transporting the target of a morphism along an equality of indices does not change the
vanishing of its composite with a map out of that target. -/
theorem comp_eqToHom_eq_zero {I C : Type*} [Category C] [HasZeroMorphisms C]
    {A B : I → C} {i j : I} (p : i = j) {X : C} (a : X ⟶ A i) (b : ∀ k, A k ⟶ B k)
    (h : a ≫ b i = 0) : (a ≫ eqToHom (congrArg A p)) ≫ b j = 0 := by
  cases p; simpa using h

/-- Exactness of a short complex is unaffected by transporting its right-hand end along an
equality of indices. -/
theorem exact_comp_eqToHom {I C : Type*} [Category C] [Abelian C] {D : I → C} {i j : I}
    (p : i = j) {X Y : C} (a : X ⟶ Y) (b : Y ⟶ D i) (hab : a ≫ b = 0)
    (he : (ShortComplex.mk a b hab).Exact) :
    (ShortComplex.mk a (b ≫ eqToHom (congrArg D p))
      (by rw [← Category.assoc, hab, zero_comp])).Exact := by
  cases p; convert he using 1; simp

/-- Exactness of a short complex is unaffected by transporting its middle term along an
equality of indices. -/
theorem exact_eqToHom_comp {I C : Type*} [Category C] [Abelian C] {A B : I → C} {i j : I}
    (p : i = j) {X : C} (a : X ⟶ A i) (b : ∀ k, A k ⟶ B k) (hab : a ≫ b i = 0)
    (he : (ShortComplex.mk a (b i) hab).Exact) :
    (ShortComplex.mk (a ≫ eqToHom (congrArg A p)) (b j)
      (comp_eqToHom_eq_zero p a b hab)).Exact := by
  cases p; convert he using 1; simp

/-- **A faithful exact functor reflects exactness.** -/
theorem exact_of_exact_map {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.Faithful]
    (S : ShortComplex A) (h : (S.map F).Exact) : S.Exact :=
  (S.exact_map_iff_of_faithful F).1 h

end Stacks.SigmaExactness

end
