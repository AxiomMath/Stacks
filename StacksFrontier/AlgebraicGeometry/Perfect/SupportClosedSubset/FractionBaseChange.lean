module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechComplexBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedFractionMap

/-!
# Base change of the fraction morphism along an open immersion

Let `X` be a scheme, `f₁, …, f_c ∈ Γ(X, 𝒪_X)`, `ℱ` an `𝒪_X`-module and `g : X' ⟶ X` an open
immersion.  The class map of [Stacks, Tag 0G7Q] is built from the morphism
`ℱ ⟶ ∏_{i₀<⋯<i_p} ℱ_{i₀…i_p}` sending a section `s` to the cochain of fractions
`s / (f_{i₀} ⋯ f_{i_p})`.  This file proves that that morphism is local: its restriction along
`g`, followed by the degreewise comparison
`Stacks.Perfect.PushforwardRestrict.restrictProdTermIso` of the two extended alternating Čech
complexes, is the fraction morphism of the pulled-back equations with coefficients in `g^*ℱ`.

## Main results

* `fractionCochain_restrict`: **the fraction cochain is local**, the comparison carrying it to
  the fraction cochain of the restricted equations.
* `restrictFunctor_map_fractionHom`: **the fraction morphism is local**, the same statement as a
  commuting square of morphisms of modules.

## Implementation notes

The numerator is handled by the degreewise comparison on sections, which is a restriction map
of `ℱ` because the underlying presheaf of `Scheme.Modules.restrictFunctor g` is
`g.opensFunctor.op ⋙ X.presheaf` for every open immersion `g`.

**The denominator is the one place in the whole base change where an open immersion differs
from the inclusion of an open subscheme.**  It is a section of the structure sheaf acting as a
scalar, and the comparison `AlgebraicGeometry.Scheme.Hom.appIso` of the two structure sheaves —
the identity for `W.ι` by `AlgebraicGeometry.Scheme.Opens.ι_appIso`, a genuine isomorphism for a
general `g` — stands between the two actions.  Three small lemmas absorb it: `restrict_smul_eq`
rewrites the action of `Γ(X', A)` on `Γ(g^*ℱ, A)` as the action of its image under
`(g.appIso A).inv` on `Γ(ℱ, g ''ᵁ A)`, `appTop_restrict` identifies the pulled-back and
restricted global section across the same comparison (Mathlib's
`AlgebraicGeometry.Scheme.Hom.appLE_appIso_inv`), and `hom_ringInverse` carries the comparison
through `Ring.inverse`, the denominator being a unit.

Everything here is for an **open immersion**; the termwise comparison it rests on is not
available for a general morphism.

## References

* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.SupportedFraction
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.PushforwardRestrict

/-- A restriction map of the structure sheaf of the source of an open immersion is, across the
comparison `AlgebraicGeometry.Scheme.Hom.appIso` of the two structure sheaves, a restriction map
of the structure sheaf of the target. -/
public theorem opens_presheaf_map {Z Z' : Scheme.{u}} (l : Z' ⟶ Z) [IsOpenImmersion l]
    {A B : Z'.Opens} (φ : B ⟶ A) (h : l ''ᵁ B ⟶ l ''ᵁ A) (y : Γ(Z', A)) :
    (l.appIso B).inv (Z'.presheaf.map φ.op y) =
      Z.presheaf.map h.op ((l.appIso A).inv y) := by
  rw [Subsingleton.elim h (l.opensFunctor.map φ), ← CommRingCat.comp_apply,
    Scheme.Hom.appIso_inv_naturality l φ.op, CommRingCat.comp_apply]
  rfl

/-- Two restriction maps of the structure sheaf between the same two opens agree. -/
public theorem ringMap_eq_apply {Z : Scheme.{u}} {A B : Z.Opens} (φ ψ : B ⟶ A) (r : Γ(Z, A)) :
    Z.presheaf.map φ.op r = Z.presheaf.map ψ.op r := by
  rw [Subsingleton.elim φ ψ]

/-- A global section pulled back along an open immersion and then restricted to an open of the
source is, across `AlgebraicGeometry.Scheme.Hom.appIso`, its restriction in the target. -/
public theorem appTop_restrict {Z Z' : Scheme.{u}} (l : Z' ⟶ Z) [IsOpenImmersion l]
    (A : Z'.Opens) (a : Γ(Z, ⊤)) (h : l ''ᵁ A ⟶ (⊤ : Z.Opens)) :
    (l.appIso A).inv (Z'.presheaf.map (homOfLE (le_top (a := A))).op (l.appTop a)) =
      Z.presheaf.map h.op a := by
  have e : A ≤ l ⁻¹ᵁ (⊤ : Z.Opens) := fun _ _ => trivial
  refine Eq.trans (congr($(Scheme.Hom.appLE_appIso_inv l e) a)) ?_
  exact ringMap_eq_apply _ h a

variable {X X' : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)) (g : X' ⟶ X)
  [IsOpenImmersion g] (F : X.Modules)

/-- Scaling equal sections by equal scalars. -/
public theorem smul_congr {Z : Scheme.{u}} (N : Z.Modules) {A : Z.Opens}
    {r r' : Γ(Z, A)} {y y' : Γ(N, A)} (hr : r = r') (hy : y = y') : r • y = r' • y' := by
  rw [hr, hy]

omit [IsOpenImmersion g] in
/-- The product of the restricted equations is the restriction of the product. -/
public theorem prod_appTop (p : ℕ) (q : CechCochains.OrdIndex (I := Fin c) p) :
    (∏ k, g.appTop (f (q.1 k))) = g.appTop (∏ k, f (q.1 k)) :=
  (map_prod (CommRingCat.Hom.hom g.appTop) (fun k => f (q.1 k)) Finset.univ).symm

/-- A morphism of commutative rings carries the inverse of a unit to the inverse of its image:
the inverse of a unit in a monoid is unique.  This is `map_ringInverse` for the comparison
`AlgebraicGeometry.Scheme.Hom.appIso` of the two structure sheaves of an open immersion, which
is not a restriction map. -/
public theorem hom_ringInverse {A B : CommRingCat.{u}} (φ : A ⟶ B) {r : A} (h : IsUnit r) :
    φ (Ring.inverse r) = Ring.inverse (φ r) := by
  obtain ⟨v, rfl⟩ := h
  rw [Ring.inverse_unit]
  have himage : φ (v : A) = ((Units.map (φ.hom : A →* B) v : B) : B) := rfl
  rw [himage, Ring.inverse_unit]
  rfl

/-- **The action of the structure sheaf of the source on a restricted module.**  A section of
`𝒪_{Z'}` acts on the sections of `l^*N` as its image under
`AlgebraicGeometry.Scheme.Hom.appIso` acts on the sections of `N`.  For `l` the inclusion of an
open subscheme that comparison is the identity and the two actions agree on the nose; for a
general open immersion it is the one place in the base change where more than the underlying
functor of images of opens is used. -/
public theorem restrict_smul_eq {Z Z' : Scheme.{u}} (l : Z' ⟶ Z) [IsOpenImmersion l]
    (N : Z.Modules) (A : Z'.Opens) (r : Γ(Z', A))
    (y : Γ((Scheme.Modules.restrictFunctor l).obj N, A)) :
    (r • y : Γ((Scheme.Modules.restrictFunctor l).obj N, A)) =
      ((l.appIso A).inv r • (show Γ(N, l ''ᵁ A) from y) : Γ(N, l ''ᵁ A)) :=
  Scheme.Modules.smul_restrictAppIso_hom_apply l N A r y

/-- The denominator of the fraction cochain of the restricted equations is, across the
comparison `AlgebraicGeometry.Scheme.Hom.appIso` of the two structure sheaves, the denominator
of the fraction cochain of the equations. -/
public theorem denominator_restrict (p : ℕ) (V : X'.Opens)
    (q : CechCochains.OrdIndex (I := Fin c) p) :
    (g.appIso (CechCochains.inter
          (fun i => V ⊓ X'.basicOpen (g.appTop (f i))) q.1)).inv
        (X'.presheaf.map (homOfLE (show CechCochains.inter
            (fun i => V ⊓ X'.basicOpen (g.appTop (f i))) q.1 ≤ ⊤ from le_top)).op
          (∏ k, g.appTop (f (q.1 k)))) =
      X.presheaf.map (eqToHom (inter_image f g V p q)).op
        (X.presheaf.map (homOfLE (show
            CechCochains.inter (fun i => (g ''ᵁ V) ⊓ X.basicOpen (f i)) q.1 ≤ ⊤
              from le_top)).op (∏ k, f (q.1 k))) := by
  refine Eq.trans (congrArg
    (fun a => (g.appIso (CechCochains.inter
        (fun i => V ⊓ X'.basicOpen (g.appTop (f i))) q.1)).inv
      (X'.presheaf.map (homOfLE (show CechCochains.inter
        (fun i => V ⊓ X'.basicOpen (g.appTop (f i))) q.1 ≤ ⊤ from le_top)).op a))
    (prod_appTop f g p q)) ?_
  refine Eq.trans (appTop_restrict g _ (∏ k, f (q.1 k))
    (homOfLE (le_top (a := g ''ᵁ (CechCochains.inter
      (fun i => V ⊓ X'.basicOpen (g.appTop (f i))) q.1))))) ?_
  exact (ringMap_collapse _ _ _ _).symm

/-- **Base change of the fraction cochain of [Stacks, Tag 0G7Q] along an open immersion.** -/
public theorem fractionCochain_restrict (p : ℕ) (V : X'.Opens)
    (x : Γ(F, g ''ᵁ V)) (q : CechCochains.OrdIndex (I := Fin c) p) :
    fractionCochain (fun j => g.appTop (f j))
        ((Scheme.Modules.restrictFunctor g).obj F) p V x q =
      F.presheaf.map (eqToHom (inter_image f g V p q)).op
        (fractionCochain f F p (g ''ᵁ V) x q) := by
  refine Eq.trans (fractionCochain_apply (fun j => g.appTop (f j))
    ((Scheme.Modules.restrictFunctor g).obj F) p V x q) ?_
  refine Eq.trans ?_ (map_congr F (eqToHom (inter_image f g V p q))
    (fractionCochain_apply f F p (g ''ᵁ V) x q)).symm
  refine Eq.trans ?_ (Scheme.Modules.map_smul F
    (eqToHom (inter_image f g V p q)) _ _).symm
  refine Eq.trans (restrict_smul_eq g F _ _ _) ?_
  refine smul_congr F ?_ ?_
  · refine Eq.trans ?_ (map_ringInverse (eqToHom (inter_image f g V p q))
      (isUnit_prodEquations f (g ''ᵁ V) p q)).symm
    refine Eq.trans (hom_ringInverse _
      (isUnit_prodEquations (fun j => g.appTop (f j)) V p q)) ?_
    exact congrArg Ring.inverse (denominator_restrict f g p V q)
  · refine Eq.trans (restrictFunctor_presheaf_map g F
      (homOfLE (interLe (fun j => g.appTop (f j)) p q V))
      (homOfLE (Scheme.Hom.image_mono g
        (interLe (fun j => g.appTop (f j)) p q V))) x) ?_
    exact (collapse2 F _ _ _ x).symm

/-- **Base change of the fraction morphism of [Stacks, Tag 0G7Q] along an open immersion.**
The restriction along `g` of the morphism `ℱ ⟶ ∏ ℱ_{i₀…i_p}` dividing a section by the product
of the equations, followed by the degreewise comparison of the two complexes, is the same
morphism for the pulled-back equations. -/
public theorem restrictFunctor_map_fractionHom (p : ℕ) :
    (Scheme.Modules.restrictFunctor g).map (fractionHom f F p) ≫
        (restrictProdTermIso f g F p).hom =
      fractionHom (fun j => g.appTop (f j))
        ((Scheme.Modules.restrictFunctor g).obj F) p := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
  refine (secIso (fun j => g.appTop (f j))
    ((Scheme.Modules.restrictFunctor g).obj F) p V).injective ?_
  funext q
  refine Eq.trans (secIso_restrictProdTermIso f g F p V
    ((fractionHom f F p).app (g ''ᵁ V) x) q) ?_
  refine Eq.trans (map_congr F (eqToHom (inter_image f g V p q))
    (fractionHom_secIso f F p (g ''ᵁ V) x q)) ?_
  exact ((fractionHom_secIso (fun j => g.appTop (f j))
    ((Scheme.Modules.restrictFunctor g).obj F) p V x q).trans
      (fractionCochain_restrict f g F p V x q)).symm

end Stacks.Perfect.PushforwardRestrict

end
