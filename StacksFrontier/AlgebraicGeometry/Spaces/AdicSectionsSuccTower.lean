module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicInternalHom
public import StacksFrontier.Algebra.Module.SuccTowerSections

/-!
# The inverse limit of the sections over a chart is the compatible sequences of a tower of types

`AlgebraicGeometry.Space.adicSectionsAt` is the inverse limit of the sections over one étale
chart of an inverse system of `𝒪_F`-modules presented by its successor transitions, and
`StacksFrontier.Algebra.Module.SuccTowerSections` is the same construction for a tower of bare
types.  The two are definitionally equal, and so are the maps induced by a morphism of systems;
this file says so once, with the system abstract, and transports the one statement a comparison
of two inverse limits needs across the identification.

## Main results

* `AlgebraicGeometry.Space.adicSectionsMapAt_eq_sectionsMap` — **the map induced on the inverse
  limits of the sections over a chart is `Stacks.SuccTower.sectionsMap` of its components.**
* `AlgebraicGeometry.Space.bijective_adicSectionsMapAt_of_congr` — **bijectivity on the inverse
  limits of the sections over a chart transports across a levelwise equivalence with a tower of
  types.**

## Implementation notes

The transport goes from the tower statement to the sheaf statement: a module-theoretic
comparison arrives as `Stacks.SuccTower.bijective_sectionsMap_of_congr`, whose conclusion is about
`Stacks.SuccTower.sectionsMap`, while the chartwise hypothesis of Stacks 08B6 is about
`AlgebraicGeometry.Space.adicSectionsMapAt`.

Both statements keep the inverse system abstract, and that is the point of the file rather than
a matter of taste.  `AlgebraicGeometry.Space.adicSectionsAt` has to be unfolded against the
subtype of compatible sequences for either to typecheck; underneath a *concrete* system — the
adic quotients of an internal Hom, say — that single unfolding exhausts the heartbeat budget,
while with nothing concrete in sight it costs nothing.

## References

* [Stacks Project, Tag 08B6](https://stacks.math.columbia.edu/tag/08B6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (X Y : ℕ → Modules.{u, m} B S hS F hF) (trX : ∀ n, X (n + 1) ⟶ X n)
    (trY : ∀ n, Y (n + 1) ⟶ Y n) (β : ∀ n : ℕ, X n ⟶ Y n)
    (hβ : ∀ n : ℕ, trX n ≫ β n = β (n + 1) ≫ trY n)
    (U : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ)

/-- **The map induced on the inverse limits of the sections over a chart is
`Stacks.SuccTower.sectionsMap` of its components.**  By `rfl`: both send a compatible sequence to
the sequence of the images of its terms, and the two compatibility witnesses are collapsed by
proof irrelevance. -/
theorem adicSectionsMapAt_eq_sectionsMap :
    adicSectionsMapAt B S hS F hF X Y trX trY β hβ U =
      Stacks.SuccTower.sectionsMap (fun n x => (trX n).val.app U x)
        (fun n y => (trY n).val.app U y) (fun n x => (β n).val.app U x)
        (fun n x => congrArg (fun k : X (n + 1) ⟶ Y n => k.val.app U x) (hβ n)) :=
  rfl

/-- **Bijectivity on the inverse limits of the sections over a chart transports across a levelwise
equivalence with a tower of types.**

This is `Stacks.SuccTower.bijective_sectionsMap_of_congr` read at
`AlgebraicGeometry.Space.adicSectionsMapAt`: if the sections of the two systems over the chart are
levelwise equivalent to a tower of types, compatibly with the transition maps and with the two
maps, and the tower map is bijective on compatible sequences, then the morphism of systems is
bijective on the inverse limits of the sections over the chart. -/
theorem bijective_adicSectionsMapAt_of_congr {T' U' : ℕ → Type w}
    {t' : ∀ n, T' (n + 1) → T' n} {u' : ∀ n, U' (n + 1) → U' n} {ψ' : ∀ n, T' n → U' n}
    {hψ' : ∀ (n : ℕ) (x : T' (n + 1)), ψ' n (t' n x) = u' n (ψ' (n + 1) x)}
    (h : Function.Bijective (Stacks.SuccTower.sectionsMap t' u' ψ' hψ'))
    (a : ∀ n, (X n).val.obj U ≃ T' n)
    (ha : ∀ (n : ℕ) (x : (X (n + 1)).val.obj U),
      a n ((trX n).val.app U x) = t' n (a (n + 1) x))
    (b : ∀ n, (Y n).val.obj U ≃ U' n)
    (hb : ∀ (n : ℕ) (y : (Y (n + 1)).val.obj U),
      b n ((trY n).val.app U y) = u' n (b (n + 1) y))
    (hsq : ∀ (n : ℕ) (x : (X n).val.obj U), b n ((β n).val.app U x) = ψ' n (a n x)) :
    Function.Bijective (adicSectionsMapAt B S hS F hF X Y trX trY β hβ U) :=
  Stacks.SuccTower.bijective_sectionsMap_of_congr
    (fun n x => (trX n).val.app U x) (fun n y => (trY n).val.app U y) t' u'
    (fun n x => (β n).val.app U x)
    (fun n x => congrArg (fun k : X (n + 1) ⟶ Y n => k.val.app U x) (hβ n)) ψ' hψ' a ha b hb hsq h

end AlgebraicGeometry.Space

end
