module

public import StacksFrontier.CategoryTheory.Adjunction.MateTransportCocycle
public import StacksFrontier.CategoryTheory.Adjunction.UnitOfRightAdjointIsoId

/-!
# A comparison of left adjoints conjugated by an equivalence, at the unit

`StacksFrontier/CategoryTheory/Adjunction/MateTransportCocycle.lean` builds, from a comparison
`cmp : B ⋙ E.functor ≅ E'.functor ⋙ A` of the two routes round a square of right adjoints, the
comparison `Stacks.CategoryTheory.transportedComparisonApp` of the two routes round the square
of their left adjoints, and shows that a system of such comparisons composes as soon as the
system of the `cmp`s does.  That is the composition law; this file is the **unit law** of the
same system.

Suppose one square of the system is degenerate: the two equivalences are the same `E`, and both
right adjoints are identified with the identity functor, `eA : A ≅ 𝟭` and `eB : B ≅ 𝟭`, so that
`cmp` is the comparison those two identifications force.  Then the comparison of the left
adjoints is the one the two identifications force as well: the identification
`CategoryTheory.Adjunction.leftAdjointIdIso` of `a` with the identity functor, followed by the
image under `E.functor` of the inverse of the identification of `b`.

Nothing is computed.  Both sides are morphisms out of a value of the left adjoint `a`, hence
determined by their transposes along `α : a ⊣ A`; the transpose of the left-hand side is
`Stacks.CategoryTheory.homEquiv_transportedComparison` and the transpose of each factor of the
right-hand side is `CategoryTheory.Adjunction.unit_comp_map_leftAdjointIdIso_hom_app`, and what
is left is one naturality square of `eA.inv` together with
`CategoryTheory.Adjunction.leftAdjointIdIso_inv_eq_unitToLeftAdjoint`, which says that the
inverse of the comparison of the left adjoints is the unit read through `eB`.

## Main results

* `Stacks.CategoryTheory.transportedComparisonApp_of_idIso`: **the unit law for the system of
  comparisons** — the transported comparison of a degenerate square is the comparison the two
  identifications of the right adjoints with the identity functor force.

## Implementation notes

The hypothesis on `cmp` is taken **at a component**, as
`∀ Y, cmp.hom.app Y = E.functor.map (eB.hom.app Y) ≫ eA.inv.app (E.functor.obj Y)`, rather than
as an equation of isomorphisms between `cmp` and a whiskered composite.  A consumer holding a
geometric `cmp` proves the component equation at the spelling its own factors have, with no
unitor bookkeeping; and the proof below needs `cmp` at exactly one component, so taking the
hypothesis there costs nothing and spares the consumer the two unitors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace Stacks.CategoryTheory

/-- **The unit law for a system of comparisons of left adjoints conjugated by equivalences.**

Let `E : M ≌ N` be an equivalence, let `α : a ⊣ A` be an adjunction between endofunctors of `N`
and `β : b ⊣ B` one between endofunctors of `M`, and let `eA : A ≅ 𝟭 N` and `eB : B ≅ 𝟭 M`
identify the two right adjoints with the identity functors.  If the comparison
`cmp : B ⋙ E.functor ≅ E.functor ⋙ A` of the two routes round the square of right adjoints is
the one `eA` and `eB` force, then the comparison
`Stacks.CategoryTheory.transportedComparisonApp` of the two routes round the square of the left
adjoints is the one they force: the identification of `a` with the identity functor, followed by
the image under `E.functor` of the inverse of the identification of `b`.

Both sides are morphisms out of `a (E X)`, so it suffices that their transposes along `α` agree;
see the module documentation. -/
theorem transportedComparisonApp_of_idIso {M N : Type*} [Category* M] [Category* N]
    (E : M ≌ N) {a A : N ⥤ N} (α : a ⊣ A) {b B : M ⥤ M} (β : b ⊣ B)
    (cmp : B ⋙ E.functor ≅ E.functor ⋙ A) (eA : A ≅ 𝟭 N) (eB : B ≅ 𝟭 M)
    (hcmp : ∀ Y, cmp.hom.app Y =
      E.functor.map (eB.hom.app Y) ≫ eA.inv.app (E.functor.obj Y)) (X : M) :
    transportedComparisonApp E E α β cmp X =
      (Adjunction.leftAdjointIdIso α eA).hom.app (E.functor.obj X) ≫
        E.functor.map ((Adjunction.leftAdjointIdIso β eB).inv.app X) := by
  refine (α.homEquiv (E.functor.obj X) (E.functor.obj (b.obj X))).injective ?_
  have hnat := eA.inv.naturality
    (E.functor.map ((Adjunction.leftAdjointIdIso β eB).inv.app X))
  simp only [Functor.id_obj, Functor.id_map] at hnat
  rw [transportedComparisonApp, homEquiv_transportedComparison E E α β cmp X, hcmp (b.obj X),
    Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit,
    Adjunction.unit_comp_map_leftAdjointIdIso_hom_app, ← hnat,
    Adjunction.leftAdjointIdIso_inv_eq_unitToLeftAdjoint, Adjunction.unitToLeftAdjoint_app,
    Functor.map_comp, Category.assoc]

end Stacks.CategoryTheory

end
