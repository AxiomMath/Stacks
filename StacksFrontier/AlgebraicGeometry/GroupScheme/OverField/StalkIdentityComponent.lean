module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.IdentitySubgroup
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local ring of a group scheme at the identity and its identity component

A flat closed immersion of schemes induces isomorphisms on all stalks: each stalk map is
surjective because the morphism is a closed immersion, and it is a flat local homomorphism,
hence faithfully flat, hence injective.  Applied to the inclusion of the identity component
`G⁰ ⟶ G` of a group scheme over a field, which is a flat closed immersion carrying the identity
to the identity, this identifies the local ring of `G` at the identity with that of `G⁰`.

## Main results

* `AlgebraicGeometry.isIso_stalkMap_of_isClosedImmersion_of_flat`: a flat closed immersion
  induces isomorphisms on stalks.
* `AlgebraicGeometry.identityComponent_ι_identityPoint`: the inclusion of the identity component
  sends its identity point to the identity point of `G`.
* `AlgebraicGeometry.stalkIdentityComponentIso`: the stalk of `G` at the identity is isomorphic
  to the stalk of its identity component at the identity.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

/-- A flat closed immersion induces an isomorphism on every stalk. -/
theorem isIso_stalkMap_of_isClosedImmersion_of_flat {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [Flat i] (z : Z) : IsIso (i.stalkMap z) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨?_, i.stalkMap_surjective z⟩
  algebraize [(i.stalkMap z).hom]
  have : Module.FaithfullyFlat (X.presheaf.stalk (i z)) (Z.presheaf.stalk z) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap i z) (i.toLRSHom.prop z)
  exact ‹RingHom.FaithfullyFlat _›.injective

/-- The inclusion of the identity component sends its identity point to the identity point
of the ambient group scheme. -/
theorem identityComponent_ι_identityPoint (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) :
    (identityComponent k G).ι.hom.hom.left
        (identityPoint k (identityComponent k G).carrier) = identityPoint k G := by
  have h : η[(identityComponent k G).carrier.X] ≫ (identityComponent k G).ι.hom.hom =
      η[G.X] := IsMonHom.one_hom _
  have h' := congrArg (fun f => f.left) h
  simp only [Over.comp_left] at h'
  show ((η[(identityComponent k G).carrier.X]).left ≫
      (identityComponent k G).ι.hom.hom.left) _ = _
  rw [h']

/-- The local ring of a group scheme over a field at its identity is isomorphic to the local
ring of its identity component at the identity. -/
@[sga "3 VIA 6.9" "identification O_{G"]
noncomputable def stalkIdentityComponentIso (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) :
    G.X.left.presheaf.stalk (identityPoint k G) ≅
      (identityComponent k G).carrier.X.left.presheaf.stalk
        (identityPoint k (identityComponent k G).carrier) :=
  let i := (identityComponent k G).ι.hom.hom.left
  have : IsClosedImmersion i := (identityComponent k G).isClosedImmersion
  have : Flat i := identityComponent_flat k G
  have := isIso_stalkMap_of_isClosedImmersion_of_flat i
    (identityPoint k (identityComponent k G).carrier)
  G.X.left.presheaf.stalkCongr
      (Inseparable.of_eq (identityComponent_ι_identityPoint k G).symm) ≪≫
    asIso (i.stalkMap (identityPoint k (identityComponent k G).carrier))

end AlgebraicGeometry

end
