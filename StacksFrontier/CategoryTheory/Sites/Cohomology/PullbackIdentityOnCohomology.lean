module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Adjunction.UnitOfRightAdjointIsoId

/-!
# A pullback whose pushforward is the identity induces the identity on cohomology

Let `(C, J)` be a site and let `adj : L ⊣ R` be an adjunction between endofunctors of the
category of abelian sheaves on it, with `i : R ≅ 𝟭` identifying the right adjoint with the
identity functor. This is the situation of a self-map of the site which is isomorphic to the
identity: `L` is the inverse image and `R` the direct image.

The map such a self-map induces on cohomology is `H^n(F) → H^n(L F)`, the map induced by the
unit `F ⟶ R (L F) ≅ L F` of the adjunction read through `i`; this is the usual pullback on
cohomology, the edge map of the Leray spectral sequence of a direct image which is identified
with the identity functor. Composed with the comparison `L F ≅ F` of
`CategoryTheory.Adjunction.leftAdjointIdIso` it is the identity of `H^n(F)`: the self-map
induces the identity on cohomology, in every degree and for every sheaf.

## Main definitions

* `Stacks.Cohomology.cohomologyPullbackMap` — the map `H^n(F) → H^n(L F)` induced by the unit
  of the adjunction.

## Main results

* `Stacks.Cohomology.cohomologyPullbackMap_comp_leftAdjointIdIso` — that map, followed by the
  comparison of `L` with the identity functor, is the identity of `H^n(F)`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w' w v u

namespace Stacks.Cohomology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  {L R : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w}}

/-- The map on cohomology induced by an adjunction `adj : L ⊣ R` of endofunctors of abelian
sheaves whose right adjoint is identified with the identity functor by `i : R ≅ 𝟭`: the map
`H^n(F) → H^n(L F)` induced by the unit `F ⟶ R (L F) ≅ L F`. -/
def cohomologyPullbackMap (adj : L ⊣ R) (i : R ≅ 𝟭 _)
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    Sheaf.H.{w'} F n →+ Sheaf.H.{w'} (L.obj F) n :=
  Sheaf.H.map ((Adjunction.unitToLeftAdjoint adj i).app F) n

/-- **The map induced on cohomology by a pullback whose pushforward is the identity functor is
the identity**: the map `H^n(F) → H^n(L F)` induced by the unit of `adj : L ⊣ R`, followed by
the comparison `L F ≅ F` induced by `i : R ≅ 𝟭`, is the identity of `H^n(F)`, in every degree
`n` and for every abelian sheaf `F`. -/
theorem cohomologyPullbackMap_comp_leftAdjointIdIso (adj : L ⊣ R) (i : R ≅ 𝟭 _)
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    (Sheaf.H.map ((Adjunction.leftAdjointIdIso adj i).hom.app F) n).comp
        (cohomologyPullbackMap.{w'} adj i F n) = AddMonoidHom.id (Sheaf.H.{w'} F n) := by
  ext x
  rw [AddMonoidHom.comp_apply, cohomologyPullbackMap, ← Sheaf.H.map_comp_apply,
    Adjunction.unitToLeftAdjoint_comp_leftAdjointIdIso_hom_app]
  simp

end Stacks.Cohomology

end
