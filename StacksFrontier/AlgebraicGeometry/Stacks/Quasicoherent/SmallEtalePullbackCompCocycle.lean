module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafifiedPullbackComparisonConjugate
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChangeCocycle

/-!
# The pushforward cocycle for the morphisms of ringed sites of Stacks 070R (2)

`AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` is the composition law
`ε_b^* ⋙ ε_a^* ≅ ε_{a ∘ b}^*` for the pullbacks of sheaves of modules along the morphisms of
ringed sites of **Stacks 070R (2)**. This file proves the cocycle condition for the corresponding
comparisons of pushforwards, read on sections, and restates the cocycle condition of
**Stacks 021J** for the base change functors as an equality of isomorphisms of functors.

## Main results

* `AlgebraicGeometry.SmallEtale.smallEtalePushforwardFactoredCompIso_assoc`: the cocycle on the
  pushforward side, read on sections.
* `AlgebraicGeometry.SmallEtale.smallEtaleBaseChange_factoredCompIso_assoc_iso`: the indexing
  cocycle of Stacks 021J as an equality of isomorphisms of functors.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {W X Y Z : B.Scheme}
  (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
  (bc : X ⟶ Z) (hbc : b ≫ c = bc) (ab : W ⟶ Y) (hab : a ≫ b = ab)
  (abc : W ⟶ Z) (habc : a ≫ bc = abc) (habc' : ab ≫ c = abc)

/-- **The cocycle condition on the pushforward side, read on sections**: restricting the sections
of `M` along the two routes of the cocycle of
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso` gives the same map. -/
public theorem smallEtalePushforwardFactoredCompIso_assoc
    (M : SheafOfModules.{u} (structureSheaf B W.obj W.property))
    (U : SmallEtale B Z.obj Z.property) :
    M.val.presheaf.map
          ((smallEtaleBaseChange_factoredCompIso B W X Z a bc abc habc).hom.app U).op ≫
        M.val.presheaf.map ((smallEtaleBaseChange B a).map
          ((smallEtaleBaseChange_factoredCompIso B X Y Z b c bc hbc).hom.app U)).op =
      M.val.presheaf.map
          ((smallEtaleBaseChange_factoredCompIso B W Y Z ab c abc habc').hom.app U).op ≫
        M.val.presheaf.map ((smallEtaleBaseChange_factoredCompIso B W X Y a b ab hab).hom.app
          ((smallEtaleBaseChange B c).obj U)).op := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
    smallEtaleBaseChange_factoredCompIso_assoc B _ _ _ _ a b c bc hbc ab hab abc habc habc' U]

/-- **The indexing cocycle of Stacks 021J as an equality of isomorphisms of functors**: the
componentwise statement `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_assoc` for the
isomorphisms `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso` themselves. -/
public theorem smallEtaleBaseChange_factoredCompIso_assoc_iso :
    isoWhiskerRight (smallEtaleBaseChange_factoredCompIso B X Y Z b c bc hbc)
          (smallEtaleBaseChange B a) ≪≫
        smallEtaleBaseChange_factoredCompIso B W X Z a bc abc habc =
      isoWhiskerLeft (smallEtaleBaseChange B c)
          (smallEtaleBaseChange_factoredCompIso B W X Y a b ab hab) ≪≫
        smallEtaleBaseChange_factoredCompIso B W Y Z ab c abc habc' :=
  Iso.ext (NatTrans.ext (funext fun U =>
    smallEtaleBaseChange_factoredCompIso_assoc B _ _ _ _ a b c bc hbc ab hab abc habc habc' U))

end AlgebraicGeometry.SmallEtale

end
