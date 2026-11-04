module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationNormalisation
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationTransitivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartThickeningRelation

/-!
# The thickened presentation of a square-zero extension

Let `E` be a square-zero extension of the small étale structure sheaf of an algebraic space `X`
by a quasi-coherent ideal (the data of Stacks 05ZT) and `X = U/R` an étale presentation. Reading
`U`, `R` and the composable pairs `R ×_U R` as étale charts of `X`, the chart thickenings
`R' ⇉ U'` of the two legs form an equivalence relation of schemes, with the thickenings of the
diagonal, of the symmetry and of the composition. This is the second paragraph of the proof of
Stacks 05ZT: "applying the functor above we obtain an étale equivalence relation
`s', t' : R' → U'`".

## Main definitions

* `AlgebraicGeometry.Space.SquareZeroExtension.presentationThickeningEquivalenceRelation`: the
  chart thickenings `t', s' : R' ⇉ U'` of the two legs of an étale presentation form an
  equivalence relation of schemes.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.presentation_legs_jointlyMono`: the two legs of an
  étale presentation are jointly monic on the underlying schemes.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
variable (P : Presentation B S hS X.obj X.property)

/-- The two legs of an étale presentation are jointly monic on the underlying schemes, against
every scheme. -/
theorem presentation_legs_jointlyMono {T : Scheme.{u}}
    (a b : T ⟶ chartScheme (presentationRelationChart P))
    (ht : a ≫ chartSchemeMap (presentationRelationTargetHom P) =
      b ≫ chartSchemeMap (presentationRelationTargetHom P))
    (hs : a ≫ chartSchemeMap (presentationRelationSourceHom P) =
      b ≫ chartSchemeMap (presentationRelationSourceHom P)) : a = b := by
  let R' := (Over.post B.inclusion).obj P.R
  let T' : Over _ := Over.mk (a ≫ R'.hom)
  have hR : R'.hom = ((Over.post B.inclusion).map P.target).left ≫
      ((Over.post B.inclusion).obj P.U).hom :=
    (Over.w ((Over.post B.inclusion).map P.target)).symm
  let a' : T' ⟶ R' := Over.homMk a rfl
  let b' : T' ⟶ R' := Over.homMk b (by
    show b ≫ R'.hom = a ≫ R'.hom
    rw [hR]
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) ht.symm)).trans
      (Category.assoc _ _ _))
  have e : a' = b' := (presentationEquivalenceRelation P).right_cancellation a' b'
    (Over.OverMorphism.ext ht) (Over.OverMorphism.ext hs)
  exact congrArg (fun m ↦ m.left) e

/-- **The thickened presentation is an equivalence relation**: the chart thickenings
`t', s' : R' ⇉ U'` of the two legs of an étale presentation `X = U/R` form an equivalence
relation of schemes. -/
noncomputable def presentationThickeningEquivalenceRelation :
    EquivalenceRelation (E.chartRealizedSchemeMap (presentationRelationTargetHom P))
      (E.chartRealizedSchemeMap (presentationRelationSourceHom P)) :=
  E.chartRealizedSchemeEquivalenceRelation (presentationRelationTargetHom P)
    (presentationRelationSourceHom P) (presentation_legs_jointlyMono P)
    (presentationRelationDiagHom P)
    (hom_ext_of_toScheme_map_eq B S hS
      (congrArg (BigFppfOver.toScheme B S hS).map (presentationDiag_comp_target P)))
    (hom_ext_of_toScheme_map_eq B S hS
      (congrArg (BigFppfOver.toScheme B S hS).map (presentationDiag_comp_source P)))
    (presentationRelationSymHom P)
    (hom_ext_of_toScheme_map_eq B S hS
      (congrArg (BigFppfOver.toScheme B S hS).map (presentationSym_comp_target P)))
    (hom_ext_of_toScheme_map_eq B S hS
      (congrArg (BigFppfOver.toScheme B S hS).map (presentationSym_comp_source P)))
    (presentationDoubleFstHom P) (presentationDoubleSndHom P) (presentationCompHom P)
    (isPullback_toScheme_map_presentationDouble P)
    (hom_ext_of_toScheme_map_eq B S hS
      (congrArg (BigFppfOver.toScheme B S hS).map (presentationComp_comp_target P)))
    (hom_ext_of_toScheme_map_eq B S hS
      (congrArg (BigFppfOver.toScheme B S hS).map (presentationComp_comp_source P)))

end AlgebraicGeometry.Space.SquareZeroExtension

end
