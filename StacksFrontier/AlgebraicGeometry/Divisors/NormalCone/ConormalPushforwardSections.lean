module

public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ConormalAlgebraSheafDegreewise
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ConormalPushforward

/-!
# The two bookkeeping values the factorization of Stacks 0FEB needs

[Stacks, Tag 0FEB] asks for a morphism into the normal cone of an effective Cartier divisor to
factor through the zero section, and
`Stacks.Conormal.normalConeNested_eq_comp_normalConeZeroSection_iff` reduces that to the vanishing
of one morphism of modules — the module component of the relative-spectrum pair that the functor of
points of the total space of the conormal line bundle attaches to a composite of morphisms of
normal cones. Reading that component off the pair needs two values which the library does not
state, and this file states them.

## Main results

* `Stacks.LineBundle.Situation.totalSpaceHomEquiv_pairToHom`: **the functor of points of the total
  space of a line bundle, at the morphism attached to a relative-spectrum pair**, is that pair with
  its algebra datum read as a module morphism.
* `Stacks.RelativeSpec.ungradedAlgebraSheafHomEquiv_symm_ungradedAlgebraSheafIncl`: a morphism of
  algebra sheaves out of the ungraded realization of a sheaf of graded algebras, produced by the
  universal property of sheafification, is the given presheaf morphism on a homogeneous local
  section.
* `Stacks.Conormal.conormalAlgebraSheafPushforwardHom_ungradedIncl`: **the bridge
  `𝒞_{Y/X',*} ⟶ f_* 𝒞_{Z/X,*}` carries a homogeneous local section to the homogeneous local
  section of the same degree given by the sectionwise datum.**

## Implementation notes

Both are formal. The first is the round-trip identity
`Stacks.RelativeSpec.pullback_universalRelativeSpecPair_pairToHom` read through the second factor
of `Stacks.LineBundle.Situation.totalSpaceHomEquiv`; no property of the line bundle is used.

The second splits the bridge `Stacks.Conormal.conormalAlgebraSheafPushforwardHom` into its three
factors and evaluates each on a homogeneous section: the two comparisons of the ungraded
realizations are `Stacks.RelativeSpec.ungradedAlgebraSheafIsoGradedAlgebraSheaf_inv_ungradedIncl`
and `Stacks.RelativeSpec.ungradedToGradedRight_ungradedAlgebraSheafIncl`, and the middle factor is
the universal property of sheafification, whose value on a homogeneous section is the degree-`n`
component of `Stacks.Conormal.conormalPushforwardUnitalHom`, i.e.
`Stacks.Conormal.conormalPushforwardPiece_app`. The direct image enters only through the
identification of its sections over `W` with the sections over `f⁻¹W`, which holds by `rfl`, so no
comparison morphism is inserted.

## References

* [Stacks Project, Tag 0FEB](https://stacks.math.columbia.edu/tag/0FEB)
* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 0634](https://stacks.math.columbia.edu/tag/0634)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.SymAlgSheaf

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **The functor of points of the total space of a line bundle, evaluated at the morphism
attached to a relative-spectrum pair.** It is that pair, with its algebra datum read as a morphism
of modules by `Stacks.LineBundle.Situation.algebraPairEquiv`. This is the round-trip identity
`Stacks.RelativeSpec.pullback_universalRelativeSpecPair_pairToHom` of [Stacks, Tag 01LV] carried
through the second factor of the bijection. -/
theorem Situation.totalSpaceHomEquiv_pairToHom {T : Scheme.{u}}
    (q : Stacks.RelativeSpec.RelativeSpecPair D.relativeSpecSituation T) :
    D.totalSpaceHomEquiv T (Stacks.RelativeSpec.pairToHom q) =
      ⟨q.1, D.algebraPairEquiv q.1 q.2⟩ :=
  congrArg (Equiv.sigmaCongrRight fun g => D.algebraPairEquiv g)
    (Stacks.RelativeSpec.pullback_universalRelativeSpecPair_pairToHom q)

end Stacks.LineBundle

namespace Stacks.RelativeSpec

variable {X : Scheme.{u}} (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hA : ∀ (i j : ℤ) (U : (Opens ↥X)ᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
    HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x))
  (𝒜 : AlgebraSheaf X)

/-- **A morphism of algebra sheaves out of the ungraded realization of a sheaf of graded algebras,
produced from a presheaf morphism by the universal property of sheafification, is that presheaf
morphism on a homogeneous local section.** The inclusion of a homogeneous section into the
realization is the sheafification unit applied to its inclusion into the direct sum, and the
universal property is exactly the statement that the unit followed by the produced morphism is the
given one. -/
theorem ungradedAlgebraSheafHomEquiv_symm_ungradedAlgebraSheafIncl
    (u : {u : ungradedCommPresheaf X A hA ⟶ algebraPresheaf 𝒜 //
      ungradedCommStructureMap X A hA ≫ u = 𝒜.hom.hom})
    (n : ℤ) (U : X.Opens) (x : (A.piece n).val.obj (op U)) :
    (((ungradedAlgebraSheafHomEquiv A hA 𝒜).symm u).right.hom.app (op U)).hom
        (ungradedAlgebraSheafIncl X A hA n U x) =
      (u.1.app (op U)).hom (A.toPresheafGradedAlgebra.incl n x) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (congrArg Subtype.val ((ungradedAlgebraSheafHomEquiv A hA 𝒜).apply_symm_apply u)) (op U))
    (A.toPresheafGradedAlgebra.incl n x)

end Stacks.RelativeSpec

namespace Stacks.Conormal

open Stacks.RelativeSpec

variable {Z X Y X' : Scheme.{u}} (i : Z ⟶ X) (i' : Y ⟶ X') (f : Z ⟶ Y)
  [IsImmersion i] [IsImmersion i'] (H : AlgebraicGeometry.ConormalAlgebraHom i i' f)

/-- **The morphism of algebra sheaves `𝒞_{Y/X',*} ⟶ f_* 𝒞_{Z/X,*}` into the *ungraded*
realization, on a homogeneous local section.** It is the universal property of sheafification at
`Stacks.Conormal.conormalPushforwardUnitalHom`, whose degree-`n` component is the sectionwise
datum of `H` followed by the inclusion of a homogeneous section. -/
theorem conormalUngradedPushforwardHom_ungradedAlgebraSheafIncl (n : ℤ) (W : Y.Opens)
    (x : ((conormalAlgebra i').algebra.piece n).val.obj (op W)) :
    (((conormalUngradedPushforwardHom i i' f H).right.hom).app (op W)).hom
        (ungradedAlgebraSheafIncl Y (conormalAlgebra i').algebra
          (conormalAlgebra i').mul_comm_int n W x) =
      ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra (conormalAlgebra i).mul_comm_int n
        (f ⁻¹ᵁ W) (H.map n (f ⁻¹ᵁ W) W le_rfl x) :=
  (ungradedAlgebraSheafHomEquiv_symm_ungradedAlgebraSheafIncl (conormalAlgebra i').algebra
      (conormalAlgebra i').mul_comm_int (conormalPushforwardAlgebra i f)
      ((ungradedCommHomEquiv (conormalAlgebra i').algebra (conormalAlgebra i').mul_comm_int
        (conormalPushforwardAlgebra i f)).symm (conormalPushforwardUnitalHom i i' f H))
      n W x).trans
    ((ungradedTotal_incl (conormalAlgebra i').algebra (conormalPushforwardAlgebra i f)
        (conormalPushforwardUnitalHom i i' f H) n (op W) x).trans
      (conormalPushforwardPiece_app i i' f H n (op W) x))

/-- **The bridge `𝒞_{Y/X',*} ⟶ f_* 𝒞_{Z/X,*}` carries a homogeneous local section of degree `n`
to the homogeneous local section of degree `n` given by the sectionwise datum of `H`.**

This is the value of the algebra map of the relative-spectrum pair of a morphism of normal cones
on a homogeneous section, which is what [Stacks, Tag 0FEB] compares. -/
theorem conormalAlgebraSheafPushforwardHom_ungradedIncl (n : ℤ) (W : Y.Opens)
    (x : ((conormalAlgebra i').algebra.piece n).val.obj (op W)) :
    (((conormalAlgebraSheafPushforwardHom i i' f H).right.hom).app (op W)).hom
        ((conormalAlgebra i').algebra.ungradedIncl n x) =
      (conormalAlgebra i).algebra.ungradedIncl n (H.map n (f ⁻¹ᵁ W) W le_rfl x) := by
  have hdec : (((conormalAlgebraSheafPushforwardHom i i' f H).right.hom).app (op W)).hom
        ((conormalAlgebra i').algebra.ungradedIncl n x) =
      (((ungradedAlgebraSheafIsoGradedAlgebraSheaf Z (conormalAlgebra i).algebra
            (conormalAlgebra i).mul_comm_int).hom.right.hom.app (op (f ⁻¹ᵁ W))).hom
        ((((conormalUngradedPushforwardHom i i' f H).right.hom).app (op W)).hom
          ((((ungradedAlgebraSheafIsoGradedAlgebraSheaf Y (conormalAlgebra i').algebra
              (conormalAlgebra i').mul_comm_int).inv.right.hom).app (op W)).hom
            ((conormalAlgebra i').algebra.ungradedIncl n x)))) := rfl
  rw [hdec, ungradedAlgebraSheafIsoGradedAlgebraSheaf_inv_ungradedIncl,
    conormalUngradedPushforwardHom_ungradedAlgebraSheafIncl]
  exact ungradedToGradedRight_ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int n (f ⁻¹ᵁ W) (H.map n (f ⁻¹ᵁ W) W le_rfl x)

end Stacks.Conormal

end
