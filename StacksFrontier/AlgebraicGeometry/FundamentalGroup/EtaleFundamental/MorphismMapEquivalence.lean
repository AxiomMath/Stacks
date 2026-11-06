module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.ChangeBasePoint

/-!
# Base change and restriction of the fundamental-group action agree

Let `f : X ⟶ Y` be a morphism of connected schemes and let `x` be a geometric point of `X`.
Grothendieck's equivalence identifies `FÉt_X` with the finite continuous `π₁(X, x)`-sets and
`FÉt_Y` with the finite continuous `π₁(Y, f ∘ x)`-sets, and `f` gives two functors
`FÉt_Y ⥤ FÉt_X`-worth of comparison: base change `- ×_Y X` downstairs, and restriction of the
action along `AlgebraicGeometry.etaleFundamentalGroupMap` upstairs. This file proves that the
resulting square of functors commutes up to a natural isomorphism whose underlying map of finite
sets is, on each cover `V` of `Y`, precisely the canonical projection
`AlgebraicGeometry.finiteEtaleFiberProjection` of geometric fibres.

The content is entirely in the identification of the underlying sets. The isomorphism of fibre
functors `AlgebraicGeometry.finiteEtaleFiberProjectionIso` already identifies
`(- ×_Y X) ⋙ F_x` with `F_{f ∘ x}`; conjugating it through the two fibre identifications of the
equivalences gives an isomorphism `(- ×_Y X) ⋙ U_X ≅ U_Y` of the two underlying-set functors, and
the only thing to check is that its components are equivariant, which is the fibre-projection
equation `AlgebraicGeometry.etaleFundamentalGroupMap_finiteEtaleFiberProjection` sandwiched
between the two action equations of the equivalences. Naturality transports unchanged.

## The Galois-category hypothesis

The equivalences are built from the Galois-category axioms, so the statement below takes
`Stacks.FundamentalGroup.IsGaloisCategory` instance hypotheses at both geometric points. For
connected schemes they hold, by Stacks Tag 0BNB
(`Stacks.FundamentalGroup.isGaloisCategory_finiteEtaleFiberFunctor`); the hypothesis-free
statement of Tag 0BND (3) is `AlgebraicGeometry.exists_finiteEtaleEquivalence_mapIso`.

## Main results

* `AlgebraicGeometry.exists_finiteEtaleEquivalenceOfIsGaloisCategory_mapIso` — the comparison
  isomorphism for the functoriality square, together with the specification of its underlying
  map as the geometric-fibre projection.

## Implementation notes

The isomorphism is produced by `CategoryTheory.NatIso.ofComponents` on the *inverse* direction
`(- ×_Y X) ⋙ E_X ≅ E_Y ⋙ ContAction.res _ ρ` and then reversed, because that is the direction in
which a component is built: an isomorphism of continuous actions is an
`CategoryTheory.ObjectProperty.isoMk` of an `CategoryTheory.Action.mkIso` of an isomorphism of
finite sets, and the finite-set isomorphism is the component of the underlying-set comparison
transported by `CategoryTheory.equivEquivIso` and `FintypeCat.equivEquivIso`.

Stating the underlying-set computation once, as the local `hq`, is what keeps the proof short:
it is used for the equivariance check at two different arguments and then again, unchanged, as
the second half of the conclusion.

## References

* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
* [Stacks Project, Tag 0BNB](https://stacks.math.columbia.edu/tag/0BNB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.FundamentalGroup
open scoped FintypeCatDiscrete

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y] (f : X ⟶ Y)
  (x : GeometricPoint X)
  [IsGaloisCategory (finiteEtaleFiberFunctor x)]
  [IsGaloisCategory (finiteEtaleFiberFunctor (x.map f))]

/-- **Stacks 0BND, the functoriality square, conditionally on Tag 0BNB.** Under the equivalences
between finite étale covers and finite continuous fundamental-group sets, base change along
`f : X ⟶ Y` agrees naturally with restriction of the action along the induced homomorphism
`AlgebraicGeometry.etaleFundamentalGroupMap`; and the component of the comparison isomorphism
is, after the two fibre identifications, the canonical projection of geometric fibres. -/
theorem exists_finiteEtaleEquivalenceOfIsGaloisCategory_mapIso :
    ∃ η : (finiteEtaleEquivalenceOfIsGaloisCategory Y (x.map f)).functor ⋙
          ContAction.res FintypeCat (etaleFundamentalGroupMap f x) ≅
        finiteEtaleBaseChange f ⋙
          (finiteEtaleEquivalenceOfIsGaloisCategory X x).functor,
      ∀ (V : FiniteEtaleOver Y)
        (a : (((finiteEtaleEquivalenceOfIsGaloisCategory X x).functor.obj
          ((finiteEtaleBaseChange f).obj V)).obj.V.obj)),
        (finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso Y (x.map f)).hom.app V
            ((η.inv.app V).hom.hom a) =
          finiteEtaleFiberProjection f x V
            ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x).hom.app
              ((finiteEtaleBaseChange f).obj V) a) := by
  let EX := finiteEtaleEquivalenceOfIsGaloisCategory X x
  let EY := finiteEtaleEquivalenceOfIsGaloisCategory Y (x.map f)
  let H := finiteEtaleBaseChange f
  let UX := EX.functor ⋙
    forget₂ (ContAction FintypeCat (EtaleFundamentalGroup X x)) FintypeCat ⋙ FintypeCat.incl
  let UY := EY.functor ⋙
    forget₂ (ContAction FintypeCat (EtaleFundamentalGroup Y (x.map f))) FintypeCat ⋙
      FintypeCat.incl
  let aX := finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x
  let aY := finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso Y (x.map f)
  let g : H ⋙ UX ≅ UY :=
    Functor.isoWhiskerLeft H aX ≪≫ finiteEtaleFiberProjectionIso f x ≪≫ aY.symm
  let r := etaleFundamentalGroupMap f x
  have hq (V : FiniteEtaleOver Y) (b : ((EX.functor.obj (H.obj V)).obj.V.obj)) :
      aY.hom.app V ((equivEquivIso.symm (g.app V)) b) =
        finiteEtaleFiberProjection f x V (aX.hom.app (H.obj V) b) := by
    show aY.hom.app V
        ((aY.symm.app V).toEquiv
          (((finiteEtaleFiberProjectionIso f x).app V).toEquiv
            (((Functor.isoWhiskerLeft H aX).app V).toEquiv b))) = _
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, Iso.toEquiv_apply, Iso.app_hom,
      Iso.symm_hom, Iso.inv_hom_id_app_apply]
    rfl
  let b : H ⋙ EX.functor ≅ EY.functor ⋙ ContAction.res FintypeCat r :=
    NatIso.ofComponents (fun V ↦ by
      refine ObjectProperty.isoMk _ (Action.mkIso
        (FintypeCat.equivEquivIso (equivEquivIso.symm (g.app V))) (fun s ↦ ?_))
      apply FintypeCat.hom_ext
      intro a
      apply (equivEquivIso.symm (aY.app V)).injective
      show aY.hom.app V ((equivEquivIso.symm (g.app V))
          (ConcreteCategory.hom ((EX.functor.obj (H.obj V)).obj.ρ s).asHom a)) =
        aY.hom.app V (ConcreteCategory.hom ((EY.functor.obj V).obj.ρ (r s)).asHom
          ((equivEquivIso.symm (g.app V)) a))
      have hX := finiteEtaleEquivalenceOfIsGaloisCategory_action X x (H.obj V) s a
      have hP := etaleFundamentalGroupMap_finiteEtaleFiberProjection f x V s
        (aX.hom.app (H.obj V) a)
      have hY := finiteEtaleEquivalenceOfIsGaloisCategory_action Y (x.map f) V (r s)
        ((equivEquivIso.symm (g.app V)) a)
      rw [hq V a] at hY
      rw [hq V (ConcreteCategory.hom ((EX.functor.obj (H.obj V)).obj.ρ s).asHom a)]
      exact ((congrArg (finiteEtaleFiberProjection f x V) hX).trans hP).trans hY.symm) (by
      intro V W k
      ext a
      exact congrArg (fun t ↦ t a) (g.hom.naturality k))
  exact ⟨b.symm, hq⟩

end AlgebraicGeometry

end
