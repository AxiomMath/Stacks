module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.BasePointChangeEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.ChangeBasePoint
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.Functoriality

/-!
# Homomorphisms of étale fundamental groups induced by a morphism are inner conjugate

A homomorphism `Φ : π₁(Y, ȳ) → π₁(X, x̄)` is *induced by* a functor `H : FÉt_X ⥤ FÉt_Y` if for
some isomorphism `T : H ⋙ F_ȳ ≅ F_x̄` of fibre functors, `Φ(γ)` acts on `F_x̄(V)` as
`T ∘ γ_{H V} ∘ T⁻¹` (`AlgebraicGeometry.IsEtaleFundamentalGroupHomInducedBy`). The map
`f_* : π₁(Y, ȳ) → π₁(X, f(ȳ))` of a morphism `f : Y ⟶ X` is induced by the base change
`FÉt_X ⥤ FÉt_Y` along `f`, a change of base point `π₁(X, x̄') → π₁(X, x̄)` is induced by the
identity functor, composites are induced by composites, and the property only depends on `H` up
to isomorphism. Two homomorphisms induced by the same functor differ by an inner automorphism
of the target ([Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)).

Hence any two homomorphisms `π₁(Y, ȳ) → π₁(X, x̄)` assembled from maps induced by morphisms of
schemes and changes of base point, whose underlying morphisms `Y ⟶ X` agree, are inner conjugate
(`AlgebraicGeometry.IsEtaleFundamentalGroupHomInducedBy.isInnerConjugate_of_eq`).

## Main definitions

* `AlgebraicGeometry.IsEtaleFundamentalGroupHomInducedBy`: the homomorphism `Φ` is induced by the
  functor `H : FÉt_X ⥤ FÉt_Y`.

## Main results

* `AlgebraicGeometry.isEtaleFundamentalGroupHomInducedBy_map`: `f_*` is induced by the base change
  along `f`.
* `AlgebraicGeometry.isEtaleFundamentalGroupHomInducedBy_basePointHom`: a change of base point is
  induced by the identity functor.
* `AlgebraicGeometry.IsEtaleFundamentalGroupHomInducedBy.comp`: composites of induced homomorphisms
  are induced by the composite functors.
* `AlgebraicGeometry.IsEtaleFundamentalGroupHomInducedBy.of_iso`: being induced only depends on the
  functor up to isomorphism.
* `AlgebraicGeometry.IsEtaleFundamentalGroupHomInducedBy.isInnerConjugate`: two homomorphisms
  induced by the same functor are inner conjugate.
* `AlgebraicGeometry.IsEtaleFundamentalGroupHomInducedBy.isInnerConjugate_of_eq`: homomorphisms
  induced by base changes along equal morphisms are inner conjugate.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y] [ConnectedSpace Z]

/-- **`Φ : π₁(Y, ȳ) → π₁(X, x̄)` is induced by the functor `H : FÉt_X ⥤ FÉt_Y`**: for some
isomorphism `T : H ⋙ F_ȳ ≅ F_x̄` of fibre functors, `Φ(γ)` acts on `F_x̄(V)` as
`T ∘ γ_{H V} ∘ T⁻¹`. -/
public def IsEtaleFundamentalGroupHomInducedBy {x : GeometricPoint X} {y : GeometricPoint Y}
    (H : FiniteEtaleOver X ⥤ FiniteEtaleOver Y)
    (Φ : EtaleFundamentalGroup Y y →* EtaleFundamentalGroup X x) : Prop :=
  ∃ T : H ⋙ finiteEtaleFiberFunctor y ≅ finiteEtaleFiberFunctor x,
    ∀ (γ : EtaleFundamentalGroup Y y) (V : FiniteEtaleOver X)
      (w : (finiteEtaleFiberFunctor x).obj V),
      ((Φ γ).app V).hom w = T.hom.app V ((γ.app (H.obj V)).hom (T.inv.app V w))

/-- **`f_*` is induced by the base change along `f`.** -/
public theorem isEtaleFundamentalGroupHomInducedBy_map (f : Y ⟶ X) (y : GeometricPoint Y) :
    IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange f)
      (etaleFundamentalGroupMap f y).toMonoidHom :=
  ⟨finiteEtaleFiberProjectionIso f y, fun _ _ _ => rfl⟩

/-- **A change of base point is induced by the identity functor.** -/
public theorem isEtaleFundamentalGroupHomInducedBy_basePointHom {x x' : GeometricPoint X}
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :
    IsEtaleFundamentalGroupHomInducedBy (𝟭 (FiniteEtaleOver X))
      (etaleFundamentalGroupBasePointHom t).toMonoidHom := by
  refine ⟨Functor.leftUnitor _ ≪≫ t.symm, fun γ V w => ?_⟩
  have h := Stacks.FundamentalGroup.conjAut_app_apply t
    (etaleFundamentalGroupBasePointHom t γ) V w
  have hγ : t.conjAut (etaleFundamentalGroupBasePointHom t γ) = γ :=
    etaleFundamentalGroupMulEquiv_basePointHom t γ
  rw [hγ] at h
  show ((etaleFundamentalGroupBasePointHom t γ).app V).hom w =
    t.inv.app V ((γ.app V).hom (t.hom.app V w))
  rw [h, Iso.hom_inv_id_app_apply]

namespace IsEtaleFundamentalGroupHomInducedBy

variable {x : GeometricPoint X} {y : GeometricPoint Y} {z : GeometricPoint Z}

/-- **Composites of induced homomorphisms are induced by the composite functors.** -/
public theorem comp {H₁ : FiniteEtaleOver X ⥤ FiniteEtaleOver Y}
    {Φ₁ : EtaleFundamentalGroup Y y →* EtaleFundamentalGroup X x}
    {H₂ : FiniteEtaleOver Z ⥤ FiniteEtaleOver X}
    {Φ₂ : EtaleFundamentalGroup X x →* EtaleFundamentalGroup Z z}
    (h₁ : IsEtaleFundamentalGroupHomInducedBy H₁ Φ₁)
    (h₂ : IsEtaleFundamentalGroupHomInducedBy H₂ Φ₂) :
    IsEtaleFundamentalGroupHomInducedBy (H₂ ⋙ H₁) (Φ₂.comp Φ₁) := by
  obtain ⟨T₁, hT₁⟩ := h₁
  obtain ⟨T₂, hT₂⟩ := h₂
  refine ⟨Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft H₂ T₁ ≪≫ T₂, fun γ V w => ?_⟩
  rw [MonoidHom.comp_apply, hT₂, hT₁]
  rfl

/-- **Being induced only depends on the functor up to isomorphism.** -/
public theorem of_iso {H H' : FiniteEtaleOver X ⥤ FiniteEtaleOver Y} (ν : H ≅ H')
    {Φ : EtaleFundamentalGroup Y y →* EtaleFundamentalGroup X x}
    (h : IsEtaleFundamentalGroupHomInducedBy H Φ) : IsEtaleFundamentalGroupHomInducedBy H' Φ := by
  obtain ⟨T, hT⟩ := h
  refine ⟨Functor.isoWhiskerRight ν.symm (finiteEtaleFiberFunctor y) ≪≫ T, fun γ V w => ?_⟩
  rw [hT]
  show T.hom.app V ((γ.app (H.obj V)).hom (T.inv.app V w)) =
    T.hom.app V ((finiteEtaleFiberFunctor y).map (ν.inv.app V)
      ((γ.app (H'.obj V)).hom ((finiteEtaleFiberFunctor y).map (ν.hom.app V) (T.inv.app V w))))
  congr 1
  have hn : (γ.app (H'.obj V)).hom ((finiteEtaleFiberFunctor y).map (ν.hom.app V) (T.inv.app V w)) =
      (finiteEtaleFiberFunctor y).map (ν.hom.app V) ((γ.app (H.obj V)).hom (T.inv.app V w)) :=
    ConcreteCategory.congr_hom (γ.hom.naturality (ν.hom.app V)) (T.inv.app V w)
  rw [hn, ← Functor.map_comp_apply, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rfl

/-- **Two homomorphisms induced by the same functor are inner conjugate.** -/
public theorem isInnerConjugate {H : FiniteEtaleOver X ⥤ FiniteEtaleOver Y}
    {Φ Φ' : EtaleFundamentalGroup Y y →* EtaleFundamentalGroup X x}
    (h : IsEtaleFundamentalGroupHomInducedBy H Φ) (h' : IsEtaleFundamentalGroupHomInducedBy H Φ') :
    IsInnerConjugate Φ Φ' := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨T', hT'⟩ := h'
  let c : EtaleFundamentalGroup X x := T.symm ≪≫ T'
  refine ⟨c, fun γ => Aut.ext ?_⟩
  ext V w
  show ((Φ' γ).app V).hom w = T'.hom.app V (T.inv.app V (((Φ γ).app V).hom
    (T.hom.app V (T'.inv.app V w))))
  rw [hT', hT, Iso.hom_inv_id_app_apply, Iso.hom_inv_id_app_apply]

/-- **Homomorphisms induced by base changes along equal morphisms are inner conjugate.** -/
public theorem isInnerConjugate_of_eq {f f' : Y ⟶ X}
    {Φ Φ' : EtaleFundamentalGroup Y y →* EtaleFundamentalGroup X x}
    (h : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange f) Φ)
    (h' : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange f') Φ') (hf : f = f') :
    IsInnerConjugate Φ Φ' := by
  subst hf
  exact h.isInnerConjugate h'

/-- **The composite of homomorphisms induced by base changes along `f` and `g` is induced by the
base change along `f ≫ g`.** -/
public theorem comp_baseChange {f : Y ⟶ X} {g : X ⟶ Z}
    {Φ₁ : EtaleFundamentalGroup Y y →* EtaleFundamentalGroup X x}
    {Φ₂ : EtaleFundamentalGroup X x →* EtaleFundamentalGroup Z z}
    (h₁ : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange f) Φ₁)
    (h₂ : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange g) Φ₂) :
    IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange (f ≫ g)) (Φ₂.comp Φ₁) :=
  (h₁.comp h₂).of_iso (finiteEtaleBaseChangeComp f g).symm

end IsEtaleFundamentalGroupHomInducedBy

/-- **A change of base point is induced by the base change along the identity.** -/
public theorem isEtaleFundamentalGroupHomInducedBy_basePointHom_id {x x' : GeometricPoint X}
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :
    IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange (𝟙 X))
      (etaleFundamentalGroupBasePointHom t).toMonoidHom :=
  (isEtaleFundamentalGroupHomInducedBy_basePointHom t).of_iso finiteEtaleBaseChangeId.symm

end AlgebraicGeometry

end
