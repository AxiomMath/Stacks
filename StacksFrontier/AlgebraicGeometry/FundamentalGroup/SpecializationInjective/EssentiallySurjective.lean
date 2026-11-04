module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationSurjective

/-!
# Injectivity of a specialization map, from essential surjectivity of base change

Let `f : X ⟶ S` be a proper morphism with geometrically connected fibres and let `s'` and `s` be
geometric points of `S`. A specialization map `sp : π₁(X_{s̄'}) ⟶ π₁(X_{s̄})` is built from a
morphism `g : T ⟶ S` with `X_T` connected through which both geometric points factor: it is the
composite `π₁(X_{s̄'}) ⟶ π₁(X_T) = π₁(X_{s̄})`, the second map being an isomorphism. So `sp` is
injective as soon as `π₁(X_{s̄'}) ⟶ π₁(X_T)` is, and that holds whenever every finite étale cover
of `X_{s̄'}` is isomorphic to the base change of a finite étale cover of `X_T`.

The reason is that precomposition with an essentially surjective functor is faithful: a natural
transformation between functors on the target category is determined by its components at the
objects in the image, because naturality against an isomorphism `H P ≅ Q` recovers the component
at `Q` from the component at `H P`. The induced map on étale fundamental groups is, by
construction, the action on automorphism groups of precomposition with base change, conjugated by
the fibre projections; faithfulness of the former makes that action injective, and conjugation is
a bijection.

## Main results

* `CategoryTheory.Functor.faithful_whiskeringLeft_obj_of_essSurj` — precomposition with an
  essentially surjective functor is faithful.
* `AlgebraicGeometry.injective_etaleFundamentalGroupMap_of_essSurj` — the homomorphism of étale
  fundamental groups induced by a morphism along which base change is essentially surjective on
  finite étale covers is injective.
* `AlgebraicGeometry.injective_of_essSurj_of_specializationMapEquation` — a continuous
  homomorphism satisfying the equation defining a specialization map against a base `g : T ⟶ S`
  is injective when base change along `X_{s̄'} ⟶ X_T` is essentially surjective.
* `AlgebraicGeometry.injective_specializationMap_of_essSurj` — the same for the base
  `Spec A ⟶ S` of a strict henselization of `𝒪_{S,s}`, in the shape in which the construction of
  the specialization map presents its data.
* `AlgebraicGeometry.bijective_specializationMap_of_essSurj_of_flat` — bijectivity, combining
  the above with surjectivity for a flat proper morphism with a geometrically reduced fibre.

## Implementation notes

The essential surjectivity hypothesis is stated for the base change functor attached to the
chosen factorization of `s̄'`, not for an arbitrary one, so the results take the data of the
construction as explicit arguments rather than the predicate
`AlgebraicGeometry.IsSpecializationMap`, whose witnesses are existentially quantified. This is the
shape in which `AlgebraicGeometry.surjective_specializationMap_of_isProper_of_flat` states
surjectivity, and the two combine directly.

Neither the strict henselization hypothesis nor the requirement that `s̄` land on the closed point
is used for injectivity: all that the argument needs of the base is that `X_T` be connected. They
appear in `AlgebraicGeometry.injective_specializationMap_of_essSurj` only to fix the shape of the
statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace CategoryTheory.Functor

/-- **Precomposition with an essentially surjective functor is faithful.** Let `H : C ⥤ C'` be
essentially surjective. Two natural transformations between functors `C' ⥤ D` which agree after
restriction along `H` are equal.

Given an object `Q` of `C'`, choose `P` with an isomorphism `e : H P ≅ Q`. Naturality of a
transformation `α` against `e.hom` writes `α.app Q` as `F.map e.hom` composed with
`α.app (H P) ≫ G.map e.hom`, and `F.map e.hom` is an isomorphism, hence an epimorphism. So the
component at `Q` is determined by the component at `H P`. -/
theorem faithful_whiskeringLeft_obj_of_essSurj {C : Type*} [Category C] {C' : Type*}
    [Category C'] (D : Type*) [Category D] (H : C ⥤ C') [H.EssSurj] :
    ((whiskeringLeft C C' D).obj H).Faithful where
  map_injective := by
    intro F G α β h
    ext Q
    have hα := α.naturality (H.objObjPreimageIso Q).hom
    have hβ := β.naturality (H.objObjPreimageIso Q).hom
    rw [show α.app (H.obj (H.objPreimage Q)) = β.app (H.obj (H.objPreimage Q)) from
      NatTrans.congr_app h (H.objPreimage Q)] at hα
    exact (cancel_epi (F.map (H.objObjPreimageIso Q).hom)).mp (hα.trans hβ.symm)

end CategoryTheory.Functor

namespace AlgebraicGeometry

/-! ### Injectivity of the induced homomorphism -/

/-- **An essentially surjective base change makes the induced homomorphism of étale fundamental
groups injective.** Let `f : X ⟶ Y` be a morphism of connected schemes and `x` a geometric point
of `X`. If every finite étale cover of `X` is isomorphic to the base change of a finite étale
cover of `Y`, then `π₁(X, x) ⟶ π₁(Y, f ∘ x)` is injective.

The induced homomorphism is the action on automorphism groups of precomposition with the base
change functor, followed by conjugation by the fibre projections. Precomposition with an
essentially surjective functor is faithful, so it is injective on automorphism groups, and
conjugation is a bijection. -/
theorem injective_etaleFundamentalGroupMap_of_essSurj {X Y : Scheme.{u}} [ConnectedSpace X]
    [ConnectedSpace Y] (f : X ⟶ Y) (x : GeometricPoint X)
    (hess : (finiteEtaleBaseChange f).EssSurj) :
    Function.Injective (etaleFundamentalGroupMap f x) := by
  let W := (Functor.whiskeringLeft (FiniteEtaleOver Y) (FiniteEtaleOver X) (Type u)).obj
    (finiteEtaleBaseChange f)
  have _ : W.Faithful :=
    Functor.faithful_whiskeringLeft_obj_of_essSurj (Type u) (finiteEtaleBaseChange f)
  have hmap : Function.Injective (W.mapAut (finiteEtaleFiberFunctor x)) := fun a b hab =>
    Iso.ext (W.map_injective (congrArg Iso.hom hab))
  exact (finiteEtaleFiberProjectionIso f x).conjAut.injective.comp hmap

/-! ### Injectivity of a specialization map -/

/-- **A specialization map is injective when base change to the generic geometric fibre is
essentially surjective.** Let `f : X ⟶ S` be proper with geometrically connected fibres, let `s'`
and `s` be geometric points of `S`, let `g : T ⟶ S` be a morphism with `X_T` connected through
which both geometric points factor, and let `sp : π₁(X_{s̄'}) ⟶ π₁(X_{s̄})` satisfy the equation
defining a specialization map against a fibre-functor isomorphism `t` on `X_T`. If every finite
étale cover of `X_{s̄'}` is isomorphic to the base change of a finite étale cover of `X_T`, then
`sp` is injective.

The defining equation exhibits `π₁(X_{s̄}) ⟶ π₁(X_T)` applied to `sp γ` as the transport along
`t` of `π₁(X_{s̄'}) ⟶ π₁(X_T)` applied to `γ`. Transport along `t` is a group isomorphism and the
second map is injective by
`AlgebraicGeometry.injective_etaleFundamentalGroupMap_of_essSurj`, so `γ` is determined by
`sp γ`. -/
theorem injective_of_essSurj_of_specializationMapEquation {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [GeometricallyConnected f] {s' s : GeometricPoint S} {T : Scheme.{u}}
    (g : T ⟶ S) [ConnectedSpace ↥(pullback f g)]
    (p' : s'.source ⟶ T) (hp' : p' ≫ g = s'.hom)
    (p : s.source ⟶ T) (hp : p ≫ g = s.hom)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hess : (finiteEtaleBaseChange (fiberOverGeometricPointMap f s' g p' hp')).EssSurj)
    (t : finiteEtaleFiberFunctor (x'.map (fiberOverGeometricPointMap f s' g p' hp')) ≅
      finiteEtaleFiberFunctor (x.map (fiberOverGeometricPointMap f s g p hp)))
    (hform : ∀ γ, etaleFundamentalGroupMap (fiberOverGeometricPointMap f s g p hp) x (sp γ)
      = etaleFundamentalGroupMulEquiv t
        (etaleFundamentalGroupMap (fiberOverGeometricPointMap f s' g p' hp') x' γ)) :
    Function.Injective sp := by
  intro γ₁ γ₂ hγ
  refine injective_etaleFundamentalGroupMap_of_essSurj
    (fiberOverGeometricPointMap f s' g p' hp') x' hess
    ((etaleFundamentalGroupMulEquiv t).injective ?_)
  rw [← hform γ₁, ← hform γ₂, hγ]

/-- **Injectivity of a specialization map presented by a strict henselization.** Let
`f : X ⟶ S` be proper with geometrically connected fibres and let `s' ⇝ s` be a specialization of
points of `S`, realized as in the construction of the specialization map: `A` is a strict
henselization of `𝒪_{S,s}` relative to a separable closure of `κ(s)`, and the two geometric
points are factored through `Spec A`, the special one over the closed point. Let

```
sp : π₁(X_{s̄'}) ⟶ π₁(X_{s̄})
```

be the resulting specialization map, that is, a continuous homomorphism satisfying the equation
defining it against the canonical maps to `π₁(X_A)`. If every finite étale cover of `X_{s̄'}` is
isomorphic to the base change of a finite étale cover of `X_A`, then `sp` is injective.

This is the reduction by which injectivity of a specialization map is proved: it remains to
produce, for each finite étale cover of the geometric generic fibre, a finite étale cover of `X_A`
restricting to it.

The hypotheses `hA` and `hclosed` are not used: all the argument needs of the base is that `X_A`
be connected, which follows from properness and local-ringness of `A` alone. They are present so
that the statement is the one made by the construction of the specialization map, matching
`AlgebraicGeometry.surjective_specializationMap_of_isProper_of_flat`. -/
theorem injective_specializationMap_of_essSurj {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [GeometricallyConnected f] (s' s : GeometricPoint S)
    (A : Type u) [CommRing A] [IsLocalRing A]
    [Algebra (S.presheaf.stalk (s.hom (closedPoint s.residueField))) A]
    (hA : Stacks.StrictHenselization.IsStrictHenselization
      (S.presheaf.stalk (s.hom (closedPoint s.residueField)))
      (SeparableClosure
        (maximalIdeal (S.presheaf.stalk (s.hom (closedPoint s.residueField)))).ResidueField) A)
    (p' : s'.source ⟶ Spec (.of A))
    (hp' : p' ≫ specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A = s'.hom)
    (p : s.source ⟶ Spec (.of A))
    (hp : p ≫ specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A = s.hom)
    (hclosed : p (closedPoint s.residueField) = closedPoint A)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hess : (finiteEtaleBaseChange
      (fiberOverGeometricPointMap f s' _ p' hp')).EssSurj) :
    letI : ConnectedSpace
        ↥(pullback f (specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A)) :=
      connectedSpace_pullback_spec_of_isProper f A _
    ∀ t : finiteEtaleFiberFunctor (x'.map (fiberOverGeometricPointMap f s' _ p' hp')) ≅
        finiteEtaleFiberFunctor (x.map (fiberOverGeometricPointMap f s _ p hp)),
      (∀ γ, etaleFundamentalGroupMap (fiberOverGeometricPointMap f s _ p hp) x (sp γ)
          = etaleFundamentalGroupMulEquiv t
            (etaleFundamentalGroupMap (fiberOverGeometricPointMap f s' _ p' hp') x' γ)) →
        Function.Injective sp := by
  let : ConnectedSpace
      ↥(pullback f (specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A)) :=
    connectedSpace_pullback_spec_of_isProper f A _
  intro t hform
  exact injective_of_essSurj_of_specializationMapEquation f _ p' hp' p hp x' x sp hess t hform

/-- **Bijectivity of a specialization map of a flat proper morphism.** Let `f : X ⟶ S` be flat
and proper with geometrically connected fibres, let `s' ⇝ s` be a specialization of points of `S`
with `X_s` geometrically reduced, and let `sp : π₁(X_{s̄'}) ⟶ π₁(X_{s̄})` be the specialization map
attached to a strict henselization `A` of `𝒪_{S,s}` and factorizations of the two geometric points
through `Spec A`, the special one over the closed point. If every finite étale cover of `X_{s̄'}`
is isomorphic to the base change of a finite étale cover of `X_A`, then `sp` is bijective.

Surjectivity is `AlgebraicGeometry.surjective_specializationMap_of_isProper_of_flat` and needs no
hypothesis beyond flatness, properness and geometric reducedness of `X_s`; injectivity is
`AlgebraicGeometry.injective_specializationMap_of_essSurj` and is where the essential
surjectivity enters. -/
theorem bijective_specializationMap_of_essSurj_of_flat {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Flat f] [GeometricallyConnected f] (s' s : GeometricPoint S)
    (hred : GeometricallyReduced
      (f.fiberToSpecResidueField (s.hom (closedPoint s.residueField))))
    (A : Type u) [CommRing A] [IsLocalRing A]
    [Algebra (S.presheaf.stalk (s.hom (closedPoint s.residueField))) A]
    (hA : Stacks.StrictHenselization.IsStrictHenselization
      (S.presheaf.stalk (s.hom (closedPoint s.residueField)))
      (SeparableClosure
        (maximalIdeal (S.presheaf.stalk (s.hom (closedPoint s.residueField)))).ResidueField) A)
    (p' : s'.source ⟶ Spec (.of A))
    (hp' : p' ≫ specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A = s'.hom)
    (p : s.source ⟶ Spec (.of A))
    (hp : p ≫ specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A = s.hom)
    (hclosed : p (closedPoint s.residueField) = closedPoint A)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hess : (finiteEtaleBaseChange
      (fiberOverGeometricPointMap f s' _ p' hp')).EssSurj) :
    letI : ConnectedSpace
        ↥(pullback f (specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A)) :=
      connectedSpace_pullback_spec_of_isProper f A _
    ∀ t : finiteEtaleFiberFunctor (x'.map (fiberOverGeometricPointMap f s' _ p' hp')) ≅
        finiteEtaleFiberFunctor (x.map (fiberOverGeometricPointMap f s _ p hp)),
      (∀ γ, etaleFundamentalGroupMap (fiberOverGeometricPointMap f s _ p hp) x (sp γ)
          = etaleFundamentalGroupMulEquiv t
            (etaleFundamentalGroupMap (fiberOverGeometricPointMap f s' _ p' hp') x' γ)) →
        Function.Bijective sp := by
  intro t hform
  exact ⟨injective_specializationMap_of_essSurj f s' s A hA p' hp' p hp hclosed x' x sp hess
      t hform,
    surjective_specializationMap_of_isProper_of_flat f s' s hred A hA p' hp' p hp hclosed x' x sp
      t hform⟩

end AlgebraicGeometry

end
