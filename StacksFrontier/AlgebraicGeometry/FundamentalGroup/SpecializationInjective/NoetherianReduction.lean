module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationInjective.BaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.AffineStageDescent.ProperSmoothGeometricallyConnectedModel
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapValuationRing
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapStrictlyHenselianDiscreteValuationRing

/-!
# Reducing injectivity of a specialization map to a strictly henselian discrete valuation ring

Let `f : X ⟶ S` be a smooth proper morphism with geometrically connected fibres and let
`sp : π₁(X_{s̄'}) → π₁(X_{s̄})` be a specialization map whose special point has residue
characteristic zero. This file carries out the three reductions with which the proof of
[Stacks, Tag 0C0Q] begins, and leaves exactly one statement: injectivity of the specialization map
of a smooth proper morphism with geometrically connected fibres over a strictly henselian discrete
valuation ring with algebraically closed residue field of characteristic zero, from its generic to
its closed point.

* The base is made affine. By [Stacks, Tag 0C0M] `sp` is isomorphic to the specialization map of
  the base change of `f` to the spectrum of a strictly henselian valuation ring over `S`.
* The base is made Noetherian. A smooth proper morphism with geometrically connected fibres over
  an affine base is the base change of one over a Noetherian affine base
  (`AlgebraicGeometry.exists_isPullback_isNoetherian_properSmoothGeometricallyConnected`), and
  injectivity of a specialization map descends along a cartesian square
  (`AlgebraicGeometry.injective_isSpecializationMap_of_isPullback`, from [Stacks, Tag 0C0K]).
* The base is made the spectrum of a strictly henselian discrete valuation ring, by
  [Stacks, Tag 0C0N].

The residue characteristic travels along each reduction because the comparison morphisms of bases
induce homomorphisms of residue fields, and a ring homomorphism between fields preserves the
characteristic (`AlgebraicGeometry.ringChar_residueField_eq`).

## Main results

* `ringChar_residueField_eq`: a morphism of schemes does not change the characteristic of the
  residue field at a point.
* `injective_isSpecializationMap_of_isAffine_of_forall_isNoetherian`.
* `injective_isSpecializationMap_of_forall_isNoetherian`.
* `injective_isSpecializationMap_of_isNoetherian_of_forall_isDiscreteValuationRing`.
* `injective_isSpecializationMap_of_forall_isDiscreteValuationRing`: the three reductions
  composed — the whole of the first two paragraphs of the proof of [Stacks, Tag 0C0Q].

## Implementation notes

The hypotheses are stated as universally quantified implications rather than as named predicates,
and no `@[stacks]` attribute is attached to anything here: the remaining input is not proved, so
nothing in this file states a Stacks result.

## References

* [Stacks Project, Tag 0C0Q](https://stacks.math.columbia.edu/tag/0C0Q)
* [Stacks Project, Tag 0C0K](https://stacks.math.columbia.edu/tag/0C0K)
* [Stacks Project, Tag 0C0M](https://stacks.math.columbia.edu/tag/0C0M)
* [Stacks Project, Tag 0C0N](https://stacks.math.columbia.edu/tag/0C0N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A morphism of schemes does not change the characteristic of the residue field.** For
`f : X ⟶ Y` and `x` a point of `X`, the residue field of `Y` at `f x` maps to the residue field of
`X` at `x`; a ring homomorphism between fields is injective and reflects the vanishing of a natural
number, so the two characteristics agree. -/
theorem ringChar_residueField_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    ringChar (Y.residueField (f x)) = ringChar (X.residueField x) := by
  rw [ringChar.eq_iff, (f.residueFieldMap x).hom.charP_iff_charP]
  exact ringChar.charP _

/-- Residue field characteristics agree at `x` and at any `y` with `f x = y`. -/
private theorem ringChar_residueField_eq_of_apply_eq {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} {y : Y}
    (hxy : f x = y) : ringChar (Y.residueField y) = ringChar (X.residueField x) := by
  subst hxy
  exact ringChar_residueField_eq f x

/-- Injectivity of `spR` transfers to `sp` along compatible maps with `eη` injective. -/
private theorem injective_of_comm {α β γ δ : Type*} (sp : α → β) (spR : γ → δ) (eη : α → γ)
    (eo : β → δ) (hη : Function.Injective eη) (hcomm : ∀ a, eo (sp a) = spR (eη a))
    (hinj : Function.Injective spR) : Function.Injective sp := fun a₁ a₂ hγ ↦
  hη (hinj (by rw [← hcomm a₁, ← hcomm a₂, hγ]))

/-- **Injectivity of specialization maps over an affine base reduces to a Noetherian base.** Let
`f : X ⟶ S` be smooth and proper with geometrically connected fibres, `S` affine, and let
`sp : π₁(X_{s̄'}) → π₁(X_{s̄})` be a specialization map with `κ(s)` of characteristic zero. If
every specialization map of a smooth proper morphism with geometrically connected fibres over a
Noetherian base whose special point has residue characteristic zero is injective, then `sp` is
injective.

`f` is the base change of such a morphism over a Noetherian affine base by absolute Noetherian
approximation, and injectivity descends along the resulting cartesian square because the induced
morphisms of geometric fibres are isomorphisms. -/
theorem injective_isSpecializationMap_of_isAffine_of_forall_isNoetherian {X S : Scheme.{u}}
    [IsAffine S] (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (s' s : GeometricPoint S)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp)
    (hchar : ringChar (S.residueField (s.hom default)) = 0)
    (H : ∀ (T Y : Scheme.{u}) (h : Y ⟶ T) [IsNoetherian T] [IsProper h] [Smooth h]
        [GeometricallyConnected h] (t' t : GeometricPoint T)
        (y' : GeometricPoint (fiberOverGeometricPoint h t'))
        (y : GeometricPoint (fiberOverGeometricPoint h t))
        (spT : EtaleFundamentalGroup (fiberOverGeometricPoint h t') y' →ₜ*
          EtaleFundamentalGroup (fiberOverGeometricPoint h t) y),
        ringChar (T.residueField (t.hom default)) = 0 →
          IsSpecializationMap h t' t y' y spT → Function.Injective spT) :
    Function.Injective sp := by
  obtain ⟨T, Y, h, q, q', hnoeth, hproper, hsmooth, hgconn, hpb⟩ :=
    exists_isPullback_isNoetherian_properSmoothGeometricallyConnected f
  have := hnoeth
  have := hproper
  have := hsmooth
  have := hgconn
  have hcharT : ringChar (T.residueField ((s.map q).hom default)) = 0 :=
    (ringChar_residueField_eq_of_apply_eq q rfl).trans hchar
  exact injective_isSpecializationMap_of_isPullback q' f h q hpb s' s x' x sp hsp
    fun sp' hsp' ↦ H T Y h (s'.map q) (s.map q) _ _ sp' hcharT hsp'

/-- **Injectivity of specialization maps reduces to a Noetherian base.** The same statement as
`AlgebraicGeometry.injective_isSpecializationMap_of_isAffine_of_forall_isNoetherian` over an
arbitrary base.

By [Stacks, Tag 0C0M] `sp` is isomorphic to the specialization map of the base change of `f` to
the spectrum of a strictly henselian valuation ring over `S`, which is affine; that base change is
again smooth and proper with geometrically connected fibres, and the residue field of the closed
point of the valuation ring receives the residue field of `s`. -/
theorem injective_isSpecializationMap_of_forall_isNoetherian {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Smooth f] [GeometricallyConnected f] (s' s : GeometricPoint S)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp)
    (hchar : ringChar (S.residueField (s.hom default)) = 0)
    (H : ∀ (T Y : Scheme.{u}) (h : Y ⟶ T) [IsNoetherian T] [IsProper h] [Smooth h]
        [GeometricallyConnected h] (t' t : GeometricPoint T)
        (y' : GeometricPoint (fiberOverGeometricPoint h t'))
        (y : GeometricPoint (fiberOverGeometricPoint h t))
        (spT : EtaleFundamentalGroup (fiberOverGeometricPoint h t') y' →ₜ*
          EtaleFundamentalGroup (fiberOverGeometricPoint h t) y),
        ringChar (T.residueField (t.hom default)) = 0 →
          IsSpecializationMap h t' t y' y spT → Function.Injective spT) :
    Function.Injective sp := by
  obtain ⟨R, hR, hdom, hval, hsh, -, -, r, η, o, yη, yo, spR, -, -, -, -, -, hro, hspR,
    eη, eo, hcomm⟩ :=
    exists_isSpecializationMap_isomorphic_over_strictlyHenselianValuationRing f s' s x' x sp hsp
  let := hR
  let := hdom
  let := hval
  let := hsh
  have : Smooth (pullback.snd f r) := inferInstance
  have hcharR : ringChar ((Spec (.of R)).residueField (o.hom default)) = 0 :=
    (ringChar_residueField_eq_of_apply_eq r hro).symm.trans hchar
  have hinjR : Function.Injective spR :=
    injective_isSpecializationMap_of_isAffine_of_forall_isNoetherian (pullback.snd f r) η o
      yη yo spR hspR hcharR H
  exact injective_of_comm sp spR eη eo eη.injective hcomm hinjR

/-- **Injectivity of specialization maps over a Noetherian base reduces to a strictly henselian
discrete valuation ring.** Let `f : X ⟶ S` be smooth and proper with geometrically connected
fibres over a Noetherian base and let `sp : π₁(X_{s̄'}) → π₁(X_{s̄})` be a specialization map with
`κ(s)` of characteristic zero. If the specialization map from the generic to the closed point of a
smooth proper morphism with geometrically connected fibres over a strictly henselian discrete
valuation ring with algebraically closed residue field of characteristic zero is always injective,
then `sp` is injective.

This is [Stacks, Tag 0C0N]: `sp` is isomorphic to the specialization map of the base change of `f`
to the spectrum of such a discrete valuation ring over `S`. -/
theorem injective_isSpecializationMap_of_isNoetherian_of_forall_isDiscreteValuationRing
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsProper f] [Smooth f]
    [GeometricallyConnected f] (s' s : GeometricPoint S)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp)
    (hchar : ringChar (S.residueField (s.hom default)) = 0)
    (H : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        [StrictlyHenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
        (Y : Scheme.{u}) (h : Y ⟶ Spec (.of R)) [IsProper h] [Smooth h]
        [GeometricallyConnected h] (η o : GeometricPoint (Spec (.of R)))
        (yη : GeometricPoint (fiberOverGeometricPoint h η))
        (yo : GeometricPoint (fiberOverGeometricPoint h o))
        (spR : EtaleFundamentalGroup (fiberOverGeometricPoint h η) yη →ₜ*
          EtaleFundamentalGroup (fiberOverGeometricPoint h o) yo),
        η.hom default = genericPoint (Spec (.of R)) →
          o.hom default = IsLocalRing.closedPoint R →
            ringChar ((Spec (.of R)).residueField (o.hom default)) = 0 →
              IsSpecializationMap h η o yη yo spR → Function.Injective spR) :
    Function.Injective sp := by
  obtain ⟨R, hR, hdom, hdvr, hsh, halg, r, η, o, yη, yo, spR, hηgen, hoclosed, -, hro, hspR,
    eη, eo, hcomm⟩ :=
    exists_isSpecializationMap_isomorphic_over_strictlyHenselianDVR f s' s x' x sp hsp
  let := hR
  let := hdom
  let := hdvr
  let := hsh
  let := halg
  have : Smooth (pullback.snd f r) := inferInstance
  have hcharR : ringChar ((Spec (.of R)).residueField (o.hom default)) = 0 :=
    (ringChar_residueField_eq_of_apply_eq r hro).symm.trans hchar
  have hinjR : Function.Injective spR :=
    H R (pullback f r) (pullback.snd f r) η o yη yo spR hηgen hoclosed hcharR hspR
  exact injective_of_comm sp spR eη eo eη.injective hcomm hinjR

/-- **Injectivity of specialization maps reduces to a strictly henselian discrete valuation
ring.** Let `f : X ⟶ S` be smooth and proper with geometrically connected fibres over an arbitrary
base and let `sp : π₁(X_{s̄'}) → π₁(X_{s̄})` be a specialization map with `κ(s)` of characteristic
zero. If the specialization map from the generic to the closed point of a smooth proper morphism
with geometrically connected fibres over a strictly henselian discrete valuation ring with
algebraically closed residue field of characteristic zero is always injective, then `sp` is
injective.

These are the first two paragraphs of the proof of [Stacks, Tag 0C0Q]: the base is made affine by
[Stacks, Tag 0C0M], then Noetherian by absolute Noetherian approximation together with
[Stacks, Tag 0C0K], then the spectrum of a strictly henselian discrete valuation ring by
[Stacks, Tag 0C0N]. The remaining input is the content of the rest of the proof. -/
theorem injective_isSpecializationMap_of_forall_isDiscreteValuationRing {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f] (s' s : GeometricPoint S)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp)
    (hchar : ringChar (S.residueField (s.hom default)) = 0)
    (H : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        [StrictlyHenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
        (Y : Scheme.{u}) (h : Y ⟶ Spec (.of R)) [IsProper h] [Smooth h]
        [GeometricallyConnected h] (η o : GeometricPoint (Spec (.of R)))
        (yη : GeometricPoint (fiberOverGeometricPoint h η))
        (yo : GeometricPoint (fiberOverGeometricPoint h o))
        (spR : EtaleFundamentalGroup (fiberOverGeometricPoint h η) yη →ₜ*
          EtaleFundamentalGroup (fiberOverGeometricPoint h o) yo),
        η.hom default = genericPoint (Spec (.of R)) →
          o.hom default = IsLocalRing.closedPoint R →
            ringChar ((Spec (.of R)).residueField (o.hom default)) = 0 →
              IsSpecializationMap h η o yη yo spR → Function.Injective spR) :
    Function.Injective sp := by
  refine injective_isSpecializationMap_of_forall_isNoetherian f s' s x' x sp hsp hchar ?_
  intro T Y h hN hP hS hG t' t y' y spT hcharT hspT
  have := hN
  have := hP
  have := hS
  have := hG
  exact injective_isSpecializationMap_of_isNoetherian_of_forall_isDiscreteValuationRing h t' t
    y' y spT hspT hcharT H

end AlgebraicGeometry

end
