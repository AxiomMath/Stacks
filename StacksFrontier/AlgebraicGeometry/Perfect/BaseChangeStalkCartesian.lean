module

public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Local rings in an abstract cartesian square of schemes

`StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk` identifies the local ring of a
*categorical* fibre product `pullback f g` as a localization of the tensor product of the
local rings at the three other corners.  Consumers state their squares as
`CategoryTheory.IsPullback g' f' f g` with an abstract upper-left corner, so this file
transports that identification along `IsPullback.isoPullback` and records the consequence that
is actually used downstream: the induced ring map out of the tensor product is flat.

## Main results

* `AlgebraicGeometry.BaseChangeStalk.cartesian_stalk_isLocalization`: for a cartesian square of
  schemes and a point `x'` of its upper-left corner, the local ring `O_{X', x'}` is a
  localization of `O_{X,g' x'} ⊗_{O_{S, f (g' x')}} O_{S', f' x'}`, by a ring map restricting on
  the two factors to the two stalk maps.
* `AlgebraicGeometry.BaseChangeStalk.cartesian_stalk_tensor_flat`: for a cartesian square of
  schemes and a point `x'` of its upper-left corner, there is a flat ring map
  `O_{X,g' x'} ⊗_{O_{S, f (g' x')}} O_{S', f' x'} → O_{X', x'}` restricting on the two factors
  to the two stalk maps.

## Implementation notes

The square's commutativity `hpb.w` appears in the statement only through the equality of the
two images of `x'` in `S`, so it is generalized away before `g'` and `f'` are substituted by
their factorizations through `IsPullback.isoPullback`.  Flatness of the composite is flatness
of the localization map composed with a stalk map that is an isomorphism, the latter because
`IsPullback.isoPullback` is an isomorphism of schemes.

Three points about spellings.

`pullback_stalk_tensor_flat` repeats the `let` preamble of `pullback_stalk_isLocalization`
verbatim, including `R := Y.presheaf.stalk ((pX ≫ f).base x')`, so that the obtained ring map
and the asserted one have the *same* instance arguments; the two algebra instances the
preamble installs with `letI` are inlined rather than bound, so they must be re-installed in
the proof with `letI` before `RingHom.Flat` can even be elaborated.  Without that,
`φ.Flat` leaves the `CommRing` of the tensor product a metavariable under a projection and
the application is rejected.

`cartesian_stalk_tensor_flat`, by contrast, ascribes its point equality at
`f.base (g'.base x') = g.base (f'.base x')` rather than at `(g' ≫ f).base x' = (f' ≫ g).base x'`.
That is the spelling
`BaseChangeTorAmplitude.ringTorIndependent_of_schemeTorIndependent_stalks` uses, and the two
differ in the *object* arguments of the `eqToHom` carrying the second base action, which proof
irrelevance does not reconcile.  With the composite spelling here, a consumer that pins
`Algebra R B` from the Tor-independence hypothesis cannot find the `IsScalarTower` instances
stated at the other spelling.

The equations are closed pointwise, with `congrArg` and `Eq.trans` against
`Scheme.Hom.stalkMap_comp`, not by `rw`: the rewrites do not find their pattern, because the
goal carries both spellings of the composite's action on `x'`.

## References

* [Stacks Project, Tag 0C0V](https://stacks.math.columbia.edu/tag/0C0V)
-/

open CategoryTheory Limits
open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.BaseChangeStalk

/-- The flatness consequence of `pullback_stalk_isLocalization`, stated at the categorical
fibre product, i.e. in the spelling that theorem itself uses. -/
public theorem pullback_stalk_tensor_flat
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (x' : (pullback f g).carrier) :
    let pX : pullback f g ⟶ X := pullback.fst f g
    let pY : pullback f g ⟶ Y' := pullback.snd f g
    let h : (pX ≫ f).base x' = (pY ≫ g).base x' :=
      congrArg (fun k : pullback f g ⟶ Y => k.base x') pullback.condition
    let R := Y.presheaf.stalk ((pX ≫ f).base x')
    let A := X.presheaf.stalk (pX.base x')
    let B := Y'.presheaf.stalk (pY.base x')
    let C := (pullback f g).presheaf.stalk x'
    letI : Algebra R A := (f.stalkMap (pX.base x')).hom.toAlgebra
    letI : Algebra R B :=
      ((eqToHom (congrArg Y.presheaf.stalk h)) ≫ g.stalkMap (pY.base x')).hom.toAlgebra
    ∃ φ : TensorProduct R A B →+* C,
      φ.comp Algebra.TensorProduct.includeLeftRingHom = (pX.stalkMap x').hom ∧
      φ.comp Algebra.TensorProduct.includeRight.toRingHom = (pY.stalkMap x').hom ∧
      φ.Flat := by
  intro pX pY h R A B C
  let instA : Algebra R A := (f.stalkMap (pX.base x')).hom.toAlgebra
  let instB : Algebra R B :=
    ((eqToHom (congrArg Y.presheaf.stalk h)) ≫ g.stalkMap (pY.base x')).hom.toAlgebra
  obtain ⟨φ, hleft, hright, M, hloc⟩ := pullback_stalk_isLocalization f g x'
  refine ⟨φ, hleft, hright, ?_⟩
  let : Algebra (TensorProduct R A B) C := φ.toAlgebra
  have : IsLocalization M C := hloc
  exact IsLocalization.flat C M

/-- The local ring at a point of the upper-left corner of a cartesian square of schemes is a
localization of the tensor product of the local rings at its two images over the local ring of
the base. This is `AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization` transported
along `CategoryTheory.IsPullback.isoPullback`: the transport is an isomorphism of algebras over
the tensor product, and being a localization is invariant under such an isomorphism. -/
public theorem cartesian_stalk_isLocalization
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (hpb : IsPullback g' f' f g) (x' : X') :
    let h : f.base (g'.base x') = g.base (f'.base x') :=
      congrArg (fun k : X' ⟶ S => k.base x') hpb.w
    let R := S.presheaf.stalk (f.base (g'.base x'))
    let A := X.presheaf.stalk (g'.base x')
    let B := S'.presheaf.stalk (f'.base x')
    let C := X'.presheaf.stalk x'
    letI : Algebra R A := (f.stalkMap (g'.base x')).hom.toAlgebra
    letI : Algebra R B :=
      (eqToHom (congrArg (fun z => S.presheaf.stalk z) h) ≫
        g.stalkMap (f'.base x')).hom.toAlgebra
    ∃ φ : TensorProduct R A B →+* C,
      φ.comp Algebra.TensorProduct.includeLeftRingHom = (g'.stalkMap x').hom ∧
      φ.comp Algebra.TensorProduct.includeRight.toRingHom = (f'.stalkMap x').hom ∧
      letI : Algebra (TensorProduct R A B) C := φ.toAlgebra
      ∃ M : Submonoid (TensorProduct R A B), IsLocalization M C := by
  let e := hpb.isoPullback
  have hg' : g' = e.hom ≫ pullback.fst f g := hpb.isoPullback_hom_fst.symm
  have hf' : f' = e.hom ≫ pullback.snd f g := hpb.isoPullback_hom_snd.symm
  clear_value e
  generalize hw : hpb.w = w
  clear hw hpb
  subst g' f'
  intro h R A B C
  let instA : Algebra R A :=
    (f.stalkMap ((e.hom ≫ pullback.fst f g).base x')).hom.toAlgebra
  let instB : Algebra R B :=
    (eqToHom (congrArg (fun z => S.presheaf.stalk z) h) ≫
      g.stalkMap ((e.hom ≫ pullback.snd f g).base x')).hom.toAlgebra
  obtain ⟨φ, hleft, hright, M, hloc⟩ :=
    pullback_stalk_isLocalization f g (e.hom.base x')
  refine ⟨(e.hom.stalkMap x').hom.comp φ, ?_, ?_, ?_⟩
  · refine RingHom.ext fun a => ?_
    refine (congrArg (fun z => (e.hom.stalkMap x').hom z)
      (DFunLike.congr_fun hleft a)).trans ?_
    exact (DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp
      (Scheme.Hom.stalkMap_comp e.hom (pullback.fst f g) x')) a).symm
  · refine RingHom.ext fun a => ?_
    refine (congrArg (fun z => (e.hom.stalkMap x').hom z)
      (DFunLike.congr_fun hright a)).trans ?_
    exact (DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp
      (Scheme.Hom.stalkMap_comp e.hom (pullback.snd f g) x')) a).symm
  · refine ⟨M, ?_⟩
    let instSource : Algebra (TensorProduct R A B)
        ((pullback f g).presheaf.stalk (e.hom.base x')) := φ.toAlgebra
    let instTarget : Algebra (TensorProduct R A B) (X'.presheaf.stalk x') :=
      ((e.hom.stalkMap x').hom.comp φ).toAlgebra
    have : @IsLocalization (TensorProduct R A B) _ M _ _ instSource := hloc
    exact IsLocalization.isLocalization_of_algEquiv M
      ({ RingEquiv.ofBijective (e.hom.stalkMap x').hom
          ((ConcreteCategory.isIso_iff_bijective (e.hom.stalkMap x')).mp inferInstance) with
          commutes' := fun _ => rfl } :
        ((pullback f g).presheaf.stalk (e.hom.base x')) ≃ₐ[TensorProduct R A B]
          (X'.presheaf.stalk x'))

/-- The local ring at a point of the upper-left corner of a cartesian square of schemes is a
flat algebra over the tensor product of the local rings at its two images over the local ring
of the base. -/
public theorem cartesian_stalk_tensor_flat
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (hpb : IsPullback g' f' f g) (x' : X') :
    let h : f.base (g'.base x') = g.base (f'.base x') :=
      congrArg (fun k : X' ⟶ S => k.base x') hpb.w
    let R := S.presheaf.stalk (f.base (g'.base x'))
    let A := X.presheaf.stalk (g'.base x')
    let B := S'.presheaf.stalk (f'.base x')
    let C := X'.presheaf.stalk x'
    letI : Algebra R A := (f.stalkMap (g'.base x')).hom.toAlgebra
    letI : Algebra R B :=
      (eqToHom (congrArg (fun z => S.presheaf.stalk z) h) ≫
        g.stalkMap (f'.base x')).hom.toAlgebra
    ∃ φ : TensorProduct R A B →+* C,
      φ.comp Algebra.TensorProduct.includeLeftRingHom = (g'.stalkMap x').hom ∧
      φ.comp Algebra.TensorProduct.includeRight.toRingHom = (f'.stalkMap x').hom ∧
      φ.Flat := by
  intro h R A B C
  let instA : Algebra R A := (f.stalkMap (g'.base x')).hom.toAlgebra
  let instB : Algebra R B :=
    (eqToHom (congrArg (fun z => S.presheaf.stalk z) h) ≫
      g.stalkMap (f'.base x')).hom.toAlgebra
  obtain ⟨φ, hleft, hright, M, hloc⟩ := cartesian_stalk_isLocalization g' f' f g hpb x'
  refine ⟨φ, hleft, hright, ?_⟩
  let : Algebra (TensorProduct R A B) C := φ.toAlgebra
  have : IsLocalization M C := hloc
  exact IsLocalization.flat C M

end AlgebraicGeometry.BaseChangeStalk
