module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitRingPresheaf
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitRestrictHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The iterated Frobenius pullback as an extension of scalars along a power of Frobenius

The diagram of Stacks Tag 0EXB is built from the `j`-fold *iterate* `(S_φ)^{∘j}` of extension
of scalars along Frobenius, not from extension of scalars along the `j`-th power `φ^j` of
Frobenius: extension of scalars is a sheafified tensor product and does not compose on the
nose. This file identifies the two, and reads off the abelian sheaf underlying the iterate:

`(S_φ)^{∘j}𝒢` has underlying abelian sheaf the sheafification of `V ↦ 𝒪_X(V) ⊗_{φ^j, 𝒪_X(V)} 𝒢(V)`.

Together with `AlgebraicGeometry.frobeniusStageExtendScalarsCompToSheafIso` this puts both the
diagram and the apex of the cocone of Tag 0EXB over one and the same objectwise construction,
the extension of scalars of presheaves of modules of
`Stacks.NoncommChangeOfRings.Presheaf.extendScalars`.

## Main definitions

* `AlgebraicGeometry.frobeniusRingSheafIter`: the `j`-th power `φ^j` of Frobenius on the
  structure sheaf, and `AlgebraicGeometry.frobeniusSelfIterStructureMap` the same morphism
  retyped as a structure map.
* `AlgebraicGeometry.frobeniusExtendScalarsIterIso`: **the `j`-fold iterate of extension of
  scalars along Frobenius is extension of scalars along `φ^j`**.

## Main results

* `AlgebraicGeometry.pushforward_frobeniusRingSheafIter`: the `j`-fold iterate of restriction
  of scalars along Frobenius *is* restriction of scalars along `φ^j`, on the nose. This is the
  statement whose two sides are definitionally equal and which the iterate of the left adjoint
  can therefore be compared through.
* `AlgebraicGeometry.frobeniusExtendScalarsIterCompToSheafIso`: **the abelian sheaf underlying
  `(S_φ)^{∘j}𝒢`** is the sheafification of the objectwise tensor product along `φ^j`.

## Implementation notes

`CategoryTheory.Functor.endoIter` recurses by composing on the right, and restriction of
scalars composes contravariantly, so the recursion for the power of Frobenius is
`φ^{j+1} = φ ≫ φ^j`; with the other convention the identification would not be an equality.
Every step of `AlgebraicGeometry.pushforward_frobeniusRingSheafIter` is then definitional,
because restriction of scalars of presheaves of modules along a composite is the composite of
the restrictions on the nose and the pushforward along the identity of a space is restriction
of scalars on the nose.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- The `j`-th power of the Frobenius endomorphism of the structure sheaf. The recursion
composes the new copy of Frobenius on the *left*, which is the order in which the iterates of
restriction of scalars compose. -/
@[sga "3 VIIA 4.3.3" "more general", sga "7 XXII 6.2" "more general"]
noncomputable def frobeniusRingSheafIter : ℕ → (X.ringSheafOnOpens ⟶ X.ringSheafOnOpens)
  | 0 => 𝟙 _
  | j + 1 => frobeniusRingSheafHom X p hX ≫ frobeniusRingSheafIter j

/-- The `j`-th power of Frobenius, read as the structure map of a morphism of ringed spaces
whose underlying continuous map is the identity of `X`, exactly as
`AlgebraicGeometry.frobeniusSelfStructureMap`. -/
noncomputable def frobeniusSelfIterStructureMap (j : ℕ) :
    X.ringSheafOnOpens ⟶
      ((Opens.map (𝟙 (X : TopCat))).sheafPushforwardContinuous RingCat.{u} _ _).obj
        X.ringSheafOnOpens :=
  frobeniusRingSheafIter X p hX j

/-- **The `j`-fold iterate of restriction of scalars along Frobenius is restriction of scalars
along the `j`-th power of Frobenius.** -/
lemma pushforward_frobeniusRingSheafIter (j : ℕ) :
    (frobeniusRestrictScalars X p hX).endoIter j =
      _root_.SheafOfModules.pushforward.{u} (frobeniusSelfIterStructureMap X p hX j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Functor.endoIter_succ, ih]
    rfl

/-- **The `j`-fold iterate of extension of scalars along Frobenius is extension of scalars
along the `j`-th power of Frobenius.** Both are left adjoint to the `j`-fold iterate of
restriction of scalars, by `AlgebraicGeometry.pushforward_frobeniusRingSheafIter`. -/
noncomputable def frobeniusExtendScalarsIterIso (j : ℕ) :
    (frobeniusExtendScalars X p hX).endoIter j ≅
      _root_.SheafOfModules.pullback.{u} (frobeniusSelfIterStructureMap X p hX j) :=
  Adjunction.leftAdjointUniq
    ((frobeniusExtendScalarsAdjunctionIter X p hX j).ofNatIsoRight
      (eqToIso (pushforward_frobeniusRingSheafIter X p hX j)))
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
      (frobeniusSelfIterStructureMap X p hX j))

/-- The hypothesis of `Stacks.SheafOfModules.pullbackIsoExtendScalars` for the `j`-th power of
Frobenius, where the presheaf of rings is the structure sheaf itself and the sheafification
comparison is the identity. -/
lemma restrictScalars_frobeniusRingSheafIter_comp (j : ℕ) :
    (_root_.SheafOfModules.forget X.ringSheafOnOpens ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringSheafOnOpens.obj)) ⋙
        PresheafOfModules.restrictScalars.{u} (frobeniusRingSheafIter X p hX j).hom =
      (_root_.SheafOfModules.forget X.ringSheafOnOpens ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringSheafOnOpens.obj)) ⋙
        PresheafOfModules.pushforward.{u} (frobeniusSelfIterStructureMap X p hX j).hom :=
  rfl

/-- **The abelian sheaf underlying `(S_φ)^{∘j}𝒢`** is the sheafification of the objectwise
tensor product `V ↦ 𝒪_X(V) ⊗_{φ^j, 𝒪_X(V)} 𝒢(V)`. -/
noncomputable def frobeniusExtendScalarsIterCompToSheafIso (j : ℕ) :
    (frobeniusExtendScalars X p hX).endoIter j ⋙
        _root_.SheafOfModules.toSheaf X.ringSheafOnOpens ≅
      _root_.SheafOfModules.forget X.ringSheafOnOpens ⋙
        Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u}
            (frobeniusRingSheafIter X p hX j).hom ⋙
          PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj ⋙
            presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u} :=
  Functor.isoWhiskerRight (frobeniusExtendScalarsIterIso X p hX j) _ ≪≫
    Stacks.SheafOfModules.pullbackCompToSheafIso (frobeniusSelfIterStructureMap X p hX j)
      (𝟙 X.ringSheafOnOpens.obj) (frobeniusRingSheafIter X p hX j).hom
      (restrictScalars_frobeniusRingSheafIter_comp X p hX j)

end AlgebraicGeometry

end
