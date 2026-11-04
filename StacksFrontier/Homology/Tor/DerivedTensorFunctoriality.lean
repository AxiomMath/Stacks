module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.TensorComplex.ExactFunctor
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of the derived tensor product in the second variable

Let `R → A` be a homomorphism of commutative rings. For a complex `N` of `A`-modules, the
derived functor `- ⊗ᴸ_R N : D(R) ⥤ D(A)` is the total left derived functor of the ordinary
tensor-total construction `M ↦ Tot(A ⊗_R M ⊗_A N)`.

A map `f : L ⟶ N` of complexes of `A`-modules induces a natural transformation
`- ⊗ᴸ_R L ⟶ - ⊗ᴸ_R N`, obtained from `1 ⊗ f` by the universal property of the left derived
functor; it is an isomorphism as soon as `f` is a quasi-isomorphism.

The two rings are related by nothing but a ring map, so their universes `uR` and `uA` are
independent here, and so is the module universe: a derived tensor product along `R → A` has to
accommodate the modules of both rings at once, so it cannot be tied to either ring's universe.
The modules therefore live at `max v uR uA` for an independent `v`. Change of scalars is
`CochainComplex.extendScalarsLarge` and tensoring is `CochainComplex.tensorRightLarge`, both of
which use the lifted monoidal structure on `ModuleCat.{max v uR uA} A`; Mathlib's own monoidal
structure on `ModuleCat` exists only when the module universe agrees with the ring's, its
tensor unit being `R` itself.

## Main results

* `CochainComplex.DerivedTensor.exists_derivedTensorNatTrans_isIso_of_quasiIso`: the induced
  transformation between any two chosen left-derived models, its characterization by the
  ordinary tensor map, and its invertibility for a quasi-isomorphism.
* `CochainComplex.DerivedTensor.exists_derivedTensorNatTrans_isIso_of_quasiIso_sameUniverse`:
  its specialization to one universe for both rings and all the modules, phrased with the
  same-universe `CochainComplex.extendScalars` and `TrightCochain`.

## Implementation notes

The transformation is produced by the universal property, so it is independent of the models
chosen for the two derived functors, and the displayed factorization pins it down uniquely.

Invertibility is checked on the image of a K-flat complex `K`, which suffices because every
object of `D(R)` is represented by one. On such a `K` both counits are invertible, extension of
scalars carries `K` to a K-flat complex of `A`-modules, and tensoring a K-flat complex with a
quasi-isomorphism again gives a quasi-isomorphism. K-flatness over the source ring is
`CochainComplex.KFlat.{uR, max v uA}` and over the target ring
`CochainComplex.KFlat.{uA, max v uR}`: one and the same module universe `max v uR uA`, with the
two rings exchanging places in the first slot.

## References

* [The Stacks Project, Tag 0BYK](https://stacks.math.columbia.edu/tag/0BYK)
-/

@[expose] public noncomputable section

open CategoryTheory

universe uR uA v

namespace CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

open CochainComplex.KFlat

/-- The specified counit of any left-derived model of the change-of-rings tensor functor is
invertible on a K-flat complex: uniqueness of left derived functors identifies the model with
the normalized construction, whose counit is invertible there. -/
private lemma isIso_leftDerived_counit_app_kFlat
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (φ : R →+* A)
    (X : CochainComplex (ModuleCat.{max v uR uA} A) ℤ)
    (FX : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (αX : DerivedCategory.Q ⋙ FX ⟶
      (extendScalarsLarge.{v, uR, uA} φ ⋙ tensorRightLarge.{uA, max v uR} X) ⋙
        DerivedCategory.Q)
    [FX.IsLeftDerivedFunctor αX
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) (hK : KFlat.{uR, max v uA} K) :
    IsIso (αX.app K) := by
  let T := canonicalDerivedTensorChangeOfRings.{uR, uA, v} φ X
  let W := HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ)
  let β : DerivedCategory.Q ⋙ T.F ⟶
      (extendScalarsLarge.{v, uR, uA} φ ⋙ tensorRightLarge.{uA, max v uR} X) ⋙
        DerivedCategory.Q :=
    T.alphaF ≫ Functor.whiskerRight T.directTensorComparison.hom DerivedCategory.Q
  let : T.F.IsLeftDerivedFunctor β W := T.isLeftDerived_directCounit
  let eFX : T.F ≅ FX := Functor.leftDerivedNatIso T.F FX β αX W (Iso.refl _)
  have hfac : Functor.whiskerLeft DerivedCategory.Q eFX.hom ≫ αX = β := by
    simp [eFX]
  have : IsIso (T.alphaF.app K) := T.isIso_alphaF K hK
  have : IsIso (β.app K) := by
    change IsIso (T.alphaF.app K ≫ DerivedCategory.Q.map (T.directTensorComparison.hom.app K))
    infer_instance
  have h := NatTrans.congr_app hfac K
  dsimp at h
  rw [← isIso_comp_left_iff (eFX.hom.app (DerivedCategory.Q.obj K)), h]
  infer_instance

/-- A map `f : L ⟶ N` of complexes of `A`-modules induces a natural
transformation `1 ⊗ᴸ f` between any chosen left-derived models of the change-of-rings tensor
functors `- ⊗ᴸ_R L` and `- ⊗ᴸ_R N`. The compatibility equation says that this is the
transformation induced by the ordinary tensor map `1 ⊗ f`. If `f` is a quasi-isomorphism, the
induced transformation is an isomorphism of functors.

The source ring universe `uR`, the target ring universe `uA` and the module universe are
mutually independent: the two rings are related by nothing but `φ`, and the modules of both
rings have to fit in one category, so they live at `max v uR uA`. -/
@[stacks 0BYK]
public theorem exists_derivedTensorNatTrans_isIso_of_quasiIso
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (φ : R →+* A)
    {L N : CochainComplex (ModuleCat.{max v uR uA} A) ℤ}
    (f : L ⟶ N)
    (FL FN : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (αL : DerivedCategory.Q ⋙ FL ⟶
      (extendScalarsLarge.{v, uR, uA} φ ⋙ tensorRightLarge.{uA, max v uR} L) ⋙
        DerivedCategory.Q)
    (αN : DerivedCategory.Q ⋙ FN ⟶
      (extendScalarsLarge.{v, uR, uA} φ ⋙ tensorRightLarge.{uA, max v uR} N) ⋙
        DerivedCategory.Q)
    [CategoryTheory.Functor.IsLeftDerivedFunctor FL αL
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))]
    [CategoryTheory.Functor.IsLeftDerivedFunctor FN αN
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))] :
    letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} A) :=
      ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR}
    letI : MonoidalCategory (ModuleCat.{max v uR uA} A) :=
      ModuleCat.liftedModuleMonoidal.{uA, max v uR}
    let tensorMap :
        (extendScalarsLarge.{v, uR, uA} φ ⋙ tensorRightLarge.{uA, max v uR} L) ⋙
            DerivedCategory.Q ⟶
          (extendScalarsLarge.{v, uR, uA} φ ⋙ tensorRightLarge.{uA, max v uR} N) ⋙
            DerivedCategory.Q :=
      CategoryTheory.Functor.whiskerRight
        (CategoryTheory.Functor.whiskerLeft (extendScalarsLarge.{v, uR, uA} φ)
          ((CategoryTheory.MonoidalCategory.curriedTensor
            (ModuleCat.{max v uR uA} A)).map₂CochainComplex.flip.map f))
        DerivedCategory.Q
    ∃ t : FL ⟶ FN,
      CategoryTheory.Functor.whiskerLeft DerivedCategory.Q t ≫ αN = αL ≫ tensorMap ∧
        (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} A) (ComplexShape.up ℤ) f →
          IsIso t) := by
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} A) :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR}
  let : MonoidalCategory (ModuleCat.{max v uR uA} A) :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR}
  dsimp only
  let tensorMap :=
    Functor.whiskerRight
      (Functor.whiskerLeft (extendScalarsLarge.{v, uR, uA} φ)
        ((MonoidalCategory.curriedTensor
          (ModuleCat.{max v uR uA} A)).map₂CochainComplex.flip.map f))
      DerivedCategory.Q
  let t := Functor.leftDerivedNatTrans FL FN αL αN
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ)) tensorMap
  refine ⟨t, Functor.leftDerivedNatTrans_fac FL FN αL αN
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ)) tensorMap,
    fun hf ↦ ?_⟩
  dsimp [t]
  have : QuasiIso f := hf
  rw [NatTrans.isIso_iff_isIso_app]
  intro Y
  rw [← NatTrans.isIso_app_iff_of_iso t
    (DerivedCategory.Q.objObjPreimageIso Y)]
  obtain ⟨K, r, hK, hKflat, hr, hsurj⟩ :=
    exists_kFlat_resolution.{uR, max v uA} (DerivedCategory.Q.objPreimage Y)
  have : QuasiIso r := hr
  have : IsIso (DerivedCategory.Q.map r) := by
    rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]
  have hαL : IsIso (αL.app K) :=
    isIso_leftDerived_counit_app_kFlat φ L FL αL K hK
  have hαN : IsIso (αN.app K) :=
    isIso_leftDerived_counit_app_kFlat φ N FN αN K hK
  have htmap : IsIso (tensorMap.app K) := by
    dsimp [tensorMap]
    change IsIso (DerivedCategory.Q.map
      ((TleftCochain ((extendScalarsLarge.{v, uR, uA} φ).obj K)).map f))
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact quasiIso_tleft_map_of_kFlat.{uA, max v uR} _
      (ScalarBaseChange.kFlat_extendScalars.{uR, uA, v} φ K hK) f
  have htK : IsIso (t.app (DerivedCategory.Q.obj K)) := by
    have hfac := Functor.leftDerivedNatTrans_app FL FN αL αN
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ)) tensorMap K
    change t.app (DerivedCategory.Q.obj K) ≫ αN.app K =
      αL.app K ≫ tensorMap.app K at hfac
    rw [← isIso_comp_right_iff _ (αN.app K), hfac]
    exact IsIso.comp_isIso' hαL htmap
  rw [← isIso_comp_left_iff (FL.map (DerivedCategory.Q.map r)), t.naturality]
  infer_instance

universe u

/-- The specialization of `exists_derivedTensorNatTrans_isIso_of_quasiIso` to one universe:
both rings and all the modules in `Type u`. At `uR = uA = v = u` the large-universe change of
scalars and tensor-total functors are the same functors as the same-universe ones —
`CochainComplex.extendScalarsLarge.{u, u, u} = CochainComplex.extendScalars` and
`CochainComplex.tensorRightLarge.{u, u} = TrightCochain`, both by `rfl`, the lifted monoidal
structure differing from Mathlib's only in a tensor unit that the tensor-total functor never
mentions. The two universal-property hypotheses have to be handed over explicitly, since
instance synthesis matches only up to reducible unfolding and would not see through
`extendScalarsLarge` to `extendScalars`. -/
public theorem exists_derivedTensorNatTrans_isIso_of_quasiIso_sameUniverse
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    {L N : CochainComplex (ModuleCat.{u} A) ℤ}
    (f : L ⟶ N)
    (FL FN : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (αL : DerivedCategory.Q ⋙ FL ⟶
      (CochainComplex.extendScalars φ ⋙ TrightCochain L) ⋙ DerivedCategory.Q)
    (αN : DerivedCategory.Q ⋙ FN ⟶
      (CochainComplex.extendScalars φ ⋙ TrightCochain N) ⋙ DerivedCategory.Q)
    [hL : CategoryTheory.Functor.IsLeftDerivedFunctor FL αL
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    [hN : CategoryTheory.Functor.IsLeftDerivedFunctor FN αN
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))] :
    let tensorMap :
        (CochainComplex.extendScalars φ ⋙ TrightCochain L) ⋙ DerivedCategory.Q ⟶
          (CochainComplex.extendScalars φ ⋙ TrightCochain N) ⋙ DerivedCategory.Q :=
      CategoryTheory.Functor.whiskerRight
        (CategoryTheory.Functor.whiskerLeft (CochainComplex.extendScalars φ)
          ((CategoryTheory.MonoidalCategory.curriedTensor
            (ModuleCat.{u} A)).map₂CochainComplex.flip.map f))
        DerivedCategory.Q
    ∃ t : FL ⟶ FN,
      CategoryTheory.Functor.whiskerLeft DerivedCategory.Q t ≫ αN = αL ≫ tensorMap ∧
        (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ) f → IsIso t) :=
  @exists_derivedTensorNatTrans_isIso_of_quasiIso.{u, u, u}
    R A ‹CommRing R› ‹CommRing A› φ L N f FL FN αL αN hL hN

end CochainComplex.DerivedTensor

end
