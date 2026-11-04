module

public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackPseudofunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedCoherator.EtalePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.InvertibleDerivedSheafHomCounitOnASite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness

/-!
# Extensions on an algebraic space through the derived direct image and the derived internal Hom

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, and let `D(𝒪_X)` be the
derived category of `𝒪_X`-modules on the small étale site of `X`, at the standard model.  This
file proves, for the small étale sites of algebraic spaces, two identifications of the groups
`Ext^i_{𝒪_X}(K, E) = Hom_{D(𝒪_X)}(K, E[i])`:

* the Leray identity `H^i(X, M) = H^i(Y, Rf_* M)` (the clause of Stacks 0D6H on global sections),
  in the form `Hom(𝒪_X, M[i]) = Hom(𝒪_Y, (Rf_* M)[i])`;
* the identity `Ext^i(K, E) = H^i(X, R𝓗om(K, E))` (Stacks 08JA), in the form
  `Hom(K, E[i]) = Hom(𝒪_X, R𝓗om(K, E)[i])`.

Both are stated for the derived direct image `AlgebraicGeometry.Space.spaceDerivedPushforward`
and the derived internal Hom `AlgebraicGeometry.Space.smallEtaleDerivedSheafHom`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedPullPushAdjunction`: `Lf^* ⊣ Rf_*`, with `Rf_*` the
  functor `AlgebraicGeometry.Space.spaceDerivedPushforward`.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullStructureIso`: `Lf^* 𝒪_Y ≅ 𝒪_X`.
* `AlgebraicGeometry.Space.structureHomShiftEquivPushforward`: the Leray identity
  `Hom(𝒪_X, M[i]) ≃ Hom(𝒪_Y, (Rf_* M)[i])`.
* `AlgebraicGeometry.Space.smallEtaleDerivedLeftUnitIso`: `𝒪_X ⊗^L P ≅ P`.
* `AlgebraicGeometry.Space.homEquivStructureHomSheafHom`: `Hom(K, G) ≃ Hom(𝒪_X, R𝓗om(K, G))`.
* `AlgebraicGeometry.Space.smallEtaleDerivedSheafHomShiftIso`: `R𝓗om(K, G[i]) ≅ R𝓗om(K, G)[i]`.
* `AlgebraicGeometry.Space.homShiftEquivStructureHomSheafHom`:
  `Hom(K, G[i]) ≃ Hom(𝒪_X, R𝓗om(K, G)[i])`.
* `AlgebraicGeometry.Space.homShiftEquivOfPushforwardSheafHomIso`: from an isomorphism
  `Rf_* R𝓗om(K, E) ≅ R𝓗om(L, 𝒪_Y)`, the bijection `Hom(K, E[i]) ≃ Hom(L, 𝒪_Y[i])`.

## Main results

* `AlgebraicGeometry.Space.derivedPushforward_eq_spaceDerivedPushforward`: the derived direct
  image of the morphism of small étale ringed topoi (Stacks 07A5) is
  `AlgebraicGeometry.Space.spaceDerivedPushforward`.
* `AlgebraicGeometry.Space.isGE_spaceDerivedPushforward_obj`: `Rf_*` carries `D^{≥ n}` into
  `D^{≥ n}`.
* `AlgebraicGeometry.Space.subsingleton_pull_hom_structureObject_shift`: if `L` has no cohomology
  in positive degrees, then `Hom(Lg^*L, 𝒪[i]) = 0` for every `g` and every `i < 0`.

## References

* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_modules enoughInjectives_modules
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-! ### The derived adjunction for `AlgebraicGeometry.Space.spaceDerivedPushforward` -/

/-- **The derived direct image of the morphism of small étale ringed topoi is
`AlgebraicGeometry.Space.spaceDerivedPushforward`.** -/
theorem derivedPushforward_eq_spaceDerivedPushforward (f : X ⟶ Y) :
    Stacks.Cohomology.DerivedPushforward.derivedPushforward.{u, u, u, u + 1, u, u + 1}
      (smallEtaleRingedToposHom B S hS f) =
      spaceDerivedPushforward B S hS f := by
  unfold Stacks.Cohomology.DerivedPushforward.derivedPushforward
    Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy
  simp only [pushforwardModules_eq_modulePushforward]
  rfl

/-- **`Lf^* ⊣ Rf_*` for a morphism of algebraic spaces**, with the derived pullback of the
pullback pseudofunctor datum `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` and the
derived direct image `AlgebraicGeometry.Space.spaceDerivedPushforward`. -/
def smallEtaleDerivedPullPushAdjunction (f : X ⟶ Y) :
    (smallEtaleDerivedPullbackData B S hS).pull f ⊣ spaceDerivedPushforward B S hS f :=
  (smallEtaleDerivedModuleAdjunction B S hS f).ofNatIsoRight
    (eqToIso (derivedPushforward_eq_spaceDerivedPushforward B S hS f))

/-- **The derived pullback of the structure sheaf is the structure sheaf**: `Lf^* 𝒪_Y ≅ 𝒪_X`
for a morphism of algebraic spaces, `𝒪_Y` being placed in degree zero. -/
def smallEtaleDerivedPullStructureIso (f : X ⟶ Y) :
    ((smallEtaleDerivedPullbackData B S hS).pull f).obj (structureObject B S hS Y) ≅
      structureObject B S hS X :=
  haveI := hasDerivedModulePullbacks B S hS f
  Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackUnitIsoGeneral
    (smallEtaleRingedToposHom B S hS f)

/-- **The Leray identity for a morphism of algebraic spaces** (the clause of Stacks 0D6H on
global sections, in the Hom form): `H^i(X, M) = H^i(Y, Rf_* M)`, that is,
`Hom_{D(𝒪_X)}(𝒪_X, M[i]) ≃ Hom_{D(𝒪_Y)}(𝒪_Y, (Rf_* M)[i])`. -/
def structureHomShiftEquivPushforward (f : X ⟶ Y) (M : derivedModules B S hS X) (i : ℤ) :
    (structureObject B S hS X ⟶ M⟦i⟧) ≃
      (structureObject B S hS Y ⟶ ((spaceDerivedPushforward B S hS f).obj M)⟦i⟧) :=
  ((smallEtaleDerivedPullStructureIso B S hS f).homCongr (Iso.refl _)).symm.trans
    (((smallEtaleDerivedPullPushAdjunction B S hS f).homEquiv _ _).trans
      ((Iso.refl _).homCongr (((spaceDerivedPushforward B S hS f).commShiftIso i).app M)))

/-! ### Extensions as cohomology of the derived internal Hom -/

/-- **The left unit constraint of the derived tensor product on an algebraic space**:
`𝒪_X ⊗^L P ≅ P`. -/
def smallEtaleDerivedLeftUnitIso (P : derivedModules B S hS X) :
    ((smallEtaleDerivedTensor B S hS X).obj (structureObject B S hS X)).obj P ≅ P :=
  letI := RingedSite.derivedTensorMonoidal (smallEtaleModelRingedSite B S hS X.1 X.2)
  ((smallEtaleDerivedTensorRightIso B S hS X P).app (structureObject B S hS X)) ≪≫
    (smallEtaleModelDerivedEquivalence B S hS X).inverse.mapIso
      (((Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleModelRingedSite B S hS X.1 X.2)).flip.obj
            ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj P)).mapIso
        (smallEtaleModelDerivedStructureSheafIso B S hS X) ≪≫
        (λ_ ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj P))) ≪≫
    ((smallEtaleModelDerivedEquivalence B S hS X).unitIso.app P).symm

/-- **Morphisms in `D(𝒪_X)` are global sections of the derived internal Hom** (Stacks 08JA, in
the Hom form, for an algebraic space): `Hom(K, G) ≃ Hom(𝒪_X, R𝓗om(K, G))`. -/
def homEquivStructureHomSheafHom (K G : derivedModules B S hS X) :
    (K ⟶ G) ≃ (structureObject B S hS X ⟶ ((smallEtaleDerivedSheafHom B S hS X).obj
      (Opposite.op K)).obj G) :=
  ((smallEtaleDerivedLeftUnitIso B S hS K).homCongr (Iso.refl G)).symm.trans
    ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X K).homEquiv _ _)

/-- **`R𝓗om(K, -)` commutes with the shift**: `R𝓗om(K, G[i]) ≅ R𝓗om(K, G)[i]`. -/
def smallEtaleDerivedSheafHomShiftIso (K G : derivedModules B S hS X) (i : ℤ) :
    ((smallEtaleDerivedSheafHom B S hS X).obj (Opposite.op K)).obj (G⟦i⟧) ≅
      (((smallEtaleDerivedSheafHom B S hS X).obj (Opposite.op K)).obj G)⟦i⟧ :=
  letI : ((smallEtaleDerivedTensor B S hS X).flip.obj K).CommShift ℤ :=
    (smallEtaleDerivedTensorProduct B S hS X).commShift₂.commShiftFlipObj K
  (Adjunction.RightAdjointCommShift.iso (smallEtaleDerivedTensorSheafHomAdjunction B S hS X K)
    i).app G

/-- **`Ext^i(K, G) = H^i(X, R𝓗om(K, G))`** (Stacks 08JA, in the Hom form, for an algebraic
space): `Hom(K, G[i]) ≃ Hom(𝒪_X, R𝓗om(K, G)[i])`. -/
def homShiftEquivStructureHomSheafHom (K G : derivedModules B S hS X) (i : ℤ) :
    (K ⟶ G⟦i⟧) ≃ (structureObject B S hS X ⟶ (((smallEtaleDerivedSheafHom B S hS X).obj
      (Opposite.op K)).obj G)⟦i⟧) :=
  (homEquivStructureHomSheafHom B S hS K (G⟦i⟧)).trans
    ((Iso.refl _).homCongr (smallEtaleDerivedSheafHomShiftIso B S hS K G i))

/-- **Extensions computed by a dual on the base.**  Let `f : X ⟶ Y` be a morphism of algebraic
spaces, `K`, `E` in `D(𝒪_X)` and `L` in `D(𝒪_Y)` with `Rf_* R𝓗om(K, E) ≅ R𝓗om(L, 𝒪_Y)`.  Then
`Ext^i(K, E) ≃ Ext^i(L, 𝒪_Y)`, that is `Hom(K, E[i]) ≃ Hom(L, 𝒪_Y[i])`, for every `i`. -/
def homShiftEquivOfPushforwardSheafHomIso (f : X ⟶ Y) (K E : derivedModules B S hS X)
    (L : derivedModules B S hS Y)
    (e : (spaceDerivedPushforward B S hS f).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (Opposite.op K)).obj E) ≅
      smallEtaleDerivedDual B S hS Y L) (i : ℤ) :
    (K ⟶ E⟦i⟧) ≃ (L ⟶ (structureObject B S hS Y)⟦i⟧) :=
  (homShiftEquivStructureHomSheafHom B S hS K E i).trans
    ((structureHomShiftEquivPushforward B S hS f _ i).trans
      (((Iso.refl _).homCongr ((shiftFunctor _ i).mapIso e)).trans
        (homShiftEquivStructureHomSheafHom B S hS L (structureObject B S hS Y) i).symm))

/-! ### Vanishing of the negative extensions out of a connective object -/

/-- **`Rf_*` is left t-exact**: it carries an object of `D(𝒪_X)` with no cohomology below
degree `n` to one with no cohomology below degree `n`. -/
theorem isGE_spaceDerivedPushforward_obj (f : X ⟶ Y) (M : derivedModules B S hS X) (n : ℤ)
    (hM : M.IsGE n) : ((spaceDerivedPushforward B S hS f).obj M).IsGE n :=
  have := hM
  Stacks.DerivedFunctor.isGE_totalRightDerived_obj (modulePushforward B S hS f) M n

/-- **The negative extensions out of the pullback of a connective object vanish.**  If `L` in
`D(𝒪_Y)` has no cohomology in positive degrees, then for every morphism `g : X ⟶ Y` of algebraic
spaces and every `i < 0`, `Ext^i(Lg^*L, 𝒪_X) = Hom(Lg^*L, 𝒪_X[i]) = 0`. -/
theorem subsingleton_pull_hom_structureObject_shift (g : X ⟶ Y) (L : derivedModules B S hS Y)
    (hL : L.IsLE 0) (i : ℤ) (hi : i < 0) :
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull g).obj L ⟶
      (structureObject B S hS X)⟦i⟧) := by
  refine ((smallEtaleDerivedPullPushAdjunction B S hS g).homEquiv _ _).subsingleton_congr.2 ?_
  have := hL
  have : ((structureObject B S hS X)⟦i⟧).IsGE (-i) :=
    DerivedCategory.TStructure.t.isGE_shift _ 0 i (-i)
  have := isGE_spaceDerivedPushforward_obj B S hS g ((structureObject B S hS X)⟦i⟧) (-i)
    inferInstance
  have : ((spaceDerivedPushforward B S hS g).obj ((structureObject B S hS X)⟦i⟧)).IsGE 1 :=
    DerivedCategory.TStructure.t.isGE_of_ge _ 1 (-i)
  exact ⟨fun a b ↦ (DerivedCategory.TStructure.t.zero a 0 1).trans
    (DerivedCategory.TStructure.t.zero b 0 1).symm⟩

end AlgebraicGeometry.Space

end
