module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FiniteMorphism

/-!
# Pseudo-coherence descends along a finite pseudo-coherent morphism

Let `f : X ⟶ Y` be a finite morphism of schemes such that the direct image `f_*𝒪_X` of its
structure sheaf is a pseudo-coherent `𝒪_Y`-module — equivalently, by Stacks 0AVX, such that `f`
is a pseudo-coherent morphism. Let `E` be an object of `D_{QCoh}(𝒪_X)`. Then `E` is
`m`-pseudo-coherent on `X` if and only if `Rf_*E` is `m`-pseudo-coherent on `Y`.

## Main results

* `AlgebraicGeometry.isPseudoCoherentFrom_iff_derivedPushforward_of_pseudoCoherent`: the
  equivalence with the hypothesis that `f` is pseudo-coherent.
* `AlgebraicGeometry.isPseudoCoherentFrom_iff_derivedPushforward_of_isFinite`: the equivalence
  with the hypothesis that `f_*𝒪_X` is a pseudo-coherent `𝒪_Y`-module.
* `AlgebraicGeometry.isPseudoCoherent_iff_derivedPushforward_of_isFinite`: the same statement for
  pseudo-coherence in all degrees at once.

## Implementation notes

Both shapes of the hypothesis are stated: that `f_*𝒪_X` is a pseudo-coherent `𝒪_Y`-module, and
that `f` is pseudo-coherent. They are interchangeable for a finite morphism by
`AlgebraicGeometry.pseudoCoherent_iff_isPseudoCoherent_pushforward_unit`.

Membership in `D_{QCoh}(𝒪_X)` is spelled as quasi-coherence of every cohomology sheaf of `E`.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.12.6 (09VB)](https://stacks.math.columbia.edu/tag/09VB)
* [The Stacks Project, Lemma 37.60.8 (0AVX)](https://stacks.math.columbia.edu/tag/0AVX)
* [The Stacks Project, Tag 09UK](https://stacks.math.columbia.edu/tag/09UK)
* [The Stacks Project, Tag 09UU](https://stacks.math.columbia.edu/tag/09UU)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- Let `f : X ⟶ Y` be a finite morphism of schemes which is pseudo-coherent, and let `E` be an
object of `D(𝒪_X)` with quasi-coherent cohomology sheaves. Then `E` is `m`-pseudo-coherent on `X`
if and only if `Rf_*E` is `m`-pseudo-coherent on `Y`. -/
theorem isPseudoCoherentFrom_iff_derivedPushforward_of_pseudoCoherent {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [PseudoCoherent f] (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (m : ℤ) :
    RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E m ↔
      RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace)
        ((RingedSpace.derivedPushforward f.toLRSHom.toShHom).obj E) m :=
  (Scheme.Hom.isPseudoCoherentFrom_iff_of_pseudoCoherent f E m).symm.trans
    ((Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward f f (𝟙 Y) (Category.comp_id f)
        E hE m).trans
      (Scheme.Hom.derivedPushforwardRelative_iff_pseudoCoherentFrom f (𝟙 Y) E m))

/-- Let `f : X ⟶ Y` be a finite morphism of schemes such that `f_*𝒪_X` is pseudo-coherent as an
`𝒪_Y`-module, that is, such that the object of `D(𝒪_Y)` it determines in degree zero is
pseudo-coherent in the sense of Stacks 08CB. Let `E` be an object of `D_{QCoh}(𝒪_X)`. Then `E` is
`m`-pseudo-coherent if and only if `Rf_*E` is `m`-pseudo-coherent. -/
@[stacks 09VB]
theorem isPseudoCoherentFrom_iff_derivedPushforward_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f]
    (hf : RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace)
      ((DerivedCategory.singleFunctor Y.Modules 0).obj
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))))
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (m : ℤ) :
    RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E m ↔
      RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace)
        ((RingedSpace.derivedPushforward f.toLRSHom.toShHom).obj E) m :=
  let : PseudoCoherent f := (pseudoCoherent_iff_isPseudoCoherent_pushforward_unit f).mpr hf
  isPseudoCoherentFrom_iff_derivedPushforward_of_pseudoCoherent f E hE m

/-- For `f : X ⟶ Y` finite with `f_*𝒪_X` a pseudo-coherent `𝒪_Y`-module and `E` an object of
`D_{QCoh}(𝒪_X)`, the object `E` is pseudo-coherent on `X` if and only if `Rf_*E` is
pseudo-coherent on `Y`. -/
theorem isPseudoCoherent_iff_derivedPushforward_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f]
    (hf : RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace)
      ((DerivedCategory.singleFunctor Y.Modules 0).obj
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))))
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) :
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E ↔
      RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace)
        ((RingedSpace.derivedPushforward f.toLRSHom.toShHom).obj E) :=
  (RingedSpace.isPseudoCoherent_iff_forall (X := X.toRingedSpace) E).trans
    ((forall_congr' fun m =>
        isPseudoCoherentFrom_iff_derivedPushforward_of_isFinite f hf E hE m).trans
      (RingedSpace.isPseudoCoherent_iff_forall (X := Y.toRingedSpace) _).symm)

end AlgebraicGeometry

end
