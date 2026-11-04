module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineCase
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentHomDescentIso
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentMayerVietoris
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentPerfectColimit

/-!
# Tag 0DI7 from the affine ring translation and the Mayer--Vietoris sequences

In the relative descent situation of Stacks 0DI6, for `K₀` pseudo-coherent and `L₀` in
`D_QCoh(𝒪_{X₀})` of locally finite Tor dimension over `(X₀ ⟶ S₀)⁻¹𝒪_{S₀}`, the comparison map
`colim_i Hom_{D(𝒪_{Xᵢ})}(Lf_{i0}^*K₀, Lf_{i0}^*L₀) ⟶ Hom_{D(𝒪_X)}(Lf₀^*K₀, Lf₀^*L₀)` is bijective.
The reduction of the tag to the quasi-compact opens of `X₀` leaves two hypotheses: the affine case
over an affine open of the base, here in the form of the affine ring translation
`AffineRingTranslation`, and the Mayer--Vietoris union step, in the form of the sequences
`MayerVietorisHomSequence` of Stacks 08BW. The induction runs on the family of shifts `L₀⟦n⟧` of
the second argument.

## Main results

* `homDescent_of_isPseudoCoherent_of_locallyHasFiniteTorDimension`: **Stacks 0DI7.**
* `homDescent_shift_of_mayerVietorisHomSequence`: the conclusion of the tag for the family of
  shifts `L₀⟦n⟧` of a single second argument, from the affine ring translation and the
  Mayer--Vietoris sequences.
* `homDescent_of_mayerVietorisHomSequence`: the same for `L₀`.

## References

* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Tag 08BW](https://stacks.math.columbia.edu/tag/08BW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)
  (K₀ L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))

/-- **The conclusion of Tag 0DI7 for the family of shifts of a single second argument**: if `K₀` is
pseudo-coherent, and `L₀` lies in `D_QCoh(𝒪_{X₀})` and has finite Tor dimension over `S₀`, then the
conclusion of the tag holds for every shift `L₀⟦n⟧`, given the affine ring translation `hdict` over
every affine open lying over an affine open of the base and the Mayer--Vietoris sequences `mv`. -/
theorem homDescent_shift_of_mayerVietorisHomSequence
    (hK₀ : RingedSpace.IsPseudoCoherent (X := D.X₀.left.toRingedSpace) K₀)
    (hL₀qc : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor D.X₀.left.Modules n).obj L₀).IsQuasicoherent)
    (hL₀ : ∃ a b : ℤ, HasTorAmplitudeOver D.X₀.hom L₀ a b)
    (hdict : ∀ (W₀ : (D.descent.system.obj (op D.descent.base)).Opens)
      (U₀ : D.X₀.left.Opens) (hU₀ : IsAffineOpen U₀) (hUW : U₀ ≤ D.X₀.hom ⁻¹ᵁ W₀)
      (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace))),
      IsAffineOpen W₀ → RingedSpace.IsPseudoCoherent (X := D.X₀.left.toRingedSpace) K₀ →
        (∀ m : ℤ,
          ((DerivedCategory.homologyFunctor D.X₀.left.Modules m).obj L).IsQuasicoherent) →
        (∃ a b : ℤ, HasTorAmplitudeOver D.X₀.hom L a b) →
          D.AffineRingTranslation W₀ U₀ hU₀ hUW K₀ L)
    (mv : ∀ (U₀ V₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
      (hV₀ : IsCompact (V₀ : Set D.X₀.left))
      (hinf : IsCompact ((U₀ ⊓ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
      (hsupc : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left)),
      D.MayerVietorisHomSequence K₀ (fun n => L₀⟦n⟧) U₀ V₀ hU₀ hV₀ hinf hsupc) (n : ℤ) :
    D.HomDescent K₀ (L₀⟦n⟧) :=
  D.homDescent_family_of_mayerVietorisHomSequence K₀ (fun n => L₀⟦n⟧)
    (D.restrictHomDescent_shift_of_isAffineOpenOverAffine K₀ L₀ hK₀ hL₀qc hL₀ hdict) mv n

/-- The conclusion of Tag 0DI7 for `K₀` and `L₀`, from the affine ring translation `hdict` and the
Mayer--Vietoris sequences `mv`. -/
theorem homDescent_of_mayerVietorisHomSequence
    (hK₀ : RingedSpace.IsPseudoCoherent (X := D.X₀.left.toRingedSpace) K₀)
    (hL₀qc : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor D.X₀.left.Modules n).obj L₀).IsQuasicoherent)
    (hL₀ : ∃ a b : ℤ, HasTorAmplitudeOver D.X₀.hom L₀ a b)
    (hdict : ∀ (W₀ : (D.descent.system.obj (op D.descent.base)).Opens)
      (U₀ : D.X₀.left.Opens) (hU₀ : IsAffineOpen U₀) (hUW : U₀ ≤ D.X₀.hom ⁻¹ᵁ W₀)
      (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace))),
      IsAffineOpen W₀ → RingedSpace.IsPseudoCoherent (X := D.X₀.left.toRingedSpace) K₀ →
        (∀ m : ℤ,
          ((DerivedCategory.homologyFunctor D.X₀.left.Modules m).obj L).IsQuasicoherent) →
        (∃ a b : ℤ, HasTorAmplitudeOver D.X₀.hom L a b) →
          D.AffineRingTranslation W₀ U₀ hU₀ hUW K₀ L)
    (mv : ∀ (U₀ V₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
      (hV₀ : IsCompact (V₀ : Set D.X₀.left))
      (hinf : IsCompact ((U₀ ⊓ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
      (hsupc : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left)),
      D.MayerVietorisHomSequence K₀ (fun n => L₀⟦n⟧) U₀ V₀ hU₀ hV₀ hinf hsupc) :
    D.HomDescent K₀ L₀ :=
  D.homDescent_shiftZero K₀ L₀
    (D.homDescent_shift_of_mayerVietorisHomSequence K₀ L₀ hK₀ hL₀qc hL₀ hdict mv 0)

/-- **Stacks 0DI7.** In Situation 0DI6, let `K₀` and `L₀` be objects of `D(𝒪_{X₀})` with `K₀`
pseudo-coherent and `L₀` in `D_QCoh(𝒪_{X₀})` of locally finite Tor dimension as an object of
`D((X₀ ⟶ S₀)⁻¹𝒪_{S₀})`. Then
`colim_i Hom_{D(𝒪_{Xᵢ})}(Lf_{i0}^*K₀, Lf_{i0}^*L₀) ⟶ Hom_{D(𝒪_X)}(Lf₀^*K₀, Lf₀^*L₀)`
is bijective. -/
@[stacks 0DI7]
theorem homDescent_of_isPseudoCoherent_of_locallyHasFiniteTorDimension
    (hK₀ : RingedSpace.IsPseudoCoherent (X := D.X₀.left.toRingedSpace) K₀)
    (hL₀qc : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor D.X₀.left.Modules n).obj L₀).IsQuasicoherent)
    (hL₀tor : RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage (D.descent.system.obj (op D.descent.base)).toRingedSpace
        D.X₀.hom.base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((Scheme.Hom.derivedScalarRestriction D.X₀.hom).obj L₀)) :
    D.HomDescent K₀ L₀ :=
  D.homDescent_of_isPseudoCoherent K₀ L₀ hK₀ hL₀qc hL₀tor

end AlgebraicGeometry.RelativeDescentSituation

end
