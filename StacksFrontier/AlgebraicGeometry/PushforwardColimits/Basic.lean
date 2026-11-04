module

public import StacksFrontier.AlgebraicGeometry.PushforwardColimits.Affine

/-!
# Direct image along an affine morphism commutes with colimits of quasi-coherent modules

Let `f : X ⟶ S` be an affine morphism of schemes.  This file proves that the direct image of
`𝒪_X`-modules preserves the colimit of a diagram of quasi-coherent modules.  Nothing of the sort
holds for a general morphism, nor for a general diagram: the direct image is a right adjoint, so
the content is entirely in the affineness of `f` and the quasi-coherence of the diagram.

The statement is local on `S`, by
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`, and over an affine open `V`
of `S` the direct image commutes with restriction, by
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`; so the affine case
`Stacks.AlgebraicGeometry.PushforwardColimits.preservesColimit_pushforward_of_isAffine` applies
to `f ∣_ V`, whose source `f ⁻¹ᵁ V` is affine precisely because `f` is.

## Main results

* `Stacks.AlgebraicGeometry.PushforwardColimits.preservesColimit_pushforward_comp_restrictFunctor`:
  over an affine open of `S`, the direct image followed by restriction preserves the colimit.
* `Stacks.AlgebraicGeometry.PushforwardColimits.preservesColimit_pushforward_of_isAffineHom`:
  **the direct image along an affine morphism preserves colimits of quasi-coherent modules.**
* `Stacks.AlgebraicGeometry.PushforwardColimits.isIso_coproductComparison_pushforward`: the
  coproduct form of the previous statement, as the invertibility of the canonical morphism
  `∐ (f_* M i) ⟶ f_* (∐ M i)`.

## Implementation notes

The invertibility of the comparison morphism is deduced from, rather than used to prove, the two
local statements: `Stacks.AlgebraicGeometry.PushforwardColimits.isIso_map_colimit_post` turns
"restriction preserves the colimit" and "direct image followed by restriction preserves the
colimit" into "restriction carries the comparison morphism to an isomorphism", which is the
hypothesis of the locality statement.  Restriction to an open preserves all colimits because it
is a left adjoint.

The hypotheses `HasColimitsOfShape K W.Modules` for every scheme `W` and
`HasColimitsOfShape K (ModuleCat R)` for every ring `R` are what the comparison morphisms need in
order to exist at all.  For the shapes of interest they are automatic: a discrete shape on a type
in `Type u`, or a finite shape.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe v₂ u₂ u

noncomputable section

namespace Stacks.AlgebraicGeometry.PushforwardColimits

variable {K : Type u₂} [Category.{v₂} K] [HasColimitsOfShape K AddCommGrpCat.{u}]
  [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
  [∀ W : Scheme.{u}, HasColimitsOfShape K W.Modules]

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### The statement over an affine open of the target -/

/-- Over an affine open `V` of `S`, the direct image along an affine morphism followed by
restriction to `V` preserves the colimit of a diagram of quasi-coherent modules: it is
isomorphic to restriction to `f ⁻¹ᵁ V` followed by the direct image along `f ∣_ V`, a morphism
between affine schemes. -/
theorem preservesColimit_pushforward_comp_restrictFunctor [IsAffineHom f] (V : S.affineOpens)
    {D : K ⥤ X.Modules} (hD : ∀ k, (D.obj k).IsQuasicoherent) :
    PreservesColimit D
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor (V : S.Opens).ι) := by
  have _hV : IsAffine (V : S.Opens).toScheme := V.2
  have _hU : IsAffine (f ⁻¹ᵁ (V : S.Opens)).toScheme := V.2.preimage f
  have hD' : ∀ k,
      ((D ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (V : S.Opens)).ι).obj k).IsQuasicoherent :=
    fun k ↦
      have := hD k
      Scheme.Modules.isQuasicoherent_restrictFunctor (f ⁻¹ᵁ (V : S.Opens)).ι (D.obj k)
  have _h1 : PreservesColimit (D ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (V : S.Opens)).ι)
      (Scheme.Modules.pushforward (f ∣_ (V : S.Opens))) :=
    preservesColimit_pushforward_of_isAffine (f ∣_ (V : S.Opens)) hD'
  have _h2 : PreservesColimit D
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (V : S.Opens)).ι ⋙
        Scheme.Modules.pushforward (f ∣_ (V : S.Opens))) :=
    inferInstance
  exact preservesColimit_of_natIso D
    (AffinePushforward.restrictPushforwardIso f (V : S.Opens)).symm

/-! ### The statement on `S` -/

/-- **The direct image along an affine morphism of schemes preserves colimits of quasi-coherent
modules.**  Invertibility of the colimit comparison morphism is local on `S`, and over an affine
open of `S` it follows from the affine case. -/
theorem preservesColimit_pushforward_of_isAffineHom [IsAffineHom f] {D : K ⥤ X.Modules}
    (hD : ∀ k, (D.obj k).IsQuasicoherent) :
    PreservesColimit D (Scheme.Modules.pushforward f) := by
  have hres : ∀ V : S.affineOpens,
      IsIso ((Scheme.Modules.restrictFunctor (V : S.Opens).ι).map
        (colimit.post D (Scheme.Modules.pushforward f))) := fun V ↦
    have := preservesColimit_pushforward_comp_restrictFunctor f V hD
    isIso_map_colimit_post D (Scheme.Modules.pushforward f)
      (Scheme.Modules.restrictFunctor (V : S.Opens).ι)
  have _hiso : IsIso (colimit.post D (Scheme.Modules.pushforward f)) :=
    AffineBaseChange.isIso_of_isIso_restrict _ (fun V : S.affineOpens ↦ (V : S.Opens))
      (IsOpenCover.mk (iSup_affineOpens_eq_top S)) hres
  exact preservesColimit_of_isIso_post (Scheme.Modules.pushforward f) D

/-- **The direct image along an affine morphism commutes with coproducts of quasi-coherent
modules**: the canonical morphism `∐ (f_* M i) ⟶ f_* (∐ M i)` is invertible. -/
theorem isIso_coproductComparison_pushforward [IsAffineHom f] {I : Type u} (M : I → X.Modules)
    (hM : ∀ i, (M i).IsQuasicoherent) :
    IsIso (colimit.post (Discrete.functor M) (Scheme.Modules.pushforward f)) :=
  have := preservesColimit_pushforward_of_isAffineHom f
    (D := Discrete.functor M) fun i ↦ hM i.as
  inferInstance

end Stacks.AlgebraicGeometry.PushforwardColimits

end

end
