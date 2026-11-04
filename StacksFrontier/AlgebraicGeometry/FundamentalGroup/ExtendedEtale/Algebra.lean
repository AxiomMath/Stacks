module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.AffineExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.Locality
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.LocalAtTarget
public import StacksFrontier.RingTheory.Sequence.RegularLocus
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.Depth.RingEquiv

/-!
# The extension algebra of a finite étale cover is coherent and reflexive

Let `X` be a locally Noetherian scheme, `j : U ⟶ X` an open immersion whose complement consists
of points at which `𝒪_X` has depth at least two, and `π : V ⟶ U` a finite étale morphism. This
file proves that the `𝒪_X`-module underlying the extension algebra `𝓑 = (π ≫ j)_* 𝒪_V` is
coherent and reflexive.

## Main results

* `extendedEtaleAlgebra_isCoherent` — the `𝒪_X`-module underlying `𝓑` is coherent.
* `extendedEtaleAlgebra_isReflexive` — it is reflexive.
* `extendedEtaleSituation` — the algebra, with its quasi-coherence, as the relative-spectrum
  situation out of which the extension scheme is formed.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
* [Stacks Project, Tag 0G41](https://stacks.math.columbia.edu/tag/0G41)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.AlgebraicGeometry.ReflexiveEquivalence
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

universe u

namespace Stacks.FundamentalGroup.ExtendedEtaleFold

/-! ### Transfer of the depth hypothesis along an isomorphism of local rings -/

/-- Depth at least two for a local ring transfers along a ring isomorphism. -/
private theorem two_le_depth_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B)
    (h : (2 : ℕ∞) ≤ Module.depth A (IsLocalRing.maximalIdeal A) A) :
    (2 : ℕ∞) ≤ Module.depth B (IsLocalRing.maximalIdeal B) B := by
  refine h.trans ?_
  have hle := Module.depth_le_of_ringEquiv e
    (IsLocalRing.maximalIdeal A)
  rwa [IsLocalRing.map_maximalIdeal_of_surjective (e : A →+* B) e.surjective] at hle

/-! ### The two assertions over an affine open -/

open Stacks.FundamentalGroup.ExtendedEtale in
/-- Over an affine open `W` of `X`, the restriction to `W` of the `𝒪_X`-module underlying the
extension algebra `(π ≫ j)_* 𝒪_V` is coherent and reflexive. -/
private theorem isCoherent_and_isReflexive_restrict_isAffineOpen {U X V : Scheme.{u}}
    [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (π : V ⟶ U) [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (W : X.Opens) (hW : IsAffineOpen W) :
    _root_.SheafOfModules.IsCoherent
        ((AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))).restrict W.ι) ∧
      IsReflexive
        ((AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))).restrict W.ι) := by
  have : IsAffine W.toScheme := hW
  have : IsLocallyNoetherian W.toScheme := isLocallyNoetherian_of_isOpenImmersion W.ι
  let T : U.Opens := j ⁻¹ᵁ W
  let a : (π ⁻¹ᵁ T).toScheme ⟶ T.toScheme := π ∣_ T
  let b : T.toScheme ⟶ W.toScheme := j ∣_ W
  have hcomp : (π ≫ j) ∣_ W = a ≫ b := morphismRestrict_comp π j W
  let q : (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))).restrict W.ι ≅
      AlgebraSheaf.underlyingModule (pushforwardAlgebra (a ≫ b)) :=
    Stacks.Morphisms.restrictPushforwardStructureSheafIso (π ≫ j) W ≪≫
      (Scheme.Modules.pushforwardCongr hcomp).app _
  have : IsLocallyNoetherian T.toScheme := isLocallyNoetherian_of_isOpenImmersion b
  have : IsLocallyNoetherian b.opensRange.toScheme :=
    isLocallyNoetherian_of_isOpenImmersion b.opensRange.ι
  have hM : _root_.SheafOfModules.IsCoherent
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra a)) :=
    isCoherent_underlyingModule_pushforwardAlgebra_of_isOpenImmersion b a
  have hMq : (AlgebraSheaf.underlyingModule (pushforwardAlgebra a)).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  have hA : _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward b.isoOpensRange.hom).obj
        (AlgebraSheaf.underlyingModule (pushforwardAlgebra a))) :=
    Stacks.AlgebraicGeometry.PushforwardCoherent.pushforward_isCoherent_of_isFinite
      b.isoOpensRange.hom (AlgebraSheaf.underlyingModule (pushforwardAlgebra a))
  have hG : _root_.SheafOfModules.IsCoherent
      ((AlgebraSheaf.underlyingModule (pushforwardAlgebra (a ≫ b))).restrict
        b.opensRange.ι) :=
    _root_.Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
      (isoRestrictOpensRangePushforward b
        (AlgebraSheaf.underlyingModule (pushforwardAlgebra a)))
  obtain ⟨E, hEc, ⟨eE⟩⟩ := exists_isCoherent_restrict_iso b.opensRange
    ((AlgebraSheaf.underlyingModule (pushforwardAlgebra (a ≫ b))).restrict b.opensRange.ι)
  have : _root_.SheafOfModules.IsCoherent E := hEc
  have hd : ∀ x : W.toScheme, x ∉ (b.opensRange : Set W.toScheme) →
      (2 : ℕ∞) ≤ Module.depth (W.toScheme.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (W.toScheme.presheaf.stalk x))
        (W.toScheme.presheaf.stalk x) := by
    intro x hx
    refine two_le_depth_of_ringEquiv (W.stalkIso x).commRingCatIsoToRingEquiv.symm
      (hdepth x.1 ?_)
    intro hxU
    apply hx
    obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp hxU
    have hyW : y ∈ T := by
      show j y ∈ W
      rw [hy]
      exact x.property
    refine ⟨⟨y, hyW⟩, ?_⟩
    exact Subtype.ext ((morphismRestrict_base_coe j W ⟨y, hyW⟩).trans hy)
  obtain ⟨hc, hr⟩ :=
    isCoherent_and_isReflexive_underlyingModule_pushforwardAlgebra_of_extension' b a E eE hd
  have : _root_.SheafOfModules.IsCoherent
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (a ≫ b))) := hc
  have hcr : _root_.SheafOfModules.IsCoherent
      ((AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))).restrict W.ι) :=
    _root_.Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso q
  exact ⟨hcr, isReflexive_of_iso q.symm hr⟩

/-! ### The two assertions of Tag 0EY6 about the extension algebra -/

/-- **The extension algebra of a finite étale cover is a coherent module over the base.** Let
`j : U ⟶ X` be an open immersion into a locally Noetherian scheme whose complement carries depth at
least two and let `π : V ⟶ U` be finite étale. Then the `𝒪_X`-module underlying
`𝓑 = (π ≫ j)_* 𝒪_V` is coherent. -/
@[stacks 0EY6 "algebra"]
public theorem extendedEtaleAlgebra_isCoherent {U X V : Scheme.{u}} [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] (π : V ⟶ U) [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    _root_.SheafOfModules.IsCoherent
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) :=
  isCoherent_of_isAffineOpen_restrict _ fun W hW =>
    (isCoherent_and_isReflexive_restrict_isAffineOpen j π hdepth W hW).1

/-- **The extension algebra of a finite étale cover is reflexive as a module over the base.** Let
`j : U ⟶ X` be an open immersion into a locally Noetherian scheme whose complement carries depth at
least two and let `π : V ⟶ U` be finite étale. Then the `𝒪_X`-module underlying
`𝓑 = (π ≫ j)_* 𝒪_V` is reflexive. -/
@[stacks 0EY6 "algebra"]
public theorem extendedEtaleAlgebra_isReflexive {U X V : Scheme.{u}} [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] (π : V ⟶ U) [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    IsReflexive (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) :=
  have : _root_.SheafOfModules.IsCoherent
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) :=
    extendedEtaleAlgebra_isCoherent j π hdepth
  isReflexive_of_isAffineOpen_restrict _ fun W hW =>
    (isCoherent_and_isReflexive_restrict_isAffineOpen j π hdepth W hW).2

/-- **The extension algebra, with its quasi-coherence, as a relative-spectrum situation.** It is
the pair consisting of `X` and the quasi-coherent `𝒪_X`-algebra `𝓑 = (π ≫ j)_* 𝒪_V`, whose relative
spectrum `Spec_X(𝓑)` is the extension scheme of the cover. -/
@[stacks 0EY6 "algebra"]
public def extendedEtaleSituation {U X V : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X)
    [IsOpenImmersion j] (π : V ⟶ U) [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    Stacks.RelativeSpec.RelativeSpecSituation.{u} :=
  letI : _root_.SheafOfModules.IsCoherent
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) :=
    extendedEtaleAlgebra_isCoherent j π hdepth
  letI : (pushforwardAlgebra (π ≫ j)).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  ⟨X, pushforwardAlgebra (π ≫ j)⟩

end Stacks.FundamentalGroup.ExtendedEtaleFold

end
