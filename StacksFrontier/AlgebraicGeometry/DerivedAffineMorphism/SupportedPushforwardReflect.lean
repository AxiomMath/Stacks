module

public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardTExactness
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.SupportedDevissage
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TorAmplitudeStalkwise
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ClosedSupportPerfect

/-!
# Direct image detects vanishing of cohomology supported over an affine open

Let `p : P ⟶ Y` be a morphism of schemes, let `U ⊆ P` be an open subscheme and let `j : U ⟶ P`
be its inclusion. Suppose `j ≫ p` is an **affine** morphism; `p` itself need not be. If `E` is
an object of `D(𝒪_P)` with quasi-coherent cohomology whose cohomology sheaves are supported on a
closed subset `T ⊆ U`, then

`H^i(Rp_*E) = 0 ⟹ H^i(E) = 0`.

Supportedness makes the unit `E ⟶ Rj_*(j^*E)` invertible ([Stacks, Tag 08DF] part (1)); Leray
turns `Rp_*E` into `R(j ≫ p)_*(j^*E)`; direct image along the affine `j ≫ p` detects vanishing
of cohomology ([Stacks, Tag 08D5] and [Stacks, Tag 0G9N]), giving `H^i(j^*E) = 0`; and a sheaf
supported on `T ⊆ U` whose restriction to `U` vanishes has no nonzero stalk.

The geometric source of the affineness hypothesis is the first half of the file. If `P` is the
fibre product of `f : X ⟶ S` and `g : Y ⟶ S` and `U = fst⁻¹U₀` for an open `U₀ ⊆ X`, then `U` is
the fibre product of `U₀ ⟶ S` and `g`, so `j ≫ snd` is a base change of `U₀ ⟶ S` and is affine
whenever `U₀` and `S` are. For `X` and `Y` of finite type over a field `k` and `U₀` an affine
open of `X`, this makes the second projection `X ×_k Y ⟶ Y` affine over `U₀` although it is not
affine, and the complexes the reflection statement applies to are those whose cohomology lives
over a closed subset of `X` contained in an affine open — for instance over a finite set of
closed points, which is the support hypothesis of [Stacks, Tag 0FZ9].

## Main results

* `Stacks.AlgebraicGeometry.SupportedPushforwardReflect.isPullback_restrict_fst` — the Cartesian
  square identifying `fst⁻¹U₀` with `U₀ ×_S Y`, and
  `Stacks.AlgebraicGeometry.SupportedPushforwardReflect.restrictIsoPullback` the resulting
  isomorphism, compatible with both projections.
* `isAffineHom_ι_comp_snd` and `isAffineHom_ι_comp_pullback_snd` — the second projection is
  affine over an affine open of the first factor.
* `isZero_of_isZero_jStar_obj_of_supported` — a module supported on a closed subset of `U` is
  detected by its restriction to `U`.
* `derivedPushforwardRestrictCompIso` — `Rp_*E ≅ R(j ≫ p)_*(j^*E)` for `E` supported on a closed
  subset of `U`.
* `isZero_homology_of_isZero_homology_derivedPushforward_of_supported` — the reflection statement
  above, and `isZero_homology_of_isZero_homology_derivedPushforward_pullback_snd` its reading for
  the second projection of a fibre product.

All of these live in the namespace `Stacks.AlgebraicGeometry.SupportedPushforwardReflect`.

## Implementation notes

*The model of the derived categories is pinned, and the spelling is the ringed-space one.* The
affine input `isZero_homology_of_isZero_homology_derivedPushforward` of
`Stacks.AlgebraicGeometry.AffinePushforwardTExactness`
and the Leray isomorphism
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso` are available only
at `CategoryTheory.HasDerivedCategory.standard` and both speak of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward` of the underlying
morphism of ringed spaces, so the statements below are read there as well. The instance is
declared with priority `10000` for the reason recorded in
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/PushforwardTExactness.lean`: the import
closure also contains the locally small `SheafOfModules.hasDerivedCategory`.

*[Stacks, Tag 08DF] is applied across a definitional crossing.* It is stated for an open `U` of a
topological space through the functors `ExtensionByZeroModules.jStar`,
`ExtensionByZeroModules.jPush` and `ExtensionByZeroModules.resRing`. For `O = 𝒪_P` one has
`resRing U O = 𝒪_U` and `jPush U O = j_*` by `rfl`, so the chosen `Rf_*` of the ringed-space
development is a right derived functor of `jPush U O`; but the morphism property
`CategoryTheory.HomotopyCategory.quasiIso` is spelled at `resRing U O` by Tag 08DF and at `𝒪_U`
by that development, and instance search does not cross the two, so the derivation datum is
passed positionally. This is the device of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/SupportedPushforwardScheme.lean`.

*The vanishing criterion by stalks is restated.* It is private in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/SupportedDevissage.lean` and is reproved here rather
than exported.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
* [Stacks Project, Tag 0FZ9](https://stacks.math.columbia.edu/tag/0FZ9)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TopologicalSpace RingedSpaceModuleAdjunction ExtensionByZeroModules
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPushforwardUnit
  derivedPushforwardCompIso)
open Stacks.Cohomology.PushforwardRestriction (derivedPushforwardRestrictionUnit
  isIso_derivedPushforwardRestriction_unit_of_supported)

universe u

namespace Stacks.AlgebraicGeometry.SupportedPushforwardReflect

/-! ### A fibre product over an open of one factor -/

section Pullback

variable {P X Y S : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}

/-- **The part of a fibre product lying over an open of the first factor is again a fibre
product.** If `P` is the fibre product of `f : X ⟶ S` and `g : Y ⟶ S` and `U ⊆ X` is open, then
`fst⁻¹U` is the fibre product of `U ⟶ X ⟶ S` and `g`. -/
theorem isPullback_restrict_fst (h : IsPullback fst snd f g) (U : X.Opens) :
    IsPullback (fst ∣_ U) ((fst ⁻¹ᵁ U).ι ≫ snd) (U.ι ≫ f) g :=
  (isPullback_morphismRestrict fst U).paste_vert h

/-- **`fst⁻¹U ≅ U ×_S Y`.** The fibre product of `f : X ⟶ S` and `g : Y ⟶ S`, restricted to the
part lying over an open `U ⊆ X`, is the fibre product of `U ⟶ S` and `g`. -/
def restrictIsoPullback (h : IsPullback fst snd f g) (U : X.Opens) :
    (fst ⁻¹ᵁ U).toScheme ≅ pullback (U.ι ≫ f) g :=
  (isPullback_restrict_fst h U).isoPullback

/-- The identification `fst⁻¹U ≅ U ×_S Y` is an identification over `U`. -/
@[simp]
theorem restrictIsoPullback_hom_fst (h : IsPullback fst snd f g) (U : X.Opens) :
    (restrictIsoPullback h U).hom ≫ pullback.fst (U.ι ≫ f) g = fst ∣_ U :=
  (isPullback_restrict_fst h U).isoPullback_hom_fst

/-- The identification `fst⁻¹U ≅ U ×_S Y` is an identification over `Y`. -/
@[simp]
theorem restrictIsoPullback_hom_snd (h : IsPullback fst snd f g) (U : X.Opens) :
    (restrictIsoPullback h U).hom ≫ pullback.snd (U.ι ≫ f) g = (fst ⁻¹ᵁ U).ι ≫ snd :=
  (isPullback_restrict_fst h U).isoPullback_hom_snd

/-- **The second projection of a fibre product, restricted to the part over an open `U` of the
first factor, is affine as soon as `U ⟶ S` is**, being a base change of `U ⟶ S`. No hypothesis
is placed on `X`, and `snd` itself need not be affine. -/
theorem isAffineHom_ι_comp_snd (h : IsPullback fst snd f g) (U : X.Opens)
    [IsAffineHom (U.ι ≫ f)] : IsAffineHom ((fst ⁻¹ᵁ U).ι ≫ snd) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_restrict_fst h U)
    inferInstance

/-- **Over an affine base, the second projection of a fibre product is an affine morphism on the
part lying over an affine open of the first factor.** -/
theorem isAffineHom_ι_comp_snd_of_isAffineOpen (h : IsPullback fst snd f g) [IsAffine S]
    {U : X.Opens} (hU : IsAffineOpen U) : IsAffineHom ((fst ⁻¹ᵁ U).ι ≫ snd) :=
  have : IsAffine U.toScheme := hU
  isAffineHom_ι_comp_snd h U

/-- `Stacks.AlgebraicGeometry.SupportedPushforwardReflect.isPullback_restrict_fst` for the chosen
fibre product `X ×_S Y`. -/
theorem isPullback_restrict_pullback_fst (f : X ⟶ S) (g : Y ⟶ S) (U : X.Opens) :
    IsPullback (pullback.fst f g ∣_ U) ((pullback.fst f g ⁻¹ᵁ U).ι ≫ pullback.snd f g)
      (U.ι ≫ f) g :=
  isPullback_restrict_fst (IsPullback.of_hasPullback f g) U

/-- **The second projection `X ×_S Y ⟶ Y` is affine over an affine open of `X`** when `S` is
affine: on the preimage of an affine open `U ⊆ X` it is the base change of `U ⟶ S`. -/
theorem isAffineHom_ι_comp_pullback_snd (f : X ⟶ S) (g : Y ⟶ S) [IsAffine S] {U : X.Opens}
    (hU : IsAffineOpen U) :
    IsAffineHom ((pullback.fst f g ⁻¹ᵁ U).ι ≫ pullback.snd f g) :=
  isAffineHom_ι_comp_snd_of_isAffineOpen (IsPullback.of_hasPullback f g) hU

end Pullback

/-! ### Vanishing of a module supported on a closed subset of an open -/

section Stalks

variable {Z : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u})

/-- All stalks of a zero sheaf of modules vanish. -/
theorem isZero_stalk_of_isZero {M : SheafOfModules.{u} O} (hM : IsZero M) (x : Z) :
    IsZero (TopCat.Presheaf.stalk (X := Z) M.val.presheaf x) :=
  (AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff O x M).1
    ((AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj O M).1 hM x)

/-- **A sheaf of modules supported on a closed subset of an open subspace is detected by its
restriction to that open.** If every stalk of `M` outside `T ⊆ U` vanishes and `j^*M = 0`, then
`M = 0`. -/
theorem isZero_of_isZero_jStar_obj_of_supported (U : Opens Z) {T : Set Z} (hTU : T ⊆ U)
    (M : SheafOfModules.{u} O)
    (hsupp : ∀ x : Z, x ∉ T → IsZero (TopCat.Presheaf.stalk (X := Z) M.val.presheaf x))
    (h : IsZero ((jStar U O).obj M)) : IsZero M := by
  refine Stacks.Cohomology.PushforwardRestriction.isZero_sheafOfModules_of_stalk_isZero O M
    fun x => ?_
  by_cases hx : x ∈ T
  · exact (isZero_stalk_of_isZero (resRing U O) h ⟨x, hTU hx⟩).of_iso
      (TopCat.Presheaf.stalkRestrictIso U M.val.presheaf ⟨x, hTU hx⟩).symm
  · exact hsupp x hx

end Stalks

/-! ### Reflection of vanishing along a morphism that is affine over an open -/

section Reflect

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedQCoh.jPush_additive

variable {P Y : Scheme.{u}} (p : P ⟶ Y) (U : P.Opens)

/-- Restriction to an open subscheme commutes with the cohomology sheaves of an object of the
derived category, restriction being exact. -/
def homologyJStarIso (i : ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing P.toRingedSpace))) :
    (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing U.toScheme.toRingedSpace)) i).obj
        ((jStar U (structureSheafRing P.toRingedSpace)).mapDerivedCategory.obj E) ≅
      (jStar U (structureSheafRing P.toRingedSpace)).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing P.toRingedSpace)) i).obj E) :=
  ((jStar U (structureSheafRing P.toRingedSpace)).mapDerivedCategoryCompHomologyFunctorIso i).app E

/-- Restriction to an open subscheme preserves quasi-coherence of the cohomology sheaves. -/
theorem isQuasicoherent_homology_jStar (i : ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing P.toRingedSpace)))
    (hcoh : ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing P.toRingedSpace)) i).obj E).IsQuasicoherent) :
    ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing U.toScheme.toRingedSpace)) i).obj
      ((jStar U (structureSheafRing P.toRingedSpace)).mapDerivedCategory.obj
        E)).IsQuasicoherent := by
  have hres := @Scheme.Modules.isQuasicoherent_restrictFunctor U.toScheme P U.ι inferInstance
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing P.toRingedSpace)) i).obj E) hcoh
  have hq : (jStar U (structureSheafRing P.toRingedSpace)) = Scheme.Modules.restrictFunctor U.ι :=
    Stacks.Duality.OpenImmersion.jStar_eq_restrictFunctor P U
  refine (SheafOfModules.isQuasicoherent (structureSheafRing U.toScheme.toRingedSpace)).prop_of_iso
    (homologyJStarIso U i E).symm ?_
  rw [hq]
  exact hres

variable {T : Set P} (hT : IsClosed T) (hTU : T ⊆ U)
  (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing P.toRingedSpace)))
  (hE : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn
    (structureSheafRing P.toRingedSpace) T E)

include hT hTU hE in
/-- **[Stacks, Tag 08DF] part (1) for an open subscheme, at the chosen ringed-space derived
direct image**: the unit `E ⟶ Rj_*(j^*E)` is invertible when the cohomology sheaves of `E` are
supported on a closed subset of `U`. -/
theorem isIso_derivedPushforwardRestrictionUnit_app :
    IsIso ((derivedPushforwardRestrictionUnit (structureSheafRing P.toRingedSpace) U
      (derivedPushforward U.ι.toLRSHom.toShHom)
      (derivedPushforwardUnit U.ι.toLRSHom.toShHom)).app E) := by
  have hRj : (derivedPushforward U.ι.toLRSHom.toShHom).IsRightDerivedFunctor
      (derivedPushforwardUnit U.ι.toLRSHom.toShHom)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (structureSheafRing U.toScheme.toRingedSpace)) (ComplexShape.up ℤ)) :=
    inferInstance
  exact @isIso_derivedPushforwardRestriction_unit_of_supported _
    (structureSheafRing P.toRingedSpace) U T hT hTU _ _ (derivedPushforward U.ι.toLRSHom.toShHom)
    (derivedPushforwardUnit U.ι.toLRSHom.toShHom) hRj E hE

include hT hTU hE in
/-- **An object with cohomology supported on a closed subset of `U` is the derived direct image
of its restriction**: `E ≅ Rj_*(j^*E)`. -/
def derivedRestrictionIso :
    E ≅ (derivedPushforward U.ι.toLRSHom.toShHom).obj
      ((jStar U (structureSheafRing P.toRingedSpace)).mapDerivedCategory.obj E) :=
  @asIso _ _ _ _ _ (isIso_derivedPushforwardRestrictionUnit_app U hT hTU E hE)

include hT hTU hE in
/-- **Leray for an object supported on a closed subset of `U`**:
`Rp_*E ≅ R(j ≫ p)_*(j^*E)`. -/
def derivedPushforwardRestrictCompIso :
    (derivedPushforward p.toLRSHom.toShHom).obj E ≅
      (derivedPushforward (U.ι ≫ p).toLRSHom.toShHom).obj
        ((jStar U (structureSheafRing P.toRingedSpace)).mapDerivedCategory.obj E) :=
  (derivedPushforward p.toLRSHom.toShHom).mapIso (derivedRestrictionIso U hT hTU E hE) ≪≫
    (derivedPushforwardCompIso U.ι.toLRSHom.toShHom p.toLRSHom.toShHom).app
      ((jStar U (structureSheafRing P.toRingedSpace)).mapDerivedCategory.obj E)

include hT hTU hE in
/-- **Direct image detects vanishing of cohomology supported over an open over which it is
affine.** Let `p : P ⟶ Y` and let `U ⊆ P` be an open with `j ≫ p` affine; `p` itself need not be
affine. If the cohomology sheaves of `E` are quasi-coherent and supported on a closed subset `T`
of `U`, then a degree in which `H^i(Rp_*E)` vanishes is a degree in which `H^i(E)` vanishes.

The chain is `Rp_*E ≅ R(j ≫ p)_*(j^*E)` by [Stacks, Tag 08DF] and Leray, then vanishing of
`H^i(j^*E)` because `j ≫ p` is affine, then vanishing of `H^i(E)` because its restriction to `U`
vanishes and its stalks off `T` do. -/
theorem isZero_homology_of_isZero_homology_derivedPushforward_of_supported
    [IsAffineHom (U.ι ≫ p)]
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing P.toRingedSpace)) i).obj E).IsQuasicoherent) {i : ℤ}
    (h : IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).obj
      ((derivedPushforward p.toLRSHom.toShHom).obj E))) :
    IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing P.toRingedSpace)) i).obj E) := by
  have hcomp : IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).obj
      ((derivedPushforward (U.ι ≫ p).toLRSHom.toShHom).obj
        ((jStar U (structureSheafRing P.toRingedSpace)).mapDerivedCategory.obj E))) :=
    h.of_iso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).mapIso
      (derivedPushforwardRestrictCompIso p U hT hTU E hE).symm)
  have hres : IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing U.toScheme.toRingedSpace)) i).obj
      ((jStar U (structureSheafRing P.toRingedSpace)).mapDerivedCategory.obj E)) :=
    AffinePushforwardTExactness.isZero_homology_of_isZero_homology_derivedPushforward
      (U.ι ≫ p) _ (fun j => isQuasicoherent_homology_jStar U j E (hcoh j)) hcomp
  exact isZero_of_isZero_jStar_obj_of_supported (structureSheafRing P.toRingedSpace) U hTU _
    (fun x hx => hE i x hx) (hres.of_iso (homologyJStarIso U i E).symm)

end Reflect

/-! ### The second projection of a fibre product -/

section PullbackSnd

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **The second projection of a fibre product detects vanishing of cohomology supported over a
closed subset of an affine open of the first factor.** For `S` affine, `U` an affine open of `X`
and `Z ⊆ U` closed in `X`, an object `E` of `D(𝒪_{X ×_S Y})` with quasi-coherent cohomology
supported over `Z` satisfies `H^i(Rsnd_*E) = 0 ⟹ H^i(E) = 0`.

The projection is not affine; what makes the statement true is that it is affine over `U`. For
`X` and `Y` of finite type over a field and `Z` a finite set of closed points lying in an affine
open, this is the vanishing criterion [Stacks, Tag 0FZ9] rests on. -/
theorem isZero_homology_of_isZero_homology_derivedPushforward_pullback_snd [IsAffine S]
    {U : X.Opens} (hU : IsAffineOpen U) {Z : Set X} (hZ : IsClosed Z) (hZU : Z ⊆ U)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing (pullback f g).toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing (pullback f g).toRingedSpace)) i).obj
        E).IsQuasicoherent)
    (hE : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn
      (structureSheafRing (pullback f g).toRingedSpace) ((pullback.fst f g).base ⁻¹' Z) E) {i : ℤ}
    (h : IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).obj
      ((derivedPushforward (pullback.snd f g).toLRSHom.toShHom).obj E))) :
    IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing (pullback f g).toRingedSpace)) i).obj E) :=
  have : IsAffineHom ((pullback.fst f g ⁻¹ᵁ U).ι ≫ pullback.snd f g) :=
    isAffineHom_ι_comp_pullback_snd f g hU
  isZero_homology_of_isZero_homology_derivedPushforward_of_supported (pullback.snd f g)
    (pullback.fst f g ⁻¹ᵁ U) (hZ.preimage (pullback.fst f g).base.hom.continuous)
    (Set.preimage_mono hZU) E hE hcoh h

end PullbackSnd

end Stacks.AlgebraicGeometry.SupportedPushforwardReflect

end
