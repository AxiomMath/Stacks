module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.SectionValue
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLines
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.CotangentSpace

/-!
# The stalk map of the morphism induced by a graded ring homomorphism

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings and let
`mapHom : U(ψ) ⟶ Proj 𝒜` be the morphism it induces on its domain of definition
`U(ψ) ⊆ Proj ℬ`. At a point `y ∈ U(ψ)` the stalk map of `mapHom`, read through Mathlib's
identification `AlgebraicGeometry.Proj.stalkIso` of a stalk of `Proj` with a degree-zero
homogeneous localization, is the algebraic map `HomogeneousLocalization.localRingHom ψ` between
the homogeneous localizations at the two homogeneous primes.

Specialized to the inclusion of a submodule `W ≤ V`, whose induced morphism is the linear
projection `r_W` from the complement of the linear subspace cut out by `W` to `𝐏(W)`, this says
that `r_W` carries the affine coordinate
`w / w₀` of `𝐏(W)` at the image point to the affine coordinate `w / w₀` of `𝐏(V)` at the point,
for degree-one forms `w, w₀` on `W` read as degree-one forms on `V`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistCompare.stalkIso_inv_comp_stalkMap`: the stalk map of
  `mapHom` is `HomogeneousLocalization.localRingHom ψ`, conjugated by `Proj.stalkIso` at the
  source and by `Proj.stalkIso` together with the stalk map of the open immersion at the target.
  This is the analogue of `AlgebraicGeometry.Proj.localRingHom_comp_stalkIso` for a morphism
  defined only on `U(ψ)`.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.atPrime_ringHom_ext`: two ring homomorphisms out of
  the homogeneous localization at a point agree as soon as they agree on the degree-zero
  localization away from one positive-degree homogeneous element omitted by that point.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.projectionLocalRingHom_chartGerm`: the comparison
  map of local rings attached to a linear projection sends the affine coordinate `w / w₀` at the
  image point to the affine coordinate `w / w₀` at the point.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.stalkMap_projection_chartGerm`: the same identity
  for the stalk map of the projection itself.

## Implementation notes

Mathlib's stalk computation for a morphism of projective spectra,
`AlgebraicGeometry.Proj.localRingHom_comp_stalkIso`, is stated for `Proj.sheafedSpaceMap` and so
assumes `ℬ₊ ≤ 𝒜₊.map ψ`, which makes the morphism defined on all of `Proj ℬ`. That hypothesis
fails for a linear projection away from a nonempty centre, so the identification has to be made
for `mapHom` on its own domain of definition, and it cannot be quoted.

It is nevertheless cheap, because the hard half is already available at the level of sections:
`Stacks.AlgebraicGeometry.ProjTwistChain.awayToSection_comp_appLE_mapHom` is Tag 01MY part (2) as
a commuting square of degree-zero homogeneous localizations, and it is stated with
`AlgebraicGeometry.Scheme.Hom.appLE` landing in the *same* open on both sides, so passing to
germs needs no transport along the equality of inverse images. Germifying that square with
`AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply` gives the stalk square on the image of
`𝒜_{(f)}`, which is `stalkMap_germ_awayToSection`.

What remains is that this image determines the map, and that is Mathlib's
`AlgebraicGeometry.ProjectiveSpectrum.Proj.isLocalization_atPrime`: the homogeneous localization
at a point of `D₊(f)` is a localization of `𝒜_{(f)}`, so `IsLocalization.ringHom_ext` applies.
No unwinding of the gluing that defines `mapHom` is needed, and neither
`AlgebraicGeometry.Proj.basicOpenToSpec` nor `AlgebraicGeometry.Proj.awayι` appears.

The transparency gotcha of the neighbouring files recurs: the carrier of `Proj 𝒜` is not
`ProjectiveSpectrum 𝒜` at instance transparency, so points are bound at the
`ProjectiveSpectrum` spelling, through
`Stacks.AlgebraicGeometry.ProjTwistCompare.basePoint` and `ambientPoint`, wherever a homogeneous
localization at them is formed. Conversely the rewrites by
`AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply` need the point written as a morphism applied
to an argument, so `stalkMap_germ_awayToSection` opens with a `change` that converts between the
two spellings.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain

namespace Stacks.AlgebraicGeometry.ProjTwistCompare

attribute [local instance_reducible] ProjectiveSpectrum.top

universe u v w w'

section AtPrime

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **A ring homomorphism out of the homogeneous localization at a point is determined on one
standard open.** If `f` is homogeneous of positive degree and is omitted by the homogeneous prime
of `x`, then `𝒜ₓ` is a localization of `𝒜_{(f)}`, so two ring homomorphisms out of `𝒜ₓ` agreeing
on the image of `𝒜_{(f)}` are equal. -/
public theorem atPrime_ringHom_ext {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d)
    (x : ProjectiveSpectrum 𝒜) (hx : f ∈ x.asHomogeneousIdeal.toIdeal.primeCompl)
    {T : Type v} [CommRing T]
    {j k : AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal →+* T}
    (h : ∀ w : HomogeneousLocalization.Away 𝒜 f,
      j (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hx) w) =
        k (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hx) w)) :
    j = k := by
  let _inst : Algebra (HomogeneousLocalization.Away 𝒜 f)
      (AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) :=
    (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hx)).toAlgebra
  have _hp : ((AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec 𝒜 f).base
      ⟨x, hx⟩).asIdeal.IsPrime :=
    ((AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec 𝒜 f).base ⟨x, hx⟩).isPrime
  have _hloc : @IsLocalization (HomogeneousLocalization.Away 𝒜 f) _
      ((AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec 𝒜 f).base ⟨x, hx⟩).asIdeal.primeCompl
      (AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) _ _inst :=
    AlgebraicGeometry.ProjectiveSpectrum.Proj.isLocalization_atPrime 𝒜 f ⟨x, hx⟩ hf hd
  exact IsLocalization.ringHom_ext
    ((AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec 𝒜 f).base ⟨x, hx⟩).asIdeal.primeCompl
    (RingHom.ext h)

/-- The germ at `x` of the section of the structure sheaf on `D₊(f)` attached to an element of
`𝒜_{(f)}` is, under the identification of the stalk with `𝒜ₓ`, the image of that element in
`𝒜ₓ`. -/
public theorem stalkIso_inv_mapId (x : ProjectiveSpectrum 𝒜) {f : A}
    (hx : f ∈ x.asHomogeneousIdeal.toIdeal.primeCompl)
    (w : HomogeneousLocalization.Away 𝒜 f) :
    (Proj.stalkIso 𝒜 x).inv.hom'
        (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hx) w) =
      (AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 f) x hx
        ((Proj.awayToSection 𝒜 f).hom' w) :=
  (congrFun (congrArg (fun m => m.hom')
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 f x hx)) w).symm

end AtPrime

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **The stalk map of `mapHom` on the sections coming from a standard open.** The germ at the
image point of the section attached to `v ∈ 𝒜_{(f)}` is carried to the germ at the point of the
section attached to `ψ v ∈ ℬ_{(ψ f)}`.

This is `Stacks.AlgebraicGeometry.ProjTwistChain.awayToSection_comp_appLE_mapHom`, Tag 01MY part
(2) as a square of degree-zero localizations, pushed to germs. -/
public theorem stalkMap_germ_awayToSection (ψ : 𝒜 →+*ᵍ ℬ) {d : ℕ} (hd : 0 < d) {f : A}
    (hf : f ∈ 𝒜 d) (y : (mapDomain 𝒜 ℬ ψ).toScheme)
    (hfy : (mapDomain 𝒜 ℬ ψ).ι y ∈ Proj.basicOpen ℬ (ψ f))
    (hfx : (mapHom 𝒜 ℬ ψ).base y ∈ Proj.basicOpen 𝒜 f)
    (w : HomogeneousLocalization.Away 𝒜 f) :
    (mapHom 𝒜 ℬ ψ).stalkMap y
        ((AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 f)
          (basePoint 𝒜 ℬ ψ y) hfx ((Proj.awayToSection 𝒜 f).hom' w)) =
      (mapDomain 𝒜 ℬ ψ).ι.stalkMap y
        ((AlgebraicGeometry.Proj ℬ).presheaf.germ (Proj.basicOpen ℬ (ψ f))
          (ambientPoint 𝒜 ℬ ψ y) hfy
          ((Proj.awayToSection ℬ (ψ f)).hom'
            (HomogeneousLocalization.Away.map ψ f w))) := by
  change (mapHom 𝒜 ℬ ψ).stalkMap y
      ((AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 f)
        ((mapHom 𝒜 ℬ ψ).base y) hfx ((Proj.awayToSection 𝒜 f).hom' w)) =
    (mapDomain 𝒜 ℬ ψ).ι.stalkMap y
      ((AlgebraicGeometry.Proj ℬ).presheaf.germ (Proj.basicOpen ℬ (ψ f))
        ((mapDomain 𝒜 ℬ ψ).ι y) hfy
        ((Proj.awayToSection ℬ (ψ f)).hom'
          (HomogeneousLocalization.Away.map ψ f w)))
  have hyO : y ∈ (mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f) := hfy
  have hsection := congrArg
    (fun m : CommRingCat.of (HomogeneousLocalization.Away 𝒜 f) ⟶
        Γ((mapDomain 𝒜 ℬ ψ).toScheme, (mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f)) =>
      (mapDomain 𝒜 ℬ ψ).toScheme.presheaf.germ _ y hyO (ConcreteCategory.hom m w))
    (awayToSection_comp_appLE_mapHom 𝒜 ℬ ψ f d hf hd)
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom, TopCat.Presheaf.germ_res_apply'] at hsection
  rwa [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]

/-- **The stalk map of `mapHom` is `HomogeneousLocalization.localRingHom ψ`.** For a point `y` of
the domain of definition, the stalk map of `mapHom` at `y`, conjugated by the identifications of
the two stalks of `Proj` with homogeneous localizations, is the fibre comparison
`Stacks.AlgebraicGeometry.ProjTwistCompare.fibreHom`.

This is the analogue of `AlgebraicGeometry.Proj.localRingHom_comp_stalkIso`, which assumes
`ℬ₊ ≤ 𝒜₊.map ψ` and so describes a morphism defined on all of `Proj ℬ`. -/
public theorem stalkIso_inv_comp_stalkMap (ψ : 𝒜 →+*ᵍ ℬ) (y : (mapDomain 𝒜 ℬ ψ).toScheme) :
    (Proj.stalkIso 𝒜 (basePoint 𝒜 ℬ ψ y)).inv ≫ (mapHom 𝒜 ℬ ψ).stalkMap y =
      CommRingCat.ofHom (fibreHom 𝒜 ℬ ψ y) ≫
        (Proj.stalkIso ℬ (ambientPoint 𝒜 ℬ ψ y)).inv ≫
          (mapDomain 𝒜 ℬ ψ).ι.stalkMap y := by
  obtain ⟨d, f, hd, hf, hfy0⟩ := (mem_mapDomain_iff 𝒜 ℬ ψ y.1).mp y.2
  have hfy : ψ f ∈ (ambientPoint 𝒜 ℬ ψ y).asHomogeneousIdeal.toIdeal.primeCompl := hfy0
  have hfx : f ∈ (basePoint 𝒜 ℬ ψ y).asHomogeneousIdeal.toIdeal.primeCompl :=
    (notMem_mapHom_base_iff 𝒜 ℬ ψ y hf).mpr hfy0
  refine CommRingCat.hom_ext
    (atPrime_ringHom_ext 𝒜 hd hf (basePoint 𝒜 ℬ ψ y) hfx fun w => ?_)
  change (mapHom 𝒜 ℬ ψ).stalkMap y ((Proj.stalkIso 𝒜 (basePoint 𝒜 ℬ ψ y)).inv.hom'
      (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hfx) w)) =
    (mapDomain 𝒜 ℬ ψ).ι.stalkMap y ((Proj.stalkIso ℬ (ambientPoint 𝒜 ℬ ψ y)).inv.hom'
      (fibreHom 𝒜 ℬ ψ y (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hfx) w)))
  rw [stalkIso_inv_mapId 𝒜 (basePoint 𝒜 ℬ ψ y) hfx w,
    stalkMap_germ_awayToSection 𝒜 ℬ ψ hd hf y hfy hfx,
    show fibreHom 𝒜 ℬ ψ y (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hfx) w) =
      HomogeneousLocalization.mapId ℬ (Submonoid.powers_le.mpr hfy)
        (HomogeneousLocalization.Away.map ψ f w) from
      localRingHom_mapId 𝒜 ℬ ψ
        (congrArg HomogeneousIdeal.toIdeal (basePoint_asHomogeneousIdeal 𝒜 ℬ ψ y))
        (Submonoid.powers_le.mpr hfx) (Submonoid.powers_le.mpr hfy) w,
    stalkIso_inv_mapId ℬ (ambientPoint 𝒜 ℬ ψ y) hfy
      (HomogeneousLocalization.Away.map ψ f w)]

/-- The elementwise form of `stalkIso_inv_comp_stalkMap`: the stalk map of `mapHom` carries the
germ attached to a homogeneous fraction at the image point to the germ attached to its image
under `ψ` at the point. -/
public theorem stalkMap_stalkIso_inv_apply (ψ : 𝒜 →+*ᵍ ℬ) (y : (mapDomain 𝒜 ℬ ψ).toScheme)
    (z : AtPrime 𝒜 (basePoint 𝒜 ℬ ψ y).asHomogeneousIdeal.toIdeal) :
    (mapHom 𝒜 ℬ ψ).stalkMap y ((Proj.stalkIso 𝒜 (basePoint 𝒜 ℬ ψ y)).inv.hom' z) =
      (mapDomain 𝒜 ℬ ψ).ι.stalkMap y
        ((Proj.stalkIso ℬ (ambientPoint 𝒜 ℬ ψ y)).inv.hom' (fibreHom 𝒜 ℬ ψ y z)) :=
  congrFun (congrArg (fun m => m.hom') (stalkIso_inv_comp_stalkMap 𝒜 ℬ ψ y)) z

end Stacks.AlgebraicGeometry.ProjTwistCompare

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

open Stacks.AlgebraicGeometry.ProjTwistCompare

universe u

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V] {W : Submodule k V}

/-- The graded homomorphism attached to the inclusion of a submodule carries the degree-one form
`w` on `W` to the degree-one form `w` on `V`. -/
public theorem gradedSymAlgMap_subtype_ι (w : ↥W) :
    SymPow.gradedSymAlgMap W.subtype (SymmetricAlgebra.ι k ↥W w) =
      SymmetricAlgebra.ι k V (w : V) := by
  simp [SymPow.gradedSymAlgMap_apply, SymPow.symAlgMap_ι]

/-- **The comparison of local rings along a linear projection.** For a point `x` of the domain of
the projection away from the linear subspace cut out by `W`, the local ring of `𝐏(W)` at the
image of `x` maps to the local ring of `𝐏(V)` at `x`, a homogeneous fraction of forms on `W`
going to the same fraction read on `V`. -/
public abbrev projectionLocalRingHom (x : (projectionDomain k V W).toScheme) :
    localRing ((projection k V W).base x) →+* localRing x.1 :=
  fibreHom (fun n => SymPow.symmetricPower n k ↥W) (fun n => SymPow.symmetricPower n k V)
    (SymPow.gradedSymAlgMap W.subtype) x

/-- **A linear projection preserves affine coordinates.** The comparison of local rings along the
projection away from the linear subspace cut out by `W` sends the affine coordinate `w / w₀` at
the image point to the affine coordinate `w / w₀` at the point, for degree-one forms `w, w₀` on
`W` read as degree-one forms on `V`. -/
public theorem projectionLocalRingHom_chartGerm (x : (projectionDomain k V W).toScheme)
    {w₀ : ↥W} (hw₀ : w₀ ∉ pointSubmodule k ↥W ((projection k V W).base x))
    (hv₀ : (w₀ : V) ∉ pointSubmodule k V x.1) (w : ↥W) :
    projectionLocalRingHom x (chartGerm ((projection k V W).base x) hw₀ w) =
      chartGerm x.1 hv₀ (w : V) := by
  apply HomogeneousLocalization.val_injective
  have h1 : (projectionLocalRingHom x (chartGerm ((projection k V W).base x) hw₀ w)).val =
      Localization.mk (SymPow.gradedSymAlgMap W.subtype (SymmetricAlgebra.ι k ↥W w))
        ⟨SymPow.gradedSymAlgMap W.subtype (SymmetricAlgebra.ι k ↥W w₀),
          by rw [gradedSymAlgMap_subtype_ι]; exact ι_mem_primeCompl hv₀⟩ := rfl
  rw [h1, val_chartGerm]
  simp only [gradedSymAlgMap_subtype_ι]

/-- Transporting a germ to the local ring and back is the identity: the inverse of
`AlgebraicGeometry.ProjectiveSpaceOfModule.stalkRingEquiv` is the inverse of Mathlib's
`AlgebraicGeometry.Proj.stalkIso`. -/
public theorem stalkRingEquiv_symm_apply (x : projectiveSpaceOfModule k V) (z : localRing x) :
    (stalkRingEquiv x).symm z =
      (Proj.stalkIso (fun n => SymPow.symmetricPower n k V) x).inv.hom' z :=
  rfl

/-- **The stalk map of a linear projection.** Read through the identification of the stalks with
the local rings, the stalk map of the projection away from the linear subspace cut out by `W` is
the comparison `projectionLocalRingHom`. -/
public theorem stalkMap_projection_apply (x : (projectionDomain k V W).toScheme)
    (z : localRing ((projection k V W).base x)) :
    (projection k V W).stalkMap x ((stalkRingEquiv ((projection k V W).base x)).symm z) =
      (projectionDomain k V W).ι.stalkMap x
        ((stalkRingEquiv x.1).symm (projectionLocalRingHom x z)) :=
  stalkMap_stalkIso_inv_apply (fun n => SymPow.symmetricPower n k ↥W)
    (fun n => SymPow.symmetricPower n k V) (SymPow.gradedSymAlgMap W.subtype) x z

/-- **A linear projection preserves affine coordinates, at the level of stalks.** The stalk map
of the projection away from the linear subspace cut out by `W` sends the germ of the affine
coordinate `w / w₀` at the image point to the germ of the affine coordinate `w / w₀` at the
point. -/
public theorem stalkMap_projection_chartGerm (x : (projectionDomain k V W).toScheme)
    {w₀ : ↥W} (hw₀ : w₀ ∉ pointSubmodule k ↥W ((projection k V W).base x))
    (hv₀ : (w₀ : V) ∉ pointSubmodule k V x.1) (w : ↥W) :
    (projection k V W).stalkMap x
        ((stalkRingEquiv ((projection k V W).base x)).symm
          (chartGerm ((projection k V W).base x) hw₀ w)) =
      (projectionDomain k V W).ι.stalkMap x
        ((stalkRingEquiv x.1).symm (chartGerm x.1 hv₀ (w : V))) := by
  rw [stalkMap_projection_apply, projectionLocalRingHom_chartGerm x hw₀ hv₀ w]

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
