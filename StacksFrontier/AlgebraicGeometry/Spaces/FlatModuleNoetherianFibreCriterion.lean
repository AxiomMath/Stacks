module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleComposition

/-!
# Critère de platitude par fibres over a locally Noetherian base, for algebraic spaces

Let `X ⟶ Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S`, let `F` be an `𝒪_X`-module
and let `x̄` be a geometric point of `X` with images `ȳ` in `Y` and `z̄` in `Z`.  When the three
spaces are locally Noetherian and the geometric stalk `F_{x̄}` is a nonzero finite module, the
two conditions of Stacks 0APR are equivalent: flatness of `F` over `Z` at `x̄` together with
flatness of `F` on the fibre over `z̄` relative to the fibre of `Y`, and flatness of `Y` over
`Z` at `ȳ` together with flatness of `F` over `Y` at `x̄`.

## Main definitions

* `AlgebraicGeometry.Space.IsFlatOnFibreAtGeometricPoint`: the fibre condition, read on
  geometric stalks as in Stacks 05WY part (1): the quotient `F_{x̄}/𝔪_{z̄}F_{x̄}` is flat over
  `𝒪_{Y, ȳ}/𝔪_{z̄}𝒪_{Y, ȳ}`.

## Main results

* `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_and_isFlatOnFibre_iff`: **Stacks 0APR**,
  the equivalence of the two conditions.

## Implementation notes

Through Stacks 05VU and Stacks 04NG both conditions are conditions on the homomorphisms of
étale local rings `𝒪_{Z, z̄} → 𝒪_{Y, ȳ} → 𝒪_{X, x̄}` of Stacks 04NG and the module `F_{x̄}` of
Stacks 05VQ over the last of them, exactly as for Stacks 05VX in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleComposition.lean`; the identity
`AlgebraicGeometry.Space.etaleLocalRingMap_comp` is what makes the scalar tower
`𝒪_{Z, z̄} → 𝒪_{Y, ȳ} → F_{x̄}` hold and lets flatness over `Z` be read over `𝒪_{Z, z̄}`.  With
the three rings Noetherian local, the two homomorphisms local and `F_{x̄}` finite and nonzero,
the equivalence is the local statement `Module.flat_and_flat_of_flat_quotient_maximalIdeal_of_flat`
(Stacks 00MP) in one direction, and transitivity of flatness together with base change along
`𝒪_{Y, ȳ} → 𝒪_{Y, ȳ}/𝔪_{z̄}𝒪_{Y, ȳ}` in the other; the first conjunct of the latter is
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_comp`, Stacks 05VX part (1).

Noetherianity of the three étale local rings comes from
`AlgebraicGeometry.Space.isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian`, so local
Noetherianity of the spaces is carried as the étale-local scheme property of Stacks 03E6, which
is how the source's hypothesis reads for algebraic spaces.

Coherence of `F` enters the source's proof only through finiteness of the stalk, and that is
what is assumed here: `Module.Finite 𝒪_{X, x̄} F_{x̄}`.  The comparison of site-local finiteness
of `F` with finiteness of its geometric stalk is not available (it is the chartwise comparison
recorded as missing under Tag 060Q in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestriction.lean`), so the hypothesis is taken
on the stalk, which also makes the statement apply to modules that are not quasi-coherent.

The fibre condition is the geometric-stalk condition of Stacks 05WY part (1) rather than
flatness of a pullback of `F` to a genuine fibre product; the identification of the two is
conditions (1) and (2) of Stacks 05WY, which is, in the namespace `AlgebraicGeometry`,
`Space.isFlatOverAtGeometricPoint_fieldFibreSpace_iff_isFibreFlatOverAtGeometricPoint`
of `StacksFrontier/AlgebraicGeometry/Spaces/FibreFlatnessFieldFibre.lean`.  The condition is
written with `𝔪_{z̄}F_{x̄}` computed over `𝒪_{Y, ȳ}`, the spelling that Stacks 00MP consumes.

## References

* [Stacks Project, Tag 0APR](https://stacks.math.columbia.edu/tag/0APR)
* [Stacks Project, Tag 039B](https://stacks.math.columbia.edu/tag/039B)
* [Stacks Project, Tag 00MP](https://stacks.math.columbia.edu/tag/00MP)
* [Stacks Project, Tag 05WY](https://stacks.math.columbia.edu/tag/05WY)
* [Stacks Project, Tag 05VX](https://stacks.math.columbia.edu/tag/05VX)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The fibre condition of Stacks 0APR, read on geometric stalks as in Stacks 05WY part (1):
for `X ⟶ Y ⟶ Z` and a geometric point `x̄` of `X` with images `ȳ` and `z̄`, the quotient
`F_{x̄}/𝔪_{z̄}F_{x̄}` is flat over `𝒪_{Y, ȳ}/𝔪_{z̄}𝒪_{Y, ȳ}`.

The ideal `𝔪_{z̄}𝒪_{Y, ȳ}` is the image of the maximal ideal of `𝒪_{Z, z̄}` under the canonical
homomorphism of étale local rings of Stacks 04NG, and `𝔪_{z̄}F_{x̄}` is its action on the
geometric stalk of Stacks 05VQ, read over `𝒪_{Y, ȳ}`. -/
def IsFlatOnFibreAtGeometricPoint {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, m} B S hS X.1 X.2) (xbar : GeometricPoint B S hS X.1) : Prop :=
  letI : IsLocalRing (etaleLocalRing B S hS Z.1
      (geometricPointMap g.hom (geometricPointMap f.hom xbar))) :=
    isLocalRing_etaleLocalRing B S hS Z.1 Z.2 (geometricPointMap g.hom
      (geometricPointMap f.hom xbar))
  letI : Module (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
      (geometricModuleStalk B S hS X xbar F) :=
    Module.compHom _ (etaleLocalRingMap X.2 f.hom xbar)
  Module.Flat
    (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar) ⧸
      Ideal.map (etaleLocalRingMap Y.2 g.hom (geometricPointMap f.hom xbar))
        (IsLocalRing.maximalIdeal (etaleLocalRing B S hS Z.1
          (geometricPointMap g.hom (geometricPointMap f.hom xbar)))))
    (geometricModuleStalk B S hS X xbar F ⧸
      (Ideal.map (etaleLocalRingMap Y.2 g.hom (geometricPointMap f.hom xbar))
        (IsLocalRing.maximalIdeal (etaleLocalRing B S hS Z.1
          (geometricPointMap g.hom (geometricPointMap f.hom xbar)))) •
          (⊤ : Submodule (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
            (geometricModuleStalk B S hS X xbar F))))

/-- **Stacks 0APR.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over `S`
with `X`, `Y`, `Z` locally Noetherian, let `F` be an `𝒪_X`-module and let `x̄` be a geometric
point of `X` whose geometric stalk `F_{x̄}` is a nonzero finite `𝒪_{X, x̄}`-module.  Then `F` is
flat over `Z` at `x̄` and flat on the fibre over `z̄` relative to the fibre of `Y` exactly when
`Y` is flat over `Z` at `ȳ` and `F` is flat over `Y` at `x̄`.

Over the étale local rings `𝒪_{Z, z̄} → 𝒪_{Y, ȳ} → 𝒪_{X, x̄}` this is Stacks 00MP in one
direction, and transitivity of flatness together with base change along
`𝒪_{Y, ȳ} → 𝒪_{Y, ȳ}/𝔪_{z̄}𝒪_{Y, ȳ}` in the other. -/
@[stacks 0APR "The full equivalence, at a geometric point `x̄` of `X`: condition (1) is
  flatness of `F` over `Z` at `x̄` (condition (2) of Stacks 05VU for `X ⟶ Z`) together with the
  fibre condition read on geometric stalks as in part (1) of Stacks 05WY, and condition (2) is
  flatness of `Y` over `Z` at the image point of `ȳ` together with flatness of `F` over `Y` at
  `x̄`.  Local Noetherianity of `X`, `Y`, `Z` is the étale-local scheme property; coherence of
  `F` is used only through finiteness of `F_{x̄}` over `𝒪_{X, x̄}`, which is hypothesised, so
  quasi-coherence of `F` is not assumed.  NOT covered: the identification of the fibre
  condition with flatness of a pullback of `F` to a genuine fibre product over a field-valued
  representative of `z̄`, which is Stacks 05WY."]
theorem isFlatOverAtGeometricPoint_and_isFlatOnFibre_iff {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (F : Modules.{u, m} B S hS X.1 X.2)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hZ : HasEtaleLocalProperty B S hS Z.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (xbar : GeometricPoint B S hS X.1)
    (hfin : Module.Finite (etaleLocalRing B S hS X.1 xbar)
      (geometricModuleStalk B S hS X xbar F))
    (hne : Nontrivial (geometricModuleStalk B S hS X xbar F)) :
    (IsFlatOverAtGeometricPoint B S hS (f ≫ g) F xbar ∧
        IsFlatOnFibreAtGeometricPoint B S hS f g F xbar) ↔
      (IsFlatAt B S hS g.hom (geometricPointMap f.hom xbar).image ∧
        IsFlatOverAtGeometricPoint B S hS f F xbar) := by
  let ybar := geometricPointMap f.hom xbar
  let zbar := geometricPointMap g.hom ybar
  let A := etaleLocalRing B S hS Y.1 ybar
  let A' := etaleLocalRing B S hS X.1 xbar
  let C := etaleLocalRing B S hS Z.1 zbar
  let M := geometricModuleStalk B S hS X xbar F
  let α : A →+* A' := etaleLocalRingMap X.2 f.hom xbar
  let β : C →+* A := etaleLocalRingMap Y.2 g.hom ybar
  let γ : C →+* A' := etaleLocalRingMap X.2 (f ≫ g).hom xbar
  have hαγ : γ = α.comp β := (etaleLocalRingMap_comp X.2 Y.2 f.hom g.hom xbar).symm
  have : IsLocalRing A := isLocalRing_etaleLocalRing B S hS Y.1 Y.2 ybar
  have : IsLocalRing A' := isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
  have : IsLocalRing C := isLocalRing_etaleLocalRing B S hS Z.1 Z.2 zbar
  have : IsNoetherianRing A :=
    isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian B S hS Y.1 Y.2 hY ybar
  have : IsNoetherianRing A' :=
    isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian B S hS X.1 X.2 hX xbar
  have : IsNoetherianRing C :=
    isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian B S hS Z.1 Z.2 hZ zbar
  let : Algebra C A := β.toAlgebra
  let : Algebra A A' := α.toAlgebra
  have : IsLocalHom (algebraMap C A) := isLocalHom_etaleLocalRingMap B S hS Y.2 Z.2 g.hom ybar
  have : IsLocalHom (algebraMap A A') := isLocalHom_etaleLocalRingMap B S hS X.2 Y.2 f.hom xbar
  let : Module A M := Module.compHom M α
  let : Module C M := Module.compHom M γ
  have : IsScalarTower A A' M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower C A M := IsScalarTower.of_algebraMap_smul fun c n => by
    change α (β c) • n = γ c • n
    rw [RingHom.congr_fun hαγ c]
    rfl
  have : Module.Finite A' M := hfin
  have : Nontrivial M := hne
  set J : Ideal A := (IsLocalRing.maximalIdeal C).map (algebraMap C A)
  constructor
  · rintro ⟨hbase, hfibre⟩
    have hflatC : Module.Flat C M := hbase
    have hflatJ : Module.Flat (A ⧸ J) (M ⧸ (J • (⊤ : Submodule A M))) := hfibre
    obtain ⟨hCA, hAM⟩ :=
      Module.flat_and_flat_of_flat_quotient_maximalIdeal_of_flat (R := C) (S := A) (S' := A')
        (M := M)
    exact ⟨(isFlatAt_iff_etaleLocalRingMap_flat Y.2 Z.2 g.hom ybar).mpr hCA, hAM⟩
  · rintro ⟨hgflat, hFflat⟩
    refine ⟨isFlatOverAtGeometricPoint_comp B S hS f g F xbar hFflat hgflat, ?_⟩
    have hAM : Module.Flat A M := hFflat
    have hquot : Module.Flat (A ⧸ J) (M ⧸ (J • (⊤ : Submodule A M))) :=
      (Module.Flat.equiv_iff (isBaseChange_mkQ_smul_top (M := M) J).equiv).mp inferInstance
    exact hquot

end AlgebraicGeometry.Space

end
