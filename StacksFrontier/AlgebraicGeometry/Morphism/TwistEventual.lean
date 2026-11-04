module

public import StacksFrontier.AlgebraicGeometry.Morphism.TwistExists
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.EventualBijective

/-!
# Tags 07ZI, 07ZJ and 07ZK, assertion (3): the maps on twists

Let `S` be a scheme, let `A` and `B` be quasi-coherent graded `𝒪_S`-algebras and let `ψ : A ⟶ B`
be a homomorphism between them. Write `X = Proj_S(A)` and `Y = Proj_S(B)`, let `U(ψ) ⊆ Y` be the
open on which `ψ` induces a morphism, let `r_ψ : U(ψ) ⟶ X` be that morphism and let

`θ_n : r_ψ^* 𝒪_X(n) ⟶ 𝒪_Y(n)|_{U(ψ)}`

be the map of Tag 07ZG's assertion (3). This file proves the third assertion of each of Tags 07ZI,
07ZJ and 07ZK about `θ_n` itself: it is an epimorphism when `A_d → B_d` is surjective in all large
degrees, an isomorphism when `A_d → B_d` is an isomorphism in all large degrees, and an isomorphism
in the surjective case as well once `A` is generated in degree one over every affine open of the
base.

The pieces of `U(ψ)` over the affine opens of the base cover `U(ψ)`, and over such a piece `θ_n` is
the absolute comparison map of Tag 01MY for the induced homomorphism `Γ(U, A) ⟶ Γ(U, B)` of graded
rings of sections, conjugated by two isomorphisms
(`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap_chart`). Both of being an epimorphism and
of being an isomorphism are properties of a morphism of sheaves of modules that are local on the
scheme and stable under conjugation by isomorphisms, and the chart-level assertions are the three
results of Tags 07ZI, 07ZJ and 07ZK read in the charts. So each of the three assertions is the
corresponding chart-level assertion carried along that cover.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.epi_of_epi_pullback_locally` and
  `Stacks.AlgebraicGeometry.Tag07ZGTwist.isIso_of_isIso_pullback_locally`: a morphism of sheaves of
  modules on a scheme whose inverse image along some open immersion through every point is an
  epimorphism, respectively an isomorphism, is an epimorphism, respectively an isomorphism.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.epi_relativeTwistMap_of_forall_chart` and
  `Stacks.AlgebraicGeometry.Tag07ZGTwist.isIso_relativeTwistMap_of_forall_chart`: **the
  globalization of the affine-local description.** If the absolute comparison map of Tag 01MY is an
  epimorphism, respectively an isomorphism, over every affine open of the base, then so is `θ_n`.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.epi_relativeTwistMap_of_eventually_epi`: **Tag 07ZI's
  assertion (3).**
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.isIso_relativeTwistMap_of_eventually_isIso`: **Tag 07ZJ's
  assertion (3).**
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.isIso_relativeTwistMap_of_generatedInDegreeOne`: **Tag
  07ZK's assertion (3).**

## Implementation notes

Locality of invertibility is `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk`,
through the identification of the stalks of a restriction with the stalks of the module
(`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`). Locality of surjectivity is proved here
on sections: two morphisms out of the target which agree after restriction to each member of the
cover agree on a neighbourhood of every point, and a morphism of sheaves is determined by such
local data.

## References

* [Stacks Project, Tag 07ZI](https://stacks.math.columbia.edu/tag/07ZI)
* [Stacks Project, Tag 07ZJ](https://stacks.math.columbia.edu/tag/07ZJ)
* [Stacks Project, Tag 07ZK](https://stacks.math.columbia.edu/tag/07ZK)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter Opposite
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

universe u

/-! ### Surjectivity and invertibility are local on the scheme -/

section Locality

variable {X : Scheme.{u}} {M N : X.Modules}

/-- The restriction of a morphism of sheaves of modules along an open immersion is an epimorphism
as soon as its inverse image is: the two differ by conjugation with
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. -/
private theorem epi_restrictFunctor_map_of_epi_pullback_map {Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (φ : M ⟶ N) (h : Epi ((Scheme.Modules.pullback f).map φ)) :
    Epi ((Scheme.Modules.restrictFunctor f).map φ) := by
  have := h
  have e := Scheme.Modules.restrictFunctorIsoPullback f
  have h2 : Epi ((Scheme.Modules.restrictFunctor f).map φ ≫ e.hom.app N) := by
    rw [e.hom.naturality φ]; infer_instance
  exact (epi_comp_iff_of_isIso _ (e.hom.app N)).mp h2

/-- **Surjectivity of a morphism of sheaves of modules is local on the scheme.** If every point of
`X` lies in the image of an open immersion along which the inverse image of `φ` is an epimorphism,
then `φ` is an epimorphism.

Two morphisms out of the target of `φ` which agree after composition with `φ` agree after
restriction to each member of the cover, hence on a neighbourhood of every point of every open, and
a section of a sheaf is determined by such local data. -/
public theorem epi_of_epi_pullback_locally (φ : M ⟶ N)
    (h : ∀ x : X, ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsOpenImmersion f ∧ x ∈ Set.range f ∧
      Epi ((Scheme.Modules.pullback f).map φ)) :
    Epi φ := by
  refine ⟨fun {P} a b hab => ?_⟩
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  apply P.isSheaf.section_ext
  intro x hx
  obtain ⟨Y, f, hf, ⟨y, hy⟩, he⟩ := h x
  have := hf
  have : Epi ((Scheme.Modules.restrictFunctor f).map φ) :=
    epi_restrictFunctor_map_of_epi_pullback_map f φ he
  have hab' : (Scheme.Modules.restrictFunctor f).map a =
      (Scheme.Modules.restrictFunctor f).map b := by
    apply (cancel_epi ((Scheme.Modules.restrictFunctor f).map φ)).mp
    simpa only [← Functor.map_comp] using
      congrArg ((Scheme.Modules.restrictFunctor f).map) hab
  have hsec : a.app (f ''ᵁ (f ⁻¹ᵁ U)) = b.app (f ''ᵁ (f ⁻¹ᵁ U)) :=
    congrArg (fun k => k.app (f ⁻¹ᵁ U)) hab'
  refine ⟨f ''ᵁ (f ⁻¹ᵁ U), f.image_preimage_le U, ⟨y, by simpa [hy], hy⟩, ?_⟩
  have ha := a.mapPresheaf.naturality (homOfLE (f.image_preimage_le U)).op
  have hb := b.mapPresheaf.naturality (homOfLE (f.image_preimage_le U)).op
  exact (congrArg (fun k => k s) ha).symm.trans
    ((congrArg (fun k => k (N.presheaf.map (homOfLE (f.image_preimage_le U)).op s)) hsec).trans
      (congrArg (fun k => k s) hb))

/-- **Invertibility of a morphism of sheaves of modules is local on the scheme.** If every point of
`X` lies in the image of an open immersion along which the inverse image of `φ` is an isomorphism,
then `φ` is an isomorphism.

This is `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk`: the stalk of a
restriction at a point is the stalk of the module at its image, so the hypothesis makes every
stalk of `φ` invertible. -/
public theorem isIso_of_isIso_pullback_locally (φ : M ⟶ N)
    (h : ∀ x : X, ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsOpenImmersion f ∧ x ∈ Set.range f ∧
      IsIso ((Scheme.Modules.pullback f).map φ)) :
    IsIso φ := by
  refine AffineBaseChange.isIso_of_isIso_stalk φ fun x => ?_
  obtain ⟨Y, f, hf, ⟨y, hy⟩, he⟩ := h x
  have := hf
  have : IsIso ((Scheme.Modules.restrictFunctor f).map φ) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback f) φ).mpr he
  rw [← hy]
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso f y) φ).mp
    (Functor.map_isIso (Scheme.Modules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y) _)

end Locality

/-! ### The globalization of the affine-local description -/

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)

/-- The affine-local comparison map, factored: Tag 01MY's `θ` for the induced homomorphism of
graded rings of sections over `U`, read along the identification of the absolute domain of
definition with the piece of `U(ψ)` over `U` and conjugated by the identifications of the source
and the target. -/
private theorem relativeTwistChart_eq (n : ℤ) (U : S.affineOpens) :
    relativeTwistChart ψ n U =
      (chartSourceIso ψ n U).hom ≫
        (Scheme.Modules.pullback (chartDomainIso ψ U).inv).map
          (twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) n) ≫
        (chartTargetIso ψ n U).inv :=
  rfl

/-- Every point of `U(ψ)` lies in the piece of `U(ψ)` over some affine open of the base. -/
private theorem exists_mem_range_pieceIncl (x : ψ.relativeMapDomain.toScheme) :
    ∃ U : S.affineOpens, x ∈ Set.range (pieceIncl ψ U) := by
  have hx : x ∈ (⊤ : ψ.relativeMapDomain.toScheme.Opens) := trivial
  rw [← iSup_image_pieceIncl_eq_top ψ] at hx
  obtain ⟨U, y, -, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨U, y, hy⟩

/-- **The affine-local description globalizes surjectivity.** If Tag 01MY's comparison map on the
`n`-th twist is an epimorphism over every affine open of the base, then so is the map `θ_n` of Tag
07ZG.

The pieces of `U(ψ)` over the affine opens of the base cover `U(ψ)`, surjectivity of a morphism of
sheaves of modules is local on the scheme, and over such a piece `θ_n` is the comparison map over
that affine open conjugated by two isomorphisms. -/
public theorem epi_relativeTwistMap_of_forall_chart (n : ℤ)
    (h : ∀ U : S.affineOpens,
      Epi (twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) n)) :
    Epi (relativeTwistMap ψ n) := by
  refine epi_of_epi_pullback_locally (relativeTwistMap ψ n) fun x => ?_
  obtain ⟨U, hU⟩ := exists_mem_range_pieceIncl ψ x
  refine ⟨_, pieceIncl ψ U, inferInstance, hU, ?_⟩
  rw [relativeTwistMap_chart ψ n U, relativeTwistChart_eq ψ n U]
  have := h U
  infer_instance

/-- **The affine-local description globalizes invertibility.** If Tag 01MY's comparison map on the
`n`-th twist is an isomorphism over every affine open of the base, then so is the map `θ_n` of Tag
07ZG. -/
public theorem isIso_relativeTwistMap_of_forall_chart (n : ℤ)
    (h : ∀ U : S.affineOpens,
      IsIso (twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) n)) :
    IsIso (relativeTwistMap ψ n) := by
  refine isIso_of_isIso_pullback_locally (relativeTwistMap ψ n) fun x => ?_
  obtain ⟨U, hU⟩ := exists_mem_range_pieceIncl ψ x
  refine ⟨_, pieceIncl ψ U, inferInstance, hU, ?_⟩
  rw [relativeTwistMap_chart ψ n U, relativeTwistChart_eq ψ n U]
  have := h U
  infer_instance

/-! ### The three assertions -/

/-- **Stacks Project, Tag 07ZI.** *Assertion (3): the maps on twists are surjective.*

If `A_d → B_d` is surjective for all sufficiently large `d`, then for every `n` the map

`θ_n : r_ψ^* 𝒪_X(n) ⟶ 𝒪_Y(n)|_{U(ψ)}`

of Tag 07ZG is an epimorphism. (These maps are not isomorphisms in general; Tag 07ZK gives a
hypothesis under which they are.)

Over every affine open of the base this is the surjectivity of Tag 01MY's comparison map for the
induced homomorphism of graded rings of sections, which is
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.epi_chart_twistMap_of_eventually_epi`. -/
public theorem epi_relativeTwistMap_of_eventually_epi
    (hψ : ∀ᶠ d : ℕ in atTop, Epi (ψ.app (d : ℤ))) (n : ℤ) :
    Epi (relativeTwistMap ψ n) :=
  epi_relativeTwistMap_of_forall_chart ψ n fun U => by
    have h := epi_chart_twistMap_of_eventually_epi ψ hψ U.2 n
    rwa [projMapData_twistMap] at h

/-- **Stacks Project, Tag 07ZJ.** *Assertion (3): the maps on twists are isomorphisms.*

If `A_d → B_d` is an isomorphism for all sufficiently large `d`, then for every `n` the map `θ_n`
of Tag 07ZG is an isomorphism.

Over every affine open of the base this is
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.isIso_chart_twistMap_of_eventually_isIso`. -/
public theorem isIso_relativeTwistMap_of_eventually_isIso
    (hψ : ∀ᶠ d : ℕ in atTop, IsIso (ψ.app (d : ℤ))) (n : ℤ) :
    IsIso (relativeTwistMap ψ n) :=
  isIso_relativeTwistMap_of_forall_chart ψ n fun U => by
    have h := isIso_chart_twistMap_of_eventually_isIso ψ hψ U.1 n
    rwa [projMapData_twistMap] at h

/-- **Stacks Project, Tag 07ZK.** *Assertion (3): the maps on twists are isomorphisms.*

If `A_d → B_d` is surjective for all sufficiently large `d` and `A` is generated in degree one over
`A_0` over every affine open of the base, then for every `n` the map `θ_n` of Tag 07ZG is an
isomorphism.

Over every affine open of the base this is
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.isIso_chart_twistMap_of_generatedInDegreeOne`. -/
public theorem isIso_relativeTwistMap_of_generatedInDegreeOne
    (hψ : ∀ᶠ d : ℕ in atTop, Epi (ψ.app (d : ℤ)))
    (hgen : ∀ U : S.Opens, IsAffineOpen U → A.IsGeneratedInDegreeOneAt U) (n : ℤ) :
    IsIso (relativeTwistMap ψ n) :=
  isIso_relativeTwistMap_of_forall_chart ψ n fun U => by
    have h := isIso_chart_twistMap_of_generatedInDegreeOne ψ hψ hgen U.2 n
    rwa [projMapData_twistMap] at h

end Stacks.AlgebraicGeometry.Tag07ZGTwist

end
