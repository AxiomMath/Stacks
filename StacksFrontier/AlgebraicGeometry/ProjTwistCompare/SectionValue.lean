module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.BaseMap

/-!
# The induced morphism on structure-sheaf sections, pointwise

Sections of `AlgebraicGeometry.Proj.structureSheaf 𝒜` over an open `U` are literally dependent
functions on `U` into the homogeneous localizations at the points of `U`, cut out by a
local-fraction condition. This file computes the morphism `mapHom : U(ψ) ⟶ Proj 𝒜` of
`Stacks.AlgebraicGeometry.ProjTwistChain` on such sections *pointwise*: the value of
`mapHom.app U r` at a point `y ∈ U(ψ)` is the comparison map on fibres of
`StacksFrontier.AlgebraicGeometry.ProjTwistCompare.BaseMap` applied to the value of `r` at the
image point. In short, `mapHom` acts on a degree-zero homogeneous fraction `a / s` by `ψ`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistCompare.basePoint`: the image of a point of `U(ψ)` under
  `mapHom`, bound at the `ProjectiveSpectrum` spelling.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.fibreHom`: the fibre comparison at a point of
  `U(ψ)`.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.localRingHom_mapId`: the fibre comparison commutes
  with the maps from a localization away from an element into a localization at a prime.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.val_app_basicOpen`: the pointwise formula on a
  standard open, where the sections of the structure sheaf are `𝒜_{(g)}`.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.val_app`: the pointwise formula on an arbitrary
  open.

## Implementation notes

The route is
`Stacks.AlgebraicGeometry.ProjTwistChain.awayToSection_comp_appLE_mapHom` — Tag 01MY part (2)
as a square of degree-zero homogeneous localizations — pushed to points, and then spread from
standard opens to arbitrary opens along
`Stacks.AlgebraicGeometry.ProjShared.exists_basicOpen_homogeneous_le`, the statement that the
standard opens of positive-degree homogeneous elements form a basis. Nothing unwinds the gluing
that defines `mapHom`, and nothing computes a stalk map.

Three definitional facts make this cheap, and they are worth recording because the obvious
expectation is that they fail. Sections of an open subscheme of `Proj ℬ` over `V` are *equal*,
not merely isomorphic, to sections of `Proj ℬ` over the image of `V`; every restriction map of
the structure sheaf is literally restriction of dependent functions; and `Scheme.Hom.appLE` is
`Scheme.Hom.app` followed by such a restriction. Consequently each of the three reduction steps
— from `app` to `appLE`, from `appLE` along the open immersion to plain restriction, and from a
value on a larger open to a value on a smaller one — holds by `rfl`, with no transport along an
equality of opens, even though the opens involved are only propositionally equal.

The final step is purely algebraic, and is where Mathlib does the work:
`AlgebraicGeometry.Proj.awayToSection` is *defined* by `HomogeneousLocalization.mapId`, the
fibre comparison is `HomogeneousLocalization.localRingHom`, and both are instances of
`HomogeneousLocalization.map`, so the square between them is a consequence of
`HomogeneousLocalization.map_map` and proof irrelevance in the membership side conditions — it
reduces to `rfl` on a representative fraction.

The transparency gotchas of the neighbouring files appear in the same places: the carrier of
`Proj 𝒜` is not `ProjectiveSpectrum 𝒜` at instance transparency, so the primality of a point's
homogeneous ideal is not found unless the point is bound at the `ProjectiveSpectrum` spelling.
That is why `basePoint` and `ambientPoint` are definitions rather than being inlined.

## What is not done

Nothing of the comparison map on twists is done here; it is built on top of this file, in
`StacksFrontier.AlgebraicGeometry.ProjTwistCompare.Twist`, where `val_app` is exactly the
semilinearity of the fibrewise comparison over `Γ(Proj 𝒜, U)`.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain

namespace Stacks.AlgebraicGeometry.ProjTwistCompare

attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-! ### The image point and the fibre comparison at it -/

/-- The image of a point of `U(ψ)` under the induced morphism, as a point of `Proj 𝒜`. Kept as
a definition so that it is bound at the `ProjectiveSpectrum` spelling, where the primality of
its homogeneous ideal is found by instance search. -/
public def basePoint (ψ : 𝒜 →+*ᵍ ℬ) (y : (mapDomain 𝒜 ℬ ψ).toScheme) :
    ProjectiveSpectrum 𝒜 := (mapHom 𝒜 ℬ ψ).base y

/-- The point of `Proj ℬ` underlying a point of `U(ψ)`. -/
public def ambientPoint (ψ : 𝒜 →+*ᵍ ℬ) (y : (mapDomain 𝒜 ℬ ψ).toScheme) :
    ProjectiveSpectrum ℬ := y.1

/-- The homogeneous ideal at `basePoint` is the `ψ`-preimage of the one at the point. -/
public theorem basePoint_asHomogeneousIdeal (ψ : 𝒜 →+*ᵍ ℬ)
    (y : (mapDomain 𝒜 ℬ ψ).toScheme) :
    (basePoint 𝒜 ℬ ψ y).asHomogeneousIdeal =
      (ambientPoint 𝒜 ℬ ψ y).asHomogeneousIdeal.comap ψ :=
  mapHom_base_asHomogeneousIdeal 𝒜 ℬ ψ y

/-- The comparison map on structure-sheaf fibres at a point of `U(ψ)`. -/
public def fibreHom (ψ : 𝒜 →+*ᵍ ℬ) (y : (mapDomain 𝒜 ℬ ψ).toScheme) :
    AtPrime 𝒜 (basePoint 𝒜 ℬ ψ y).asHomogeneousIdeal.toIdeal →+*
      AtPrime ℬ (ambientPoint 𝒜 ℬ ψ y).asHomogeneousIdeal.toIdeal :=
  homogeneousFibreMap 𝒜 ℬ ψ _ _ (basePoint_asHomogeneousIdeal 𝒜 ℬ ψ y)

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- A point of an open `V ⊆ U(ψ)` gives a point of the image of `V`. -/
public theorem mem_image_of_mem (ψ : 𝒜 →+*ᵍ ℬ) {V : (mapDomain 𝒜 ℬ ψ).toScheme.Opens}
    (y : (mapDomain 𝒜 ℬ ψ).toScheme) (hy : y ∈ V) :
    (y.1 : AlgebraicGeometry.Proj ℬ) ∈ (mapDomain 𝒜 ℬ ψ).ι ''ᵁ V :=
  ⟨y, hy, rfl⟩

/-! ### The algebraic square -/

/-- The fibre comparison commutes with the maps out of a localization away from an element: a
degree-zero homogeneous fraction `a / gⁿ` of `𝒜`, pushed into the fibre at a prime and then
mapped by `ψ`, is `ψ a / (ψ g)ⁿ` pushed into the fibre at the corresponding prime of `ℬ`.

Both sides are instances of `HomogeneousLocalization.map`, so on a representative fraction they
are the same term, the membership side conditions being proof-irrelevant. -/
public theorem localRingHom_mapId (ψ : 𝒜 →+*ᵍ ℬ) {I : Ideal A} [I.IsPrime] {J : Ideal B}
    [J.IsPrime] (hIJ : I = Ideal.comap (ψ : A →+* B) J) {g : A}
    (h₁ : Submonoid.powers g ≤ I.primeCompl)
    (h₂ : Submonoid.powers (ψ g) ≤ J.primeCompl) (w : HomogeneousLocalization.Away 𝒜 g) :
    HomogeneousLocalization.localRingHom ψ I J hIJ
        (HomogeneousLocalization.mapId 𝒜 h₁ w) =
      HomogeneousLocalization.mapId ℬ h₂ (HomogeneousLocalization.Away.map ψ g w) := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective w
  rfl

/-- The value at a point of the section of the structure sheaf attached to an element of the
degree-zero localization `𝒜_{(g)}`. This is how `AlgebraicGeometry.Proj.awayToSection` is
defined. -/
public theorem awayToSection_val_apply {g : A} (w : HomogeneousLocalization.Away 𝒜 g)
    (p : ↥(Proj.basicOpen 𝒜 g)) :
    ((Proj.awayToSection 𝒜 g).hom' w).1 p =
      HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr p.2) w := rfl

/-! ### The pointwise formula -/

/-- **The pointwise form of Tag 01MY part (2) on a standard open.** On `D₊(g)`, where the
sections of the structure sheaf are the degree-zero homogeneous localization `𝒜_{(g)}`, the
induced morphism acts fibre by fibre through `ψ`. -/
public theorem val_app_basicOpen (ψ : 𝒜 →+*ᵍ ℬ) {d : ℕ} (hd : 0 < d) {g : A} (hg : g ∈ 𝒜 d)
    (w : HomogeneousLocalization.Away 𝒜 g) (y : (mapDomain 𝒜 ℬ ψ).toScheme)
    (hy : y ∈ mapHom 𝒜 ℬ ψ ⁻¹ᵁ Proj.basicOpen 𝒜 g) :
    (((mapHom 𝒜 ℬ ψ).app (Proj.basicOpen 𝒜 g)).hom'
        ((Proj.awayToSection 𝒜 g).hom' w)).1
      ⟨y.1, mem_image_of_mem 𝒜 ℬ ψ y hy⟩ =
    fibreHom 𝒜 ℬ ψ y (((Proj.awayToSection 𝒜 g).hom' w).1 ⟨basePoint 𝒜 ℬ ψ y, hy⟩) := by
  have hxg : g ∉ (basePoint 𝒜 ℬ ψ y).asHomogeneousIdeal := hy
  have hzg : ψ g ∉ (ambientPoint 𝒜 ℬ ψ y).asHomogeneousIdeal :=
    (notMem_mapHom_base_iff 𝒜 ℬ ψ y hg).mp hxg
  have hyV : y ∈ (mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ g) := hzg
  refine (congrArg (fun s => s.1 ⟨y.1, mem_image_of_mem 𝒜 ℬ ψ y hyV⟩)
    (ConcreteCategory.congr_hom (awayToSection_comp_appLE_mapHom 𝒜 ℬ ψ g d hg hd) w)).trans ?_
  exact (localRingHom_mapId 𝒜 ℬ ψ
    (congrArg HomogeneousIdeal.toIdeal (basePoint_asHomogeneousIdeal 𝒜 ℬ ψ y))
    (Submonoid.powers_le.mpr hxg) (Submonoid.powers_le.mpr hzg) w).symm

/-- **The pointwise form of Tag 01MY part (2).** For any open `U` of `Proj 𝒜`, any section `r`
of the structure sheaf over `U`, and any point `y` of `U(ψ)` mapping into `U`, the value at `y`
of the pulled-back section is the fibre comparison applied to the value of `r` at the image of
`y`.

Nothing in the statement refers to standard opens: this is the statement needed to see the
action of `Γ(Proj 𝒜, U)` on pushed-forward sections, and hence the statement needed to turn a
pointwise comparison of twisting sheaves into a morphism of sheaves of modules. -/
public theorem val_app (ψ : 𝒜 →+*ᵍ ℬ) (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (r : Γ(AlgebraicGeometry.Proj 𝒜, U)) (y : (mapDomain 𝒜 ℬ ψ).toScheme)
    (hy : y ∈ mapHom 𝒜 ℬ ψ ⁻¹ᵁ U) :
    (((mapHom 𝒜 ℬ ψ).app U).hom' r).1 ⟨y.1, mem_image_of_mem 𝒜 ℬ ψ y hy⟩ =
      fibreHom 𝒜 ℬ ψ y (r.1 ⟨basePoint 𝒜 ℬ ψ y, hy⟩) := by
  have hxU : basePoint 𝒜 ℬ ψ y ∈ U := hy
  obtain ⟨d, g, hd, hg, hxg, hgU⟩ := exists_basicOpen_homogeneous_le 𝒜 hxU
  have hyg : y ∈ mapHom 𝒜 ℬ ψ ⁻¹ᵁ Proj.basicOpen 𝒜 g := hxg
  set r' := ((AlgebraicGeometry.Proj 𝒜).presheaf.map (homOfLE hgU).op).hom' r
  have hinv : (Proj.basicOpenIsoAway 𝒜 g hg hd).inv ≫ Proj.awayToSection 𝒜 g = 𝟙 _ := by
    rw [← Proj.basicOpenIsoAway_hom 𝒜 g hg hd]
    exact (Proj.basicOpenIsoAway 𝒜 g hg hd).inv_hom_id
  have hw : (Proj.awayToSection 𝒜 g).hom'
      ((Proj.basicOpenIsoAway 𝒜 g hg hd).inv.hom' r') = r' :=
    ConcreteCategory.congr_hom hinv r'
  have key := val_app_basicOpen 𝒜 ℬ ψ hd hg
    ((Proj.basicOpenIsoAway 𝒜 g hg hd).inv.hom' r') y hyg
  rw [hw] at key
  have hmap := Scheme.Hom.map_appLE (mapHom 𝒜 ℬ ψ)
    (U := Proj.basicOpen 𝒜 g) (U' := U)
    (V := mapHom 𝒜 ℬ ψ ⁻¹ᵁ Proj.basicOpen 𝒜 g) le_rfl (homOfLE hgU).op
  exact (congrArg (fun s => s.1 ⟨y.1, mem_image_of_mem 𝒜 ℬ ψ y hyg⟩)
    (ConcreteCategory.congr_hom hmap r)).symm.trans key

end Stacks.AlgebraicGeometry.ProjTwistCompare

end
