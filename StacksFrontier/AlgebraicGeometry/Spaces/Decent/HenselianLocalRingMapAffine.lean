module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingMap

/-!
# The map of henselian local rings, on a square whose chart of the target is affine

`AlgebraicGeometry.Space.exists_henselianLocalRingHom_chartSquare` produces the local
homomorphism `φ : 𝒪^h_{Y, f(x)} ⟶ 𝒪^h_{X, x}` induced by a morphism `f : X ⟶ Y` of decent
algebraic spaces, together with a commuting square of pointed étale charts exhibiting it as
induced. The elementary étale neighborhood `V` of `f(x)` in that square is produced affine, by
Stacks 0BBP (`AlgebraicGeometry.Space.exists_affine_elementaryEtaleNeighborhood'`), but the
statement there forgets this. This file records the same construction with the affineness of
`V` kept, which is what a computation of `φ` on global sections of `V` needs.

## Main results

* `AlgebraicGeometry.Space.exists_henselianLocalRingHom_affineChartSquare`: the statement of
  `AlgebraicGeometry.Space.exists_henselianLocalRingHom_chartSquare` with the extra conclusion
  that the chart `V` of `Y` is affine.

## References

* [Stacks Project, Tag 04GS](https://stacks.math.columbia.edu/tag/04GS)
* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The map of henselian local rings induced by a morphism of decent algebraic spaces, on an
affine chart of the target.** Let `f : X ⟶ Y` be a morphism of decent algebraic spaces over `S`
and let `x` be a point of `X`. There is a commuting square of pointed étale charts — an affine
elementary étale neighborhood `V` of `f(x)` in `Y`, an elementary étale neighborhood `U` of `x`
in `X` and a morphism of schemes `j : U ⟶ V` over `f` carrying the distinguished point to the
distinguished point — and a local ring homomorphism `φ : 𝒪^h_{Y, f(x)} ⟶ 𝒪^h_{X, x}` which
agrees on the image of `𝒪_{V, v}` with the stalk map of that square. It is flat when `f` is
flat.

This is `AlgebraicGeometry.Space.exists_henselianLocalRingHom_chartSquare` with the affineness
of `V` kept: the neighborhood is chosen affine by Stacks 0BBP, and the rest of the construction
— the universal property of the henselization, Stacks 04GS, and the ascent of flatness to the
henselization — is the same. -/
theorem exists_henselianLocalRingHom_affineChartSquare
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXd : IsDecentSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hYd : IsDecentSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X) :
    ∃ (V : ElementaryEtaleNeighborhood B S hS Y hY (pointsMap B S hS X f x))
      (U : ElementaryEtaleNeighborhood B S hS X hX x) (j : U.scheme ⟶ V.scheme)
      (hj : j.left.1 U.point = V.point)
      (φ : (henselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd : Type (u + 1)) →+*
        (henselianLocalRing B S hS X hX x hXd : Type (u + 1))),
      yoneda.map j ≫ V.toSpace = U.toSpace ≫ f ∧
        IsAffine V.scheme.left.1 ∧
        IsLocalHom φ ∧
        (∀ a, φ (stalkToHenselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd V a) =
          stalkToHenselianLocalRing B S hS X hX x hXd U
            (((V.scheme.left.1.presheaf.stalkCongr (.of_eq hj.symm)).hom ≫
              j.left.1.stalkMap U.point).hom a)) ∧
        (IsFlat B S hS f → φ.Flat) := by
  classical
  obtain ⟨V, hVaffine, -⟩ := exists_affine_elementaryEtaleNeighborhood' B S hS hY hYd
    (pointsMap B S hS X f x)
  obtain ⟨U, j, hj, hsq, hloc⟩ :=
    exists_elementaryEtaleNeighborhood_pullback_isLocalHom B S hS hY hX hXd f x V
  set α : V.scheme.left.1.presheaf.stalk V.point →+*
      U.scheme.left.1.presheaf.stalk U.point :=
    ((V.scheme.left.1.presheaf.stalkCongr (.of_eq hj.symm)).hom ≫
      j.left.1.stalkMap U.point).hom with hαdef
  let : IsLocalRing (henselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd :
      Type (u + 1)) :=
    henselianLocalRing_isLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd
  let : IsLocalRing (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    henselianLocalRing_isLocalRing B S hS X hX x hXd
  let : Algebra (V.scheme.left.1.presheaf.stalk V.point)
      (henselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd : Type (u + 1)) :=
    stalkAlgebra B S hS Y hY (pointsMap B S hS X f x) hYd V
  let : Algebra (U.scheme.left.1.presheaf.stalk U.point)
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    stalkAlgebra B S hS X hX x hXd U
  let : IsHenselization (V.scheme.left.1.presheaf.stalk V.point)
      (ResidueField (V.scheme.left.1.presheaf.stalk V.point))
      (henselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd : Type (u + 1)) :=
    henselianLocalRing_isHenselization B S hS Y hY (pointsMap B S hS X f x) hYd V
  let : IsHenselization (U.scheme.left.1.presheaf.stalk U.point)
      (ResidueField (U.scheme.left.1.presheaf.stalk U.point))
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    henselianLocalRing_isHenselization B S hS X hX x hXd U
  let : Algebra (V.scheme.left.1.presheaf.stalk V.point)
      (U.scheme.left.1.presheaf.stalk U.point) := α.toAlgebra
  let : Algebra (V.scheme.left.1.presheaf.stalk V.point)
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    ((stalkToHenselianLocalRing B S hS X hX x hXd U).comp α).toAlgebra
  have : IsScalarTower (V.scheme.left.1.presheaf.stalk V.point)
      (U.scheme.left.1.presheaf.stalk U.point)
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocalHom α := hloc
  have : IsLocalHom (stalkToHenselianLocalRing B S hS X hX x hXd U) :=
    isLocalHom_stalkToHenselianLocalRing B S hS X hX x hXd U
  have : IsLocalHom (algebraMap (V.scheme.left.1.presheaf.stalk V.point)
      (henselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd : Type (u + 1))) :=
    isLocalHom_stalkToHenselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd V
  have : IsLocalHom (algebraMap (V.scheme.left.1.presheaf.stalk V.point)
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1))) :=
    RingHom.isLocalHom_comp _ _
  have : HenselianLocalRing (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    IsHenselization.henselian (U.scheme.left.1.presheaf.stalk U.point)
      (ResidueField (U.scheme.left.1.presheaf.stalk U.point))
  obtain ⟨g, hg, -⟩ := HenselianLocalRing.existsUnique_isLocalHom_of_ind_etale
    (R := V.scheme.left.1.presheaf.stalk V.point)
    (Rh := (henselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd : Type (u + 1)))
    (Sh := (henselianLocalRing B S hS X hX x hXd : Type (u + 1)))
    (IsHenselization.ind_etale
      (R := V.scheme.left.1.presheaf.stalk V.point)
      (L := ResidueField (V.scheme.left.1.presheaf.stalk V.point)))
    (IsHenselization.residueField_map_bijective
      (R := V.scheme.left.1.presheaf.stalk V.point)).surjective
  refine ⟨V, U, j, hj, (g : _ →+* _), hsq, hVaffine, ⟨fun a ha ↦ hg.map_nonunit a ha⟩,
    fun a ↦ g.commutes a, fun hf ↦ ?_⟩
  have : AlgebraicGeometry.Flat j.left.1 :=
    hf U.scheme V.scheme U.toSpace V.toSpace j
      (by simpa using U.etale_toSpace U.scheme (𝟙 _) (presheaf_etale_id B S hS U.scheme))
      (by simpa using V.etale_toSpace V.scheme (𝟙 _) (presheaf_etale_id B S hS V.scheme)) hsq
  have : Module.Flat (V.scheme.left.1.presheaf.stalk V.point)
      (U.scheme.left.1.presheaf.stalk U.point) := by
    have hαflat : α.Flat := by
      rw [hαdef, CommRingCat.hom_comp]
      exact RingHom.Flat.comp
        (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))
        (AlgebraicGeometry.Flat.stalkMap j.left.1 U.point)
    exact hαflat
  have : Module.Flat (U.scheme.left.1.presheaf.stalk U.point)
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    IsHenselization.flat (L := ResidueField (U.scheme.left.1.presheaf.stalk U.point))
  have : Module.Flat (V.scheme.left.1.presheaf.stalk V.point)
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    Module.Flat.trans (V.scheme.left.1.presheaf.stalk V.point)
      (U.scheme.left.1.presheaf.stalk U.point)
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1))
  let : Algebra (henselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd : Type (u + 1))
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    (g : _ →+* _).toAlgebra
  have : IsScalarTower (V.scheme.left.1.presheaf.stalk V.point)
      (henselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd : Type (u + 1))
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (g.commutes a).symm
  exact Module.Flat.of_isHenselization
    (R := V.scheme.left.1.presheaf.stalk V.point)
    (Rh := (henselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd : Type (u + 1)))
    (ResidueField (V.scheme.left.1.presheaf.stalk V.point))
    (henselianLocalRing B S hS X hX x hXd : Type (u + 1))

end AlgebraicGeometry.Space

end
