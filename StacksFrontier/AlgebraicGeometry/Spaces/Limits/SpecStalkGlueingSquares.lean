module

public import StacksFrontier.AlgebraicGeometry.Equivalence.PuncturedStage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.OpensSiteSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SpecStalkGlueingData

/-!
# The two cartesian squares of the glueing, in the nested spelling of the overlaps

An open of a scheme `X` over `S` which is the preimage of an open `U ⊆ S` is the fibre product
`U ×_S X`. This file proves it in the big fppf category over `S` for the stages and the vertex of
the system of overlaps, whose opens are the preimages `Dⱼ⁻¹ (W₀ ∩ U)` inside the neighbourhoods
and the preimage of `U` along the leg of the scheme-level cone. These opens are equal to the
preimages of `U` only propositionally.

## Main results

* `AlgebraicGeometry.isPullback_preimage_of_eq`: the scheme-level preimage square, for any open
  equal to the preimage of `U`.
* `AlgebraicGeometry.isPullback_opensSpecStalkStage`: the square `W ∩ U = U ×_S W` at a stage of
  the system of overlaps, in the big fppf category over `S`.
* `AlgebraicGeometry.isPullback_opensSpecStalkApex`: the square `V = U ×_S Spec 𝒪_{S, s}` at its
  vertex.

## References

* [Stacks Project, Tag 0E90](https://stacks.math.columbia.edu/tag/0E90)
* [Stacks Project, Tag 0E91](https://stacks.math.columbia.edu/tag/0E91)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The scheme-level preimage square -/

/-- **An open contained in the preimage of `U` has, after the open immersion, image inside
`U`.** -/
theorem range_ι_comp_subset_of_le_preimage {X Y : Scheme.{u}} (g : X ⟶ Y) (V : Y.Opens)
    (A : X.Opens) (hA : A ≤ g ⁻¹ᵁ V) :
    Set.range ⇑(Scheme.Opens.ι A ≫ g) ⊆ (V : Set Y) := by
  rintro y ⟨z, rfl⟩
  exact hA z.2

/-- **An open of a scheme `X` over `Y` that is the preimage of an open `V` of `Y` is the fibre
product `V ×_Y X`.**  Here `A` is any open equal to `g ⁻¹ᵁ V`, `b` is its open immersion and `a`
is any morphism with `a ≫ ι V = b ≫ g`. -/
theorem isPullback_preimage_of_eq {X Y : Scheme.{u}} (V : Y.Opens) (g : X ⟶ Y) (A : X.Opens)
    (hA : A = g ⁻¹ᵁ V) (a : (A : Scheme.{u}) ⟶ (V : Scheme.{u})) (b : (A : Scheme.{u}) ⟶ X)
    (hb : b = Scheme.Opens.ι A) (ha : a ≫ Scheme.Opens.ι V = b ≫ g) :
    IsPullback a b (Scheme.Opens.ι V) g := by
  subst hA hb
  obtain rfl : a = g ∣_ V := by
    rw [← cancel_mono (Scheme.Opens.ι V), ha, morphismRestrict_ι]
  exact isPullback_morphismRestrict g V

/-! ### The square at a stage of the system of overlaps -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : S)
  (W₀ : AffineOpenNhds S s) (U : S.Opens)

/-- **A stage of the system of overlaps is the preimage of `U` along the open immersion of the
neighbourhood it sits in.** -/
theorem opensSpecStalkStageOpen_eq (j : Over W₀) :
    opensSpecStalkStageOpen S s W₀ U j = Scheme.Opens.ι (X := S) j.left.obj.1 ⁻¹ᵁ U :=
  congrArg (fun g : (affineOpenNhdsDiagram S s).obj j.left ⟶ S => g ⁻¹ᵁ U)
    (affineOpenNhdsDiagram_map_comp_ι s W₀ j)

/-- The structure morphism of a stage of the system of overlaps has range inside `U`. -/
theorem range_opensSpecStalkStageHom_subset (j : Over W₀) :
    Set.range ⇑(opensSpecStalkStageHom S s W₀ U j) ⊆ (U : Set S) :=
  range_ι_comp_subset_of_le_preimage (Scheme.Opens.ι (X := S) j.left.obj.1) U _
    (le_of_eq (opensSpecStalkStageOpen_eq S s W₀ U j))

/-- The morphism from a stage of the system of overlaps to `U`, as a morphism of the big fppf
category over `S`. -/
noncomputable def opensSpecStalkStageToU (j : Over W₀) :
    (opensSpecStalkSiteDiagram B S hS s W₀ U).obj j ⟶ BigFppfOver.opensObj B S hS U :=
  BigFppfOver.homOfRangeLe B S hS U (range_opensSpecStalkStageHom_subset S s W₀ U j)

/-- The morphism from a stage of the system of overlaps to the neighbourhood it sits in, as a
morphism of the big fppf category over `S`. -/
noncomputable def opensSpecStalkStageToW (j : Over W₀) :
    (opensSpecStalkSiteDiagram B S hS s W₀ U).obj j ⟶
      (restrictedAffineOpenNhdsSiteDiagram B S hS s W₀).obj j :=
  Over.homMk (ObjectProperty.homMk (Scheme.Opens.ι (opensSpecStalkStageOpen S s W₀ U j)))
    (by apply ObjectProperty.hom_ext; rfl)

/-- **A square of the big fppf category over `S` that is a fibre product `U ×_S Q` of schemes is
one in the big fppf category.** -/
private theorem isPullback_opensObj_of_toScheme {P Q : BigFppfOver B S hS} (U : S.Opens)
    (a : P ⟶ BigFppfOver.opensObj B S hS U) (b : P ⟶ Q)
    (h : IsPullback ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b)
      (B.inclusion.map (BigFppfOver.opensObj B S hS U).hom) (B.inclusion.map Q.hom)) :
    IsPullback a b (Over.mkIdTerminal.from (BigFppfOver.opensObj B S hS U))
      (Over.mkIdTerminal.from Q) := by
  refine BigFppfOver.isPullback_of_toScheme B S hS ?_
  rwa [← BigFppfOver.toScheme_map_mkIdTerminal_from B S hS (BigFppfOver.opensObj B S hS U),
    ← BigFppfOver.toScheme_map_mkIdTerminal_from B S hS Q] at h

/-- **The overlap `W ∩ U` is the fibre product `U ×_S W` at every stage of the system of
overlaps.** -/
theorem isPullback_opensSpecStalkStage (j : Over W₀) :
    IsPullback (opensSpecStalkStageToU B S hS s W₀ U j)
      (opensSpecStalkStageToW B S hS s W₀ U j)
      (Over.mkIdTerminal.from (BigFppfOver.opensObj B S hS U))
      (Over.mkIdTerminal.from ((restrictedAffineOpenNhdsSiteDiagram B S hS s W₀).obj j)) := by
  exact isPullback_opensObj_of_toScheme B S hS U _ _
    (isPullback_preimage_of_eq U (Scheme.Opens.ι (X := S) j.left.obj.1)
      (opensSpecStalkStageOpen S s W₀ U j) (opensSpecStalkStageOpen_eq S s W₀ U j) _ _ rfl
      (BigFppfOver.hom_hom_eq B S hS (opensSpecStalkStageToU B S hS s W₀ U j)).symm)

/-! ### The square at the vertex -/

/-- The structure morphism of the vertex of the system of overlaps has range inside `U`. -/
theorem range_opensSpecStalkApexHom_subset :
    Set.range ⇑(opensSpecStalkApexHom S s W₀ U) ⊆ (U : Set S) :=
  range_ι_comp_subset_of_le_preimage (S.fromSpecStalk s) U _
    (le_of_eq (specStalkCone_π_preimage S s W₀ U))

/-- The morphism from the vertex of the system of overlaps to `U`, as a morphism of the big fppf
category over `S`. -/
noncomputable def opensSpecStalkApexToU :
    opensSpecStalkSiteObj B S hS s W₀ U ⟶ BigFppfOver.opensObj B S hS U :=
  BigFppfOver.homOfRangeLe B S hS U (range_opensSpecStalkApexHom_subset S s W₀ U)

/-- The morphism from the vertex of the system of overlaps to `Spec 𝒪_{S, s}`, as a morphism of the
big fppf category over `S`. -/
noncomputable def opensSpecStalkApexToM :
    opensSpecStalkSiteObj B S hS s W₀ U ⟶ specStalkSiteObj B S hS s :=
  Over.homMk (ObjectProperty.homMk (Scheme.Opens.ι (opensSpecStalkApexOpen S s W₀ U)))
    (by apply ObjectProperty.hom_ext; rfl)

/-- **`V` is the fibre product `U ×_S Spec 𝒪_{S, s}`**, where `V` is the preimage of `U` along the
leg of the scheme-level cone. -/
theorem isPullback_opensSpecStalkApex :
    IsPullback (opensSpecStalkApexToU B S hS s W₀ U) (opensSpecStalkApexToM B S hS s W₀ U)
      (Over.mkIdTerminal.from (BigFppfOver.opensObj B S hS U))
      (Over.mkIdTerminal.from (specStalkSiteObj B S hS s)) := by
  exact isPullback_opensObj_of_toScheme B S hS U _ _
    (isPullback_preimage_of_eq U (S.fromSpecStalk s) (opensSpecStalkApexOpen S s W₀ U)
      (specStalkCone_π_preimage S s W₀ U) _ _ rfl
      (BigFppfOver.hom_hom_eq B S hS (opensSpecStalkApexToU B S hS s W₀ U)).symm)

end AlgebraicGeometry

end
