module

public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.DualizingPullback
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.EpiIso

/-!
# The dualizing sheaf along a contraction, when it is a pullback

Let `k` be a field and `c : X ⟶ Y` a morphism of proper `k`-schemes of dimension at most one
with `𝒪_Y = c_*𝒪_X` and `R^1 c_*𝒪_X = 0`. If `ω_Y` is invertible and `ω_X ≅ c^*𝒩` for some
invertible `𝒪_Y`-module `𝒩`, then `c^*ω_Y ≅ ω_X`.

This is the argument of [Stacks, Tag 0E3N] once `ω_X` is known to lie in the essential image of
`c^*` on invertible modules. There the source compares the functors `H^1(-)^∨` on the categories
of invertible modules on `Y` and of invertible modules on `X` trivial along the contracted curve,
and concludes by the Yoneda lemma. Here the comparison is made through the trace instead:
by [Stacks, Tag 0E7P]'s first step (`Stacks.Duality.exists_pushforward_map_comp_eq_id_of_isZero`)
there is `b : c^*ω_Y ⟶ ω_X` with `c_*(b)` a split monomorphism, so by the projection formula
`ω_Y = c_*c^*ω_Y` is a direct summand of `c_*ω_X = c_*c^*𝒩 = 𝒩`. A split epimorphism between
invertible modules is an isomorphism, so `ω_Y ≅ 𝒩` and `c^*ω_Y ≅ c^*𝒩 ≅ ω_X`.

## Main results

* `Stacks.Curves.DualizingPullback.isIso_of_comp_eq_id_of_isFiniteLocallyFreeOfRank`: a split
  monomorphism between modules finite locally free of rank one is an isomorphism.
* `Stacks.Curves.DualizingPullback.nonempty_pullback_iso_of_pullback_iso`: `c^*ω_Y ≅ ω_X` when
  `ω_X ≅ c^*𝒩` for an invertible `𝒩`.

## References

* [Stacks Project, Tag 0E3N](https://stacks.math.columbia.edu/tag/0E3N)
* [Stacks Project, Tag 0E7P](https://stacks.math.columbia.edu/tag/0E7P)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Curves.DualizingPullback

/-- **A split monomorphism between modules finite locally free of rank one is an isomorphism**:
its retraction is an epimorphism between invertible modules, hence an isomorphism. -/
theorem isIso_of_comp_eq_id_of_isFiniteLocallyFreeOfRank {Z : Scheme.{u}} {A B : Z.Modules}
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} A 1]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} B 1] (s : A ⟶ B) (r : B ⟶ A)
    (h : s ≫ r = 𝟙 A) : IsIso s := by
  have := isInvertible_of_isFiniteLocallyFreeOfRank_one Z A
  have := isInvertible_of_isFiniteLocallyFreeOfRank_one Z B
  have : @Epi (_root_.SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) _ _ _ r :=
    @IsSplitEpi.epi _ _ _ _ r ⟨⟨⟨s, h⟩⟩⟩
  have hr := Stacks.SheafOfModules.isIso_of_epi_of_isInvertible Z.toRingedSpace r
  have : IsIso r := ⟨⟨hr.out.choose, hr.out.choose_spec⟩⟩
  exact ⟨⟨r, h, by rw [IsIso.eq_inv_of_inv_hom_id h, IsIso.hom_inv_id]⟩⟩

section Core

open Stacks.Duality Stacks.AlgebraicGeometry.CurveEulerBridge

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (c : X ⟶ Y) (g : Y ⟶ Spec (.of k))

/-- **`c^*ω_Y ≅ ω_X` when `ω_X` is a pullback**, for `c : X ⟶ Y` between proper `k`-schemes of
dimension at most one with `𝒪_Y = c_*𝒪_X`, `R^1 c_*𝒪_X = 0` and `ω_Y` invertible, provided
`ω_X ≅ c^*𝒩` for an invertible `𝒩`. The trace gives `b : c^*ω_Y ⟶ ω_X` with `c_*(b)` split
mono; by the projection formula this is a split mono `ω_Y ⟶ 𝒩` of invertible modules, hence an
isomorphism. -/
theorem nonempty_pullback_iso_of_pullback_iso [IsProper (c ≫ g)] [IsProper g]
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (hR1 : IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualizingSheafOverField g) 1]
    (N : Y.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N 1]
    (e : (Scheme.Modules.pullback c).obj N ≅ dualizingSheafOverField (c ≫ g)) :
    Nonempty ((Scheme.Modules.pullback c).obj (dualizingSheafOverField g) ≅
      dualizingSheafOverField (c ≫ g)) := by
  have : IsProper c := IsProper.of_comp c g
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  set L := (Scheme.Modules.pullback c).obj (dualizingSheafOverField g)
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback c (dualizingSheafOverField g) 1
  have := isInvertible_of_isFiniteLocallyFreeOfRank_one Y (dualizingSheafOverField g)
  have := isInvertible_of_isFiniteLocallyFreeOfRank_one Y N
  have hRL : ∀ i : ℕ, 0 < i → IsZero (((Scheme.Modules.pushforward c).rightDerived i).obj L) :=
    fun i hi => Stacks.ProjectionFormula.isZero_rightDerived_pullback_of_isZero_rightDerived_unit
      c (dualizingSheafOverField g) i (isZero_rightDerived_unit c g hdimX hR1 i hi)
  let eL := Stacks.ProjectionFormula.pushforwardPullbackIsoOfIsIso c (dualizingSheafOverField g) hO
  have : L.IsCoherent := isCoherent_of_isFiniteLocallyFreeOfRank k (c ≫ g) L 1
  obtain ⟨b, t, hbt⟩ := exists_pushforward_map_comp_eq_id_of_isZero c g hdimX hdimY L
    (isQuasicoherent_of_isCoherent L) hRL eL
  let E : (Scheme.Modules.pushforward c).obj (dualizingSheafOverField (c ≫ g)) ≅ N :=
    (Scheme.Modules.pushforward c).mapIso e.symm ≪≫
      Stacks.ProjectionFormula.pushforwardPullbackIsoOfIsIso c N hO
  let s : dualizingSheafOverField g ⟶ N := eL.inv ≫ (Scheme.Modules.pushforward c).map b ≫ E.hom
  let r : N ⟶ dualizingSheafOverField g := E.inv ≫ t ≫ eL.hom
  have hsr : s ≫ r = 𝟙 _ := by
    simp only [s, r, Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% hbt, Iso.inv_hom_id]
  have := isIso_of_comp_eq_id_of_isFiniteLocallyFreeOfRank s r hsr
  exact ⟨(Scheme.Modules.pullback c).mapIso (asIso s) ≪≫ e⟩

end Core

end Stacks.Curves.DualizingPullback
