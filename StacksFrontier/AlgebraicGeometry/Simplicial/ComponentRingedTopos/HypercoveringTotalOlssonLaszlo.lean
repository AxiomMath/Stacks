module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringOlssonLaszlo

/-!
# The Olsson--Laszlo situation on the total site of a hypercovering

Let `(C, O_C)` be a ringed site with a `LocalSerreFamily` `A_U` and let `K` be a hypercovering.
For the proof of Stacks 0DC7 the source equips the total ringed site `((C/K)_total, O)` with the
data of the Olsson--Laszlo Situation 0D6R for the class `A_total`: the set `B_total` of objects
`V/U_{n,i}` with `V` in the set `B` of condition 0DC4, the bound `d_V`, and the cofinal system
of coverings `Cov_V` of `V`, read over `U_{n,i}` in degree `n`.

An object of the total site is an object `W : V ⟶ U_{n,i}` of a summand slice `C/U_{n,i}` of a
component `C/K_n`, and every covering family of it in the total site is refined by a covering
family of `V` in `C` lifted to `C/U_{n,i}`: the inclusions of the summand slice into the
component and of the component into the total site are cocontinuous.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.summandLift`: a covering family of `V` lifted to the
  object `V/U_{n,i}` of the total site.
* `Stacks.CategoryTheory.Hypercovering.totalOlssonLaszloSituation`: the Olsson--Laszlo
  situation `((C/K)_total, O, A_total)`.

## References

* [Stacks Project, Tag 0DC7](https://stacks.math.columbia.edu/tag/0DC7)
* [Stacks Project, Tag 0D6R](https://stacks.math.columbia.edu/tag/0D6R)
* [Stacks Project, Tag 0D8A](https://stacks.math.columbia.edu/tag/0D8A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.SimplicialSiteSituation CategoryTheory.SimplicialSemiRepresentable
open Stacks.Cohomology.CohomologicalDescent Stacks.Cohomology

universe u

namespace Stacks.CategoryTheory.Hypercovering

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (J : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} J) (OC : Sheaf J.toGrothendieck CommRingCat.{u})
  (T : LocalSerreFamily.{u} (pretopologyRingedSite J OC))

section Lift

/-- The inclusion `C/U_{n,i} ⥤ C/K_n` of a summand slice into the degree-`n` component, with its
target read as the component of the simplicial-site situation of the hypercovering. -/
abbrev summandIncl (n : SimplexCategory) (i : (H.toSimplicialObject.obj (op n)).I) :
    Over ((H.toSimplicialObject.obj (op n)).obj i) ⥤ (hypercoveringSituation J H).component n :=
  summandFunctor (pretopologyRingedSite J OC) H.toSimplicialObject n i

variable {n : SimplexCategory} {i : (H.toSimplicialObject.obj (op n)).I}

/-- **A covering family of `V` lifted to the object `V/U_{n,i}` of the total site.** For an
object `W : V ⟶ U_{n,i}` of the summand slice and a family `{V_k ⟶ V}` of `C`, the family
`{V_k/U_{n,i} ⟶ V/U_{n,i}}` of the total site, lying in degree `n` and summand `i`. -/
def summandLift (W : Over ((H.toSimplicialObject.obj (op n)).obj i))
    (𝒱 : PreZeroHypercover.{u} W.left) :
    PreZeroHypercover.{u} ((componentFunctor (hypercoveringSituation J H) n).obj
      ((summandIncl J H OC n i).obj W)) where
  I₀ := 𝒱.I₀
  X k := (componentFunctor (hypercoveringSituation J H) n).obj
    ((summandIncl J H OC n i).obj
      (Over.mk (𝒱.f k ≫ W.hom)))
  f k := (componentFunctor (hypercoveringSituation J H) n).map
    ((summandIncl J H OC n i).map
      (Over.homMk (𝒱.f k)))

/-- **A covering of `V` lifts to a covering of `V/U_{n,i}` in the total site.** The localization
`C/U_{n,i} ⥤ C` reflects coverings, and the inclusions of the summand into the component and of
the component into the total site are continuous, hence carry covering sieves to covering
sieves. -/
theorem summandLift_sieve₀_mem (W : Over ((H.toSimplicialObject.obj (op n)).obj i))
    (𝒱 : PreZeroHypercover.{u} W.left) (h𝒱 : 𝒱.sieve₀ ∈ J.toGrothendieck W.left) :
    (summandLift J H OC W 𝒱).sieve₀ ∈ (hypercoveringSituation J H).totalTopology _ := by
  have hs := @CoverPreserving.of_isContinuous _ _ _ _
    (summandIncl J H OC n i)
    (J.toGrothendieck.over ((H.toSimplicialObject.obj (op n)).obj i))
    ((hypercoveringSituation J H).componentTopology n)
    (summandFunctor_isContinuous (pretopologyRingedSite J OC) H.toSimplicialObject n i)
  have hc := @CoverPreserving.of_isContinuous _ _ _ _
    (componentFunctor (hypercoveringSituation J H) n)
    ((hypercoveringSituation J H).componentTopology n) (hypercoveringSituation J H).totalTopology
    (componentFunctor_isContinuous (hypercoveringSituation J H) n)
  have h1 := GrothendieckTopology.overEquiv_symm_mem_over _ W _ h𝒱
  refine GrothendieckTopology.superset_covering _ ?_ (hc.cover_preserve (hs.cover_preserve h1))
  rintro Z g ⟨Y, a, b, ⟨Y', a', b', ha', rfl⟩, rfl⟩
  rw [Sieve.overEquiv_symm_iff, Sieve.mem_ofArrows_iff] at ha'
  obtain ⟨k, h, hk⟩ := ha'
  let c := componentFunctor (hypercoveringSituation J H) n
  let sf := summandIncl J H OC n i
  let x : Y' ⟶ Over.mk (𝒱.f k ≫ W.hom) := Over.homMk h
    (by change h ≫ 𝒱.f k ≫ W.hom = Y'.hom; rw [← Category.assoc, ← hk, Over.w])
  let y : Over.mk (𝒱.f k ≫ W.hom) ⟶ W := Over.homMk (𝒱.f k)
  have ha : a' = x ≫ y := Over.OverMorphism.ext (by simp [x, y, hk])
  have this : (summandLift J H OC W 𝒱).sieve₀.arrows
      ((b ≫ c.map (b' ≫ sf.map x)) ≫ c.map (sf.map y)) :=
    (summandLift J H OC W 𝒱).sieve₀.downward_closed (Sieve.ofArrows_mk _ _ k)
      (b ≫ c.map (b' ≫ sf.map x))
  have E : b ≫ c.map (b' ≫ sf.map a') = (b ≫ c.map (b' ≫ sf.map x)) ≫ c.map (sf.map y) :=
    calc b ≫ c.map (b' ≫ sf.map a') = b ≫ c.map (b' ≫ sf.map (x ≫ y)) :=
          congrArg (fun t ↦ b ≫ c.map (b' ≫ sf.map t)) ha
      _ = b ≫ c.map (b' ≫ (sf.map x ≫ sf.map y)) :=
          congrArg (fun t ↦ b ≫ c.map (b' ≫ t)) (sf.map_comp x y)
      _ = b ≫ c.map ((b' ≫ sf.map x) ≫ sf.map y) :=
          congrArg (fun t ↦ b ≫ c.map t) (Category.assoc _ _ _).symm
      _ = b ≫ (c.map (b' ≫ sf.map x) ≫ c.map (sf.map y)) :=
          congrArg (fun t ↦ b ≫ t) (c.map_comp _ _)
      _ = _ := (Category.assoc _ _ _).symm
  exact E ▸ this

/-- The inclusion of a summand slice into the degree-`n` component is cocontinuous: the
component topology is the componentwise localized topology, for which the summand inclusion is
cocontinuous by definition. -/
theorem summandIncl_cover_lift (W : Over ((H.toSimplicialObject.obj (op n)).obj i))
    (S : Sieve ((summandIncl J H OC n i).obj W))
    (hS : S ∈ (hypercoveringSituation J H).componentTopology n ((summandIncl J H OC n i).obj W)) :
    S.functorPullback (summandIncl J H OC n i) ∈
      J.toGrothendieck.over ((H.toSimplicialObject.obj (op n)).obj i) W := by
  have hS' : S ∈ SemiRepresentable.componentwiseTopology J.toGrothendieck
      (H.toSimplicialObject.obj (op n))
      ⟨i, W⟩ := by
    rw [← componentTopology_eq J.toGrothendieck H.toSimplicialObject n]
    exact hS
  exact (Stacks.Cohomology.SimplicialSummand.incl_isCocontinuous J.toGrothendieck
    (H.toSimplicialObject.obj (op n)) i).cover_lift hS'

/-- **Every covering of `V/U_{n,i}` in the total site is refined by a lifted distinguished
covering of `V`.** Pull the covering sieve back to the component, then to the summand slice,
then to `C`: each step is cocontinuous, so the result is a covering sieve of `V`, which a
distinguished covering of `V` refines; its lift then refines the given covering. -/
theorem summandLift_cofinal (W : Over ((H.toSimplicialObject.obj (op n)).obj i))
    (hW : T.bound.B W.left)
    (𝒰 : PreZeroHypercover.{u} ((componentFunctor (hypercoveringSituation J H) n).obj
      ((summandIncl J H OC n i).obj W)))
    (h𝒰 : 𝒰.sieve₀ ∈ (hypercoveringSituation J H).totalTopology _) :
    ∃ 𝒱, (T.bound.coverings W.left hW).cov 𝒱 ∧ Nonempty ((summandLift J H OC W 𝒱).Hom 𝒰) := by
  have h1 : 𝒰.sieve₀.functorPullback (componentFunctor (hypercoveringSituation J H) n) ∈
      (hypercoveringSituation J H).componentTopology n ((summandIncl J H OC n i).obj W) :=
    Functor.cover_lift _ _ _ h𝒰
  have h2 := summandIncl_cover_lift J H OC W _ h1
  rw [GrothendieckTopology.mem_over_iff] at h2
  obtain ⟨𝒱, h𝒱, ⟨φ⟩⟩ := (T.bound.coverings W.left hW).cofinal
    (preZeroHypercoverOfSieve _) (by rw [preZeroHypercoverOfSieve_sieve₀]; exact h2)
  refine ⟨𝒱, h𝒱, ⟨?_⟩⟩
  have hk : ∀ k, 𝒰.sieve₀ ((summandLift J H OC W 𝒱).f k) := fun k ↦ by
    have h0 : (Sieve.overEquiv W _) (φ.h₀ k ≫ (preZeroHypercoverOfSieve _).f (φ.s₀ k)) :=
      (Sieve.overEquiv W _).downward_closed (φ.s₀ k).2.2 (φ.h₀ k)
    have h := φ.w₀ k ▸ h0
    rw [Sieve.overEquiv_iff] at h
    exact h
  choose j a ha using fun k ↦ (Sieve.mem_ofArrows_iff _ _ _).1 (hk k)
  exact { s₀ := j, h₀ := a, w₀ := fun k ↦ (ha k).symm }

/-- **The cofinal system of coverings of `V/U_{n,i}`**: the lifts of the distinguished coverings
`Cov_V` of condition 0DC4. -/
def summandCoverings (W : Over ((H.toSimplicialObject.obj (op n)).obj i))
    (hW : T.bound.B W.left) :
    CofinalCoveringSystem (hypercoveringSituation J H).totalTopology
      ((componentFunctor (hypercoveringSituation J H) n).obj
        ((summandIncl J H OC n i).obj W)) where
  cov := {𝒲 | ∃ 𝒱, (T.bound.coverings W.left hW).cov 𝒱 ∧ 𝒲 = summandLift J H OC W 𝒱}
  isCover := by
    rintro _ ⟨𝒱, h𝒱, rfl⟩
    exact summandLift_sieve₀_mem J H OC W 𝒱 ((T.bound.coverings W.left hW).isCover 𝒱 h𝒱)
  cofinal 𝒰 h𝒰 := by
    obtain ⟨𝒱, h𝒱, hφ⟩ := summandLift_cofinal J H OC T W hW 𝒰 h𝒰
    exact ⟨_, ⟨𝒱, h𝒱, rfl⟩, hφ⟩

end Lift

/-- The degree of an object of the total site of the hypercovering. -/
abbrev totalDegree (x : (hypercoveringSituation J H).totalCategory) : SimplexCategory :=
  (show Grothendieck (slices H.toSimplicialObject) from x).base.unop

/-- The summand of the degree-`totalDegree x` component in which an object of the total site
lies. -/
abbrev totalSummand (x : (hypercoveringSituation J H).totalCategory) :
    (H.toSimplicialObject.obj (op (totalDegree J H x))).I :=
  (show Grothendieck (slices H.toSimplicialObject) from x).fiber.1

/-- An object of the total site, as an object `V ⟶ U_{n,i}` of its summand slice. -/
abbrev totalSliceObj (x : (hypercoveringSituation J H).totalCategory) :
    Over ((H.toSimplicialObject.obj (op (totalDegree J H x))).obj (totalSummand J H x)) :=
  (show Grothendieck (slices H.toSimplicialObject) from x).fiber.2

/-- **Assumption (4) of Stacks 0D7V in the proof of Stacks 0DC7**: the total ringed site
`((C/K)_total, O)` with the class `A_total` satisfies the assumption of the Olsson--Laszlo
Situation 0D6R. The set `B_total` consists of the objects `V/U_{n,i}` with `V` in the set `B` of
condition 0DC4; such an object has the bound `d_V` and the lifts of the distinguished coverings
`Cov_V` (Section 0D8A), and the vanishing comes from 0DBZ, 0DC0 and 0DC2 as in
`isZero_moduleCohomology_totalLocalSerre`. Every object has a covering by members of `B_total`,
lifted from a covering of `V` by members of `B`. -/
def totalOlssonLaszloSituation : OlssonLaszloSituation.{u, u, u, u} where
  C := (hypercoveringSituation J H).totalCategory
  J := (hypercoveringSituation J H).totalTopology
  O := (hypercoveringSituation J H).totalRingSheaf (hypercoveringRingedAugmentation J H OC).O
  hasSheafify := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u, u, u}
  wEqualsLocallyBijective :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u, u, u}
  A := totalLocalSerre J H OC T
  weakSerre := isWeakSerreClass_totalLocalSerre J H OC T
  B x := T.bound.B ((jTotal J H).obj x)
  basis_cover x := by
    obtain ⟨𝒱, h𝒱, hB⟩ := T.bound.basisCover ((jTotal J H).obj x)
    exact ⟨summandLift J H OC (totalSliceObj J H x) 𝒱,
      summandLift_sieve₀_mem J H OC (totalSliceObj J H x) 𝒱 h𝒱, hB⟩
  degreeBound x hx := T.bound.degreeBound _ hx
  coverings x hx := summandCoverings J H OC T (totalSliceObj J H x) hx
  vanishing x hx 𝒲 h𝒲 k p hp F hF := by
    obtain ⟨𝒱, h𝒱, rfl⟩ := h𝒲
    exact isZero_moduleCohomology_totalLocalSerre J OC T H _ _ (totalSliceObj J H x) hx 𝒱 h𝒱 k
      p hp F hF

end Stacks.CategoryTheory.Hypercovering

end
