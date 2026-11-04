module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiHigherDirectImageVanishing
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The cohomology presheaf of a direct image

Let `u : 𝒟 ⥤ 𝒞` be a continuous functor between sites and `f_* = u^s` the induced direct image of
`𝒜`-valued sheaves. The presheaf underlying `f_* F` is `V ↦ F(u(V))`, so the functor
`pushforwardCohomologyPresheaf`, whose `p`-th right derived functor is the presheaf
`V ↦ H^p(u(V), F)` of [Stacks, Tag 072W], is `sheafToPresheaf` followed by precomposition with
`u.op`. Precomposition of presheaves is exact, so

`R^p (pushforward cohomology presheaf) ≅ (R^p sheafToPresheaf) ⋙ (- ∘ u.op)`:

the cohomology presheaf of a direct image is the cohomology presheaf of the source site,
restricted along `u`.

## Main definitions

* `Stacks.Cohomology.SheafifiedHigherDirectImage.pushforwardCohomologyPresheafRestrictionIso`:
  the isomorphism above.
* `sheafToPresheafRightDerivedEvaluationIso`, in the same namespace: evaluation of presheaves at
  an object `U` commutes with the right derived functor of `sheafToPresheaf`, so the value at `U`
  of the `p`-th cohomology presheaf of a site is `H^p(U, -)`.

## Main results

* `isZero_rightDerived_pushforward_of_restrictionIso`, in the same namespace: `R^p f_* F = 0` for
  `p > 0` as soon as the `p`-th cohomology presheaf of `F` on the source site, restricted along
  `u`, is isomorphic to the `p`-th cohomology presheaf of some sheaf on the target site.
* `isIso_properDerivedImageComparison_of_restrictedCohomologyPresheafIso`, in the namespace
  `Stacks.Topology.LocallyQuasiCompactZariskiSituation`: for a proper map, the derived Zariski
  base-change comparison map of [Stacks, Tag 0DCU] is invertible as soon as, for injective `J` and
  `p > 0`, the restricted cohomology presheaf of `π_X^{-1} J` is the cohomology presheaf of some
  sheaf on the big site over the target.
* `isIso_properDerivedImageComparison_of_restrictedCohomologyPresheafIso_pushforward`: the same,
  with that sheaf taken to be `π_Y^{-1}(g_* J)`.

## Implementation notes

The instances making `(Functor.whiskeringLeft _ _ 𝒜).obj u.op` additive and homology-preserving
need `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` and
`Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory` imported directly.

`sheafToPresheafRightDerivedEvaluationIso` is stated for the composite
`sheafToPresheaf K A ⋙ (evaluation Cᵒᵖ A).obj (op U)`, definitionally
`(sheafSections K A).obj (op U)`, because the additivity of the composite is available from that
of its two factors.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.SheafifiedHigherDirectImage

namespace Stacks.Cohomology.SheafifiedHigherDirectImage

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology D} {K : GrothendieckTopology C}
  (A : Type*) [Category* A] [Abelian A] [HasSheafify J A] [HasSheafify K A]
  (u : D ⥤ C) [u.IsContinuous J K] [EnoughInjectives (Sheaf K A)]

/-- The `p`-th right derived functor of `pushforwardCohomologyPresheaf A u`, the presheaf
`V ↦ H^p(u(V), F)` of [Stacks, Tag 072W], is the `p`-th right derived functor of
`sheafToPresheaf`, the presheaf `U ↦ H^p(U, F)` of the source site, precomposed with `u.op`. -/
def pushforwardCohomologyPresheafRestrictionIso (p : ℕ) :
    (pushforwardCohomologyPresheaf (K := K) A u).rightDerived p ≅
      (sheafToPresheaf K A).rightDerived p ⋙ (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj u.op :=
  Functor.rightDerivedCompIso (sheafToPresheaf K A)
    ((Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj u.op) p

/-- The `p`-th right derived functor of `sheafToPresheaf`, evaluated at `U`, is the `p`-th right
derived functor of the sections functor at `U`, that is `H^p(U, -) = R^p Γ(U, -)`. -/
def sheafToPresheafRightDerivedEvaluationIso (p : ℕ) (U : C) :
    (sheafToPresheaf K A ⋙ (evaluation Cᵒᵖ A).obj (op U)).rightDerived p ≅
      (sheafToPresheaf K A).rightDerived p ⋙ (evaluation Cᵒᵖ A).obj (op U) :=
  Functor.rightDerivedCompIso (sheafToPresheaf K A) ((evaluation Cᵒᵖ A).obj (op U)) p

/-- Let `p > 0`. If the `p`-th cohomology presheaf of `F` on the source site, restricted along
`u`, is isomorphic to the `p`-th cohomology presheaf of a sheaf `G` on the target site, then
`R^p f_* F = 0`. -/
theorem isZero_rightDerived_pushforward_of_restrictionIso [EnoughInjectives (Sheaf J A)] (p : ℕ)
    (hp : 0 < p) (F : Sheaf K A) (G : Sheaf J A)
    (e : u.op ⋙ ((sheafToPresheaf K A).rightDerived p).obj F ≅
      ((sheafToPresheaf J A).rightDerived p).obj G) :
    IsZero (((u.sheafPushforwardContinuous A J K).rightDerived p).obj F) :=
  isZero_rightDerived_pushforward_of_cohomologyPresheafIso A u p hp F G
    ((pushforwardCohomologyPresheafRestrictionIso A u p).app F ≪≫ e)

end Stacks.Cohomology.SheafifiedHigherDirectImage

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

attribute [local instance] HasDerivedCategory.standard

-- The cheap instance for `HasPointwiseRightDerivedFunctor` on `K⁺` has to be given precedence,
-- or synthesis tries to prove termwise injectivity of an unknown complex and times out.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v})]

/-- Let `f : X ⟶ Y` be proper. The derived Zariski base-change comparison map of `f` is invertible
as soon as, for every injective abelian sheaf `J` on the small Zariski site of `X` and every
`p > 0`, the cohomology presheaf `W ↦ H^p(W, π_X^{-1} J)` of the big site over `X`, restricted
along `Over.pullback f` (that is, evaluated at the objects `Z ×_Y X`), is isomorphic to the
cohomology presheaf `Z ↦ H^p(Z, G)` of some abelian sheaf `G` on the big site over `Y`. -/
theorem isIso_properDerivedImageComparison_of_restrictedCohomologyPresheafIso
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u}
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj))
    (hcoh : ∀ J : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v},
      Injective J → ∀ p : ℕ, 0 < p →
        ∃ G : Sheaf (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v},
          Nonempty ((Over.pullback f).op ⋙
              ((sheafToPresheaf (S.zariskiTopology.over X)
                  AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj
                ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J) ≅
            ((sheafToPresheaf (S.zariskiTopology.over Y)
                AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj G)) :
    IsIso (properDerivedImageComparison.{u, w, v} S f) := by
  refine isIso_properDerivedImageComparison_of_cohomologyPresheafIso.{u, w, v} S f hf
    fun J hJ p hp => ?_
  obtain ⟨G, ⟨e⟩⟩ := hcoh J hJ p hp
  exact ⟨G, ⟨(pushforwardCohomologyPresheafRestrictionIso AddCommGrpCat.{max (u + 1) v}
    (Over.pullback f) p).app _ ≪≫ e⟩⟩

/-- Let `f : X ⟶ Y` be proper, with underlying continuous map `g`. The derived Zariski
base-change comparison map of `f` is invertible as soon as, for every injective abelian sheaf `J`
on the small Zariski site of `X` and every `p > 0`, the presheaf `W ↦ H^p(W, π_X^{-1} J)` on the
big site over `X`, evaluated at the objects `Z ×_Y X`, is isomorphic to the presheaf
`Z ↦ H^p(Z, π_Y^{-1}(g_* J))` on the big site over `Y`. -/
theorem isIso_properDerivedImageComparison_of_restrictedCohomologyPresheafIso_pushforward
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u}
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj))
    (hcoh : ∀ J : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v},
      Injective J → ∀ p : ℕ, 0 < p →
        Nonempty ((Over.pullback f).op ⋙
            ((sheafToPresheaf (S.zariskiTopology.over X)
                AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj
              ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J) ≅
          ((sheafToPresheaf (S.zariskiTopology.over Y)
              AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj
            ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).obj
              ((topologicalPushforward.{u, w, v} S f).obj J)))) :
    IsIso (properDerivedImageComparison.{u, w, v} S f) :=
  isIso_properDerivedImageComparison_of_restrictedCohomologyPresheafIso.{u, w, v} S f hf
    fun J hJ p hp => ⟨_, hcoh J hJ p hp⟩

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
