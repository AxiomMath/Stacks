module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.HigherDirectImageLocalVanishing

/-!
# A higher direct image vanishes if cohomology vanishes on a covering family

Let `u : 𝒟 ⥤ 𝒞` be a continuous functor of sites and `ε_* = u^s` the induced direct image of
abelian sheaves. We prove that `R^p ε_* F = 0` as soon as every object `V` of `𝒟` has a covering
sieve all of whose members `W` satisfy `H^p(u(W), F) = 0`.

## Main results

* `Stacks.Cohomology.HigherDirectImageOnACover.isZero_pushforwardCohomologyPresheaf_obj`: the
  value at `V` of the `p`-th cohomology presheaf of the direct image is zero as soon as
  right-derived sections over `u(V)` vanish.
* `Stacks.Cohomology.HigherDirectImageOnACover.isZero_rightDerived_pushforward_of_cover`: the
  criterion, with the hypothesis phrased by right-derived sections.
* `Stacks.Cohomology.HigherDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`: the
  same with the covering family given as a presieve.
* `isZero_rightDerived_pushforward_of_sheafCohomology_cover`, in the same namespace: the same
  with the hypothesis phrased by `CategoryTheory.Sheaf.H'`, for coefficients in the morphism
  universe of the source site.

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SheafifiedHigherDirectImage

universe t v₁ u₁ v₂ u₂

namespace Stacks.Cohomology.HigherDirectImageOnACover

section Sections

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology D} {K : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{t}] [HasSheafify K AddCommGrpCat.{t}]
  [J.HasSheafCompose (forget AddCommGrpCat.{t})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{t})]

/-- The `p`-th cohomology presheaf of a direct image vanishes at `V` as soon as right-derived
sections over `u(V)` vanish. -/
public theorem isZero_pushforwardCohomologyPresheaf_obj (p : ℕ)
    (F : Sheaf K AddCommGrpCat.{t}) (V : D)
    (h : IsZero ((((sheafSections K AddCommGrpCat.{t}).obj
      (op (u.obj V))).rightDerived p).obj F)) :
    IsZero ((((pushforwardCohomologyPresheaf (K := K) AddCommGrpCat.{t} u).rightDerived
      p).obj F).obj (op V)) :=
  h.of_iso ((pushforwardCohomologyPresheafEvaluationIso AddCommGrpCat.{t} u p V).app F).symm

/-- A higher direct image vanishes if right-derived sections vanish on a covering family: if
each object `V` of the target site has a covering sieve all of whose members `W` have
`R^p Γ(u(W), F) = 0`, then `R^p ε_* F = 0`. -/
public theorem isZero_rightDerived_pushforward_of_cover (p : ℕ)
    (F : Sheaf K AddCommGrpCat.{t})
    (h : ∀ V : D, ∃ R ∈ J V, ∀ ⦃W : D⦄ (g : W ⟶ V), R.arrows g →
      IsZero ((((sheafSections K AddCommGrpCat.{t}).obj
        (op (u.obj W))).rightDerived p).obj F)) :
    IsZero (((u.sheafPushforwardContinuous AddCommGrpCat.{t} J K).rightDerived p).obj F) := by
  refine isZero_rightDerived_pushforward_of_locallyZero u p F (fun V ξ ↦ ?_)
  obtain ⟨R, hR, hvan⟩ := h V
  exact J.superset_covering (fun W g hg ↦ (AddCommGrpCat.subsingleton_of_isZero
    (isZero_pushforwardCohomologyPresheaf_obj u p F W (hvan g hg))).elim _ _) hR

/-- If each object `V` of the target site has a presieve generating a covering sieve, all of
whose members `W` have `R^p Γ(u(W), F) = 0`, then `R^p ε_* F = 0`. -/
public theorem isZero_rightDerived_pushforward_of_presieve (p : ℕ)
    (F : Sheaf K AddCommGrpCat.{t})
    (h : ∀ V : D, ∃ P : Presieve V, Sieve.generate P ∈ J V ∧
      ∀ ⦃W : D⦄ (g : W ⟶ V), P g →
        IsZero ((((sheafSections K AddCommGrpCat.{t}).obj
          (op (u.obj W))).rightDerived p).obj F)) :
    IsZero (((u.sheafPushforwardContinuous AddCommGrpCat.{t} J K).rightDerived p).obj F) := by
  refine isZero_rightDerived_pushforward_of_locallyZero u p F (fun V ξ ↦ ?_)
  obtain ⟨P, hgen, hvan⟩ := h V
  exact J.superset_covering ((Sieve.generate_le_iff P _).mpr (fun W g hg ↦
    (AddCommGrpCat.subsingleton_of_isZero
      (isZero_pushforwardCohomologyPresheaf_obj u p F W (hvan g hg))).elim _ _)) hgen

end Sections

section Pinned

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology D} {K : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{v₁}] [HasSheafify K AddCommGrpCat.{v₁}]
  [J.HasSheafCompose (forget AddCommGrpCat.{v₁})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{v₁})]
  [HasExt.{v₁} (Sheaf K AddCommGrpCat.{v₁})]

/-- A higher direct image vanishes if sheaf cohomology vanishes on a covering family: if each
object `V` of the target site has a covering sieve all of whose members `W` have
`Sheaf.H' F p (u.obj W) = 0`, then `R^p ε_* F = 0`. -/
public theorem isZero_rightDerived_pushforward_of_sheafCohomology_cover (p : ℕ)
    (F : Sheaf K AddCommGrpCat.{v₁})
    (h : ∀ V : D, ∃ R ∈ J V, ∀ ⦃W : D⦄ (g : W ⟶ V), R.arrows g →
      IsZero (Sheaf.H' F p (u.obj W))) :
    IsZero (((u.sheafPushforwardContinuous AddCommGrpCat.{v₁} J K).rightDerived p).obj F) :=
  isZero_rightDerived_pushforward_of_cover u p F fun V ↦ (h V).imp fun _ ⟨hR, hvan⟩ ↦
    ⟨hR, fun W g hg ↦ (hvan g hg).of_iso
      (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections
        K F p (u.obj W)).symm⟩

end Pinned

end Stacks.Cohomology.HigherDirectImageOnACover

end
