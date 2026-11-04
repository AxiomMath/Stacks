module
public import StacksCore.CategoryTheory.Filtration.Preadditive
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImageUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldSheaves
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.RingTheory.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageDirectSums

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DirectSumsOfEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointDerivedConservativity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageFilteredColimits

/-!
# Filtered colimits and direct sums of acyclic abelian étale sheaves

Let `X` be a quasi-compact and quasi-separated scheme. Étale cohomology of `X` commutes with
filtered colimits (Stacks 03Q5) and with direct sums. Read through right acyclicity this says:

* `Γ(X, -)` commutes with filtered colimits of abelian sheaves;
* a filtered colimit, or a direct sum, of `Γ(X, -)`-acyclic abelian sheaves is `Γ(X, -)`-acyclic.

The same holds for the direct image `f_*` along a quasi-compact and quasi-separated morphism
`f : X ⟶ Y`, whose higher direct images commute with filtered colimits
(`Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_etaleAbelianDirectImage`), and in
particular along any `f' : X' ⟶ Spec Ω` with `X'` quasi-compact and quasi-separated. Over the
spectrum of a separably closed field `Ω`, `f'_*`-acyclicity is moreover the same thing as
`Γ(X', -)`-acyclicity, because `Γ(Spec Ω, -)` is an exact equivalence and `Γ(Spec Ω, f'_* -)` is
`Γ(X', -)`.

Acyclicity is `CategoryTheory.Functor.rightAcyclic`, the form taken by Leray's acyclicity lemma
for the unbounded `Rf_*`,
`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedDirectImageUnit_app_of_plus_of_rightAcyclic`.

## Main results

* `Stacks.DerivedFunctor.rightAcyclic_of_isColimit` — for a left exact functor `F`, a colimit of
  `F`-acyclic objects is `F`-acyclic as soon as the higher right derived functors of `F` preserve
  it.
* `Stacks.EtaleCohomology.preservesColimitsOfShape_Γ_smallEtale`,
  `Stacks.EtaleCohomology.rightAcyclic_Γ_colimit_smallEtale` and
  `Stacks.EtaleCohomology.rightAcyclic_Γ_sigma_smallEtale` — global sections on a quasi-compact
  quasi-separated scheme.
* `Stacks.EtaleCohomology.preservesColimitsOfShape_etaleAbelianDirectImage`,
  `Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_etaleAbelianDirectImage`,
  `Stacks.EtaleCohomology.rightAcyclic_etaleAbelianDirectImage_colimit` and
  `Stacks.EtaleCohomology.rightAcyclic_etaleAbelianDirectImage_sigma` — the direct image along a
  quasi-compact quasi-separated morphism.
* `Stacks.EtaleCohomology.rightDerivedEtaleAbelianDirectImageCompΓIso` and
  `Stacks.EtaleCohomology.rightAcyclic_etaleAbelianDirectImage_iff_of_isSepClosed` — over
  `Spec Ω`, `Γ(Spec Ω, Rⁿf'_* M) ≅ Hⁿ(X', M)`, so `f'_*`-acyclic means `Γ(X', -)`-acyclic.

## Implementation notes

Index categories of filtered colimits and index types of direct sums live in
`Type (max (u + 1) v)`, the universe of the coefficients `AddCommGrpCat.{max (u + 1) v}`, as in
Stacks 03Q5 here (`Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_Γ_smallEtale`).
Existence of the colimits is opened from the scoped namespace
`AlgebraicGeometry.Scheme.SmallEtaleColimits`. Stating `Functor.rightAcyclic` sends instance
search after a `HasRightDerivedFunctor` whose default route does not terminate in time, so the
instance coming from `EnoughInjectives` is given precedence, as in
`StacksFrontier/Algebra/Homology/DerivedCategory/AcyclicPreservesHomology.lean`.

## References

* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry.Scheme.SmallEtaleColimits

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe v u

namespace Stacks.DerivedFunctor

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B] [EnoughInjectives A]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- **A colimit of acyclic objects is acyclic when the higher derived functors preserve it.** For a
left exact functor `F` and a colimit cocone `c` over a diagram `K` of `F`-acyclic objects, if every
`RᵖF`, `p > 0`, preserves the colimit of `K`, then `c.pt` is `F`-acyclic: `RᵖF(c.pt)` is the
colimit of the zero objects `RᵖF(K j)`. -/
theorem rightAcyclic_of_isColimit (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    {J : Type*} [Category* J] {K : J ⥤ A} {c : Cocone K} (hc : IsColimit c)
    (hpres : ∀ p : ℕ, 0 < p → PreservesColimit K (F.rightDerived p))
    (hK : ∀ j, F.rightAcyclic (K.obj j)) :
    F.rightAcyclic c.pt := by
  rw [rightAcyclic_iff_isZero_rightDerived]
  intro p hp
  have := hpres p hp
  exact (isColimitOfPreserves (F.rightDerived p) hc).isZero_pt
    (Functor.isZero _ fun j ↦ (rightAcyclic_iff_isZero_rightDerived F (K.obj j)).1 (hK j) p hp)

end Stacks.DerivedFunctor

namespace Stacks.EtaleCohomology

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

/-! ### Global sections on a quasi-compact quasi-separated scheme -/

section GlobalSections

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]

/-- **Global sections on a quasi-compact quasi-separated scheme commute with filtered colimits** of
abelian étale sheaves: the degree-zero case of Stacks 03Q5. -/
theorem preservesColimitsOfShape_Γ_smallEtale (I : Type (max (u + 1) v)) [SmallCategory I]
    [IsFiltered I] :
    PreservesColimitsOfShape I (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  have := preservesColimitsOfShape_rightDerived_Γ_smallEtale.{v} X 0 I
  preservesColimitsOfShape_of_natIso (Functor.rightDerivedZeroIsoSelf _)

/-- **A filtered colimit of `Γ(X, -)`-acyclic abelian sheaves on a quasi-compact quasi-separated
scheme is `Γ(X, -)`-acyclic**, cohomology commuting with filtered colimits (Stacks 03Q5). -/
theorem rightAcyclic_Γ_colimit_smallEtale {I : Type (max (u + 1) v)} [SmallCategory I]
    [IsFiltered I] (F : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : ∀ i, (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightAcyclic
      (F.obj i)) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightAcyclic (colimit F) :=
  Stacks.DerivedFunctor.rightAcyclic_of_isColimit _ (colimit.isColimit F)
    (fun p _ ↦ have := preservesColimitsOfShape_rightDerived_Γ_smallEtale.{v} X p I
      inferInstance) hF

/-- **A direct sum of `Γ(X, -)`-acyclic abelian sheaves on a quasi-compact quasi-separated scheme
is `Γ(X, -)`-acyclic**, cohomology commuting with direct sums. -/
theorem rightAcyclic_Γ_sigma_smallEtale {α : Type (max (u + 1) v)}
    (F : α → Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : ∀ a, (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightAcyclic (F a)) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightAcyclic (∐ F) :=
  Stacks.DerivedFunctor.rightAcyclic_of_isColimit _ (coproductIsCoproduct F)
    (fun p _ ↦ have := preservesColimitsOfShape_discrete_rightDerived_Γ_smallEtale.{v} X p α
      inferInstance) fun j ↦ hF j.as

end GlobalSections

/-! ### Direct image along a quasi-compact quasi-separated morphism -/

section DirectImage

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- **The direct image along a quasi-compact quasi-separated morphism commutes with filtered
colimits** of abelian étale sheaves: the degree-zero case of
`Stacks.EtaleCohomology.preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage`. -/
theorem preservesColimitsOfShape_etaleAbelianDirectImage (I : Type (max (u + 1) v))
    [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I (etaleAbelianDirectImage.{u, v} f) :=
  have := preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage.{v} f 0 I
  preservesColimitsOfShape_of_natIso (Functor.rightDerivedZeroIsoSelf _)

/-- **A filtered colimit of `f_*`-acyclic abelian sheaves is `f_*`-acyclic**, for `f`
quasi-compact and quasi-separated: higher direct images commute with filtered colimits. -/
theorem rightAcyclic_etaleAbelianDirectImage_colimit {I : Type (max (u + 1) v)}
    [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : ∀ i, (etaleAbelianDirectImage.{u, v} f).rightAcyclic (F.obj i)) :
    (etaleAbelianDirectImage.{u, v} f).rightAcyclic (colimit F) :=
  Stacks.DerivedFunctor.rightAcyclic_of_isColimit _ (colimit.isColimit F)
    (fun p _ ↦ have := preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage.{v} f p I
      inferInstance) hF

/-- **A direct sum of `f_*`-acyclic abelian sheaves is `f_*`-acyclic**, for `f` quasi-compact and
quasi-separated: higher direct images commute with direct sums. -/
theorem rightAcyclic_etaleAbelianDirectImage_sigma {α : Type (max (u + 1) v)}
    (F : α → Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : ∀ a, (etaleAbelianDirectImage.{u, v} f).rightAcyclic (F a)) :
    (etaleAbelianDirectImage.{u, v} f).rightAcyclic (∐ F) :=
  Stacks.DerivedFunctor.rightAcyclic_of_isColimit _ (coproductIsCoproduct F)
    (fun p _ ↦
      have := preservesColimitsOfShape_discrete_rightDerived_etaleAbelianDirectImage.{v} f p α
      inferInstance) fun j ↦ hF j.as

end DirectImage

/-! ### Direct image to a separably closed point -/

section SeparablyClosedField

variable {X' : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (f' : X' ⟶ Spec (.of Ω))

/-- **Global sections of a higher direct image to a separably closed point are cohomology
upstairs.** For `f' : X' ⟶ Spec Ω`, `Ω` separably closed, `Γ(Spec Ω, Rⁿf'_* M) ≅ Hⁿ(X', M)`
naturally in `M`: `Γ(Spec Ω, -)` is exact, so it passes through the right derived functor, and
`Γ(Spec Ω, f'_* -)` is `Γ(X', -)`. -/
def rightDerivedEtaleAbelianDirectImageCompΓIso (n : ℕ) :
    (etaleAbelianDirectImage.{u, v} f').rightDerived n ⋙
        Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ≅
      (Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived n :=
  (Functor.rightDerivedCompIso _ _ n).symm ≪≫
    Functor.rightDerivedIsoOfNatIso (etaleAbelianDirectImageCompGlobalSectionsIsoUniv.{u, v} f') n

/-- **Over a separably closed field, `f'_*`-acyclicity is `Γ(X', -)`-acyclicity.** For
`f' : X' ⟶ Spec Ω`, `Ω` separably closed, an abelian sheaf `M` on `X'_étale` is acyclic for `f'_*`
if and only if it is acyclic for `Γ(X', -)`: `Γ(Spec Ω, Rⁿf'_* M) ≅ Hⁿ(X', M)`, and
`Γ(Spec Ω, -)` is an equivalence, so it detects zero objects. -/
theorem rightAcyclic_etaleAbelianDirectImage_iff_of_isSepClosed
    (M : Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianDirectImage.{u, v} f').rightAcyclic M ↔
      (Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightAcyclic M := by
  have := isEquivalence_globalSections_of_isSepClosed Ω AddCommGrpCat.{max (u + 1) v}
  rw [rightAcyclic_iff_isZero_rightDerived, rightAcyclic_iff_isZero_rightDerived]
  refine forall₂_congr fun p _ ↦ ?_
  rw [← ((rightDerivedEtaleAbelianDirectImageCompΓIso.{v} f' p).app M).isZero_iff]
  exact ⟨fun h ↦ Functor.map_isZero
      (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) h,
    fun h ↦ IsZero.of_full_of_faithful_of_isZero
      (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) _ h⟩

end SeparablyClosedField

end Stacks.EtaleCohomology

end
