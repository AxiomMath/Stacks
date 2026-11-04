module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonEmbedding
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonSituationData
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiDerivedUnit
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaves pulled back from the space form a weak Serre subcategory

Situation 0EZ3 asks, as part of its data, for a weak Serre subcategory
`A'_X ⊆ Ab(C_{τ'}/X)` over every object `X` of the site. Stacks 0EZI makes the choice
`A'_X = {π_X^{-1}F : F ∈ Ab(X)}` for the comparison `ε : LC_qc → LC_Zar`, and its proof opens by
checking that this choice really is a weak Serre subcategory, by the four conditions of
Homology, Lemma 0754. This file carries out that check.

The argument of the source is entirely formal in the adjunction `π_X^{-1} ⊣ π_{X,*}`, so it is
done here once and abstractly, as `CategoryTheory.ObjectProperty.isWeakSerreClass_map_top`: the
essential image of a fully faithful exact left adjoint whose right adjoint is also exact is a
weak Serre class. Both halves of the source's argument appear there. Conditions (1), (2) and (3)
of 0754 hold because `π_X^{-1}` is exact and fully faithful, so a kernel or cokernel of a map
between objects of the class is the image of the corresponding kernel or cokernel downstairs; and
the extension condition holds because `π_{X,*}` is exact, so applying it to a short exact sequence
`0 → π_X^{-1}F → G → π_X^{-1}F' → 0` gives a short exact sequence `0 → F → π_{X,*}G → F' → 0`
downstairs, whose image under `π_X^{-1}` maps to the original by the counit. The counit is
invertible at the four outer terms, hence at `G` by the five lemma, which exhibits `G` as
`π_X^{-1}π_{X,*}G`.

## Main results

* `CategoryTheory.ObjectProperty.isWeakSerreClass_map_top`: the essential image of a fully
  faithful exact functor with an exact right adjoint is a weak Serre class.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiPullbackClass_isWeakSerreClass`:
  the sheaves pulled back from the space are a weak Serre subcategory of the abelian sheaves on
  the localized Zariski site, which is the standing requirement Situation 0EZ3 places on the
  class `A'_X` chosen by Stacks 0EZI.

## Implementation notes

The class is `ObjectProperty.map` of `⊤` along `π_X^{-1}`, that is the essential image, so it is
already closed under isomorphism and the only content is the three closure conditions. The
abstract statement is therefore about `(⊤ : ObjectProperty C).map L` rather than about
`L.essImage`; `CategoryTheory.Adjunction.isIso_counit_app_iff_mem_essImage` identifies the two.

The five lemma is applied in the shape
`CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`, to the morphism of five term exact
sequences whose components are the components of the counit. The five term sequences are assembled
from their three inner short complexes by `exact_mk₄`.

## References

* [Stacks Project, Tag 0EZI](https://stacks.math.columbia.edu/tag/0EZI)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace CategoryTheory.ObjectProperty

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- A five term sequence is exact as a `CategoryTheory.ComposableArrows` as soon as it is exact
at each of its three inner objects. -/
private theorem exact_mk₄ {X₀ X₁ X₂ X₃ X₄ : D}
    {f₀ : X₀ ⟶ X₁} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃} {f₃ : X₃ ⟶ X₄}
    (w₀ : f₀ ≫ f₁ = 0) (w₁ : f₁ ≫ f₂ = 0) (w₂ : f₂ ≫ f₃ = 0)
    (e₀ : (ShortComplex.mk f₀ f₁ w₀).Exact) (e₁ : (ShortComplex.mk f₁ f₂ w₁).Exact)
    (e₂ : (ShortComplex.mk f₂ f₃ w₂).Exact) :
    (ComposableArrows.mk₄ f₀ f₁ f₂ f₃).Exact :=
  ComposableArrows.exact_of_δ₀ (ComposableArrows.exact₂_mk _ w₀ e₀)
    (ComposableArrows.exact_of_δ₀ (ComposableArrows.exact₂_mk _ w₁ e₁)
      (ComposableArrows.exact₂_mk _ w₂ e₂))

/-- A five term exact sequence is exact when reassembled from its maps by
`CategoryTheory.ComposableArrows.mk₄`. -/
private theorem exact_mk₄_self {S : ComposableArrows D 4} (hS : S.Exact) :
    (ComposableArrows.mk₄ (S.map' 0 1) (S.map' 1 2) (S.map' 2 3) (S.map' 3 4)).Exact :=
  exact_mk₄ (hS.toIsComplex.zero' 0 1 2) (hS.toIsComplex.zero' 1 2 3)
    (hS.toIsComplex.zero' 2 3 4) (hS.exact' 0 1 2) (hS.exact' 1 2 3) (hS.exact' 2 3 4)

/-- The image of a five term exact sequence under an exact additive functor is exact. -/
private theorem exact_mk₄_map {S : ComposableArrows C 4} (hS : S.Exact) (T : C ⥤ D)
    [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T] :
    (ComposableArrows.mk₄ (T.map (S.map' 0 1)) (T.map (S.map' 1 2)) (T.map (S.map' 2 3))
      (T.map (S.map' 3 4))).Exact :=
  exact_mk₄ (by rw [← T.map_comp, hS.toIsComplex.zero' 0 1 2, T.map_zero])
    (by rw [← T.map_comp, hS.toIsComplex.zero' 1 2 3, T.map_zero])
    (by rw [← T.map_comp, hS.toIsComplex.zero' 2 3 4, T.map_zero])
    ((hS.exact' 0 1 2).map T) ((hS.exact' 1 2 3).map T) ((hS.exact' 2 3 4).map T)

/-- **The essential image of a fully faithful exact left adjoint with an exact right adjoint is a
weak Serre class.**

Membership in the essential image is invertibility of the counit, so the three closure conditions
of Stacks 0754 beyond closure under isomorphism all reduce to one application of the five lemma:
a five term exact sequence whose four outer terms lie in the image is compared along the counit
with its image under `L ∘ R`, which is again exact because both functors are, and the counit is
invertible at the four outer terms. -/
theorem isWeakSerreClass_map_top {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Full] [L.Faithful] [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] :
    ((⊤ : ObjectProperty C).map L).IsWeakSerreClass := by
  have hmem (Y : D) : ((⊤ : ObjectProperty C).map L) Y ↔ IsIso (adj.counit.app Y) := by
    rw [prop_map_iff, adj.isIso_counit_app_iff_mem_essImage]
    exact ⟨fun ⟨A, _, h⟩ => ⟨A, h⟩, fun ⟨A, h⟩ => ⟨A, trivial, h⟩⟩
  refine (isWeakSerreClass_iff_prop_obj₂_of_exact _).2
    ⟨⟨L.obj 0, ⟨0, trivial, ⟨Iso.refl _⟩⟩⟩, ?_⟩
  intro S hS h₀ h₁ h₃ h₄
  rw [hmem] at h₀ h₁ h₃ h₄ ⊢
  let T : D ⥤ D := R ⋙ L
  let φ : ComposableArrows.mk₄ (T.map (S.map' 0 1)) (T.map (S.map' 1 2)) (T.map (S.map' 2 3))
        (T.map (S.map' 3 4)) ⟶
      ComposableArrows.mk₄ (S.map' 0 1) (S.map' 1 2) (S.map' 2 3) (S.map' 3 4) :=
    ComposableArrows.homMk₄ (adj.counit.app (S.obj' 0)) (adj.counit.app (S.obj' 1))
      (adj.counit.app (S.obj' 2)) (adj.counit.app (S.obj' 3)) (adj.counit.app (S.obj' 4))
      (adj.counit.naturality (S.map' 0 1)) (adj.counit.naturality (S.map' 1 2))
      (adj.counit.naturality (S.map' 2 3)) (adj.counit.naturality (S.map' 3 4))
  have hepi : Epi (adj.counit.app (S.obj' 0)) := have := h₀; inferInstance
  have hmono : Mono (adj.counit.app (S.obj' 4)) := have := h₄; inferInstance
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
    (exact_mk₄_map hS T) (exact_mk₄_self hS) φ hepi h₁ h₃ hmono

end CategoryTheory.ObjectProperty

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

/-- **Stacks 0EZI, the weak Serre condition on the class `A'_X`.** Situation 0EZ3 requires the
class it is handed over each object of the site to be a weak Serre subcategory of the abelian
sheaves on the localized coarse site. For the choice Stacks 0EZI makes — the sheaves of the form
`π_X^{-1}F` on the localized Zariski site — this holds because `π_X^{-1}` is exact and fully
faithful and `π_{X,*}` is exact, all three being parts of Stacks 0DCU. -/
@[stacks 0EZI "the class A'_X of Situation 0EZ3 is a weak Serre class"]
theorem zariskiPullbackClass_isWeakSerreClass
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    (S.zariskiPullbackClass.{u, w, v} X).IsWeakSerreClass := by
  obtain ⟨_, _⟩ := (exactFunctor_iff _).1 (S.abelianComparisonDirectImage_exact.{u, w, v} X)
  have _ : IsIso (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X).unit :=
    S.abelianComparisonAdjunction_unit_isIso.{u, w, v} X
  have hff := (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X).fullyFaithfulLOfIsIsoUnit
  have _ : (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).Full := hff.full
  have _ : (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).Faithful := hff.faithful
  have _ : (S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact ObjectProperty.isWeakSerreClass_map_top
    (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X)

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
