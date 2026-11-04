module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianEnlargement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianEnlargementAtTheUnion
public import StacksFrontier.Homology.DerivedCategory.SubcomplexEnlargementTransport

/-!
# The one-step enlargement rule repairing base change at a single morphism

Let `C` be a category, regarded as a site with the chaotic topology, let `O` be a presheaf of
rings on `C`, and fix a morphism `a : V ⟶ U` of `Cᵒᵖ` whose two section rings are commutative.
The enlargement claim behind conclusion (1) of Stacks 0GYZ asks that a small subcomplex of a
complex `F^•` of `O`-modules be enlarged, in countably many stages, to one at which the
base-change condition of Stacks 0GYV holds. This file produces the rule governing one stage at
the morphism `a`.

The rule is a cardinal `κ` together with, for every complex `F^•` whose image in `D(O)` is
cartesian at `a`, an assignment to each subcomplex `G^• ⊆ F^•` of a family `Ms` of sections of
`F^•` over `V` and a family `Ns` of sections of `F^•` over `U`, each of size at most
`max κ |G^•|`, with the following property: if `G_0^• ⊆ G_1^• ⊆ ⋯ ⊆ F^•` is a chain in which
every `G_{n+1}^•` contains the sections prescribed for `G_n^•`, and `H^•` is its union, then the
base-change condition at `a` holds for `H^•` as well.

The rule is defined for every map `g : G^• ⟶ F^•`; when `g` is not a monomorphism the two
families are empty and the conclusion is vacuous.

Commutativity of the two section rings is not a hypothesis beyond those of the source: extension
of scalars `M ↦ M ⊗_{O(V)} O(U)` requires a commutative `O(V)`, so there is no base change along a
restriction map of `O` without it.

## Main results

* `exists_sections_rule_isIso_comparison_at_union`: a single cardinal and a rule assigning to
  each subcomplex of a cartesian complex two small families of sections, whose repeated
  absorption forces the union of the resulting chain to be cartesian at `a`.

## References

* [Stacks Project, Tag 0GYZ](https://stacks.math.columbia.edu/tag/0GYZ)
* [Stacks Project, Tag 0GYI](https://stacks.math.columbia.edu/tag/0GYI)
* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModulesOnACategory.CartesianObjects (commRingOfComm)
open Stacks.ModulesOnACategory.QuasiCoherentCohomology (sectionsBaseChange)
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe w u v r

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ RingCat.{r}}

/-- The sections of the ranges of a family of maps are no more numerous than the source. -/
private theorem mk_sigma_range_le {ι : Type*} {α β : ι → Type v} (f : ∀ i, α i → β i) :
    Cardinal.mk (Σ i, {x // x ∈ Set.range (f i)}) ≤ Cardinal.mk (Σ i, α i) := by
  rw [Cardinal.mk_sigma, Cardinal.mk_sigma]
  exact Cardinal.sum_le_sum _ _ fun i => Cardinal.mk_range_le

/-- **A rule of small families of sections whose absorption repairs base change at a morphism.**
Let `a : V ⟶ U` in `Cᵒᵖ`, with `O(V)` and `O(U)` commutative. There is a cardinal `κ` such that
every complex `F^•` of `O`-modules whose image in `D(O)` satisfies the base-change condition of
Stacks 0GYV at `a` carries an assignment, to each map `g : G^• ⟶ F^•`, of a family `Ms G g` of
sections of `F^•` over `V` and a family `Ns G g` of sections of `F^•` over `U`, each of
cardinality at most `max κ |G^•|`, with this property: if `H^•` is the union of a chain
`G_0^• ⊆ G_1^• ⊆ ⋯ ⊆ F^•` of subcomplexes in which `G_{n+1}^•` contains every section prescribed
for `G_n^•`, then `H^•` again satisfies the base-change condition at `a`. -/
public theorem exists_sections_rule_isIso_comparison_at_union
    (bc : BaseChangeData.{w} O) {U V : Cᵒᵖ} (a : V ⟶ U)
    (hV : ∀ x y : O.obj V, x * y = y * x) (hU : ∀ x y : O.obj U, x * y = y * x) :
    ∃ κ : Cardinal.{max u v r w},
      ∀ F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ,
        IsIso (comparison.{w} bc a (DerivedCategory.Q.obj F)) →
        ∃ (Ms : ∀ G : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ, (G ⟶ F) →
            ∀ j : ℤ, Set ((F.X j).obj V))
          (Ns : ∀ G : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ, (G ⟶ F) →
            ∀ j : ℤ, Set ((F.X j).obj U)),
          (∀ G g, Cardinal.mk (Σ i : ℤ, {x // x ∈ Ms G g i}) ≤
              max κ (complexSectionSize.{w} O G)) ∧
            (∀ G g, Cardinal.mk (Σ i : ℤ, {x // x ∈ Ns G g i}) ≤
              max κ (complexSectionSize.{w} O G)) ∧
            ∀ (H : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (h : H ⟶ F)
              (G : ℕ → CochainComplex (PresheafOfModules.{max u v r w} O) ℤ)
              (γ : ∀ n, G n ⟶ F) (p : ∀ n, G n ⟶ G (n + 1)) (k : ∀ n, G n ⟶ H),
              Mono h → (∀ n, Mono (γ n)) → (∀ n, p n ≫ γ (n + 1) = γ n) →
              (∀ n, k n ≫ h = γ n) →
              (∀ (i : ℤ) (X : Cᵒᵖ) (x : (H.X i).obj X),
                ∃ (n : ℕ) (y : ((G n).X i).obj X), ((k n).f i).app X y = x) →
              (∀ (n : ℕ) (i : ℤ) (x : (F.X i).obj V), x ∈ Ms (G n) (γ n) i →
                ∃ y : ((G (n + 1)).X i).obj V, ((γ (n + 1)).f i).app V y = x) →
              (∀ (n : ℕ) (i : ℤ) (x : (F.X i).obj U), x ∈ Ns (G n) (γ n) i →
                ∃ y : ((G (n + 1)).X i).obj U, ((γ (n + 1)).f i).app U y = x) →
              IsIso (comparison.{w} bc a (DerivedCategory.Q.obj H)) := by
  let := commRingOfComm (O.obj V) hV
  let := commRingOfComm (O.obj U) hU
  have : (ModuleCat.extendScalars.{r, r, max u v r w} (O.map a).hom).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max u v w, r, r} (O.map a).hom).isLeftAdjoint
  have : (ModuleCat.extendScalars.{r, r, max u v r w} (O.map a).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max u v w, r, r} (O.map a).hom).left_adjoint_additive
  let D := totalDerivedExtensionScalars.{r, r, max u v r w} (O.map a).hom
  let T : DerivedCategory (ModuleCat.{max u v r w} (O.obj V)) ⥤
      DerivedCategory (ModuleCat.{max u v r w} (O.obj U)) := D.functor
  let α : DerivedCategory.Q ⋙ T ⟶
      (ModuleCat.extendScalars.{r, r, max u v r w} (O.map a).hom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D.comparison
  have : T.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{max u v r w} (O.obj V)) (ComplexShape.up ℤ)) :=
    D.isLeftDerived
  let bSec : ∀ P : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ,
      ((ModuleCat.extendScalars.{r, r, max u v r w} (O.map a).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((sectionsComplexFunctor.{w} O V).obj P) ⟶
        (sectionsComplexFunctor.{w} O U).obj P :=
    fun P => (NatTrans.mapHomologicalComplex
      (sectionsBaseChange.{w} O a
        (ModuleCat.extendRestrictScalarsAdj.{max u v w, r, r} (O.map a).hom))
      (ComplexShape.up ℤ)).app P
  have hnat {P Q : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ} (g : P ⟶ Q) :=
    (NatTrans.mapHomologicalComplex
      (sectionsBaseChange.{w} O a
        (ModuleCat.extendRestrictScalarsAdj.{max u v w, r, r} (O.map a).hom))
      (ComplexShape.up ℤ)).naturality g
  obtain ⟨κ₀, hκ₀⟩ :=
    Stacks.SubcomplexEnlargement.exists_enlargements_stagewise_elementwise.{r, r, max u v r w}
      (O.map a).hom
  refine ⟨max Cardinal.aleph0 (Cardinal.lift.{max u v r w} κ₀), ?_⟩
  intro F hF
  have hFiso : IsIso (α.app ((sectionsComplexFunctor.{w} O V).obj F) ≫
      DerivedCategory.Q.map (bSec F)) :=
    (CartesianObjects.isIso_comparison_Q_iff_isLeftDerived.{w} O a hV hU T α bc F).1 hF
  have key : ∀ (G : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (g : G ⟶ F),
      ∃ (Ms : ∀ j : ℤ, Set ((F.X j).obj V)) (Ns : ∀ j : ℤ, Set ((F.X j).obj U)),
        Cardinal.mk (Σ i : ℤ, {x // x ∈ Ms i}) ≤
            max (max Cardinal.aleph0 (Cardinal.lift.{max u v r w} κ₀))
              (complexSectionSize.{w} O G) ∧
          Cardinal.mk (Σ i : ℤ, {x // x ∈ Ns i}) ≤
            max (max Cardinal.aleph0 (Cardinal.lift.{max u v r w} κ₀))
              (complexSectionSize.{w} O G) ∧
          (Mono g → ∀ (G' : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (g' : G' ⟶ F),
            Mono g' → ∀ p : G ⟶ G', p ≫ g' = g →
            (∀ (i : ℤ) (x : (F.X i).obj V), x ∈ Ms i →
              ∃ y : (G'.X i).obj V, ((g'.f i).app V) y = x) →
            (∀ (i : ℤ) (x : (F.X i).obj U), x ∈ Ns i →
              ∃ y : (G'.X i).obj U, ((g'.f i).app U) y = x) →
            (∀ (i : ℤ)
              (x : (DerivedCategory.homologyFunctor (ModuleCat.{max u v r w} (O.obj U)) i).obj
                (T.obj (DerivedCategory.Q.obj ((sectionsComplexFunctor.{w} O V).obj G)))),
              ((DerivedCategory.homologyFunctor (ModuleCat.{max u v r w} (O.obj U)) i).map
                  (α.app ((sectionsComplexFunctor.{w} O V).obj G) ≫
                    DerivedCategory.Q.map (bSec G))) x = 0 →
                ((DerivedCategory.homologyFunctor (ModuleCat.{max u v r w} (O.obj U)) i).map
                  (T.map (DerivedCategory.Q.map ((sectionsComplexFunctor.{w} O V).map p))))
                    x = 0) ∧
            (∀ (i : ℤ)
              (y : (DerivedCategory.homologyFunctor (ModuleCat.{max u v r w} (O.obj U)) i).obj
                (DerivedCategory.Q.obj ((sectionsComplexFunctor.{w} O U).obj G))),
              ∃ x : (DerivedCategory.homologyFunctor (ModuleCat.{max u v r w} (O.obj U)) i).obj
                (T.obj (DerivedCategory.Q.obj ((sectionsComplexFunctor.{w} O V).obj G'))),
                ((DerivedCategory.homologyFunctor (ModuleCat.{max u v r w} (O.obj U)) i).map
                    (α.app ((sectionsComplexFunctor.{w} O V).obj G') ≫
                      DerivedCategory.Q.map (bSec G'))) x =
                  ((DerivedCategory.homologyFunctor (ModuleCat.{max u v r w} (O.obj U)) i).map
                    (DerivedCategory.Q.map ((sectionsComplexFunctor.{w} O U).map p))) y)) := by
    intro G g
    by_cases hg : Mono g
    · have := mono_sectionsComplexFunctor_map.{w} g V
      have := mono_sectionsComplexFunctor_map.{w} g U
      obtain ⟨M₂, N₂, m₂, n₂, hsize, hmain⟩ :=
        hκ₀ T α ((sectionsComplexFunctor.{w} O V).obj F)
          ((sectionsComplexFunctor.{w} O U).obj F) (bSec F) hFiso
          ((sectionsComplexFunctor.{w} O V).obj G) ((sectionsComplexFunctor.{w} O U).obj G)
          ((sectionsComplexFunctor.{w} O V).map g) ((sectionsComplexFunctor.{w} O U).map g)
          (bSec G)
          (hnat g)
      have hG (W : Cᵒᵖ) : Cardinal.mk (Σ i : ℤ,
            (((sectionsComplexFunctor.{w} O W).obj G).X i : Type (max u v r w))) ≤
          complexSectionSize.{w} O G := by
        unfold complexSectionSize
        rw [Cardinal.mk_sigma, Cardinal.mk_sigma]
        refine Cardinal.sum_le_sum _ _ fun i => Cardinal.mk_le_of_injective
          (f := fun x => (⟨W.unop, x⟩ :
            Σ W : C, ((G.X i).obj (op W) : Type (max u v r w)))) fun x y hxy => ?_
        injection hxy
      have hsum : Cardinal.mk
            ((Σ i : ℤ, (((sectionsComplexFunctor.{w} O V).obj G).X i : Type (max u v r w)))
              ⊕ (Σ i : ℤ,
                (((sectionsComplexFunctor.{w} O U).obj G).X i : Type (max u v r w)))) ≤
          max Cardinal.aleph0 (complexSectionSize.{w} O G) := by
        rw [← Cardinal.add_def]
        refine (Cardinal.add_le_max _ _).trans ?_
        exact max_le (max_le (le_max_of_le_right (hG V)) (le_max_of_le_right (hG U)))
          (le_max_left _ _)
      have hfin : ∀ c : Cardinal.{max u v r w},
          c ≤ max (Cardinal.lift.{max u v r w} κ₀) (Cardinal.mk
            ((Σ i : ℤ, (((sectionsComplexFunctor.{w} O V).obj G).X i : Type (max u v r w)))
              ⊕ (Σ i : ℤ,
                (((sectionsComplexFunctor.{w} O U).obj G).X i : Type (max u v r w))))) →
          c ≤ max (max Cardinal.aleph0 (Cardinal.lift.{max u v r w} κ₀))
            (complexSectionSize.{w} O G) := fun c hc =>
        hc.trans (max_le (le_max_of_le_left (le_max_right _ _))
          (hsum.trans (max_le (le_max_of_le_left (le_max_left _ _)) (le_max_right _ _))))
      refine ⟨fun i => Set.range (m₂.f i), fun i => Set.range (n₂.f i), ?_, ?_, ?_⟩
      · exact hfin _ (((mk_sigma_range_le fun i => m₂.f i).trans
          (Cardinal.mk_le_of_injective Sum.inl_injective)).trans hsize)
      · exact hfin _ (((mk_sigma_range_le fun i => n₂.f i).trans
          (Cardinal.mk_le_of_injective Sum.inr_injective)).trans hsize)
      · intro _ G' g' hg' p hpg hMsG hNsG
        have := mono_sectionsComplexFunctor_map.{w} g' V
        have := mono_sectionsComplexFunctor_map.{w} g' U
        refine hmain ((sectionsComplexFunctor.{w} O V).obj G')
          ((sectionsComplexFunctor.{w} O U).obj G')
          ((sectionsComplexFunctor.{w} O V).map g') ((sectionsComplexFunctor.{w} O U).map g')
          inferInstance inferInstance
          ((sectionsComplexFunctor.{w} O V).map p) ((sectionsComplexFunctor.{w} O U).map p)
          (bSec G') ?_ ?_
          (hnat g')
          (fun i x hx => hMsG i x hx) (fun i x hx => hNsG i x hx)
        all_goals rw [← Functor.map_comp, hpg]
    · refine ⟨fun _ => ∅, fun _ => ∅, ?_, ?_, fun hgm => absurd hgm hg⟩
      all_goals simp
  choose Ms Ns hMs hNs hkey using key
  refine ⟨Ms, Ns, hMs, hNs, ?_⟩
  intro H h G γ p k hmono hγ hp hk hexh hcontM hcontN
  refine (CartesianObjects.isIso_comparison_Q_iff_isLeftDerived.{w} O a hV hU T α bc H).2 ?_
  exact isIso_sectionsBaseChange_at_union.{w} a hV hU T α h γ p k hmono hγ hp hk hexh
    (fun n => (hkey (G n) (γ n) (hγ n) (G (n + 1)) (γ (n + 1)) (hγ (n + 1)) (p n) (hp n)
      (hcontM n) (hcontN n)).1)
    (fun n => (hkey (G n) (γ n) (hγ n) (G (n + 1)) (γ (n + 1)) (hγ (n + 1)) (p n) (hp n)
      (hcontM n) (hcontN n)).2)

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence

end
