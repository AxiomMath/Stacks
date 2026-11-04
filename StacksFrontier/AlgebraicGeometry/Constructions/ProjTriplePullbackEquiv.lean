module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleFunctorLaws
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleSectionsSetoid

/-!
# The pullback of a triple respects strict equivalence

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `j : Y' ⟶ Y` a morphism of schemes and `d ≥ 1`. The
pullback `Stacks.AlgebraicGeometry.ProjTriplePullback.pullbackSections` of weight-`d` graded maps
`ψ : A^{(d)} ⟶ Γ_*(Y, L)` to graded maps into `Γ_*(Y', j^*L)` carries strictly equivalent maps to
strictly equivalent maps, so it descends to the set `F_d(Y)` of [Stacks, Tag 01N4]. The key input
is that the comparison `(j^*L) ^⊗ n ≅ j^*(L ^⊗ n)` of
`Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso` is natural in the
invertible module.

## Main results

* `Stacks.AlgebraicGeometry.ProjTriplePullbackEquiv.pullbackNatTensorPowIso_inv_naturality`: the
  comparison of the tensor powers is natural in the invertible module.
* `Stacks.AlgebraicGeometry.ProjTriplePullbackEquiv.pullSection_natTensorPowCongr`: the same on
  sections — pulling back the image of a global section of `L ^⊗ n` under the `n`-th tensor power
  of `β : L ≅ L'` is the image of its pullback under the `n`-th tensor power of `j^*β`.
* `Stacks.AlgebraicGeometry.ProjTriplePullbackEquiv.sectionsEquiv_pullbackSections`: the pullback
  of a weight-`d` graded map respects strict equivalence.

## Implementation notes

The naturality statement is written with the inverse of the comparison on both sides, the
direction in which `Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection` composes it and in
which `Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullbackNatTensorPowIso_inv_succ` is
stated.

The two arms of the recursion for the tensor powers of an isomorphism are used as the named
equations `Stacks.AmplePullbackPart1.natTensorPowCongr_zero` and `natTensorPowCongr_succ` rather
than by `show`: the two spellings are definitionally equal but not syntactically so, and a goal in
which the reduction has been performed is not type-correct at the transparency `rw` checks its
motive at. For the same reason the induction step `step_aux` is stated with every object a
variable.

The monoidal structure on `Y.Modules` is available only through the local instances of
`Stacks.SheafInternalHom`, reintroduced below with `attribute [local instance]`.

## References

* [Stacks Project, Tag 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjChartFromRatios (VeroneseSections)
open Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator (pullbackCotensorator
  pullbackCotensorator_tensorHom pullbackNatTensorPowIso_inv_succ)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection pullbackNatTensorPowIso
  top_le_preimage_top)
open Stacks.AlgebraicGeometry.ProjChartSectionPullback (pullbackNatTensorPowIso_inv_zero)
open Stacks.AlgebraicGeometry.ProjTripleClassifying (SectionsEquiv)
open Stacks.AlgebraicGeometry.ProjTriplePullback (pullbackSections)
open Stacks.AmplePullbackPart1 (natTensorPowCongr natTensorPowCongr_zero natTensorPowCongr_succ)
open Stacks.PullbackUnitSection (unitPullbackHom)
open Stacks.Ample (IsInvertibleModule)
open Stacks.TensorPowers (natTensorPow)

universe v u w

namespace Stacks.AlgebraicGeometry.ProjTriplePullbackEquiv

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### Naturality of the comparison of the tensor powers -/

section Naturality

/-- In a monoidal category, two comparisons `δ`, `δ'` of a tensor product with the tensor product
of the comparisons, a morphism `m` compatible with them, and an identity `pa ≫ dn' = dn ≫ cn` in
the first factor give the same identity one tensor factor further. -/
private theorem step_aux {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {X X' A A' B B' E E' : C} (m : X ⟶ X') (δ : X ⟶ A ⊗ B) (δ' : X' ⟶ A' ⊗ B')
    (pa : A ⟶ A') (pb : B ⟶ B') (dn : A ⟶ E) (dn' : A' ⟶ E') (cn : E ⟶ E')
    (hδ : m ≫ δ' = δ ≫ (pa ⊗ₘ pb)) (hih : pa ≫ dn' = dn ≫ cn) :
    m ≫ δ' ≫ (dn' ▷ B') = (δ ≫ (dn ▷ B)) ≫ (cn ⊗ₘ pb) := by
  rw [← Category.assoc, hδ, Category.assoc, Category.assoc,
    ← MonoidalCategory.tensorHom_id, ← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.comp_id, Category.id_comp, hih]

variable {Y Y' : Scheme.{u}} (j : Y' ⟶ Y) {L L' : Y.Modules} [IsInvertibleModule Y L]
  [IsInvertibleModule Y L']

/-- The comparison `(j^*L) ^⊗ n ≅ j^*(L ^⊗ n)` is natural in the invertible module. -/
theorem pullbackNatTensorPowIso_inv_naturality (β : L ≅ L') : ∀ n : ℕ,
    (Scheme.Modules.pullback j).map (natTensorPowCongr β n).hom ≫
        (pullbackNatTensorPowIso j L' n).inv =
      (pullbackNatTensorPowIso j L n).inv ≫
        (natTensorPowCongr ((Scheme.Modules.pullback j).mapIso β) n).hom
  | 0 => by
      have h0 : (Scheme.Modules.pullback j).map (natTensorPowCongr β 0).hom =
          𝟙 ((Scheme.Modules.pullback j).obj (natTensorPow L 0)) :=
        (congrArg (Scheme.Modules.pullback j).map
            (congrArg Iso.hom (natTensorPowCongr_zero β))).trans
          ((Scheme.Modules.pullback j).map_id _)
      have h1 : (natTensorPowCongr ((Scheme.Modules.pullback j).mapIso β) 0).hom =
          𝟙 (natTensorPow ((Scheme.Modules.pullback j).obj L) 0) :=
        congrArg Iso.hom (natTensorPowCongr_zero _)
      have hl : (Scheme.Modules.pullback j).map (natTensorPowCongr β 0).hom ≫
          (pullbackNatTensorPowIso j L' 0).inv = unitPullbackHom j :=
        (congrArg (fun φ => φ ≫ (pullbackNatTensorPowIso j L' 0).inv) h0).trans
          ((Category.id_comp _).trans (pullbackNatTensorPowIso_inv_zero j L'))
      have hr : (pullbackNatTensorPowIso j L 0).inv ≫
          (natTensorPowCongr ((Scheme.Modules.pullback j).mapIso β) 0).hom =
            unitPullbackHom j :=
        (congrArg (fun φ => (pullbackNatTensorPowIso j L 0).inv ≫ φ) h1).trans
          ((Category.comp_id _).trans (pullbackNatTensorPowIso_inv_zero j L))
      exact hl.trans hr.symm
  | n + 1 => by
      rw [pullbackNatTensorPowIso_inv_succ, pullbackNatTensorPowIso_inv_succ]
      exact step_aux ((Scheme.Modules.pullback j).map (natTensorPowCongr β (n + 1)).hom)
        (pullbackCotensorator j (natTensorPow L n) L)
        (pullbackCotensorator j (natTensorPow L' n) L')
        ((Scheme.Modules.pullback j).map (natTensorPowCongr β n).hom)
        ((Scheme.Modules.pullback j).map β.hom) (pullbackNatTensorPowIso j L n).inv
        (pullbackNatTensorPowIso j L' n).inv
        (natTensorPowCongr ((Scheme.Modules.pullback j).mapIso β) n).hom
        (pullbackCotensorator_tensorHom j (natTensorPowCongr β n).hom β.hom)
        (pullbackNatTensorPowIso_inv_naturality β n)

/-- Pulling back the image of a global section of `L ^⊗ n` under the `n`-th tensor power of `β` is
the image of its pullback under the `n`-th tensor power of `j^*β`. -/
theorem pullSection_natTensorPowCongr (β : L ≅ L') (n : ℕ) (x : Γ(natTensorPow L n, ⊤)) :
    pullSection j L' n ((natTensorPowCongr β n).hom.app ⊤ x) =
      (natTensorPowCongr ((Scheme.Modules.pullback j).mapIso β) n).hom.app ⊤
        (pullSection j L n x) := by
  have hnat := congrArg
    (fun φ : (Scheme.Modules.pullback j).obj (natTensorPow L n) ⟶
        natTensorPow ((Scheme.Modules.pullback j).obj L') n =>
      φ.app ⊤ (AlgebraicGeometry.pullbackSectionHom j (natTensorPow L n) ⊤ ⊤
        (top_le_preimage_top j) x))
    (pullbackNatTensorPowIso_inv_naturality j β n)
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply] at hnat
  have hsec : AlgebraicGeometry.pullbackSectionHom j (natTensorPow L' n) ⊤ ⊤
        (top_le_preimage_top j) ((natTensorPowCongr β n).hom.app ⊤ x) =
      ((Scheme.Modules.pullback j).map (natTensorPowCongr β n).hom).app ⊤
        (AlgebraicGeometry.pullbackSectionHom j (natTensorPow L n) ⊤ ⊤
          (top_le_preimage_top j) x) :=
    (Scheme.Modules.pullbackSection_naturality j (natTensorPowCongr β n).hom ⊤ ⊤
      (top_le_preimage_top j) x).symm
  rw [pullSection, pullSection, hsec]
  exact hnat

end Naturality

/-! ### The pullback respects strict equivalence -/

section Pullback

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

variable {Y Y' : Scheme.{u}} {d : ℕ} {L L' : Y.Modules} [IsInvertibleModule Y L]
  [IsInvertibleModule Y L']

/-- If `ψ` and `ψ'` are strictly equivalent weight-`d` graded maps, so are their pullbacks along
`j : Y' ⟶ Y`, the comparing isomorphism being the inverse image of the given one. -/
theorem sectionsEquiv_pullbackSections {ψ : VeroneseSections 𝒜 d L}
    {ψ' : VeroneseSections 𝒜 d L'} (j : Y' ⟶ Y) (h : SectionsEquiv 𝒜 ψ ψ') :
    SectionsEquiv 𝒜 (pullbackSections 𝒜 ψ j) (pullbackSections 𝒜 ψ' j) := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨(Scheme.Modules.pullback j).mapIso β, fun n x => ?_⟩
  rw [show (pullbackSections 𝒜 ψ j).toFun n x = pullSection j L n (ψ.toFun n x) from rfl,
    show (pullbackSections 𝒜 ψ' j).toFun n x = pullSection j L' n (ψ'.toFun n x) from rfl,
    ← hβ n x, pullSection_natTensorPowCongr]

end Pullback

end Stacks.AlgebraicGeometry.ProjTriplePullbackEquiv

end
