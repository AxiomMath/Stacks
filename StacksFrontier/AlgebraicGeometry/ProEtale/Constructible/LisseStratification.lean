module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedConstancy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuotientByIdealPowers
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuotientScalarsLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.InverseImageSectionsLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LocallyClosedStratum
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.NoetherianStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.ConstantSheafSections
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ConstructibleComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ModuleComparisonWithEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.AdicModuleSheaf
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.ConstantAdicQuotientTower
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.InverseImageLimits
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.LocallyConstantFiniteType
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.LocallyConstantValues
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.QuotientScalarsInverseImage
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.WeakSerre
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteTypeLocality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructible `Λ`-sheaves are lisse on the strata of a partition

Let `X` be a Noetherian scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal. A constructible
`Λ`-sheaf `F` on `X_proet` (Stacks 09BT (1)) is lisse on each stratum of a finite partition of
`X` into constructible locally closed subschemes (Stacks 09BU). Consequently it is adic
constructible (Stacks 09BX).

Write `Q n = F / IⁿF` and `grₙ = IⁿF / Iⁿ⁺¹F`, the kernel of `Q (n + 1) ⟶ Q n`. Each `grₙ` is
constructible (Stacks 09B5), so it comes from the étale site (Stacks 09AK). Multiplication by
generators `μ₁, …, μ_k` of `I` gives commuting maps `grₙ ⟶ grₙ₊₁` which generate every `grₙ` from
`gr₀ = F / IF`: this is the structure of a module over `⨁ Iⁿ / Iⁿ⁺¹`, a quotient of the polynomial
ring `Λ[X₁, …, X_k]`, which the source uses. By Noetherian induction it suffices to find, inside
any nonempty closed subset, a nonempty relatively open part on which all the `grₙ` are locally
constant of finite type. Inside a stratum on which `gr₀` is locally constant, the direct images of
the `grₙ` to the étale site are constant over one étale scheme with a point, uniformly in `n`
(`Stacks.ConstantSheaf.exists_constantSheaf_iso_overPullback_of_graded`); the image of an affine
open of that étale scheme is open, and over an affine open inside it all the `grₙ` are locally
constant of finite type. Finally the extensions `0 → grₙ → Q (n + 1) → Q n → 0` make every `Q n`
locally constant of finite type (Stacks 093U), and inverse image along an immersion preserves the
limit `F = lim Q n` and the quotients.

## Main results

* `AlgebraicGeometry.ProEtale.exists_constructibleStratification_forall_of_graded`: the uniform
  stratification for a graded family of étale sheaves generated in degree zero.
* `AlgebraicGeometry.ProEtale.isLisseAdicModuleSheaf_proetaleModuleInverseImage_of_forall`: the
  lisse criterion along an immersion.
* `AlgebraicGeometry.ProEtale.exists_isLisseAdicModuleSheaf_stratification`: Stacks 09BU.

## Implementation notes

The source forms the sheaf `⨁ₙ Gₙ` of modules over `⨁ₙ Iⁿ / Iⁿ⁺¹` on `X_et` and quotes the
theory of constructible sheaves of modules over a Noetherian ring for it. Here the graded module
is never formed as a sheaf: the uniformity in `n` is extracted directly from the Noetherian
property of finitely generated modules over the polynomial ring, over the objects of the small
étale site, which is the content of the cited results that the proof uses.

## References

* [Stacks Project, Tag 09BU](https://stacks.math.columbia.edu/tag/09BU)
* [Stacks Project, Tag 09BX](https://stacks.math.columbia.edu/tag/09BX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf

universe w v u

namespace AlgebraicGeometry.ProEtale

variable {Λ : Type v} [CommRing Λ]

attribute [local instance] hasSheafify_proEt_moduleCat hasSheafify_proEt_over_moduleCat
  hasSheafify_etale_moduleCat hasSheafify_etale_over_moduleCat

/-- The empty sieve does not cover an étale scheme with a point. -/
theorem _root_.AlgebraicGeometry.Scheme.bot_notMem_smallEtaleTopology {Y : Scheme.{u}} {T : Y.Etale}
    (x : T.left) :
    (⊥ : Sieve T) ∉ Y.smallEtaleTopology T := fun h => by
  obtain ⟨_, _, hg, -⟩ := Stacks.EtaleCohomology.exists_mem_range_of_mem_smallEtaleTopology ⊥ h x
  exact hg

/-- If every member of a covering family is covered by the empty sieve, so is its target. -/
theorem _root_.CategoryTheory.GrothendieckTopology.bot_mem_of_ofArrows_mem {C : Type*} [Category C]
    {J : GrothendieckTopology C} {X : C}
    {ι : Type*} {V : ι → C} {f : ∀ i, V i ⟶ X} (hf : Sieve.ofArrows V f ∈ J X)
    (h : ∀ i, (⊥ : Sieve (V i)) ∈ J (V i)) : (⊥ : Sieve X) ∈ J X := by
  refine J.transitive hf ⊥ fun Z g hg => ?_
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  rw [Sieve.pullback_bot]
  simpa using J.pullback_stable a (h i)

/-- The counit of the étale inverse image adjunction is invertible on its essential image. -/
private theorem isIso_etaleCounit_app {Y : Scheme.{u}}
    {B : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{max (u + 1) v w} Λ)}
    (hB : (Scheme.etaleInverseImage.{u, w, v} Y Λ).essImage B) :
    IsIso ((Scheme.etaleInverseImageAdjunction.{w} Y Λ).counit.app B) := by
  have hff := (Scheme.etaleInverseImageAdjunction.{w} Y Λ).fullyFaithfulLOfIsIsoUnit
  have : (Scheme.etaleInverseImage.{u, w, v} Y Λ).Full := hff.full
  have : (Scheme.etaleInverseImage.{u, w, v} Y Λ).Faithful := hff.faithful
  exact (Scheme.etaleInverseImageAdjunction.{w} Y Λ).isIso_counit_app_iff_mem_essImage.2 hB

/-- **Uniform constancy over one étale object.** Let `Y` be a scheme with a point and `B n`
sheaves on `Y_proet` coming from `Y_et`, with commuting maps `ψ j : B n ⟶ B (n + 1)` generating
each `B n` from `B 0`. If `B 0` is locally constant of finite type, there is an étale `Y`-scheme
with a point over which the direct images to `Y_et` of all the `B n` are constant with finitely
generated values. -/
theorem exists_etale_constantSheaf_iso_of_graded [IsNoetherianRing Λ] {Y : Scheme.{u}} (y : Y)
    (B : ℕ → Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{max (u + 1) v w} Λ)) {k : ℕ}
    (ψ : Fin k → ∀ n, B n ⟶ B (n + 1))
    (hψ : ∀ i j n, ψ i n ≫ ψ j (n + 1) = ψ j n ≫ ψ i (n + 1))
    (hgen : ∀ (n : ℕ) {Z : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{max (u + 1) v w} Λ)}
      (h : B n ⟶ Z), (∀ w : Fin n → Fin k, pathHom ψ w ≫ h = 0) → h = 0)
    (hB : ∀ n, (Scheme.etaleInverseImage.{u, w, v} Y Λ).essImage (B n))
    (h0 : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
      (Scheme.ProEt.topology Y) Λ (B 0)) :
    ∃ U₀ : Y.Etale, Nonempty U₀.left ∧ ∀ n, ∃ E : ModuleCat.{max (u + 1) v w} Λ,
      Module.Finite Λ E ∧
      Nonempty ((constantSheaf (Y.smallEtaleTopology.over U₀)
          (ModuleCat.{max (u + 1) v w} Λ)).obj E ≅
        (Y.smallEtaleTopology.overPullback _ U₀).obj
          ((Scheme.etaleDirectImage.{u, w, v} Y Λ).obj (B n))) := by
  classical
  let J := Y.smallEtaleTopology
  let A := ModuleCat.{max (u + 1) v w} Λ
  let adj := Scheme.etaleInverseImageAdjunction.{w} Y Λ
  have hff := adj.fullyFaithfulLOfIsIsoUnit
  have : (Scheme.etaleInverseImage.{u, w, v} Y Λ).Full := hff.full
  have : (Scheme.etaleInverseImage.{u, w, v} Y Λ).Faithful := hff.faithful
  have hc (n : ℕ) : IsIso (adj.counit.app (B n)) := isIso_etaleCounit_app (hB n)
  let C (n : ℕ) := (Scheme.etaleDirectImage.{u, w, v} Y Λ).obj (B n)
  let ψC (j : Fin k) (n : ℕ) : C n ⟶ C (n + 1) :=
    (Scheme.etaleDirectImage.{u, w, v} Y Λ).map (ψ j n)
  have hψC (i j : Fin k) (n : ℕ) : ψC i n ≫ ψC j (n + 1) = ψC j n ≫ ψC i (n + 1) := by
    simp only [ψC, ← Functor.map_comp, hψ]
  have hgenC (n : ℕ) {Z : Sheaf J A} (h : C n ⟶ Z)
      (hh : ∀ w : Fin n → Fin k, pathHom ψC w ≫ h = 0) : h = 0 := by
    have := hc 0
    have := hc n
    exact pathHom_generates_map_of_isIso_counit adj ψ (hgen n) h hh
  -- `C 0` is locally constant of finite type on the étale site
  have hC0 : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v} J Λ (C 0) := by
    have := hc 0
    rw [← isFinitePresentationLocallyConstantModuleSheaf_iff_isFiniteTypeLocallyConstantModuleSheaf]
    refine isFinitePresentationLocallyConstantModuleSheaf_of_etaleInverseImage (C 0) ?_
    refine ObjectProperty.prop_of_iso _ (asIso (adj.counit.app (B 0))).symm ?_
    rwa [isFinitePresentationLocallyConstantModuleSheaf_iff_isFiniteTypeLocallyConstantModuleSheaf]
  -- a trivializing étale `Y`-scheme with a point
  obtain ⟨I, V, f, hcov, hV⟩ := hC0 (etaleFinal Y)
  obtain ⟨i, hi⟩ : ∃ i, (⊥ : Sieve (V i)) ∉ J (V i) := by
    by_contra hcon
    push Not at hcon
    exact Scheme.bot_notMem_smallEtaleTopology (T := etaleFinal Y) y
      (GrothendieckTopology.bot_mem_of_ofArrows_mem hcov hcon)
  obtain ⟨E0, hE0, ⟨c⟩⟩ := hV i
  have : Module.Finite Λ E0 := (ModuleCat.isFG_iff E0).mp hE0
  let U := V i
  have hT₀ : (⊥ : Sieve (Over.mk (𝟙 U))) ∉ (J.over U) (Over.mk (𝟙 U)) := by
    rwa [GrothendieckTopology.mem_over_iff, map_bot]
  let L := J.overPullback A U
  let adjU := (Over.forget U).sheafAdjunctionCocontinuous A (J.over U) J
  have : ((Over.forget U).sheafPushforwardCocontinuous A (J.over U) J).IsRightAdjoint :=
    adjU.isRightAdjoint
  have : ((Over.forget U).sheafPushforwardCocontinuous A (J.over U) J).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isRightAdjoint _
  obtain ⟨U₀', hU₀', hconst⟩ :=
    exists_constantSheaf_iso_overPullback_of_graded.{max v w, u, u + 1, v}
    (B := fun n => L.obj (C n)) Over.mkIdTerminal hT₀ (fun j n => L.map (ψC j n))
    (fun i j n => by simp only [← Functor.map_comp, hψC])
    (fun n Z h hh => pathHom_generates_map adjU ψC (hgenC n) h hh) E0 c
  refine ⟨U₀'.left, ?_, fun n => ?_⟩
  · by_contra h
    apply hU₀'
    rw [GrothendieckTopology.mem_over_iff, map_bot]
    exact smallEtale_bot_mem Y (not_nonempty_iff.mp h)
  · obtain ⟨E, hE, ⟨e⟩⟩ := hconst n
    exact ⟨E, hE, ⟨constantTrivializationFromIteratedSlice J U U₀' (C n) E e⟩⟩

/-- **From constancy over one étale object to local constancy on an open.** Let `Y` be affine and
`U₀` an étale `Y`-scheme with a point, over which the direct images to the étale site of the
sheaves `B n` are all constant with finitely generated values. Then on some nonempty affine open
`O` of `Y`, the restrictions of all the `B n` are locally constant of finite type. The open is a
neighbourhood of the image of the point inside the image of an affine open of `U₀`, which is
open because étale morphisms are open; the base change of that affine open to `O` is affine and
maps onto `O`, so it covers `O` in the pro-étale topology. -/
theorem exists_opens_isFiniteTypeLocallyConstant_of_etale [IsNoetherianRing Λ] {Y : Scheme.{u}}
    [IsAffine Y] (U₀ : Y.Etale) (x : U₀.left)
    (B : ℕ → Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{max (u + 1) v w} Λ))
    (hB : ∀ n, (Scheme.etaleInverseImage.{u, w, v} Y Λ).essImage (B n))
    (hU : ∀ n, ∃ E : ModuleCat.{max (u + 1) v w} Λ, Module.Finite Λ E ∧
      Nonempty ((constantSheaf (Y.smallEtaleTopology.over U₀)
          (ModuleCat.{max (u + 1) v w} Λ)).obj E ≅
        (Y.smallEtaleTopology.overPullback _ U₀).obj
          ((Scheme.etaleDirectImage.{u, w, v} Y Λ).obj (B n)))) :
    ∃ O : Y.Opens, (O : Set Y).Nonempty ∧ ∀ n,
      IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
        (Scheme.ProEt.topology O) Λ
        ((proetaleModuleInverseImage.{u, v, w} (Scheme.Opens.ι O) Λ).obj (B n)) := by
  classical
  let J := Y.smallEtaleTopology
  let K := Scheme.ProEt.topology Y
  let A := ModuleCat.{max (u + 1) v w} Λ
  let adj := Scheme.etaleInverseImageAdjunction.{w} Y Λ
  have hc (n : ℕ) : IsIso (adj.counit.app (B n)) := isIso_etaleCounit_app (hB n)
  -- an affine open neighbourhood `W` of `x`, as an étale `Y`-scheme
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : U₀.left.Opens)) trivial
  have : IsAffine W := hW
  let Uₐ : Y.Etale := Scheme.Etale.mk ((Scheme.Opens.ι W) ≫ U₀.hom)
  let gₐ : Uₐ ⟶ U₀ := MorphismProperty.Over.homMk (Scheme.Opens.ι W) rfl
  -- its image is open; an affine open `O` inside it through the image of `x`
  let O' : Y.Opens := ⟨Set.range Uₐ.hom, Uₐ.hom.isOpenMap.isOpen_range⟩
  have hpO' : U₀.hom x ∈ O' := ⟨⟨x, hxW⟩, rfl⟩
  obtain ⟨O, hO, hpO, hOO'⟩ := exists_isAffineOpen_mem_and_subset hpO'
  have : IsAffine O := hO
  refine ⟨O, ⟨_, hpO⟩, fun n => ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := hU n
  -- constancy over `Uₐ`, on the étale and then on the pro-étale site
  let e₁ := constantIsoOverPullbackOfMap J A gₐ _ E e
  let G := Y.etaleToProetale
  let e₂ : (constantSheaf (K.over (G.obj Uₐ)) A).obj E ≅ (K.overPullback A (G.obj Uₐ)).obj (B n) :=
    constantIsoOverPullbackSheafPullback J K A G Uₐ _ E e₁ ≪≫
      (K.overPullback A (G.obj Uₐ)).mapIso
        ((Functor.sheafPullbackConstruction.sheafPullbackIso G A J K).app _) ≪≫
      (K.overPullback A (G.obj Uₐ)).mapIso (asIso (adj.counit.app (B n)))
  -- base change to `O`
  let bc := Scheme.proetaleBaseChange (Scheme.Opens.ι O)
  let K' := Scheme.ProEt.topology (Scheme.Opens.toScheme O)
  let e₃ : (constantSheaf (K'.over (bc.obj (G.obj Uₐ))) A).obj E ≅
      (K'.overPullback A (bc.obj (G.obj Uₐ))).obj
        ((proetaleModuleInverseImage.{u, v, w} (Scheme.Opens.ι O) Λ).obj (B n)) :=
    constantIsoOverPullbackSheafPullback K K' A bc (G.obj Uₐ) (B n) E e₂ ≪≫
      (K'.overPullback A (bc.obj (G.obj Uₐ))).mapIso
        ((proetaleModuleInverseImageIsoSheafPullback.{u, v, w} Λ (Scheme.Opens.ι O)).app (B n)).symm
  -- the base change covers `O`
  let T := Scheme.ProEt.mk (𝟙 (Scheme.Opens.toScheme O))
  have hT := isTerminalProEtId (Scheme.Opens.toScheme O)
  have : IsAffine (bc.obj (G.obj Uₐ)).left := by
    have key : ∀ {X' Y' Z' : Scheme.{u}} (_ : IsAffine X') (_ : IsAffine Y') (_ : IsAffine Z')
        (f : X' ⟶ Z') (g : Y' ⟶ Z'), IsAffine (pullback f g) := fun _ _ _ _ _ => inferInstance
    exact key (show IsAffine W from hW) (show IsAffine O from hO)
      (show IsAffine Y from inferInstance)
      (Scheme.Opens.ι W ≫ U₀.hom) (Scheme.Opens.ι O)
  have : IsAffine T.left := ‹IsAffine O›
  have hcov : Sieve.ofArrows (fun _ : PUnit.{1} => bc.obj (G.obj Uₐ)) (fun _ => hT.from _) ∈
      K' T := by
    refine Scheme.ProEt.ofArrows_mem_topology_of_isAffine _ _ 1 (fun _ => PUnit.unit)
      (fun _ => ⊤) (fun _ => isCompact_univ) ?_
    refine Set.eq_univ_of_forall fun o => Set.mem_iUnion.mpr ⟨0, ?_⟩
    obtain ⟨z, hz⟩ := hOO' o.2
    obtain ⟨t, -, ht⟩ := Scheme.Pullback.exists_preimage_pullback (f := Uₐ.hom)
      (g := Scheme.Opens.ι O) z o hz
    refine ⟨t, trivial, ?_⟩
    have hw : (hT.from (bc.obj (G.obj Uₐ))).left = pullback.snd Uₐ.hom (Scheme.Opens.ι O) :=
      (Category.comp_id _).symm.trans (MorphismProperty.Over.w (hT.from (bc.obj (G.obj Uₐ))))
    rwa [hw]
  exact isFiniteTypeLocallyConstant_of_cover K' Λ hT _ hcov fun _ =>
    ⟨E, (ModuleCat.isFG_iff E).mpr hE, ⟨e₃⟩⟩

/-- **Generic local constancy of a graded sheaf.** Let `g : Y ⟶ X` be a morphism from a nonempty
affine scheme, and `B n` sheaves on `X_proet` coming from `X_et`, with commuting maps
`ψ j : B n ⟶ B (n + 1)` generating each `B n` from `B 0`. If the inverse image of `B 0` to `Y` is
locally constant of finite type, then on a nonempty open of `Y` the inverse images of all the
`B n` are. -/
theorem exists_opens_isFiniteTypeLocallyConstant_of_graded [IsNoetherianRing Λ]
    {X Y : Scheme.{u}} [IsAffine Y] (y : Y) (g : Y ⟶ X)
    (B : ℕ → Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)) {k : ℕ}
    (ψ : Fin k → ∀ n, B n ⟶ B (n + 1))
    (hψ : ∀ i j n, ψ i n ≫ ψ j (n + 1) = ψ j n ≫ ψ i (n + 1))
    (hgen : ∀ (n : ℕ) {Z : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)}
      (h : B n ⟶ Z), (∀ w : Fin n → Fin k, pathHom ψ w ≫ h = 0) → h = 0)
    (hB : ∀ n, (Scheme.etaleInverseImage.{u, w, v} X Λ).essImage (B n))
    (h0 : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
      (Scheme.ProEt.topology Y) Λ ((proetaleModuleInverseImage.{u, v, w} g Λ).obj (B 0))) :
    ∃ O : Y.Opens, (O : Set Y).Nonempty ∧ ∀ n,
      IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v} (Scheme.ProEt.topology O) Λ
        ((proetaleModuleInverseImage.{u, v, w} (O.ι ≫ g) Λ).obj (B n)) := by
  let L := proetaleModuleInverseImage.{u, v, w} g Λ
  let adjg := proetaleModuleInverseImageAdjunction.{u, v, w} Λ g
  have : ((Scheme.proetaleBaseChange g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) v w} Λ)
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)).IsRightAdjoint := adjg.isRightAdjoint
  have : ((Scheme.proetaleBaseChange g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) v w} Λ)
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isRightAdjoint _
  have hBY (n : ℕ) : (Scheme.etaleInverseImage.{u, w, v} Y Λ).essImage (L.obj (B n)) := by
    obtain ⟨G, ⟨e⟩⟩ := hB n
    exact ⟨_, ⟨((Scheme.etaleInverseImageCompSheafPullbackIso X (ModuleCat.{max (u + 1) v w} Λ)
      g).app G).symm ≪≫ L.mapIso e⟩⟩
  obtain ⟨U₀, ⟨x⟩, hU⟩ := exists_etale_constantSheaf_iso_of_graded y (fun n => L.obj (B n))
    (fun j n => L.map (ψ j n)) (fun i j n => by rw [← L.map_comp, ← L.map_comp, hψ])
    (fun n Z h hh => pathHom_generates_map adjg ψ (hgen n) h hh) hBY h0
  obtain ⟨O, hO, hl⟩ := exists_opens_isFiniteTypeLocallyConstant_of_etale U₀ x
    (fun n => L.obj (B n)) hBY hU
  exact ⟨O, hO, fun n => ObjectProperty.prop_of_iso _
    ((proetaleModuleInverseImageCompIso.{u, v, w} Λ O.ι g).app (B n)) (hl n)⟩

end AlgebraicGeometry.ProEtale

/-- **A finite cover by locally closed sets has a member containing a nonempty relatively open
part.** If a nonempty subset `Z` of a topological space is covered by finitely many locally closed
sets, one of them contains `V ∩ Z ≠ ∅` for some open `V`. -/
theorem exists_isOpen_inter_subset_of_isLocallyClosed {α ι : Type*} [TopologicalSpace α]
    (L : ι → Set α) (hL : ∀ i, IsLocallyClosed (L i)) (s : Finset ι) :
    ∀ (Z : Set α), Z.Nonempty → Z ⊆ ⋃ i ∈ s, L i →
      ∃ i ∈ s, ∃ V : Set α, IsOpen V ∧ (V ∩ Z).Nonempty ∧ V ∩ Z ⊆ L i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro Z hZ hcov
    obtain ⟨z, hz⟩ := hZ
    simpa using hcov hz
  | insert a s ha ih =>
    intro Z hZ hcov
    rw [Finset.set_biUnion_insert] at hcov
    by_cases h1 : (Z \ closure (L a)).Nonempty
    · obtain ⟨i, hi, V, hV, hVne, hVsub⟩ := ih (Z \ closure (L a)) h1 fun x hx =>
        (hcov hx.1).resolve_left fun h => hx.2 (subset_closure h)
      refine ⟨i, Finset.mem_insert_of_mem hi, V ∩ (closure (L a))ᶜ,
        hV.inter isClosed_closure.isOpen_compl, ?_, ?_⟩
      · obtain ⟨x, hxV, hxZ, hxc⟩ := hVne
        exact ⟨x, ⟨hxV, hxc⟩, hxZ⟩
      · rintro x ⟨⟨hxV, hxc⟩, hxZ⟩
        exact hVsub ⟨hxV, hxZ, hxc⟩
    · have hZc : Z ⊆ closure (L a) := fun x hx => by
        by_contra hxc
        exact h1 ⟨x, hx, hxc⟩
      obtain ⟨U, F, hU, hF, hUF⟩ := hL a
      have hLa : L a = U ∩ closure (L a) := by
        refine Set.Subset.antisymm (fun x hx => ⟨(hUF ▸ hx).1, subset_closure hx⟩) ?_
        rintro x ⟨hxU, hxc⟩
        rw [hUF]
        exact ⟨hxU, closure_minimal (hUF ▸ Set.inter_subset_right) hF hxc⟩
      by_cases h2 : (U ∩ Z).Nonempty
      · refine ⟨a, Finset.mem_insert_self _ _, U, hU, h2, fun x hx => ?_⟩
        rw [hLa]
        exact ⟨hx.1, hZc hx.2⟩
      · obtain ⟨i, hi, V, hV, hVne, hVsub⟩ := ih Z hZ fun x hx =>
          (hcov hx).resolve_left fun h => h2 ⟨x, (hLa ▸ h).1, hx⟩
        exact ⟨i, Finset.mem_insert_of_mem hi, V, hV, hVne, hVsub⟩


namespace AlgebraicGeometry.ProEtale

open Stacks.ModuleSheaf

attribute [local instance] hasSheafify_proEt_moduleCat hasSheafify_proEt_over_moduleCat

variable {Λ : Type v} [CommRing Λ]

/-- **The Noetherian induction of Stacks 09BU.** On a Noetherian scheme, sheaves `B n` on `X_proet`
coming from `X_et` with commuting maps `ψ j : B n ⟶ B (n + 1)` generating each `B n` from a
constructible `B 0` are all locally constant of finite type on the strata of one constructible
stratification. -/
theorem exists_constructibleStratification_forall_of_graded [IsNoetherianRing Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (B : ℕ → Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)) {k : ℕ}
    (ψ : Fin k → ∀ n, B n ⟶ B (n + 1))
    (hψ : ∀ i j n, ψ i n ≫ ψ j (n + 1) = ψ j n ≫ ψ i (n + 1))
    (hgen : ∀ (n : ℕ) {Z : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)}
      (h : B n ⟶ Z), (∀ w : Fin n → Fin k, pathHom ψ w ≫ h = 0) → h = 0)
    (hB : ∀ n, (Scheme.etaleInverseImage.{u, w, v} X Λ).essImage (B n))
    (hB0 : IsConstructibleModuleSheaf'.{u, v, w} X Λ (B 0)) :
    ∃ s : Scheme.ConstructibleStratification X ⊤, ∀ i n,
      IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
        (Scheme.ProEt.topology (s.piece i)) Λ
        ((proetaleModuleInverseImage.{u, v, w} (s.inclusion i) Λ).obj (B n)) := by
  classical
  let P : Set X → Prop := fun S => ∃ (Z : Scheme.{u}) (ι : Z ⟶ X), IsImmersion ι ∧
    Set.range ι = S ∧ ∀ n, IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
      (Scheme.ProEt.topology Z) Λ ((proetaleModuleInverseImage.{u, v, w} ι Λ).obj (B n))
  have hstep : ∀ Z : Set X, IsClosed Z → (Set.univ ∩ Z).Nonempty →
      ∃ V : Set X, IsOpen V ∧ (V ∩ Set.univ ∩ Z).Nonempty ∧ P (V ∩ Set.univ ∩ Z) := by
    intro Z hZ hne
    obtain ⟨z, -, hz⟩ := hne
    obtain ⟨V₁, hV₁, hzV₁, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) trivial
    obtain ⟨s, hs⟩ := hB0 ⟨V₁, hV₁⟩
    obtain ⟨k₀, -, V, hV, hVne, hVsub⟩ := exists_isOpen_inter_subset_of_isLocallyClosed
      (fun i => Set.range (s.inclusion i))
      (fun i => by have := s.isImmersion i; exact (s.inclusion i).isLocallyClosed_range)
      Finset.univ ((V₁ : Set X) ∩ Z) ⟨z, hzV₁, hz⟩ fun x hx => by
        have h := s.covers ▸ hx.1
        simpa using h
    let ιk := s.inclusion k₀
    have := s.isImmersion k₀
    let T : Set (s.piece k₀) := ιk ⁻¹' (V ∩ ((V₁ : Set X) ∩ Z))
    have hT : IsLocallyClosed T :=
      (hV.isLocallyClosed.inter (V₁.2.isLocallyClosed.inter hZ.isLocallyClosed)).preimage
        ιk.continuous
    let ιT := Scheme.locallyClosedSubschemeι hT
    have : IsImmersion ιT := inferInstance
    obtain ⟨p, hpV, hpV₁Z⟩ := hVne
    obtain ⟨q, hq⟩ := hVsub ⟨hpV, hpV₁Z⟩
    have hqT : q ∈ Set.range ιT := by
      rw [Scheme.range_locallyClosedSubschemeι]
      show ιk q ∈ V ∩ ((V₁ : Set X) ∩ Z)
      rw [hq]
      exact ⟨hpV, hpV₁Z⟩
    obtain ⟨y₁, -⟩ := hqT
    obtain ⟨Yo, hYo, hy₁, -⟩ := exists_isAffineOpen_mem_and_subset
      (U := (⊤ : (Scheme.locallyClosedSubscheme hT).Opens)) (x := y₁) trivial
    have : IsAffine Yo := hYo
    let gY := (Scheme.Opens.ι Yo ≫ ιT) ≫ ιk
    have h0 : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
        (Scheme.ProEt.topology Yo) Λ ((proetaleModuleInverseImage.{u, v, w} gY Λ).obj (B 0)) :=
      ObjectProperty.prop_of_iso _
        ((proetaleModuleInverseImageCompIso.{u, v, w} Λ (Scheme.Opens.ι Yo ≫ ιT) ιk).app (B 0))
        (isFiniteTypeLocallyConstantModuleSheaf_proetaleModuleInverseImage _ _ (hs k₀))
    obtain ⟨O, hOne, hO⟩ := exists_opens_isFiniteTypeLocallyConstant_of_graded
      (Y := Scheme.Opens.toScheme Yo) ⟨y₁, hy₁⟩ gY B ψ hψ hgen hB h0
    -- the image of `O` is relatively open in `V ∩ V₁ ∩ Z`
    let e := ιT ≫ ιk
    have he : IsImmersion e := inferInstance
    have hre : Set.range e = V ∩ ((V₁ : Set X) ∩ Z) := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Scheme.range_locallyClosedSubschemeι,
        Set.image_preimage_eq_inter_range, Set.inter_eq_left]
      rintro x ⟨hxV, hxV₁Z⟩
      exact hVsub ⟨hxV, hxV₁Z⟩
    let O₁ : Set (Scheme.locallyClosedSubscheme hT) := Scheme.Opens.ι Yo '' O
    have hO₁ : IsOpen O₁ := (Scheme.Opens.ι Yo).isOpenEmbedding.isOpenMap _ O.2
    obtain ⟨V₃, hV₃, hpre⟩ := e.isEmbedding.isInducing.isOpen_iff.mp hO₁
    have hrange : Set.range (O.ι ≫ gY) = V₃ ∩ V ∩ (V₁ : Set X) ∩ Set.univ ∩ Z := by
      have : Set.range (O.ι ≫ gY) = e '' O₁ := by
        rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
        show (fun y => e ((Scheme.Opens.ι Yo) y)) '' O = _
        rw [← Set.image_image]
      rw [this, ← hpre, Set.image_preimage_eq_inter_range, hre]
      ext x
      simp [and_assoc]
    refine ⟨V₃ ∩ V ∩ (V₁ : Set X), (hV₃.inter hV).inter V₁.2, ?_, O, O.ι ≫ gY, inferInstance,
      hrange, hO⟩
    rw [← hrange]
    obtain ⟨o, ho⟩ := hOne
    exact ⟨_, ⟨o, ho⟩, rfl⟩
  obtain ⟨m, A, hlc, -, hP, hdisj, hcov⟩ :=
    exists_locallyClosed_partition_of_noetherianSpace (α := X) Set.univ isOpen_univ P hstep
  choose Zs ιs hιs hrs hls using hP
  have : TopologicalSpace.NoetherianSpace (⊤ : X.Opens).toScheme :=
    (⊤ : X.Opens).isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  refine ⟨Scheme.ConstructibleStratification.mk m Zs ιs hιs (fun i => by simp) (fun i => ?_)
    (fun i j hij => ?_) ?_, fun i n => hls i n⟩
  · rw [hrs]
    exact isConstructible_of_isLocallyClosed ((hlc i).preimage (⊤ : X.Opens).ι.base.hom.continuous)
  · rw [hrs, hrs]
    exact hdisj i j hij
  · simpa only [hrs, TopologicalSpace.Opens.coe_top] using hcov

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

open Stacks.ModuleSheaf

attribute [local instance] hasSheafify_proEt_moduleCat hasSheafify_proEt_over_moduleCat

variable {Λ : Type v} [CommRing Λ]

/-- **Restriction of coefficients along `Λ → Λ ⧸ I` preserves constructibility.** -/
theorem isConstructibleModuleSheaf'_restrictQuotientScalars [IsNoetherianRing Λ] {X : Scheme.{u}}
    (I : Ideal Λ) (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} (Λ ⧸ I)))
    (hG : IsConstructibleModuleSheaf'.{u, v, w} X (Λ ⧸ I) G) :
    IsConstructibleModuleSheaf'.{u, v, w} X Λ
      ((Stacks.ModuleSheaf.restrictQuotientScalars.{u + 1, u, max (u + 1) v w}
        (Scheme.ProEt.topology X) Λ I).obj G) :=
  fun U => by
    obtain ⟨s, hs⟩ := hG U
    exact ⟨s, fun i => ObjectProperty.prop_of_iso _
      (restrictQuotientScalarsProetaleModuleInverseImageIso.{w} Λ I (s.inclusion i) G)
      (isFiniteTypeLocallyConstantModuleSheaf_restrictQuotientScalars.{w, u, u + 1, v} _ Λ I _
        (hs i))⟩


/-- **The lisse criterion along an immersion.** Let `F` be the limit of its quotients `Q n` by the
powers of `I`, each the restriction of coefficients of a sheaf `G n` of `Λ ⧸ Iⁿ`-modules. If the
inverse images along an immersion `ι` of all the graded pieces `IⁿF / Iⁿ⁺¹F` are locally constant
of finite type, then the inverse image of `F` is lisse: the inverse images of the `Q n` are
extensions of locally constant sheaves of finite type, hence so (Stacks 093U), inverse image
along an immersion preserves the limit and the quotients, and a locally constant sheaf of finite
type is constructible and locally constant. -/
theorem isLisseAdicModuleSheaf_proetaleModuleInverseImage_of_forall [IsNoetherianRing Λ]
    {X Z : Scheme.{u}} (I : Ideal Λ) (ι : Z ⟶ X) [IsImmersion ι]
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)}
    {Q : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)}
    {q : (Functor.const ℕᵒᵖ).obj F ⟶ Q} (hlim : IsLimit (Cone.mk F q))
    (hq : ∀ n : ℕ, Stacks.ModuleSheaf.IsQuotientBy.{u + 1, u, max (u + 1) v w}
      (Scheme.ProEt.topology X) Λ (I ^ n) F (Q.obj (op n)) (q.app (op n)))
    (G : ∀ n : ℕ, Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} (Λ ⧸ I ^ n)))
    (eG : ∀ n : ℕ, Q.obj (op n) ≅
      (Stacks.ModuleSheaf.restrictQuotientScalars.{u + 1, u, max (u + 1) v w}
        (Scheme.ProEt.topology X) Λ (I ^ n)).obj (G n))
    (hgr : ∀ n : ℕ, IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
      (Scheme.ProEt.topology Z) Λ
        ((proetaleModuleInverseImage.{u, v, w} ι Λ).obj (gradedPiece Q n))) :
    IsLisseAdicModuleSheaf.{w} Z Λ I ((proetaleModuleInverseImage.{u, v, w} ι Λ).obj F) := by
  let L := proetaleModuleInverseImage.{u, v, w} ι Λ
  let P : ObjectProperty (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{max (u + 1) v w} Λ)) :=
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v} (Scheme.ProEt.topology Z) Λ
  have : P.IsWeakSerreClass := isWeakSerreClass_isFiniteTypeLocallyConstantModuleSheaf _ _
  have : L.IsLeftAdjoint := (proetaleModuleInverseImageAdjunction.{u, v, w} Λ ι).isLeftAdjoint
  -- the inverse images of the quotients are locally constant of finite type
  have hQ (n : ℕ) : P (L.obj (Q.obj (op n))) := by
    induction n with
    | zero =>
      have h := (isAnnihilatedBy_iff_smul_id _ (Q.obj (op 0))).mp (hq 0).1 1 (by simp)
      rw [one_smul] at h
      exact ObjectProperty.prop_of_isZero _
        (L.map_isZero ((IsZero.iff_id_eq_zero _).2 h))
    | succ n ih =>
      have hepi : Epi (towerMap Q n) :=
        (Stacks.ModuleSheaf.isQuotientBy_map_of_tower I q hq (Nat.le_succ n)).epi
      let S := ShortComplex.mk (kernel.ι (towerMap Q n)) (towerMap Q n) (kernel.condition _)
      have hS : S.ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel _) inferInstance hepi
      exact P.prop_X₂_of_shortExact (hS.map_of_exact L) (hgr n) ih
  have hlimL : IsLimit (L.mapCone (Cone.mk F q)) := by
    have := preservesLimitsOfShape_proetaleModuleInverseImage_of_isImmersion.{w} Λ ι ℕᵒᵖ
    exact isLimitOfPreserves L hlim
  have : ((Scheme.proetaleBaseChange ι).sheafPushforwardContinuous (ModuleCat.{max (u + 1) v w} Λ)
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)).Linear Λ := ⟨fun _ _ => rfl⟩
  refine ⟨Q ⋙ L, (L.mapCone (Cone.mk F q)).π, ⟨hlimL⟩, fun n => ⟨?_, ?_⟩⟩
  · exact (hq n).map' (proetaleModuleInverseImageAdjunction.{u, v, w} Λ ι)
  let G' := (proetaleModuleInverseImage.{u, v, w} ι (Λ ⧸ I ^ n)).obj (G n)
  let e : (Q ⋙ L).obj (op n) ≅
      (Stacks.ModuleSheaf.restrictQuotientScalars.{u + 1, u, max (u + 1) v w}
        (Scheme.ProEt.topology Z) Λ (I ^ n)).obj G' :=
    L.mapIso (eG n) ≪≫
      (restrictQuotientScalarsProetaleModuleInverseImageIso.{w} Λ (I ^ n) ι (G n)).symm
  have hG' : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
      (Scheme.ProEt.topology Z) (Λ ⧸ I ^ n) G' :=
    isFiniteTypeLocallyConstantModuleSheaf_of_restrictQuotientScalars.{w, u, u + 1, v} _ Λ (I ^ n)
      G' (ObjectProperty.prop_of_iso _ e (hQ n))
  exact ⟨G', ⟨e⟩, isConstructibleModuleSheaf'_of_isFiniteTypeLocallyConstant G' hG',
    isLocallyConstant_of_isFiniteTypeLocallyConstantModuleSheaf hG'⟩

/-- **Stacks 09BU.** Let `X` be a Noetherian scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal.
A constructible `Λ`-sheaf on `X_proet` is lisse on the strata of a finite partition of `X` into
constructible locally closed subschemes. -/
@[stacks 09BU, sga "4½ Rapport 2.5" "more general"]
theorem exists_isLisseAdicModuleSheaf_stratification [IsNoetherianRing Λ] {X : Scheme.{u}}
    [IsNoetherian X]
    (I : Ideal Λ) {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)}
    (hF : IsConstructibleAdicModuleSheaf.{w} X Λ I F) :
    ∃ s : Scheme.ConstructibleStratification X ⊤, ∀ i, IsLisseAdicModuleSheaf.{w} (s.piece i) Λ I
      ((proetaleModuleInverseImage.{u, v, w} (s.inclusion i) Λ).obj F) := by
  classical
  obtain ⟨Q, q, ⟨hlim⟩, hQ⟩ := hF
  have hq (n : ℕ) := (hQ n).1
  choose G hG using fun n => (hQ n).2
  obtain ⟨k, μ, hμI⟩ := (Submodule.fg_iff_exists_fin_generating_family).mp
    (IsNoetherian.noetherian I)
  have hμ (j : Fin k) : μ j ∈ I := hμI ▸ Submodule.subset_span ⟨j, rfl⟩
  have : ObjectProperty.IsWeakSerreClass (IsConstructibleModuleSheaf'.{u, v, w} X Λ) :=
    isWeakSerreClass_isConstructibleModuleSheaf' X Λ
  have hQc (n : ℕ) : IsConstructibleModuleSheaf'.{u, v, w} X Λ (Q.obj (op n)) :=
    ObjectProperty.prop_of_iso _ (hG n).1.some.symm
      (isConstructibleModuleSheaf'_restrictQuotientScalars _ _ (hG n).2)
  have hBc (n : ℕ) : IsConstructibleModuleSheaf'.{u, v, w} X Λ (gradedPiece Q n) :=
    ObjectProperty.prop_kernel _ _ (hQc (n + 1)) (hQc n)
  obtain ⟨s, hs⟩ := exists_constructibleStratification_forall_of_graded (gradedPiece Q)
    (fun j n => gradedMul I q hq (μ j) (hμ j) n)
    (fun i j n => gradedMul_comm I q hq _ _ _ _ n)
    (fun n Z h hh => gradedPiece_hom_ext I q hq μ hμ hμI h hh)
    (fun n => etaleInverseImage_essImage_of_isConstructibleModuleSheaf' _ (hBc n)) (hBc 0)
  refine ⟨s, fun i => ?_⟩
  have := s.isImmersion i
  exact isLisseAdicModuleSheaf_proetaleModuleInverseImage_of_forall I (s.inclusion i) hlim hq G
    (fun n => (hG n).1.some) (fun n => hs i n)

end AlgebraicGeometry.ProEtale

end
