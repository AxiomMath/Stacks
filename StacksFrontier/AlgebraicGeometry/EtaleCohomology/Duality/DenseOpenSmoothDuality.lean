module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.DenseOpenDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.StratumPurityDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.StratumShortExact
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.SmoothStratumOfClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness

/-!
# Poincaré duality on a smooth variety from a dense open, given purity

Let `k` be an algebraically closed field, `ℓ` a prime and `Λ = ℤ/ℓ`. Let `W` be smooth of
relative dimension `e` over `k`, with noetherian underlying space, `j : W → X̄` a compactification
and `L` a sheaf of `Λ`-modules on `W`. Write `D = j_! Λ_W` and fix a trace `t` on
`Ext^{2e}_X̄(Λ, D) = H^{2e}_c(W)`.

A *purity class* for a closed immersion `i : T → Y` in degree `c` is a class
`γ ∈ Ext^c_Y(i_* Λ_T, Λ_Y)` such that `y ↦ i_* y ∘ γ` is bijective
`Ext^q_T(G, Λ_T) → Ext^{q + c}_Y(i_* G, Λ_Y)` for every sheaf `G` on `T` and every `q`, and
`Ext^q_Y(i_* G, Λ_Y) = 0` for `q < c` (`Stacks.EtaleCohomology.IsPurityClass`). *Local purity*
(`Stacks.EtaleCohomology.LocalPurity`) says that a closed immersion `i : T → Y` of a scheme smooth
of relative dimension `d` into one smooth of relative dimension `d + c` over `k` has a purity class
in degree `2c` on a neighbourhood of every point of `T` (SGA 4 XVI 3.7, Milne, *Lectures on étale
cohomology* §16; it is cohomological purity for smooth pairs, `Ri^! Λ = Λ[-2c]`, over a field
containing the `ℓ`-th roots of unity).

Given local purity, duality and the vanishing of `Ext^q(j_! L, D)` for `q > 2e` hold at `j_! L` as
soon as they hold at `j_! (L|_{W°})` for a dense open `W°`, provided that, for every smooth stratum
`T` of relative dimension `e' < e` closed in an open `N` of `W` with a purity class, duality holds
on the induced compactification `T̄` of `T` at the inverse image of `L` for the trace induced by
`t` and the Gysin class (`Stacks.EtaleCohomology.stratumTrace`), with the vanishing above `2e'`
(Poincaré duality in dimension `e' < e`), and `H^{2e+1}(X̄, j_! M) = 0` for every `M`
(Tag 095U). Purity identifies duality at a stratum with duality on `T̄`
(`Stacks.EtaleCohomology.isDualityPerfect_stratum_iff`).

## Main results

* `Stacks.EtaleCohomology.IsPurityClass`, `Stacks.EtaleCohomology.LocalPurity`.
* `Stacks.EtaleCohomology.isDualityPerfect_of_dense_open_of_smooth`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- A **purity class** for a closed immersion `i : T → Y` in degree `c`: a class
`γ ∈ Ext^c_Y(i_* Λ_T, A)` such that `y ↦ i_* y ∘ γ` is bijective
`Ext^q_T(G, Λ_T) → Ext^{q + c}_Y(i_* G, A)` for all `G` and `q`, and `Ext^q_Y(i_* G, A) = 0` for
`q < c`. For `A = Λ_Y`, `Y` smooth and `T` smooth of codimension `c'`, `c = 2c'`, this is
cohomological purity. -/
def IsPurityClass {T Y : Scheme.{u}} (i : T ⟶ Y) [IsClosedImmersion i]
    (A : EtaleModules.{u, 0} (ZMod ℓ) Y) {c : ℕ}
    (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ)) A c) :
    Prop :=
  (∀ (G : EtaleModules.{u, 0} (ZMod ℓ) T) (q : ℕ),
    Function.Bijective (fun y : Ext G (unitSheaf (X := T) ℓ) q =>
      (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)).comp γ
        (rfl : q + c = q + c))) ∧
  ∀ (G : EtaleModules.{u, 0} (ZMod ℓ) T) (q : ℕ), q < c →
    Subsingleton (Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj G) A q)

variable (k : Type u) [Field k] (ℓ) in
/-- **Local purity for smooth pairs over `k`**: for `p : Y → Spec k` smooth of relative dimension
`d + c` and a closed immersion `i : T → Y` with `T` smooth of relative dimension `d`, every point
of `T` has an open neighbourhood `N` in `Y` over which `T ∩ N → N` has a purity class in degree
`2c` for `Λ_N`. -/
def LocalPurity : Prop :=
  ∀ (Y T : Scheme.{u}) (p : Y ⟶ Spec (.of k)) (i : T ⟶ Y) [IsClosedImmersion i] (d c : ℕ)
    [SmoothOfRelativeDimension (d + c) p] [SmoothOfRelativeDimension d (i ≫ p)] (x : T),
    ∃ N : Y.Opens, i.base x ∈ N ∧
      ∃ γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i ∣_ N)).obj
          (unitSheaf (X := (i ⁻¹ᵁ N).toScheme) ℓ)) (unitSheaf (X := N.toScheme) ℓ) (2 * c),
        IsPurityClass (i ∣_ N) (unitSheaf (X := N.toScheme) ℓ) γ

/-- A purity class transports along an isomorphism of its target. -/
theorem IsPurityClass.comp_mk₀ {T Y : Scheme.{u}} {i : T ⟶ Y} [IsClosedImmersion i]
    {A B : EtaleModules.{u, 0} (ZMod ℓ) Y} {c : ℕ}
    {γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ)) A c}
    (hγ : IsPurityClass i A γ) (e : A ≅ B) :
    IsPurityClass i B (γ.comp (Ext.mk₀ e.hom) (add_zero c)) := by
  refine ⟨fun G q => ?_, fun G q hq =>
    Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target e q (hγ.2 G q hq)⟩
  have h := (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso e.hom (q + c)).comp (hγ.1 G q)
  convert h using 1
  funext y
  simp only [Function.comp_apply]
  rw [Stacks.ExtAdjunction.postcomp_apply, Ext.comp_assoc _ _ _ rfl (add_zero c) (by omega)]

section InducedClosed

variable {k : Type u} [Field k] {W : Scheme.{u}} (f : W ⟶ Spec (.of k))
  (jc : CompactificationOf (Over.mk f))

/-- The closed immersion `T̄ → X̄` of the compactification of `T ⊆ N` induced through an open
immersion `n : N → W`, with codomain the compactification `X̄` of `W` itself. -/
lemma isClosedImmersion_restrictOpen_closedSpaceι {N T : Scheme.{u}} (n : N ⟶ W)
    [IsOpenImmersion n] (i : T ⟶ N) [IsClosedImmersion i] [QuasiCompact (n ≫ f)] :
    @IsClosedImmersion _ jc.space ((jc.restrictOpen n).closedSpaceι i) :=
  (inferInstance : IsClosedImmersion ((jc.restrictOpen n).closedSpaceι i))

/-- The direct image along the closed immersion `T̄ → X̄` of
`isClosedImmersion_restrictOpen_closedSpaceι` is exact. -/
lemma preservesFiniteColimits_restrictOpen_closedSpaceι {N T : Scheme.{u}} (n : N ⟶ W)
    [IsOpenImmersion n] (i : T ⟶ N) [IsClosedImmersion i] [QuasiCompact (n ≫ f)] :
    PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} (ZMod ℓ)
      (X := (jc.restrictOpen n).closedSpace i) (Y := jc.space)
        ((jc.restrictOpen n).closedSpaceι i)) := by
  have : @IsIntegralHom _ jc.space ((jc.restrictOpen n).closedSpaceι i) :=
    (inferInstance : IsIntegralHom ((jc.restrictOpen n).closedSpaceι i))
  exact etaleModuleDirectImage_preservesFiniteColimits_of_isIntegralHom (ZMod ℓ)
    (X := (jc.restrictOpen n).closedSpace i) (Y := jc.space) ((jc.restrictOpen n).closedSpaceι i)

end InducedClosed

attribute [local instance] isClosedImmersion_restrictOpen_closedSpaceι
  preservesFiniteColimits_restrictOpen_closedSpaceι

/-- If a stratum `i : T → Y` of an open `Y ⊆ W` has image the part of `Y` outside an open `V`,
its restriction over an open `N ⊆ Y` has image the part of `N` outside `V`. -/
private lemma range_morphismRestrict_comp_ι_eq_diff {W T : Scheme.{u}} {Y : W.Opens}
    (i : T ⟶ Y.toScheme) (N : Y.toScheme.Opens) (V : W.Opens)
    (hrange : Set.range (i ≫ Y.ι).base = (V : Set W)ᶜ ∩ (Y : Set W)) :
    Set.range ((i ∣_ N) ≫ N.ι ≫ Y.ι).base = Set.range (N.ι ≫ Y.ι).base \ (V : Set W) := by
  have hcomp : (i ∣_ N) ≫ N.ι ≫ Y.ι = (i ⁻¹ᵁ N).ι ≫ i ≫ Y.ι := by
    simp only [← Category.assoc, morphismRestrict_ι]
  have hYinj : Function.Injective Y.ι.base := Y.ι.isOpenEmbedding.injective
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨⟨(i ∣_ N).base s, rfl⟩, ?_⟩
    have : ((i ∣_ N) ≫ N.ι ≫ Y.ι).base s ∈ Set.range (i ≫ Y.ι).base := by
      rw [hcomp]
      exact ⟨((i ⁻¹ᵁ N).ι).base s, rfl⟩
    rw [hrange] at this
    exact this.1
  · rintro ⟨⟨m, rfl⟩, hm⟩
    have hmZ : (N.ι ≫ Y.ι).base m ∈ Set.range (i ≫ Y.ι).base := by
      rw [hrange]
      exact ⟨hm, (N.ι.base m).2⟩
    obtain ⟨s, hs⟩ := hmZ
    have hs' : i.base s = N.ι.base m := hYinj (by simpa using hs)
    have hsN : s ∈ i ⁻¹ᵁ N := by
      show i.base s ∈ N
      rw [hs']
      exact m.2
    refine ⟨⟨s, hsN⟩, ?_⟩
    rw [hcomp]
    exact hs

section Smooth

variable {k : Type u} [Field k] [IsAlgClosed k] {W : Scheme.{u}} (f : W ⟶ Spec (.of k)) {e : ℕ}
  [SmoothOfRelativeDimension e f] [TopologicalSpace.NoetherianSpace W]
  (jc : CompactificationOf (Over.mk f)) (L : EtaleModules.{u, 0} (ZMod ℓ) W)

/-- `Λ_N ≅ (n ≫ j)^{-1} j_! Λ_W` for open immersions `n : N → W` and `j : W → X̄`. -/
def unitSheafIsoRestrictionExtensionByZero {N X : Scheme.{u}} (n : N ⟶ W) [IsOpenImmersion n]
    (j : W ⟶ X) [IsOpenImmersion j] :
    unitSheaf (X := N) ℓ ≅ (etaleModuleRestriction.{u, 0} (ZMod ℓ) (n ≫ j)).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj (unitSheaf (X := W) ℓ)) :=
  ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) n).app
      (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))).symm ≪≫
    (etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod ℓ) n).app (unitSheaf (X := W) ℓ) ≪≫
    (etaleModuleRestriction.{u, 0} (ZMod ℓ) n).mapIso
      (asIso ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j).unit.app
        (unitSheaf (X := W) ℓ))) ≪≫
    (etaleModuleRestrictionCompIso.{u, 0} (ZMod ℓ) n j).app _

/-- Poincaré duality on a smooth variety from a dense open, given local purity: duality on `X̄`
and the vanishing of `Ext^q(j_! L, D)` for `q > 2e` hold at `j_! L` if they hold at
`j_! (L|_{W₀})` for a dense open `W₀`, if `H^{2e+1}(X̄, j_! M) = 0` for every `M`, and if (`hlow`)
for every smooth irreducible `T` of relative dimension `e' < e` closed in an open `n : N → W` with
a purity class `γ`, duality and the vanishing above `2e'` hold on the compactification of `T`
induced by `j` (with `H^q_c(T, G) = 0` for `q > 2e'`), at the inverse image `G` of `L`, for the
trace induced by `t` and `γ`. -/
theorem isDualityPerfect_of_dense_open_of_smooth
    (t : Ext (unitSheaf (X := jc.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        (2 * e) →+ ZMod ℓ)
    (W₀ : W.Opens) (hW₀ : Dense (W₀ : Set W)) (hpurity : LocalPurity ℓ k)
    (hvan : ∀ M : EtaleModules.{u, 0} (ZMod ℓ) W, Subsingleton (Ext (unitSheaf (X := jc.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj M) (2 * e + 1)))
    (h₀ : Ext.IsDualityPerfect (unitSheaf (X := jc.space) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        (2 * e) t ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
          ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) W₀.ι).obj L)) ∧
      ∀ q, 2 * e < q → Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ)
        jc.immersion).obj ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) W₀.ι).obj L))
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ)) q))
    (hlow : ∀ (N T : Scheme.{u}) (n : N ⟶ W) [IsOpenImmersion n] (i : T ⟶ N)
      [IsClosedImmersion i] [IrreducibleSpace T] (e' c : ℕ) (hc : e' + c = e) (_ : 0 < c)
      [SmoothOfRelativeDimension e' (i ≫ n ≫ f)] [QuasiCompact (n ≫ f)]
      (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ))
        ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
            (unitSheaf (X := W) ℓ))) (2 * c)),
      IsPurityClass i _ γ →
      (∀ q, 2 * e' < q → Subsingleton (Ext (unitSheaf (X := (jc.restrictOpen n).closedSpace i) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ)
          ((jc.restrictOpen n).closedImmersion i).toImage).obj
          ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (𝟙 T)).obj
            ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) (i ≫ n)).obj L))) q)) ∧
      Ext.IsDualityPerfect (unitSheaf (X := (jc.restrictOpen n).closedSpace i) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ)
          ((jc.restrictOpen n).closedImmersion i).toImage).obj (unitSheaf (X := T) ℓ)) (2 * e')
        (stratumTrace i ((jc.restrictOpen n).closedImmersion i).toImage (n ≫ jc.immersion)
          ((jc.restrictOpen n).closedSpaceι i) ((jc.restrictOpen n).isPullback_restrictClosed i)
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
          (show 2 * e' + 2 * c = 2 * e by omega) γ t)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ)
          ((jc.restrictOpen n).closedImmersion i).toImage).obj
          ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (𝟙 T)).obj
            ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) (i ≫ n)).obj L))) ∧
      ∀ q, 2 * e' < q → Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ)
          ((jc.restrictOpen n).closedImmersion i).toImage).obj
          ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (𝟙 T)).obj
            ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) (i ≫ n)).obj L)))
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ)
          ((jc.restrictOpen n).closedImmersion i).toImage).obj (unitSheaf (X := T) ℓ)) q)) :
    Ext.IsDualityPerfect (unitSheaf (X := jc.space) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        (2 * e) t ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj L) ∧
      ∀ q, 2 * e < q → Subsingleton (Ext
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj L)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
          (unitSheaf (X := W) ℓ)) q) := by
  let Φ := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion
  let D := Φ.obj (unitSheaf (X := W) ℓ)
  have : Smooth f := SmoothOfRelativeDimension.smooth e f
  refine isDualityPerfect_of_dense_open (W := W) Φ L D t W₀ hvan h₀ ?_
  intro V hV hVtop
  let Z : Set W := (V : Set W)ᶜ
  have hZc : IsClosed Z := V.isOpen.isClosed_compl
  have hZne : Z.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
    exact hVtop (TopologicalSpace.Opens.ext (h.trans TopologicalSpace.Opens.coe_top.symm))
  have hint : interior Z = ∅ := (hW₀.mono hV).interior_compl
  obtain ⟨Y, T, i, hiC, e', hsm, hT, hTirr, hrange⟩ :=
    exists_smoothOfRelativeDimension_closedImmersion_of_isClosed f Z hZc hZne
  have : Nonempty W := ⟨hZne.some⟩
  have hdimW : topologicalKrullDim W ≤ e :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field e f).le
  have hdimT := topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field e' (i ≫ Y.ι ≫ f)
  have hlt := topologicalKrullDim_lt_of_isClosed_of_interior_eq_empty hZc hint hdimW
    (i ≫ Y.ι).isEmbedding.isInducing (hrange.subset.trans Set.inter_subset_left)
  rw [hdimT] at hlt
  have hlt' : e' < e := mod_cast hlt
  obtain ⟨c, hc⟩ : ∃ c, e' + c = e := ⟨e - e', by omega⟩
  have : SmoothOfRelativeDimension (e' + c) (Y.ι ≫ f) := by
    rw [hc, ← zero_add e]
    infer_instance
  obtain ⟨x⟩ := hT
  obtain ⟨N₂, hxN, γ₀, hγ₀⟩ := hpurity Y.toScheme T (Y.ι ≫ f) i e' c x
  let i₂ : (i ⁻¹ᵁ N₂).toScheme ⟶ N₂.toScheme := i ∣_ N₂
  let n : N₂.toScheme ⟶ W := N₂.ι ≫ Y.ι
  have hi₂ : i₂ ≫ N₂.ι = (i ⁻¹ᵁ N₂).ι ≫ i := morphismRestrict_ι i N₂
  have hcomp : i₂ ≫ n = (i ⁻¹ᵁ N₂).ι ≫ i ≫ Y.ι := by
    simp only [n, ← Category.assoc, hi₂]
  have : SmoothOfRelativeDimension e' (i₂ ≫ n ≫ f) := by
    rw [← Category.assoc, hcomp, Category.assoc, ← zero_add e']
    have : SmoothOfRelativeDimension e' ((i ≫ Y.ι) ≫ f) := by rwa [Category.assoc]
    infer_instance
  have : CompactSpace N₂.toScheme := ⟨(n.isOpenEmbedding.isInducing.isCompact_iff).2
    (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  have : QuasiCompact (n ≫ f) := inferInstance
  have hrange₂ : Set.range (i₂ ≫ n).base = Set.range n.base \ (V : Set W) :=
    range_morphismRestrict_comp_ι_eq_diff i N₂ V hrange
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    exists_shortExact_extensionByZero_sup_stratum (ZMod ℓ) V n i₂ hrange₂ L
  refine ⟨V ⊔ n.opensRange, lt_of_le_of_ne le_sup_left fun h => ?_, S, hS, ⟨e₁⟩, ⟨e₂⟩, ?_⟩
  · have hy : (i₂ ≫ n).base ⟨x, hxN⟩ ∈ Set.range (i₂ ≫ n).base := ⟨_, rfl⟩
    rw [hrange₂] at hy
    apply hy.2
    rw [h]
    exact Or.inr hy.1
  · let G := (etaleModuleRestriction.{u, 0} (ZMod ℓ) (𝟙 (i ⁻¹ᵁ N₂).toScheme)).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) (i₂ ≫ n)).obj L)
    have hγ := hγ₀.comp_mk₀ (unitSheafIsoRestrictionExtensionByZero n jc.immersion)
    have : IrreducibleSpace (i ⁻¹ᵁ N₂).toScheme :=
      Subtype.irreducibleSpace ⟨⟨x, hxN⟩, (IrreducibleSpace.isIrreducible_univ T).2.open_subset
        (i ⁻¹ᵁ N₂).isOpen (Set.subset_univ _)⟩
    obtain ⟨hvanT, hPD, hCD⟩ := hlow N₂.toScheme (i ⁻¹ᵁ N₂).toScheme n i₂ e' c hc (by omega) _ hγ
    let E : Φ.obj S.X₃ ≅ (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i₂).obj G) :=
      Φ.mapIso e₃ ≪≫ ((etaleModuleExtensionByZeroCompIso.{u, 0} (ZMod ℓ) n jc.immersion).app _).symm
    refine ⟨Ext.isDualityPerfect_of_iso E.symm ((isDualityPerfect_stratum_iff i₂
      ((jc.restrictOpen n).closedImmersion i₂).toImage (n ≫ jc.immersion)
      ((jc.restrictOpen n).closedSpaceι i₂) ((jc.restrictOpen n).isPullback_restrictClosed i₂) D
      (show 2 * e' + 2 * c = 2 * e by omega) _ t G (hγ.1 G) (hγ.2 G) hvanT).2 hPD), fun q hq => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 2 * c := ⟨q - 2 * c, by omega⟩
    exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source E.symm _
      (subsingleton_ext_stratum (i := i₂) (u := ((jc.restrictOpen n).closedImmersion i₂).toImage)
        (j := n ≫ jc.immersion) (D := D) _ G (hγ.1 G) m (hCD m (by omega)))

end Smooth

end Stacks.EtaleCohomology
