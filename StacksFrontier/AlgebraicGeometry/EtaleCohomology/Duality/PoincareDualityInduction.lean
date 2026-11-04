module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.DenseOpenSmoothDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperLocallyConstantDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.ConnectedIrreducible

/-!
# Poincaré duality on smooth varieties by induction on the dimension

Let `k` be an algebraically closed field, `ℓ` a prime and `Λ = ℤ/ℓ`. For `W` smooth of relative
dimension `e` over `k` with a compactification `j : W → X̄` and a trace `t` on
`H^{2e}_c(W) = Ext^{2e}_X̄(Λ, j_! Λ_W)`, *Poincaré duality* is the perfectness of the pairing
`H^a_c(W) × Ext^{2e-a}_X̄(j_! Λ_W, j_! Λ_W) → H^{2e}_c(W) → Λ`
(`CategoryTheory.Abelian.Ext.IsDualityPerfect`), together with `Ext^q_X̄(j_! Λ_W, j_! Λ_W) = 0`
for `q > 2e`.

A trace is *good* (`Stacks.EtaleCohomology.IsGoodTrace`) when it is injective and, for every
smooth irreducible stratum `T` of `W` of smaller dimension closed in an open of `W` with a purity
class `γ`, the trace induced on `H^{2 dim T}_c(T)` by `t` and the Gysin class of `γ`
(`Stacks.EtaleCohomology.stratumTrace`) is good, on the compactification of `T` induced by `j`.
This is a definition by recursion on the dimension. For `W` irreducible a good trace exists
(`H^{2e}_c(W) ≅ Λ` and the Gysin maps between top compactly supported cohomologies of irreducible
strata are isomorphisms).

This file proves duality for every good trace, by induction on `e`, from local purity
(`Stacks.EtaleCohomology.LocalPurity`) and from duality at `j_!` of the constant sheaf on *some*
dense open of `W` (`hcore`; in the proof of Poincaré duality, a dense open which is an elementary
fibration over a smooth variety of dimension `e - 1`): the dense-open step
`Stacks.EtaleCohomology.isDualityPerfect_of_dense_open_of_smooth` applies, its strata are smooth
irreducible of dimension `< e` with a good induced trace, their compactifications have dimension
at most theirs (`AlgebraicGeometry.topologicalKrullDim_le_of_isOpen_of_irreducibleSpace`), and
the vanishing in degrees above twice the dimension is Tag 095U on the compactifications.

## Main results

* `Stacks.EtaleCohomology.IsGoodTrace`.
* `Stacks.EtaleCohomology.isDualityPerfect_unitSheaf_of_isGoodTrace`.
* `Stacks.EtaleCohomology.isDualityPerfect_of_isFiniteTypeLocallyConstant_of_smooth_proper`:
  Poincaré duality with lisse coefficients on a connected smooth proper `X` of dimension `d`,
  `Ext^q_X(Λ, F) × Ext^{2d-q}_X(F, Λ) → H^{2d}(X, Λ) → Λ`, for an injective trace, from the same
  inputs, from the existence of good traces on the connected finite étale covers of `X`, and from
  `#H^{2d}(T, Λ) = #H^{2d}(X, Λ)` on those covers.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize isClosedImmersion_restrictOpen_closedSpaceι
  preservesFiniteColimits_restrictOpen_closedSpaceι

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]

/-- **Good traces, with fuel**: `IsGoodTraceAux m e f jc t` says that `t` is injective and, if
`m > 0`, that for every irreducible stratum `T` closed in an open `n : N → W`, smooth of relative
dimension `e' = e - c` over `k` with `c > 0`, with a purity class `γ` of degree `2c`, the trace
`stratumTrace` induced on `H^{2e'}_c(T)` satisfies `IsGoodTraceAux (m - 1) e'` for the
compactification of `T` induced by `j`. The fuel `m = e` is `Stacks.EtaleCohomology.IsGoodTrace`.
-/
def IsGoodTraceAux : ℕ → (e : ℕ) → {W : Scheme.{u}} → (f : W ⟶ Spec (.of k)) →
    (jc : CompactificationOf (Over.mk f)) →
    (Ext (unitSheaf (X := jc.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        (2 * e) →+ ZMod ℓ) → Prop
  | 0, _, _, _, _, t => Function.Injective t
  | m + 1, e, W, f, jc, t => Function.Injective t ∧
    ∀ (N T : Scheme.{u}) (n : N ⟶ W) [IsOpenImmersion n] (i : T ⟶ N) [IsClosedImmersion i]
      [IrreducibleSpace T] (e' c : ℕ) (hc : e' + c = e) (_ : 0 < c) [QuasiCompact (n ≫ f)]
      [SmoothOfRelativeDimension e' (i ≫ n ≫ f)]
      (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ))
        ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
            (unitSheaf (X := W) ℓ))) (2 * c)),
      IsPurityClass i _ γ →
        IsGoodTraceAux m e' (i ≫ n ≫ f) ((jc.restrictOpen n).restrictClosed i)
          (stratumTrace i ((jc.restrictOpen n).closedImmersion i).toImage (n ≫ jc.immersion)
            ((jc.restrictOpen n).closedSpaceι i) ((jc.restrictOpen n).isPullback_restrictClosed i)
            ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
              (unitSheaf (X := W) ℓ))
            (show 2 * e' + 2 * c = 2 * e by omega) γ t)

/-- A **good trace** on `H^{2e}_c(W) = Ext^{2e}_X̄(Λ, j_! Λ_W)` for a compactification `j` of
`f : W → Spec k`: it is injective, and for every smooth irreducible stratum `T` closed in an open
of `W`, of relative dimension `e' < e`, with a purity class, the trace `stratumTrace` induced on
`H^{2e'}_c(T)` is good for the compactification of `T` induced by `j`
(`Stacks.EtaleCohomology.IsGoodTraceAux` with fuel `e`). -/
def IsGoodTrace (e : ℕ) {W : Scheme.{u}} (f : W ⟶ Spec (.of k))
    (jc : CompactificationOf (Over.mk f))
    (t : Ext (unitSheaf (X := jc.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        (2 * e) →+ ZMod ℓ) : Prop :=
  IsGoodTraceAux ℓ k e e f jc t

/-- `𝟙^{-1} g^{-1} Λ_S ≅ Λ_T` for a morphism `g : T → S`. -/
def unitSheafRestrictionIdInverseImageIso {T S : Scheme.{u}} (g : T ⟶ S) :
    (etaleModuleRestriction.{u, 0} (ZMod ℓ) (𝟙 T)).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) g).obj (unitSheaf (X := S) ℓ)) ≅
      unitSheaf (X := T) ℓ :=
  (etaleModuleRestriction.{u, 0} (ZMod ℓ) (𝟙 T)).mapIso
      ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) g).app
        (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))) ≪≫
    ((etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod ℓ) (𝟙 T)).app _).symm ≪≫
    (etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) (𝟙 T)).app
      (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))

variable {k}

/-- **The compactification of an irreducible stratum has its dimension**: for `T` smooth
irreducible of relative dimension `e'` over `k`, closed in an open `n : N → W`, the closure of `T`
in a compactification of `W` has dimension at most `e'` — it is irreducible, locally of finite
type over `k`, and contains `T` as a nonempty open. -/
theorem topologicalKrullDim_restrictClosed_space_le {W N T : Scheme.{u}} (f : W ⟶ Spec (.of k))
    (jc : CompactificationOf (Over.mk f)) (n : N ⟶ W) [IsOpenImmersion n] (i : T ⟶ N)
    [IsClosedImmersion i] [QuasiCompact (n ≫ f)] [IrreducibleSpace T] (e' : ℕ)
    [SmoothOfRelativeDimension e' (i ≫ n ≫ f)] :
    topologicalKrullDim ((jc.restrictOpen n).restrictClosed i).space ≤ e' := by
  let g := (jc.restrictOpen n).closedImmersion i
  let p := ((jc.restrictOpen n).restrictClosed i).toBase
  have hopen : IsOpen (Set.range g.toImage.base) := g.toImage.isOpenEmbedding.isOpen_range
  obtain ⟨x⟩ := (‹IrreducibleSpace T›).toNonempty
  have : Nonempty T := ⟨x⟩
  have hne : (Set.range g.toImage.base).Nonempty := ⟨_, x, rfl⟩
  have : IrreducibleSpace ((jc.restrictOpen n).restrictClosed i).space := by
    rw [irreducibleSpace_def]
    have h := (IrreducibleSpace.isIrreducible_univ T).image g.toImage.base
      g.toImage.base.hom.continuous.continuousOn
    rw [Set.image_univ] at h
    have hc := h.closure
    rwa [g.toImage.denseRange.closure_range] at hc
  have h1 : topologicalKrullDim ((jc.restrictOpen n).restrictClosed i).space ≤
      topologicalKrullDim (Set.range g.toImage.base) :=
    topologicalKrullDim_le_of_isOpen_of_irreducibleSpace p hopen hne
  have h2 : topologicalKrullDim (Set.range g.toImage.base) = topologicalKrullDim T :=
    ((g.toImage.isOpenEmbedding.isEmbedding.toHomeomorph).isHomeomorph.topologicalKrullDim_eq).symm
  have h3 := topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field e' (i ≫ n ≫ f)
  rwa [h2, h3] at h1

variable [IsAlgClosed k]

/-- **Poincaré duality on smooth varieties by induction on the dimension, for good traces**, with
fuel `m ≥ e`; see `Stacks.EtaleCohomology.isDualityPerfect_unitSheaf_of_isGoodTrace`. -/
theorem isDualityPerfect_unitSheaf_of_isGoodTraceAux (hpurity : LocalPurity ℓ k)
    (hcore : ∀ (e : ℕ) (W : Scheme.{u}) (f : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension e f]
      [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
      (jc : CompactificationOf (Over.mk f)), topologicalKrullDim jc.space ≤ e →
      ∀ (m : ℕ) (t : Ext (unitSheaf (X := jc.space) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
          (2 * e) →+ ZMod ℓ), e ≤ m → IsGoodTraceAux ℓ k m e f jc t →
      ∃ W₀ : W.Opens, Dense (W₀ : Set W) ∧
        Ext.IsDualityPerfect (unitSheaf (X := jc.space) ℓ)
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
          (2 * e) t ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
            ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) W₀.ι).obj
              (unitSheaf (X := W) ℓ))) ∧
        ∀ q, 2 * e < q → Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ)
          jc.immersion).obj ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) W₀.ι).obj
            (unitSheaf (X := W) ℓ)))
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
            (unitSheaf (X := W) ℓ)) q)) :
    ∀ (m e : ℕ) (W : Scheme.{u}) (f : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension e f]
      [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
      (jc : CompactificationOf (Over.mk f)), topologicalKrullDim jc.space ≤ e →
      ∀ (t : Ext (unitSheaf (X := jc.space) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
          (2 * e) →+ ZMod ℓ), e ≤ m → IsGoodTraceAux ℓ k m e f jc t →
      Ext.IsDualityPerfect (unitSheaf (X := jc.space) ℓ)
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
          (2 * e) t ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
            (unitSheaf (X := W) ℓ)) ∧
        ∀ q, 2 * e < q → Subsingleton (Ext
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
            (unitSheaf (X := W) ℓ)) q) := by
  intro m
  induction m with
  | zero => ?_
  | succ m ih => ?_
  all_goals
    intro e W f _ _ _ jc hdim t hem ht
    obtain ⟨W₀, hW₀, h₀⟩ := hcore e W f jc hdim _ t hem ht
    refine isDualityPerfect_of_dense_open_of_smooth f jc (unitSheaf ℓ) t W₀ hW₀ hpurity
      (fun M => subsingleton_ext_unitSheaf_of_proper jc.toBase e hdim _ _ (by omega)) h₀ ?_
    intro N T n _ i _ _ e' c hc hc0
  · omega
  · intro _ _ γ hγ
    have : TopologicalSpace.NoetherianSpace T := (i ≫ n).isEmbedding.isInducing.noetherianSpace
    have hdimT := topologicalKrullDim_restrictClosed_space_le f jc n i e'
    obtain ⟨hPD, hCD⟩ := ih e' T (i ≫ n ≫ f) ((jc.restrictOpen n).restrictClosed i) hdimT _
      (by omega) (ht.2 N T n i e' c hc hc0 γ hγ)
    let uS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ)
      ((jc.restrictOpen n).closedImmersion i).toImage
    let eG := uS.mapIso (unitSheafRestrictionIdInverseImageIso ℓ (i ≫ n))
    exact ⟨fun q hq => subsingleton_ext_unitSheaf_of_proper
        ((jc.restrictOpen n).restrictClosed i).toBase e' hdimT _ q hq,
      Ext.isDualityPerfect_of_iso eG.symm hPD,
      fun q hq => Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source eG.symm q (hCD q hq)⟩

/-- **Poincaré duality on smooth varieties by induction on the dimension, for good traces.** Let
`W` be smooth irreducible of relative dimension `e` over an algebraically closed field `k`, with
noetherian underlying space and a compactification `j : W → X̄` of dimension at most `e`, and let
`t` be a good trace on `H^{2e}_c(W)`. Given local purity and, for every such `W`, duality and the
vanishing above `2e` at `j_! Λ` on some dense open of `W` (`hcore`), duality holds at `j_! Λ_W`
for `D = j_! Λ_W` and `t`, with `Ext^q_X̄(j_! Λ_W, j_! Λ_W) = 0` for `q > 2e`. -/
theorem isDualityPerfect_unitSheaf_of_isGoodTrace (hpurity : LocalPurity ℓ k)
    (hcore : ∀ (e : ℕ) (W : Scheme.{u}) (f : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension e f]
      [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
      (jc : CompactificationOf (Over.mk f)), topologicalKrullDim jc.space ≤ e →
      ∀ (m : ℕ) (t : Ext (unitSheaf (X := jc.space) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
          (2 * e) →+ ZMod ℓ), e ≤ m → IsGoodTraceAux ℓ k m e f jc t →
      ∃ W₀ : W.Opens, Dense (W₀ : Set W) ∧
        Ext.IsDualityPerfect (unitSheaf (X := jc.space) ℓ)
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
          (2 * e) t ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
            ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) W₀.ι).obj
              (unitSheaf (X := W) ℓ))) ∧
        ∀ q, 2 * e < q → Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ)
          jc.immersion).obj ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) W₀.ι).obj
            (unitSheaf (X := W) ℓ)))
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
            (unitSheaf (X := W) ℓ)) q))
    (e : ℕ) {W : Scheme.{u}} (f : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension e f]
    [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
    (jc : CompactificationOf (Over.mk f)) (hdim : topologicalKrullDim jc.space ≤ e)
    (t : Ext (unitSheaf (X := jc.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        (2 * e) →+ ZMod ℓ) (ht : IsGoodTrace ℓ k e f jc t) :
    Ext.IsDualityPerfect (unitSheaf (X := jc.space) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        (2 * e) t ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
          (unitSheaf (X := W) ℓ)) ∧
      ∀ q, 2 * e < q → Subsingleton (Ext
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
          (unitSheaf (X := W) ℓ)) q) :=
  isDualityPerfect_unitSheaf_of_isGoodTraceAux ℓ hpurity hcore e e W f jc hdim t le_rfl ht

/-- The compactification of a proper `X` by itself: `Λ_X ≅ 𝟙_! Λ_X`. -/
def unitSheafIsoExtensionByZeroId (X : Scheme.{u}) :
    unitSheaf (X := X) ℓ ≅ (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (𝟙 X)).obj
      (unitSheaf (X := X) ℓ) :=
  ((etaleModuleExtensionByZeroIdIso (ZMod ℓ) X).app (unitSheaf (X := X) ℓ)).symm

/-- **Poincaré duality with lisse coefficients on a connected smooth proper variety.** Let `X` be
connected, smooth of relative dimension `d` and proper over an algebraically closed field `k`,
of dimension at most `d`, and `t` an injective trace on `H^{2d}(X, Λ)`. Given local purity, the
elementary-fibration core `hcore`, that every injective trace on `H^{2d}(T, Λ)` is good (for the
compactification of `T` by itself) for every connected finite étale `T → X`, and
`#H^{2d}(T, Λ) = #H^{2d}(X, Λ)` for those `T`, duality holds at every locally constant sheaf of
finite type `F`: `Ext^q(Λ, F) × Ext^{2d-q}(F, Λ) → Ext^{2d}(Λ, Λ) → Λ` is perfect. -/
theorem isDualityPerfect_of_isFiniteTypeLocallyConstant_of_smooth_proper
    (hpurity : LocalPurity ℓ k)
    (hcore : ∀ (e : ℕ) (W : Scheme.{u}) (f : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension e f]
      [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
      (jc : CompactificationOf (Over.mk f)), topologicalKrullDim jc.space ≤ e →
      ∀ (m : ℕ) (t : Ext (unitSheaf (X := jc.space) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
          (2 * e) →+ ZMod ℓ), e ≤ m → IsGoodTraceAux ℓ k m e f jc t →
      ∃ W₀ : W.Opens, Dense (W₀ : Set W) ∧
        Ext.IsDualityPerfect (unitSheaf (X := jc.space) ℓ)
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
          (2 * e) t ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
            ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) W₀.ι).obj
              (unitSheaf (X := W) ℓ))) ∧
        ∀ q, 2 * e < q → Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ)
          jc.immersion).obj ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) W₀.ι).obj
            (unitSheaf (X := W) ℓ)))
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
            (unitSheaf (X := W) ℓ)) q))
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (d : ℕ) [SmoothOfRelativeDimension d f]
    [ConnectedSpace X] (hdim : topologicalKrullDim X ≤ d)
    (t : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) (2 * d) →+ ZMod ℓ) (ht : Function.Injective t)
    (hgood : ∀ (T : Scheme.{u}) (π : T ⟶ X) [IsFinite π] [Etale π] [ConnectedSpace T]
      (t' : Ext (unitSheaf (X := T) ℓ) (unitSheaf ℓ) (2 * d) →+ ZMod ℓ), Function.Injective t' →
        IsGoodTrace ℓ k d (π ≫ f) (CompactificationOf.ofProper (π ≫ f))
          (Ext.transportTrace t' (Iso.refl _) (unitSheafIsoExtensionByZeroId ℓ T)))
    (hcard : ∀ (T : Scheme.{u}) (π : T ⟶ X) [IsFinite π] [Etale π] [ConnectedSpace T],
      Finite (Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) (2 * d)) ∧
        Nat.card (Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) (2 * d)) =
          Nat.card (Ext (unitSheaf (X := X) ℓ) (unitSheaf (X := X) ℓ) (2 * d)))
    (F : EtaleModules.{u, 0} (ZMod ℓ) X)
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) X.smallEtaleTopology F) :
    Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) (unitSheaf ℓ) (2 * d) t F := by
  refine isDualityPerfect_of_isFiniteTypeLocallyConstant_of_proper f d hdim t ht hcard
    (fun T π _ _ _ t' ht' => ?_) F hF
  have : IsProper (π ≫ f) := inferInstance
  have : SmoothOfRelativeDimension d (π ≫ f) := by rw [← zero_add d]; infer_instance
  have : Smooth (π ≫ f) := SmoothOfRelativeDimension.smooth d (π ≫ f)
  have : CompactSpace T := ⟨by
    simpa using QuasiCompact.isCompact_preimage (f := π ≫ f) Set.univ isOpen_univ isCompact_univ⟩
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (π ≫ f)
  have : IsNoetherian T := ⟨⟩
  have : IrreducibleSpace T := irreducibleSpace_of_smooth_of_connectedSpace (π ≫ f)
  obtain ⟨x⟩ := (‹ConnectedSpace T›).toNonempty
  have : Nonempty T := ⟨x⟩
  have hdimT : topologicalKrullDim (CompactificationOf.ofProper (π ≫ f)).space ≤ d :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field d (π ≫ f)).le
  have h := isDualityPerfect_unitSheaf_of_isGoodTrace ℓ hpurity hcore d (π ≫ f)
    (CompactificationOf.ofProper (π ≫ f)) hdimT _ (hgood T π t' ht')
  refine (Ext.isDualityPerfect_transport_iff t' (Iso.refl _)
    (unitSheafIsoExtensionByZeroId ℓ T) _).2 ?_
  exact Ext.isDualityPerfect_of_iso (unitSheafIsoExtensionByZeroId ℓ T).symm h.1

end Stacks.EtaleCohomology
