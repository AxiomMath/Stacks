module

public import StacksFrontier.Algebra.Homology.TwoPeriodicObjectComplex
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Additivity
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.CoherentSupportDimension
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexHomologyCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapClosedSubscheme
public import StacksFrontier.CategoryTheory.Abelian.KZeroRealisation
public import StacksFrontier.KTheory.SerreQuotient

/-!
# Equal classes in the K-group of a dimension layer give rationally equivalent cycles

Let `X` be locally of finite type over the base scheme of chapter 42 of the Stacks Project and
let `A` and `B` be coherent `𝒪_X`-modules whose supports have delta-dimension at most `k`, read
as objects of `Coh_{≤k+1}(X)`. This file proves that if `[A] = [B]` in `K₀(Coh_{≤k+1}(X))` then
the `k`-cycles `[A]_k` and `[B]_k` are rationally equivalent.

This is the step of [Stacks, Tag 02SC] that its proof takes from [Stacks, Tag 02MX] part (2) and
[Stacks, Tag 02SB]: part (2) of 02MX realises the equality `[A] = [B]` by a `(2, 1)`-periodic
complex `(ℱ, φ, ψ)` in `Coh_{≤k+1}(X)` whose two homology objects are `A` and `B`, and 02SB says
that the `k`-cycles of the two homology sheaves of such a complex are rationally equivalent.

## Main definitions

* `Stacks.Chow.layerToModules` — the underlying `𝒪_X`-module of an object of a dimension layer,
  as a functor.
* `Stacks.Chow.layerCycleOfLE` — the `k`-cycle of an object of the layer `Coh_{≤b}(X)`, given a
  bound `k` on the delta-dimension of its support. For `b = k` this is
  `Stacks.Chow.dimensionLayerCycle`; the case `b = k + 1` is the one 02SC needs, and is the
  reason the bound is a separate argument.

## Main results

* `Stacks.Chow.layerCycleOfLE_add` — the cycle is additive along a short exact sequence of the
  layer all of whose terms satisfy the bound.
* `Stacks.Chow.layerCycleOfLE_eq_zero_of_le_pred` — the cycle of an object whose support has
  delta-dimension at most `k - 1` vanishes.
* `Stacks.Chow.rationallyEquivalent_layerCycleOfLE_of_mk_eq` — the statement above.

## Implementation notes

The periodic complex that [Stacks, Tag 02MX] part (2) produces lives in `Coh_{≤k+1}(X)`, whereas
[Stacks, Tag 02SB] is stated for a `ZMod 2`-indexed cochain complex of `𝒪_X`-modules. The passage
between them is `Stacks.Chow.layerToModules`, the composite of the two full-subcategory
inclusions, which is exact, hence preserves homology: `CategoryTheory.twoPeriodicObjectComplex`
assembles the cochain complex out of the two pushed-forward endomorphisms, and
`CategoryTheory.ShortComplex.mapHomologyIso` identifies its homology objects with the images of
the homology objects of the periodic complex. Both identifications are given their own `def`s,
`Stacks.Chow.layerPeriodicHomologyIsoZero` and `Stacks.Chow.layerPeriodicHomologyIsoOne`.

The two hypotheses of 02SB on the supports are read off those identifications: the support of a
module is an isomorphism invariant, and a delta-dimension bound on the support is the pointwise
bound on the relative dimension that 02SB asks for.

## References

* [Stacks Project, Tag 02MX](https://stacks.math.columbia.edu/tag/02MX)
* [Stacks Project, Tag 02QZ](https://stacks.math.columbia.edu/tag/02QZ)
* [Stacks Project, Tag 02S8](https://stacks.math.columbia.edu/tag/02S8)
* [Stacks Project, Tag 02SB](https://stacks.math.columbia.edu/tag/02SB)
* [Stacks Project, Tag 02SC](https://stacks.math.columbia.edu/tag/02SC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]

/-! ### The underlying module of an object of a layer -/

/-- The underlying `𝒪_X`-module of an object of the dimension layer `Coh_{≤b}(X)`, as a functor:
the composite of the inclusion into all coherent modules with the inclusion of those into all
`𝒪_X`-modules. -/
def layerToModules (b : ℤ) : CoherentModulesDimLE C f b ⥤ X.Modules :=
  (coherentModulesDimLE C f b).ι ⋙ (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι

/-- The functor `layerToModules` sends an object of `Coh_{≤b}(X)` to its underlying
`𝒪_X`-module. -/
@[simp]
theorem layerToModules_obj (b : ℤ) (A : CoherentModulesDimLE C f b) :
    (layerToModules C f b).obj A = A.obj.obj :=
  rfl

/-- The functor `layerToModules` preserves finite limits; it is left exact. -/
instance preservesFiniteLimits_layerToModules (b : ℤ) :
    PreservesFiniteLimits (layerToModules C f b) :=
  inferInstanceAs (PreservesFiniteLimits
    ((coherentModulesDimLE C f b).ι ⋙ (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι))

/-- The functor `layerToModules` preserves finite colimits; it is right exact. -/
instance preservesFiniteColimits_layerToModules (b : ℤ) :
    PreservesFiniteColimits (layerToModules C f b) :=
  inferInstanceAs (PreservesFiniteColimits
    ((coherentModulesDimLE C f b).ι ⋙ (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι))

/-- The functor `layerToModules` is an additive functor. -/
instance additive_layerToModules (b : ℤ) : (layerToModules C f b).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The underlying module of an object of a dimension layer is coherent, at the spelling the
cycle constructions use. -/
theorem isCoherent_layerToModules (b : ℤ) (A : CoherentModulesDimLE C f b) :
    _root_.SheafOfModules.IsCoherent A.obj.obj :=
  AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent A.obj.property

/-- A short exact sequence of a dimension layer stays short exact in `𝒪_X`-modules. -/
theorem shortExact_map_layerToModules (b : ℤ)
    ⦃S : ShortComplex (CoherentModulesDimLE C f b)⦄ (hS : S.ShortExact) :
    (S.map (layerToModules C f b)).ShortExact :=
  hS.map_of_exact _

/-! ### The cycle of an object of a layer -/

/-- The `k`-cycle `[A]_k` of an object `A` of the dimension layer `Coh_{≤b}(X)`, given a bound `k`
on the delta-dimension of its support. The bound is phrased as membership in
`Stacks.Chow.coherentModulesDimLE C f k`, which carries the coherence instance that forming the
support of the module needs. -/
def layerCycleOfLE (k : ℤ) {b : ℤ} (A : CoherentModulesDimLE C f b)
    (hA : coherentModulesDimLE C f k A.obj) : CycleGroup C f k :=
  haveI := isCoherent_layerToModules C f b A
  cycleAssociatedToCoherentSheaf C f A.obj.obj k hA

/-- **Stacks 02QZ** on a dimension layer. The cycle is additive along a short exact sequence of
the layer all of whose terms have support of delta-dimension at most `k`. -/
theorem layerCycleOfLE_add (k : ℤ) {b : ℤ} ⦃S : ShortComplex (CoherentModulesDimLE C f b)⦄
    (hS : S.ShortExact) (h₁ : coherentModulesDimLE C f k S.X₁.obj)
    (h₂ : coherentModulesDimLE C f k S.X₂.obj) (h₃ : coherentModulesDimLE C f k S.X₃.obj) :
    layerCycleOfLE C f k S.X₂ h₂ =
      layerCycleOfLE C f k S.X₁ h₁ + layerCycleOfLE C f k S.X₃ h₃ := by
  have i₁ : _root_.SheafOfModules.IsCoherent (S.map (layerToModules C f b)).X₁ :=
    isCoherent_layerToModules C f b S.X₁
  have i₂ : _root_.SheafOfModules.IsCoherent (S.map (layerToModules C f b)).X₂ :=
    isCoherent_layerToModules C f b S.X₂
  have i₃ : _root_.SheafOfModules.IsCoherent (S.map (layerToModules C f b)).X₃ :=
    isCoherent_layerToModules C f b S.X₃
  exact cycleAssociatedToCoherentSheaf_add C f (S.map (layerToModules C f b))
    (shortExact_map_layerToModules C f b hS) k h₁ h₂ h₃

/-- Isomorphic objects of a dimension layer have the same cycle. -/
theorem layerCycleOfLE_eq_of_iso (k : ℤ) {b : ℤ} {A B : CoherentModulesDimLE C f b} (e : A ≅ B)
    (hA : coherentModulesDimLE C f k A.obj) (hB : coherentModulesDimLE C f k B.obj) :
    layerCycleOfLE C f k A hA = layerCycleOfLE C f k B hB := by
  have i₁ : _root_.SheafOfModules.IsCoherent ((layerToModules C f b).obj A) :=
    isCoherent_layerToModules C f b A
  have i₂ : _root_.SheafOfModules.IsCoherent ((layerToModules C f b).obj B) :=
    isCoherent_layerToModules C f b B
  exact cycleAssociatedToCoherentSheaf_eq_of_iso C f ((layerToModules C f b).mapIso e) k hA hB

/-- The `k`-cycle of an object of a dimension layer whose support has delta-dimension at most
`k - 1` vanishes: a point of the support then has relative dimension at most `k - 1`, so it is
not one of the points of relative dimension `k` carrying the coefficients of a `k`-cycle. -/
theorem layerCycleOfLE_eq_zero_of_le_pred (k : ℤ) {b : ℤ} (A : CoherentModulesDimLE C f b)
    (hA : coherentModulesDimLE C f k A.obj)
    (hA' : coherentModulesDimLE C f (k - 1) A.obj) :
    layerCycleOfLE C f k A hA = 0 := by
  have i₁ := isCoherent_layerToModules C f b A
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
  change (cycleAssociatedToCoherentSheaf C f A.obj.obj k hA).1 x = 0
  by_cases hx : relativeDimension C.dimensionFunction f x = k
  · rw [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C f A.obj.obj k hA hx]
    refine sheafMultiplicity_eq_zero_of_notMem_supp A.obj.obj fun hmem => ?_
    have hle := relativeDimension_le_of_mem_supp C f A.obj.obj hA' hmem
    omega
  · exact cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f A.obj.obj k hA hx

/-! ### The periodic complex of an equality of classes -/

/-- The two endomorphisms of the underlying module of a `(2, 1)`-periodic complex of a dimension
layer annihilate each other. -/
theorem layerToModules_map_comp_eq_zero (b : ℤ) {M : CoherentModulesDimLE C f b} {φ ψ : M ⟶ M}
    (hφψ : φ ≫ ψ = 0) :
    (layerToModules C f b).map φ ≫ (layerToModules C f b).map ψ = 0 := by
  rw [← Functor.map_comp, hφψ, Functor.map_zero]

section Periodic

variable {b : ℤ} {M : CoherentModulesDimLE C f b} (φ ψ : M ⟶ M) (hφψ : φ ≫ ψ = 0)
  (hψφ : ψ ≫ φ = 0)

include hφψ hψφ

/-- The `ZMod 2`-indexed cochain complex of `𝒪_X`-modules of a `(2, 1)`-periodic complex of a
dimension layer. -/
def layerPeriodicComplex : CochainComplex X.Modules (ZMod 2) :=
  twoPeriodicObjectComplex ((layerToModules C f b).map φ) ((layerToModules C f b).map ψ)
    (layerToModules_map_comp_eq_zero C f b hφψ) (layerToModules_map_comp_eq_zero C f b hψφ)

/-- Every term of the cochain complex is the underlying module of `M`. -/
def layerPeriodicComplexXIso (i : ZMod 2) :
    (layerPeriodicComplex C f φ ψ hφψ hψφ).X i ≅ M.obj.obj :=
  Iso.refl _

/-- The homology of the cochain complex in degree `0` is the underlying module of the homology
object `H⁰ = Ker φ / Im ψ` of the periodic complex. -/
def layerPeriodicHomologyIsoZero :
    (layerPeriodicComplex C f φ ψ hφψ hψφ).homology 0 ≅
      (layerToModules C f b).obj (ShortComplex.mk ψ φ hψφ).homology :=
  twoPeriodicObjectComplexHomologyIsoZero ((layerToModules C f b).map φ)
      ((layerToModules C f b).map ψ) (layerToModules_map_comp_eq_zero C f b hφψ)
      (layerToModules_map_comp_eq_zero C f b hψφ) ≪≫
    (ShortComplex.mk ψ φ hψφ).mapHomologyIso (layerToModules C f b)

/-- The homology of the cochain complex in degree `1` is the underlying module of the homology
object `H¹ = Ker ψ / Im φ` of the periodic complex. -/
def layerPeriodicHomologyIsoOne :
    (layerPeriodicComplex C f φ ψ hφψ hψφ).homology 1 ≅
      (layerToModules C f b).obj (ShortComplex.mk φ ψ hφψ).homology :=
  twoPeriodicObjectComplexHomologyIsoOne ((layerToModules C f b).map φ)
      ((layerToModules C f b).map ψ) (layerToModules_map_comp_eq_zero C f b hφψ)
      (layerToModules_map_comp_eq_zero C f b hψφ) ≪≫
    (ShortComplex.mk φ ψ hφψ).mapHomologyIso (layerToModules C f b)

end Periodic

/-- **The step of [Stacks, Tag 02SC] that [Stacks, Tag 02MX] part (2) and [Stacks, Tag 02SB]
supply.** Let `A` and `B` be objects of the dimension layer `Coh_{≤k+1}(X)` whose supports have
delta-dimension at most `k`. If `A` and `B` have the same class in `K₀(Coh_{≤k+1}(X))`, then the
`k`-cycles `[A]_k` and `[B]_k` are rationally equivalent. -/
theorem rationallyEquivalent_layerCycleOfLE_of_mk_eq (k : ℤ)
    (A B : CoherentModulesDimLE C f (k + 1)) (hA : coherentModulesDimLE C f k A.obj)
    (hB : coherentModulesDimLE C f k B.obj)
    (h : KZero.mk (CoherentModulesDimLE C f (k + 1)) A =
      KZero.mk (CoherentModulesDimLE C f (k + 1)) B) :
    RationallyEquivalent C f k (layerCycleOfLE C f k A hA) (layerCycleOfLE C f k B hB) := by
  have hAc := isCoherent_layerToModules C f (k + 1) A
  have hBc := isCoherent_layerToModules C f (k + 1) B
  obtain ⟨M, φ, ψ, hφψ, hψφ, ⟨e₀⟩, ⟨e₁⟩⟩ := KZero.mk_eq_mk_iff_exists_homology_iso.1 h
  have hMc := isCoherent_layerToModules C f (k + 1) M
  -- the two homology objects of the cochain complex, identified with `B` and with `A`
  have iso₀ : (layerPeriodicComplex C f φ ψ hφψ hψφ).homology 0 ≅ B.obj.obj :=
    layerPeriodicHomologyIsoZero C f φ ψ hφψ hψφ ≪≫ (layerToModules C f (k + 1)).mapIso e₁
  have iso₁ : (layerPeriodicComplex C f φ ψ hφψ hψφ).homology 1 ≅ A.obj.obj :=
    layerPeriodicHomologyIsoOne C f φ ψ hφψ hψφ ≪≫ (layerToModules C f (k + 1)).mapIso e₀
  have hHk : ∀ (i : ZMod 2) (x : X), x ∈ _root_.SheafOfModules.supp
      ((layerPeriodicComplex C f φ ψ hφψ hψφ).homology i) →
      relativeDimension C.dimensionFunction f x ≤ k := by
    intro i x hx
    fin_cases i
    · exact relativeDimension_le_of_mem_supp C f B.obj.obj hB
        (_root_.SheafOfModules.supp_eq_of_iso iso₀ ▸ hx)
    · exact relativeDimension_le_of_mem_supp C f A.obj.obj hA
        (_root_.SheafOfModules.supp_eq_of_iso iso₁ ▸ hx)
  obtain ⟨c₀, c₁, d₀, d₁, hrat⟩ := rationallyEquivalent_cycles_of_twoPeriodicComplex C f
    M.obj.obj (layerPeriodicComplex C f φ ψ hφψ hψφ)
    (layerPeriodicComplexXIso C f φ ψ hφψ hψφ) k M.property hHk
  rw [cycleAssociatedToCoherentSheaf_eq_of_iso C f iso₀ k d₀ hB,
    cycleAssociatedToCoherentSheaf_eq_of_iso C f iso₁ k d₁ hA] at hrat
  have hneg := neg_mem hrat
  rw [neg_sub] at hneg
  exact hneg

end Stacks.Chow

end
