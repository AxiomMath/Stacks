module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Localization
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerKGroup

/-!
# Computing in the K-group of a dimension layer

Let `X` be locally of finite type over the base scheme of chapter 42 of the Stacks Project. This
file is the calculus of `Stacks.Chow.coherentDimensionKZero`, the Grothendieck group of the layer
`(a, b]` of coherent `𝒪_X`-modules: the class of a module is additive along a short exact
sequence, it is an isomorphism invariant, it vanishes when the support has delta-dimension at
most `a`, and it lies in the subgroup `Bₖ(X)` of Stacks 02SC when the support has delta-dimension
at most `k`. A short complex in `Coh_{≤b}(𝒪_X)` is short exact as soon as its image in
`Mod(𝒪_X)` is.

## Main results

* `Stacks.Chow.shortExact_of_shortExact_map_ι` — a weak Serre subcategory inherits short
  exactness from the ambient category.
* `Stacks.Chow.shortExact_coherentModulesDimLE` — the same for a dimension-bounded subcategory of
  coherent modules, through both inclusions at once.
* `Stacks.Chow.coherentDimensionKZeroMk_add` — additivity of the class along a short exact
  sequence.
* `Stacks.Chow.coherentDimensionKZeroMk_eq_of_iso` — the class is an isomorphism invariant.
* `Stacks.Chow.coherentDimensionKZeroMk_eq_zero` — the class vanishes below the layer.
* `Stacks.Chow.coherentDimensionKZeroMk_mem_coherentDimensionLayerImage` — a module of support
  dimension at most `k` has class in `Bₖ(X)`.

## References

* [Stacks Project, Tag 02S8](https://stacks.math.columbia.edu/tag/02S8)
* [Stacks Project, Tag 02SC](https://stacks.math.columbia.edu/tag/02SC)
* [Stacks Project, Tag 02MU](https://stacks.math.columbia.edu/tag/02MU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Short exactness is reflected by a weak Serre subcategory -/

/-- **A weak Serre subcategory inherits short exactness from the ambient category.** -/
theorem shortExact_of_shortExact_map_ι {A : Type*} [Category A] [Abelian A] (B : ObjectProperty A)
    [B.IsWeakSerreClass] {S : ShortComplex B.FullSubcategory} (h : (S.map B.ι).ShortExact) :
    S.ShortExact := by
  have := B.preservesFiniteLimits_ι_of_isWeakSerreClass
  have := B.preservesFiniteColimits_ι_of_isWeakSerreClass
  exact .mk' ((ShortComplex.exact_map_iff_of_faithful S B.ι).1 h.exact)
    (B.ι.mono_of_mono_map h.mono_f) (B.ι.epi_of_epi_map h.epi_g)

variable {X : Scheme.{u}} (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]

/-- **Short exactness in a dimension layer from short exactness of `𝒪_X`-modules.** A short
complex of coherent modules of support dimension at most `b` whose image in `Mod(𝒪_X)` is short
exact is short exact. -/
theorem shortExact_coherentModulesDimLE (b : ℤ) {S : ShortComplex (CoherentModulesDimLE C f b)}
    (h : ((S.map (coherentModulesDimLE C f b).ι).map
      (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι).ShortExact) : S.ShortExact :=
  shortExact_of_shortExact_map_ι (coherentModulesDimLE C f b)
    (shortExact_of_shortExact_map_ι (Stacks.SheafOfModules.coherentModules X.ringCatSheaf) h)

/-! ### The class of a module in the layer -/

/-- **Additivity of the class in the K-group of a layer.** Along a short exact sequence the class
of the middle term is the sum of the classes of the outer terms. -/
theorem coherentDimensionKZeroMk_add (a b : ℤ) {S : ShortComplex (CoherentModulesDimLE C f b)}
    (hS : S.ShortExact) :
    coherentDimensionKZeroMk C f a b S.X₂ =
      coherentDimensionKZeroMk C f a b S.X₁ + coherentDimensionKZeroMk C f a b S.X₃ :=
  KZero.mk_of_shortExact _
    (ObjectProperty.SerreClassLocalization.shortExact_map
      (lowerDimensionClass C f a b).isoModSerre.Q (lowerDimensionClass C f a b) hS)

/-- The class in the K-group of a layer is an isomorphism invariant. -/
theorem coherentDimensionKZeroMk_eq_of_iso (a b : ℤ) {F G : CoherentModulesDimLE C f b}
    (e : F ≅ G) :
    coherentDimensionKZeroMk C f a b F = coherentDimensionKZeroMk C f a b G :=
  KZero.mk_eq_of_iso ((lowerDimensionClass C f a b).isoModSerre.Q.mapIso e)

/-- **A module of support dimension at most `a` has class zero in the layer `(a, b]`.** -/
theorem coherentDimensionKZeroMk_eq_zero (a b : ℤ) (F : CoherentModulesDimLE C f b)
    (hF : coherentModulesDimLE C f a F.obj) :
    coherentDimensionKZeroMk C f a b F = 0 :=
  KZero.mk_eq_zero_of_isZero
    (ObjectProperty.le_kernel_of_isoModSerre_isInvertedBy (lowerDimensionClass C f a b)
      (lowerDimensionClass C f a b).isoModSerre.Q
      (Localization.inverts _ (lowerDimensionClass C f a b).isoModSerre) F hF)

/-- **A module of support dimension at most `k` has class in `Bₖ(X)`**, the image of the K-group
of the layer `(k - 1, k]` in that of the layer `(k - 1, k + 1]`. -/
theorem coherentDimensionKZeroMk_mem_coherentDimensionLayerImage (k : ℤ)
    (F : CoherentModulesDimLE C f (k + 1)) (hF : coherentModulesDimLE C f k F.obj) :
    coherentDimensionKZeroMk C f (k - 1) (k + 1) F ∈ coherentDimensionLayerImage C f k := by
  refine ⟨coherentDimensionKZeroMk C f (k - 1) k ⟨F.obj, hF⟩, ?_⟩
  rw [coherentDimensionLayerHom_apply_mk]
  rfl

end Stacks.Chow

end
