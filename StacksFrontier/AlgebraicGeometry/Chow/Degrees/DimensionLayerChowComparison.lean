module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerKGroup
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerPeriodicCycle
public import StacksFrontier.KTheory.SerreQuotient

/-!
# The homomorphism `Bₖ(X) ⟶ CH_k(X)` of Stacks 02SC

Let `X` be locally of finite type over the base scheme of chapter 42 of the Stacks Project, and
let `Bₖ(X)` be the subgroup `Stacks.Chow.coherentDimensionLayerImage` of
`K₀(Coh_{≤k+1}/Coh_{≤k-1})` built in
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerKGroup`.

Stacks 02SC asserts that the map `CH_k(X) ⟶ K₀(Coh_{≤k+1}/Coh_{≤k-1})` of Stacks 0FDS is a
bijection onto `Bₖ(X)`; what is proved here is the half of that statement which makes the
inverse `Bₖ(X) ⟶ CH_k(X)` exist, namely that an element of `K₀(Coh_{≤k}(X))` whose class in
`K₀(Coh_{≤k+1}/Coh_{≤k-1})` vanishes has rationally trivial `k`-cycle. See the implementation
notes for what is not proved.

## Main definitions

* `Stacks.Chow.layerChowClass` — the homomorphism `K₀(Coh_{≤k}(X)) ⟶ CH_k(X)`, `[A] ↦ [[A]_k]`.
* `Stacks.Chow.layerWideningClass` — the homomorphism
  `K₀(Coh_{≤k}(X)) ⟶ K₀(Coh_{≤k+1}/Coh_{≤k-1})` whose image is `Bₖ(X)`.
* `Stacks.Chow.lowerDimensionClassToLayer` — an object of `Coh_{≤k+1}(X)` of support dimension at
  most `k - 1`, read as an object of `Coh_{≤k}(X)`.
* `Stacks.Chow.layerChowClassOfKer` — the homomorphism `Bₖ(X) ⟶ CH_k(X)` before restricting to
  `Bₖ(X)`, i.e. on the quotient of `K₀(Coh_{≤k}(X))` by the kernel of
  `Stacks.Chow.layerWideningClass`.
* `Stacks.Chow.coherentDimensionLayerImageChowHom` — the homomorphism `Bₖ(X) ⟶ CH_k(X)` of
  Stacks 02SC.

## Main results

* `Stacks.Chow.range_layerWideningClass` — the image of `Stacks.Chow.layerWideningClass` is
  `Bₖ(X)`.
* `Stacks.Chow.layerChowClass_eq_zero_of_layerWideningClass_eq_zero` — **Stacks 02SC**, the
  comparison: a class of `K₀(Coh_{≤k}(X))` killed in `K₀(Coh_{≤k+1}/Coh_{≤k-1})` has rationally
  trivial `k`-cycle.
* `Stacks.Chow.coherentDimensionLayerImageChowHom_coherentDimensionKZeroMk` — the homomorphism
  `Bₖ(X) ⟶ CH_k(X)` sends the class of a coherent module `F` with `dim_δ(Supp F) ≤ k` to the
  class of the cycle `[F]_k`.

## Implementation notes

**What of Stacks 02SC is proved.** The tag's bijection `CH_k(X) ⟶ Bₖ(X)` is the map of
Stacks 0FDS restricted to its image. Neither that map nor the surjectivity onto `Bₖ(X)` is
available: both rest on the homomorphism `Z_k(X) ⟶ K₀(Coh_{≤k}/Coh_{≤k-1})` of Stacks 02S9,
which this development does not have — see the "What is not proved" section of
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerCycleClass`, where the other of the
two mutually inverse maps of 02S9 is built. What is proved is the injectivity half, in the form
that does not mention the missing map: the composite
`K₀(Coh_{≤k}(X)) ⟶ Z_k(X) ⟶ CH_k(X)` kills the kernel of
`K₀(Coh_{≤k}(X)) ⟶ K₀(Coh_{≤k+1}/Coh_{≤k-1})`. Since the latter homomorphism is onto `Bₖ(X)`,
that is exactly what makes the map `Bₖ(X) ⟶ CH_k(X)` of the tag's statement — the one
[Stacks, Tag 02SX] refers to — exist and be well defined.

The argument is the source's. Stacks 02MX (1), as `KZero.exact_map_ι_map_localization`, turns the
vanishing into an object of `Coh_{≤k-1}(X)` correcting the class to one that already dies in
`K₀(Coh_{≤k+1}(X))`; the correction does not change the `k`-cycle class, because a module of
support dimension at most `k - 1` has zero `k`-cycle. The corrected class is a difference
`[A] - [B]` of the classes of two objects, so `[A] = [B]` in `K₀(Coh_{≤k+1}(X))`, and
`Stacks.Chow.rationallyEquivalent_layerCycleOfLE_of_mk_eq` — Stacks 02MX (2) followed by
Stacks 02SB — says that `[A]_k` and `[B]_k` are then rationally equivalent.

Several functors are given additivity and exactness instances here, and the inclusions of the
dimension-bounded subcategories are made local instances. Those instances are the reason this
material is a module of its own rather than a further section of
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerKGroup`: in scope there they change
the elaborated statements of that file's declarations.

## References

* [Stacks Project, Tag 02MX](https://stacks.math.columbia.edu/tag/02MX)
* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
* [Stacks Project, Tag 02SB](https://stacks.math.columbia.edu/tag/02SB)
* [Stacks Project, Tag 02SC](https://stacks.math.columbia.edu/tag/02SC)
* [Stacks Project, Tag 02SX](https://stacks.math.columbia.edu/tag/02SX)
* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-! ### The homomorphism `Bₖ(X) ⟶ CH_k(X)` of Stacks 02SC -/

attribute [local instance] ObjectProperty.preservesFiniteLimits_ι
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass

/-- The inclusion `Coh_{≤k}(X) ⥤ Coh_{≤k+1}(X)` is an additive functor. -/
instance additive_dimensionLayerInclusion (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) : (dimensionLayerInclusion C f k).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The quotient functor `Coh_{≤b}(X) ⥤ Coh_{≤b}(X)/Coh_{≤a}(X)` is an additive functor. -/
instance additive_coherentDimensionQuotientQ (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (a b : ℤ) :
    (lowerDimensionClass C f a b).isoModSerre.Q.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The homomorphism `K₀(Coh_{≤k}(X)) ⟶ CH_k(X)`, `[A] ↦ [[A]_k]`: the `k`-cycle of a coherent
module of support dimension at most `k` is additive along short exact sequences, so its class in
the Chow group descends to the Grothendieck group. -/
def layerChowClass (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) :
    KZero (CoherentModulesDimLE C f k) →+ chowGroup C f k :=
  KZero.lift
    (fun A => QuotientAddGroup.mk' (rationalEquivalences C f k) (layerCycleOfLE C f k A A.property))
    fun _ hS => by
      rw [layerCycleOfLE_add C f k hS _ _ _, map_add]

/-- `Stacks.Chow.layerChowClass` sends the class of `A` to the class of the cycle `[A]_k`. -/
@[simp]
theorem layerChowClass_mk (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (A : CoherentModulesDimLE C f k) :
    layerChowClass C f k (KZero.mk _ A) =
      QuotientAddGroup.mk' (rationalEquivalences C f k) (layerCycleOfLE C f k A A.property) :=
  KZero.lift_mk _ _ A

/-- The homomorphism `K₀(Coh_{≤k}(X)) ⟶ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` whose image is the
subgroup `Bₖ(X)`: pass to the layer `(k-1, k]` and then widen the upper bound. -/
def layerWideningClass (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) :
    KZero (CoherentModulesDimLE C f k) →+ coherentDimensionKZero C f (k - 1) (k + 1) :=
  (coherentDimensionLayerHom C f k).comp
    (KZero.map (lowerDimensionClass C f (k - 1) k).isoModSerre.Q)

/-- `Stacks.Chow.layerWideningClass` sends the class of `F` to its class in
`K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`. -/
@[simp]
theorem layerWideningClass_mk (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (k : ℤ) (F : CoherentModulesDimLE C f k) :
    layerWideningClass C f k (KZero.mk _ F) =
      coherentDimensionKZeroMk C f (k - 1) (k + 1) ((dimensionLayerInclusion C f k).obj F) :=
  (congrArg (coherentDimensionLayerHom C f k) (KZero.map_mk _ F)).trans
    (coherentDimensionLayerHom_apply_mk C f k F)

/-- `Stacks.Chow.layerWideningClass`, factored the other way round: first include `Coh_{≤k}(X)`
into `Coh_{≤k+1}(X)`, then pass to the layer `(k-1, k+1]`. -/
theorem layerWideningClass_eq_map_comp_map (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) :
    layerWideningClass C f k =
      (KZero.map (lowerDimensionClass C f (k - 1) (k + 1)).isoModSerre.Q).comp
        (KZero.map (dimensionLayerInclusion C f k)) :=
  KZero.hom_ext fun F => by
    rw [layerWideningClass_mk, AddMonoidHom.comp_apply, KZero.map_mk, KZero.map_mk]
    rfl

/-- The image of `Stacks.Chow.layerWideningClass` is the subgroup `Bₖ(X)`: the homomorphism
`K₀(Coh_{≤k}(X)) ⟶ K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` is surjective by Stacks 02MX (1). -/
theorem range_layerWideningClass (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (k : ℤ) :
    (layerWideningClass C f k).range = coherentDimensionLayerImage C f k := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨a, rfl⟩
    exact ⟨KZero.map (lowerDimensionClass C f (k - 1) k).isoModSerre.Q a, rfl⟩
  · rintro _ ⟨b, rfl⟩
    obtain ⟨a, ha⟩ := KZero.surjective_map_localization (lowerDimensionClass C f (k - 1) k)
      (lowerDimensionClass C f (k - 1) k).isoModSerre.Q b
    exact ⟨a, by rw [layerWideningClass, AddMonoidHom.comp_apply, ha]⟩

/-- An object of `Coh_{≤k+1}(X)` of support dimension at most `k - 1`, read as an object of
`Coh_{≤k}(X)`. -/
def lowerDimensionClassToLayer (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (k : ℤ) :
    (lowerDimensionClass C f (k - 1) (k + 1)).FullSubcategory ⥤ CoherentModulesDimLE C f k :=
  ObjectProperty.lift (coherentModulesDimLE C f k)
    ((lowerDimensionClass C f (k - 1) (k + 1)).ι ⋙ (coherentModulesDimLE C f (k + 1)).ι)
    fun Z => coherentModulesDimLE_le_coherentModulesDimLE C f (by omega) _ Z.property

/-- `Stacks.Chow.lowerDimensionClassToLayer` preserves finite limits. -/
instance preservesFiniteLimits_lowerDimensionClassToLayer (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) :
    PreservesFiniteLimits (lowerDimensionClassToLayer C f k) :=
  have : PreservesFiniteLimits
      (lowerDimensionClassToLayer C f k ⋙ (coherentModulesDimLE C f k).ι) :=
    inferInstanceAs (PreservesFiniteLimits
      ((lowerDimensionClass C f (k - 1) (k + 1)).ι ⋙ (coherentModulesDimLE C f (k + 1)).ι))
  preservesFiniteLimits_of_reflects_of_preserves _ (coherentModulesDimLE C f k).ι

/-- `Stacks.Chow.lowerDimensionClassToLayer` preserves finite colimits. -/
instance preservesFiniteColimits_lowerDimensionClassToLayer (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) :
    PreservesFiniteColimits (lowerDimensionClassToLayer C f k) :=
  have : PreservesFiniteColimits
      (lowerDimensionClassToLayer C f k ⋙ (coherentModulesDimLE C f k).ι) :=
    inferInstanceAs (PreservesFiniteColimits
      ((lowerDimensionClass C f (k - 1) (k + 1)).ι ⋙ (coherentModulesDimLE C f (k + 1)).ι))
  preservesFiniteColimits_of_reflects_of_preserves _ (coherentModulesDimLE C f k).ι

/-- `Stacks.Chow.lowerDimensionClassToLayer` is an additive functor. -/
instance additive_lowerDimensionClassToLayer (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) : (lowerDimensionClassToLayer C f k).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Reading an object of support dimension at most `k - 1` inside `Coh_{≤k}(X)` and then back
inside `Coh_{≤k+1}(X)` returns it, so the two induced maps of Grothendieck groups agree. -/
theorem map_dimensionLayerInclusion_comp_map_lowerDimensionClassToLayer (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) :
    (KZero.map (dimensionLayerInclusion C f k)).comp
        (KZero.map (lowerDimensionClassToLayer C f k)) =
      KZero.map (lowerDimensionClass C f (k - 1) (k + 1)).ι :=
  KZero.hom_ext fun Z => by
    rw [AddMonoidHom.comp_apply, KZero.map_mk, KZero.map_mk, KZero.map_mk]
    rfl

/-- The `k`-cycle of an object of support dimension at most `k - 1` is rationally trivial: it is
zero. -/
theorem layerChowClass_comp_map_lowerDimensionClassToLayer (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) :
    (layerChowClass C f k).comp (KZero.map (lowerDimensionClassToLayer C f k)) = 0 :=
  KZero.hom_ext fun Z => by
    rw [AddMonoidHom.comp_apply, KZero.map_mk, layerChowClass_mk, AddMonoidHom.zero_apply,
      layerCycleOfLE_eq_zero_of_le_pred C f k ((lowerDimensionClassToLayer C f k).obj Z) _
        Z.property, map_zero]

/-- **Stacks 02SC, the comparison.** An element of `K₀(Coh_{≤k}(X))` whose class in
`K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` vanishes has rationally trivial `k`-cycle.

This is the content of Stacks 02SC: by Stacks 02MX (1) the vanishing produces an object of
`Coh_{≤k-1}(X)` correcting the element to one that already dies in `K₀(Coh_{≤k+1}(X))`, by
Stacks 02MX (2) that corrected element is the difference of the classes of the two homology
objects of a `(2, 1)`-periodic complex of `Coh_{≤k+1}(X)`, and by Stacks 02SB the `k`-cycles of
those two homology objects are rationally equivalent. -/
@[stacks 02SC "the comparison: a class killed in `K₀(Coh_{≤k+1}/Coh_{≤k-1})` has trivial cycle"]
theorem layerChowClass_eq_zero_of_layerWideningClass_eq_zero (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (a : KZero (CoherentModulesDimLE C f k))
    (ha : layerWideningClass C f k a = 0) : layerChowClass C f k a = 0 := by
  rw [layerWideningClass_eq_map_comp_map, AddMonoidHom.comp_apply] at ha
  obtain ⟨c, hc⟩ := (KZero.exact_map_ι_map_localization (lowerDimensionClass C f (k - 1) (k + 1))
    (lowerDimensionClass C f (k - 1) (k + 1)).isoModSerre.Q _).1 ha
  set a' := a - KZero.map (lowerDimensionClassToLayer C f k) c with ha'
  have hzero : KZero.map (dimensionLayerInclusion C f k) a' = 0 := by
    rw [ha', map_sub, ← AddMonoidHom.comp_apply,
      map_dimensionLayerInclusion_comp_map_lowerDimensionClassToLayer, hc, sub_self]
  have hcorr : layerChowClass C f k a = layerChowClass C f k a' := by
    rw [ha', map_sub, ← AddMonoidHom.comp_apply,
      layerChowClass_comp_map_lowerDimensionClassToLayer, AddMonoidHom.zero_apply, sub_zero]
  obtain ⟨Y, Z, hYZ⟩ := KZero.exists_eq_mk_sub_mk a'
  rw [hYZ, map_sub, KZero.map_mk, KZero.map_mk, sub_eq_zero] at hzero
  have hrat := rationallyEquivalent_layerCycleOfLE_of_mk_eq C f k
    ((dimensionLayerInclusion C f k).obj Y) ((dimensionLayerInclusion C f k).obj Z)
    Y.property Z.property hzero
  rw [hcorr, hYZ, map_sub, layerChowClass_mk, layerChowClass_mk, ← map_sub,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact hrat

/-- **Stacks 02SC, the map `Bₖ(X) ⟶ CH_k(X)`, before restricting to `Bₖ(X)`.** -/
def layerChowClassOfKer (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) :
    KZero (CoherentModulesDimLE C f k) ⧸ (layerWideningClass C f k).ker →+ chowGroup C f k :=
  QuotientAddGroup.lift _ (layerChowClass C f k) fun a ha =>
    layerChowClass_eq_zero_of_layerWideningClass_eq_zero C f k a ha

/-- **Stacks 02SC.** The homomorphism `Bₖ(X) ⟶ CH_k(X)`. On the class of a coherent
`𝒪_X`-module `A` with `dim_δ(Supp A) ≤ k` it is the class of the `k`-cycle `[A]_k`; this is
`Stacks.Chow.coherentDimensionLayerImageChowHom_apply` below. It exists because the `k`-cycle of
an element of `K₀(Coh_{≤k}(X))` killed by the map to `K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` is
rationally trivial, which is
`Stacks.Chow.layerChowClass_eq_zero_of_layerWideningClass_eq_zero`. -/
@[stacks 02SC "the homomorphism `Bₖ(X) → CH_k(X)` the bijection of the tag inverts"]
def coherentDimensionLayerImageChowHom (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) :
    coherentDimensionLayerImage C f k →+ chowGroup C f k :=
  (layerChowClassOfKer C f k).comp
    ((QuotientAddGroup.quotientKerEquivRange (layerWideningClass C f k)).symm.toAddMonoidHom.comp
      (AddSubgroup.inclusion (le_of_eq (range_layerWideningClass C f k).symm)))

/-- The homomorphism `Bₖ(X) ⟶ CH_k(X)` sends the image of an element `a` of `K₀(Coh_{≤k}(X))`
to the class of the `k`-cycle of `a`. This is the characterisation of
`Stacks.Chow.coherentDimensionLayerImageChowHom` that
`Stacks.Chow.coherentDimensionLayerImageChowHom_coherentDimensionKZeroMk`, the statement of
Stacks 02SC, is read off. -/
theorem coherentDimensionLayerImageChowHom_apply (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (a : KZero (CoherentModulesDimLE C f k))
    (ha : layerWideningClass C f k a ∈ coherentDimensionLayerImage C f k) :
    coherentDimensionLayerImageChowHom C f k ⟨layerWideningClass C f k a, ha⟩ =
      layerChowClass C f k a := by
  have h : (QuotientAddGroup.quotientKerEquivRange (layerWideningClass C f k)).symm
      ⟨layerWideningClass C f k a, ⟨a, rfl⟩⟩ = QuotientAddGroup.mk a := by
    apply (QuotientAddGroup.quotientKerEquivRange (layerWideningClass C f k)).injective
    rw [AddEquiv.apply_symm_apply]
    rfl
  exact congrArg (layerChowClassOfKer C f k) h

/-- **Stacks 02SC.** The homomorphism `Bₖ(X) ⟶ CH_k(X)` sends the class of a coherent
`𝒪_X`-module `F` with `dim_δ(Supp F) ≤ k`, read in the layer `(k-1, k+1]`, to the class of the
`k`-cycle `[F]_k`. -/
@[stacks 02SC "the value of `Bₖ(X) → CH_k(X)` on the class of a coherent module"]
theorem coherentDimensionLayerImageChowHom_coherentDimensionKZeroMk (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (F : CoherentModulesDimLE C f k)
    (hF : coherentDimensionKZeroMk C f (k - 1) (k + 1) ((dimensionLayerInclusion C f k).obj F) ∈
      coherentDimensionLayerImage C f k) :
    coherentDimensionLayerImageChowHom C f k
        ⟨coherentDimensionKZeroMk C f (k - 1) (k + 1) ((dimensionLayerInclusion C f k).obj F),
          hF⟩ =
      QuotientAddGroup.mk' (rationalEquivalences C f k) (layerCycleOfLE C f k F F.property) := by
  have := coherentDimensionLayerImageChowHom_apply C f k (KZero.mk _ F)
    ((layerWideningClass_mk C f k F).symm ▸ hF)
  simpa only [layerChowClass_mk, layerWideningClass_mk] using this

end Stacks.Chow
