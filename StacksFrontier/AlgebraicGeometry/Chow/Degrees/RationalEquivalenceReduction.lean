module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ChowToDimensionLayer
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerFinitePushforward
public import StacksFrontier.CategoryTheory.Abelian.KZeroRealisation

/-!
# Reducing a cycle rationally equivalent to zero to a finite cover

Let `(S, δ)` be a base situation with a dimension function and let `X` be a scheme locally of
finite type over `S`. [Stacks, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS) asserts that
the homomorphism

`Z_k(X) ⟶ K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) ⟶ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`

of `Stacks.Chow.cycleDimensionLayerWideHom` kills the cycles rationally equivalent to zero. This
file constructs direct image along a finite morphism `π : W ⟶ X` on an arbitrary layer `(a, b]`,
proves it compatible with widening the layer `(k - 1, k]` to `(k - 1, k + 1]`, and shows that for
`X` Noetherian the class in the wide layer of the proper pushforward of a `k`-cycle on `W` is the
direct image of its class over `W`.

## Main definitions

* `Stacks.Chow.coherentDimensionQuotientFinitePushforward` — direct image along a finite morphism
  as a functor between the dimension layers `(a, b]` of the source and the target.
* `Stacks.Chow.coherentDimensionKZeroFinitePushforwardHom` — the induced homomorphism
  `K₀(Coh_{≤b}(W)/Coh_{≤a}(W)) → K₀(Coh_{≤b}(X)/Coh_{≤a}(X))`.

## Main results

* `Stacks.Chow.coherentDimensionKZeroFinitePushforwardHom_mk` — the induced homomorphism sends
  the class of a module to the class of its direct image.
* `Stacks.Chow.cycleDimensionLayerWideHom_properPushforwardHom` — the reduction identity: the
  class in the wide layer over `X` of the proper pushforward of a `k`-cycle `c` on `W` is the
  direct image of the class in the wide layer over `W` of `c`.
* `Stacks.Chow.cycleDimensionLayerWideHom_properPushforwardHom_eq_zero` and
  `Stacks.Chow.cycleDimensionLayerWideHom_eq_zero_of_properPushforwardHom_eq` — if the class of a
  `k`-cycle on `W` in the wide layer vanishes, so does the class of its proper pushforward.

## References

* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
* [Stacks Project, Tag 02SC](https://stacks.math.columbia.edu/tag/02SC)
* [Stacks Project, Tag 0FDR](https://stacks.math.columbia.edu/tag/0FDR)
* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {W X : Scheme.{u}}

/-! ### Direct image along a finite morphism on an arbitrary dimension layer -/

/-- Direct image along a finite morphism, followed by the localization onto the layer `(a, b]` of
the target, inverts the morphisms inverted by the localization onto the layer `(a, b]` of the
source. -/
theorem isInvertedBy_finitePushforwardDimLE_comp_q (C : ChowSituation.{u}) (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (π : W ⟶ X) [IsFinite π]
    (hπ : π ≫ sX = sW) (a b : ℤ) :
    (lowerDimensionClass C sW a b).isoModSerre.IsInvertedBy
      (finitePushforwardDimLE C sW sX π hπ b ⋙
        (lowerDimensionClass C sX a b).isoModSerre.Q) :=
  (ObjectProperty.isoModSerre_isInvertedBy_iff _ _).2 (by
    intro M hM
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    exact ObjectProperty.le_kernel_of_isoModSerre_isInvertedBy (lowerDimensionClass C sX a b)
      (lowerDimensionClass C sX a b).isoModSerre.Q
      (Localization.inverts _ (lowerDimensionClass C sX a b).isoModSerre)
      ((finitePushforwardDimLE C sW sX π hπ b).obj M)
      (coherentModulesDimLE_finitePushforward C sW sX π hπ a M.obj hM))

/-- Direct image along a finite morphism as a functor between the dimension layers `(a, b]` of the
source and the target. -/
def coherentDimensionQuotientFinitePushforward (C : ChowSituation.{u}) (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (π : W ⟶ X) [IsFinite π]
    (hπ : π ≫ sX = sW) (a b : ℤ) :
    coherentDimensionQuotient C sW a b ⥤ coherentDimensionQuotient C sX a b :=
  Localization.lift _ (isInvertedBy_finitePushforwardDimLE_comp_q C sW sX π hπ a b)
    (lowerDimensionClass C sW a b).isoModSerre.Q

/-- The functor between layers induced by direct image is compatible with direct image on the
underlying categories of coherent modules of bounded support dimension. -/
def coherentDimensionQuotientFinitePushforwardFac (C : ChowSituation.{u}) (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (π : W ⟶ X) [IsFinite π]
    (hπ : π ≫ sX = sW) (a b : ℤ) :
    (lowerDimensionClass C sW a b).isoModSerre.Q ⋙
        coherentDimensionQuotientFinitePushforward C sW sX π hπ a b ≅
      finitePushforwardDimLE C sW sX π hπ b ⋙ (lowerDimensionClass C sX a b).isoModSerre.Q :=
  Localization.fac _ (isInvertedBy_finitePushforwardDimLE_comp_q C sW sX π hπ a b) _

/-- Direct image between the layers `(a, b]` preserves finite limits. -/
instance preservesFiniteLimits_coherentDimensionQuotientFinitePushforward
    (C : ChowSituation.{u}) (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (π : W ⟶ X) [IsFinite π] (hπ : π ≫ sX = sW) (a b : ℤ) :
    PreservesFiniteLimits (coherentDimensionQuotientFinitePushforward C sW sX π hπ a b) :=
  have : PreservesFiniteLimits (finitePushforwardDimLE C sW sX π hπ b ⋙
      (lowerDimensionClass C sX a b).isoModSerre.Q) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits ((lowerDimensionClass C sW a b).isoModSerre.Q ⋙
      coherentDimensionQuotientFinitePushforward C sW sX π hπ a b) :=
    preservesFiniteLimits_of_natIso
      (coherentDimensionQuotientFinitePushforwardFac C sW sX π hπ a b).symm
  (ObjectProperty.SerreClassLocalization.preservesFiniteLimits_comp_iff _
    (lowerDimensionClass C sW a b) _).mp this

/-- Direct image between the layers `(a, b]` preserves finite colimits. -/
instance preservesFiniteColimits_coherentDimensionQuotientFinitePushforward
    (C : ChowSituation.{u}) (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (π : W ⟶ X) [IsFinite π] (hπ : π ≫ sX = sW) (a b : ℤ) :
    PreservesFiniteColimits (coherentDimensionQuotientFinitePushforward C sW sX π hπ a b) :=
  have : PreservesFiniteColimits (finitePushforwardDimLE C sW sX π hπ b ⋙
      (lowerDimensionClass C sX a b).isoModSerre.Q) :=
    comp_preservesFiniteColimits _ _
  have : PreservesFiniteColimits ((lowerDimensionClass C sW a b).isoModSerre.Q ⋙
      coherentDimensionQuotientFinitePushforward C sW sX π hπ a b) :=
    preservesFiniteColimits_of_natIso
      (coherentDimensionQuotientFinitePushforwardFac C sW sX π hπ a b).symm
  (ObjectProperty.SerreClassLocalization.preservesFiniteColimits_comp_iff _
    (lowerDimensionClass C sW a b) _).mp this

/-- Direct image between the layers `(a, b]` is an additive functor. -/
instance additive_coherentDimensionQuotientFinitePushforward (C : ChowSituation.{u})
    (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (π : W ⟶ X) [IsFinite π] (hπ : π ≫ sX = sW) (a b : ℤ) :
    (coherentDimensionQuotientFinitePushforward C sW sX π hπ a b).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The homomorphism `K₀(Coh_{≤b}(W)/Coh_{≤a}(W)) → K₀(Coh_{≤b}(X)/Coh_{≤a}(X))` on the
Grothendieck groups of the layers `(a, b]` induced by direct image along a finite morphism. -/
def coherentDimensionKZeroFinitePushforwardHom (C : ChowSituation.{u}) (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (π : W ⟶ X) [IsFinite π]
    (hπ : π ≫ sX = sW) (a b : ℤ) :
    coherentDimensionKZero C sW a b →+ coherentDimensionKZero C sX a b :=
  KZero.lift
    (fun A ↦ KZero.mk _ ((coherentDimensionQuotientFinitePushforward C sW sX π hπ a b).obj A))
    fun _ hS ↦ KZero.mk_of_shortExact _
      (hS.map_of_exact (coherentDimensionQuotientFinitePushforward C sW sX π hπ a b))

/-- The homomorphism on the Grothendieck groups of the layers sends the class of a coherent module
of support dimension at most `b` to the class of its direct image. -/
@[simp]
theorem coherentDimensionKZeroFinitePushforwardHom_mk (C : ChowSituation.{u}) (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (π : W ⟶ X) [IsFinite π]
    (hπ : π ≫ sX = sW) (a b : ℤ) (F : CoherentModulesDimLE C sW b) :
    coherentDimensionKZeroFinitePushforwardHom C sW sX π hπ a b
        (coherentDimensionKZeroMk C sW a b F) =
      coherentDimensionKZeroMk C sX a b ((finitePushforwardDimLE C sW sX π hπ b).obj F) :=
  (KZero.lift_mk _ _ _).trans (KZero.mk_eq_of_iso
    ((coherentDimensionQuotientFinitePushforwardFac C sW sX π hπ a b).app F))

/-! ### Compatibility of direct image with widening the layer -/

/-- Including the coherent modules of support dimension at most `k` into those of support
dimension at most `k + 1` commutes with direct image along a finite morphism. -/
theorem dimensionLayerInclusion_obj_finitePushforwardDimLE_obj (C : ChowSituation.{u})
    (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (π : W ⟶ X) [IsFinite π] (hπ : π ≫ sX = sW) (k : ℤ) (F : CoherentModulesDimLE C sW k) :
    (dimensionLayerInclusion C sX k).obj ((finitePushforwardDimLE C sW sX π hπ k).obj F) =
      (finitePushforwardDimLE C sW sX π hπ (k + 1)).obj
        ((dimensionLayerInclusion C sW k).obj F) :=
  rfl

/-- Direct image along a finite morphism commutes with the map that widens the layer `(k - 1, k]`
to the layer `(k - 1, k + 1]`. -/
theorem coherentDimensionLayerHom_comp_toKZero_comp_dimensionLayerFinitePushforwardHom
    (C : ChowSituation.{u}) (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (π : W ⟶ X) [IsFinite π] (hπ : π ≫ sX = sW) (k : ℤ) :
    (coherentDimensionLayerHom C sX k).comp
        ((KZero.ofGrothendieckGroup).comp
          (dimensionLayerFinitePushforwardHom C sW sX π hπ k)) =
      (coherentDimensionKZeroFinitePushforwardHom C sW sX π hπ (k - 1) (k + 1)).comp
        ((coherentDimensionLayerHom C sW k).comp
          (KZero.ofGrothendieckGroup)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  refine (AddMonoidHom.cancel_right
    (ObjectProperty.SerreClassLocalization.grothendieckGroup_map_surjective
      (lowerDimensionClass C sW (k - 1) k).isoModSerre.Q (lowerDimensionClass C sW (k - 1) k)
      (shortExact_map_q_lowerDimensionClass C sW k))).1 (GrothendieckGroup.hom_ext fun F ↦ ?_)
  simp only [AddMonoidHom.comp_apply, GrothendieckGroup.map_of,
    dimensionLayerFinitePushforwardHom_of, KZero.ofGrothendieckGroup_of]
  rw [show KZero.mk (coherentDimensionQuotient C sX (k - 1) k)
      ((lowerDimensionClass C sX (k - 1) k).isoModSerre.Q.obj
        ((finitePushforwardDimLE C sW sX π hπ k).obj F)) =
      coherentDimensionKZeroMk C sX (k - 1) k
        ((finitePushforwardDimLE C sW sX π hπ k).obj F) from rfl,
    show KZero.mk (coherentDimensionQuotient C sW (k - 1) k)
      ((lowerDimensionClass C sW (k - 1) k).isoModSerre.Q.obj F) =
      coherentDimensionKZeroMk C sW (k - 1) k F from rfl, coherentDimensionLayerHom_apply_mk,
    coherentDimensionLayerHom_apply_mk,
    coherentDimensionKZeroFinitePushforwardHom_mk,
    dimensionLayerInclusion_obj_finitePushforwardDimLE_obj]

/-! ### The reduction -/

/-- For a finite morphism `π : W ⟶ X` with `X` Noetherian, the class in the wide layer
`(k - 1, k + 1]` over `X` of the proper pushforward of a `k`-cycle `c` on `W` is the direct image
of the class in the wide layer over `W` of `c`. -/
theorem cycleDimensionLayerWideHom_properPushforwardHom (C : ChowSituation.{u}) (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (π : W ⟶ X) [IsFinite π]
    [IsNoetherian X] (hπ : π ≫ sX = sW) (k : ℤ) (c : CycleGroup C sW k) :
    cycleDimensionLayerWideHom C sX k (properPushforwardHom C sW sX π hπ k c) =
      coherentDimensionKZeroFinitePushforwardHom C sW sX π hπ (k - 1) (k + 1)
        (cycleDimensionLayerWideHom C sW k c) := by
  have hcomp := DFunLike.congr_fun
    (coherentDimensionLayerHom_comp_toKZero_comp_dimensionLayerFinitePushforwardHom
      C sW sX π hπ k) (cycleDimensionLayerHom C sW k c)
  simp only [AddMonoidHom.comp_apply] at hcomp
  show coherentDimensionLayerHom C sX k (KZero.ofGrothendieckGroup
      (cycleDimensionLayerHom C sX k (properPushforwardHom C sW sX π hπ k c))) = _
  rw [← dimensionLayerFinitePushforwardHom_cycleDimensionLayerHom C sW sX π hπ k c, hcomp]
  rfl

/-- If the class of a `k`-cycle `c` on `W` in the wide layer `(k - 1, k + 1]` vanishes, then so
does the class of its proper pushforward along a finite morphism `π : W ⟶ X` with `X`
Noetherian. -/
theorem cycleDimensionLayerWideHom_properPushforwardHom_eq_zero (C : ChowSituation.{u})
    (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (π : W ⟶ X) [IsFinite π] [IsNoetherian X] (hπ : π ≫ sX = sW) (k : ℤ)
    (c : CycleGroup C sW k) (hc : cycleDimensionLayerWideHom C sW k c = 0) :
    cycleDimensionLayerWideHom C sX k (properPushforwardHom C sW sX π hπ k c) = 0 := by
  rw [cycleDimensionLayerWideHom_properPushforwardHom, hc, map_zero]

/-- A `k`-cycle `α` on `X` which is the proper pushforward along a finite morphism `π : W ⟶ X`,
with `X` Noetherian, of a `k`-cycle whose class in the wide layer `(k - 1, k + 1]` over `W`
vanishes, has vanishing class in the wide layer over `X`. -/
theorem cycleDimensionLayerWideHom_eq_zero_of_properPushforwardHom_eq (C : ChowSituation.{u})
    (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (π : W ⟶ X) [IsFinite π] [IsNoetherian X] (hπ : π ≫ sX = sW) (k : ℤ)
    {α : CycleGroup C sX k} {c : CycleGroup C sW k}
    (hα : properPushforwardHom C sW sX π hπ k c = α)
    (hc : cycleDimensionLayerWideHom C sW k c = 0) :
    cycleDimensionLayerWideHom C sX k α = 0 :=
  hα ▸ cycleDimensionLayerWideHom_properPushforwardHom_eq_zero C sW sX π hπ k c hc

end Stacks.Chow

end
