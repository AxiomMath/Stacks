module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerPushforwardClass
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.SchemeTheoreticSupportDimension
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.FunctionFieldPresentation
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.SchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Meromorphic.RegularSectionExistence
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.PushforwardTwist

/-!
# The twist of a module with no embedded associated points, in a dimension layer

Let `X` be locally of finite type over the base scheme of chapter 42 of the Stacks Project, let
`ℒ` be an invertible `𝒪_X`-module and let `ℱ` be coherent with `dim_δ(Supp ℱ) ≤ k + 1` **and no
embedded associated points**. Then

`[ℱ ⊗ ℒ] - [ℱ] ∈ Bₖ(X) ⊆ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`,

which is the membership assertion of [Stacks, Tag 02SX] for such an `ℱ`.

## Main results

* `Stacks.Chow.coherentDimensionKZeroMk_finitePushforward_add_of_modules` — additivity of the
  classes of the direct images along a finite morphism, from a short exact sequence of modules.
* `Stacks.Chow.coherentDimensionKZeroMk_layerMkTensor_sub_mem_of_descends` — the membership for a
  module given as the direct image of a module of full support on a closed subscheme without
  embedded points.
* `Stacks.Chow.coherentDimensionKZeroMk_layerMkTensor_sub_mem_of_hasNoEmbeddedAssociatedPoints`
  — the membership above, for a module with no embedded associated points.

## Implementation notes

The geometric statement
`Stacks.Chow.coherentDimensionKZeroMk_layerMkTensor_sub_mem_of_descends` is stated for an
arbitrary closed immersion `i : Z ⟶ X` and an arbitrary descent `i_*𝒢 ≅ ℱ`, not for the
scheme-theoretic support of `ℱ`: at the let-bound `Scheme.IdealSheafData.subschemeι` instance
search does not find `IsClosedImmersion i`, `IsFinite i` or `LocallyOfFiniteType (i ≫ f)`.

The projection formula is used at the `AlgebraicGeometry.tensorModules` spelling with no
transport: `Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso` is stated with
`Stacks.RingedSpace.tensorSheaf`, `Stacks.RingedSpace.pushforwardFunctor` and
`Stacks.RingedSpace.pullbackFunctor`, each the same term as its `AlgebraicGeometry.Scheme.Modules`
spelling.

## References

* [Stacks Project, Tag 02SX](https://stacks.math.columbia.edu/tag/02SX)
* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02SC](https://stacks.math.columbia.edu/tag/02SC)
* [Stacks Project, Tag 02OM](https://stacks.math.columbia.edu/tag/02OM)
* [Stacks Project, Tag 02OZ](https://stacks.math.columbia.edu/tag/02OZ)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 0FDR](https://stacks.math.columbia.edu/tag/0FDR)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Additivity of the pushed-forward classes -/

/-- **Additivity of the classes of the direct images along a finite morphism, from a short exact
sequence of modules.** Given a short exact sequence `0 ⟶ A ⟶ B ⟶ D ⟶ 0` of coherent `𝒪_Z`-modules
whose three supports have delta-dimension at most `b`, the class of the direct image of `B` in the
Grothendieck group of the layer `(a, b]` over `X` is the sum of the classes of the direct images
of `A` and `D`. -/
theorem coherentDimensionKZeroMk_finitePushforward_add_of_modules (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (i : Z ⟶ X) [IsFinite i] (hπ : i ≫ f = sZ) (a b : ℤ)
    {A B D : CoherentModulesDimLE C sZ b} (u : A.obj.obj ⟶ B.obj.obj)
    (v : B.obj.obj ⟶ D.obj.obj) (w : u ≫ v = 0) (h : (ShortComplex.mk u v w).ShortExact) :
    coherentDimensionKZeroMk C f a b ((finitePushforwardDimLE C sZ f i hπ b).obj B) =
      coherentDimensionKZeroMk C f a b ((finitePushforwardDimLE C sZ f i hπ b).obj A) +
        coherentDimensionKZeroMk C f a b ((finitePushforwardDimLE C sZ f i hπ b).obj D) :=
  coherentDimensionKZeroMk_finitePushforward_add C f sZ i hπ a b
    (S := layerShortComplex C sZ u v w)
    (shortExact_coherentModulesDimLE C sZ b
      (by rw [layerShortComplex_map_ι C sZ u v w]; exact h))

/-- **Two short exact sequences with a common first term put a difference of classes in
`Bₖ(X)`.** If `0 ⟶ 𝒫 ⟶ ℬ₁ ⟶ 𝒬₁ ⟶ 0` and `0 ⟶ 𝒫 ⟶ ℬ₂ ⟶ 𝒬₂ ⟶ 0` are short exact sequences in the
layer `Coh_{≤k+1}(𝒪_Z)` whose third terms have support of delta-dimension at most `k`, then the
difference of the classes of the direct images of `ℬ₂` and `ℬ₁` along a finite morphism lies in
`Bₖ(X)`. -/
theorem coherentDimensionKZeroMk_finitePushforward_sub_mem (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (i : Z ⟶ X) [IsFinite i] (hπ : i ≫ f = sZ) {k : ℤ}
    {P B₁ B₂ Q₁ Q₂ : CoherentModulesDimLE C sZ (k + 1)}
    (u₁ : P.obj.obj ⟶ B₁.obj.obj) (v₁ : B₁.obj.obj ⟶ Q₁.obj.obj) (w₁ : u₁ ≫ v₁ = 0)
    (h₁ : (ShortComplex.mk u₁ v₁ w₁).ShortExact)
    (u₂ : P.obj.obj ⟶ B₂.obj.obj) (v₂ : B₂.obj.obj ⟶ Q₂.obj.obj) (w₂ : u₂ ≫ v₂ = 0)
    (h₂ : (ShortComplex.mk u₂ v₂ w₂).ShortExact)
    (hQ₁ : coherentModulesDimLE C sZ k Q₁.obj)
    (hQ₂ : coherentModulesDimLE C sZ k Q₂.obj) :
    coherentDimensionKZeroMk C f (k - 1) (k + 1)
          ((finitePushforwardDimLE C sZ f i hπ (k + 1)).obj B₂) -
        coherentDimensionKZeroMk C f (k - 1) (k + 1)
          ((finitePushforwardDimLE C sZ f i hπ (k + 1)).obj B₁) ∈
      coherentDimensionLayerImage C f k := by
  have hd : ∀ {B Q : CoherentModulesDimLE C sZ (k + 1)} (u : P.obj.obj ⟶ B.obj.obj)
      (v : B.obj.obj ⟶ Q.obj.obj) (w : u ≫ v = 0), (ShortComplex.mk u v w).ShortExact →
      coherentModulesDimLE C sZ k Q.obj →
      coherentDimensionKZeroMk C f (k - 1) (k + 1)
          ((finitePushforwardDimLE C sZ f i hπ (k + 1)).obj B) -
        coherentDimensionKZeroMk C f (k - 1) (k + 1)
          ((finitePushforwardDimLE C sZ f i hπ (k + 1)).obj P) ∈
      coherentDimensionLayerImage C f k := by
    intro B Q u v w h hQ
    rw [coherentDimensionKZeroMk_finitePushforward_add_of_modules C f sZ i hπ (k - 1) (k + 1)
      u v w h, add_sub_cancel_left]
    exact coherentDimensionKZeroMk_mem_coherentDimensionLayerImage C f k _
      (coherentModulesDimLE_finitePushforward C sZ f i hπ k Q.obj hQ)
  simpa using sub_mem (hd u₂ v₂ w₂ h₂ hQ₂) (hd u₁ v₁ w₁ h₁ hQ₁)

/-! ### The projection formula at the `tensorModules` spelling -/

/-- **The projection formula for a closed immersion of schemes**, at the
`AlgebraicGeometry.tensorModules` spelling: `i_*𝒢 ⊗ ℒ ≅ i_*(𝒢 ⊗ i^*ℒ)`, [Stacks, Tag 01E8]. -/
def pushforwardTensorModulesIso {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (G : Z.Modules) (L : X.Modules) :
    tensorModules ((Scheme.Modules.pushforward i).obj G) L ≅
      (Scheme.Modules.pushforward i).obj (tensorModules G ((Scheme.Modules.pullback i).obj L)) :=
  Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso i G L

/-- An isomorphism `A ≅ B` of `𝒪_X`-modules induces an isomorphism `A ⊗ L ≅ B ⊗ L`. -/
def tensorModulesIsoLeft {X : Scheme.{u}} {A B : X.Modules} (e : A ≅ B) (L : X.Modules) :
    tensorModules A L ≅ tensorModules B L :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).mapIso e).app L

/-! ### The two sequences of Stacks 02SW, read in the layer over `X` -/

/-- **The difference of the classes of the direct images of `𝒢 ⊗ 𝒩` and `𝒢` lies in `Bₖ(X)`.**
Let `i : Z ⟶ X` be a closed immersion with `dim_δ(Z) ≤ k + 1` and no embedded points, let `𝒢` be
a coherent `𝒪_Z`-module of full support with no embedded associated points, and let `s` be a
regular meromorphic section of an invertible `𝒪_Z`-module `𝒩`. Then the difference of the
classes of `i_*(𝒢 ⊗ 𝒩)` and `i_*𝒢` in the layer `(k-1, k+1]` over `X` lies in `Bₖ(X)`. -/
theorem coherentDimensionKZeroMk_finitePushforward_tensor_sub_mem_of_regularSection
    (C : ChowSituation.{u}) {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFiniteType (i ≫ f)] (N G : Z.Modules)
    [G.IsCoherent] [(tensorModules G N).IsCoherent]
    (hN : AlgebraicGeometry.SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property N)
    {k : ℤ} (hdimZ : schemeDeltaDimension C (i ≫ f) ≤ ((k + 1 : ℤ) : EInt))
    (hZemb : HasNoEmbeddedPoints Z) (hGemb : HasNoEmbeddedAssociatedPoints G)
    (hGsupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules G).supp = Set.univ)
    (s : MeromorphicSection Z.sheaf N) (hs : IsRegularMeromorphicSection Z.sheaf N s) :
    coherentDimensionKZeroMk C f (k - 1) (k + 1)
          ((finitePushforwardDimLE C (i ≫ f) f i rfl (k + 1)).obj
            (layerMk C (i ≫ f) (k + 1) (tensorModules G N)
              (schemeDeltaDimension_reducedSupport_le_of_le C (i ≫ f) (tensorModules G N) hdimZ))) -
        coherentDimensionKZeroMk C f (k - 1) (k + 1)
          ((finitePushforwardDimLE C (i ≫ f) f i rfl (k + 1)).obj
            (layerMk C (i ≫ f) (k + 1) G
              (schemeDeltaDimension_reducedSupport_le_of_le C (i ≫ f) G hdimZ))) ∈
      coherentDimensionLayerImage C f k := by
  have hZN : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ f)
  have hQ₁coh : (denominatorQuotient Z N G s).IsCoherent :=
    isCoherent_denominatorQuotient C (i ≫ f) N G s hdimZ hZemb hGemb hGsupp hN hs
  have hQ₂coh : (@denominatorSectionQuotient Z N G s hZN hN hs inferInstance hGemb
      hGsupp).IsCoherent :=
    isCoherent_denominatorSectionQuotient C (i ≫ f) N G s hdimZ hZemb hGemb hGsupp hN hs
  have hQ₁dimk : schemeDeltaDimension C
      ((reducedSupport (denominatorQuotient Z N G s)).subschemeι ≫ (i ≫ f)) ≤ (k : EInt) :=
    schemeDeltaDimension_denominatorQuotient_le C (i ≫ f) N G s hdimZ hZemb hGemb hGsupp hN hs
  have hQ₂dimk : schemeDeltaDimension C
      ((reducedSupport (@denominatorSectionQuotient Z N G s hZN hN hs inferInstance hGemb
        hGsupp)).subschemeι ≫ (i ≫ f)) ≤ (k : EInt) :=
    schemeDeltaDimension_denominatorSectionQuotient_le C (i ≫ f) N G s hdimZ hZemb hGemb hGsupp
      hN hs
  have hPcoh : (denominatorIdealTimesModule Z N G s).IsCoherent :=
    isCoherent_denominatorIdealTimesModule N G s hN
  exact coherentDimensionKZeroMk_finitePushforward_sub_mem C f (i ≫ f) i rfl
    (P := layerMk C (i ≫ f) (k + 1) (denominatorIdealTimesModule Z N G s)
      (schemeDeltaDimension_reducedSupport_le_of_le C (i ≫ f) _ hdimZ))
    (Q₁ := layerMk C (i ≫ f) (k + 1) (denominatorQuotient Z N G s)
      (hQ₁dimk.trans (WithBotTop.coe_le_coe.mpr (by omega))))
    (Q₂ := layerMk C (i ≫ f) (k + 1)
      (@denominatorSectionQuotient Z N G s hZN hN hs inferInstance hGemb hGsupp)
      (hQ₂dimk.trans (WithBotTop.coe_le_coe.mpr (by omega))))
    (denominatorIdealTimesModuleι Z N G s)
    (cokernel.π (denominatorIdealTimesModuleι Z N G s)) (cokernel.condition _)
    (denominatorQuotientShortComplex_shortExact C (i ≫ f) N G s hdimZ hZemb hGemb hGsupp hN hs)
    (denominatorIdealTimesModuleMul Z N G s hN hs hGemb hGsupp).val
    (cokernel.π (denominatorIdealTimesModuleMul Z N G s hN hs hGemb hGsupp).val)
    (cokernel.condition _)
    (denominatorSectionQuotientShortComplex_shortExact C (i ≫ f) N G s hdimZ hZemb hGemb hGsupp
      hN hs)
    hQ₁dimk hQ₂dimk

/-! ### The membership of Stacks 02SX for a descended module -/

/-- **[Stacks, Tag 02SX], the membership clause, for a module descended to a closed subscheme
without embedded points.** Let `i : Z ⟶ X` be a closed immersion with `dim_δ(Z) ≤ k + 1` and no
embedded points, let `𝒢` be a coherent `𝒪_Z`-module of full support with no embedded associated
points, and let `ℱ ≅ i_*𝒢` be coherent with `dim_δ(Supp ℱ) ≤ k + 1`. Then for `ℒ` invertible the
element `[ℱ ⊗ ℒ] - [ℱ]` of `K₀(Coh_{≤k+1}/Coh_{≤k-1})` lies in the subgroup `Bₖ(X)`. -/
theorem coherentDimensionKZeroMk_layerMkTensor_sub_mem_of_descends (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFiniteType (i ≫ f)] (F : X.Modules) [F.IsCoherent] (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    {k : ℤ}
    (hdim : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ ((k + 1 : ℤ) : EInt))
    (hdimZ : schemeDeltaDimension C (i ≫ f) ≤ ((k + 1 : ℤ) : EInt))
    (hZemb : HasNoEmbeddedPoints Z) (G : Z.Modules) (hGcoh : G.IsCoherent)
    (hGemb : HasNoEmbeddedAssociatedPoints G)
    (hGsupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules G).supp = Set.univ)
    (e : (Scheme.Modules.pushforward i).obj G ≅ F) :
    coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMkTensor C f (k + 1) F L hL hdim) -
        coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMk C f (k + 1) F hdim) ∈
      coherentDimensionLayerImage C f k := by
  have hZN : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ f)
  have hL' : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
  have _ : G.IsCoherent := hGcoh
  have hNinv : AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      ((Scheme.Modules.pullback i).obj L) :=
    AlgebraicGeometry.SheafOfModules.isInvertible_pullback i L
  have hNinv' : AlgebraicGeometry.SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property
      ((Scheme.Modules.pullback i).obj L) := hNinv
  have hGNcoh : (tensorModules G ((Scheme.Modules.pullback i).obj L)).IsCoherent :=
    isCoherent_tensorModules_of_isInvertible G _ hNinv'
  obtain ⟨s, hs⟩ := AlgebraicGeometry.exists_isRegularMeromorphicSection_of_hasNoEmbeddedPoints Z
    hZemb ((Scheme.Modules.pullback i).obj L)
  have hsub := coherentDimensionKZeroMk_finitePushforward_tensor_sub_mem_of_regularSection C f i
    ((Scheme.Modules.pullback i).obj L) G hNinv' hdimZ hZemb hGemb hGsupp s hs
  have heG : coherentDimensionKZeroMk C f (k - 1) (k + 1)
      ((finitePushforwardDimLE C (i ≫ f) f i rfl (k + 1)).obj
        (layerMk C (i ≫ f) (k + 1) G
          (schemeDeltaDimension_reducedSupport_le_of_le C (i ≫ f) G hdimZ))) =
      coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMk C f (k + 1) F hdim) :=
    coherentDimensionKZeroMk_eq_of_moduleIso C f (k - 1) (k + 1) e
  have heGN : coherentDimensionKZeroMk C f (k - 1) (k + 1)
      ((finitePushforwardDimLE C (i ≫ f) f i rfl (k + 1)).obj
        (layerMk C (i ≫ f) (k + 1) (tensorModules G ((Scheme.Modules.pullback i).obj L))
          (schemeDeltaDimension_reducedSupport_le_of_le C (i ≫ f)
            (tensorModules G ((Scheme.Modules.pullback i).obj L)) hdimZ))) =
      coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMkTensor C f (k + 1) F L hL hdim) :=
    coherentDimensionKZeroMk_eq_of_moduleIso C f (k - 1) (k + 1)
      ((pushforwardTensorModulesIso i G L).symm ≪≫ tensorModulesIsoLeft e L)
  rw [heG, heGN] at hsub
  exact hsub

/-! ### The membership of Stacks 02SX for a module with no embedded associated points -/

/-- **[Stacks, Tag 02SX], the membership clause, for a module with no embedded associated
points.** For `ℒ` invertible and `ℱ` coherent with no embedded associated points and
`dim_δ(Supp ℱ) ≤ k + 1`, the element `[ℱ ⊗ ℒ] - [ℱ]` of `K₀(Coh_{≤k+1}/Coh_{≤k-1})` lies in the
subgroup `Bₖ(X)` of [Stacks, Tag 02SC]. -/
theorem coherentDimensionKZeroMk_layerMkTensor_sub_mem_of_hasNoEmbeddedAssociatedPoints
    (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent] (hF : HasNoEmbeddedAssociatedPoints F) (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    {k : ℤ}
    (hdim : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ ((k + 1 : ℤ) : EInt)) :
    coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMkTensor C f (k + 1) F L hL hdim) -
        coherentDimensionKZeroMk C f (k - 1) (k + 1) (layerMk C f (k + 1) F hdim) ∈
      coherentDimensionLayerImage C f k := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨G, hGcoh, hGemb, hGsupp, ⟨e⟩⟩ :=
    exists_coherent_module_on_annihilatorIdeal_subscheme F hF
  exact coherentDimensionKZeroMk_layerMkTensor_sub_mem_of_descends C f
    (annihilatorIdeal' F).subschemeι F L hL hdim
    (schemeDeltaDimension_annihilatorIdeal_le C f F hdim)
    (hasNoEmbeddedPoints_annihilatorIdeal_subscheme F hF) G hGcoh hGemb hGsupp e

end Stacks.Chow

end
