module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalCycle
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.DivisorVirtualNormalBundleClass
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.LocalRing
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic
public import StacksFrontier.RingTheory.CohenMacaulay.Witnesses
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Gysin map of a flat local complete intersection morphism is flat pullback

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
local complete intersection morphism of schemes locally of finite type over `S` for which the
Gysin map `f^! ∈ A^*(X ⟶ Y)^∧` of Stacks 0FF3 exists. **Stacks 0FF4** asserts that if `f` is
moreover flat, then `f^!` is the flat-pullback class `f^*` of Stacks 0B78.

## Main results

* `Stacks.Chow.lciGysinMap_eq_completedFlatPullbackOfFlatLCI` — **Stacks 0FF4**: for a flat
  local complete intersection morphism `f` whose Gysin map exists, `f^! = f^*`.
* `Stacks.Chow.SmoothFactorization.gysinMap_eq_completedFlatPullbackOfFlatLCI` — the same for the
  Gysin map `i^! ∘ g^*` of every factorization.
* `Stacks.Chow.SmoothFactorization.hasCapFundamentalFormula_gysinMap` — on each connected
  component the Gysin map of a factorization is concentrated in the degree `r - t`, where it caps
  fundamental classes of Cohen–Macaulay test schemes to fundamental classes.
* `Stacks.Chow.completedBivariantGroup.eq_of_hasCapFundamentalFormula` — two completed classes
  for a flat morphism of locally constant relative dimension `s` which are concentrated in degree
  `-s` on each connected component, where they cap fundamental classes of Cohen–Macaulay test
  schemes to fundamental classes, are equal.
* `Stacks.Chow.hasCapFundamentalFormula_completedFlatPullback` — the completed flat pullback has
  that property.
* `Stacks.Chow.fiberRank_conormalModule_add_of_flat` — for a factorization `f = g ∘ i` of a flat
  morphism through a regular immersion `i` and a smooth `g`, the rank of the conormal sheaf of
  `i` at a generic point of `X` plus the relative dimension of `f` there is the relative dimension
  of `g`.
* `Stacks.Chow.ringKrullDim_stalk_eq_sub_toNat_residueTrdeg` — the local ring at a point `ζ` over
  a generic point of the target of a flat morphism of relative dimension `t` has dimension `t`
  minus the residue transcendence degree at `ζ`.

## References

* [Stacks Project, Tag 0FF4](https://stacks.math.columbia.edu/tag/0FF4)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 00ON](https://stacks.math.columbia.edu/tag/00ON)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The dimension of a local ring over a generic point of the target -/

/-- **The local ring over a generic point of the target of a flat morphism.** Let `g : P ⟶ Y` be
a flat morphism of locally Noetherian schemes, locally of finite type and of relative dimension
`t`, and let `ζ ∈ P` lie over a generic point of `Y`. Then `dim 𝒪_{P, ζ} = t - e` for `e` the
transcendence degree of `κ(ζ)` over `κ(g ζ)`. -/
@[sga "1 II 5.8" "special case"]
theorem ringKrullDim_stalk_eq_sub_toNat_residueTrdeg {P Y : Scheme.{u}} (g : P ⟶ Y) [Flat g]
    [LocallyOfFiniteType g] [IsLocallyNoetherian P] [IsLocallyNoetherian Y] {t : ℕ}
    (ht : AlgebraicGeometry.RelativeDimension g t) (ζ : P) (hζ : g ζ ∈ genericPoints Y) :
    ringKrullDim (P.presheaf.stalk ζ) =
      (((t - Cardinal.toNat (residueTrdeg g ζ) : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  have hq : LocallyOfFiniteType (g.fiberToSpecResidueField (g.base ζ)) :=
    (inferInstance : LocallyOfFiniteType (pullback.snd g (Y.fromSpecResidueField (g.base ζ))))
  have hfibre := ht (g.base ζ) ⟨g.asFiber ζ⟩
  have hAt := @topologicalKrullDimAt_eq_of_equidimensional _ _ (g.fiber (g.base ζ))
    (g.fiberToSpecResidueField (g.base ζ)) hq t hfibre.1 hfibre.2 (g.asFiber ζ)
  have hfx : topologicalKrullDimAt (g.fiber (g.base ζ)) (g.asFiber ζ) =
      ringKrullDim ((g.fiber (g.base ζ)).presheaf.stalk (g.asFiber ζ)) +
        (Cardinal.toENat (residueTrdeg g ζ) : WithBot ℕ∞) :=
    topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg g ζ
  rw [hAt] at hfx
  have hflat := ringKrullDim_stalk_eq_add_ringKrullDim_stalk_fiber_of_flat g ζ
  rw [(ringKrullDim_stalk_eq_zero_iff_mem_genericPoints Y _).mpr hζ, zero_add] at hflat
  rw [hflat]
  have hfin : Cardinal.toENat (residueTrdeg g ζ) = (Cardinal.toNat (residueTrdeg g ζ) : ℕ∞) := by
    rw [← Cardinal.toENat_nat, Cardinal.cast_toNat_of_lt_aleph0 (residueTrdeg_lt_aleph0 g ζ)]
  rw [hfin] at hfx
  have hle := toNat_residueTrdeg_le_of_relativeDimension g t ht ζ
  generalize ringKrullDim ((g.fiber (g.base ζ)).presheaf.stalk (g.asFiber ζ)) = a at hfx ⊢
  generalize Cardinal.toNat (residueTrdeg g ζ) = e at hfx hle ⊢
  induction a with
  | bot => simp at hfx
  | coe b =>
    induction b with
    | top =>
      exfalso
      have h : (t : ℕ∞) = ⊤ + (e : ℕ∞) := by exact_mod_cast hfx
      simp at h
    | coe n =>
      have h : n + e = t := by exact_mod_cast hfx.symm
      rw [show n = t - e by omega]

/-! ### The codimension of the immersion of a factorization of a flat morphism -/

section Codimension

variable {X Y P : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [IsLocallyNoetherian P] {f : X ⟶ Y} [LocallyOfFiniteType f] [Flat f]

/-- **The codimension of the immersion in a factorization of a flat morphism.** Let `f : X ⟶ Y`
be flat, factored as `f = g ∘ i` with `i : X ⟶ P` a regular immersion and `g : P ⟶ Y` smooth, all
schemes being locally Noetherian. Let `ξ` be a generic point of `X`, let `s` be the relative
dimension of `f` on the connected component of `X` containing `ξ`, and `t` that of `g` on the
connected component of `P` containing `i ξ`. Then the conormal sheaf of `i` has rank `t - s` at
`ξ`. -/
theorem fiberRank_conormalModule_add_of_flat (i : X ⟶ P) [IsImmersion i] (g : P ⟶ Y) [Smooth g]
    (hig : i ≫ g = f) (hreg : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i)
    {ξ : X} (hξ : ξ ∈ genericPoints X) {s t : ℕ}
    (hs : AlgebraicGeometry.RelativeDimension
      (f.resConnectedComponent (_root_.ConnectedComponents.mk ξ)) s)
    (ht : AlgebraicGeometry.RelativeDimension
      (g.resConnectedComponent (i.continuous.connectedComponentsMap
        (_root_.ConnectedComponents.mk ξ))) t) :
    Scheme.Modules.fiberRank (conormalModule i) ξ + s = t := by
  set a := _root_.ConnectedComponents.mk ξ
  set c := i.continuous.connectedComponentsMap a
  set ga := g.resConnectedComponent c
  set fa := f.resConnectedComponent a
  set ξa : (X.connectedComponentOpens a : Scheme.{u}) := ⟨ξ, mem_connectedComponentOpens_mk ξ⟩
  have hmem : i ξ ∈ P.connectedComponentOpens c :=
    i.connectedComponentOpens_le_preimage a (mem_connectedComponentOpens_mk ξ)
  set pt : (P.connectedComponentOpens c : Scheme.{u}) := ⟨i ξ, hmem⟩
  have hy : f ξ ∈ genericPoints Y :=
    AlgebraicGeometry.mem_genericPoints_of_generalizingMap (Flat.generalizingMap f) hξ
  have hξa : ξa ∈ genericPoints (X.connectedComponentOpens a : Scheme.{u}) :=
    mem_genericPoints_source_of_isOpenImmersion (X.connectedComponentOpens a).ι hξ
  have hfa : (Y.connectedComponentOpens (f.continuous.connectedComponentsMap a)).ι (fa ξa) =
      f ξ := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resConnectedComponent_comp_ι]
    rfl
  have hga : (Y.connectedComponentOpens (g.continuous.connectedComponentsMap c)).ι (ga pt) =
      f ξ := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resConnectedComponent_comp_ι, Scheme.Hom.comp_apply]
    exact (Scheme.Hom.comp_apply i g ξ).symm.trans (by rw [hig])
  have hfaξ : fa ξa ∈ genericPoints _ :=
    mem_genericPoints_source_of_isOpenImmersion _ (by rw [hfa]; exact hy)
  have hgapt : ga pt ∈ genericPoints _ :=
    mem_genericPoints_source_of_isOpenImmersion _ (by rw [hga]; exact hy)
  have hDf := ringKrullDim_stalk_eq_sub_toNat_residueTrdeg fa hs ξa hfaξ
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_zero_of_mem_genericPoints _ ξa hξa] at hDf
  have hlef := toNat_residueTrdeg_le_of_relativeDimension fa s hs ξa
  have htrf : Cardinal.toNat (residueTrdeg fa ξa) = s := by
    have h0 : s - Cardinal.toNat (residueTrdeg fa ξa) = 0 := by exact_mod_cast hDf.symm
    omega
  have htr : residueTrdeg ga pt = residueTrdeg fa ξa := by
    rw [← residueTrdeg_eq_of_comp_eq_comp (P.connectedComponentOpens c).ι g ga _
        (Scheme.Hom.resConnectedComponent_comp_ι g c).symm pt,
      ← residueTrdeg_eq_of_comp_eq_comp (X.connectedComponentOpens a).ι f fa _
        (Scheme.Hom.resConnectedComponent_comp_ι f a).symm ξa]
    have h := residueTrdeg_comp i g ξ
    rw [hig, residueTrdeg_eq_zero_of_isPreimmersion i, add_zero] at h
    exact h.symm
  have hDg := ringKrullDim_stalk_eq_sub_toNat_residueTrdeg ga ht pt hgapt
  have hleg := toNat_residueTrdeg_le_of_relativeDimension ga t ht pt
  rw [htr, htrf] at hDg hleg
  have hdimP := Stacks.AlgebraicGeometry.ringKrullDim_stalk_eq_add_fiberRank_conormalModule
    i hreg ξ
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_zero_of_mem_genericPoints X ξ hξ, zero_add] at hdimP
  have hPc : ringKrullDim (P.presheaf.stalk (i ξ)) =
      ringKrullDim ((P.connectedComponentOpens c : Scheme.{u}).presheaf.stalk pt) :=
    ringKrullDim_eq_of_ringEquiv
      (asIso ((P.connectedComponentOpens c).ι.stalkMap pt)).commRingCatIsoToRingEquiv
  rw [hPc, hDg] at hdimP
  have h : t - s = Scheme.Modules.fiberRank (conormalModule i) ξ := by exact_mod_cast hdimP
  omega

end Codimension

/-! ### Classes of a flat morphism determined by their caps with fundamental classes -/

section Flat

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
  (hf : f ≫ sY = sX)

/-- **The flat-pullback class satisfies the formula over Cohen–Macaulay test schemes.** The class
`f^* ∈ A^{-r}(X ⟶ Y)` of Stacks 0B78 of a flat morphism of relative dimension `r` sends `[T]_n`
to `[X ×_Y T]_{n + r}` for every test scheme `T` pure of `δ`-dimension `n` (Stacks 02RB), so it
satisfies `Stacks.Chow.BivariantClass.CapFundamentalFormula` in every degree. -/
theorem flatPullbackBivariantClass_capFundamentalFormula (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension f r) (n : ℤ) :
    (flatPullbackBivariantClassOfInvertible C sX sY f hf r hr).CapFundamentalFormula C _ sX sY f hf
        n := by
  intro T t _ hT _ _
  exact IsBivariantFlatPullback.cap_fundamentalChowClass
      (hdesc := flatPullbackDescends C)
        (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C sX sY f hf r hr)
      t n (iSup_le fun V ↦ (congrArg (fun z : ℤ ↦ (z : EInt)) (hT V)).le)

/-- **A class of degree `-r` for a flat morphism of relative dimension `r` is determined by the
formula over Cohen–Macaulay test schemes.** Two classes in `A^{-r}(X ⟶ Y)` which both satisfy
`Stacks.Chow.BivariantClass.CapFundamentalFormula` in every degree are equal. -/
theorem BivariantClass.eq_of_capFundamentalFormula_of_flat {r : ℕ}
    (hr : AlgebraicGeometry.RelativeDimension f r)
    {c c' : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf (-(r : ℤ))}
    (hc : ∀ n, c.CapFundamentalFormula C _ sX sY f hf n)
    (hc' : ∀ n, c'.CapFundamentalFormula C _ sX sY f hf n) : c = c' := by
  refine BivariantClass.eq_of_cap_fundamentalChowClass_eq C _ sX sY f hf _ fun {T} t _ _ k ↦ ?_
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (t ≫ sY)
  by_cases hk : relativeDimension C.dimensionFunction (t ≫ sY) (genericPoint T) = k
  swap
  · rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_ne C _ genericPoints_eq_singleton hk,
      map_zero, map_zero, map_zero]
  have : Flat (pullback.snd f t) :=
    Flat.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f t) inferInstance
  have hT : ∀ W : irreducibleComponents T,
      deltaDimension C (t ≫ sY)
        ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set T) W.2⟩ = k := by
    intro W
    have hW : (W : Set T) = Set.univ :=
      Set.eq_univ_of_univ_subset (W.2.2 (IrreducibleSpace.isIrreducible_univ T)
        (Set.subset_univ _))
    have hgen : IsGenericPoint (genericPoint T) (W : Set T) := by
      rw [hW]
      exact genericPoint_spec T
    rw [deltaDimension_eq_of_isGenericPoint C (t ≫ sY)
      ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set T) W.2⟩ _ hgen, hk]
  have hstr : pullback.snd f t ≫ (t ≫ sY) = pullback.fst f t ≫ sX :=
    pullbackSnd_comp_structureMorphism hf t
  have hpure : ∀ W : irreducibleComponents (pullback f t : Scheme.{u}),
      relativeDimension C.dimensionFunction (pullback.fst f t ≫ sX) W.2.1.genericPoint =
        k + r := by
    intro W
    have h := deltaDimension_irreducibleComponent_eq_add_of_irreducible C (pullback.snd f t)
      (t ≫ sY) r (relativeDimension_pullbackSnd f hr t) W
    rw [deltaDimension_eq_of_isGenericPoint C _ ⟨Set.univ, IrreducibleSpace.isIrreducible_univ T,
        isClosed_univ⟩ (genericPoint T) (genericPoint_spec T), hk,
      deltaDimension_eq_of_isGenericPoint C _ _ W.2.1.genericPoint
        (W.2.1.isGenericPoint_genericPoint
          (isClosed_of_mem_irreducibleComponents (W : Set (pullback f t : Scheme.{u})) W.2)),
      hstr] at h
    exact h
  have hdim : schemeDeltaDimension C (pullback.fst f t ≫ sX) ≤ ((k - -(r : ℤ) : ℤ) : EInt) := by
    simpa using schemeDeltaDimension_le_of_forall_relativeDimension_le C
      (pullback.fst f t ≫ sX) (𝟙 _) (k := k - -(r : ℤ)) fun w ↦ by
        simpa using (relativeDimension_le_of_forall_genericPoint C _ hpure w).trans
          (le_of_eq (by ring))
  have hCM : ∀ ξ : (pullback f t : Scheme.{u}),
      relativeDimension C.dimensionFunction (pullback.fst f t ≫ sX) ξ = k - -(r : ℤ) →
      IsCohenMacaulayLocalRing (T.presheaf.stalk (pullback.snd f t ξ)) := by
    intro ξ hξ
    have h0 := ringKrullDim_stalk_eq_toNat_sub_relativeDimension C _ hpure ξ
    rw [hξ, show k + (r : ℤ) - (k - -(r : ℤ)) = 0 by ring] at h0
    have hgen : ξ ∈ genericPoints (pullback f t : Scheme.{u}) :=
      (ringKrullDim_stalk_eq_zero_iff_mem_genericPoints _ ξ).mp (by simpa using h0)
    exact isCohenMacaulayLocalRing_of_ringKrullDim_eq_zero _
      ((ringKrullDim_stalk_eq_zero_iff_mem_genericPoints T _).mpr
        (AlgebraicGeometry.mem_genericPoints_of_generalizingMap
          (Flat.generalizingMap (pullback.snd f t)) hgen))
  rw [hc k t hT hdim hCM, hc' k t hT hdim hCM]

variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- **The completed flat pullback satisfies the formula componentwise.** The class
`f^* ∈ A^*(X ⟶ Y)^∧` of a flat morphism whose relative dimension is `s_a` on the connected
component `X_a` is concentrated there in degree `-s_a`, where it satisfies
`Stacks.Chow.BivariantClass.CapFundamentalFormula` in every degree. -/
theorem hasCapFundamentalFormula_completedFlatPullback
    (hrel : ∀ a : _root_.ConnectedComponents X,
      ∃ r : ℕ, AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) r) :
    completedBivariantGroup.HasCapFundamentalFormula C (completedFlatPullback C sX sY f hf hrel)
      fun a ↦ -(flatComponentRelativeDimension f hrel a : ℤ) := fun a ↦
  ⟨by rw [completedFlatPullback_apply, DirectSum.of_eq_same], fun n ↦ by
    rw [completedFlatPullback_apply, DirectSum.of_eq_same]
    exact flatPullbackBivariantClass_capFundamentalFormula C _ _ _ _ _ _ n⟩

/-- **Completed classes of a flat morphism determined by the formula.** Let `f` be flat, of
relative dimension `s_a` on each connected component `X_a` of `X`. Two completed classes in
`A^*(X ⟶ Y)^∧` which are both concentrated on each `X_a` in degree `-s_a`, where they satisfy
`Stacks.Chow.BivariantClass.CapFundamentalFormula` in every degree, are equal. -/
theorem completedBivariantGroup.eq_of_hasCapFundamentalFormula
    (hrel : ∀ a : _root_.ConnectedComponents X,
      ∃ r : ℕ, AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) r)
    {c c' : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf}
    {d d' : _root_.ConnectedComponents X → ℤ}
    (hc : completedBivariantGroup.HasCapFundamentalFormula C c d)
    (hc' : completedBivariantGroup.HasCapFundamentalFormula C c' d')
    (hd : ∀ a, d a = -(flatComponentRelativeDimension f hrel a : ℤ))
    (hd' : ∀ a, d' a = -(flatComponentRelativeDimension f hrel a : ℤ)) : c = c' := by
  funext a
  rw [(hc a).1, (hc' a).1]
  have key : ∀ (q q' : ℤ) (hq : q = -(flatComponentRelativeDimension f hrel a : ℤ))
      (hq' : q' = -(flatComponentRelativeDimension f hrel a : ℤ))
      (x : BivariantClass C (gysinSystemOfInvertible C) ((X.connectedComponentOpens a).ι ≫ sX)
        ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap a)).ι ≫ sY)
        (f.resConnectedComponent a) (f.resConnectedComponent_comp_ι_comp hf a) q)
      (x' : BivariantClass C (gysinSystemOfInvertible C) ((X.connectedComponentOpens a).ι ≫ sX)
        ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap a)).ι ≫ sY)
        (f.resConnectedComponent a) (f.resConnectedComponent_comp_ι_comp hf a) q'),
      (∀ n, x.CapFundamentalFormula C _ _ _ _ _ n) →
      (∀ n, x'.CapFundamentalFormula C _ _ _ _ _ n) →
      DirectSum.of _ q x = DirectSum.of _ q' x' := by
    rintro q q' rfl rfl x x' hx hx'
    exact congrArg _ (BivariantClass.eq_of_capFundamentalFormula_of_flat C _ _ _ _
      (relativeDimension_flatComponentRelativeDimension f hrel a) hx hx')
  exact key _ _ (hd a) (hd' a) _ _ (hc a).2 (hc' a).2

end Flat

/-! ### Stacks 0FF4 -/

section Lci

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX)

/-- **The Gysin map of a factorization satisfies the formula componentwise, in the expected
degree.** On the connected component `X_a` of `X`, the class `i^! ∘ g^*` of Stacks 0FF3 is
concentrated in degree `r_a - t`, for `r_a` the rank of the normal sheaf of `i` on `X_a` and `t`
the relative dimension of `g` on the connected component of `P` containing `i(X_a)`, and there it
satisfies `Stacks.Chow.BivariantClass.CapFundamentalFormula` in every degree. -/
theorem SmoothFactorization.hasCapFundamentalFormula_gysinMap [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (F : SmoothFactorization f)
    (hlci : IsLocalCompleteIntersectionMorphism f) :
    letI : IsLocallyNoetherian F.ambient := LocallyOfFiniteType.isLocallyNoetherian (F.proj ≫ sY)
    completedBivariantGroup.HasCapFundamentalFormula C (F.gysinMap C sX sY hf hlci)
      fun a ↦ (componentRank ((VirtualNormalBundle.ofIsRegularImmersion F.imm
          (F.isRegularImmersion hlci)).toOpenFactor F.imm.liftCoborder_ι).bundle a : ℤ) +
        -(smoothComponentRelativeDimension F.proj (F.imm.continuous.connectedComponentsMap a) :
          ℤ) := by
  have : IsLocallyNoetherian F.ambient := LocallyOfFiniteType.isLocallyNoetherian (F.proj ≫ sY)
  rw [SmoothFactorization.gysinMap]
  exact ((hasCapFundamentalFormula_completedVirtualNormalGysinClassOfOpen C sX (F.proj ≫ sY)
    F.imm _ _ _ _ _).comp_completedFlatPullbackOfSmooth C sX (F.proj ≫ sY) F.imm _ sY
      F.proj rfl).copy C F.imm_proj _ hf

/-- **Stacks 0FF4 for the Gysin map of a factorization.** For a flat local complete intersection
morphism `f` and a factorization `f = g ∘ i` with `i` an immersion and `g` smooth, the class
`i^! ∘ g^*` of Stacks 0FF3 is the flat pullback `f^*` of Stacks 0B78. -/
theorem SmoothFactorization.gysinMap_eq_completedFlatPullbackOfFlatLCI [Flat f]
    (F : SmoothFactorization f) (hlci : IsLocalCompleteIntersectionMorphism f) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    F.gysinMap C sX sY hf hlci = completedFlatPullbackOfFlatLCI C sX sY f hf hlci := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian F.ambient := LocallyOfFiniteType.isLocallyNoetherian (F.proj ≫ sY)
  have : IsImmersion F.imm := F.isImmersion
  have : Smooth F.proj := F.isSmooth
  have hreg := F.isRegularImmersion hlci
  have hrel := exists_relativeDimension_resConnectedComponent_of_isLocalCompleteIntersection f hlci
  refine completedBivariantGroup.eq_of_hasCapFundamentalFormula C sX sY f hf hrel
    (F.hasCapFundamentalFormula_gysinMap C sX sY hf hlci)
    (hasCapFundamentalFormula_completedFlatPullback C sX sY f hf hrel) (fun a ↦ ?_) fun _ ↦ rfl
  obtain ⟨ξ, hξ, rfl⟩ := exists_mem_genericPoints_mk_eq a
  have hE := fiberRank_conormalModule_add_of_flat F.imm F.proj F.imm_proj hreg hξ
    (relativeDimension_flatComponentRelativeDimension f hrel _)
    (relativeDimension_smoothComponentRelativeDimension F.proj _)
  have hrank : (componentRank ((VirtualNormalBundle.ofIsRegularImmersion F.imm hreg).toOpenFactor
      F.imm.liftCoborder_ι).bundle (_root_.ConnectedComponents.mk ξ) : ℤ) =
        Scheme.Modules.fiberRank (conormalModule F.imm) ξ := by
    rw [← fiberRank_eq_componentRank _ _ ξ (mem_connectedComponentOpens_mk ξ)]
    exact congrArg _ (Scheme.Modules.fiberRank_dualSheaf (conormalModule F.imm)
      (isFiniteLocallyFree_conormalModule F.imm hreg) ξ)
  dsimp only
  rw [hrank]
  omega

/-- **Stacks 0FF4.** Let `f : X ⟶ Y` be a local complete intersection morphism of schemes locally
of finite type over the base for which the Gysin map exists. If `f` is flat, its Gysin map
`f^! ∈ A^*(X ⟶ Y)^∧` (Stacks 0FF3) is the flat-pullback class `f^*` of Stacks 0B78, read in the
completed bivariant group because the relative dimension of `f` is only locally constant. -/
@[stacks 0FF4 "f^! = f^* in the completed bivariant group A^*(X → Y)^∧, the relative dimension \
of the flat morphism f being only locally constant"]
theorem lciGysinMap_eq_completedFlatPullbackOfFlatLCI [Flat f]
    (hlci : IsLocalCompleteIntersectionMorphism f) (h : GysinMapExists f) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    lciGysinMap C sX sY hf hlci h = completedFlatPullbackOfFlatLCI C sX sY f hf hlci :=
  SmoothFactorization.gysinMap_eq_completedFlatPullbackOfFlatLCI C sX sY hf _ hlci

end Lci

end Stacks.Chow

end
