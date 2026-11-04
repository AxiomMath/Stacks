module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientHigherDirectImageStalkLinearIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveSpecializationMapInput
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LevelAdjunctStalkSplitMono

/-!
# The specialization injection at the origin of Laumon's degeneration

In Laumon's degeneration argument ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), piece
P5 of `Stacks.EtaleCohomology.LaumonDegenerationFamilyInput`) the family sheaf
`K = pr₁^*ℱ_{σ₁} ⊗ L_ψ'(t (xⁿ⁰ + c x))` on `𝔸² = Spec k'[x][t]`
(`Stacks.EtaleCohomology.laumonFamilySheaf`) has `G = R¹pr₂! K` on the `t`-line `W`
(`Stacks.EtaleCohomology.laumonFamilyHigherDirectImage`). At the origin `y` (`t = 0`) the
specialization map embeds the stalk `ℚ_ℓ ⊗ G_ȳ` into the inertia invariants `τ^{I_y}` of the
representation of a sheaf `F_V` on a punctured neighbourhood `V` of `y` receiving `G|_V` by a split
monomorphism `χ` (`Stacks.EtaleCohomology.curveSpecializationMapInput`), and the stalk is
`H¹_c(𝔸¹_k̄, ℱ_σ ⊗ ℚ_ℓ)` with the Frobenius `(π^*) ^ {d_y}`, `#κ(y) = q ^ {d_y}`. Composing gives
the injection `J` of `Stacks.EtaleCohomology.LaumonDegenerationFamilyInput`
(`Stacks.EtaleCohomology.exists_laumonSpecializationInjection`).

The stalk is identified in three steps:

* (Θ) `E`-linear proper base change at the stalk,
  `H¹_c(Y_k̄, K|_Y ⊗ ℚ_ℓ) ≃ ℚ_ℓ ⊗ G_ȳ` for the fibre `Y` of `pr₂` over `y`
  (`Stacks.EtaleCohomology.CoefficientHigherDirectImageStalkLinearIsoInput`);
* (F0, BC) the fibre over `t = 0` is `𝔸¹_{κ(y)}` with the kernel `0`, so `K|_Y` is the inverse
  image of `ℱ_σ`, and the base change `k → κ(y)` identifies `H¹_c(Y_k̄, K|_Y ⊗ ℚ_ℓ)` with
  `H¹_c(U_k̄, ℱ_σ ⊗ ℚ_ℓ)`, carrying the Frobenius of `κ(y)` to `(π^*) ^ {d_y}`
  (`Stacks.EtaleCohomology.LaumonOriginFibreCohomologyInput`);
* (H2) `G` has no punctual sections: the kernels of the stalks of the units `Gₙ → j_* j⁻¹ Gₙ` at
  `ȳ` are killed by a fixed power of `ℓ`
  (`Stacks.EtaleCohomology.LaumonFamilyNoPunctualSectionsInput`).

## Main definitions

* `Stacks.EtaleCohomology.LaumonOriginFibreCohomologyInput` (F0, BC).
* `Stacks.EtaleCohomology.LaumonFamilyNoPunctualSectionsInput` (H2).

## Main results

* `Stacks.EtaleCohomology.exists_laumonSpecializationInjection`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.Frobenius
open scoped Pointwise Matrix

universe u

namespace Stacks.EtaleCohomology

/-- **(F0, BC) The fibre of Laumon's family over the origin**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): let
`K = pr₁^*ℱ_{σ₁} ⊗ L_ψ'(t (xⁿ⁰ + c x))` be the family sheaf on `Spec k'[x][t]`
(`Stacks.EtaleCohomology.laumonFamilySheaf`, `σ₁` the pullback of `σ` to `𝔸¹_{k'}`,
`ψ' = ψ ∘ Tr_{k'/k}`), `y` the origin `t = 0` of the `t`-line, with `#κ(y) = q ^ {d_y}`, and
`k̄` an algebraic closure of `k` with a compatible embedding of `κ(y)`. For any fibre `Y` of
`pr₂` over `y` with a compactification over `κ(y)`, there is an `E`-linear isomorphism
`H¹_c(Y_k̄, K|_Y ⊗ ℚ_ℓ) ≃ H¹_c(U_k̄, ℱ_σ ⊗ ℚ_ℓ)` carrying the Frobenius of `κ(y)` to
`(π_U^*) ^ {d_y}`: the kernel vanishes at `t = 0`, so `K|_Y` is the inverse image of `ℱ_σ` along
`Y ≅ U ×_k κ(y) → U`, and the base change of `H¹_c` along `k → κ(y)` carries the Frobenius of
`κ(y)` to the `d_y`-th power of that of `k`. -/
public def LaumonOriginFibreCohomologyInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fintype k] (U : B.Scheme) [ConnectedSpace U.1] [IsNoetherian U.1]
    (f : U.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsIso e]
    (_ : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n)
    (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ))
    (ψ : AddChar k E) (n₀ : ℕ) (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] (c : k')
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (hz : (z.map (laumonFamilyPr₁ k')).map (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) = x)
    (p₀ : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonKernel k' n₀ c)))
    (hσ₁ : Continuous (restrictScalarsRep b (σ.comp (hz ▸ (etaleFundamentalGroupMap
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
        (z.map (laumonFamilyPr₁ k'))).toMonoidHom))))
    (y : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1)
    (_ : y.asIdeal = Ideal.span {Polynomial.X})
    [Fintype ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y)]
    [CharP ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y) p] (dy : ℕ)
    (hcardy : Fintype.card
      ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y) = p ^ (n * dy))
    [Algebra ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y) kbar]
    (_ : ∀ a : k, algebraMap
        ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y)
        kbar (laumonPointRingHom (𝟙 _) y (algebraMap k (Polynomial k') a)) = algebraMap k kbar a)
    (Y : B.Scheme) [IsNoetherian Y.1]
    (i : Y ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS)
    (fY : Y.1 ⟶
      Spec (.of ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y)))
    [LocallyOfFiniteType fY] [QuasiCompact fY] [IsSeparated fY],
    IsPullback (B.inclusion.map i) fY (B.inclusion.map (laumonFamilyProjection k' B hS hL))
      ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.fromSpecResidueField y) →
    ∀ jY : CompactificationOf (Over.mk fY),
    haveI : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
      inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
    letI K := LAdicSheaf.CoefficientSheaf.inverseImage i
      (laumonFamilySheaf k' B hS b (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c
        z p₀ _ hσ₁)
    letI := K.rationalCohomologyModule fY jY kbar 1 E
    letI := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 1 E
    ∃ eY : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar
        K.toLAdicSheaf 1 ≃ₗ[E]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1,
      ∀ v, eY (K.rationalGeometricCompactlySupportedFrobenius fY jY kbar 1 E p (n * dy) hcardy v) =
        (((restrictScalarsRepCoefficientSheaf B U x b σ
          hσ).rationalGeometricCompactlySupportedFrobenius f j kbar 1 E p n hcard) ^ dy) (eY v)

/-- **(H2) `G = R¹pr₂! K` has no punctual sections**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): for the family sheaf
`K = pr₁^*ℱ_{σ₁} ⊗ L_ψ'(t h(x))`, `h = xⁿ⁰ + c x ≠ 0`, `ψ'` nontrivial, a nonempty open
`j : V ⟶ W` of the `t`-line `W` and a point `y ∉ V`, the kernels of the stalks at `ȳ` of the units
`Gₙ → j_* j⁻¹ Gₙ` are killed by a fixed power of `ℓ`. (Since `R⁰pr₂! K = 0`, the Leray
edge map identifies `H⁰_c(W_k̄, Gₙ)` with `H¹_c(𝔸²_k̄, Kₙ)`, which vanishes because
`R pr₁! L_ψ'(t h(x))` is supported on `h = 0`, where `L_ψ'` is trivial along the `t`-line; a
section of `Gₙ` supported at `ȳ` is a compactly supported section.) -/
public def LaumonFamilyNoPunctualSectionsInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [Fact ℓ.Prime]
    (k' : Type u) [Field k'] [Fintype k']
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    {E : Type} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) (ψ' : AddChar k' E) (_ : ψ' ≠ 1) (n₀ : ℕ) (c : k')
    (_ : (Polynomial.X ^ n₀ + Polynomial.C c * Polynomial.X : Polynomial k') ≠ 0)
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (p₀ : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonKernel k' n₀ c))) {m : ℕ}
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁))
    (jg : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyProjection k' B hS hL))))
    (V : B.Scheme) [IsNoetherian V.1] [Nonempty V.1]
    (jW : V.1 ⟶ (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1) [IsOpenImmersion jW]
    (y : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1) (_ : y ∉ Set.range jW.base),
    haveI : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1 :=
      inferInstanceAs (IsNoetherian (Spec (.of (Polynomial k'))))
    ∃ M : ℕ, ∀ (n : ℕ)
      (w : finiteLevelStalk B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
        ℓ (laumonFamilyHigherDirectImage k' B hS hL b ψ' n₀ c z p₀ σ₁ hσ₁ jg).toLAdicSheaf
        (geometricPointAt _ y) n),
      (levelUnitStalkMap (ObjectProperty.homMk jW :
          V ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
        (laumonFamilyHigherDirectImage k' B hS hL b ψ' n₀ c z p₀ σ₁ hσ₁ jg).toLAdicSheaf
        (geometricPointAt _ y) n).hom w = 0 → (ℓ ^ M) • w = 0

/-- **The specialization injection at the origin of Laumon's degeneration** (piece P5 of
`Stacks.EtaleCohomology.LaumonDegenerationFamilyInput`,
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).
Let `K` be the family sheaf on `Spec k'[x][t]` (`Stacks.EtaleCohomology.laumonFamilySheaf`), `G`
its `R¹pr₂!` on the `t`-line `W` (`Stacks.EtaleCohomology.laumonFamilyHigherDirectImage`), `y` the
origin with `#κ(y) = q ^ {d_y}`, `V ⊆ W ∖ {y}` a nonempty open with the local data of Weil II 1.8.4
at `y`, `F_V` a sheaf on `V` with coefficients in those of `G`, `χ : G|_V → F_V` an
`O`-compatible morphism with a left inverse, and `ρ, φ, ψ, N, τ, P, Q` the data of
`Stacks.EtaleCohomology.exists_restrictScalarsRep_of_isLisse` for `F_V`. Then there is an
injective `E`-linear map `J : H¹_c(U_k̄, ℱ_σ ⊗ ℚ_ℓ) → τ^{I_y}` carrying `(π_U^*) ^ {d_y}` to
`τ(φ Fr⁻¹)`: the J clause of `Stacks.EtaleCohomology.LaumonDegenerationFamilyInput`. The inputs
are `E`-linear proper base change at the stalk (Θ), the fibre over the origin (F0, BC) and the
absence of punctual sections (H2). For `F_V = G|_V`, `χ = 𝟙`, `τ` is the representation of
`G|_V`. -/
public theorem exists_laumonSpecializationInjection
    (hΘ : CoefficientHigherDirectImageStalkLinearIsoInput.{u})
    (hF0 : LaumonOriginFibreCohomologyInput.{u})
    (hH2 : LaumonFamilyNoPunctualSectionsInput.{u})
    (B : BigEtaleSite.{u}) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fintype k] (U : B.Scheme) [ConnectedSpace U.1] [IsNoetherian U.1]
    (f : U.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsIso e]
    (he : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n)
    (hℓp : ℓ ≠ p) (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ))
    (ψ : AddChar k E) (n₀ : ℕ) (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] (c : k')
    (hψ : ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom ≠ 1)
    (hh : (Polynomial.X ^ n₀ + Polynomial.C c * Polynomial.X : Polynomial k') ≠ 0)
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (hz : (z.map (laumonFamilyPr₁ k')).map (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) = x)
    (p₀ : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonKernel k' n₀ c)))
    (hσ₁ : Continuous (restrictScalarsRep b (σ.comp (hz ▸ (etaleFundamentalGroupMap
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
        (z.map (laumonFamilyPr₁ k'))).toMonoidHom))))
    (jg : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyProjection k' B hS hL))))
    -- the open `V` of the `t`-line
    (V : B.Scheme) [IsNoetherian V.1] [ConnectedSpace V.1] [IrreducibleSpace V.1] [IsAffine V.1]
    (fV : V.1 ⟶ Spec (.of k'))
    [LocallyOfFiniteType fV] [QuasiCompact fV] [IsSeparated fV] [SmoothOfRelativeDimension 1 fV]
    (jV : CompactificationOf (Over.mk fV)) (kbar' : Type u) [Field kbar'] [Algebra k' kbar']
    [IsAlgClosure k' kbar']
    [ConnectedSpace ↥(Limits.pullback fV (Spec.map (CommRingCat.ofHom (algebraMap k' kbar'))))]
    (n' : ℕ) [CharP k' p] (hcard' : Fintype.card k' = p ^ n')
    (fW : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1 ⟶ Spec (.of k'))
    [LocallyOfFiniteType fW] [QuasiCompact fW] [IsSeparated fW] [SmoothOfRelativeDimension 1 fW]
    (eW : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1 ⟶ Spec (.of (Polynomial k')))
    [IsOpenImmersion eW]
    (heW : eW ≫ Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k'))) = fW)
    (jW : V.1 ⟶ (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1) [IsOpenImmersion jW]
    (hjW : jW ≫ fW = fV)
    -- the origin `y`
    (y : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1)
    (hy0 : y.asIdeal = Ideal.span {Polynomial.X}) (hyc : IsClosed ({y} : Set _))
    (hyV : y ∉ Set.range jW.base) (hy : jW.base (genericPoint V.1) ⤳ y) (dy : ℕ)
    (hcardy : Nat.card ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y) =
      (p ^ n) ^ dy)
    -- the local field at `y`
    (L Ω : Type u) [Field L] [Field Ω]
    [Algebra (V.1.residueField (genericPoint V.1)) L]
    [IsSepClosure (V.1.residueField (genericPoint V.1)) L]
    [Algebra L Ω] [Algebra (V.1.residueField (genericPoint V.1)) Ω]
    [IsScalarTower (V.1.residueField (genericPoint V.1)) L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic (V.1.residueField (genericPoint V.1)) Ω]
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (V.1.residueField (genericPoint V.1))]
    [IsFractionRing A (V.1.residueField (genericPoint V.1))] [Algebra A L]
    [IsScalarTower A (V.1.residueField (genericPoint V.1)) L]
    [Finite (IsLocalRing.ResidueField A)]
    (eA : A ≃+* (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.presheaf.stalk y)
    (hA : ∀ a : A, algebraMap A (V.1.residueField (genericPoint V.1)) a =
      (curveLocalRingToFunctionField jW hy).hom (eA a))
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (Fr : Gal(L / V.1.residueField (genericPoint V.1)))
    (hFrD :
      letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
        (integralClosure A L)
      Fr ∈ MulAction.stabilizer Gal(L / V.1.residueField (genericPoint V.1)) P)
    (hFr :
      letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
        (integralClosure A L)
      ∀ b : integralClosure A L, Fr • b - b ^ Nat.card (IsLocalRing.ResidueField A) ∈ P)
    -- the sheaf `F_V` with a split `O`-compatible morphism `χ : G|_V → F_V`
    (FV : LAdicSheaf.CoefficientSheaf B V ℓ _)
    (χ : ((laumonFamilyHigherDirectImage k' B hS hL b
        (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jg).inverseImage
        (ObjectProperty.homMk jW :
          V ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)).toLAdicSheaf ⟶
      FV.toLAdicSheaf)
    (hχ : ∀ o, ((laumonFamilyHigherDirectImage k' B hS hL b
        (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jg).inverseImage
        (ObjectProperty.homMk jW :
          V ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)).act o ≫
          χ = χ ≫ FV.act o)
    (χ' : FV.toLAdicSheaf ⟶ ((laumonFamilyHigherDirectImage k' B hS hL b
        (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jg).inverseImage
        (ObjectProperty.homMk jW :
          V ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)).toLAdicSheaf)
    (hχχ' : χ ≫ χ' = 𝟙 _)
    -- the representation of `F_V` (the data of `exists_restrictScalarsRep_of_isLisse`)
    (r : ℕ) (ρ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
    (φ : FV.toLAdicSheaf ⟶ LAdicSheaf.representationSheaf B V _ ρ hρ)
    (ψ₀ : LAdicSheaf.representationSheaf B V _ ρ hρ ⟶ FV.toLAdicSheaf) (N : ℕ)
    (hφψ : φ ≫ ψ₀ = (ℓ ^ N) • 𝟙 _) (hψφ : ψ₀ ≫ φ = (ℓ ^ N) • 𝟙 _)
    (mτ : ℕ) (τ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin mτ) E)
    (Pm : Matrix (Fin r) (Fin (mτ * d)) ℚ_[ℓ]) (Qm : Matrix (Fin (mτ * d)) (Fin r) ℚ_[ℓ])
    (hPQ : Pm * Qm = 1)
    (hα : ∀ e' : E, Qm * isogenyCoefficientAlgHom B V _ FV ρ hρ φ ψ₀ N E hφψ hψφ
      (algebraMap_conjIntegralSubring_algebraMap _ _) e' * Pm =
        restrictScalarsMatrix b (Matrix.scalar (Fin mτ) e'))
    (hτ : ∀ g, Qm * (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
        (haveI := compactSpace_etaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
          (V.1.residueField (genericPoint V.1)) Ω).map
            (V.1.fromSpecResidueField (genericPoint V.1)))
         integralModel ρ hρ g)).val * Pm = (restrictScalarsRep b τ g).val) :
    letI := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 1 E
    letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
      (integralClosure A L)
    ∃ J : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
        (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1 →ₗ[E]
        Representation.invariants ((matrixRepresentation τ).comp
          (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P).subtype),
      Function.Injective J ∧
      J ∘ₗ (((restrictScalarsRepCoefficientSheaf B U x b σ
          hσ).rationalGeometricCompactlySupportedFrobenius f j kbar 1 E p n hcard) ^ dy) =
        ((Matrix.toLin' ((τ ((galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr⁻¹) :
          GL (Fin mτ) E) : Matrix (Fin mτ) (Fin mτ) E)).restrict
        (toLin'_mem_invariants_of_mem_normalizer τ
          (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P)
          (map_inv_mem_normalizer_map_inertia A (V.1.residueField (genericPoint V.1)) L P
            (galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr hFrD))) ∘ₗ J := by
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial k'))))
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  let W := Stacks.ArtinSchreier.specObject (Polynomial k') B hL
  let ψ' := ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom
  let G := laumonFamilyHigherDirectImage k' B hS hL b ψ' n₀ c z p₀ _ hσ₁ jg
  have hOE := algebraMap_conjIntegralSubring_algebraMap (ℓ := ℓ)
    (representationSheafConj B (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS)
      z (restrictScalarsRep b (laumonFamilyRep k' ψ' n₀ c z p₀ _))
      (continuous_restrictScalarsRep_laumonFamilyRep k' b ψ' n₀ c z p₀ _ hσ₁))
    (restrictScalarsScalarAlgHom b m)
  have hyf : Finite (W.1.residueField y) := finite_residueField fW y hyc
  -- (H2) no punctual sections
  let := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 1 E
  have : Nonempty V.1 := (inferInstance : IrreducibleSpace V.1).toNonempty
  obtain ⟨M, hM⟩ := hH2 B ℓ k' hS hL b ψ' hψ n₀ c hh z p₀ _ hσ₁ jg V jW y hyV
  -- the specialization map
  obtain ⟨sp, hsp, hspF⟩ := curveSpecializationMapInput.{u} B V ℓ k' fV jV kbar' p n' hcard' hℓp
    W fW eW heW jW hjW y hyc hyV hy L Ω A eA hA P Fr hFrD hFr hyf G E hOE b FV χ hχ r ρ hρ φ ψ₀
    N hφψ hψφ mτ τ Pm Qm hPQ hα hτ M (fun n w h => hM n w
      (levelUnitStalkMap_eq_zero_of_levelAdjunctStalkMap_eq_zero _ _ _ χ χ' hχχ' n w h))
  -- the rational stalk is finite dimensional, as it embeds into `E ^ mτ`
  let := G.rationalStalkModule (geometricPointAt W.1 y) E
  have := G.rationalStalkModule_isScalarTower (geometricPointAt W.1 y) E hOE
  have : Module.Finite E (LAdicSheaf.rationalStalkLeft B W ℓ G.toLAdicSheaf
      (geometricPointAt W.1 y)) := Module.Finite.of_injective sp hsp
  have : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalStalkLeft B W ℓ G.toLAdicSheaf
      (geometricPointAt W.1 y)) := Module.Finite.trans E _
  -- the residue field at `y` and its embedding into `k̄`
  let : Fintype (W.1.residueField y) := Fintype.ofFinite _
  have : CharP (W.1.residueField y) p :=
    charP_of_injective_ringHom ((laumonPointRingHom (𝟙 W) y).comp Polynomial.C).injective p
  have hcardY : Fintype.card (W.1.residueField y) = p ^ (n * dy) := by
    rw [← Nat.card_eq_fintype_card, hcardy, pow_mul]
  let : Algebra k (W.1.residueField y) := laumonPointAlgebra (𝟙 W) y k
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  let ι : W.1.residueField y →ₐ[k] kbar := IsAlgClosed.lift
  let : Algebra (W.1.residueField y) kbar := ι.toRingHom.toAlgebra
  have : IsScalarTower k (W.1.residueField y) kbar :=
    IsScalarTower.of_algebraMap_eq fun a => (ι.commutes a).symm
  have : IsAlgClosure (W.1.residueField y) kbar :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := k) _⟩
  have hι : ∀ a : k, algebraMap (W.1.residueField y) kbar
      (laumonPointRingHom (𝟙 W) y (algebraMap k (Polynomial k') a)) = algebraMap k kbar a :=
    ι.commutes
  -- (Θ) proper base change at the stalk
  refine hΘ B ℓ k' (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) W
    (laumonFamilyProjection k' B hS hL) jg fW ⟨y, hyc⟩ kbar p (n * dy) hcardY _ ?_
  intro Y _ i fY _ _ _ hpb jY hY
  obtain ⟨Θ, hΘF⟩ := hY (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ _ hσ₁) 1 E hOE
  let := ((laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ _ hσ₁).higherDirectImageShriek B ℓ
    (laumonFamilyProjection k' B hS hL) jg 1).rationalStalkModule (geometricPointAt W.1 y) E
  let := (LAdicSheaf.CoefficientSheaf.inverseImage i
    (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ _ hσ₁)).rationalCohomologyModule fY jY kbar 1 E
  -- (F0, BC) the fibre over the origin
  obtain ⟨eY, heY⟩ := hF0 B ℓ k U f e he j kbar p n hcard x E b σ hσ ψ n₀ k' c hS hL z hz p₀
    hσ₁ y hy0 dy hcardY hι Y i fY hpb jY
  let eS := eY.symm.trans Θ
  have hS' : eS.toLinearMap ∘ₗ
      ((restrictScalarsRepCoefficientSheaf B U x b σ
          hσ).rationalGeometricCompactlySupportedFrobenius f j kbar 1 E p n hcard) ^ dy =
      G.rationalStalkFrobenius E y hyf ∘ₗ eS.toLinearMap := by
    refine LinearMap.ext fun v => ?_
    have h1 := heY (eY.symm v)
    rw [LinearEquiv.apply_symm_apply] at h1
    exact (congrArg Θ (eY.symm_apply_eq.2 h1.symm)).trans (LinearMap.congr_fun hΘF (eY.symm v))
  exact ⟨sp ∘ₗ eS.toLinearMap,
    injective_comp_linearEquiv_and_comp_pow sp hsp _ _ hspF _ dy eS hS'⟩

end Stacks.EtaleCohomology

end
