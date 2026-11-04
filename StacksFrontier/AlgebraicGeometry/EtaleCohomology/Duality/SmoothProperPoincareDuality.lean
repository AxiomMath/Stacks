module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PoincareDualityInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveCupProductLevel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurvePoincareDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LocalPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.GoodTraceExistence

/-!
# Poincaré duality with `ℤ/ℓ` coefficients on a connected smooth proper variety

Let `k` be an algebraically closed field, `ℓ` a prime and `Λ = ℤ/ℓ`. For `X` connected, smooth
of relative dimension `d` and proper over `k`, Poincaré duality is the perfectness of the Yoneda
pairing

`Ext^q_X(Λ, F) × Ext^{2d-q}_X(F, Λ) → H^{2d}(X, Λ) → Λ`

for every locally constant sheaf `F` of finite type and every injective trace on `H^{2d}(X, Λ)`.

The inputs are those of the induction on the dimension
(`Stacks.EtaleCohomology.isDualityPerfect_unitSheaf_of_isGoodTrace`): local purity, duality on a
dense open of every smooth irreducible variety for good traces
(`Stacks.EtaleCohomology.PoincareDualityCore`), and the existence of a good trace on
`H^{2d}(T, Λ)` for every connected finite étale `T → X`. Then:

* duality in degrees `(2d, 0)` at `Λ_T` reads `H^{2d}(T, Λ) ≅ Hom(H^0(T, Λ), Λ)`, and
  `H^0(T, Λ) = Λ` for `T` connected, so `#H^{2d}(T, Λ) = ℓ`
  (`Stacks.EtaleCohomology.natCard_ext_unitSheaf_of_isDualityPerfect`);
* every injective trace on `H^{2d}(T, Λ)` is then a good trace followed by an automorphism of
  `Λ`, so duality at `Λ_T` holds for it
  (`CategoryTheory.Abelian.Ext.isDualityPerfect_comp_addEquiv_iff`);
* and these are the inputs of the lisse step
  `Stacks.EtaleCohomology.isDualityPerfect_of_isFiniteTypeLocallyConstant_of_proper`.

The declarations below are in the namespace `Stacks.EtaleCohomology`.

## Main definitions

* `PoincareDualityCore`: duality on a dense open, for good traces.

## Main results

* `natCard_ext_unitSheaf_of_isDualityPerfect`: `#H^{2d}(T, Λ) = ℓ`.
* `isDualityPerfect_unitSheaf_of_isGoodTrace_ofProper`.
* `natCard_ext_unitSheaf_of_exists_isGoodTrace`.
* `isDualityPerfect_of_isFiniteTypeLocallyConstant_of_exists_isGoodTrace`:
  Poincaré duality with lisse `ℤ/ℓ` coefficients.
* `isDualityPerfect_of_isFiniteTypeLocallyConstant_of_topCohomologyPointClass`:
  the same, with the good traces supplied by the computation of the top cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe w v u

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {A A' : Type*} [AddCommGroup A] [AddCommGroup A']

/-- **Duality does not see an automorphism of the coefficients**: for `e : A ≃+ A'`, duality
holds at `F` for the trace `e ∘ t` if and only if it holds for `t`. -/
theorem isDualityPerfect_comp_addEquiv_iff {O D : C} {N : ℕ} (t : Ext.{w} O D N →+ A)
    (e : A ≃+ A') (F : C) :
    IsDualityPerfect O D N (e.toAddMonoidHom.comp t) F ↔ IsDualityPerfect O D N t F := by
  refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun h => ?_
  let post : (Ext.{w} F D j →+ A) ≃ (Ext.{w} F D j →+ A') :=
    { toFun φ := e.toAddMonoidHom.comp φ
      invFun φ := e.symm.toAddMonoidHom.comp φ
      left_inv φ := by ext; simp
      right_inv φ := by ext; simp }
  have hcomp : dualityPairing O D N (e.toAddMonoidHom.comp t) F h =
      post ∘ dualityPairing O D N t F h := by
    funext x
    ext y
    rfl
  rw [hcomp]
  exact Function.Bijective.of_comp_iff' post.bijective _

end CategoryTheory.Abelian.Ext

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]

/-- **Poincaré duality on a dense open, for good traces**: for every smooth irreducible `W` of
relative dimension `e` over `k` with noetherian underlying space, every compactification
`j : W → X̄` of dimension at most `e` and every good trace `t` on `H^{2e}_c(W, ℤ/ℓ)`, duality
holds at `j_! Λ` of the constant sheaf on some dense open `W₀ ⊆ W`, with
`Ext^q_X̄(j_! Λ_{W₀}, j_! Λ_W) = 0` for `q > 2e`. In the proof of Poincaré duality `W₀` is an
elementary fibration over a smooth variety of dimension `e - 1`; this is the hypothesis `hcore`
of `Stacks.EtaleCohomology.isDualityPerfect_unitSheaf_of_isGoodTrace`. -/
def PoincareDualityCore : Prop :=
  ∀ (e : ℕ) (W : Scheme.{u}) (f : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension e f]
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
          (unitSheaf (X := W) ℓ)) q)

variable {k}

/-- **The top cohomology of a connected scheme with duality has `ℓ` elements**: if duality holds
at `Λ_T` for `D = Λ_T` and a trace on `H^{2d}(T, Λ)`, then in degrees `(2d, 0)` it identifies
`H^{2d}(T, Λ)` with `Hom(H^0(T, Λ), Λ)`, and `H^0(T, Λ) = Λ` for `T` connected. -/
theorem natCard_ext_unitSheaf_of_isDualityPerfect {T : Scheme.{u}} [ConnectedSpace T] (d : ℕ)
    (t : Ext (unitSheaf (X := T) ℓ) (unitSheaf ℓ) (2 * d) →+ ZMod ℓ)
    (h : Ext.IsDualityPerfect (unitSheaf (X := T) ℓ) (unitSheaf ℓ) (2 * d) t (unitSheaf ℓ)) :
    Finite (Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) (2 * d)) ∧
      Nat.card (Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) (2 * d)) = ℓ := by
  have hp : ℓ.Prime := Fact.out
  have h0 : Nat.card (Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) 0) = ℓ :=
    LevelChange.natCard_ext_zero_unitSheaf ℓ
  have : Finite (Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) 0) :=
    Nat.finite_of_card_ne_zero (by rw [h0]; exact hp.ne_zero)
  have hcard : Nat.card (Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) 0 →+ ZMod ℓ) = ℓ := by
    rw [natCard_addMonoidHom_zmod, h0]
  have : Finite (Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) 0 →+ ZMod ℓ) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  let e := Equiv.ofBijective _ (h (2 * d) 0 (add_zero _))
  exact ⟨Finite.of_equiv _ e.symm, (Nat.card_congr e).trans hcard⟩

variable [IsAlgClosed k]

/-- **Poincaré duality at `Λ` on a connected smooth proper variety, for a good trace**: `T`
compactified by itself, `Λ_T = 𝟙_! Λ_T`. -/
theorem isDualityPerfect_unitSheaf_of_isGoodTrace_ofProper (hpurity : LocalPurity ℓ k)
    (hcore : PoincareDualityCore ℓ k) {T : Scheme.{u}} (g : T ⟶ Spec (.of k)) [IsProper g]
    (d : ℕ) [SmoothOfRelativeDimension d g] [ConnectedSpace T]
    (t : Ext (unitSheaf (X := T) ℓ) (unitSheaf ℓ) (2 * d) →+ ZMod ℓ)
    (ht : IsGoodTrace ℓ k d g (CompactificationOf.ofProper g)
      (Ext.transportTrace t (Iso.refl _) (unitSheafIsoExtensionByZeroId ℓ T))) :
    Ext.IsDualityPerfect (unitSheaf (X := T) ℓ) (unitSheaf ℓ) (2 * d) t (unitSheaf ℓ) := by
  have : Smooth g := SmoothOfRelativeDimension.smooth d g
  have : CompactSpace T := ⟨by
    simpa using QuasiCompact.isCompact_preimage (f := g) Set.univ isOpen_univ isCompact_univ⟩
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsNoetherian T := ⟨⟩
  have : IrreducibleSpace T := irreducibleSpace_of_smooth_of_connectedSpace g
  have : Nonempty T := ConnectedSpace.toNonempty
  exact (Ext.isDualityPerfect_transport_iff t (Iso.refl _)
    (unitSheafIsoExtensionByZeroId ℓ T) _).2
    (Ext.isDualityPerfect_of_iso (unitSheafIsoExtensionByZeroId ℓ T).symm
      (isDualityPerfect_unitSheaf_of_isGoodTrace ℓ hpurity hcore d g
        (CompactificationOf.ofProper g)
        (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field d g).le _ ht).1)

/-- **`#H^{2d}(X, ℤ/ℓ) = ℓ`** for `X` connected, smooth of relative dimension `d` and proper over
`k`, given local purity, the core `hcore` and an injective good trace on `H^{2d}(X, ℤ/ℓ)`. -/
theorem natCard_ext_unitSheaf_of_exists_isGoodTrace (hpurity : LocalPurity ℓ k)
    (hcore : PoincareDualityCore ℓ k) {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (d : ℕ) [SmoothOfRelativeDimension d f] [ConnectedSpace X]
    (hgood : ∃ t : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) (2 * d) →+ ZMod ℓ,
      Function.Injective t ∧ IsGoodTrace ℓ k d f (CompactificationOf.ofProper f)
        (Ext.transportTrace t (Iso.refl _) (unitSheafIsoExtensionByZeroId ℓ X))) :
    Finite (Ext (unitSheaf (X := X) ℓ) (unitSheaf (X := X) ℓ) (2 * d)) ∧
      Nat.card (Ext (unitSheaf (X := X) ℓ) (unitSheaf (X := X) ℓ) (2 * d)) = ℓ := by
  obtain ⟨t, -, ht⟩ := hgood
  exact natCard_ext_unitSheaf_of_isDualityPerfect ℓ d t
    (isDualityPerfect_unitSheaf_of_isGoodTrace_ofProper ℓ hpurity hcore f d t ht)

/-- **Poincaré duality at `Λ` for every injective trace**, on a connected smooth proper variety
with an injective good trace `t`: an injective trace `t'` on `H^{2d}(X, Λ)`, a group with `ℓ`
elements, is `t` followed by the automorphism `t' ∘ t⁻¹` of `Λ`. -/
theorem isDualityPerfect_unitSheaf_of_injective_of_exists_isGoodTrace
    (hpurity : LocalPurity ℓ k) (hcore : PoincareDualityCore ℓ k) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (d : ℕ) [SmoothOfRelativeDimension d f]
    [ConnectedSpace X]
    (hgood : ∃ t : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) (2 * d) →+ ZMod ℓ,
      Function.Injective t ∧ IsGoodTrace ℓ k d f (CompactificationOf.ofProper f)
        (Ext.transportTrace t (Iso.refl _) (unitSheafIsoExtensionByZeroId ℓ X)))
    (t' : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) (2 * d) →+ ZMod ℓ)
    (ht' : Function.Injective t') :
    Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) (unitSheaf ℓ) (2 * d) t' (unitSheaf ℓ) := by
  obtain ⟨t, htinj, ht⟩ := hgood
  have hPD := isDualityPerfect_unitSheaf_of_isGoodTrace_ofProper ℓ hpurity hcore f d t ht
  obtain ⟨-, hcard⟩ := natCard_ext_unitSheaf_of_isDualityPerfect ℓ d t hPD
  have hcard' : Nat.card (ZMod ℓ) ≤
      Nat.card (Ext (unitSheaf (X := X) ℓ) (unitSheaf (X := X) ℓ) (2 * d)) := by
    rw [hcard, Nat.card_zmod]
  let et := AddEquiv.ofBijective t (htinj.bijective_of_nat_card_le hcard')
  let et' := AddEquiv.ofBijective t' (ht'.bijective_of_nat_card_le hcard')
  have heq : (et.symm.trans et').toAddMonoidHom.comp t = t' := by
    ext z
    exact congrArg et' (et.symm_apply_apply z)
  rw [← heq]
  exact (Ext.isDualityPerfect_comp_addEquiv_iff t _ _).2 hPD

/-- **Poincaré duality with lisse `ℤ/ℓ` coefficients on a connected smooth proper variety.** Let
`k` be algebraically closed, `ℓ` a prime invertible in `k`, and `X` connected, smooth of relative
dimension `d` and proper over `k`. Given duality on a dense open for good traces
(`Stacks.EtaleCohomology.PoincareDualityCore`, for `ℓ` invertible and under local purity, which
holds by `Stacks.EtaleCohomology.Purity.localPurity`), and an
injective good trace on `H^{2d}(T, ℤ/ℓ)` for every connected finite étale `T → X`, the Yoneda
pairing `Ext^q_X(Λ, F) × Ext^{2d-q}_X(F, Λ) → H^{2d}(X, Λ) → Λ` is perfect for every injective
trace and every locally constant sheaf `F` of finite type. -/
theorem isDualityPerfect_of_isFiniteTypeLocallyConstant_of_exists_isGoodTrace
    (hℓ : IsUnit (ℓ : k))
    (hcore : IsUnit (ℓ : k) → LocalPurity ℓ k → PoincareDualityCore ℓ k)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (d : ℕ)
    [SmoothOfRelativeDimension d f] [ConnectedSpace X]
    (hgood : ∀ (T : Scheme.{u}) (π : T ⟶ X) [IsFinite π] [Etale π] [ConnectedSpace T],
      ∃ t' : Ext (unitSheaf (X := T) ℓ) (unitSheaf ℓ) (2 * d) →+ ZMod ℓ,
        Function.Injective t' ∧ IsGoodTrace ℓ k d (π ≫ f) (CompactificationOf.ofProper (π ≫ f))
          (Ext.transportTrace t' (Iso.refl _) (unitSheafIsoExtensionByZeroId ℓ T)))
    (t : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) (2 * d) →+ ZMod ℓ) (ht : Function.Injective t)
    (F : EtaleModules.{u, 0} (ZMod ℓ) X)
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) X.smallEtaleTopology F) :
    Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) (unitSheaf ℓ) (2 * d) t F := by
  have hpurity : LocalPurity ℓ k := Purity.localPurity (k := k) (ℓ := ℓ) hℓ
  have hcore' := hcore hℓ hpurity
  have : Nonempty X := ConnectedSpace.toNonempty
  have hcardT : ∀ (T : Scheme.{u}) (π : T ⟶ X) [IsFinite π] [Etale π] [ConnectedSpace T],
      Finite (Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) (2 * d)) ∧
        Nat.card (Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) (2 * d)) = ℓ := by
    intro T π _ _ _
    have : SmoothOfRelativeDimension d (π ≫ f) := by
      rw [← zero_add d]
      infer_instance
    exact natCard_ext_unitSheaf_of_exists_isGoodTrace ℓ hpurity hcore' (π ≫ f) d (hgood T π)
  refine isDualityPerfect_of_isFiniteTypeLocallyConstant_of_proper f d
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field d f).le t ht
    (fun T π _ _ _ => ⟨(hcardT T π).1, (hcardT T π).2.trans (hcardT X (𝟙 X)).2.symm⟩)
    (fun T π _ _ _ t' ht' => ?_) F hF
  have : SmoothOfRelativeDimension d (π ≫ f) := by
    rw [← zero_add d]
    infer_instance
  exact isDualityPerfect_unitSheaf_of_injective_of_exists_isGoodTrace ℓ hpurity hcore' (π ≫ f) d
    (hgood T π) t' ht'

/-- **Poincaré duality with lisse `ℤ/ℓ` coefficients on a connected smooth proper variety**, from
the core and the computation of the top cohomology. Let `k` be algebraically closed, `ℓ` a prime
invertible in `k`, and `X` connected, smooth of relative dimension `d` and proper over `k`. Given
duality on a dense open for good traces (`Stacks.EtaleCohomology.PoincareDualityCore`) and the
computation `H^{2e}_c(W, ℤ/ℓ) ≅ ℤ/ℓ` on the class of a point
(`Stacks.EtaleCohomology.TopCohomologyPointClass`), the Yoneda pairing
`Ext^q_X(Λ, F) × Ext^{2d-q}_X(F, Λ) → H^{2d}(X, Λ) → Λ` is perfect for every injective trace
and every locally constant sheaf `F` of finite type. The good traces on the connected finite
étale covers `T → X`, which are smooth proper and irreducible over `k`, come from
`Stacks.EtaleCohomology.exists_injective_isGoodTrace`. -/
theorem isDualityPerfect_of_isFiniteTypeLocallyConstant_of_topCohomologyPointClass
    (hℓ : IsUnit (ℓ : k))
    (hcore : IsUnit (ℓ : k) → LocalPurity ℓ k → PoincareDualityCore ℓ k)
    (hD1 : TopCohomologyPointClass ℓ k)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (d : ℕ)
    [SmoothOfRelativeDimension d f] [ConnectedSpace X]
    (t : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) (2 * d) →+ ZMod ℓ) (ht : Function.Injective t)
    (F : EtaleModules.{u, 0} (ZMod ℓ) X)
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) X.smallEtaleTopology F) :
    Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) (unitSheaf ℓ) (2 * d) t F := by
  refine isDualityPerfect_of_isFiniteTypeLocallyConstant_of_exists_isGoodTrace ℓ hℓ hcore f d
    (fun T π _ _ _ => ?_) t ht F hF
  have : SmoothOfRelativeDimension d (π ≫ f) := by
    rw [← zero_add d]
    infer_instance
  have : Smooth (π ≫ f) := SmoothOfRelativeDimension.smooth d (π ≫ f)
  have : CompactSpace T := ⟨by
    simpa using QuasiCompact.isCompact_preimage (f := π ≫ f) Set.univ isOpen_univ isCompact_univ⟩
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (π ≫ f)
  have : IsNoetherian T := ⟨⟩
  have : IrreducibleSpace T := irreducibleSpace_of_smooth_of_connectedSpace (π ≫ f)
  exact exists_injective_isGoodTrace hℓ hD1 (π ≫ f) d

end Stacks.EtaleCohomology

end
