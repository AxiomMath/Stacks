module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.NormalFunctionField.FundamentalGroupIso
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.NormalFunctionField.MaximalEtaleExtension

/-!
# The generic-point homomorphism of a normal integral scheme is a quotient map

Let `X` be an integral normal scheme, let `sbar` be an algebraic geometric point of `X` lying over
the generic point, and let `M` be the maximal subextension of `Ω = κ(sbar)` in which `X` is
unramified (`AlgebraicGeometry.maximalEtaleExtension`). This file proves that `M` has the
defining property and that the canonical homomorphism `Gal(Ω/K) → π₁(X, sbar)` is the quotient map
`Gal(Ω/K) → Gal(M/K)`.

## Main results

* `AlgebraicGeometry.finiteEtaleNormalization_of_le_maximalEtaleExtension` — every finite
  subextension of `M` has finite étale normalization: the defining property of `M`.
* `AlgebraicGeometry.isQuotientMap_absoluteGaloisToFundamentalGroup` — Stacks Tag 0BQM: the
  four statements above bundled into the one assertion that the canonical generic-point
  homomorphism is the quotient map `Gal(Ω/K) → Gal(M/K)` onto the Galois group of the maximal
  subextension in which `X` is unramified.

## References

* [Stacks Project, Tag 03VG](https://stacks.math.columbia.edu/tag/03VG)
* [Stacks Project, Tag 0BQM](https://stacks.math.columbia.edu/tag/0BQM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (sbar : GeometricPoint X)

attribute [local instance]
  instAlgebraCarrierResidueFieldCoeContinuousMapCarrierCarrierCommRingCatSpecOfResidueFieldHomTopCatBaseHomDefault

private theorem finiteEtaleNormalization_isSeparable
    [IsIntegral X] [IsNormal X]
    (hgeneric : sbar.hom default = genericPoint X)
    (E : IntermediateField (X.residueField (sbar.hom default)) sbar.residueField)
    (hE : FiniteEtaleNormalization X sbar E) :
    Algebra.IsSeparable (X.residueField (sbar.hom default)) E := by
  let K := X.residueField (sbar.hom default)
  let j := X.fromSpecResidueField (sbar.hom default)
  let g := Spec.map (CommRingCat.ofHom (algebraMap K E))
  let f := g ≫ j
  let : FiniteDimensional K E := hE.1
  let : Mono f.toNormalization :=
    finiteExtension_toNormalization_mono_at_generic X (sbar.hom default) hgeneric E
  let : Etale f.fromNormalization := hE.2.2
  have : FormallyUnramified f.toNormalization := inferInstance
  have : FormallyUnramified f := by
    have hc : FormallyUnramified (f.toNormalization ≫ f.fromNormalization) :=
      MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance inferInstance
    exact f.toNormalization_fromNormalization ▸ hc
  have : FormallyUnramified g := FormallyUnramified.of_comp g j
  have : Algebra.FormallyUnramified K E :=
    (RingHom.formallyUnramified_algebraMap).mp
      ((HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mp
        (inferInstance : FormallyUnramified g))
  exact Algebra.FormallyUnramified.isSeparable K E

private theorem finiteEtaleFiber_factors_through_mono
    [IsIntegral X] [IsNormal X]
    (hgeneric : sbar.hom default = genericPoint X)
    (Y : FiniteEtaleOver X) (p : finiteEtaleFiber sbar Y) :
    ∃ E : IntermediateField (X.residueField (sbar.hom default)) sbar.residueField,
      FiniteEtaleNormalization X sbar E ∧
      ∃ j : Spec (.of E) ⟶ Y.left, Mono j ∧
        Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫ j = p.1 := by
  obtain ⟨W, hW, i, q, himono, hq⟩ := exists_integral_finiteEtale_factor X Y p.1
  let : IsIntegral W.left := hW
  let : IsFinite W.hom := W.prop.1
  let : Etale W.hom := W.prop.2
  let : Mono i.left := himono
  have hi : i.left ≫ Y.hom = W.hom := by simpa using i.w
  have hp : q ≫ W.hom =
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.residueField (sbar.hom default)) sbar.residueField)) ≫
        X.fromSpecResidueField (sbar.hom default) := by
    rw [← hi, ← Category.assoc, hq, p.2]
    exact (geometricPoint_factorization X sbar).symm
  obtain ⟨E, hfin, hfe, j, hjmono, hj⟩ :=
    exists_finiteEtale_intermediate_factor_at X (sbar.hom default)
      hgeneric sbar.residueField (Y := W.left) W.hom q hp
  let : Mono j := hjmono
  exact ⟨E, ⟨hfin, hfe⟩, j ≫ i.left, inferInstance,
    (Category.assoc _ _ _).symm.trans ((congrArg (fun f => f ≫ i.left) hj).trans hq)⟩

private theorem maximalEtaleExtension_isSeparable
    [IsIntegral X] [IsNormal X]
    (hgeneric : sbar.hom default = genericPoint X) :
    Algebra.IsSeparable (X.residueField (sbar.hom default))
      (maximalEtaleExtension X sbar) := by
  apply (le_separableClosure_iff _ _ _).mp
  apply sSup_le
  intro E hE
  exact (le_separableClosure_iff _ _ _).mpr
    (finiteEtaleNormalization_isSeparable X sbar hgeneric E hE)

section

open scoped FintypeCatDiscrete

private theorem finiteEtale_exists_equivariant_fiber
    (X : Scheme.{u}) [ConnectedSpace X] (sbar : GeometricPoint X)
    (A : ContAction FintypeCat.{u} (AlgebraicGeometry.EtaleFundamentalGroup X sbar)) :
    ∃ (Y : FiniteEtaleOver X)
      (e : A.obj.V ≃ finiteEtaleFiber sbar Y),
      ∀ (σ : AlgebraicGeometry.EtaleFundamentalGroup X sbar) (a : A.obj.V),
        e ((A.obj.ρ σ).asHom.hom a) = (σ.asIso.app Y).hom (e a) := by
  obtain ⟨E, α, hα⟩ :=
    exists_finiteEtaleEquivalence_of_isGaloisCategory X sbar
  let Y := E.inverse.obj A
  let i := E.counitIso.app A
  let U := forget₂ (ContAction FintypeCat.{u} (AlgebraicGeometry.EtaleFundamentalGroup X sbar))
    FintypeCat.{u} ⋙ FintypeCat.incl
  let e := ((U.mapIso i).symm ≪≫ α.app Y).toEquiv
  refine ⟨Y, e, fun σ a => ?_⟩
  show (α.hom.app Y) (i.inv.hom.hom ((A.obj.ρ σ).asHom.hom a)) =
    (σ.asIso.app Y).hom ((α.hom.app Y) (i.inv.hom.hom a))
  rw [← hα]
  congr 1
  exact ConcreteCategory.congr_hom (i.inv.hom.comm σ) a

private theorem exists_embedding_action
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [FiniteDimensional K L]
    (h : G →ₜ* Gal(M/K)) :
    ∃ A : ContAction FintypeCat.{u} G,
      ∃ e : A.obj.V ≃ (L →ₐ[K] M),
        ∀ σ a, e ((A.obj.ρ σ).asHom.hom a) = (h σ).toAlgHom.comp (e a) := by
  let V := FintypeCat.of (L →ₐ[K] M)
  let A : Action FintypeCat G :=
    { V := V
      ρ :=
        { toFun := fun σ => End.of <| FintypeCat.homMk (fun a => (h σ).toAlgHom.comp a)
          map_one' := by
            apply End.ext
            apply ConcreteCategory.hom_ext
            intro a
            apply AlgHom.ext
            intro x
            show (h 1) (a x) = a x
            simp
          map_mul' := by
            intro σ τ
            apply End.ext
            apply ConcreteCategory.hom_ext
            intro a
            apply AlgHom.ext
            intro x
            show (h (σ * τ)) (a x) = (h σ) ((h τ) (a x))
            rw [map_mul]
            rfl } }
  have hc : A.IsContinuous := by
    let : DiscreteTopology ((forget₂ (Action FintypeCat G) TopCat).obj A) := ⟨rfl⟩
    apply continuousSMul_iff_stabilizer_isOpen.mpr
    intro a
    let E := a.fieldRange
    let : FiniteDimensional K E := Module.Finite.equiv a.equivFieldRange.toLinearEquiv
    have heq : (MulAction.stabilizer G a : Set G) = h ⁻¹' E.fixingSubgroup := by
      ext σ
      show (h σ).toAlgHom.comp a = a ↔ h σ ∈ E.fixingSubgroup
      rw [IntermediateField.mem_fixingSubgroup_iff]
      constructor
      · intro he x hx
        obtain ⟨y, rfl⟩ := hx
        exact DFunLike.congr_fun he y
      · intro he
        ext x
        exact he _ ⟨x, rfl⟩
    rw [heq]
    exact (IntermediateField.fixingSubgroup_isOpen E).preimage h.continuous
  exact ⟨⟨A, hc⟩, Equiv.refl _, fun _ _ => rfl⟩

private theorem restriction_fixes_inclusion_iff
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    (M L : IntermediateField K Ω) [Normal K M] (hL : L ≤ M)
    (σ : Gal(Ω/K)) :
    (AlgEquiv.restrictNormalHom M σ).toAlgHom.comp (IntermediateField.inclusion hL) =
        IntermediateField.inclusion hL ↔ σ ∈ L.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hh x hx
    have h := congrArg Subtype.val (DFunLike.congr_fun hh ⟨x, hx⟩)
    exact (AlgEquiv.restrictNormal_commutes σ M
      (IntermediateField.inclusion hL ⟨x, hx⟩)).symm.trans h
  · intro hh
    ext x
    exact (AlgEquiv.restrictNormal_commutes σ M
      (IntermediateField.inclusion hL x)).trans (hh x x.property)

private theorem intermediateField_eq_of_fixingSubgroup_eq_in_normal
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [Normal K Ω]
    (M : IntermediateField K Ω) [IsGalois K M]
    (E L : IntermediateField K Ω) (hE : E ≤ M) (hL : L ≤ M)
    (h : E.fixingSubgroup = L.fixingSubgroup) : E = L := by
  let E' := IntermediateField.restrict hE
  let L' := IntermediateField.restrict hL
  have hfix (D : IntermediateField K Ω) (hD : D ≤ M) (σ : Gal(Ω/K)) :
      AlgEquiv.restrictNormalHom M σ ∈ (IntermediateField.restrict hD).fixingSubgroup ↔
        σ ∈ D.fixingSubgroup := by
    rw [← restriction_fixes_inclusion_iff M D hD σ, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro hh
      refine AlgHom.ext fun y => ?_
      exact hh (IntermediateField.inclusion hD y)
        ((IntermediateField.mem_restrict hD _).mpr y.2)
    · intro hh x hx
      exact DFunLike.congr_fun hh ⟨x, (IntermediateField.mem_restrict hD x).mp hx⟩
  have heq : E'.fixingSubgroup = L'.fixingSubgroup := by
    ext τ
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (E := Ω) τ
    exact (hfix E hE σ).trans ((SetLike.ext_iff.mp h σ).trans (hfix L hL σ).symm)
  have hf : E' = L' := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E',
      ← InfiniteGalois.fixedField_fixingSubgroup L', heq]
  have := congrArg IntermediateField.lift hf
  simpa only [E', L', IntermediateField.lift_restrict] using this

end

/-- Every finite subextension of the maximal extension gives a finite étale normalization. -/
@[stacks 03VG "finite étale normalization"]
public theorem finiteEtaleNormalization_of_le_maximalEtaleExtension
    [IsIntegral X] [IsNormal X]
    (hs : GeometricPoint.IsAlgebraic sbar)
    (hgeneric : sbar.hom default = genericPoint X)
    (L : IntermediateField (X.residueField (sbar.hom default)) sbar.residueField)
    [FiniteDimensional (X.residueField (sbar.hom default)) L]
    (hL : L ≤ maximalEtaleExtension X sbar) :
    FiniteEtaleNormalization X sbar L := by
  let K := X.residueField (sbar.hom default)
  let Ω := sbar.residueField
  let M := maximalEtaleExtension X sbar
  let : IsAlgClosure K Ω := hs
  let : Normal K M := normal_maximalEtaleExtension X sbar hs hgeneric
  let : Algebra.IsSeparable K M := maximalEtaleExtension_isSeparable X sbar hgeneric
  let : IsGalois K M := {}
  let iso := fundamentalGroupIsoGalMaximalEtaleExtension X sbar hs hgeneric
  let h : AlgebraicGeometry.EtaleFundamentalGroup X sbar →ₜ* Gal(M/K) :=
    ⟨iso.toMonoidHom, iso.continuous⟩
  obtain ⟨A, eA, heA⟩ := exists_embedding_action K L M h
  obtain ⟨Y, eY, heY⟩ := finiteEtale_exists_equivariant_fiber X sbar A
  let incl : L →ₐ[K] M := IntermediateField.inclusion hL
  let a : A.obj.V := eA.symm incl
  let p : finiteEtaleFiber sbar Y := eY a
  obtain ⟨E, hE, j, hjmono, hj⟩ :=
    finiteEtaleFiber_factors_through_mono X sbar hgeneric Y p
  let : Mono j := hjmono
  have hfix : E.fixingSubgroup = L.fixingSubgroup := by
    ext σ
    let τ := absoluteGaloisToFundamentalGroup X sbar σ
    have hτ : h τ = AlgEquiv.restrictNormalHom M σ :=
      fundamentalGroupIsoGalMaximalEtaleExtension_apply X sbar hs hgeneric σ
    calc
      σ ∈ E.fixingSubgroup ↔ ((τ.asIso.app Y).hom p = p) :=
        (fiber_stabilizer_of_mono_factor X sbar Y p E j hj σ).symm
      _ ↔ eY ((A.obj.ρ τ).asHom.hom a) = eY a := by rw [heY]
      _ ↔ (A.obj.ρ τ).asHom.hom a = a := eY.injective.eq_iff
      _ ↔ eA ((A.obj.ρ τ).asHom.hom a) = eA a := eA.injective.eq_iff.symm
      _ ↔ (h τ).toAlgHom.comp incl = incl := by
        rw [heA]
        simp only [a, eA.apply_symm_apply]
      _ ↔ σ ∈ L.fixingSubgroup := by
        rw [hτ]
        exact restriction_fixes_inclusion_iff M L hL σ
  exact intermediateField_eq_of_fixingSubgroup_eq_in_normal M E L (le_sSup hE) hL hfix ▸ hE

/-- **Stacks Project, Tag 0BQM.** Let `X` be a normal integral scheme with function field
`K = κ(η)` and let `η̄` be an algebraic geometric point over the generic point, with
algebraically closed residue field `Ω = κ(η̄)`. Let `M ⊆ Ω` be the union of the finite
subextensions of `K` in which `X` is unramified, that is `AlgebraicGeometry.maximalEtaleExtension`.
Then `M` has that defining property and is the largest subextension with it, `M/K` is Galois —
in particular `M` is separable over `K`, so it lies in a separable closure `K^sep` of `K` inside
`Ω` — and the canonical homomorphism `Gal(Ω/K) → π₁(X, η̄)` is identified with the quotient map
`Gal(Ω/K) → Gal(M/K)`: there is an isomorphism of topological groups
`π₁(X, η̄) ≃ Gal(M/K)` carrying the canonical homomorphism to restriction of automorphisms
to `M`.

No Noetherian hypothesis is needed; this is the difference between the present tag and Stacks
Tag 03VG, which the library proves in the same generality above. -/
@[stacks 0BQM "π₁(X, η̄) = Gal(M/K), with the canonical generic-point homomorphism identified \
with the quotient map onto Gal(M/K)", sga "1 V 8.2" "special case", sga "7 XIX 1.4" "π1(ℓ−S"]
public theorem isQuotientMap_absoluteGaloisToFundamentalGroup
    [IsIntegral X] [IsNormal X]
    (hs : GeometricPoint.IsAlgebraic sbar)
    (hgeneric : sbar.hom default = genericPoint X) :
    letI : Normal (X.residueField (sbar.hom default)) (maximalEtaleExtension X sbar) :=
      normal_maximalEtaleExtension X sbar hs hgeneric
    (∀ L : IntermediateField (X.residueField (sbar.hom default)) sbar.residueField,
        FiniteDimensional (X.residueField (sbar.hom default)) L →
          L ≤ maximalEtaleExtension X sbar → FiniteEtaleNormalization X sbar L) ∧
      (∀ N : IntermediateField (X.residueField (sbar.hom default)) sbar.residueField,
        (∀ L : IntermediateField (X.residueField (sbar.hom default)) sbar.residueField,
            L ≤ N → FiniteDimensional (X.residueField (sbar.hom default)) L →
              FiniteEtaleNormalization X sbar L) →
          N ≤ maximalEtaleExtension X sbar) ∧
      Normal (X.residueField (sbar.hom default)) (maximalEtaleExtension X sbar) ∧
      Algebra.IsSeparable (X.residueField (sbar.hom default)) (maximalEtaleExtension X sbar) ∧
      ∃ e : AlgebraicGeometry.EtaleFundamentalGroup X sbar ≃ₜ*
          Gal(maximalEtaleExtension X sbar / X.residueField (sbar.hom default)),
        ∀ σ : Gal(sbar.residueField / X.residueField (sbar.hom default)),
          e (absoluteGaloisToFundamentalGroup X sbar σ) =
            AlgEquiv.restrictNormalHom (maximalEtaleExtension X sbar) σ := by
  let : Normal (X.residueField (sbar.hom default)) (maximalEtaleExtension X sbar) :=
    normal_maximalEtaleExtension X sbar hs hgeneric
  refine ⟨fun L hfin hL => ?_, fun N hN => le_maximalEtaleExtension X sbar hs hgeneric N hN,
    normal_maximalEtaleExtension X sbar hs hgeneric,
    maximalEtaleExtension_isSeparable X sbar hgeneric,
    fundamentalGroupIsoGalMaximalEtaleExtension X sbar hs hgeneric,
    fundamentalGroupIsoGalMaximalEtaleExtension_apply X sbar hs hgeneric⟩
  let := hfin
  exact finiteEtaleNormalization_of_le_maximalEtaleExtension X sbar hs hgeneric L hL

/-- **The kernel of the generic-point homomorphism fixes every subextension in which `X` is
unramified.** Let `X` be a normal integral scheme with function field `K`, let `K^sep` be a
separable closure of `K` inside an algebraically closed algebraic extension `Ω` of `K`, and let
`E` be a finite subextension of `K^sep / K` whose normalization over `X` is finite étale. Then
every element of the kernel of `Gal(K^sep/K) → π₁(X)` fixes `E` pointwise.

The normalization of `X` in `E` is a connected finite étale cover of `X`, and the inclusion
`E ⊆ Ω` is a point of its geometric fibre at the generic point. An element of the kernel fixes
that point, which says exactly that a lift of it to `Gal(Ω/K)` fixes the image of `E` in `Ω`,
because the morphism `Spec E ⟶` normalization is a monomorphism. -/
public theorem mem_fixingSubgroup_of_galoisToFundamentalGroup_eq_one
    [IsIntegral X] [IsNormal X] (L Ω : Type u) [Field L] [Field Ω]
    [Algebra (X.residueField (genericPoint X)) L]
    [IsSepClosure (X.residueField (genericPoint X)) L]
    [Algebra L Ω] [Algebra (X.residueField (genericPoint X)) Ω]
    [IsScalarTower (X.residueField (genericPoint X)) L Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic (X.residueField (genericPoint X)) Ω]
    (E : IntermediateField (X.residueField (genericPoint X)) L)
    [FiniteDimensional (X.residueField (genericPoint X)) E]
    (hE : IsFinite (Scheme.Hom.fromNormalization
          (Spec.map (CommRingCat.ofHom
              (algebraMap (X.residueField (genericPoint X)) (E : Type u))) ≫
            X.fromSpecResidueField (genericPoint X))) ∧
        Etale (Scheme.Hom.fromNormalization
          (Spec.map (CommRingCat.ofHom
              (algebraMap (X.residueField (genericPoint X)) (E : Type u))) ≫
            X.fromSpecResidueField (genericPoint X))))
    (σ : Gal(L/X.residueField (genericPoint X)))
    (hσ : galoisToFundamentalGroup X L Ω σ = 1) :
    σ ∈ E.fixingSubgroup := by
  let : IsAlgClosure (X.residueField (genericPoint X)) Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := X.residueField (genericPoint X)) (K₁ := L) Ω σ
  set f : Spec (.of (E : Type u)) ⟶ X :=
    Spec.map (CommRingCat.ofHom
        (algebraMap (X.residueField (genericPoint X)) (E : Type u))) ≫
      X.fromSpecResidueField (genericPoint X) with hf
  have : Mono f.toNormalization :=
    finiteExtension_toNormalization_mono_at_generic X (genericPoint X) rfl E
  let Y : FiniteEtaleOver X := MorphismProperty.Over.mk ⊤ f.fromNormalization hE
  let eEΩ : (E : Type u) →+* Ω :=
    (algebraMap L Ω).comp (algebraMap (E : Type u) L)
  have heEΩ : CommRingCat.ofHom
        (algebraMap (X.residueField (genericPoint X)) (E : Type u)) ≫
      CommRingCat.ofHom eEΩ =
      CommRingCat.ofHom (algebraMap (X.residueField (genericPoint X)) Ω) := by
    apply CommRingCat.hom_ext
    ext a
    exact (IsScalarTower.algebraMap_apply (X.residueField (genericPoint X)) L Ω a).symm
  let p : finiteEtaleFiber
      ((algebraicClosureGeometricPoint (X.residueField (genericPoint X)) Ω).map
        (X.fromSpecResidueField (genericPoint X))) Y :=
    ⟨Spec.map (CommRingCat.ofHom eEΩ) ≫ f.toNormalization, by
      show (Spec.map (CommRingCat.ofHom eEΩ) ≫ f.toNormalization) ≫
        f.fromNormalization = _
      rw [Category.assoc, f.toNormalization_fromNormalization, hf, ← Spec.map_comp_assoc,
        heEΩ]
      rfl⟩
  have hact := galoisToFundamentalGroup_restrict_apply X L Ω τ Y p
  rw [hτ, hσ] at hact
  have hcancel : Spec.map (CommRingCat.ofHom τ.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom eEΩ) = Spec.map (CommRingCat.ofHom eEΩ) := by
    refine (cancel_mono f.toNormalization).mp ?_
    rw [Category.assoc]
    exact hact.symm
  have hring : CommRingCat.ofHom eEΩ ≫ CommRingCat.ofHom τ.toAlgHom.toRingHom =
      CommRingCat.ofHom eEΩ := by
    apply Spec.map_injective
    simpa only [Spec.map_comp] using hcancel
  refine (IntermediateField.mem_fixingSubgroup_iff E σ).2 fun x hx => ?_
  have hx' := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hring) (⟨x, hx⟩ : (E : Type u))
  have hcomm : (algebraMap L Ω) (σ x) = τ ((algebraMap L Ω) x) := by
    rw [← hτ]
    exact AlgEquiv.restrictNormal_commutes τ L x
  exact (algebraMap L Ω).injective (hcomm.trans hx')

end AlgebraicGeometry
