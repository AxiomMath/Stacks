module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocalTermsStalkReduction
public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs

/-!
# The local terms at the boundary when the compactification is a smooth curve

Every consumer of the bound on the local terms at the boundary
(`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsKilledBy`) has a smooth compactification: finite
level Poincaré duality on a curve
(`Stacks.EtaleCohomology.LAdicSheaf.exists_levelPairing_of_curve`) assumes that `X̄_k̄` is a
smooth proper curve over `k̄`. This file states the input of
`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsBoundaryStalkInput` under that extra hypothesis,
`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsSmoothBoundaryStalkInput`, and reduces it to one
boundary point at a time.

At a point `x` of `X̄_k̄ ∖ V_k̄` the local ring is a discrete valuation ring (`X̄_k̄` is a smooth
curve), so the stalks of `j'_* Gₙ` and `R¹j'_* Gₙ` at a geometric point over `x` are `H⁰` and
`H¹` of the inertia group of a place of the function field of `V` at infinity
(`Stacks.EtaleCohomology.LAdicSheaf.SmoothBoundaryPointInput`, the per-point input). The boundary
`X̄_k̄ ∖ V_k̄` is finite, the complement of a nonempty open in an integral scheme of dimension one,
so finitely many inertia groups govern all the boundary stalks
(`LAdicSheaf.localTermsSmoothBoundaryStalkInput_of_smoothBoundaryPointInput`).

The consumer route is `Stacks.EtaleCohomology.LAdicSheaf.exists_localTermsKilledBy_of_smooth`: for
the sheaf `ℱ_τ` of a continuous `τ : π₁(V, η̄) → GL_r(ℚ_ℓ)` whose inertia groups at infinity fix no
nonzero vector, one power of `ℓ` kills the local terms at the boundary, under the hypotheses on
`X̄_k̄` that `Stacks.EtaleCohomology.LAdicSheaf.exists_levelPairing_of_curve` takes.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.LocalTermsSmoothBoundaryStalkInput`.
* `Stacks.EtaleCohomology.LAdicSheaf.SmoothBoundaryPointInput`.

## Main results

* `LAdicSheaf.localTermsSmoothBoundaryStalkInput_of_smoothBoundaryPointInput`.
* `Stacks.EtaleCohomology.LAdicSheaf.exists_localTermsKilledBy_of_smoothBoundary`.
* `Stacks.EtaleCohomology.LAdicSheaf.exists_localTermsKilledBy_of_smooth`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Matrix

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

/-- **The boundary stalks of `ℱ_{ρ₀}` for a smooth compactification**: the statement of
`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsBoundaryStalkInput` with the extra hypothesis that
`X̄_k̄` is a smooth curve over `k̄`. There are finitely many inertia groups `I₁, …, I_m` of places
at infinity such that, whenever `ℓ ^ e` kills `H⁰(I_i, Mₙ)` and `H¹(I_i, Mₙ)` for all `i` and `n`,
`ℓ ^ e` kills the stalks of `j'_* Gₙ` and of `R¹j'_* Gₙ` at every geometric point of `X̄_k̄`
outside `V_k̄`. This proposition is not registered and is not a hypothesis of any registered
statement. -/
public def LAdicSheaf.LocalTermsSmoothBoundaryStalkInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (V : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B V.1 V.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian V.1] [Fact ℓ.Prime] [ConnectedSpace V.1] [IrreducibleSpace V.1] [IsAffine V.1]
    (k : Type u) [Field k] [Finite k] (f : V.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [IsCurve kbar (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
    [Smooth (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
    (p : ℕ) [Fact p.Prime] [CharP k p] (_ : ℓ ≠ p)
    (L Ω : Type u) [Field L] [Field Ω]
    [Algebra (V.1.residueField (genericPoint V.1)) L]
    [IsSepClosure (V.1.residueField (genericPoint V.1)) L]
    [Algebra L Ω] [Algebra (V.1.residueField (genericPoint V.1)) Ω]
    [IsScalarTower (V.1.residueField (genericPoint V.1)) L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic (V.1.residueField (genericPoint V.1)) Ω]
    (r : ℕ) (ρ₀ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin r) ℤ_[ℓ]) (hρ₀ : Continuous ρ₀),
    ∃ (m : ℕ) (I : Fin m → Subgroup Gal(L / V.1.residueField (genericPoint V.1))),
      (∀ i, LAdicSheaf.IsBoundaryInertia V.1 ℓ L (I i)) ∧
      ∀ e : ℕ, (∀ i, InertiaLevelsKilledBy (I i)
          (ρ₀.comp (galoisToFundamentalGroup V.1 L Ω).toMonoidHom) e) →
        ∀ n : ℕ, BoundaryStalksKilledBy (fieldBaseChangeMap j.obj.hom kbar)
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk f) kbar)).obj
              (LAdicSheaf.etaleLevel B V ℓ (representationLAdicSheaf B V
                ((algebraicClosureGeometricPoint (V.1.residueField (genericPoint V.1)) Ω).map
                  (V.1.fromSpecResidueField (genericPoint V.1)))
                (canonicalFiniteLocallyConstantAbelianSheafEquivalence B V _) ρ₀ hρ₀) n))
          (ℓ ^ e)

/-- **One boundary point at a time.** In the setting of
`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsSmoothBoundaryStalkInput`, for every point `x` of
`X̄_k̄` outside `V_k̄` there is an inertia group `I` of a place at infinity such that, whenever
`ℓ ^ e` kills `H⁰(I, Mₙ)` and `H¹(I, Mₙ)` for all `n`, `ℓ ^ e` kills the stalks of `j'_* Gₙ` and
of `R¹j'_* Gₙ` at every geometric point of `X̄_k̄` over `x`.

Mathematically: the local ring of `X̄_k̄` at `x` is a discrete valuation ring, so by Stacks 03Q9
these stalks are `H⁰` and `H¹` of `Spec K^{sh}`, `K^{sh}` the fraction field of the strict
henselization, whose absolute Galois group is the inertia group of a place over the image of `x`
in `X̄` (Stacks 03QU). This proposition is not registered and is not a hypothesis of any
registered statement. -/
public def LAdicSheaf.SmoothBoundaryPointInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (V : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B V.1 V.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian V.1] [Fact ℓ.Prime] [ConnectedSpace V.1] [IrreducibleSpace V.1] [IsAffine V.1]
    (k : Type u) [Field k] [Finite k] (f : V.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [IsCurve kbar (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
    [Smooth (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
    (p : ℕ) [Fact p.Prime] [CharP k p] (_ : ℓ ≠ p)
    (L Ω : Type u) [Field L] [Field Ω]
    [Algebra (V.1.residueField (genericPoint V.1)) L]
    [IsSepClosure (V.1.residueField (genericPoint V.1)) L]
    [Algebra L Ω] [Algebra (V.1.residueField (genericPoint V.1)) Ω]
    [IsScalarTower (V.1.residueField (genericPoint V.1)) L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic (V.1.residueField (genericPoint V.1)) Ω]
    (r : ℕ) (ρ₀ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin r) ℤ_[ℓ]) (hρ₀ : Continuous ρ₀)
    (x : fieldBaseChange j.obj.right kbar)
    (_ : x ∉ Set.range (fieldBaseChangeMap j.obj.hom kbar).base),
    ∃ I : Subgroup Gal(L / V.1.residueField (genericPoint V.1)),
      LAdicSheaf.IsBoundaryInertia V.1 ℓ L I ∧
      ∀ e : ℕ, InertiaLevelsKilledBy I (ρ₀.comp (galoisToFundamentalGroup V.1 L Ω).toMonoidHom) e →
        ∀ (n : ℕ) (s : GeometricPoint (fieldBaseChange j.obj.right kbar)), s.hom.base default = x →
          (ℓ ^ e) • 𝟙 (((Scheme.pointSmallEtale s.hom).sheafFiber
            (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj
            ((etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
              (fieldBaseChangeMap j.obj.hom kbar)).obj
              ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
                (fieldBaseChangeProj (Over.mk f) kbar)).obj
                  (LAdicSheaf.etaleLevel B V ℓ (representationLAdicSheaf B V
                    ((algebraicClosureGeometricPoint (V.1.residueField (genericPoint V.1)) Ω).map
                      (V.1.fromSpecResidueField (genericPoint V.1)))
                    (canonicalFiniteLocallyConstantAbelianSheafEquivalence B V _) ρ₀ hρ₀) n)))) =
            0 ∧
          (ℓ ^ e) • 𝟙 (((Scheme.pointSmallEtale s.hom).sheafFiber
            (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj
            (((etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
              (fieldBaseChangeMap j.obj.hom kbar)).rightDerived 1).obj
              ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
                (fieldBaseChangeProj (Over.mk f) kbar)).obj
                  (LAdicSheaf.etaleLevel B V ℓ (representationLAdicSheaf B V
                    ((algebraicClosureGeometricPoint (V.1.residueField (genericPoint V.1)) Ω).map
                      (V.1.fromSpecResidueField (genericPoint V.1)))
                    (canonicalFiniteLocallyConstantAbelianSheafEquivalence B V _) ρ₀ hρ₀) n)))) =
            0

/-- The base change `V_k̄ ⟶ X̄_k̄` of a compactification `V ⟶ X̄` is an open immersion. -/
private theorem isOpenImmersion_fieldBaseChangeMap_of_compactification {V : Scheme.{u}}
    {k : Type u} [Field k] (f : V ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
    (kbar : Type u) [Field kbar] [Algebra k kbar] :
    IsOpenImmersion (fieldBaseChangeMap j.obj.hom kbar) :=
  have : IsOpenImmersion j.obj.hom.left := j.property.1
  have : MorphismProperty.IsStableUnderComposition @IsOpenImmersion.{u} :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstanceAs (IsOpenImmersion j.obj.hom.left))
    (inferInstanceAs (IsOpenImmersion (𝟙 _))) (Over.w j.obj.hom).symm (Category.id_comp _).symm

/-- **The boundary of a smooth compactification is finite.** If `X̄_k̄` is a proper curve over
`k̄`, the complement of `V_k̄` in `X̄_k̄` is a finite set: `V_k̄` is a nonempty open of an integral
scheme of dimension one. -/
theorem finite_compl_range_fieldBaseChangeMap {V : Scheme.{u}} [Nonempty V] {k : Type u} [Field k]
    (f : V ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
    [Algebra k kbar] [IsCurve kbar (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))] :
    (Set.range (fieldBaseChangeMap j.obj.hom kbar).base)ᶜ.Finite := by
  let fY := pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)
  have : IsProper fY :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback (Over.mk j.toBase).hom (specAlgebraMap k kbar))
      (inferInstanceAs (IsProper j.toBase))
  have : IsIntegral (fieldBaseChange j.obj.right kbar) :=
    IsCurve.toIsVariety.toIsIntegral (k := kbar) (f := fY)
  have hdim : topologicalKrullDim (fieldBaseChange j.obj.right kbar) = 1 :=
    IsCurve.topologicalKrullDim_eq_one (f := fY)
  have : IsLocallyNoetherian (fieldBaseChange j.obj.right kbar) :=
    LocallyOfFiniteType.isLocallyNoetherian fY
  have : CompactSpace (fieldBaseChange j.obj.right kbar) :=
    QuasiCompact.compactSpace_of_compactSpace fY
  have : IsNoetherian (fieldBaseChange j.obj.right kbar) := ⟨⟩
  have := isOpenImmersion_fieldBaseChangeMap_of_compactification f j kbar
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨y, -, -⟩ := Scheme.Pullback.exists_preimage_pullback v (default : Spec (.of kbar))
    (f := f) (g := specAlgebraMap k kbar) (Subsingleton.elim _ _)
  have hW : (fieldBaseChangeMap j.obj.hom kbar).opensRange ≠ ⊥ := fun h => by
    have hy : (fieldBaseChangeMap j.obj.hom kbar).base y ∈
        (fieldBaseChangeMap j.obj.hom kbar).opensRange := ⟨y, rfl⟩
    rw [h] at hy
    exact hy
  exact Stacks.AlgebraicGeometry.AmpleDimensionOne.finite_compl_of_ne_bot _ hdim _ hW

/-- **`LocalTermsSmoothBoundaryStalkInput` from one boundary point at a time.** The boundary
`X̄_k̄ ∖ V_k̄` is finite (`Stacks.EtaleCohomology.finite_compl_range_fieldBaseChangeMap`); choosing
for each of its points the inertia group of
`Stacks.EtaleCohomology.LAdicSheaf.SmoothBoundaryPointInput` gives finitely many inertia groups
governing all boundary stalks. -/
theorem LAdicSheaf.localTermsSmoothBoundaryStalkInput_of_smoothBoundaryPointInput
    (h : LAdicSheaf.SmoothBoundaryPointInput.{u}) :
    LAdicSheaf.LocalTermsSmoothBoundaryStalkInput.{u} := by
  intro B V ℓ _ _ _ _ _ _ _ _ k _ _ f _ _ _ _ j kbar _ _ _ _ _ p _ _ hℓp L Ω _ _ _ _ _ _ _ _ _
    r ρ₀ hρ₀
  have : Nonempty V.1 := ⟨genericPoint V.1⟩
  have hfin := finite_compl_range_fieldBaseChangeMap f j kbar
  let S := hfin.toFinset
  choose I hI hbd using fun x : S => h B V ℓ k f j kbar p hℓp L Ω r ρ₀ hρ₀ x.1
    ((Set.Finite.mem_toFinset hfin).1 x.2)
  refine ⟨S.card, fun i => I (S.equivFin.symm i), fun i => hI _, fun e he n s hs => ?_⟩
  let xs : S := ⟨s.hom.base default, (Set.Finite.mem_toFinset hfin).2 hs⟩
  have he' : InertiaLevelsKilledBy (I xs)
      (ρ₀.comp (galoisToFundamentalGroup V.1 L Ω).toMonoidHom) e := by
    have := he (S.equivFin xs)
    simp only [Equiv.symm_apply_apply] at this
    exact this
  exact hbd xs e he' n s rfl

section Consumer

variable (B : BigEtaleSite.{u}) (V : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B V.1 V.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian V.1] [Fact ℓ.Prime] [ConnectedSpace V.1] [IrreducibleSpace V.1] [IsAffine V.1]
  (k : Type u) [Field k] [Finite k] (f : V.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosure k kbar]
  [IsCurve kbar (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
  [Smooth (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
  (p : ℕ) [Fact p.Prime] [CharP k p] (hℓp : ℓ ≠ p)
  (L Ω : Type u) [Field L] [Field Ω]
  [Algebra (V.1.residueField (genericPoint V.1)) L]
  [IsSepClosure (V.1.residueField (genericPoint V.1)) L]
  [Algebra L Ω] [Algebra (V.1.residueField (genericPoint V.1)) Ω]
  [IsScalarTower (V.1.residueField (genericPoint V.1)) L Ω] [IsAlgClosed Ω]
  [Algebra.IsAlgebraic (V.1.residueField (genericPoint V.1)) Ω] (r : ℕ)

include hℓp in
/-- **The local terms of `ℱ_{ρ₀}` for a smooth compactification, from per-place bounds.** In the
setting of `Stacks.EtaleCohomology.LAdicSheaf.LocalTermsStalkInput`, with `X̄_k̄` a smooth curve
over `k̄`: if at every place `(A, P)` at infinity with finite residue field of characteristic
`≠ ℓ` some power `ℓ ^ e` kills `H⁰(I_P, Mₙ)` and `H¹(I_P, Mₙ)` for all levels `Mₙ` of `ρ₀`, then
one power of `ℓ` kills the local terms of `ℱ_{ρ₀}` at the boundary. The per-place bounds of the
finitely many inertia groups of
`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsSmoothBoundaryStalkInput` have a maximum `E`, and
`ℓ ^ E` kills the boundary stalks, hence the local terms
(`Stacks.EtaleCohomology.localTerms_nsmul_id_eq_zero_of_boundaryStalksKilledBy`). -/
theorem LAdicSheaf.exists_localTermsKilledBy_of_smoothBoundary
    (h : LAdicSheaf.LocalTermsSmoothBoundaryStalkInput.{u})
    (ρ₀ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin r) ℤ_[ℓ]) (hρ₀ : Continuous ρ₀)
    (hplace : ∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
      [Algebra A (V.1.residueField (genericPoint V.1))]
      [IsFractionRing A (V.1.residueField (genericPoint V.1))] [Algebra A L]
      [IsScalarTower A (V.1.residueField (genericPoint V.1)) L]
      (P : Ideal (integralClosure A L)) [P.IsMaximal] [Finite (IsLocalRing.ResidueField A)],
      ℓ ≠ ringChar (IsLocalRing.ResidueField A) →
      (∃ a : Γ(V.1, ⊤), (V.1.evaluation ⊤ (genericPoint V.1) trivial).hom a ∉
        Set.range (algebraMap A (V.1.residueField (genericPoint V.1)))) →
      letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
        (integralClosure A L)
      ∃ e : ℕ, InertiaLevelsKilledBy (P.inertia Gal(L / V.1.residueField (genericPoint V.1)))
        (ρ₀.comp (galoisToFundamentalGroup V.1 L Ω).toMonoidHom) e) :
    ∃ K : ℕ, LAdicSheaf.LocalTermsKilledBy B V ℓ f j kbar
      (representationLAdicSheaf B V ((algebraicClosureGeometricPoint
        (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B V _) ρ₀ hρ₀) K := by
  obtain ⟨m, I, hI, hbd⟩ := h B V ℓ k f j kbar p hℓp L Ω r ρ₀ hρ₀
  have hex : ∀ i, ∃ e : ℕ, InertiaLevelsKilledBy (I i)
      (ρ₀.comp (galoisToFundamentalGroup V.1 L Ω).toMonoidHom) e := by
    intro i
    obtain ⟨A, _, _, _, _, _, _, _, P, _, _, hℓA, hA, hIP⟩ := hI i
    obtain ⟨e, he⟩ := hplace A P hℓA hA
    exact ⟨e, hIP ▸ he⟩
  choose e he using hex
  refine ⟨Finset.univ.sup e, fun n => ?_⟩
  have hb := hbd (Finset.univ.sup e)
    (fun i => (he i).mono (Finset.le_sup (Finset.mem_univ i))) n
  have := Fintype.ofFinite k
  have := isOpenImmersion_fieldBaseChangeMap_of_compactification f j kbar
  have : TopologicalSpace.NoetherianSpace (Over.mk f).left :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace V.1)
  have : QuasiCompact j.obj.hom.left := quasiCompact_of_noetherianSpace_source _
  have : QuasiCompact (fieldBaseChangeMap j.obj.hom kbar) :=
    MorphismProperty.of_isPullback (isPullback_fieldBaseChangeMap j.obj.hom kbar).flip ‹_›
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have hℓk : IsUnit ((ℓ ^ (n + 1) : ℕ) : kbar) := by
    refine isUnit_iff_ne_zero.2 ?_
    rw [Nat.cast_pow]
    refine pow_ne_zero _ fun h0 => hℓp ?_
    have hdvd := (CharP.cast_eq_zero_iff kbar p ℓ).1 h0
    exact ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).1 hdvd).symm
  have hN : IsUnit (((ℓ ^ (n + 1) : ℕ) : ℤ) : Γ(fieldBaseChange j.obj.right kbar, ⊤)) := by
    have := Purity.isUnit_natCast_globalSections_of_over
      (pullback.snd j.obj.right.hom (specAlgebraMap k kbar)) hℓk
    exact_mod_cast this
  exact localTerms_nsmul_id_eq_zero_of_boundaryStalksKilledBy
    (fieldBaseChangeMap j.obj.hom kbar) (pow_pos (Fact.out : ℓ.Prime).pos _) hN _ _ hb

include hℓp in
/-- **The local terms at infinity of `ℱ_τ` are bounded for a smooth compactification** (the
consumer route of Poincaré duality on an affine curve,
`Stacks.EtaleCohomology.LAdicSheaf.exists_levelPairing_of_curve`, which assumes the same of
`X̄_k̄`). For a smooth affine curve `V` over a finite field `k` of characteristic `p ≠ ℓ`, a
compactification `j : V ⟶ X̄` with `X̄_k̄` a smooth curve over `k̄`, and a continuous
`τ : π₁(V, η̄) → GL_r(ℚ_ℓ)`: if at every place `(A, P)` at infinity the inertia group fixes no
nonzero vector of `ℚ_ℓ ^ r`, then one power `ℓ ^ K` kills the local terms of `ℱ_τ` at the
boundary. The integral model `ρ₀` of `τ` is conjugate to `τ`, so its inertia groups fix no
nonzero vector of `ℤ_ℓ ^ r`, and `Stacks.EtaleCohomology.exists_inertiaLevelsKilledBy_inertia`
gives the per-place bounds of
`Stacks.EtaleCohomology.LAdicSheaf.exists_localTermsKilledBy_of_smoothBoundary`. -/
theorem LAdicSheaf.exists_localTermsKilledBy_of_smooth
    (h : LAdicSheaf.LocalTermsSmoothBoundaryStalkInput.{u})
    (τ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin r) ℚ_[ℓ]) (hτ : Continuous τ)
    (hinvτ : ∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
      [Algebra A (V.1.residueField (genericPoint V.1))]
      [IsFractionRing A (V.1.residueField (genericPoint V.1))] [Algebra A L]
      [IsScalarTower A (V.1.residueField (genericPoint V.1)) L]
      (P : Ideal (integralClosure A L)) [P.IsMaximal],
      (∃ a : Γ(V.1, ⊤), (V.1.evaluation ⊤ (genericPoint V.1) trivial).hom a ∉
        Set.range (algebraMap A (V.1.residueField (genericPoint V.1)))) →
      Representation.invariants ((matrixRepresentation τ).comp
        (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P).subtype) = ⊥) :
    ∃ K : ℕ, LAdicSheaf.LocalTermsKilledBy B V ℓ f j kbar
      (LAdicSheaf.representationSheaf B V _ τ hτ) K := by
  have := compactSpace_etaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
    (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
  refine LAdicSheaf.exists_localTermsKilledBy_of_smoothBoundary B V ℓ k f j kbar p hℓp L Ω r h
    (integralModel τ hτ) (continuous_integralModel τ hτ) ?_
  intro A _ _ _ _ _ _ _ P _ _ hℓA hA
  let := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
    (integralClosure A L)
  refine exists_inertiaLevelsKilledBy_inertia A _ L P hℓA _
    ((continuous_integralModel τ hτ).comp (galoisToFundamentalGroup V.1 L Ω).continuous) ?_
  intro v hv
  let x := (algebraicClosureGeometricPoint (V.1.residueField (genericPoint V.1)) Ω).map
    (V.1.fromSpecResidueField (genericPoint V.1))
  obtain ⟨Pm, hPm⟩ : ∃ Pm : GL (Fin r) ℚ_[ℓ], ∀ g, Matrix.GeneralLinearGroup.map
      (PadicInt.Coe.ringHom (p := ℓ)) (integralModel τ hτ g) = Pm⁻¹ * τ g * Pm :=
    ⟨_, map_integralModel τ hτ⟩
  let φQ : ℤ_[ℓ] →+* ℚ_[ℓ] := PadicInt.Coe.ringHom
  let vQ : Fin r → ℚ_[ℓ] := φQ ∘ v
  have hfix : ∀ g : EtaleFundamentalGroup V.1 x,
      ((integralModel τ hτ g : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v →
      ((τ g : GL (Fin r) ℚ_[ℓ]) : Matrix (Fin r) (Fin r) ℚ_[ℓ]) *ᵥ
        ((Pm : Matrix (Fin r) (Fin r) ℚ_[ℓ]) *ᵥ vQ) =
          (Pm : Matrix (Fin r) (Fin r) ℚ_[ℓ]) *ᵥ vQ := by
    intro g hg
    have h2 := hPm g
    have hmapv : ((Matrix.GeneralLinearGroup.map φQ (integralModel τ hτ g) : GL (Fin r) ℚ_[ℓ]) :
        Matrix (Fin r) (Fin r) ℚ_[ℓ]) *ᵥ vQ = vQ := by
      change φQ.mapMatrix ((integralModel τ hτ g : GL (Fin r) ℤ_[ℓ]) :
        Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ (φQ ∘ v) = φQ ∘ v
      funext i
      rw [RingHom.mapMatrix_apply, ← RingHom.map_mulVec, hg]
      rfl
    have hτg : τ g * Pm = Pm * Matrix.GeneralLinearGroup.map φQ (integralModel τ hτ g) := by
      rw [h2]; group
    rw [mulVec_mulVec, ← Units.val_mul, hτg, Units.val_mul, ← mulVec_mulVec, hmapv]
  have hmem : (Pm : Matrix (Fin r) (Fin r) ℚ_[ℓ]) *ᵥ vQ ∈ Representation.invariants
      ((matrixRepresentation τ).comp
        (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P).subtype) := by
    rw [Representation.mem_invariants]
    rintro ⟨g, hg⟩
    obtain ⟨σ, hσ, rfl⟩ := (Stacks.FundamentalGroup.mem_curvePointInertia_iff V.1 L Ω A P g).1 hg
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, matrixRepresentation_apply]
    exact hfix _ (hv σ hσ)
  rw [hinvτ A P hA, Submodule.mem_bot] at hmem
  have hvQ : vQ = 0 := by
    have := congrArg (fun y => ((Pm⁻¹ : GL (Fin r) ℚ_[ℓ]) : Matrix (Fin r) (Fin r) ℚ_[ℓ]) *ᵥ y) hmem
    simpa [mulVec_mulVec, ← Units.val_mul] using this
  funext i
  have := congrFun hvQ i
  exact PadicInt.coe_eq_zero.1 this

end Consumer

end Stacks.EtaleCohomology

end
