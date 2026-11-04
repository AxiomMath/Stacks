module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InvariantsDeltaForget
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleTorsionReduction
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportGeometricCoinvariantsEquiv
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricRepresentationComparisonIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCompactSupport
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DeJongConjectureFlatnessGenus
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.Deformation.Representation.FixedDeterminantFlatness.AdjointCoinvariants

/-!
# `H ²(π₁(X_k̄), ad⁰ ρ₀) = 0` for a curve of positive genus

Let `X` be a geometrically irreducible smooth proper curve over a field `k`, `k̄` an algebraic
closure, `ℓ` a prime invertible in `k`, and `ρ₀ : π₁(X) → GLₙ(𝐅_ℓ)` continuous with
`ρ₀|_{π₁(X_k̄)}` absolutely irreducible and `ℓ ∤ n`. This file proves the input of the flatness
half of [Stacks, Tag 03W1]:

* `H ²(X_k̄, ℱ_{ad⁰ ρ₀}) = 0`: since `X` is proper, `H ² = H ²_c`
  (`Stacks.EtaleCohomology.galoisCompactSupportCohomologyGroupOfIsProperIso`), and
  `H ²_c(X_k̄, ℱ_ρ) ≅ M_{π₁(X_k̄)}` (`AlgebraicGeometry.compactSupportGeometricCoinvariantsEquiv`,
  Tag 03VK); the coinvariants of `ad⁰` vanish (`Deformation.AdZero.span_smul_sub_eq_top`);
* in genus `≥ 1`, `H ²(π₁(X_k̄), ad⁰) ≅ H ²(X_k̄, ℱ_{ad⁰})`
  (`AlgebraicGeometry.bijective_geometricComparison_app_of_genus`, Tag 03VM), so the
  derived-functor group vanishes, and hence every locally constant `2`-cocycle is a coboundary.

## Main definitions

* `Deformation.AdZero.finiteTypeContinuousModule`: `ad⁰ ρ` as a finite `𝐅_ℓ`-module with a
  continuous action.

## Main results

* `AlgebraicGeometry.isZero_geometricRepresentationCohomology_two_adZero`
* `AlgebraicGeometry.vanishesTwo_adZero_of_one_le_genus`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.ContinuousCohomology
  Stacks.EtaleCohomology Stacks.Frobenius

universe u

namespace Deformation.AdZero

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n ℓ : ℕ}
  [Fact ℓ.Prime]

/-- The actions of `G` and of `𝐅_ℓ` on the lift of `ad⁰ ρ` commute. -/
instance smulCommClass_ulift (ρ : G →* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)) :
    SMulCommClass G (ZMod ℓ) (ULift.{u} (AdZero ρ)) where
  smul_comm g a X := ULift.ext _ _ (smul_comm g a X.down)

/-- **`ad⁰ ρ` as a finite `𝐅_ℓ`-module with a continuous `G`-action**, its carrier lifted to the
universe of `G`. -/
def finiteTypeContinuousModule (ρ : G →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)) :
    FiniteTypeContinuousModule.{0, u, u} (ZMod ℓ) G :=
  ⟨ofRepresentation (Representation.ofDistribMulAction (ZMod ℓ) G
      (ULift.{u} (AdZero ρ.toMonoidHom))) ((isContinuous_actionOfRepresentation_iff _).2 fun X => by
        have h := hasOpenStabilizers (ρ := ρ) X.down
        have hset : {g : G | (Representation.ofDistribMulAction (ZMod ℓ) G
            (ULift.{u} (AdZero ρ.toMonoidHom))) g X = X} = {g : G | g • X.down = X.down} := by
          ext g
          exact ⟨fun h => congrArg ULift.down h, fun h => ULift.ext _ _ h⟩
        rw [hset]
        exact h),
    (inferInstance : Module.Finite (ZMod ℓ) (ULift.{u} (AdZero ρ.toMonoidHom)))⟩

end Deformation.AdZero

namespace AlgebraicGeometry

section Etale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  [ConnectedSpace X.1] [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) {n ℓ : ℕ} [Fact ℓ.Prime]

omit [IsAlgClosed kbar] in
/-- **The coinvariants of `ad⁰ ρ₀` under `π₁(X_k̄)` vanish** when `ρ₀|_{π₁(X_k̄)}` is absolutely
irreducible and `ℓ ∤ n`. -/
theorem subsingleton_coinvariants_geometricRepresentation_adZero (hn : ¬ ℓ ∣ n)
    (ρ₀ : EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) →ₜ*
        Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (hirr : Deformation.IsAbsolutelyIrreducible fun g : EtaleFundamentalGroup _ y =>
      ρ₀ (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g)) :
    Subsingleton (Stacks.Trace.coinvariants (geometricRepresentation B X f kbar (ZMod ℓ) y
      (Deformation.AdZero.finiteTypeContinuousModule ρ₀))) := by
  let ι := etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
    (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y
  let ρ' := ρ₀.comp ι
  have hirr' : Deformation.IsAbsolutelyIrreducible
      fun g : (⊤ : Subgroup (EtaleFundamentalGroup _ y)) => ρ'.toMonoidHom g := by
    unfold Deformation.IsAbsolutelyIrreducible at hirr ⊢
    rw [← hirr]
    congr 1
    ext M
    exact ⟨fun ⟨g, hg⟩ => ⟨g.1, hg⟩, fun ⟨g, hg⟩ => ⟨⟨g, Subgroup.mem_top g⟩, hg⟩⟩
  have hspan := Deformation.AdZero.span_smul_sub_eq_top (ρ := ρ'.toMonoidHom) ⊤ hirr' hn
  suffices htop : Stacks.Trace.coinvariantsKer (geometricRepresentation B X f kbar (ZMod ℓ) y
      (Deformation.AdZero.finiteTypeContinuousModule ρ₀)) = ⊤ by
    refine ⟨fun a b => ?_⟩
    induction a using Submodule.Quotient.induction_on with | _ a => ?_
    induction b using Submodule.Quotient.induction_on with | _ b => ?_
    rw [Submodule.Quotient.eq, htop]
    trivial
  rw [eq_top_iff]
  have h := congrArg (Submodule.map (ULift.moduleEquiv :
    ULift.{u + 1} (Deformation.AdZero ρ'.toMonoidHom) ≃ₗ[ZMod ℓ] _).symm.toLinearMap) hspan
  rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h
  refine h.ge.trans (Submodule.span_mono ?_)
  rintro _ ⟨_, ⟨⟨g, X⟩, rfl⟩, rfl⟩
  exact ⟨(g.1, ULift.up X), rfl⟩

variable [IsProper f]

/-- **`H ²(X_k̄, ℱ_{ad⁰ ρ₀}) = 0`** for a geometrically connected smooth proper curve `X` over `k`,
`ρ₀|_{π₁(X_k̄)}` absolutely irreducible, `ℓ ∤ n` and `ℓ` invertible in `k̄`: through
`H ² = H ²_c` (`X` is proper) and `H ²_c(X_k̄, ℱ_ρ) ≅ M_{π₁(X_k̄)}` (Tag 03VK). -/
theorem isZero_geometricRepresentationCohomology_two_adZero (hℓ : IsUnit (ℓ : kbar))
    (hn : ¬ ℓ ∣ n)
    (ρ₀ : EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) →ₜ*
        Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (hirr : Deformation.IsAbsolutelyIrreducible fun g : EtaleFundamentalGroup _ y =>
      ρ₀ (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g)) :
    IsZero (((geometricRepresentationCohomology.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) (ZMod ℓ) f kbar).functor 2).obj
        (Deformation.AdZero.finiteTypeContinuousModule ρ₀)) := by
  have := etaleModules_enoughInjectives.{u, 0} (ZMod ℓ) (fieldBaseChange (Over.mk f) kbar)
  let := HasDerivedCategory.standard
    (EtaleModules.{u, 0} (ZMod ℓ) (fieldBaseChange (Over.mk f) kbar))
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} (ZMod ℓ))
  have hn' : IsUnit ((Fintype.card (ZMod ℓ) : ℕ) : kbar) := by rwa [ZMod.card]
  have hζ := (exists_isPrimitiveRoot_of_isUnit hn').choose_spec
  let M := Deformation.AdZero.finiteTypeContinuousModule ρ₀
  let F := (representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
    (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) (ZMod ℓ)).obj M
  let e := compactSupportGeometricCoinvariantsEquiv B X f kbar (ZMod ℓ) y
    (CompactificationOf.ofProper f) hn' hζ M
  have := subsingleton_coinvariants_geometricRepresentation_adZero B X f kbar y hn ρ₀ hirr
  let H := galoisCompactSupportCohomologyGroup.{u, 0} (ZMod ℓ) f
      (CompactificationOf.ofProper f) kbar
      ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) ((2 : ℕ) : ℤ)
  have : Subsingleton H := e.toEquiv.subsingleton
  refine (ModuleCat.isZero_of_subsingleton H).of_iso ?_
  exact (Stacks.DerivedIndexing.rightDerivedIso (etaleModuleGlobalSections.{u, 0} (ZMod ℓ)
      (fieldBaseChange (Over.mk f) kbar)) 2).app
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) (fieldBaseChangeProj (Over.mk f) kbar)).obj F) ≪≫
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} (ZMod ℓ)) ((2 : ℕ) : ℤ)).mapIso
      ((etaleModuleDerivedGlobalSections.{u, 0} (ZMod ℓ) (fieldBaseChange (Over.mk f) kbar)).mapIso
        (fieldBaseChangeRestrictionSingleIso (Over.mk f) kbar F).symm) ≪≫
    (galoisCompactSupportCohomologyGroupOfIsProperIso (ZMod ℓ) f kbar
      ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) ((2 : ℕ) : ℤ)).symm

end Etale

section Group

/-- `ℓ` is invertible in an extension of a field of characteristic `p ≠ ℓ`. -/
theorem isUnit_natCast_of_ne_charP (k K : Type*) [Field k] [Field K] [Algebra k K] (p ℓ : ℕ)
    [CharP k p] [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : IsUnit (ℓ : K) := by
  have hℓk : (ℓ : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k p]
    intro hd
    rcases (Fact.out : ℓ.Prime).eq_one_or_self_of_dvd p hd with h1 | h1
    · exact CharP.char_ne_one k p h1
    · exact hℓp h1.symm
  rw [isUnit_iff_ne_zero, ← map_natCast (algebraMap k K)]
  exact (map_ne_zero _).2 hℓk

/-- **`H ²(π₁(X_k̄), ad⁰ ρ₀) = 0` at the cochain level in positive genus.** Let `X` be a
geometrically irreducible smooth proper curve over a field `k` of characteristic `p`, `k̄` an
algebraic closure, `ℓ ≠ p` a prime, `ρ₀ : π₁(X) → GLₙ(𝐅_ℓ)` continuous with `ρ₀|_{π₁(X_k̄)}`
absolutely irreducible and `ℓ ∤ n`, and assume `X_k̄` has genus `≥ 1`. Then every locally
constant `2`-cocycle of `π₁(X_k̄)` with values in `ad⁰ ρ₀` is a coboundary.

The derived-functor group `H ²(π₁(X_k̄), ad⁰)` is `H ²(X_k̄, ℱ_{ad⁰})` (Tag 03VM, genus `≥ 1`),
which vanishes by `AlgebraicGeometry.isZero_geometricRepresentationCohomology_two_adZero`; the
cochain statement follows by
`Stacks.GroupCohomology.vanishesTwo_of_isZero_continuousGroupCohomology_two`. -/
theorem vanishesTwo_adZero_of_one_le_genus
    (k kbar : Type u) [Field k] [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (p ℓ n : ℕ) [CharP k p] [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (hn : ¬ ℓ ∣ n)
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IsCurve k f] [Smooth f] [IsProper f] [GeometricallyIrreducible f] [ConnectedSpace X]
    [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (x : GeometricPoint (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
    (ρ₀ : EtaleFundamentalGroup X (x.map (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))) →ₜ*
        Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (hirred : Deformation.IsAbsolutelyIrreducible fun g : EtaleFundamentalGroup _ x =>
      ρ₀ (etaleFundamentalGroupMap (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) x g))
    (hg : 1 ≤ genus (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))) :
    VanishesTwo (EtaleFundamentalGroup _ x)
      (Deformation.AdZero ((ρ₀.comp (etaleFundamentalGroupMap (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) x)).toMonoidHom)) := by
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : Algebra.IsAlgebraic k kbar := IsAlgClosure.isAlgebraic
  have : GeometricallyConnected f := ⟨fun _ _ y Z fst snd h ↦ @IrreducibleSpace.connectedSpace Z _
    ((inferInstance : GeometricallyIrreducible f).geometrically_irreducibleSpace y fst snd h)⟩
  have : ConnectedSpace (fieldBaseChange (Over.mk f) kbar) :=
    ‹ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))›
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have := isCurve_pullback_snd k kbar f
  have : IsCurve kbar (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) :=
    ‹IsCurve kbar (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))›
  have : Smooth (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) :=
    inferInstanceAs (Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
  have : IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) :=
    inferInstanceAs (IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
  have := compactSpace_etaleFundamentalGroup _ x
  have := totallyDisconnectedSpace_etaleFundamentalGroup _ x
  have := compactSpace_etaleFundamentalGroup _
    (x.map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
  have := totallyDisconnectedSpace_etaleFundamentalGroup _
    (x.map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
  let B := BigEtaleSite.containing X
  let X' : B.Scheme := ⟨X, BigEtaleSite.contains_containing X⟩
  have : ConnectedSpace X'.1 := ‹ConnectedSpace X›
  have : CompactSpace X'.1 := ‹CompactSpace X›
  have : QuasiSeparatedSpace X'.1 := ‹QuasiSeparatedSpace X›
  have hK := contains_fieldBaseChange_of_isCurve B X' f kbar
  have hℓ : IsUnit (ℓ : kbar) := isUnit_natCast_of_ne_charP k kbar p ℓ hℓp
  have hΛ : IsUnit ((Nat.card (ZMod ℓ) : ℕ) : kbar) := by rwa [Nat.card_zmod]
  let M := Deformation.AdZero.finiteTypeContinuousModule ρ₀
  have hbij := bijective_geometricComparison_app_of_genus B X' (ZMod ℓ) f kbar hK x
    (inferInstance : IsCurve k f) hg hΛ 2 M
  have hiso : IsIso (((geometricComparison B X' (ZMod ℓ) f kbar hK x).app 2).app M) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hbij
  have htgt := isZero_geometricRepresentationCohomology_two_adZero B X' f kbar x hℓ hn ρ₀ hirred
  have hsrc : IsZero (((invariantsDelta.{0, u + 1, u + 1} (ZMod ℓ)
      (G := EtaleFundamentalGroup _ x)).functor 2).obj
        ((finiteTypeContinuousModuleToRes (ZMod ℓ) (etaleFundamentalGroupMap (pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) x)).obj M)) :=
    htgt.of_iso
      (@asIso _ _ _ _ (((geometricComparison B X' (ZMod ℓ) f kbar hK x).app 2).app M) hiso)
  have h3 := isZero_continuousGroupCohomology_of_isZero_invariantsDelta (ZMod ℓ) 2 _ hsrc
  have h4 := vanishesTwo_of_isZero_continuousGroupCohomology_two _ h3
  let N := (continuousModuleForget.{0, u + 1, u + 1} (ZMod ℓ) _).obj
    ((finiteTypeContinuousModuleToRes (ZMod ℓ) (etaleFundamentalGroupMap (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) x)).obj M)
  let := carrierAction N
  exact vanishesTwo_of_addEquiv (M := N.obj.obj.V)
    (AddEquiv.ulift : ULift.{u + 1} (Deformation.AdZero ((ρ₀.comp (etaleFundamentalGroupMap
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) x)).toMonoidHom)) ≃+ _)
    (fun _ _ => rfl) h4

end Group

end AlgebraicGeometry

end
