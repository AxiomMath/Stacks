module

public import StacksFrontier.Homology.ExtendScalars.DerivedHomology
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.RelativelyPerfect.BaseChange
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.Homology.Tor.IndependenceBaseChange

/-!
# Boundedness below of derived base changes

Boundedness below of an object of `D(R)` is preserved by derived extension of scalars along a
flat ring map and reflected along a faithfully flat one, and it is unchanged by restriction of
scalars. Consequently the derived fibre `K ⊗^L_R L` along a ring map `R → L` to a field is bounded
below exactly when the derived fibre `K ⊗^L_R κ(p)` at the kernel `p` is, and for a flat
`R`-algebra `A`, a pushout `A' = A ⊗_R L` and `K ∈ D(A)`, the object `K ⊗^L_A A'` is bounded below
exactly when `K ⊗^L_R L` is (Stacks 065Z for Tor independent squares).

## Main results

* `CochainComplex.DerivedExtensionScalars.isGE_totalDerivedExtensionScalars_iff_residueField`
* `CochainComplex.DerivedExtensionScalars.isGE_totalDerivedExtensionScalars_iff_of_isPushout`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CochainComplex.DerivedExtensionScalars

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Derived extension of scalars along a flat ring map preserves boundedness below. -/
theorem isGE_totalDerivedExtensionScalars_obj_of_flat (f : R →+* S) (hf : f.Flat)
    (K : DerivedCategory (ModuleCat.{u} R)) (a : ℤ) (hK : K.IsGE a) :
    ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj K).IsGE a := by
  let := f.toAlgebra
  refine (DerivedCategory.isGE_iff _ a).2 fun i hi => ?_
  refine IsZero.of_iso ?_ (derivedExtensionScalarsHomologyIso.{u, u, u} f hf K i)
  have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) :=
    ModuleCat.subsingleton_of_isZero ((DerivedCategory.isGE_iff K a).1 hK i hi)
  show IsZero (ModuleCat.of S (TensorProduct R S
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)))
  exact ModuleCat.isZero_of_subsingleton _

/-- Derived extension of scalars along a faithfully flat ring map reflects boundedness below. -/
theorem isGE_of_isGE_totalDerivedExtensionScalars_obj (f : R →+* S) (hf : f.FaithfullyFlat)
    (K : DerivedCategory (ModuleCat.{u} R)) (a : ℤ)
    (hK : ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj K).IsGE a) : K.IsGE a := by
  let := f.toAlgebra
  have : Module.FaithfullyFlat R S := hf
  refine (DerivedCategory.isGE_iff K a).2 fun i hi => ?_
  have h1 : Subsingleton (TensorProduct R S
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) :=
    ModuleCat.subsingleton_of_isZero (IsZero.of_iso ((DerivedCategory.isGE_iff _ a).1 hK i hi)
      (derivedExtensionScalarsHomologyIso.{u, u, u} f hf.flat K i).symm)
  have := (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right R S).1 h1
  exact ModuleCat.isZero_of_subsingleton _

/-- Boundedness below is invariant under isomorphism. -/
private theorem isGE_iff_of_iso {A : Type u} [CommRing A] {X Y : DerivedCategory (ModuleCat.{u} A)}
    (e : X ≅ Y) (a : ℤ) : X.IsGE a ↔ Y.IsGE a :=
  ⟨fun _ => DerivedCategory.TStructure.t.isGE_of_iso e a,
    fun _ => DerivedCategory.TStructure.t.isGE_of_iso e.symm a⟩

/-- Restriction of scalars neither creates nor destroys boundedness below. -/
theorem isGE_restrictScalars_mapDerivedCategory_obj_iff (f : R →+* S)
    (K : DerivedCategory (ModuleCat.{u} S)) (a : ℤ) :
    ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj K).IsGE a ↔ K.IsGE a := by
  rw [DerivedCategory.isGE_iff, DerivedCategory.isGE_iff]
  refine forall_congr' fun i => imp_congr_right fun _ => ?_
  refine (Iso.isZero_iff ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
    (ModuleCat.restrictScalars.{u} f) i).app K)).trans ?_
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  exact Iff.rfl

/-- For ring maps `f : R → κ` to a field and `g : κ → L` to a nonzero ring, the derived base
change of `M ∈ D(R)` to `L` is bounded below exactly when its derived base change to `κ` is. -/
theorem isGE_totalDerivedExtensionScalars_comp_iff {κ L : Type u} [Field κ] [CommRing L]
    [Nontrivial L] (f : R →+* κ) (g : κ →+* L) (M : DerivedCategory (ModuleCat.{u} R)) (a : ℤ) :
    ((totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor.obj M).IsGE a ↔
      ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj M).IsGE a := by
  let := g.toAlgebra
  have hff : g.FaithfullyFlat := (inferInstance : Module.FaithfullyFlat κ L)
  let e := (totalDerivedExtensionScalarsComp.{u, u} f g).app M
  exact (isGE_iff_of_iso e a).symm.trans
    ⟨fun h => isGE_of_isGE_totalDerivedExtensionScalars_obj g hff _ a h,
      fun h => isGE_totalDerivedExtensionScalars_obj_of_flat g hff.flat _ a h⟩

/-- **The derived fibre along a map to a field is read at the kernel.** For a ring map
`φ : R → L` to a field and `M ∈ D(R)`, `M ⊗^L_R L` is bounded below exactly when
`M ⊗^L_R κ(p)` is, for `p = ker φ`. -/
theorem isGE_totalDerivedExtensionScalars_iff_residueField {L : Type u} [CommRing L]
    (hL : IsField L) (φ : R →+* L) (M : DerivedCategory (ModuleCat.{u} R)) (a : ℤ) :
    haveI := hL.isDomain
    haveI := RingHom.ker_isPrime φ
    ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj M).IsGE a ↔
      ((totalDerivedExtensionScalars.{u, u, u}
        (algebraMap R (RingHom.ker φ).ResidueField)).functor.obj M).IsGE a := by
  have := hL.isDomain
  have := RingHom.ker_isPrime φ
  have : Nontrivial L := ⟨hL.exists_pair_ne⟩
  have hunit : (RingHom.ker φ).primeCompl ≤ Submonoid.comap φ (IsUnit.submonoid L) := by
    intro r hr
    obtain ⟨b, hb⟩ := hL.mul_inv_cancel fun h => hr (RingHom.mem_ker.2 h)
    exact IsUnit.of_mul_eq_one b hb
  let g := Ideal.ResidueField.lift (RingHom.ker φ) φ le_rfl hunit
  have hφ : φ = g.comp (algebraMap R (RingHom.ker φ).ResidueField) :=
    RingHom.ext fun r => (Ideal.ResidueField.lift_algebraMap _ φ le_rfl hunit r).symm
  conv_lhs => rw [hφ]
  exact isGE_totalDerivedExtensionScalars_comp_iff _ g M a

/-- The derived fibre at a prime only depends on the prime. -/
theorem isGE_totalDerivedExtensionScalars_residueField_congr {I J : Ideal R} [I.IsPrime]
    [J.IsPrime] (h : I = J) (M : DerivedCategory (ModuleCat.{u} R)) (a : ℤ) :
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R I.ResidueField)).functor.obj M).IsGE a ↔
      ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R J.ResidueField)).functor.obj M).IsGE
        a := by
  subst h
  rfl

/-- **Boundedness below across a Tor independent base change.** For a flat `R`-algebra `A`, a
pushout `A' = A ⊗_R R'` and `K ∈ D(A)`, the derived base change `K ⊗^L_A A'` is bounded below
exactly when `K ⊗^L_R R'` is, `K` being read over `R`. -/
theorem isGE_totalDerivedExtensionScalars_iff_of_isPushout {A R' A' : Type u} [CommRing A]
    [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A']
    [Algebra R' A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] [Algebra.IsPushout R A R' A']
    [Module.Flat R A] (K : DerivedCategory (ModuleCat.{u} A)) (a : ℤ) :
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj K).IsGE a ↔
      ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor.obj
        ((ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory.obj K)).IsGE a := by
  let Tg := totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')
  let Th := totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')
  have : Tg.functor.IsLeftDerivedFunctor Tg.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := Tg.isLeftDerived
  have : Th.functor.IsLeftDerivedFunctor Th.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) := Th.isLeftDerived
  obtain ⟨cmp, hiso⟩ : ∃ cmp : (ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory ⋙
      Tg.functor ⟶
        Th.functor ⋙ (ModuleCat.restrictScalars.{u} (algebraMap R' A')).mapDerivedCategory,
      IsIso cmp := by
    refine ⟨_, @RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent.{u,
      u, u, u, u, u + 1, u + 1, u + 1, u + 1} R A R' A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      PseudoCoherence.torIndependent_of_flat Tg.functor Th.functor Tg.comparison Th.comparison
      ?_ ?_⟩
    all_goals first | exact Tg.isLeftDerived | exact Th.isLeftDerived
  refine (isGE_restrictScalars_mapDerivedCategory_obj_iff (algebraMap R' A') _ a).symm.trans ?_
  exact (isGE_iff_of_iso (asIso (cmp.app K)) a).symm

end CochainComplex.DerivedExtensionScalars

end
