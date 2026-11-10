module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Finiteness.Cardinality
public import StacksFrontier.RingTheory.Depth.Nakayama
public import StacksFrontier.Algebra.Homology.ProjectiveDimension.FiniteResolution
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.Perfect.Module
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Depth.Localization
public import StacksFrontier.RingTheory.ProjectiveDimension.AuslanderBuchsbaum
public import StacksFrontier.RingTheory.Depth.AlgebraMap

/-!
# Additivity of projective dimension over a quotient

Let `R` be a Noetherian local ring, let `I` be an ideal of `R` and let `E` be a nonzero finite
module over `R ⧸ I`.  If `R ⧸ I` has finite projective dimension over `R` and `E` has finite
projective dimension over `R ⧸ I`, then `E`, viewed as an `R`-module, has finite projective
dimension, and

`pd_R(E) = pd_R(R ⧸ I) + pd_{R ⧸ I}(E)`.

## Main results

* `Stacks.ProjectiveDimension.Additivity.projectiveDimension_restrictScalars_quotient_eq_add` (tag
  0929) is the additivity
  statement above.

## Implementation notes

The underlying `R`-module of `E` is expressed by the canonical restriction-of-scalars functor
along the quotient map.  Projective dimensions are valued in `WithBot ℕ∞`, so finiteness of a
projective dimension is expressed by inequality with `⊤`.

Finiteness of `pd_R(E)` is the transitivity of perfectness along the quotient map: a perfect
`R ⧸ I`-module is represented by a bounded complex of finite projective `R ⧸ I`-modules, each
term of which is a retract of a finite free `R ⧸ I`-module and therefore of finite projective
dimension over `R`, so that the restriction of that complex is a bounded complex of perfect
`R`-modules and hence perfect by tag 066T.  This argument is carried out in the
`RestrictScalarsPerfect` section below; see the note there.

The additivity itself is the Auslander-Buchsbaum formula
(`Module.projectiveDimension_add_depth_eq_depth_self`) applied over `R` and over `R ⧸ I`,
together with the observation that the depth of an `R ⧸ I`-module with respect to the maximal
ideal of `R` agrees with its depth with respect to the maximal ideal of `R ⧸ I`.

## References

* [Stacks Project, Tag 0929](https://stacks.math.columbia.edu/tag/0929)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

/-! ## Support replayed for restriction of scalars along the quotient map

Tag 0929 needs the statement that restriction of scalars along a ring map whose target is a
perfect module carries perfect objects to perfect objects, which is tag 066V.  Tag 066V is not
claimed here: the declarations of this section are untagged, and are specialized to the quotient
map and to modules, which is all tag 0929 consumes.

A conceptual provider for tag 066V now exists,
  `StacksDraft.Perfect.isPerfect_restrictScalars_of_isPerfectModule`.
It is not used here, and the reason is a proof obligation rather than an oversight: that provider
states the COMPLEX-level form, on `IsPerfect (DerivedCategory.Q.obj K)`, whereas what tag 0929
consumes is the MODULE-level specialization, which this section derives by a different route
because the path to it through that provider runs through tag 066K.  Replacing this section by
the conceptual provider is therefore a change of proof, not a rename. -/

namespace RestrictScalarsPerfect

attribute [local instance] HasDerivedCategory.standard

/-- The projective dimension of a finite product of copies of a module of finite projective
dimension is again finite. -/
private lemma projectiveDimension_pi_ne_top {R : Type u} [Ring R] [Small.{v} R]
    (X : Type v) [AddCommGroup X] [Module R X]
    (hX : CategoryTheory.projectiveDimension (ModuleCat.of R X) ≠ ⊤) (n : ℕ) :
    CategoryTheory.projectiveDimension (ModuleCat.of R (Fin n → X)) ≠ ⊤ := by
  obtain ⟨m, hm⟩ := (CategoryTheory.projectiveDimension_ne_top_iff _).mp hX
  rw [CategoryTheory.projectiveDimension_ne_top_iff]
  refine ⟨m, ?_⟩
  induction n with
  | zero =>
    have hzero : IsZero (ModuleCat.of R (Fin 0 → X)) :=
      ModuleCat.isZero_iff_subsingleton.mpr ⟨fun _ _ => funext fun i => i.elim0⟩
    have := hzero.hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge _ 0 (m + 1) (Nat.zero_le _)
  | succ n ih =>
    have := hm
    have := ih
    let ecomp : (Fin (n + 1) → X) ≃ₗ[R] (X × (Fin n → X)) :=
      { (Fin.consEquiv (fun _ : Fin (n + 1) => X)).symm with
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact hasProjectiveDimensionLT_of_iso
      (ModuleCat.biprodIsoProd (ModuleCat.of R X) (ModuleCat.of R (Fin n → X)) ≪≫
        (LinearEquiv.toModuleIso ecomp).symm) (m + 1)

variable {R : Type u} [CommRing R]

/-- A finite `R ⧸ I`-module is finite over `R`. -/
private lemma finite_restrictScalars (I : Ideal R) (N : ModuleCat.{v} (R ⧸ I))
    [Module.Finite (R ⧸ I) N] :
    Module.Finite R (((ModuleCat.restrictScalars.{v} (Ideal.Quotient.mk I)).obj N :
      ModuleCat.{v} R) : Type v) := by
  let : Module R (N : Type v) := Module.compHom _ (Ideal.Quotient.mk I)
  have : IsScalarTower R (R ⧸ I) (N : Type v) := .of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite R (N : Type v) := Module.Finite.trans (R := R) (R ⧸ I) _
  exact inferInstanceAs (Module.Finite R (N : Type v))

/-- A finite projective `R ⧸ I`-module has finite projective dimension over `R` as soon as
`R ⧸ I` does: it is a retract of a finite free `R ⧸ I`-module. -/
private lemma projectiveDimension_restrictScalars_ne_top_of_projective
    (I : Ideal R)
    (hI : CategoryTheory.projectiveDimension
      ((ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk I)).obj
        (ModuleCat.of (R ⧸ I) (ULift.{max u v} (R ⧸ I)))) ≠ ⊤)
    (N : ModuleCat.{max u v} (R ⧸ I)) [Module.Finite (R ⧸ I) N]
    (hN : Module.Projective (R ⧸ I) N) :
    CategoryTheory.projectiveDimension
      ((ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk I)).obj N) ≠ ⊤ := by
  have := hN
  set F := ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk I) with hF
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' (R ⧸ I) (N : Type max u v)
  let lift : (Fin n → ULift.{max u v} (R ⧸ I)) ≃ₗ[R ⧸ I] (Fin n → (R ⧸ I)) :=
    LinearEquiv.piCongrRight fun _ => ULift.moduleEquiv
  let π' : (Fin n → ULift.{max u v} (R ⧸ I)) →ₗ[R ⧸ I] (N : Type max u v) :=
    π ∘ₗ lift.toLinearMap
  have hπ' : Function.Surjective π' := hπ.comp lift.surjective
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π' LinearMap.id hπ'
  let Free : ModuleCat.{max u v} (R ⧸ I) :=
    ModuleCat.of (R ⧸ I) (Fin n → ULift.{max u v} (R ⧸ I))
  let ρ : Retract (F.obj N) (F.obj Free) :=
    { i := F.map (ModuleCat.ofHom σ)
      r := F.map (ModuleCat.ofHom π')
      retract := by
        rw [← F.map_comp]
        change F.map (ModuleCat.ofHom (π' ∘ₗ σ)) = _
        rw [hσ]
        simp }
  have hFree : CategoryTheory.projectiveDimension (F.obj Free) ≠ ⊤ := by
    let : Module R (ULift.{max u v} (R ⧸ I)) :=
      Module.compHom _ (Ideal.Quotient.mk I)
    have hbase : CategoryTheory.projectiveDimension
        (ModuleCat.of R (ULift.{max u v} (R ⧸ I))) ≠ ⊤ := hI
    let eFree : ((F.obj Free : ModuleCat.{max u v} R) : Type max u v) ≃ₗ[R]
        (Fin n → ULift.{max u v} (R ⧸ I)) :=
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := id
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [ModuleCat.projectiveDimension_eq_of_linearEquiv (M := F.obj Free)
      (N := ModuleCat.of R (Fin n → ULift.{max u v} (R ⧸ I))) eFree]
    exact projectiveDimension_pi_ne_top (ULift.{max u v} (R ⧸ I)) hbase n
  obtain ⟨m, hm⟩ := (CategoryTheory.projectiveDimension_ne_top_iff _).mp hFree
  rw [CategoryTheory.projectiveDimension_ne_top_iff]
  have := hm
  exact ⟨m, ρ.hasProjectiveDimensionLT (m + 1)⟩

/-- Perfectness of a module is the finiteness of its projective dimension. -/
private lemma isPerfectModule_iff_projectiveDimension_ne_top
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    StacksDraft.Perfect.IsPerfectModule (R := R) M ↔ Module.projectiveDimension R M ≠ ⊤ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨d, F, hF, hzero⟩ :=
      (StacksDraft.Perfect.isPerfectModule_iff_exists_finite_projective_resolution M).mp h
    rw [CategoryTheory.projectiveDimension_ne_top_iff]
    let G : CategoryTheory.ObjectProperty.LeftResolution
        (fun N : ModuleCat.{v} R => CategoryTheory.Projective N ∧ Module.Finite R N)
        (ModuleCat.of R M) :=
      { complex := F.complex, property := fun i =>
          ⟨(IsProjective.iff_projective _).mp (hF i).2, (hF i).1⟩,
        π := F.π, quasiIso := F.quasiIso }
    refine ⟨d, (ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_projective_finite
      (ModuleCat.of R M) d).mpr ⟨G, ?_⟩⟩
    simpa [G] using hzero
  · obtain ⟨d, hd⟩ := (CategoryTheory.projectiveDimension_ne_top_iff _).mp h
    obtain ⟨F, hzero⟩ :=
      (ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_projective_finite
        (ModuleCat.of R M) d).mp hd
    let G : ModuleResolution R M :=
      { complex := F.complex
        hasHomology := F.hasHomology
        π := F.π
        quasiIso := F.quasiIso }
    exact (StacksDraft.Perfect.isPerfectModule_iff_exists_finite_projective_resolution M).mpr
      ⟨d, G, fun i => ⟨(F.property i).2, (IsProjective.iff_projective _).mpr (F.property i).1⟩,
        hzero⟩

/-- Perfectness of objects of the derived category is invariant under isomorphism. -/
private lemma isPerfect_iso {R : Type u} [Ring R]
    {X Y : DerivedCategory (ModuleCat.{v} R)} (e : X ≅ Y)
    (h : StacksDraft.Perfect.IsPerfect X) : StacksDraft.Perfect.IsPerfect Y := by
  obtain ⟨P, a, b, hge, hle, hfin, hproj, ⟨i⟩⟩ := h
  exact ⟨P, a, b, hge, hle, hfin, hproj, ⟨e.symm ≪≫ i⟩⟩

/-- **Local untagged replay of the content of tag 066V**, specialized to the quotient map and to
modules.  If `R ⧸ I` has finite projective dimension over the Noetherian ring `R`, then a perfect
`R ⧸ I`-module is perfect as an `R`-module. -/
private theorem isPerfectModule_restrictScalars [IsNoetherianRing R] (I : Ideal R)
    (hI : CategoryTheory.projectiveDimension
      ((ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk I)).obj
        (ModuleCat.of (R ⧸ I) (ULift.{max u v} (R ⧸ I)))) ≠ ⊤)
    (M : ModuleCat.{max u v} (R ⧸ I))
    (hM : StacksDraft.Perfect.IsPerfectModule (R := R ⧸ I) (M : Type max u v)) :
    StacksDraft.Perfect.IsPerfectModule (R := R)
      (((ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk I)).obj M :
        ModuleCat.{max u v} R) : Type max u v) := by
  set F := ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk I) with hF
  obtain ⟨P, a, b, hGE, hLE, hfin, hproj, ⟨e⟩⟩ := hM
  let P' : CochainComplex (ModuleCat.{max u v} R) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hP'GE : CochainComplex.IsStrictlyGE P' a :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff (K := P) F a).2 hGE
  have hP'LE : CochainComplex.IsStrictlyLE P' b :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff (K := P) F b).2 hLE
  have hterms : ∀ i : ℤ, StacksDraft.Perfect.IsPerfectModule (R := R) (P'.X i) := by
    intro i
    have := hfin i
    have : Module.Finite R ((P'.X i : ModuleCat.{max u v} R) : Type max u v) :=
      finite_restrictScalars I (P.X i)
    exact (isPerfectModule_iff_projectiveDimension_ne_top
      (R := R) (M := ((P'.X i : ModuleCat.{max u v} R) : Type max u v))).mpr
      (projectiveDimension_restrictScalars_ne_top_of_projective I hI (P.X i) (hproj i))
  have hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj P') :=
    StacksDraft.Perfect.isPerfect_of_bounded_of_isPerfectModule P'
      ⟨a, b, hP'GE, hP'LE⟩ hterms
  refine isPerfect_iso ?_ hperf
  exact ((F.mapDerivedCategorySingleFunctor 0).app M).symm ≪≫
      F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app P |>.symm

end RestrictScalarsPerfect

/-! ## Tag 0929 -/

namespace Stacks.ProjectiveDimension.Additivity

attribute [local instance] HasDerivedCategory.standard

private lemma add_depth_right_cancel {a b : WithBot ℕ∞} {d : ℕ∞} (hd : d ≠ ⊤)
    (h : a + (d : WithBot ℕ∞) = b + d) : a = b := by
  induction a with
  | bot =>
    induction b with
    | bot => rfl
    | coe b => simp [← WithBot.coe_add] at h
  | coe a =>
    induction b with
    | bot => simp [← WithBot.coe_add] at h
    | coe b =>
      have hab : a + d = b + d := by
        simpa only [← WithBot.coe_add, WithBot.coe_inj] using h
      exact congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞))
        (ENat.add_left_injective_of_ne_top hd hab)

/-- If `R ⧸ I` has finite projective dimension over the Noetherian ring `R` and the finite
`R ⧸ I`-module `E` has finite projective dimension over `R ⧸ I`, then `E` has finite projective
dimension over `R`. -/
theorem projectiveDimension_restrictScalars_quotient_ne_top
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v} R]
    (I : Ideal R) (E : Type v) [AddCommGroup E] [Module (R ⧸ I) E] [Module.Finite (R ⧸ I) E]
    (hRI : Module.projectiveDimension R (R ⧸ I) ≠ ⊤)
    (hE : Module.projectiveDimension (R ⧸ I) E ≠ ⊤) :
    Module.projectiveDimension R ((ModuleCat.restrictScalars.{v} (Ideal.Quotient.mk I)).obj
      (ModuleCat.of (R ⧸ I) E)) ≠ ⊤ := by
  let : Module R E := Module.compHom E (Ideal.Quotient.mk I)
  have : IsScalarTower R (R ⧸ I) E := .of_algebraMap_smul fun _ _ => rfl
  let E_R := (ModuleCat.restrictScalars.{v} (Ideal.Quotient.mk I)).obj
    (ModuleCat.of (R ⧸ I) E)
  have : Module.Finite R E := Module.Finite.trans (R := R) (R ⧸ I) E
  have : Module.Finite R E_R := inferInstanceAs (Module.Finite R E)
  let RI' := (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk I)).obj
    (ModuleCat.of (R ⧸ I) (ULift.{max u v} (R ⧸ I)))
  have : Module.Finite R RI' := Module.Finite.equiv
    (ULift.moduleEquiv (R := R) (M := R ⧸ I)).symm
  have eRI : RI' ≃ₗ[R] R ⧸ I := by
    dsimp [RI']
    exact ULift.moduleEquiv
  have hRI' : CategoryTheory.projectiveDimension (ModuleCat.of R RI') ≠ ⊤ := by
    rwa [ModuleCat.projectiveDimension_eq_of_linearEquiv
      (M := ModuleCat.of R RI') (N := ModuleCat.of R (R ⧸ I)) eRI]
  have : Module.Finite (R ⧸ I) (ULift.{max u v} E) :=
    Module.Finite.equiv (ULift.moduleEquiv (R := R ⧸ I) (M := E)).symm
  have eE : ULift.{max u v} E ≃ₗ[R ⧸ I] E := ULift.moduleEquiv
  have hperfectE' : StacksDraft.Perfect.IsPerfectModule (R := R ⧸ I) (ULift.{max u v} E) :=
    (RestrictScalarsPerfect.isPerfectModule_iff_projectiveDimension_ne_top
      (ULift.{max u v} E)).mpr <| by
      change CategoryTheory.projectiveDimension
        (ModuleCat.of (R ⧸ I) (ULift.{max u v} E)) ≠ ⊤
      rwa [ModuleCat.projectiveDimension_eq_of_linearEquiv
        (M := ModuleCat.of (R ⧸ I) (ULift.{max u v} E))
        (N := ModuleCat.of (R ⧸ I) E) eE]
  let ER' := (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk I)).obj
    (ModuleCat.of (R ⧸ I) (ULift.{max u v} E))
  have eER : ER' ≃ₗ[R] E_R := by
    dsimp [ER', E_R]
    change ULift.{max u v} E ≃ₗ[R] E
    exact ULift.moduleEquiv (R := R) (M := E)
  have : Module.Finite R ER' := Module.Finite.equiv eER.symm
  have hperfectER' : StacksDraft.Perfect.IsPerfectModule (R := R) ER' :=
    RestrictScalarsPerfect.isPerfectModule_restrictScalars I hRI'
      (ModuleCat.of (R ⧸ I) (ULift.{max u v} E)) hperfectE'
  change CategoryTheory.projectiveDimension (ModuleCat.of R E_R) ≠ ⊤
  rw [← ModuleCat.projectiveDimension_eq_of_linearEquiv
    (M := ModuleCat.of R ER') (N := ModuleCat.of R E_R) eER]
  exact (RestrictScalarsPerfect.isPerfectModule_iff_projectiveDimension_ne_top
    (R := R) (M := (ER' : Type max u v))).mp hperfectER'

/-- The depth of an `R ⧸ I`-module along the maximal ideal of the local ring `R` agrees with its
depth along the maximal ideal of `R ⧸ I`. -/
theorem depth_maximalIdeal_eq_depth_quotient {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) [IsLocalRing (R ⧸ I)] (M : Type v) [AddCommGroup M] [Module R M]
    [Module (R ⧸ I) M] [IsScalarTower R (R ⧸ I) M] :
    Module.depth R (IsLocalRing.maximalIdeal R) M =
      Module.depth (R ⧸ I) (IsLocalRing.maximalIdeal (R ⧸ I)) M := by
  rw [Module.depth_eq_depth_map_algebraMap (A := R) (B := R ⧸ I) Ideal.Quotient.mk_surjective]
  congr 1
  exact IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective

/-- **Stacks 0929.** Let `R` be a Noetherian local ring, `I` an ideal of `R`, and `E` a
nonzero finite `R ⧸ I`-module. If `R ⧸ I` has finite projective dimension over `R` and `E` has
finite projective dimension over `R ⧸ I`, then the restriction of `E` to `R` has finite
projective dimension, equal to the sum of the two given projective dimensions. -/
@[stacks 0929]
theorem projectiveDimension_restrictScalars_quotient_eq_add
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Small.{v} R]
    (I : Ideal R) (E : Type v) [AddCommGroup E] [Module (R ⧸ I) E]
    [Nontrivial E] [Module.Finite (R ⧸ I) E]
    (hRI : Module.projectiveDimension R (R ⧸ I) ≠ ⊤)
    (hE : Module.projectiveDimension (R ⧸ I) E ≠ ⊤) :
    let E_R := (ModuleCat.restrictScalars.{v} (Ideal.Quotient.mk I)).obj
      (ModuleCat.of (R ⧸ I) E)
    Module.projectiveDimension R E_R ≠ ⊤ ∧
      Module.projectiveDimension R E_R =
        Module.projectiveDimension R (R ⧸ I) + Module.projectiveDimension (R ⧸ I) E := by
  have : Nontrivial (R ⧸ I) := Module.nontrivial (R ⧸ I) E
  have : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : Module R E := Module.compHom E (Ideal.Quotient.mk I)
  have : IsScalarTower R (R ⧸ I) E := .of_algebraMap_smul fun _ _ => rfl
  let E_R := (ModuleCat.restrictScalars.{v} (Ideal.Quotient.mk I)).obj
    (ModuleCat.of (R ⧸ I) E)
  have : Nontrivial E_R := inferInstanceAs (Nontrivial E)
  have : Module.Finite R E := Module.Finite.trans (R := R) (R ⧸ I) E
  have : Module.Finite R E_R := inferInstanceAs (Module.Finite R E)
  have hER : Module.projectiveDimension R E_R ≠ ⊤ :=
    projectiveDimension_restrictScalars_quotient_ne_top I E hRI hE
  refine ⟨hER, ?_⟩
  have habE := Module.projectiveDimension_add_depth_eq_depth_self E_R hER
  change Module.projectiveDimension R E +
    (Module.depth R (IsLocalRing.maximalIdeal R) E : WithBot ℕ∞) =
      (Module.depth R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) at habE
  have habRI := Module.projectiveDimension_add_depth_eq_depth_self (R ⧸ I) hRI
  have habE' := Module.projectiveDimension_add_depth_eq_depth_self E hE
  rw [depth_maximalIdeal_eq_depth_quotient I E] at habE
  rw [depth_maximalIdeal_eq_depth_quotient I (R ⧸ I)] at habRI
  change Module.projectiveDimension R E =
    Module.projectiveDimension R (R ⧸ I) + Module.projectiveDimension (R ⧸ I) E
  exact add_depth_right_cancel (d := Module.depth (R ⧸ I) (IsLocalRing.maximalIdeal (R ⧸ I)) E)
    (Module.depth_lt_top (R ⧸ I) _ E (Module.maximalIdeal_smul_top_ne_top E)).ne
    (by rw [habE, add_assoc, habE', habRI])

end Stacks.ProjectiveDimension.Additivity

end
