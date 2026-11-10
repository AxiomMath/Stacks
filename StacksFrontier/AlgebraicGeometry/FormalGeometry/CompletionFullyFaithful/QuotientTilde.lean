module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.IdealSheafEq
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerQuotientSections
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.BlowupFibreDimension

/-!
# The ideal-power quotient of the structure sheaf, as an associated sheaf

Let `A` be a commutative ring, `I ⊆ A` an ideal and `𝓘 = I 𝒪_{Spec A}` the ideal sheaf it
generates. The quotient `𝒪_{Spec A} / 𝓘ⁿ 𝒪_{Spec A}` is the sheaf associated to `A / Iⁿ`,
compatibly with the two quotient projections out of the structure sheaf.

The proof is the one the affine theory supplies: both sides are quasi-coherent, so both are
sheaves associated to modules, and the module on the left is read off its global sections. There
the quotient projection is surjective with kernel `𝓘ⁿ(X)`, which for `𝓘 = I 𝒪_{Spec A}` is the
image of `Iⁿ`; so the global sections are `A / Iⁿ`.

## Main results

* `Stacks.Algebraization.surjective_app_top_unitIdealPowerQuotientπ` and
  `Stacks.Algebraization.app_top_unitIdealPowerQuotientπ_eq_zero_iff` — on an affine scheme the
  quotient projection `Γ(X, 𝒪_X) ⟶ Γ(X, 𝒪_X / 𝓘ⁿ 𝒪_X)` is surjective with kernel `𝓘ⁿ(X)`.
* `Stacks.Algebraization.specUnitQuotientSectionsIso` — `Γ(Spec A, 𝒪 / Iⁿ 𝒪)` is `A / Iⁿ`.
* `Stacks.Algebraization.exists_specUnitQuotient_iso` — **`𝒪_{Spec A} / Iⁿ 𝒪_{Spec A}` is the
  sheaf associated to `A / Iⁿ`**, compatibly with the quotient projections.
* `Stacks.Algebraization.complementPrincipalIdealSheaf_eq_comap` — on
  `U = Spec(A) ∖ V(𝔞)` the ideal sheaf `f 𝒪_U` is the inverse image of `f 𝒪_{Spec A}`.

## Implementation notes

The affine statements are read off
`Stacks.Cohomology.FormalFunctions.idealPowerQuotientSubschemeSectionsIso_hom_app_top_π`, which
identifies the composite of the projection on global sections with the comparison of
[Stacks, Tag 0EL1] with restriction of functions along the closed immersion of the subscheme cut
out by `𝓘ⁿ`. That restriction is surjective because the ambient scheme is affine
(`AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine`) and its kernel is `𝓘ⁿ(X)`
because the ideal sheaf of a closed subscheme is computed by the kernels of its restriction maps
(`AlgebraicGeometry.Scheme.Hom.ker_apply`) and the subscheme of an ideal sheaf has that ideal
sheaf as its kernel.

The passage from global sections to sheaves is the tilde-sections adjunction of
`AlgebraicGeometry.tilde.adjunction`: a quasi-coherent module on an affine spectrum is the sheaf
associated to its global sections (`AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ`), and
the two projections are matched by the naturality of the counit together with the triangle
identity. `Stacks.Algebraization.specUnitQuotientπ` and
`Stacks.Algebraization.specUnitQuotientCounit` ascribe to the projection and to the counit the
spellings `(tilde.functor R).obj M` of their sources: `tilde M` and
`(tilde.functor R).obj M`, and `Γ(X, ⊤)` and `Γ(𝒪_X, ⊤)`, are definitionally equal but not
syntactically equal, and `rw` and `simp` build motives that are not type-correct across the
difference.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Section 02O7](https://stacks.math.columbia.edu/tag/02O7)
* [Stacks Project, Tag 01IC](https://stacks.math.columbia.edu/tag/01IC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Algebraization

section Affine

variable {X : Scheme.{u}} (K : X.IdealSheafData) (n : ℕ)

/-- The quotient projection `𝒪_X ⟶ 𝒪_X / 𝓘ⁿ 𝒪_X` of the structure sheaf. -/
public abbrev unitIdealPowerQuotientπ :
    X.unitModule ⟶ idealPowerQuotient K n X.unitModule :=
  cokernel.π (C := X.Modules) (idealPowerMultiple K n X.unitModule).ι

/-- Sections of the comparison of [Stacks, Tag 0EL1] at the structure sheaf form a bijection. -/
public theorem bijective_app_top_idealPowerQuotientSubschemeIso :
    Function.Bijective
      ((Cohomology.FormalFunctions.idealPowerQuotientSubschemeIso K n).hom.app
        (⊤ : X.Opens)) :=
  (sectionsEquivOfIso (Cohomology.FormalFunctions.idealPowerQuotientSubschemeIso K n)
    (⊤ : X.Opens)).bijective

/-- The quotient projection sends `x` to `y` exactly when restricting `x` to the closed subscheme
cut out by the `n`-th power gives the image of `y` under the comparison of [Stacks, Tag 0EL1]. -/
private theorem app_top_unitIdealPowerQuotientπ_eq_iff (x : Γ(X, ⊤)) (y) :
    (unitIdealPowerQuotientπ K n).app (⊤ : X.Opens) x = y ↔
      (K ^ n).subschemeι.appTop x =
        (Cohomology.FormalFunctions.idealPowerQuotientSubschemeIso K n).hom.app
          (⊤ : X.Opens) y := by
  rw [← (bijective_app_top_idealPowerQuotientSubschemeIso K n).1.eq_iff,
    Cohomology.FormalFunctions.idealPowerQuotientSubschemeSectionsIso_hom_app_top_π]
  exact Iff.rfl

variable [IsAffine X]

/-- **The quotient projection is surjective on global sections of an affine scheme.** -/
public theorem surjective_app_top_unitIdealPowerQuotientπ :
    Function.Surjective ((unitIdealPowerQuotientπ K n).app (⊤ : X.Opens)) := fun y =>
  have ⟨x, hx⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine (K ^ n).subschemeι).2
    ((Cohomology.FormalFunctions.idealPowerQuotientSubschemeIso K n).hom.app (⊤ : X.Opens) y)
  ⟨x, (app_top_unitIdealPowerQuotientπ_eq_iff K n x y).2 hx⟩

/-- The ideal of the `n`-th power of a quasi-coherent ideal sheaf over the top affine open is the
kernel of the restriction of functions to the closed subscheme it cuts out. -/
public theorem ideal_pow_top_eq_ker_subschemeι_app :
    (K ^ n).ideal ⟨⊤, isAffineOpen_top X⟩ =
      RingHom.ker ((K ^ n).subschemeι.app (⊤ : X.Opens)).hom := by
  have h := Scheme.Hom.ker_apply (K ^ n).subschemeι ⟨⊤, isAffineOpen_top X⟩
  rwa [Scheme.IdealSheafData.ker_subschemeι] at h

/-- A global function lies in the ideal of the `n`-th power exactly when it restricts to zero on
the closed subscheme that power cuts out. -/
public theorem mem_ideal_pow_top_iff (x : Γ(X, ⊤)) :
    x ∈ (K ^ n).ideal ⟨⊤, isAffineOpen_top X⟩ ↔
      (K ^ n).subschemeι.appTop x = 0 := by
  rw [ideal_pow_top_eq_ker_subschemeι_app]
  exact RingHom.mem_ker

/-- **The kernel of the quotient projection on global sections of an affine scheme is the ideal
of the `n`-th power.** -/
public theorem app_top_unitIdealPowerQuotientπ_eq_zero_iff (x : Γ(X, ⊤)) :
    (unitIdealPowerQuotientπ K n).app (⊤ : X.Opens) x = 0 ↔
      x ∈ (K ^ n).ideal ⟨⊤, isAffineOpen_top X⟩ := by
  rw [mem_ideal_pow_top_iff, app_top_unitIdealPowerQuotientπ_eq_iff, map_zero]
  exact Iff.rfl

end Affine

/-! ### The quotient of the structure sheaf of an affine spectrum -/

section Spec

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)

/-- Over the whole spectrum the ideal of `I 𝒪_{Spec A}` is the image of `I` under
`A ≅ Γ(Spec A, 𝒪)`. -/
public theorem specIdealSheaf_ideal_top :
    (specIdealSheaf A I).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom I := by
  rw [specIdealSheaf, Scheme.IdealSheafData.ofIdealTop_ideal]
  simp

/-- Over the whole spectrum the ideal of `(I 𝒪_{Spec A})ⁿ` is the image of `Iⁿ`. -/
public theorem specIdealSheaf_pow_ideal_top :
    (specIdealSheaf A I ^ n).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (I ^ n) := by
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, specIdealSheaf_ideal_top, Ideal.map_pow]

/-- The image of an element of `A` lies in the image of `Iⁿ` exactly when it lies in `Iⁿ`:
`A ⟶ Γ(Spec A, 𝒪)` is an isomorphism. -/
public theorem mem_map_ΓSpecIso_inv_iff (x : A) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv x ∈
        Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (I ^ n) ↔ x ∈ I ^ n := by
  have hbij : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv
  refine ⟨fun hx => ?_, fun hx => Ideal.mem_map_of_mem _ hx⟩
  obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective _ hbij.2).mp hx
  exact hbij.1 hxy ▸ hy

/-- The quotient `𝒪_{Spec A} / Iⁿ 𝒪_{Spec A}` of the structure sheaf of an affine spectrum. -/
public abbrev specUnitQuotient : (Spec (CommRingCat.of A)).Modules :=
  idealPowerQuotient (specIdealSheaf A I) n (Spec (CommRingCat.of A)).unitModule

/-- The quotient projection, with the structure sheaf written as the sheaf associated to `A`. -/
public abbrev specUnitQuotientπ :
    (tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A A) ⟶ specUnitQuotient A I n :=
  unitIdealPowerQuotientπ (specIdealSheaf A I) n

/-- The map `A ⟶ Γ(Spec A, 𝒪 / Iⁿ 𝒪)` of `A`-modules: the unit of the tilde-sections adjunction
followed by the quotient projection on global sections. -/
public def specUnitQuotientSections :
    ModuleCat.of A A ⟶ moduleSpecΓFunctor.obj (specUnitQuotient A I n) :=
  (tilde.adjunction (R := CommRingCat.of A)).unit.app (ModuleCat.of A A) ≫
    moduleSpecΓFunctor.map (specUnitQuotientπ A I n)

/-- The map `A ⟶ Γ(Spec A, 𝒪 / Iⁿ 𝒪)`, written out. -/
public theorem specUnitQuotientSections_def :
    specUnitQuotientSections A I n =
      (tilde.adjunction (R := CommRingCat.of A)).unit.app (ModuleCat.of A A) ≫
        moduleSpecΓFunctor.map (specUnitQuotientπ A I n) :=
  rfl

/-- The map `A ⟶ Γ(Spec A, 𝒪 / Iⁿ 𝒪)` evaluated at an element of `A`. -/
public theorem specUnitQuotientSections_apply (x : A) :
    specUnitQuotientSections A I n x =
      (specUnitQuotientπ A I n).app (⊤ : (Spec (CommRingCat.of A)).Opens)
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv x) := by
  rw [specUnitQuotientSections_def, ConcreteCategory.comp_apply]
  rfl

/-- **The map `A ⟶ Γ(Spec A, 𝒪 / Iⁿ 𝒪)` is surjective.** -/
public theorem surjective_specUnitQuotientSections :
    Function.Surjective (specUnitQuotientSections A I n) := fun y => by
  obtain ⟨z, hz⟩ := surjective_app_top_unitIdealPowerQuotientπ (specIdealSheaf A I) n y
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom z, ?_⟩
  refine Eq.trans (specUnitQuotientSections_apply A I n _) (Eq.trans (congrArg _ ?_) hz)
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id z

/-- **The kernel of `A ⟶ Γ(Spec A, 𝒪 / Iⁿ 𝒪)` is `Iⁿ`.** -/
public theorem specUnitQuotientSections_eq_zero_iff (x : A) :
    specUnitQuotientSections A I n x = 0 ↔ x ∈ I ^ n := by
  have h1 := app_top_unitIdealPowerQuotientπ_eq_zero_iff (specIdealSheaf A I) n
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv x)
  rw [specIdealSheaf_pow_ideal_top, mem_map_ΓSpecIso_inv_iff] at h1
  exact Iff.trans (Iff.of_eq
    (congrArg (fun z => z = 0) (specUnitQuotientSections_apply A I n x))) h1

/-- **`Γ(Spec A, 𝒪 / Iⁿ 𝒪)` is `A / Iⁿ`.** -/
public def specUnitQuotientSectionsIso :
    ModuleCat.of A (A ⧸ (I ^ n : Ideal A)) ≅
      moduleSpecΓFunctor.obj (specUnitQuotient A I n) :=
  LinearEquiv.toModuleIso
    ((Submodule.quotEquivOfEq (I ^ n : Ideal A)
        (LinearMap.ker (specUnitQuotientSections A I n).hom)
        (Submodule.ext fun x =>
          (specUnitQuotientSections_eq_zero_iff A I n x).symm)).trans
      (LinearMap.quotKerEquivOfSurjective _ (surjective_specUnitQuotientSections A I n)))

/-- The identification carries the quotient projection `A ⟶ A / Iⁿ` to the map on global
sections. -/
public theorem specUnitQuotientSectionsIso_hom_comp :
    ModuleCat.ofHom (Submodule.mkQ (I ^ n : Ideal A)) ≫
        (specUnitQuotientSectionsIso A I n).hom =
      specUnitQuotientSections A I n :=
  ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- The counit of the tilde-sections adjunction at `𝒪_{Spec A} / Iⁿ 𝒪_{Spec A}`, with its source
written as a single application of the associated-sheaf functor. -/
public abbrev specUnitQuotientCounit :
    (tilde.functor (CommRingCat.of A)).obj
        (moduleSpecΓFunctor.obj (specUnitQuotient A I n)) ⟶ specUnitQuotient A I n :=
  (tilde.adjunction (R := CommRingCat.of A)).counit.app (specUnitQuotient A I n)

/-- **The quotient of the structure sheaf of `Spec A` by `Iⁿ` is the sheaf associated to
`A / Iⁿ`**, compatibly with the quotient projections.

Both sides are quasi-coherent, hence sheaves associated to modules, and the module of the left
side is computed by `Stacks.Algebraization.specUnitQuotientSectionsIso`: on global sections the
quotient projection is surjective with kernel `Iⁿ`. The two projections match because the counit
of the tilde-sections adjunction is natural and its composite with the image of the unit is the
identity. -/
public theorem exists_specUnitQuotient_iso :
    ∃ e : specUnitQuotient A I n ≅ tilde (ModuleCat.of A (A ⧸ (I ^ n : Ideal A))),
      specUnitQuotientπ A I n ≫ e.hom =
        (tilde.functor (CommRingCat.of A)).map
          (ModuleCat.ofHom (Submodule.mkQ (I ^ n : Ideal A))) := by
  have hiso : IsIso (specUnitQuotientCounit A I n) :=
    (isQuasicoherent_iff_isIso_fromTildeΓ (specUnitQuotient A I n)).mp inferInstance
  have key : (tilde.functor (CommRingCat.of A)).map (specUnitQuotientSections A I n) ≫
      specUnitQuotientCounit A I n = specUnitQuotientπ A I n := by
    rw [specUnitQuotientSections_def, Functor.map_comp, Category.assoc,
      show (tilde.functor (CommRingCat.of A)).map
            (moduleSpecΓFunctor.map (specUnitQuotientπ A I n)) =
          (moduleSpecΓFunctor ⋙ tilde.functor (CommRingCat.of A)).map
            (specUnitQuotientπ A I n) from rfl,
      (tilde.adjunction (R := CommRingCat.of A)).counit.naturality, ← Category.assoc,
      (tilde.adjunction (R := CommRingCat.of A)).left_triangle_components, Category.id_comp,
      Functor.id_map]
  have hδ : specUnitQuotientSections A I n ≫ (specUnitQuotientSectionsIso A I n).inv =
      ModuleCat.ofHom (Submodule.mkQ (I ^ n : Ideal A)) := by
    rw [← specUnitQuotientSectionsIso_hom_comp, Category.assoc,
      (specUnitQuotientSectionsIso A I n).hom_inv_id, Category.comp_id]
  refine ⟨(asIso (specUnitQuotientCounit A I n)).symm ≪≫
    (tilde.functor (CommRingCat.of A)).mapIso (specUnitQuotientSectionsIso A I n).symm, ?_⟩
  change specUnitQuotientπ A I n ≫ (inv (specUnitQuotientCounit A I n) ≫
      (tilde.functor (CommRingCat.of A)).map (specUnitQuotientSectionsIso A I n).inv) = _
  have hπinv : specUnitQuotientπ A I n ≫ inv (specUnitQuotientCounit A I n) =
      (tilde.functor (CommRingCat.of A)).map (specUnitQuotientSections A I n) :=
    (IsIso.comp_inv_eq _).mpr key.symm
  rw [← Category.assoc, hπinv, ← Functor.map_comp, hδ]

end Spec

/-! ### The ideal sheaf on the complement of a closed subset -/

section Complement

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (a : Ideal A) (f : A)

/-- **The ideal sheaf `f 𝒪_U` on `U = Spec(A) ∖ V(𝔞)` is the inverse image of `f 𝒪_{Spec A}`.**
Both are `I 𝒪` for the ideal `(f)` of `A`, one formed on `U` and one formed on `Spec A` and
pulled back along the open immersion. -/
public theorem complementPrincipalIdealSheaf_eq_comap :
    complementPrincipalIdealSheaf A a f =
      (specIdealSheaf A (Ideal.span {f})).comap (complementZeroLocus A a).ι := by
  rw [complementPrincipalIdealSheaf_eq_idealSheafNearVanishing]
  exact Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_comap A (Ideal.span {f})
    (complementZeroLocus A a).ι

end Complement

end Stacks.Algebraization

end
