module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.CompletedLocalCohomologyProjections
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Comparison

/-!
# The Čech model of a derived limit of the tower of local cohomologies

Let `I` and `J` be ideals of a commutative ring `A`, let `g` be a finite generating family of
`J` and let `M` be an `A`-module. The tower `n ↦ RΓ_{V(J)}(M/IⁿM)` of
`Dualizing.adicQuotientLocalCohomologySystem` is, term by term, the extended alternating Čech
complex `C^•(g; M/IⁿM)` (`Stacks.LocalCohomology.localCohomologyIsoCech`). The transition maps of
the tower of Čech complexes are surjective in every degree, and its termwise inverse limit is a
derived limit of the tower, with no Noetherian hypothesis on `A` and no finiteness hypothesis on
`M`:

`Dualizing.cechCompletedLocalCohomology A I g M = (lim_n C^•(g; M/IⁿM))` in `D(A)`,

with projections the images of the projections `lim_n C^•(g; M/IⁿM) ⟶ C^•(g; M/IⁿM)`, and with
the comparison map out of `RΓ_{V(J)}(M)` the image of the map
`C^•(g; M) ⟶ lim_n C^•(g; M/IⁿM)` assembled from the quotient maps `M ⟶ M/IⁿM`.

## Main definitions

* `Dualizing.cechAdicQuotientSystem` — the tower `n ↦ C^•(g; M/IⁿM)` of cochain complexes.
* `Dualizing.cechCompletedLocalCohomology` — its termwise inverse limit, in `D(A)`.
* `Dualizing.cechCompletedProjection` — the honest projections of that limit, read in the tower
  `n ↦ RΓ_{V(J)}(M/IⁿM)`.
* `Dualizing.cechCompletionComparison` — the comparison map
  `RΓ_{V(J)}(M) ⟶ lim_n C^•(g; M/IⁿM)`.

## Main results

* `Dualizing.surjective_cechAdicQuotientSystem_map` — the transition maps of the tower of Čech
  complexes are surjective in every degree.
* `Dualizing.isDerivedLimitWithProjections_cechCompletedProjection` — the honest projections
  present the termwise inverse limit as a derived limit of `n ↦ RΓ_{V(J)}(M/IⁿM)`.
* `Dualizing.cechCompletionComparison_comp_cechCompletedProjection` — the comparison map
  followed by the `n`-th projection is the canonical map `RΓ_{V(J)}(M) ⟶ RΓ_{V(J)}(M/IⁿM)`.

## References

* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Dualizing

section Surjectivity

variable {A : Type u} [CommRing A] {m : ℕ} (g : Fin m → A)

/-- A surjection of modules induces a surjection on each Čech localization. -/
theorem surjective_cechModMap {M N : ModuleCat.{u} A} (φ : M ⟶ N)
    (hφ : Function.Surjective φ) (s : Finset (Fin m)) :
    Function.Surjective (Stacks.LocalCohomology.cechModMap g φ s) := by
  intro y
  induction y using LocalizedModule.induction_on with
  | _ y a =>
    obtain ⟨x, hx⟩ := hφ y
    refine ⟨LocalizedModule.mk x a, ?_⟩
    rw [Stacks.LocalCohomology.cechModMap_mk g φ s x a]
    exact congrArg (fun z => LocalizedModule.mk z a) hx

/-- A surjection of modules induces a surjection on each term of the Čech complex. -/
theorem surjective_cechTermMap {M N : ModuleCat.{u} A} (φ : M ⟶ N)
    (hφ : Function.Surjective φ) (p : ℕ) :
    Function.Surjective (Stacks.LocalCohomology.cechTermMap g φ p) := by
  intro y
  induction y using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of s x =>
    obtain ⟨z, hz⟩ := surjective_cechModMap g φ hφ s.1 x
    refine ⟨DirectSum.lof A _ _ s z, ?_⟩
    rw [Stacks.LocalCohomology.cechTermMap_lof, hz]
    rfl
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb]⟩

/-- A surjection of modules induces a degreewise surjection of extended Čech complexes. -/
theorem surjective_extendedCechFunctor_map_f {M N : ModuleCat.{u} A} (φ : M ⟶ N)
    (hφ : Function.Surjective φ) (i : ℤ) :
    Function.Surjective (((Stacks.LocalCohomology.extendedCechFunctor g).map φ).f i) := by
  rw [← ModuleCat.epi_iff_surjective]
  by_cases hi : i < 0
  · have hz : IsZero ((Stacks.LocalCohomology.extendedCechComplex g N).X i) :=
      Stacks.LocalCohomology.isZero_extendedCechComplex_X g N i (Or.inl (by omega))
    exact ⟨fun a b _ => hz.eq_of_src a b⟩
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = (p : ℤ) := ⟨i.toNat, by omega⟩
    have hfp : ComplexShape.embeddingUpNat.f p = (p : ℤ) := rfl
    have hepi : Epi ((Stacks.LocalCohomology.cechComplexMap g φ).f p) :=
      (ModuleCat.epi_iff_surjective _).2 (surjective_cechTermMap g φ hφ p)
    have h1 : Epi (HomologicalComplex.extendXIso (Cech.cechComplex g M)
        ComplexShape.embeddingUpNat hfp).hom := inferInstance
    have h2 : Epi (HomologicalComplex.extendXIso (Cech.cechComplex g N)
        ComplexShape.embeddingUpNat hfp).inv := inferInstance
    rw [show ((Stacks.LocalCohomology.extendedCechFunctor g).map φ).f (p : ℤ) =
        (HomologicalComplex.extendXIso (Cech.cechComplex g M)
            ComplexShape.embeddingUpNat hfp).hom ≫
          (Stacks.LocalCohomology.cechComplexMap g φ).f p ≫
          (HomologicalComplex.extendXIso (Cech.cechComplex g N)
            ComplexShape.embeddingUpNat hfp).inv from
      HomologicalComplex.extendMap_f _ _ hfp]
    exact epi_comp' h1 (epi_comp' hepi h2)

end Surjectivity

section Tower

variable (A : Type u) [CommRing A]

/-- The tower `n ↦ C^•(g; M/IⁿM)` of extended alternating Čech complexes of the adic quotients
of `M`. -/
abbrev cechAdicQuotientSystem (I : Ideal A) {m : ℕ} (g : Fin m → A) (M : ModuleCat.{u} A) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  adicQuotientModuleSystem A I M ⋙ Stacks.LocalCohomology.extendedCechFunctor g

/-- The successor transition maps of the tower of adic quotients are surjective. -/
theorem surjective_adicQuotientModuleSystem_succ (I : Ideal A) (M : ModuleCat.{u} A) (n : ℕ) :
    Function.Surjective ((adicQuotientModuleSystem A I M).map (homOfLE (Nat.le_succ n)).op) := by
  rw [adicQuotientModuleSystem, Functor.ofOpSequence_map_homOfLE_succ]
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨Submodule.Quotient.mk y, rfl⟩

/-- The transition maps of the tower of Čech complexes of the adic quotients are surjective in
every degree. -/
theorem surjective_cechAdicQuotientSystem_map (I : Ideal A) {m : ℕ} (g : Fin m → A)
    (M : ModuleCat.{u} A) (n : ℕ) (i : ℤ) :
    Function.Surjective
      (((cechAdicQuotientSystem A I g M).map (homOfLE (Nat.le_succ n)).op).f i) :=
  surjective_extendedCechFunctor_map_f g _
    (surjective_adicQuotientModuleSystem_succ A I M n) i

/-- The identification of the `n`-th term of the tower of Čech complexes, in `D(A)`, with the
`n`-th term `RΓ_{V(J)}(M/IⁿM)` of the tower of local cohomologies. -/
def cechAdicQuotientIso (I J : Ideal A) (hJ : J.FG) {m : ℕ} (g : Fin m → A)
    (hg : Ideal.span (Set.range g) = J) (M : ModuleCat.{u} A) (n : ℕ) :
    DerivedCategory.Q.obj ((cechAdicQuotientSystem A I g M).obj (op n)) ≅
      (adicQuotientLocalCohomologySystem A I J hJ M).obj (op n) where
  hom := (Stacks.LocalCohomology.localCohomologyIsoCech g J hJ hg).inv.app
    ((adicQuotientModuleSystem A I M).obj (op n))
  inv := (Stacks.LocalCohomology.localCohomologyIsoCech g J hJ hg).hom.app
    ((adicQuotientModuleSystem A I M).obj (op n))
  hom_inv_id := (Stacks.LocalCohomology.localCohomologyIsoCech g J hJ hg).inv_hom_id_app _
  inv_hom_id := (Stacks.LocalCohomology.localCohomologyIsoCech g J hJ hg).hom_inv_id_app _

/-- The identification of the terms is compatible with the transition maps. -/
theorem cechAdicQuotientIso_naturality (I J : Ideal A) (hJ : J.FG) {m : ℕ} (g : Fin m → A)
    (hg : Ideal.span (Set.range g) = J) (M : ModuleCat.{u} A) (n : ℕ) :
    DerivedCategory.Q.map ((cechAdicQuotientSystem A I g M).map (homOfLE (Nat.le_succ n)).op) ≫
        (cechAdicQuotientIso A I J hJ g hg M n).hom =
      (cechAdicQuotientIso A I J hJ g hg M (n + 1)).hom ≫
        (adicQuotientLocalCohomologySystem A I J hJ M).map (homOfLE (Nat.le_succ n)).op :=
  (Stacks.LocalCohomology.localCohomologyIsoCech g J hJ hg).inv.naturality
    ((adicQuotientModuleSystem A I M).map (homOfLE (Nat.le_succ n)).op)

/-- **The Čech model of a derived limit of the tower `n ↦ RΓ_{V(J)}(M/IⁿM)`**: the termwise
inverse limit of the tower of Čech complexes `n ↦ C^•(g; M/IⁿM)`, regarded in `D(A)`.
Degreewise it is the complex of `I`-adic completions of the localizations of `M`. -/
abbrev cechCompletedLocalCohomology (I : Ideal A) {m : ℕ} (g : Fin m → A)
    (M : ModuleCat.{u} A) : DerivedCategory (ModuleCat.{u} A) :=
  DerivedCategory.Q.obj (limit (cechAdicQuotientSystem A I g M))

/-- The honest projections of the termwise inverse limit, read in the tower of local
cohomologies. -/
def cechCompletedProjection (I J : Ideal A) (hJ : J.FG) {m : ℕ} (g : Fin m → A)
    (hg : Ideal.span (Set.range g) = J) (M : ModuleCat.{u} A) (n : ℕ) :
    cechCompletedLocalCohomology A I g M ⟶
      (adicQuotientLocalCohomologySystem A I J hJ M).obj (op n) :=
  DerivedCategory.Q.map (limit.π (cechAdicQuotientSystem A I g M) (op n)) ≫
    (cechAdicQuotientIso A I J hJ g hg M n).hom

/-- The honest projections of the termwise inverse limit present it as a derived limit of the
tower `n ↦ RΓ_{V(J)}(M/IⁿM)`. -/
theorem isDerivedLimitWithProjections_cechCompletedProjection (I J : Ideal A) (hJ : J.FG)
    {m : ℕ} (g : Fin m → A) (hg : Ideal.span (Set.range g) = J) (M : ModuleCat.{u} A) :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (adicQuotientLocalCohomologySystem A I J hJ M)
      (cechCompletedLocalCohomology A I g M)
      (cechCompletedProjection A I J hJ g hg M) :=
  StacksDraft.DerivedInverseLimit.exists_distTriang_of_degreewise_surjective_of_iso
    (cechAdicQuotientSystem A I g M)
    (surjective_cechAdicQuotientSystem_map A I g M)
    (fun n => (adicQuotientLocalCohomologySystem A I J hJ M).obj (op n))
    (fun n => (adicQuotientLocalCohomologySystem A I J hJ M).map (homOfLE (Nat.le_succ n)).op)
    (cechAdicQuotientIso A I J hJ g hg M)
    (cechAdicQuotientIso_naturality A I J hJ g hg M)

/-- The cone of adic quotients with vertex `M`, assembled from the quotient maps `M ⟶ M/IⁿM`. -/
def adicQuotientModuleCone (I : Ideal A) (M : ModuleCat.{u} A) :
    Cone (adicQuotientModuleSystem A I M) where
  pt := M
  π :=
    { app := fun n => adicQuotientProjection A I M n.unop
      naturality := by
        intro j k φ
        have h : k.unop ≤ j.unop := leOfHom φ.unop
        have hφ : φ = (homOfLE h).op := Subsingleton.elim _ _
        subst hφ
        simpa using (adicQuotientProjection_comp_map A I M h).symm }

/-- The cone of Čech complexes assembled from the quotient maps `M ⟶ M/IⁿM`. -/
def cechAdicQuotientCone (I : Ideal A) {m : ℕ} (g : Fin m → A) (M : ModuleCat.{u} A) :
    Cone (cechAdicQuotientSystem A I g M) :=
  (Stacks.LocalCohomology.extendedCechFunctor g).mapCone (adicQuotientModuleCone A I M)

/-- The honest map of complexes `C^•(g; M) ⟶ lim_n C^•(g; M/IⁿM)` assembled from the quotient
maps `M ⟶ M/IⁿM`. -/
def cechCompletionComplexMap (I : Ideal A) {m : ℕ} (g : Fin m → A) (M : ModuleCat.{u} A) :
    (Stacks.LocalCohomology.extendedCechFunctor g).obj M ⟶
      limit (cechAdicQuotientSystem A I g M) :=
  limit.lift (cechAdicQuotientSystem A I g M) (cechAdicQuotientCone A I g M)

/-- The honest map followed by the `n`-th honest projection is the Čech complex of the quotient
map `M ⟶ M/IⁿM`. -/
theorem cechCompletionComplexMap_comp_π (I : Ideal A) {m : ℕ} (g : Fin m → A)
    (M : ModuleCat.{u} A) (n : ℕ) :
    cechCompletionComplexMap A I g M ≫ limit.π (cechAdicQuotientSystem A I g M) (op n) =
      (Stacks.LocalCohomology.extendedCechFunctor g).map (adicQuotientProjection A I M n) :=
  limit.lift_π (cechAdicQuotientCone A I g M) (op n)

/-- The Čech identification at `M`, with its target spelled as the image of the Čech complex. -/
def cechLocalCohomologyIso (J : Ideal A) (hJ : J.FG) {m : ℕ} (g : Fin m → A)
    (hg : Ideal.span (Set.range g) = J) (M : ModuleCat.{u} A) :
    (Stacks.LocalCohomology.localCohomologyDerived A J hJ).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≅
      DerivedCategory.Q.obj ((Stacks.LocalCohomology.extendedCechFunctor g).obj M) :=
  (Stacks.LocalCohomology.localCohomologyIsoCech g J hJ hg).app M

/-- **The comparison map `RΓ_{V(J)}(M) ⟶ lim_n C^•(g; M/IⁿM)`.** It is the image in `D(A)` of
the honest map of complexes assembled from the quotient maps `M ⟶ M/IⁿM`, read on
`RΓ_{V(J)}(M)` through the Čech identification. -/
def cechCompletionComparison (I J : Ideal A) (hJ : J.FG) {m : ℕ} (g : Fin m → A)
    (hg : Ideal.span (Set.range g) = J) (M : ModuleCat.{u} A) :
    (Stacks.LocalCohomology.localCohomologyDerived A J hJ).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ⟶
      cechCompletedLocalCohomology A I g M :=
  (cechLocalCohomologyIso A J hJ g hg M).hom ≫
    DerivedCategory.Q.map (cechCompletionComplexMap A I g M)

/-- **The comparison map lifts the cone of canonical maps.** Its composite with the `n`-th
honest projection is the canonical map `RΓ_{V(J)}(M) ⟶ RΓ_{V(J)}(M/IⁿM)`. -/
theorem cechCompletionComparison_comp_cechCompletedProjection (I J : Ideal A) (hJ : J.FG)
    {m : ℕ} (g : Fin m → A) (hg : Ideal.span (Set.range g) = J) (M : ModuleCat.{u} A) (n : ℕ) :
    cechCompletionComparison A I J hJ g hg M ≫ cechCompletedProjection A I J hJ g hg M n =
      localCohomologyAdicQuotientMap A I J hJ M n := by
  have hA : DerivedCategory.Q.map (cechCompletionComplexMap A I g M) ≫
      cechCompletedProjection A I J hJ g hg M n =
      DerivedCategory.Q.map ((Stacks.LocalCohomology.extendedCechFunctor g).map
          (adicQuotientProjection A I M n)) ≫
        (cechAdicQuotientIso A I J hJ g hg M n).hom := by
    rw [cechCompletedProjection, ← Category.assoc, ← Functor.map_comp,
      cechCompletionComplexMap_comp_π]
  have hB : (cechLocalCohomologyIso A J hJ g hg M).hom ≫
      DerivedCategory.Q.map ((Stacks.LocalCohomology.extendedCechFunctor g).map
        (adicQuotientProjection A I M n)) =
      localCohomologyAdicQuotientMap A I J hJ M n ≫
        (cechAdicQuotientIso A I J hJ g hg M n).inv :=
    ((Stacks.LocalCohomology.localCohomologyIsoCech g J hJ hg).hom.naturality
      (adicQuotientProjection A I M n)).symm
  rw [cechCompletionComparison, Category.assoc, hA, ← Category.assoc, hB, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end Tower

end Dualizing

end
