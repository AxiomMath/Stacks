module

public import StacksFrontier.Homology.ExtendScalars.HomologyBaseChange
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeAssemblyLinear
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeChase
public import StacksFrontier.RingTheory.Flat.DegreewiseChaseCycles

/-!
# The degree-zero step of [stacks 0E2F] (2)

With the notation of `StacksFrontier/RingTheory/Dualizing/RelativeBaseChangeAssembly.lean` --
`R → A` flat of finite presentation, `R → R'` arbitrary, `A' = A ⊗[R] R'`, `B = A ⊗[R] A`,
`B' = A' ⊗[R'] A'`, `Δ : B → A` and `Δ' : B' → A'` the two multiplication maps, `K` a relative
dualizing complex for `R → A` and `Y = (K ⊗ᴸ_A A') ⊗ᴸ_{A'} B'` -- the proof of clause (2) was left
carrying one hypothesis: a morphism `A'[0] ⟶ Y` in `D(B')` generating the morphism group freely
over `A'`.  This file produces it, from the degreewise chase and nothing else.

## The three steps

*Degree zero before base change.*  Taking `S' = R` in the base-change clause of [stacks 0E1U]
makes the left coprojection `B → B ⊗[R] R` an isomorphism, so the clause says that `E^•` *is* the
Hom complex `Hom^•_B(P^•, F^•)`
(`Dualizing.nonempty_iso_homComplexR_of_includeLeftExtend`).  Its degree-zero cohomology is then
the morphism group `Hom_{D(B)}(A[0], K ⊗ᴸ_A B)`, as `B`-modules, by [stacks 0A66] read
`B`-linearly (`Dualizing.homComplexRHomologyLinearEquiv`), and that group is `A` by the diagonal
condition of [stacks 0E2C] (`Dualizing.nonempty_linearEquiv_hom_diagonalDerivedExtension`), which
is `A`-linear and hence `B`-linear along `Δ`.  So `H^0(E^•) = A`
(`Dualizing.nonempty_homology_iso_diagonalModule`).

*Base change of degree-zero cohomology.*  Termwise extension of scalars is a left adjoint, so it
commutes with the cokernel presentation of cohomology; the one thing it does not do for free is
base change the cycles, and that is exactly the degree-zero output of the chase
(`StacksDraft.HomologyBaseChange.nonempty_extendScalars_homology_iso_of_isIso_cyclesComparison`,
whose hypothesis is that `StacksDraft.HomologyBaseChange.cyclesComparison` is invertible).
Reading it at the map of diagonals instead of the left coprojection is the relabelling along
`Dualizing.diagonalBaseChangeEquiv`
(`Dualizing.nonempty_homology_iso_extendScalars_diagonalBaseChange`).  Together with
`Dualizing.diagonalBaseChangeExtendScalarsIso`, which evaluates `B' ⊗_B A = A'`, this gives
`H^0(E^• ⊗_B B') = A'` as `B'`-modules
(`Dualizing.nonempty_homology_diagonalBaseChangeExtend_iso_restrictedUnit`).

*From `B'`-linear to `A'`-linear.*  The assembly is now available `B'`-linearly
(`Dualizing.nonempty_homologyLinearEquiv_restrictedUnitSingle`), so the morphisms
`A'[0] ⟶ Y` are `A'` as `B'`-modules.  The `A'`-linearity costs nothing: `Δ'` is surjective, so
an `A'`-module structure restricting to a given `B'`-module structure is unique and a `B'`-linear
map between two modules carrying one is `A'`-linear (`Dualizing.linearEquivOfSurjective`).  The
free generator is then the image of `1` (`Dualizing.bijective_smul_symm_one`).

## Main results

* `Dualizing.nonempty_iso_homComplexR_of_includeLeftExtend` -- the base-change clause of
  [stacks 0E1U] at `S' = R`: `E^• = Hom^•_B(P^•, F^•)`.
* `Dualizing.nonempty_homology_iso_diagonalModule` -- `H^0(E^•) = A`, as `B`-modules.
* `Dualizing.nonempty_homology_iso_extendScalars_diagonalBaseChange` and
  `Dualizing.nonempty_homology_diagonalBaseChangeExtend_iso_restrictedUnit` --
  `H^0(E^• ⊗_B B') = A'`, as `B'`-modules.
* `Dualizing.nonempty_linearEquiv_hom_diagonalBaseChangeTarget` and
  `Dualizing.exists_bijective_smul_hom_diagonalBaseChangeTarget` -- **the degree-zero hypothesis of
  clause (2), discharged**: the morphisms `A'[0] ⟶ Y` are `A'` as an `A'`-module, and the image of
  `1` generates them freely.
* `Dualizing.isRelativeDualizingComplex_baseChange_of_residueFieldVanishing` -- **clause (2) with
  the degree-zero generator gone**: it is now
  `Dualizing.isRelativeDualizingComplex_baseChange_of_residueFieldHomology` carrying the
  residue-field vanishing alone.

## Implementation notes

`Dualizing.linearEquivRestrictOfSmulEq` and `Dualizing.linearEquivOfSurjective` are the two
directions of the passage between `B`-linearity and `A`-linearity along a ring map `φ : B → A`:
restriction needs nothing, and the other direction needs `φ` surjective.  Both consume the
compatibility of the two actions, which on the morphism groups out of `A'[0]` is
`Dualizing.smulRestrictedUnitSingle_comp_eq_smul`.

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0E1U](https://stacks.math.columbia.edu/tag/0E1U)
* [Stacks Project, Tag 0A66](https://stacks.math.columbia.edu/tag/0A66)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Dualizing.smulHomRestrictedUnitSingle

universe u

namespace Dualizing

noncomputable section

section Collapse

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- **The base-change clause of [stacks 0E1U] at the identity base change.**  Taking `S' = R` in
the base-change clause, the left coprojection `B → B ⊗[R] R` is an isomorphism and the clause says
that `E^•` is itself the Hom complex `Hom^•_B(P^•, F^•)`.

The relabelling along `Algebra.TensorProduct.rid` is
`StacksDraft.ScalarTransport.nonempty_extendScalars_iso_homComplexR_comp`, and what remains is that
extension of scalars along the identity is the identity functor. -/
theorem nonempty_iso_homComplexR_of_includeLeftExtend
    (E P F : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ)
    (hE : Nonempty ((diagonalIncludeLeftExtend R A R).obj E ≅
      CochainComplex.HomComplexR ((A ⊗[R] A) ⊗[R] R)
        ((diagonalIncludeLeftExtend R A R).obj P)
        ((diagonalIncludeLeftExtend R A R).obj F))) :
    Nonempty (E ≅ CochainComplex.HomComplexR (A ⊗[R] A) P F) := by
  let ε : ((A ⊗[R] A) ⊗[R] R) ≃+* (A ⊗[R] A) :=
    (Algebra.TensorProduct.rid R R (A ⊗[R] A)).toRingEquiv
  let φ : (A ⊗[R] A) →+* ((A ⊗[R] A) ⊗[R] R) := Algebra.TensorProduct.includeLeftRingHom
  have hid : ε.toRingHom.comp φ = RingHom.id (A ⊗[R] A) := by
    refine RingHom.ext fun b => ?_
    show (Algebra.TensorProduct.rid R R (A ⊗[R] A)) (b ⊗ₜ[R] (1 : R)) = b
    rw [Algebra.TensorProduct.rid_tmul, one_smul]
  have h := StacksDraft.ScalarTransport.nonempty_extendScalars_iso_homComplexR_comp ε φ E P F hE
  rw [hid] at h
  obtain ⟨e⟩ := h
  let idIso : ModuleCat.extendScalars.{u, u, u} (RingHom.id (A ⊗[R] A)) ≅
      𝟭 (ModuleCat.{u} (A ⊗[R] A)) :=
    ModuleCat.extendScalarsIsoRestrictScalarsSymm (RingEquiv.refl (A ⊗[R] A)) ≪≫
      ModuleCat.restrictScalarsId' _ rfl
  let Θ : (ModuleCat.extendScalars.{u, u, u}
        (RingHom.id (A ⊗[R] A))).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      𝟭 (CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) :=
    NatIso.mapHomologicalComplex idIso (ComplexShape.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)
  exact ⟨(Θ.app E).symm ≪≫ e ≪≫
    StacksDraft.ScalarTransport.homComplexRCongr (A ⊗[R] A) (Θ.app P) (Θ.app F)⟩

end Collapse

section Restriction

/-- **A linear equivalence over `A` is one over `B` along a ring map `φ : B → A`.**  The two
`B`-actions are the restrictions of the two `A`-actions, so nothing has to be checked.

The converse passage, from `B`-linear to `A`-linear, needs `φ` surjective and is
`Dualizing.linearEquivOfSurjective`. -/
def linearEquivRestrictOfSmulEq {B A : Type u} [CommRing B] [CommRing A] (φ : B →+* A)
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N]
    [Module A M] [Module A N]
    (hM : ∀ (b : B) (m : M), φ b • m = b • m) (hN : ∀ (b : B) (x : N), φ b • x = b • x)
    (e : M ≃ₗ[A] N) : M ≃ₗ[B] N :=
  { toFun := e
    map_add' := e.map_add
    map_smul' := fun b m => by
      change e (b • m) = b • e m
      rw [← hM b m, ← hN b (e m)]
      exact e.map_smul (φ b) m
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }

end Restriction

section DegreeZero

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
  [Algebra.FinitePresentation R A] (K : DerivedCategory (ModuleCat.{u} A))

/-- **The degree-zero cohomology of `E^•` is the diagonal.**  If `E^•` is the Hom complex
`Hom^•_B(P^•, F^•)` of a bounded above complex `P^•` of projective `B`-modules representing the
diagonal `A[0]` and a complex `F^•` representing `K ⊗ᴸ_A B`, and `K` is a relative dualizing
complex for `R → A`, then `H^0(E^•)` is the diagonal `A`, as `B`-modules.

The three steps are [stacks 0A66] read `B`-linearly
(`Dualizing.homComplexRHomologyLinearEquiv`), the transport of the two representatives, and the
degree-zero diagonal condition of [stacks 0E2C]
(`Dualizing.nonempty_linearEquiv_hom_diagonalDerivedExtension`), which is `A`-linear and therefore
`B`-linear along the multiplication map. -/
theorem nonempty_homology_iso_diagonalModule (hK : IsRelativeDualizingComplex R A K)
    (P : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (dP : ℤ) [P.IsStrictlyLE dP]
    [∀ i : ℤ, Projective (P.X i)]
    (eP : DerivedCategory.Q.obj P ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj (diagonalModule R A))
    (F : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ)
    (eF : DerivedCategory.Q.obj F ≅ (diagonalDerivedExtension R A).obj K)
    (E : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ)
    (hE : Nonempty (E ≅ CochainComplex.HomComplexR (A ⊗[R] A) P F)) :
    Nonempty ((E.homology 0 : ModuleCat.{u} (A ⊗[R] A)) ≅ diagonalModule R A) := by
  obtain ⟨e⟩ := hE
  obtain ⟨eA⟩ := nonempty_linearEquiv_hom_diagonalDerivedExtension R A K hK
  let Δ : (A ⊗[R] A) →+* A :=
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom
  let : Module (A ⊗[R] A) A := (diagonalModule R A).isModule
  let eB : (restrictedUnitSingle Δ 0 ⟶
        (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} (A ⊗[R] A))) (0 : ℤ)).obj
          ((diagonalDerivedExtension R A).obj K)) ≃ₗ[A ⊗[R] A]
      (diagonalModule R A : Type u) :=
    linearEquivRestrictOfSmulEq Δ
      (fun b g => smulRestrictedUnitSingle_comp_eq_smul Δ b 0 g) (fun _ _ => rfl) eA
  let eHom := (Linear.homCongr (A ⊗[R] A) eP
    ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} (A ⊗[R] A))) (0 : ℤ)).mapIso eF))
  exact ⟨((HomologicalComplex.homologyFunctor (ModuleCat.{u} (A ⊗[R] A))
      (ComplexShape.up ℤ) 0).mapIso e) ≪≫
    (((homComplexRHomologyLinearEquiv P F dP 0).trans (eHom.trans eB)).toModuleIso)⟩

end DegreeZero

section Diagonals

variable (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The degree-zero cohomology of the base change, read at the map of diagonals.**  The
base-change identification of the degree-zero cohomology of `E^•` is stated at the left
coprojection `B → B ⊗[R] R'`, which is where the degreewise chase lives; the assembly reads it at
the map of diagonals `B → B'`.  The two differ by the ring isomorphism
`Dualizing.diagonalBaseChangeEquiv`, and relabelling along a ring isomorphism neither changes a
module nor interferes with cohomology.

The two transports are
`StacksDraft.ScalarTransport.extendScalarsCompRelabelComplexIso` on the complex and
`StacksDraft.ScalarTransport.extendScalarsCompRelabelIso` on the module, with
`CochainComplex.Tor.ChangeOfRingsSpectralSequence.restrictHomologyIso` moving the relabelling
across the cohomology functor. -/
theorem nonempty_homology_iso_extendScalars_diagonalBaseChange
    (E : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ)
    (h : Nonempty ((ModuleCat.extendScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom :
          (A ⊗[R] A) →+* (A ⊗[R] A) ⊗[R] R')).obj (E.homology 0) ≅
      ((diagonalIncludeLeftExtend R A R').obj E).homology 0)) :
    Nonempty ((((diagonalBaseChangeExtend R A R').obj E).homology 0) ≅
      (ModuleCat.extendScalars.{u, u, u} (diagonalBaseChangeMap R A R')).obj
        (E.homology 0)) := by
  obtain ⟨e⟩ := h
  let ε := (diagonalBaseChangeEquiv R A R').toRingEquiv
  let φ : (A ⊗[R] A) →+* ((A ⊗[R] A) ⊗[R] R') := Algebra.TensorProduct.includeLeftRingHom
  exact ⟨HomologicalComplex.homologyMapIso
      ((StacksDraft.ScalarTransport.extendScalarsCompRelabelComplexIso ε φ).app E) 0 ≪≫
    CochainComplex.Tor.ChangeOfRingsSpectralSequence.restrictHomologyIso.{u, u}
      ε.symm.toRingHom ((diagonalIncludeLeftExtend R A R').obj E) 0 ≪≫
    (StacksDraft.ScalarTransport.relabel ε).mapIso e.symm ≪≫
    ((StacksDraft.ScalarTransport.extendScalarsCompRelabelIso ε φ).app (E.homology 0)).symm⟩

variable [Module.Flat R A] [Algebra.FinitePresentation R A]
  (K : DerivedCategory (ModuleCat.{u} A))

/-- **The degree-zero cohomology of `E^• ⊗_B B'` is `A'`.**  Under the hypotheses of the degreewise
chase, and with `E^•` the Hom complex of the two representatives of [stacks 0E1U], the degree-zero
cohomology of the base change `E^• ⊗_B B'` is `A'`, viewed as a `B'`-module through the
multiplication map `Δ'`.

The three steps are: the base change of the degree-zero cohomology
(`StacksDraft.HomologyBaseChange.nonempty_extendScalars_homology_iso_of_isIso_cyclesComparison`,
whose hypothesis `hcyc` is the degree-zero output of the chase), read at the map of diagonals
(`Dualizing.nonempty_homology_iso_extendScalars_diagonalBaseChange`); the identification
`H^0(E^•) = A` of `Dualizing.nonempty_homology_iso_diagonalModule`; and the evaluation
`B' ⊗_B A = A'` of `Dualizing.diagonalBaseChangeExtendScalarsIso`. -/
theorem nonempty_homology_diagonalBaseChangeExtend_iso_restrictedUnit
    (hK : IsRelativeDualizingComplex R A K)
    (P : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (dP : ℤ) [P.IsStrictlyLE dP]
    [∀ i : ℤ, Projective (P.X i)]
    (eP : DerivedCategory.Q.obj P ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj (diagonalModule R A))
    (F : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ)
    (eF : DerivedCategory.Q.obj F ≅ (diagonalDerivedExtension R A).obj K)
    (E : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ)
    (hER : Nonempty ((diagonalIncludeLeftExtend R A R).obj E ≅
      CochainComplex.HomComplexR ((A ⊗[R] A) ⊗[R] R)
        ((diagonalIncludeLeftExtend R A R).obj P)
        ((diagonalIncludeLeftExtend R A R).obj F)))
    (hcyc : IsIso (StacksDraft.HomologyBaseChange.cyclesComparison
      (Algebra.TensorProduct.includeLeftRingHom :
        (A ⊗[R] A) →+* (A ⊗[R] A) ⊗[R] R') E 0)) :
    Nonempty ((((diagonalBaseChangeExtend R A R').obj E).homology 0) ≅
      (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.lmul' R' :
            (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom).obj
        (ModuleCat.of (A ⊗[R] R') (A ⊗[R] R'))) := by
  obtain ⟨e₀⟩ := nonempty_homology_iso_extendScalars_diagonalBaseChange R A R' E
    (StacksDraft.HomologyBaseChange.nonempty_extendScalars_homology_iso_of_isIso_cyclesComparison
      _ E 0 hcyc)
  obtain ⟨eH⟩ := nonempty_homology_iso_diagonalModule R A K hK P dP eP F eF E
    (nonempty_iso_homComplexR_of_includeLeftExtend R A E P F hER)
  exact ⟨e₀ ≪≫ (ModuleCat.extendScalars.{u, u, u} (diagonalBaseChangeMap R A R')).mapIso eH ≪≫
    diagonalBaseChangeExtendScalarsIso R A R'⟩

/-- **The degree-zero hypothesis of [stacks 0E2F] (2), `A'`-linearly.**  Under the hypotheses of
the degreewise chase, the morphisms `A'[0] ⟶ Y` in `D(B')` are `A'` itself as an `A'`-module.

This is the `A'`-linear statement `Dualizing.isRelativeDualizingComplex_baseChange_of_hom` reads in
degree zero.  It is obtained `B'`-linearly -- the assembly
`Dualizing.nonempty_homologyLinearEquiv_restrictedUnitSingle` on one side and the chase's
degree-zero output `Dualizing.nonempty_homology_diagonalBaseChangeExtend_iso_restrictedUnit` on the
other -- and then read `A'`-linearly, which costs nothing because `Δ' : B' → A'` is surjective
(`Dualizing.linearEquivOfSurjective`). -/
theorem nonempty_linearEquiv_hom_diagonalBaseChangeTarget
    (hK : IsRelativeDualizingComplex R A K)
    (P : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (dP : ℤ) [P.IsStrictlyLE dP]
    [∀ i : ℤ, Projective (P.X i)] (hP : CochainComplex.KFlat.{u, u} P)
    (eP : DerivedCategory.Q.obj P ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj (diagonalModule R A))
    (F : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (d : ℤ) [F.IsStrictlyLE d]
    (hflat : ∀ i : ℤ, Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] A))).obj (F.X i)))
    (eF : DerivedCategory.Q.obj F ≅ (diagonalDerivedExtension R A).obj K)
    (E : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ)
    (hER : Nonempty ((diagonalIncludeLeftExtend R A R).obj E ≅
      CochainComplex.HomComplexR ((A ⊗[R] A) ⊗[R] R)
        ((diagonalIncludeLeftExtend R A R).obj P)
        ((diagonalIncludeLeftExtend R A R).obj F)))
    (hER' : Nonempty ((diagonalIncludeLeftExtend R A R').obj E ≅
      CochainComplex.HomComplexR ((A ⊗[R] A) ⊗[R] R')
        ((diagonalIncludeLeftExtend R A R').obj P)
        ((diagonalIncludeLeftExtend R A R').obj F)))
    (hcyc : IsIso (StacksDraft.HomologyBaseChange.cyclesComparison
      (Algebra.TensorProduct.includeLeftRingHom :
        (A ⊗[R] A) →+* (A ⊗[R] A) ⊗[R] R') E 0)) :
    Nonempty ((restrictedUnitSingle
          (Algebra.TensorProduct.lmul' R' :
            (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom 0 ⟶
        (CategoryTheory.shiftFunctor
            (DerivedCategory (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')))) (0 : ℤ)).obj
          (diagonalBaseChangeTarget R A R' K)) ≃ₗ[A ⊗[R] R'] (A ⊗[R] R')) := by
  obtain ⟨eAs⟩ := nonempty_homologyLinearEquiv_restrictedUnitSingle R A R' K P dP hP eP F d hflat
    eF E (nonempty_diagonalBaseChangeExtend_iso_homComplexR R A R' E P F hER') 0
  obtain ⟨eZ⟩ := nonempty_homology_diagonalBaseChangeExtend_iso_restrictedUnit R A R' K hK P dP eP
    F eF E hER hcyc
  let d' : ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) →+* (A ⊗[R] R') :=
    (Algebra.TensorProduct.lmul' R' :
      (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom
  let : Module ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) (A ⊗[R] R') :=
    ((ModuleCat.restrictScalars.{u} d').obj
      (ModuleCat.of (A ⊗[R] R') (A ⊗[R] R'))).isModule
  have hsurj : Function.Surjective d' := fun a =>
    ⟨a ⊗ₜ[R'] (1 : A ⊗[R] R'), by
      show (Algebra.TensorProduct.lmul' R' :
        (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')) (a ⊗ₜ[R'] (1 : A ⊗[R] R')) = a
      rw [Algebra.TensorProduct.lmul'_apply_tmul, mul_one]⟩
  let eB : (restrictedUnitSingle d' 0 ⟶
        (CategoryTheory.shiftFunctor
            (DerivedCategory (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')))) (0 : ℤ)).obj
          (diagonalBaseChangeTarget R A R' K)) ≃ₗ[(A ⊗[R] R') ⊗[R'] (A ⊗[R] R')]
      (A ⊗[R] R') :=
    eAs.symm.trans eZ.toLinearEquiv
  exact ⟨linearEquivOfSurjective d' hsurj
    (fun b m => smulRestrictedUnitSingle_comp_eq_smul d' b 0 m) (fun _ _ => rfl) eB⟩

/-- **The degree-zero generator of [stacks 0E2F] (2).**  The hypothesis `h0` of
`Dualizing.isRelativeDualizingComplex_baseChange_of_residueFieldHomology`, discharged: a morphism
`A'[0] ⟶ Y` in `D(B')` generating the morphism group freely over `A'` is the image of `1` under
`Dualizing.nonempty_linearEquiv_hom_diagonalBaseChangeTarget`. -/
theorem exists_bijective_smul_hom_diagonalBaseChangeTarget
    (hK : IsRelativeDualizingComplex R A K)
    (P : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (dP : ℤ) [P.IsStrictlyLE dP]
    [∀ i : ℤ, Projective (P.X i)] (hP : CochainComplex.KFlat.{u, u} P)
    (eP : DerivedCategory.Q.obj P ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj (diagonalModule R A))
    (F : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (d : ℤ) [F.IsStrictlyLE d]
    (hflat : ∀ i : ℤ, Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] A))).obj (F.X i)))
    (eF : DerivedCategory.Q.obj F ≅ (diagonalDerivedExtension R A).obj K)
    (E : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ)
    (hER : Nonempty ((diagonalIncludeLeftExtend R A R).obj E ≅
      CochainComplex.HomComplexR ((A ⊗[R] A) ⊗[R] R)
        ((diagonalIncludeLeftExtend R A R).obj P)
        ((diagonalIncludeLeftExtend R A R).obj F)))
    (hER' : Nonempty ((diagonalIncludeLeftExtend R A R').obj E ≅
      CochainComplex.HomComplexR ((A ⊗[R] A) ⊗[R] R')
        ((diagonalIncludeLeftExtend R A R').obj P)
        ((diagonalIncludeLeftExtend R A R').obj F)))
    (hcyc : IsIso (StacksDraft.HomologyBaseChange.cyclesComparison
      (Algebra.TensorProduct.includeLeftRingHom :
        (A ⊗[R] A) →+* (A ⊗[R] A) ⊗[R] R') E 0)) :
    ∃ g : restrictedUnitSingle
          (Algebra.TensorProduct.lmul' R' :
            (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom 0 ⟶
        (CategoryTheory.shiftFunctor
            (DerivedCategory (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')))) (0 : ℤ)).obj
          (diagonalBaseChangeTarget R A R' K),
      Function.Bijective fun a : A ⊗[R] R' =>
        smulRestrictedUnitSingle
          (Algebra.TensorProduct.lmul' R' :
            (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom a 0 ≫ g := by
  obtain ⟨e⟩ := nonempty_linearEquiv_hom_diagonalBaseChangeTarget R A R' K hK P dP hP eP F d hflat
    eF E hER hER' hcyc
  exact ⟨e.symm 1, bijective_smul_symm_one e⟩

/-- **Stacks Project, Tag 0E2F (2), from the Noetherian case at the residue fields.**  This is
`Dualizing.isRelativeDualizingComplex_baseChange_of_residueFieldHomology` with its hypothesis `h0`
discharged: the residue-field vanishing is now the only thing the clause carries.

The degree-zero generator comes from the same residue-field vanishing, one degree up.  At degree
one it makes the cokernel of `E^0 → E^1` flat over `R`, hence the degree-zero cycles of `E^•` base
change (`StacksDraft.DegreewiseChase.isIso_cyclesComparison_includeLeft`), hence so does
`H^0(E^•) = A`, and `Dualizing.exists_bijective_smul_hom_diagonalBaseChangeTarget` reads that on
the morphism groups `A'`-linearly. -/
theorem isRelativeDualizingComplex_baseChange_of_residueFieldVanishing
    [IsNoetherianRing (A ⊗[R] A)]
    (hK : IsRelativeDualizingComplex R A K)
    (P : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (dP : ℤ) [P.IsStrictlyLE dP]
    [∀ i : ℤ, Projective (P.X i)] (hP : CochainComplex.KFlat.{u, u} P)
    (eP : DerivedCategory.Q.obj P ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj (diagonalModule R A))
    (F : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (d : ℤ) [F.IsStrictlyLE d]
    (hflat : ∀ i : ℤ, Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] A))).obj (F.X i)))
    (eF : DerivedCategory.Q.obj F ≅ (diagonalDerivedExtension R A).obj K)
    (E : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ)
    (hE : ∀ (S' : Type u) [CommRing S'] [Algebra R S'],
      Nonempty ((diagonalIncludeLeftExtend R A S').obj E ≅
        CochainComplex.HomComplexR ((A ⊗[R] A) ⊗[R] S')
          ((diagonalIncludeLeftExtend R A S').obj P)
          ((diagonalIncludeLeftExtend R A S').obj F)))
    (hEflat : ∀ i : ℤ, Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] A))).obj (E.X i)))
    (hEfin : ∀ i : ℤ, Module.Finite (A ⊗[R] A) (E.X i))
    (hres : ∀ (p : Ideal R) [p.IsPrime] (j : ℤ), j ≠ 0 → Limits.IsZero
      ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} (A ⊗[R] StacksDraft.DegreewiseChase.ResidueFieldAt R p)) j).obj
        ((derivedHom.{u, u}
            (Algebra.TensorProduct.lmul'
              (StacksDraft.DegreewiseChase.ResidueFieldAt R p) :
              (A ⊗[R] StacksDraft.DegreewiseChase.ResidueFieldAt R p)
                  ⊗[StacksDraft.DegreewiseChase.ResidueFieldAt R p]
                (A ⊗[R] StacksDraft.DegreewiseChase.ResidueFieldAt R p)
                →ₐ[StacksDraft.DegreewiseChase.ResidueFieldAt R p]
                (A ⊗[R] StacksDraft.DegreewiseChase.ResidueFieldAt R p)).toRingHom).obj
          (diagonalBaseChangeTarget R A
            (StacksDraft.DegreewiseChase.ResidueFieldAt R p) K)))) :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    letI : Algebra.FinitePresentation R' (A ⊗[R] R') :=
      Algebra.FinitePresentation.equiv (baseChangeComm R A R')
    IsRelativeDualizingComplex R' (A ⊗[R] R')
      ((totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K) := by
  have := hEfin (0 + 1)
  refine isRelativeDualizingComplex_baseChange_of_residueFieldHomology R A R' K P dP hP eP F d
    hflat eF E hE hEflat hEfin hK hres
    (exists_bijective_smul_hom_diagonalBaseChangeTarget R A R' K hK P dP hP eP F d hflat eF E
      (hE R) (hE R')
      (StacksDraft.DegreewiseChase.isIso_cyclesComparison_includeLeft R (A ⊗[R] A) R' E 0 hEflat
        (fun p _ => ?_)))
  have h := exact_rTensor_residueField_of_isZero_homology R A K P dP hP eP F d hflat eF E hE p 1
    (hres p 1 one_ne_zero)
  rw [show (1 : ℤ) - 1 = 0 from by ring, show (1 : ℤ) + 1 = 2 from by ring] at h
  rw [show (0 : ℤ) + 1 = 1 from by ring, show (0 : ℤ) + 2 = 2 from by ring]
  exact h

end Diagonals

end

end Dualizing

end
