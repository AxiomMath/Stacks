module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.BaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.DeRhamTypeComplexHypercohomology
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.CoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DeRhamBaseChangeBasis
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DeRhamBaseChangeBijective
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Hodge cohomology commutes with extension of the base field

Let `k ⟶ K` be an extension of fields and `X` a smooth projective scheme over `k`, with base change
`X_K = X ×_{Spec k} Spec K`, `f : X ⟶ Spec k`, `f' : X_K ⟶ Spec K` and `g : Spec K ⟶ Spec k`. The
comparison map `K ⊗_k H^q(X, Ω^p_{X/k}) ⟶ H^q(X_K, Ω^p_{X_K/K})`,
`c ⊗ x ↦ c · pr^* x` (`Stacks.HodgeWeil.hodgeBaseChangeLinear`), is bijective: this is flat base
change ([Stacks, Tag 02KH]) for `H^q(X, Ω^p)`, `Ω^p_{X_K/K}` being the pullback of `Ω^p_{X/k}`
([Stacks, Tag 0FL5]), and in the library's form [Stacks, Tag 0FM0] for `Rf_*Ω^p_{X/k}` read on
cohomology over a field.

## The argument

Write `E = Rf_*Ω^p_{X/k}` and `E' = Rf'_*Ω^p_{X_K/K}`.

* The total cohomology `⨁_j H^j(Spec k, E) = ⨁_j H^j(X, Ω^p_{X/k})` is finite-dimensional: every
  piece is ([Stacks, Tag 02O6], `Ω^p_{X/k}` being coherent), and the pieces vanish outside a
  bounded interval, the cohomology of a quasi-coherent module being computed by the Čech complex of
  a finite affine cover. Choose a homogeneous basis `ξ_1, …, ξ_N` and morphisms
  `a_i : 𝒪[-n_i] ⟶ E` with value `ξ_i` at the class of `1`; then `⨁ a_i` is an isomorphism
  (`Stacks.Cohomology.OnePointDetection.isIso_biproduct_desc_of_basis`).
* Pulling back along `g` and composing with the base change isomorphism `Lg^*E ≅ E'`
  (`Stacks.HodgeWeil.formsDirectImageBaseChangeIso`) gives an isomorphism `⨁ Lg^*𝒪[-n_i] ⟶ E'`,
  so the pulled back classes form a `K`-basis of the total cohomology of `E'`.
* Those classes are the pullbacks `pr^* ξ_i`
  (`Stacks.HodgeWeil.hodgeBaseChange_hodgeLerayEquiv_evalUnit`). In degree `q`, `pr^*` therefore
  carries the `k`-basis `(ξ_i)_{n_i = q}` of `H^q(X, Ω^p_{X/k})` to a `K`-basis of
  `H^q(X_K, Ω^p_{X_K/K})`, and the comparison map carries the `K`-basis `1 ⊗ ξ_i` to it.

## Main definitions

* `Stacks.HodgeWeil.formsSinglePlus`: `Ω^p_{X/k}[0]` as a bounded below complex.
* `Stacks.HodgeWeil.hypercohomologyFormsSingleIso`: the identification of the bounded below and
  the unbounded realizations of `H^j(X, Ω^p_{X/k})`.
* `Stacks.HodgeWeil.formsLerayEquiv` and `Stacks.HodgeWeil.hodgeLerayEquiv`: the Leray
  identification `H^j(Spec k, Rf_*Ω^p_{X/k}) ≅ H^j(X, Ω^p_{X/k})` as `k`-vector spaces.

## Main results

* `Stacks.HodgeWeil.finiteDimensional_pointCohomology_derivedFormsDirectImage` and
  `Stacks.HodgeWeil.exists_subsingleton_pointCohomology_derivedFormsDirectImage`: finiteness and
  boundedness of Hodge cohomology over a field, for a proper morphism.
* `Stacks.HodgeWeil.hodgeBaseChange_hodgeLerayEquiv_evalUnit` and
  `Stacks.HodgeWeil.hodgeBaseChange_component_lof`: the base change map on the classes carried by
  morphisms `𝒪[-j] ⟶ Rf_*Ω^p_{X/k}`.
* `Stacks.HodgeWeil.exists_basis_formsDirectImageBaseChange`: base change of a decomposition of
  `Rf_*Ω^p_{X/k}` into lines gives a `K`-basis.
* `Stacks.HodgeWeil.bijective_hodgeBaseChangeLinear`: **the comparison map is bijective.**

## References

* [Stacks Project, Tag 0FM0](https://stacks.math.columbia.edu/tag/0FM0)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0FL5](https://stacks.math.columbia.edu/tag/0FL5)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
open Stacks.DeRhamDirectImage
open Stacks.Cohomology.GlobalKunneth (baseSections)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open Stacks.Cohomology.LerayCupPairing (lerayCohomologyIso restrictGlobal)
open Stacks.Cohomology.ResidueFieldPoint
open AlgebraicGeometry.DeRhamTypeComplex (hypercohomology inverseImageBaseRing
  inverseImageBaseRingHom)

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard

/-! ### Hodge cohomology over a field -/

section Field

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- `Ω^p_{X/k}` placed in degree `0`, as a bounded below complex of `f⁻¹𝒪_{Spec k}`-modules. -/
def formsSinglePlus (p : ℕ) : CochainComplex.Plus (SheafOfModules.{u} (inverseImageBaseRing f)) :=
  ⟨formsSingle f p, 0, (CochainComplex.isStrictlyGE_iff _ 0).2 fun i hi =>
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i (by omega)⟩

/-- The terms of `Ω^p_{X/k}[0]` are coherent `𝒪_X`-modules read over `f⁻¹𝒪_{Spec k}`. -/
theorem exists_isCoherent_formsSinglePlus_X [IsProper f] (p : ℕ) (q : ℤ) :
    ∃ M : X.Modules, M.IsCoherent ∧
      Nonempty ((formsSinglePlus f p).1.X q ≅ (pushforward (toInverseImageBase f)).obj M) := by
  by_cases hq : q = 0
  · subst hq
    exact ⟨Scheme.Hom.relativeDifferentialForms f (p : ℤ),
      Scheme.Hom.isCoherent_relativeDifferentialForms f p,
      ⟨HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _ ≪≫
        eqToIso (Scheme.Hom.deRhamComplex_X f p)⟩⟩
  · exact ⟨0, Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero (isZero_zero _),
      ⟨(HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ q hq).iso
        ((pushforward (toInverseImageBase f)).map_isZero (isZero_zero _))⟩⟩

/-- **`H^j(X, Ω^p_{X/k})` is finite over `Γ(Spec k, 𝒪)`** for `f` proper, in the realization by
the bounded below derived global sections of `DeRhamTypeComplex`: `Ω^p_{X/k}` is coherent. -/
theorem moduleFinite_hypercohomology_formsSinglePlus [IsProper f] (p : ℕ) (j : ℤ) :
    Module.Finite Γ(Spec (CommRingCat.of k), ⊤) (hypercohomology f (formsSinglePlus f p) j) :=
  DeRhamTypeComplex.moduleFinite_homology_derivedSections f _
    (exists_isCoherent_formsSinglePlus_X f p) j

/-- **The two realizations of `H^j(X, Ω^p_{X/k})` agree**: the bounded below derived global
sections of `DeRhamTypeComplex` and the unbounded derived global sections over `(X, f⁻¹𝒪)` at
which the Hodge groups are stated, as `Γ(Spec k, 𝒪)`-modules. -/
def hypercohomologyFormsSingleIso (p : ℕ) (j : ℤ) :
    hypercohomology f (formsSinglePlus f p) j ≅
      (restrictGlobal (inverseImageBaseProjection f)).obj
        (cohomologyModule (DerivedCategory.Q.obj (formsSingle f p)) j) :=
  (DerivedCategory.homologyFunctor _ j).mapIso
      ((ModuleCat.restrictScalars (inverseImageBaseRingHom f)).mapDerivedCategory.mapIso
        ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIsoBaseSections
          (inverseImageBase f)).app (formsSinglePlus f p))) ≪≫
    (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (ModuleCat.restrictScalars (inverseImageBaseRingHom f)) j).app _

/-- **The Leray identification over a field**, `H^j(Spec k, Rf_*Ω^p_{X/k}) ≅ H^j(X, Ω^p_{X/k})`
as `k`-vector spaces ([Stacks, Tag 0D5W]), `k` acting on the right through
`k ⟶ Γ(X, f⁻¹𝒪_{Spec k})`. -/
def formsLerayEquiv (p : ℕ) (j : ℤ) :
    (pointCohomology k j).obj (derivedFormsDirectImage f p) ≃ₗ[k]
      (restrictToField k).obj ((restrictGlobal (inverseImageBaseProjection f)).obj
        (cohomologyModule (DerivedCategory.Q.obj (formsSingle f p)) j)) :=
  ((restrictToField k).mapIso (lerayCohomologyIso (inverseImageBaseProjection f)
    (DerivedCategory.Q.obj (formsSingle f p)) j)).toLinearEquiv

/-- **Hodge cohomology over a field is finite-dimensional** for a proper morphism
([Stacks, Tag 02O6]), in the realization `H^j(Spec k, Rf_*Ω^p_{X/k})`. -/
theorem finiteDimensional_pointCohomology_derivedFormsDirectImage [IsProper f] (p : ℕ) (j : ℤ) :
    FiniteDimensional k ((pointCohomology k j).obj (derivedFormsDirectImage f p)) := by
  have h₁ := moduleFinite_hypercohomology_formsSinglePlus f p j
  have h₂ : Module.Finite Γ(Spec (CommRingCat.of k), ⊤)
      ((restrictGlobal (inverseImageBaseProjection f)).obj
        (cohomologyModule (DerivedCategory.Q.obj (formsSingle f p)) j)) :=
    Module.Finite.equiv (hypercohomologyFormsSingleIso f p j).toLinearEquiv
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2
  have h₃ : Module.Finite k ((restrictToField k).obj
      ((restrictGlobal (inverseImageBaseProjection f)).obj
        (cohomologyModule (DerivedCategory.Q.obj (formsSingle f p)) j))) :=
    Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_compHom_of_surjective
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom hsurj
      ((restrictGlobal (inverseImageBaseProjection f)).obj
        (cohomologyModule (DerivedCategory.Q.obj (formsSingle f p)) j))
  exact Module.Finite.equiv (formsLerayEquiv f p j).symm

/-- **Hodge cohomology over a field is bounded** for a proper morphism:
`H^j(Spec k, Rf_*Ω^p_{X/k}) = H^j(X, Ω^p_{X/k})` vanishes for `j < 0` and for `j` larger than
the number of opens of a finite affine cover of `X` (Čech cohomology). -/
theorem exists_subsingleton_pointCohomology_derivedFormsDirectImage [IsProper f] (p : ℕ) :
    ∃ a b : ℤ, ∀ j, j < a ∨ b < j →
      Subsingleton ((pointCohomology k j).obj (derivedFormsDirectImage f p)) := by
  have : (formsSinglePlus f p).1.IsStrictlyLE 0 :=
    (CochainComplex.isStrictlyLE_iff _ 0).2 fun i hi =>
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i (by omega)
  have : (formsSinglePlus f p).1.IsStrictlyGE 0 :=
    (CochainComplex.isStrictlyGE_iff _ 0).2 fun i hi =>
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i (by omega)
  have hK : ∀ q, ∃ M : X.Modules, M.IsQuasicoherent ∧
      Nonempty ((formsSinglePlus f p).1.X q ≅ (pushforward (toInverseImageBase f)).obj M) :=
    fun q => by
      obtain ⟨M, hM, he⟩ := exists_isCoherent_formsSinglePlus_X f p q
      exact ⟨M, _root_.isQuasicoherent_of_isCoherent M, he⟩
  obtain ⟨N, hN⟩ := DeRhamTypeComplex.exists_isZero_homology_derivedSections f
    (formsSinglePlus f p) 0 hK
  refine ⟨0, N, fun j hj => ?_⟩
  have hz : IsZero (hypercohomology f (formsSinglePlus f p) j) := by
    rcases hj with hj | hj
    · exact DeRhamTypeComplex.isZero_hypercohomology_of_lt f (formsSinglePlus f p) 0 hK j hj
    · exact hN j hj
  have h₂ : Subsingleton ((restrictGlobal (inverseImageBaseProjection f)).obj
      (cohomologyModule (DerivedCategory.Q.obj (formsSingle f p)) j)) :=
    ModuleCat.isZero_iff_subsingleton.1 (hz.of_iso (hypercohomologyFormsSingleIso f p j).symm)
  have h₃ : Subsingleton ((restrictToField k).obj
      ((restrictGlobal (inverseImageBaseProjection f)).obj
        (cohomologyModule (DerivedCategory.Q.obj (formsSingle f p)) j))) := h₂
  exact (formsLerayEquiv f p j).toEquiv.subsingleton

end Field

/-! ### The comparison map -/

section Comparison

open Stacks.WeilCohomology Stacks.WeilDeRham
open Stacks.WeilCohomology.SmoothProjectiveScheme hiding specStructure
open Stacks.Cohomology.DerivedGlobalCupProduct (unitComplex unitCycleClass evalUnit
  evalUnitEquiv)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.HomologyPullback (homologyPullback)
open AlgebraicGeometry.SheafOfModules (hodgeCohomologyComponent)

open Stacks.Cohomology.OnePointDetection
open scoped _root_.TensorProduct _root_.Stacks.TensorProduct

attribute [local instance] RestrictScalars.moduleOrig

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
  (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- A smooth projective scheme over `k` is proper over `k`. -/
private instance isProper_hom_obj : IsProper X.obj.hom := (isProjective X).isProper

/-- `H^j(Spec k, Rf_*Ω^p_{X/k}) ≅ H^j(X, Ω^p_{X/k})` for `X` smooth projective over `k`, the
`k`-vector space structure on the right being `Stacks.HodgeWeil.hodgeComponentModule`. -/
def hodgeLerayEquiv (p : ℕ) (j : ℤ) :
    (pointCohomology k j).obj (derivedFormsDirectImage X.obj.hom p) ≃ₗ[k]
      hodgeCohomologyComponent (formsAlgebras X.obj.hom) p j :=
  formsLerayEquiv X.obj.hom p j

/-- `Stacks.HodgeWeil.hodgeLerayEquiv` is the Leray identification of Tag 0D5W. -/
theorem hodgeLerayEquiv_apply (p : ℕ) (j : ℤ)
    (x : (pointCohomology k j).obj (derivedFormsDirectImage X.obj.hom p)) :
    hodgeLerayEquiv X p j x = (lerayCohomologyIso (inverseImageBaseProjection X.obj.hom)
      (DerivedCategory.Q.obj (formsSingle X.obj.hom p)) j).hom x :=
  rfl

/-- **The base change map on the value of a morphism `𝒪[-j] ⟶ Rf_*Ω^p_{X/k}`.** For
`a : 𝒪_{Spec k}[-j] ⟶ Rf_*Ω^p_{X/k}`, the base change map `pr^*` carries the value of `a` at
the class of `1` to the pullback to `Spec K` of the class of `1`, carried by `Lg^*a` and the base
change isomorphism `Lg^*Rf_*Ω^p_{X/k} ≅ Rf'_*Ω^p_{X_K/K}` of [Stacks, Tag 0FM0]. -/
theorem hodgeBaseChange_hodgeLerayEquiv_evalUnit (p : ℕ) (j : ℤ)
    (a : DerivedCategory.Q.obj (unitComplex (Spec (CommRingCat.of k)).toRingedSpace j) ⟶
      derivedFormsDirectImage X.obj.hom p) :
    haveI : IsProper X.obj.hom := (isProjective X).isProper
    hodgeBaseChange K X p j (hodgeLerayEquiv X p j
        (evalUnit (derivedFormsDirectImage X.obj.hom p) j a)) =
      hodgeLerayEquiv ((fieldBaseChange k K).obj X) p j
        (((pointCohomology K j).map ((derivedPullback (specStructure k K).toLRSHom.toShHom).map
            a ≫ (formsDirectImageBaseChangeIso (fieldBaseChangeProj X) _ X.obj.hom
              (specStructure k K) (isPullback_fieldBaseChangeProj (k' := K) X) p).hom)).hom
          (homologyPullback (specStructure k K).toLRSHom.toShHom _ j
            (unitCycleClass (Spec (CommRingCat.of k)).toRingedSpace j))) := by
  exact (homologyPullback_unitCycleClass_formsDirectImageBaseChangeIso (fieldBaseChangeProj X) _
    X.obj.hom (specStructure k K) (isPullback_fieldBaseChangeProj (k' := K) X) p j a).symm

/-- **The base change map in degree `n` on the degree-`n` component of a homogeneous class.** For
a class `y` of `H^j(Spec k, Rf_*Ω^p_{X/k})` with `j = n`, the base change map carries the
degree-`n` component of `y` to the degree-`n` component of the pullback to `Spec K` of the class
of `1`, carried by the base change of the morphism `𝒪[-j] ⟶ Rf_*Ω^p_{X/k}` with value `y`. -/
theorem hodgeBaseChange_component_lof (p : ℕ) (n j : ℤ) (hj : j = n)
    (y : (pointCohomology k j).obj (derivedFormsDirectImage X.obj.hom p)) :
    haveI : IsProper X.obj.hom := (isProjective X).isProper
    hodgeBaseChange K X p n
        (hodgeLerayEquiv X p n (DirectSum.component k ℤ (fun j => ((pointCohomology k j).obj
          (derivedFormsDirectImage X.obj.hom p) : Type u)) n
          (DirectSum.lof k ℤ (fun j => ((pointCohomology k j).obj
            (derivedFormsDirectImage X.obj.hom p) : Type u)) j y))) =
      hodgeLerayEquiv ((fieldBaseChange k K).obj X) p n
        (DirectSum.component K ℤ (fun j => ((pointCohomology K j).obj
          (derivedFormsDirectImage ((fieldBaseChange k K).obj X).obj.hom p) : Type u)) n
          (DirectSum.lof K ℤ (fun j => ((pointCohomology K j).obj
            (derivedFormsDirectImage ((fieldBaseChange k K).obj X).obj.hom p) : Type u)) j
            (((pointCohomology K j).map
              ((derivedPullback (specStructure k K).toLRSHom.toShHom).map
                ((evalUnitEquiv (derivedFormsDirectImage X.obj.hom p) j).symm y) ≫
              (formsDirectImageBaseChangeIso (fieldBaseChangeProj X) _ X.obj.hom
                (specStructure k K) (isPullback_fieldBaseChangeProj (k' := K) X) p).hom)).hom
              (homologyPullback (specStructure k K).toLRSHom.toShHom _ j
                (unitCycleClass (Spec (CommRingCat.of k)).toRingedSpace j))))) := by
  subst hj
  have h := hodgeBaseChange_hodgeLerayEquiv_evalUnit K X p j
    ((evalUnitEquiv (derivedFormsDirectImage X.obj.hom p) j).symm y)
  have hy := (evalUnitEquiv (derivedFormsDirectImage X.obj.hom p) j).apply_symm_apply y
  refine (congrArg (fun z => hodgeBaseChange K X p j (hodgeLerayEquiv X p j z))
    ((DirectSum.component.lof_self (R := k) (M := fun j => ((pointCohomology k j).obj
      (derivedFormsDirectImage X.obj.hom p) : Type u)) (i := j) (b := y)).trans
      hy.symm)).trans (h.trans ?_)
  exact congrArg (hodgeLerayEquiv ((fieldBaseChange k K).obj X) p j)
    (DirectSum.component.lof_self (R := K) (M := fun j => ((pointCohomology K j).obj
      (derivedFormsDirectImage ((fieldBaseChange k K).obj X).obj.hom p) : Type u))
      (i := j) (b := _)).symm

/-- **Base change of a decomposition of `Rf_*Ω^p_{X/k}` into lines gives a basis over `K`.** Let
`a_i : 𝒪_{Spec k}[-n_i] ⟶ Rf_*Ω^p_{X/k}` be morphisms with `⨁ a_i` an isomorphism. Then the
pullbacks to `Spec K` of the classes of `1`, carried by `Lg^*a_i` and the base change isomorphism
`Lg^*Rf_*Ω^p_{X/k} ≅ Rf'_*Ω^p_{X_K/K}` of [Stacks, Tag 0FM0], form a basis over `K` of the total
cohomology `⨁_j H^j(Spec K, Rf'_*Ω^p_{X_K/K})`. -/
theorem exists_basis_formsDirectImageBaseChange (p : ℕ) {N : ℕ} (nd : Fin N → ℤ)
    (d : ∀ i, DerivedCategory.Q.obj (unitComplex (Spec (CommRingCat.of k)).toRingedSpace (nd i)) ⟶
      derivedFormsDirectImage X.obj.hom p)
    (hd : IsIso (biproduct.desc d)) :
    haveI : IsProper X.obj.hom := (isProjective X).isProper
    ∃ B' : Module.Basis (Fin N) K (DirectSum ℤ fun j => ((pointCohomology K j).obj
        (derivedFormsDirectImage ((fieldBaseChange k K).obj X).obj.hom p) : Type u)),
      ∀ i, B' i = DirectSum.lof K ℤ (fun j => ((pointCohomology K j).obj
        (derivedFormsDirectImage ((fieldBaseChange k K).obj X).obj.hom p) : Type u)) (nd i)
        (((pointCohomology K (nd i)).map
          ((derivedPullback (specStructure k K).toLRSHom.toShHom).map (d i) ≫
            (formsDirectImageBaseChangeIso (fieldBaseChangeProj X) _ X.obj.hom
              (specStructure k K) (isPullback_fieldBaseChangeProj (k' := K) X) p).hom)).hom
          (homologyPullback (specStructure k K).toLRSHom.toShHom _ (nd i)
            (unitCycleClass (Spec (CommRingCat.of k)).toRingedSpace (nd i)))) := by
  let e := formsDirectImageBaseChangeIso (fieldBaseChangeProj X) _ X.obj.hom
    (specStructure k K) (isPullback_fieldBaseChangeProj (k' := K) X) p
  let L := derivedPullback (specStructure k K).toLRSHom.toShHom
  have hcomp : L.map (biproduct.desc d) ≫ e.hom =
      (L.mapBiproduct _).hom ≫ biproduct.desc (fun i => L.map (d i) ≫ e.hom) := by
    refine (congrArg (· ≫ e.hom) (biproduct.mapBiproduct_hom_desc L _ d).symm).trans ?_
    refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
    refine biproduct.hom_ext' _ _ fun i => ?_
    rw [biproduct.ι_desc_assoc, biproduct.ι_desc]
  have hΨ : IsIso (biproduct.desc (fun i => L.map (d i) ≫ e.hom)) := by
    have h : IsIso (L.map (biproduct.desc d) ≫ e.hom) := inferInstance
    rw [hcomp] at h
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance h
  exact exists_basis_of_isIso_biproduct_desc (fun j => pointCohomology K j) nd
    (fun i => L.obj (DerivedCategory.Q.obj
      (unitComplex (Spec (CommRingCat.of k)).toRingedSpace (nd i))))
    (derivedFormsDirectImage ((fieldBaseChange k K).obj X).obj.hom p)
    (fun i => L.map (d i) ≫ e.hom)
    (fun i => homologyPullback (specStructure k K).toLRSHom.toShHom _ (nd i)
      (unitCycleClass (Spec (CommRingCat.of k)).toRingedSpace (nd i)))
    (fun i => Module.nontrivial_of_finrank_eq_succ
      (finrank_cohomologyModule_derivedPullback_unitComplex K
        (specStructure k K).toLRSHom.toShHom (nd i)))
    (fun i j x => exists_lof_eq_smul_homologyPullback K
      (specStructure k K).toLRSHom.toShHom (nd i) j x) hΨ

/-- **[Stacks, Tag 0FM0] over a field: Hodge cohomology commutes with extension of the base
field.** For `X` smooth projective over `k` and an extension `K` of `k`, the comparison map
`K ⊗_k H^q(X, Ω^p_{X/k}) ⟶ H^q(X_K, Ω^p_{X_K/K})`, `c ⊗ x ↦ c · pr^* x`, is bijective. -/
theorem bijective_hodgeBaseChangeLinear {k : Type u} [Field k] (K : Type u) [Field K]
    [Algebra k K] (X : (SmoothProjectiveScheme k).FullSubcategory) (p : ℕ) (q : ℤ) :
    Function.Bijective (hodgeBaseChangeLinear K X p q) := by
  classical
  -- a homogeneous basis of the total cohomology over `k`
  have := finiteDimensional_pointCohomology_derivedFormsDirectImage X.obj.hom p
  obtain ⟨a, b, hz⟩ := exists_subsingleton_pointCohomology_derivedFormsDirectImage X.obj.hom p
  obtain ⟨N, nd, y, B, hB⟩ := exists_basis_lof (R := k)
    (fun j => ((pointCohomology k j).obj (derivedFormsDirectImage X.obj.hom p) : Type u)) a b hz
  -- `⨁ 𝒪[-n_i] ⟶ Rf_*Ω^p` is an isomorphism
  have hd : ∀ i, ((pointCohomology k (nd i)).map
      ((evalUnitEquiv (derivedFormsDirectImage X.obj.hom p) (nd i)).symm (y i))).hom
      (unitCycleClass (Spec (CommRingCat.of k)).toRingedSpace (nd i)) = y i := fun i =>
    (evalUnitEquiv (derivedFormsDirectImage X.obj.hom p) (nd i)).apply_symm_apply (y i)
  have hΦ := isIso_biproduct_desc_of_basis (fun j => pointCohomology k j)
    (fun φ hφ => isIso_of_forall_isIso_pointCohomology k φ hφ) nd
    (fun i => DerivedCategory.Q.obj (unitComplex (Spec (CommRingCat.of k)).toRingedSpace (nd i)))
    (derivedFormsDirectImage X.obj.hom p)
    (fun i => (evalUnitEquiv (derivedFormsDirectImage X.obj.hom p) (nd i)).symm (y i))
    (fun i => unitCycleClass (Spec (CommRingCat.of k)).toRingedSpace (nd i))
    (fun i j x => exists_lof_eq_smul_unitCycleClass k (nd i) j x) B
    (fun i => (hB i).trans (by rw [hd i]))
  -- its base change `⨁ Lg^*𝒪[-n_i] ⟶ Rf'_*Ω^p` is an isomorphism
  obtain ⟨B', hB'⟩ := exists_basis_formsDirectImageBaseChange K X p nd
    (fun i => (evalUnitEquiv (derivedFormsDirectImage X.obj.hom p) (nd i)).symm (y i)) hΦ
  -- the bases in degree `q`
  obtain ⟨bk, hbk⟩ := exists_basis_component
    (fun j => ((pointCohomology k j).obj (derivedFormsDirectImage X.obj.hom p) : Type u))
    B nd y hB q
  obtain ⟨bK, hbK⟩ := exists_basis_component
    (fun j => ((pointCohomology K j).obj
      (derivedFormsDirectImage ((fieldBaseChange k K).obj X).obj.hom p) : Type u))
    B' nd _ hB' q
  have hbase : ∀ t, hodgeBaseChange K X p q (bk.map (hodgeLerayEquiv X p q) t) =
      bK.map (hodgeLerayEquiv ((fieldBaseChange k K).obj X) p q) t := by
    intro t
    simp only [Module.Basis.map_apply]
    rw [hbk, hbK]
    exact hodgeBaseChange_component_lof K X p q (nd t) t.2 (y t)
  -- the comparison map carries a basis to a basis
  let bX := bk.map (hodgeLerayEquiv X p q)
  let bXK := bK.map (hodgeLerayEquiv ((fieldBaseChange k K).obj X) p q)
  let bT := Algebra.TensorProduct.basis K bX
  have hT : ∀ t, hodgeBaseChangeLinear K X p q (bT t) = bXK t := fun t =>
    (congrArg (hodgeBaseChangeLinear K X p q) (Algebra.TensorProduct.basis_apply bX t)).trans
      ((hodgeBaseChangeLinear_tmul K X p q 1 (bX t)).trans ((one_smul K _).trans (hbase t)))
  have heq : hodgeBaseChangeLinear K X p q = (bT.equiv bXK (Equiv.refl _)).toLinearMap :=
    bT.ext fun t => (hT t).trans
      (Module.Basis.equiv_apply (b := bT) (i := t) (b' := bXK) (e := Equiv.refl _)).symm
  rw [heq]
  exact (bT.equiv bXK (Equiv.refl _)).bijective

end Comparison

end Stacks.HodgeWeil

end
