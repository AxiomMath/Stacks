module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DeRhamBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DeRhamBaseChangeBasis
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DeRhamBaseChangeLinear
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# De Rham cohomology commutes with extension of the base field

Let `k ⟶ K` be an extension of fields and `X` a smooth projective scheme over `k`, with base change
`X_K = X ×_{Spec k} Spec K`. This file proves that the comparison map

`K ⊗_k H^n_{dR}(X/k) ⟶ H^n_{dR}(X_K/K)`, `c ⊗ x ↦ c · pr^* x`

(`Stacks.WeilDeRham.deRhamBaseChangeLinear`) is bijective, in every degree and without any
assumption on the characteristic. This is [Stacks, Tag 0FM0] read on cohomology over a field, for
the pullback map of [Stacks, Tag 0FL6], the input of Lemma 0FVT for de Rham cohomology.

## The argument

Write `f : X ⟶ Spec k`, `f' : X_K ⟶ Spec K`, `g : Spec K ⟶ Spec k`, and `E = Rf_*Ω^•_{X/k}`,
`E' = Rf'_*Ω^•_{X_K/K}`.

* The total cohomology `⨁_j H^j(Spec k, E) = ⨁_j H^j_{dR}(X/k)` is finite-dimensional: every
  piece is (Tag 0FLZ) and the pieces vanish outside a bounded interval, the de Rham complex of
  `X` being perfect over `k` (Tag 0FM0). Choose a homogeneous basis `ξ_1, …, ξ_N`, `ξ_i` in degree
  `n_i`, and morphisms `a_i : 𝒪[-n_i] ⟶ E` with value `ξ_i` at the class of `1`.
* On `Spec k` the cohomology of derived global sections detects isomorphisms, so
  `⨁ a_i : ⨁ 𝒪[-n_i] ⟶ E` is an isomorphism
  (`Stacks.Cohomology.OnePointDetection.isIso_biproduct_desc_of_basis`).
* Pulling back along `g` and composing with the base change isomorphism `Lg^*E ≅ E'` of
  Tag 0FM0 gives an isomorphism `⨁ Lg^*𝒪[-n_i] ⟶ E'`; on `Spec K` the pulled back classes of `1`
  span the total cohomology of the source, so their images form a `K`-basis of the total
  cohomology of `E'` (`Stacks.WeilDeRham.exists_basis_of_isIso_biproduct_desc`).
* Those images are the pullbacks `pr^* ξ_i`
  (`Stacks.WeilDeRham.homologyPullback_unitCycleClass_deRhamUnboundedBaseChange`). In degree `n`,
  `pr^*` therefore carries the `k`-basis `(ξ_i)_{n_i = n}` of `H^n_{dR}(X/k)` to a `K`-basis of
  `H^n_{dR}(X_K/K)`, and the comparison map carries the `K`-basis `1 ⊗ ξ_i` of
  `K ⊗_k H^n_{dR}(X/k)` to it.

## Main results

* `Stacks.WeilDeRham.exists_lof_eq_smul_unitCycleClass`: on the spectrum of a field the total
  cohomology of `𝒪[-n]` is the line through the class of `1`.
* `Stacks.WeilDeRham.finiteDimensional_pointCohomology_deRhamDirectImage` and
  `Stacks.WeilDeRham.exists_subsingleton_pointCohomology_deRhamDirectImage`: finiteness and
  boundedness of de Rham cohomology over a field.
* `Stacks.WeilDeRham.exists_basis_baseChange`: the base change of a decomposition of
  `Rf_*Ω^•_{X/k}` into lines gives a basis of the total cohomology over `K`.
* `Stacks.WeilDeRham.bijective_deRhamBaseChangeLinear_of_basis`: the comparison map is bijective
  once `pr^*` carries a basis to a basis.
* `Stacks.WeilDeRham.bijective_deRhamBaseChangeLinear`: **the comparison map is bijective.**

## References

* [Stacks Project, Tag 0FM0](https://stacks.math.columbia.edu/tag/0FM0)
* [Stacks Project, Tag 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
* [Stacks Project, Tag 0FLZ](https://stacks.math.columbia.edu/tag/0FLZ)
* [Stacks Project, Tag 0FMP](https://stacks.math.columbia.edu/tag/0FMP)
* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedGlobalCupProduct Stacks.Cohomology.GlobalKunneth
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.LerayCupPairing
open Stacks.Cohomology.HomologyPullback Stacks.Cohomology.ResidueFieldPoint
open Stacks.Cohomology.OnePointDetection
open Stacks.DeRhamDirectImage AlgebraicGeometry.DeRhamCohomologyDirectImage
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open scoped Stacks.StandardDerivedModel TensorProduct

universe u

namespace Stacks.WeilDeRham

/-! ### The structure sheaf on the spectrum of a field -/

/-- **On the spectrum of a field the total cohomology of `𝒪[-n]` is the line through the class of
`1`**: `H^j(Spec K, 𝒪[-n])` vanishes for `j ≠ n`, and `H^n(Spec K, 𝒪[-n]) = K` is spanned by the
class of `1`, which is nonzero. -/
theorem exists_lof_eq_smul_unitCycleClass (K : Type u) [Field K] (n j : ℤ)
    (x : (restrictToField K).obj (cohomologyModule
      (DerivedCategory.Q.obj (unitComplex (Spec (CommRingCat.of K)).toRingedSpace n)) j)) :
    ∃ c : K, DirectSum.lof K ℤ (fun k => (restrictToField K).obj (cohomologyModule
        (DerivedCategory.Q.obj (unitComplex (Spec (CommRingCat.of K)).toRingedSpace n)) k)) j x =
      c • DirectSum.lof K ℤ (fun k => (restrictToField K).obj (cohomologyModule
        (DerivedCategory.Q.obj (unitComplex (Spec (CommRingCat.of K)).toRingedSpace n)) k)) n
        (unitCycleClass (Spec (CommRingCat.of K)).toRingedSpace n) := by
  have hrank : Module.finrank K ((restrictToField K).obj (cohomologyModule
      (DerivedCategory.Q.obj (unitComplex (Spec (CommRingCat.of K)).toRingedSpace n)) n)) = 1 :=
    (((restrictToField K).mapIso (homologySectionsSingleSelfIso
        (Spec (CommRingCat.of K)).toRingedSpace n
        (SheafOfModules.unit (structureSheafRing
          (Spec (CommRingCat.of K)).toRingedSpace)))).toLinearEquiv.trans
      (unitSectionsLinearEquiv K)).finrank_eq.trans (Module.finrank_self K)
  have hne : unitCycleClass (Spec (CommRingCat.of K)).toRingedSpace n ≠ 0 := by
    intro h
    obtain ⟨y, hy⟩ := exists_ne_zero_of_finrank_eq_one K _ hrank
    apply hy
    obtain ⟨a, rfl⟩ := evalUnit_surjective _ n y
    show ((DerivedCategory.homologyFunctor _ n).map ((baseSections _).map a)).hom
      (unitCycleClass (Spec (CommRingCat.of K)).toRingedSpace n) = 0
    rw [h, map_zero]
  refine exists_lof_eq_smul_of_finrank_eq_one K (fun k => (restrictToField K).obj (cohomologyModule
    (DerivedCategory.Q.obj (unitComplex (Spec (CommRingCat.of K)).toRingedSpace n)) k)) n _ hne
    hrank (fun j hj => ?_) j x
  exact ModuleCat.isZero_iff_subsingleton.1 ((restrictToField K).map_isZero
    (isZero_homologySections_single (Spec (CommRingCat.of K)).toRingedSpace n j hj _))

/-! ### De Rham cohomology over a field -/

section Field

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- **The Leray identification over a field**, `H^j(Spec k, Rf_*Ω^•_{X/k}) ≅ H^j_{dR}(X/k)` as
`k`-vector spaces ([Stacks, Tag 0D5W]). -/
def deRhamLerayEquiv (j : ℤ) :
    (pointCohomology k j).obj (derivedDeRhamDirectImageUnbounded f) ≃ₗ[k]
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).obj
        (Scheme.Hom.deRhamCohomologyBaseModule f j) :=
  ((restrictToField k).mapIso (lerayCohomologyIso (inverseImageBaseProjection f)
    (DerivedCategory.Q.obj (deRhamCochainComplex f)) j)).toLinearEquiv

/-- **De Rham cohomology over a field is finite-dimensional** for a proper morphism
([Stacks, Tag 0FLZ]), in the realization `H^j(Spec k, Rf_*Ω^•_{X/k})`. -/
theorem finiteDimensional_pointCohomology_deRhamDirectImage [IsProper f] (j : ℤ) :
    FiniteDimensional k ((pointCohomology k j).obj (derivedDeRhamDirectImageUnbounded f)) :=
  have := moduleFinite_deRhamCohomologyBaseModule_of_isProper f j
  Module.Finite.equiv (deRhamLerayEquiv f j).symm

/-- **De Rham cohomology over a field is bounded** for a proper smooth morphism: the model
`RΓ(Spec k, Rf_*Ω^•_{X/k})` is perfect ([Stacks, Tag 0FM0]), hence represented by a bounded
complex, so `H^j(Spec k, Rf_*Ω^•_{X/k})` vanishes outside an interval. -/
theorem exists_subsingleton_pointCohomology_deRhamDirectImage [IsProper f] [Smooth f] :
    ∃ a b : ℤ, ∀ j, j < a ∨ b < j →
      Subsingleton ((pointCohomology k j).obj (derivedDeRhamDirectImageUnbounded f)) := by
  obtain ⟨P, a, b, hGE, hLE, -, -, ⟨e⟩⟩ := Stacks.DeRhamSmooth.isPerfect_affineDeRhamModel f
  refine ⟨a, b, fun j hj => ?_⟩
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (CommRingCat.of k)) j).obj
      (Stacks.DeRhamSmooth.affineDeRhamModel f)) := by
    refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ j).mapIso e)
    rcases hj with hj | hj
    · exact DerivedCategory.isZero_of_isGE _ a j hj
    · exact DerivedCategory.isZero_of_isLE _ b j hj
  have h₁ := ModuleCat.isZero_iff_subsingleton.1 hz
  have h₂ : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} (CommRingCat.of k))
      j).obj ((derivedGlobalSectionsQuasicoherent (CommRingCat.of k)).obj
        (deRhamDirectImageQCoh f))) := h₁
  exact ((deRhamLerayEquiv f j).toEquiv.trans
    (deRhamCohomologyModuleIso f j).toLinearEquiv.toEquiv).subsingleton

end Field

/-! ### The comparison map -/

section Comparison

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
  (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- `H^j(Spec k, Rf_*Ω^•_{X/k}) ≅ H^j_{dR}(X/k)` for `X` smooth projective over `k`, the
`k`-vector space structure on the right being that of `Stacks.DeRhamWeil.piece`. -/
def pieceLerayEquiv (j : ℤ) :
    (pointCohomology k j).obj (derivedDeRhamDirectImageUnbounded X.obj.hom) ≃ₗ[k]
      DeRhamWeil.piece X j :=
  deRhamLerayEquiv X.obj.hom j

/-- `pieceLerayEquiv` is the Leray identification `lerayCohomologyIso` on elements. -/
theorem pieceLerayEquiv_apply (j : ℤ)
    (x : (pointCohomology k j).obj (derivedDeRhamDirectImageUnbounded X.obj.hom)) :
    pieceLerayEquiv X j x = (lerayCohomologyIso (inverseImageBaseProjection X.obj.hom)
      (DerivedCategory.Q.obj (deRhamCochainComplex X.obj.hom)) j).hom x :=
  rfl

/-- **The base change map on the value of a morphism `𝒪[-j] ⟶ Rf_*Ω^•_{X/k}`.** For
`a : 𝒪_{Spec k}[-j] ⟶ Rf_*Ω^•_{X/k}`, the base change map `pr^*` carries the value of `a` at the
class of `1` to the pullback to `Spec K` of the class of `1`, carried by `Lg^*a` and the base
change isomorphism of [Stacks, Tag 0FM0]. -/
theorem baseChangePiece_pieceLerayEquiv_evalUnit (j : ℤ)
    (a : DerivedCategory.Q.obj (unitComplex (Spec (CommRingCat.of k)).toRingedSpace j) ⟶
      derivedDeRhamDirectImageUnbounded X.obj.hom) :
    haveI : IsProper X.obj.hom := (isProjective X).isProper
    DeRhamWeil.baseChangePiece (fieldBaseChangeProj X) (fieldBaseChangeProj_comp_hom X) j
        (pieceLerayEquiv X j (evalUnit (derivedDeRhamDirectImageUnbounded X.obj.hom) j a)) =
      pieceLerayEquiv ((fieldBaseChange k K).obj X) j
        (((pointCohomology K j).map ((derivedPullback (specStructure k K).toLRSHom.toShHom).map
            a ≫ (Stacks.DeRhamSmooth.deRhamUnboundedBaseChangeIsoOfIsPullback X.obj.hom
              (specStructure k K) (fieldBaseChangeProj X) _
              (isPullback_fieldBaseChangeProj (k' := K) X)).hom)).hom
          (homologyPullback (specStructure k K).toLRSHom.toShHom _ j
            (unitCycleClass (Spec (CommRingCat.of k)).toRingedSpace j))) := by
  have : IsProper X.obj.hom := (isProjective X).isProper
  exact (homologyPullback_unitCycleClass_deRhamUnboundedBaseChange (fieldBaseChangeProj X) _
    X.obj.hom (specStructure k K) (isPullback_fieldBaseChangeProj (k' := K) X) j a).symm

/-- A functor preserving biproducts carries an isomorphism `⨁ d_j` followed by an isomorphism `e` to
the isomorphism `⨁ (F d_j ≫ e)`. -/
private theorem isIso_biproduct_desc_map_comp {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (F : C ⥤ D) [F.Additive] {N : ℕ} {f : Fin N → C} {W : C} {V : D}
    (d : ∀ j, f j ⟶ W) [IsIso (biproduct.desc d)] (e : F.obj W ⟶ V) [IsIso e] :
    IsIso (biproduct.desc fun j => F.map (d j) ≫ e) := by
  have h : biproduct.desc (fun j => F.map (d j) ≫ e) =
      (F.mapBiproduct f).inv ≫ F.map (biproduct.desc d) ≫ e := by
    rw [← Category.assoc, biproduct.mapBiproduct_inv_map_desc]
    exact biproduct.hom_ext' _ _ fun j => by simp
  rw [h]
  infer_instance

/-- **Base change of a decomposition of `Rf_*Ω^•_{X/k}` into lines gives a basis over `K`.** Let
`a_i : 𝒪_{Spec k}[-n_i] ⟶ Rf_*Ω^•_{X/k}` be morphisms with `⨁ a_i` an isomorphism. Then the
pullbacks to `Spec K` of the classes of `1`, carried by `Lg^*a_i` and the base change isomorphism
`Lg^*Rf_*Ω^•_{X/k} ≅ Rf'_*Ω^•_{X_K/K}` of [Stacks, Tag 0FM0], form a basis over `K` of the total
cohomology `⨁_j H^j(Spec K, Rf'_*Ω^•_{X_K/K})`. -/
theorem exists_basis_baseChange {N : ℕ} (nd : Fin N → ℤ)
    (d : ∀ i, DerivedCategory.Q.obj (unitComplex (Spec (CommRingCat.of k)).toRingedSpace (nd i)) ⟶
      derivedDeRhamDirectImageUnbounded X.obj.hom)
    (hd : IsIso (biproduct.desc d)) :
    haveI : IsProper X.obj.hom := (isProjective X).isProper
    ∃ B' : Module.Basis (Fin N) K (DirectSum ℤ fun j => ((pointCohomology K j).obj
        (derivedDeRhamDirectImageUnbounded ((fieldBaseChange k K).obj X).obj.hom) : Type u)),
      ∀ i, B' i = DirectSum.lof K ℤ (fun j => ((pointCohomology K j).obj
        (derivedDeRhamDirectImageUnbounded ((fieldBaseChange k K).obj X).obj.hom) : Type u)) (nd i)
        (((pointCohomology K (nd i)).map
          ((derivedPullback (specStructure k K).toLRSHom.toShHom).map (d i) ≫
            (Stacks.DeRhamSmooth.deRhamUnboundedBaseChangeIsoOfIsPullback X.obj.hom
              (specStructure k K) (fieldBaseChangeProj X) _
              (isPullback_fieldBaseChangeProj (k' := K) X)).hom)).hom
          (homologyPullback (specStructure k K).toLRSHom.toShHom _ (nd i)
            (unitCycleClass (Spec (CommRingCat.of k)).toRingedSpace (nd i)))) := by
  have : IsProper X.obj.hom := (isProjective X).isProper
  have := hd
  have hΨ := isIso_biproduct_desc_map_comp (derivedPullback (specStructure k K).toLRSHom.toShHom) d
    (Stacks.DeRhamSmooth.deRhamUnboundedBaseChangeIsoOfIsPullback X.obj.hom
      (specStructure k K) (fieldBaseChangeProj X) _
      (isPullback_fieldBaseChangeProj (k' := K) X)).hom
  refine exists_basis_of_isIso_biproduct_desc (fun j => pointCohomology K j) nd
    (fun i => (derivedPullback (specStructure k K).toLRSHom.toShHom).obj
      (DerivedCategory.Q.obj (unitComplex (Spec (CommRingCat.of k)).toRingedSpace (nd i))))
    (derivedDeRhamDirectImageUnbounded ((fieldBaseChange k K).obj X).obj.hom)
    (fun i => (derivedPullback (specStructure k K).toLRSHom.toShHom).map (d i) ≫
      (Stacks.DeRhamSmooth.deRhamUnboundedBaseChangeIsoOfIsPullback X.obj.hom
        (specStructure k K) (fieldBaseChangeProj X) _
        (isPullback_fieldBaseChangeProj (k' := K) X)).hom)
    (fun i => homologyPullback (specStructure k K).toLRSHom.toShHom _ (nd i)
      (unitCycleClass (Spec (CommRingCat.of k)).toRingedSpace (nd i)))
    (fun i => Module.nontrivial_of_finrank_eq_succ
      (finrank_cohomologyModule_derivedPullback_unitComplex K
        (specStructure k K).toLRSHom.toShHom (nd i)))
    (fun i j x => exists_lof_eq_smul_homologyPullback K
      (specStructure k K).toLRSHom.toShHom (nd i) j x) hΨ

/-- **The comparison map is bijective once the base change map carries a basis to a basis**: if
`pr^*` carries a `k`-basis of `H^n_{dR}(X/k)` to a `K`-basis of `H^n_{dR}(X_K/K)`, then
`K ⊗_k H^n_{dR}(X/k) ⟶ H^n_{dR}(X_K/K)` carries the `K`-basis `1 ⊗ b_t` to it. -/
theorem bijective_deRhamBaseChangeLinear_of_basis (n : ℤ) {ι : Type*}
    (bX : Module.Basis ι k (DeRhamWeil.piece X n))
    (bXK : Module.Basis ι K (DeRhamWeil.piece ((fieldBaseChange k K).obj X) n))
    (h : ∀ t, DeRhamWeil.baseChangePiece (fieldBaseChangeProj X) (fieldBaseChangeProj_comp_hom X) n
      (bX t) = bXK t) :
    Function.Bijective (deRhamBaseChangeLinear K X n) := by
  let bT := Algebra.TensorProduct.basis K bX
  have hT : ∀ t, deRhamBaseChangeLinear K X n (bT t) = bXK t := fun t =>
    (congrArg (deRhamBaseChangeLinear K X n) (Algebra.TensorProduct.basis_apply bX t)).trans
      ((deRhamBaseChangeLinear_tmul K X n 1 (bX t)).trans ((one_smul K _).trans (h t)))
  have heq : deRhamBaseChangeLinear K X n = (bT.equiv bXK (Equiv.refl _)).toLinearMap :=
    bT.ext fun t => (hT t).trans
      (Module.Basis.equiv_apply (b := bT) (i := t) (b' := bXK) (e := Equiv.refl _)).symm
  exact heq ▸ (bT.equiv bXK (Equiv.refl _)).bijective

/-- **The base change map in degree `n` on the degree-`n` component of a homogeneous class.** For
a class `y` of `H^j(Spec k, Rf_*Ω^•_{X/k})` with `j = n`, the base change map carries the
degree-`n` component of `y` to the degree-`n` component of the pullback to `Spec K` of the class
of `1`, carried by the base change of the morphism `𝒪[-j] ⟶ Rf_*Ω^•_{X/k}` with value `y`. -/
theorem baseChangePiece_component_lof (n j : ℤ) (hj : j = n)
    (y : (pointCohomology k j).obj (derivedDeRhamDirectImageUnbounded X.obj.hom)) :
    haveI : IsProper X.obj.hom := (isProjective X).isProper
    DeRhamWeil.baseChangePiece (fieldBaseChangeProj X) (fieldBaseChangeProj_comp_hom X) n
        (pieceLerayEquiv X n (DirectSum.component k ℤ (fun j => ((pointCohomology k j).obj
          (derivedDeRhamDirectImageUnbounded X.obj.hom) : Type u)) n
          (DirectSum.lof k ℤ (fun j => ((pointCohomology k j).obj
            (derivedDeRhamDirectImageUnbounded X.obj.hom) : Type u)) j y))) =
      pieceLerayEquiv ((fieldBaseChange k K).obj X) n
        (DirectSum.component K ℤ (fun j => ((pointCohomology K j).obj
          (derivedDeRhamDirectImageUnbounded ((fieldBaseChange k K).obj X).obj.hom) :
            Type u)) n
          (DirectSum.lof K ℤ (fun j => ((pointCohomology K j).obj
            (derivedDeRhamDirectImageUnbounded ((fieldBaseChange k K).obj X).obj.hom) :
              Type u)) j
            (((pointCohomology K j).map
              ((derivedPullback (specStructure k K).toLRSHom.toShHom).map
                ((evalUnitEquiv (derivedDeRhamDirectImageUnbounded X.obj.hom) j).symm y) ≫
              (Stacks.DeRhamSmooth.deRhamUnboundedBaseChangeIsoOfIsPullback X.obj.hom
                (specStructure k K) (fieldBaseChangeProj X) _
                (isPullback_fieldBaseChangeProj (k' := K) X)).hom)).hom
              (homologyPullback (specStructure k K).toLRSHom.toShHom _ j
                (unitCycleClass (Spec (CommRingCat.of k)).toRingedSpace j))))) := by
  subst hj
  have h := baseChangePiece_pieceLerayEquiv_evalUnit K X j
    ((evalUnitEquiv (derivedDeRhamDirectImageUnbounded X.obj.hom) j).symm y)
  have hy := (evalUnitEquiv (derivedDeRhamDirectImageUnbounded X.obj.hom) j).apply_symm_apply y
  refine (congrArg (fun z => DeRhamWeil.baseChangePiece (fieldBaseChangeProj X)
    (fieldBaseChangeProj_comp_hom X) j (pieceLerayEquiv X j z))
    ((DirectSum.component.lof_self (R := k) (M := fun j => ((pointCohomology k j).obj
      (derivedDeRhamDirectImageUnbounded X.obj.hom) : Type u)) (i := j) (b := y)).trans
      hy.symm)).trans (h.trans ?_)
  exact congrArg (pieceLerayEquiv ((fieldBaseChange k K).obj X) j)
    (DirectSum.component.lof_self (R := K) (M := fun j => ((pointCohomology K j).obj
      (derivedDeRhamDirectImageUnbounded ((fieldBaseChange k K).obj X).obj.hom) : Type u))
      (i := j) (b := _)).symm

/-- **[Stacks, Tag 0FM0] over a field: de Rham cohomology commutes with extension of the base
field.** For `X` smooth projective over `k` and an extension `K` of `k`, the comparison map
`K ⊗_k H^n_{dR}(X/k) ⟶ H^n_{dR}(X_K/K)`, `c ⊗ x ↦ c · pr^* x`, is bijective. -/
theorem bijective_deRhamBaseChangeLinear (n : ℤ) :
    Function.Bijective (deRhamBaseChangeLinear K X n) := by
  classical
  have : IsProper X.obj.hom := (isProjective X).isProper
  -- a homogeneous basis of the total cohomology over `k`
  have := finiteDimensional_pointCohomology_deRhamDirectImage X.obj.hom
  obtain ⟨a, b, hz⟩ := exists_subsingleton_pointCohomology_deRhamDirectImage X.obj.hom
  obtain ⟨N, nd, y, B, hB⟩ := exists_basis_lof (R := k)
    (fun j => ((pointCohomology k j).obj (derivedDeRhamDirectImageUnbounded X.obj.hom) :
      Type u)) a b hz
  -- `⨁ 𝒪[-n_i] ⟶ E` is an isomorphism
  have hd : ∀ i, ((pointCohomology k (nd i)).map
      ((evalUnitEquiv (derivedDeRhamDirectImageUnbounded X.obj.hom) (nd i)).symm (y i))).hom
      (unitCycleClass (Spec (CommRingCat.of k)).toRingedSpace (nd i)) = y i := fun i =>
    (evalUnitEquiv (derivedDeRhamDirectImageUnbounded X.obj.hom) (nd i)).apply_symm_apply (y i)
  have hΦ := isIso_biproduct_desc_of_basis (fun j => pointCohomology k j)
    (fun φ hφ => isIso_of_forall_isIso_pointCohomology k φ hφ) nd
    (fun i => DerivedCategory.Q.obj (unitComplex (Spec (CommRingCat.of k)).toRingedSpace (nd i)))
    (derivedDeRhamDirectImageUnbounded X.obj.hom)
    (fun i => (evalUnitEquiv (derivedDeRhamDirectImageUnbounded X.obj.hom) (nd i)).symm (y i))
    (fun i => unitCycleClass (Spec (CommRingCat.of k)).toRingedSpace (nd i))
    (fun i j x => exists_lof_eq_smul_unitCycleClass k (nd i) j x) B
    (fun i => (hB i).trans (by rw [hd i]))
  -- its base change `⨁ Lg^*𝒪[-n_i] ⟶ E'` is an isomorphism
  obtain ⟨B', hB'⟩ := exists_basis_baseChange K X nd
    (fun i => (evalUnitEquiv (derivedDeRhamDirectImageUnbounded X.obj.hom) (nd i)).symm (y i)) hΦ
  -- the bases in degree `n`
  obtain ⟨bk, hbk⟩ := exists_basis_component
    (fun j => ((pointCohomology k j).obj (derivedDeRhamDirectImageUnbounded X.obj.hom) : Type u))
    B nd y hB n
  obtain ⟨bK, hbK⟩ := exists_basis_component
    (fun j => ((pointCohomology K j).obj
      (derivedDeRhamDirectImageUnbounded ((fieldBaseChange k K).obj X).obj.hom) : Type u))
    B' nd _ hB' n
  have hbase : ∀ t, DeRhamWeil.baseChangePiece (fieldBaseChangeProj X)
      (fieldBaseChangeProj_comp_hom X) n (bk.map (pieceLerayEquiv X n) t) =
      bK.map (pieceLerayEquiv ((fieldBaseChange k K).obj X) n) t := by
    intro t
    rw [Module.Basis.map_apply, Module.Basis.map_apply, hbk, hbK]
    exact baseChangePiece_component_lof K X n (nd t) t.2 (y t)
  -- the comparison map carries a basis to a basis
  exact bijective_deRhamBaseChangeLinear_of_basis K X n _ _ hbase

end Comparison

end Stacks.WeilDeRham

end
