module

public import StacksFrontier.Cotangent.KoszulRegularIdealQuotientUnconditional
public import StacksFrontier.Cotangent.LocalCompleteIntersectionPerfect
public import StacksFrontier.Cotangent.NaiveComparisonIsIso
public import StacksFrontier.Cotangent.NaiveComplexFunctoriality
public import StacksFrontier.Cotangent.PolynomialRetraction
public import StacksFrontier.Cotangent.Triangle.ProductDescent
import StacksCore.Tactic.StacksAttribute

/-!
# The cotangent complex of a local complete intersection is perfect (Stacks 08SL)

Let `A → B` be a local complete intersection map. Then `L_{B/A}` is a perfect object of `D(B)`
with Tor amplitude in `[-1, 0]`.

`CommAlgCat.isPerfect_and_hasTorAmplitude_cotangentComplexDerived_of_isLocalCompleteIntersection`
of `StacksFrontier/Cotangent/LocalCompleteIntersectionPerfect.lean` proves this from an isomorphism
`L_{B/A} ≅ NL(P → B)` in `D(B)` with the naive complex of a finite polynomial presentation
`P = A[x₁, …, x_n] → B`. This file constructs that isomorphism, following the source's proof.

1. `H^i(L_{B/A}) = 0` for `i ≤ -2`. The fundamental triangle (Tag 08QS, Proposition 08QX) of
   `A → P → B` is `L_{P/A} ⊗^𝐋_P B → L_{B/A} → L_{B/P} → …`. The first vertex lies in degrees
   `≥ 0`, as `L_{P/A} = Ω_{P/A}[0]` with `Ω_{P/A}` free (Tag 08QH), and `H^i(L_{B/P}) = 0` for
   `i ≤ -2` by Tag 08SK, the kernel `J` of `P → B` being Koszul-regular (Tag 07CZ). The long
   exact cohomology sequence then kills `H^i(L_{B/A})` for `i ≤ -2`, so
   `L_{B/A} ≅ τ_{≥ -1} L_{B/A}`.
2. `τ_{≥ -1} L_{B/A} ≅ NL_{B/A}` is Tag 08RB, at the canonical presentation `A[B] → B`.
3. `NL_{B/A} ≅ NL(P → B)`: two presentations have homotopy equivalent naive complexes. Morphisms
   of presentations both ways exist (each ring is a polynomial algebra and the other maps onto
   `B`), and two morphisms `s, t` of presentations induce homotopic maps of naive complexes, the
   homotopy being `Algebra.Extension.Hom.sub s t`; this is
   `Algebra.Extension.naiveComplexHomotopy`.

## Main results

* `Algebra.Extension.naiveComplexHomotopy`: two morphisms of extensions induce chain homotopic
  maps of naive cotangent complexes.
* `Algebra.Extension.naiveComplexQIso`: morphisms of extensions both ways induce an isomorphism
  of the naive cotangent complexes in the derived category.
* `CommAlgCat.isZero_homology_cotangentComplexDerived_of_isLocalCompleteIntersection`:
  `H^i(L_{B/A}) = 0` for `i ≤ -2` for a local complete intersection.
* `CommAlgCat.cotangentComplexDerivedIsoNaiveComplexOfIsLocalCompleteIntersection`: the
  isomorphism `L_{B/A} ≅ NL(P → B)` for every finite polynomial presentation `P` of a local
  complete intersection.
* `CommAlgCat.isPerfect_and_hasTorAmplitude_cotangentComplexDerived_of_isLCI`:
  **Stacks 08SL**, under the source's single hypothesis.

## References

* [Stacks Project, Tag 08SL](https://stacks.math.columbia.edu/tag/08SL)
* [Stacks Project, Tag 08RB](https://stacks.math.columbia.edu/tag/08RB)
* [Stacks Project, Tag 08SK](https://stacks.math.columbia.edu/tag/08SK)
* [Stacks Project, Tag 08QS](https://stacks.math.columbia.edu/tag/08QS)
* [Stacks Project, Tag 08QH](https://stacks.math.columbia.edu/tag/08QH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex.HomComplex

universe u v

/-! ### Two presentations have homotopy equivalent naive complexes -/

namespace Algebra.Extension

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

section Homotopy

variable {P P' : Extension.{v} R S} (s t : P.Hom P')

/-- The difference of the maps `J/J² ⟶ J'/J'²` induced by `s` and `t` is `Hom.sub s t`
precomposed with the differential of `NL(P)`. -/
theorem ofHom_cotangentMap_eq_add :
    ModuleCat.ofHom (Cotangent.map s) =
      ModuleCat.ofHom (Y := ModuleCat.of S P.CotangentSpace) P.cotangentComplex ≫
          ModuleCat.ofHom (Y := ModuleCat.of S P'.Cotangent) (s.sub t) +
        ModuleCat.ofHom (Cotangent.map t) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  have h := LinearMap.congr_fun (Cotangent.map_sub_map s t) x
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply] at h
  change Cotangent.map s x = (s.sub t) (P.cotangentComplex x) + Cotangent.map t x
  rw [← h, sub_add_cancel]

/-- The difference of the maps of cotangent spaces induced by `s` and `t` is `Hom.sub s t`
followed by the differential of `NL(P')`. -/
theorem ofHom_cotangentSpaceMap_eq_add :
    ModuleCat.ofHom (CotangentSpace.map s) =
      ModuleCat.ofHom (Y := ModuleCat.of S P'.Cotangent) (s.sub t) ≫
          ModuleCat.ofHom (Y := ModuleCat.of S P'.CotangentSpace) P'.cotangentComplex +
        ModuleCat.ofHom (CotangentSpace.map t) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  have h := LinearMap.congr_fun (CotangentSpace.map_sub_map s t) x
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    Function.comp_apply] at h
  change CotangentSpace.map s x = P'.cotangentComplex ((s.sub t) x) + CotangentSpace.map t x
  rw [← h, sub_add_cancel]

/-- The nonzero component of the homotopy, from degree `0` to degree `-1`:
`Ω[P⁄R] ⊗[P] S ⟶ J'/J'²` is `Algebra.Extension.Hom.sub s t`. -/
def naiveComplexHomotopyZero : (naiveComplex P).X 0 ⟶ (naiveComplex P').X (-1) :=
  (naiveComplexXZeroIso P).hom ≫ ModuleCat.ofHom (Y := ModuleCat.of S P'.Cotangent) (s.sub t) ≫
    (naiveComplexXNegOneIso P').inv

/-- The homotopy between the maps induced by `s` and `t`, as a cochain of degree `-1`. -/
def naiveComplexHomotopyCochain : Cochain (naiveComplex P) (naiveComplex P') (-1) :=
  Cochain.mk fun p q hpq =>
    if h : p = 0 then
      eqToHom (by rw [h]) ≫ naiveComplexHomotopyZero s t ≫
        eqToHom (by obtain rfl : q = -1 := by lia
                    rfl)
    else 0

/-- The component of `naiveComplexHomotopyCochain s t` from degree `0` to degree `-1` is
`naiveComplexHomotopyZero s t`. -/
theorem naiveComplexHomotopyCochain_v_zero :
    (naiveComplexHomotopyCochain s t).v 0 (-1) (by norm_num) = naiveComplexHomotopyZero s t := by
  rw [naiveComplexHomotopyCochain, Cochain.mk_v, dif_pos rfl, eqToHom_refl, eqToHom_refl,
    Category.id_comp, Category.comp_id]

/-- The components of `naiveComplexHomotopyCochain s t` out of every degree `p ≠ 0` vanish. -/
theorem naiveComplexHomotopyCochain_v_of_ne (p q : ℤ) (hpq : p + (-1) = q) (hp : p ≠ 0) :
    (naiveComplexHomotopyCochain s t).v p q hpq = 0 := by
  rw [naiveComplexHomotopyCochain, Cochain.mk_v, dif_neg hp]

/-- The homotopy identity: `naiveComplexMap s = δ h + naiveComplexMap t`. -/
theorem ofHom_naiveComplexMap_eq :
    Cochain.ofHom (naiveComplexMap s) =
      δ (-1) 0 (naiveComplexHomotopyCochain s t) + Cochain.ofHom (naiveComplexMap t) := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  obtain rfl : p = q := by lia
  rw [Cochain.add_v, Cochain.ofHom_v, Cochain.ofHom_v,
    δ_v (-1) 0 (by norm_num) _ p p hpq (p - 1) (p + 1) (by lia) rfl]
  by_cases hp : p = -1
  · obtain rfl := hp
    simp only [Int.reduceAdd, Int.reduceSub]
    rw [naiveComplexHomotopyCochain_v_of_ne s t (-1) (-2) (by norm_num) (by decide),
      naiveComplexHomotopyCochain_v_zero, naiveComplexMap_f_negOne, naiveComplexMap_f_negOne,
      naiveComplexMapNegOne, naiveComplexMapNegOne, naiveComplexHomotopyZero, naiveComplex_d,
      ofHom_cotangentMap_eq_add s t]
    simp only [Limits.zero_comp, zero_add, Int.negOnePow_zero, one_smul, Category.assoc,
      Iso.inv_hom_id_assoc, Preadditive.add_comp, Preadditive.comp_add]
  · by_cases hp0 : p = 0
    · obtain rfl := hp0
      simp only [Int.reduceAdd, Int.reduceSub]
      rw [naiveComplexHomotopyCochain_v_zero,
        naiveComplexHomotopyCochain_v_of_ne s t 1 0 (by norm_num) (by decide),
        naiveComplexMap_f_zero, naiveComplexMap_f_zero, naiveComplexMapZero, naiveComplexMapZero,
        naiveComplexHomotopyZero, naiveComplex_d, ofHom_cotangentSpaceMap_eq_add s t]
      simp only [Limits.comp_zero, add_zero, Int.negOnePow_zero, one_smul, Category.assoc,
        Iso.inv_hom_id_assoc, Preadditive.add_comp, Preadditive.comp_add]
    · rw [naiveComplexHomotopyCochain_v_of_ne s t p (p - 1) (by lia) hp0,
        naiveComplexHomotopyCochain_v_of_ne s t (p + 1) p (by lia) (by lia),
        naiveComplexMap_f_eq_zero s p hp hp0, naiveComplexMap_f_eq_zero t p hp hp0]
      simp

/-- **Two morphisms of extensions induce chain homotopic maps of naive cotangent complexes**,
the homotopy being `Algebra.Extension.Hom.sub`. -/
def naiveComplexHomotopy : Homotopy (naiveComplexMap s) (naiveComplexMap t) :=
  (Cochain.equivHomotopy _ _).symm ⟨naiveComplexHomotopyCochain s t, ofHom_naiveComplexMap_eq s t⟩

end Homotopy

section DerivedIso

variable [HasDerivedCategory (ModuleCat.{v} S)]

/-- Two morphisms of extensions induce the same map of naive cotangent complexes in the derived
category. -/
theorem Q_map_naiveComplexMap_eq {P P' : Extension.{v} R S} (s t : P.Hom P') :
    DerivedCategory.Q.map (naiveComplexMap s) = DerivedCategory.Q.map (naiveComplexMap t) :=
  DerivedCategory.Q_map_eq_of_homotopy _ (naiveComplexHomotopy s t)

/-- **Two extensions with morphisms both ways have isomorphic naive cotangent complexes** in the
derived category; the isomorphism is induced by either morphism. -/
@[sga "6 0 4.3" "partial"]
def naiveComplexQIso {P P' : Extension.{v} R S} (θ : P.Hom P') (θ' : P'.Hom P) :
    DerivedCategory.Q.obj (naiveComplex P) ≅ DerivedCategory.Q.obj (naiveComplex P') where
  hom := DerivedCategory.Q.map (naiveComplexMap θ)
  inv := DerivedCategory.Q.map (naiveComplexMap θ')
  hom_inv_id := by
    rw [← Functor.map_comp, ← naiveComplexMap_comp, Q_map_naiveComplexMap_eq _ (Hom.id P),
      naiveComplexMap_id, CategoryTheory.Functor.map_id]
  inv_hom_id := by
    rw [← Functor.map_comp, ← naiveComplexMap_comp, Q_map_naiveComplexMap_eq _ (Hom.id P'),
      naiveComplexMap_id, CategoryTheory.Functor.map_id]

end DerivedIso

end Algebra.Extension

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

/-! ### The vanishing of `H^i(L_{B/A})` for `i ≤ -2` -/

/-- The kernel of every finite polynomial presentation of a local complete intersection is a
Koszul-regular ideal (Tag 07CZ). -/
theorem isKoszulRegular_ker_algebraMap_of_isLocalCompleteIntersection
    {A B ι : Type*} [CommRing A] [CommRing B] [Algebra A B] [Finite ι]
    (P : Algebra.Generators A B ι)
    (h : RingHom.IsLocalCompleteIntersection (algebraMap A B)) :
    Ideal.IsKoszulRegular (RingHom.ker (algebraMap P.Ring B)) := by
  rw [RingHom.IsLocalCompleteIntersection, toAlgebra_algebraMap] at h
  obtain ⟨_, n, p, hp, hreg⟩ := h
  change Ideal.IsKoszulRegular P.ker
  rw [Algebra.Generators.ker_eq_ker_aeval_val]
  exact RingHom.isKoszulRegularIdeal_ker_of_surjective_mvPolynomial
    p hp hreg (MvPolynomial.aeval P.val) P.aeval_val_surjective

/-- A local complete intersection has a finite polynomial presentation with variables in the
universe of the rings. -/
theorem exists_generators_of_isLocalCompleteIntersection
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (h : RingHom.IsLocalCompleteIntersection (algebraMap A B)) :
    ∃ n : ℕ, Nonempty (Algebra.Generators A B (ULift.{u} (Fin n))) := by
  rw [RingHom.IsLocalCompleteIntersection, toAlgebra_algebraMap] at h
  obtain ⟨_, n, p, hp, -⟩ := h
  let e : MvPolynomial (ULift.{u} (Fin n)) A ≃ₐ[A] MvPolynomial (Fin n) A :=
    MvPolynomial.renameEquiv A Equiv.ulift
  exact ⟨n, ⟨Algebra.Generators.ofAlgHom (p.comp e.toAlgHom) (hp.comp e.surjective)⟩⟩

/-- **`H^i(L_{B/A}) = 0` for `i ≤ -2`, for a local complete intersection `A → B`.** Choose a
finite polynomial presentation `P → B`. In the fundamental triangle of `A → P → B` the first
vertex `L_{P/A} ⊗^𝐋_P B` lies in degrees `≥ 0` (Tag 08QH) and the third vertex `L_{B/P}` has no
cohomology in degrees `≤ -2` (Tag 08SK, the kernel of `P → B` being Koszul-regular). -/
theorem isZero_homology_cotangentComplexDerived_of_isLocalCompleteIntersection
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (hlci : RingHom.IsLocalCompleteIntersection (algebraMap A B)) (i : ℤ) (hi : i ≤ -2) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
      (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B))) := by
  obtain ⟨n, ⟨P⟩⟩ := exists_generators_of_isLocalCompleteIntersection hlci
  have hpoly : Algebra.IsPolynomialAlgebra A P.Ring :=
    ⟨ULift.{u} (Fin n), ⟨AlgEquiv.refl⟩⟩
  have h₁ : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
      (fundamentalVertex₁.{u, u} A P.Ring B)) :=
    (DerivedCategory.isGE_iff _ 0).1
      (isGE_cotangentComplexDerivedBaseChange_of_isPolynomialAlgebra A P.Ring B hpoly) i
      (by omega)
  have h₃ : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
      (fundamentalVertex₃.{u, u} P.Ring B)) :=
    (isZero_homology_cotangentComplex_of_isKoszulRegular_unconditional P.Ring
      (CommAlgCat.of P.Ring B) P.algebraMap_surjective
      (isKoszulRegular_ker_algebraMap_of_isLocalCompleteIntersection P hlci) i hi).of_iso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i).app _)
  exact (DerivedCategory.HomologySequence.exact₂ _
    (productFundamentalTriangle_distinguished A P.Ring B) i).isZero_X₂
    (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

/-! ### The isomorphism `L_{B/A} ≅ NL(P → B)` -/

/-- For a local complete intersection `A → B`, the truncation `L_{B/A} ⟶ τ_{≥ -1} L_{B/A}` is an
isomorphism. -/
theorem isIso_truncGEπ_cotangentComplexDerived_of_isLocalCompleteIntersection
    (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)
    (hlci : RingHom.IsLocalCompleteIntersection (algebraMap A ↥B)) :
    IsIso ((DerivedCategory.TStructure.t.truncGEπ (-1)).app
      (cotangentComplexDerived.{u, u} A B)) := by
  have hGE : (cotangentComplexDerived.{u, u} A B).IsGE (-1) :=
    (DerivedCategory.isGE_iff _ (-1)).2 fun i hi =>
      isZero_homology_cotangentComplexDerived_of_isLocalCompleteIntersection A ↥B hlci i
        (by omega)
  exact (DerivedCategory.TStructure.t.isGE_iff_isIso_truncGEπ_app (-1) _).1 hGE

/-- **`L_{B/A} ≅ NL(P → B)` for a local complete intersection.** For every finite polynomial
presentation `P` of `B` over `A`, the cotangent complex is isomorphic in `D(B)` to the naive
complex of `P`: `L_{B/A} ≅ τ_{≥ -1} L_{B/A}` by the vanishing of `H^i(L_{B/A})` for `i ≤ -2`,
`τ_{≥ -1} L_{B/A} ≅ NL_{B/A}` by Tag 08RB, and `NL_{B/A} ≅ NL(P → B)` since the naive complexes
of two presentations are homotopy equivalent. -/
def cotangentComplexDerivedIsoNaiveComplexOfIsLocalCompleteIntersection
    (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) {ι : Type u}
    (P : Algebra.Generators A ↥B ι)
    (hlci : RingHom.IsLocalCompleteIntersection (algebraMap A ↥B)) :
    cotangentComplexDerived.{u, u} A B ≅
      DerivedCategory.Q.obj (Algebra.Extension.naiveComplex P.toExtension) :=
  haveI := isIso_truncGEπ_cotangentComplexDerived_of_isLocalCompleteIntersection A B hlci
  asIso ((DerivedCategory.TStructure.t.truncGEπ (-1)).app (cotangentComplexDerived.{u, u} A B)) ≪≫
    (Stacks.Cotangent.naiveComparisonIso.{u, u} A B).symm ≪≫
    DerivedCategory.Q.mapIso (Stacks.Cotangent.naiveSpellingIso.{u, u} A B 0).symm ≪≫
    DerivedCategory.Q.mapIso (Stacks.Cotangent.naiveComplexStandardResolutionZeroIso.{u, u} A B) ≪≫
    Algebra.Extension.naiveComplexQIso
      (Algebra.Extension.defaultHom A ↥B P.toExtension)
      (Algebra.Generators.Hom.toExtensionHom
        (Algebra.Generators.defaultHom P (Algebra.Generators.self A ↥B)))

/-! ### Stacks 08SL -/

/-- If `A → B` is a local complete intersection map, then the cotangent complex `L_{B/A}` is a
perfect object of `D(B)` with Tor amplitude in `[-1, 0]`.

Choose a finite polynomial presentation `P = A[x₁, …, x_n] → B`. The
naive complex `NL(P → B) = (J/J² → ⨁ B dxᵢ)` consists of finite projective modules, by Tag 08RK,
`CommAlgCat.isPerfect_and_hasTorAmplitude_cotangentComplexDerived_of_isLocalCompleteIntersection`;
and `L_{B/A}` is isomorphic to it in `D(B)`
(`CommAlgCat.cotangentComplexDerivedIsoNaiveComplexOfIsLocalCompleteIntersection`): by Tag 08RB
`NL(P → B) ≅ τ_{≥ -1} L_{B/A}`, and by the fundamental triangle 08QS of `A → P → B` together with
Tags 08QH and 08SK, `H^i(L_{B/A}) = 0` for `i ≤ -2`. -/
@[stacks 08SL "the proposition, under the source's single hypothesis that A → B is a local \
  complete intersection (RingHom.IsLocalCompleteIntersection, Tag 07D0). Perfect is Tag 0657 (1) \
  and Tor amplitude is Tag 0652 (1) at the canonical derived tensor product. The isomorphism of \
  L_{B/A} with the naive complex of a finite polynomial presentation is constructed here from \
  Tag 08RB (Stacks.Cotangent.naiveComparisonIso), the fundamental triangle of A → P → B \
  (Proposition 08QX), Tag 08QH and Tag 08SK",
  sga "6 0 4.3" "special case",
  sga "6 VIII 2.4" "special case",
  sga "6 XIV 2.1" "special case"]
theorem isPerfect_and_hasTorAmplitude_cotangentComplexDerived_of_isLCI
    (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)
    (hlci : RingHom.IsLocalCompleteIntersection (algebraMap A ↥B)) :
    StacksDraft.Perfect.IsPerfect (cotangentComplexDerived.{u, u} A B) ∧
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical ↥B
        (cotangentComplexDerived.{u, u} A B) (-1) 0 := by
  obtain ⟨n, ⟨P⟩⟩ := exists_generators_of_isLocalCompleteIntersection hlci
  exact isPerfect_and_hasTorAmplitude_cotangentComplexDerived_of_isLocalCompleteIntersection A B P
    hlci (cotangentComplexDerivedIsoNaiveComplexOfIsLocalCompleteIntersection A B P hlci)

end CommAlgCat

end
