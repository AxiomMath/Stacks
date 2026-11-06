module

public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Examples.Algebra.CompletionFormallyUnramified
public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.RingTheory.Excellent.LocalGRing
public import StacksFrontier.RingTheory.FormallySmooth.Presentation
public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.NaiveCotangent.Colimit
public import StacksFrontier.RingTheory.Smoothing.PopescuTheorem

/-!
# Excellence and formal étaleness of the completion of a regular local ring

A regular local ring `A` of characteristic `p > 0` whose residue field has finite imperfection
degree `[κ : κᵖ] < ∞` is excellent exactly when the canonical map `A → A^∧` to its
maximal-ideal-adic completion is formally étale.

Formal unramifiedness of `A → A^∧` holds under these hypotheses regardless of excellence, so the
whole content of the forward implication is formal smoothness. Excellence makes `A` a G-ring, so
`A → A^∧` is a regular ring map; Néron–Popescu desingularization then presents `A^∧` as a
filtered colimit of smooth `A`-algebras. The naive cotangent complex commutes with that colimit
and vanishes in degree `-1` at each smooth stage, so `H¹(L_{A^∧/A}) = 0`; together with the
vanishing of `Ω_{A^∧/A}` this is formal smoothness.

## Main results

* `Stacks.Examples.formallySmooth_of_indSmooth_of_formallyUnramified`: an algebra that is a
  filtered colimit of smooth algebras and has vanishing module of differentials is formally
  smooth.
* `Stacks.Examples.flat_formallyUnramified_adicCompletion_and_not_formallyEtale`: Lemma `0G66`,
  that the completion map of a Noetherian local ring of prime characteristic with finite
  residue-field imperfection degree is flat and formally unramified, and is not formally étale
  when the ring is regular but not excellent.
* `Stacks.Examples.isExcellent_iff_formallyEtale_adicCompletion_maximalIdeal`: Lemma `0G68`,
  the equivalence of excellence with formal étaleness of the completion map.

## Implementation notes

The condition `[κ : κᵖ] < ∞` is finiteness of the residue field as a module over the field range
of its Frobenius at its exponential characteristic. The completion is
`AdicCompletion (IsLocalRing.maximalIdeal A) A` and the canonical map is its algebra map.

The Néron–Popescu theorem `07GC` (`Stacks.Smoothing.indSmooth_of_isRegularRingMap`), which the
forward implication uses, is unconditional: the resolution of a local smoothing situation over a
field of characteristic `p > 0` — Lemma `07FJ`, the branch of `07GC` that a statement about
characteristic `p > 0` needs — is proved as
`Stacks.Smoothing.canBeResolvedInPositiveCharacteristic`.

In Lemma `0G66`, flatness is Mathlib's instance `AdicCompletion.flat_of_isNoetherian` and formal
unramifiedness is `Stacks.Examples.formallyUnramified_adicCompletion_maximalIdeal`. The failure
of formal étaleness is proved in contrapositive form, by a route different from the source's
`p`-basis computation and Kunz's theorem: a formally smooth completion map is a regular ring
map, so the ring is a G-ring (`isGRing_of_formallySmooth_adicCompletion`), and a regular local
G-ring is excellent (`isExcellent_of_isGRing_of_isRegularLocalRing`). That route uses neither
the characteristic nor the imperfection-degree hypothesis, which the source's statement needs for
formal unramifiedness.

The passage from vanishing of `Ω_{A^∧/A}` and of `H¹(L_{A^∧/A})` to formal smoothness is
Proposition `031J`; it is immediate here because Mathlib defines `Algebra.FormallySmooth` by
exactly those two conditions, which is clause (4) of that proposition.

## References

* [Stacks Project, Tag 0G68](https://stacks.math.columbia.edu/tag/0G68)
* [Stacks Project, Tag 0G66](https://stacks.math.columbia.edu/tag/0G66)
* [Stacks Project, Tag 07GC](https://stacks.math.columbia.edu/tag/07GC)
* [Stacks Project, Tag 031J](https://stacks.math.columbia.edu/tag/031J)
-/

@[expose] public section

namespace Stacks.Examples

open Algebra CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped TensorProduct

universe u

/-! ### From a filtered colimit of smooth algebras to formal smoothness -/

/-- The degree-`0` terms of the naive cotangent complexes of a system of ring maps form a
directed system: the transition maps are identities at the diagonal and compose. -/
private theorem cotangentSpace_directedSystem {ι : Type*} [Preorder ι]
    (sys : RingMapSystemUnbundled ι) :
    DirectedSystem (fun i => (sys.NL i).CotangentSpace)
      (fun i j h => (sys.cotSpaceMap h : (sys.NL i).CotangentSpace →
        (sys.NL j).CotangentSpace)) := by
  classical
  have hx (i) (x : (sys.NL i).CotangentSpace) : x =
      ∑ c ∈ ((Generators.self (sys.R i) (sys.S i)).cotangentSpaceBasis.repr x).support,
        (Generators.self (sys.R i) (sys.S i)).cotangentSpaceBasis.repr x c •
          (Generators.self (sys.R i) (sys.S i)).cotangentSpaceBasis c := by
    conv_lhs =>
      rw [← (Generators.self (sys.R i) (sys.S i)).cotangentSpaceBasis.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine ⟨fun i x => ?_, fun k j i hij hjk x => ?_⟩
  · rw [hx i x, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sys.cotSpaceMap_smul, sys.cotSpaceMap_basis, sys.fS_id, sys.fS_id]
  · rw [hx i x, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sys.cotSpaceMap_smul, sys.cotSpaceMap_basis, sys.cotSpaceMap_smul,
      sys.cotSpaceMap_basis, sys.cotSpaceMap_smul, sys.cotSpaceMap_basis,
      sys.fS_comp, sys.fS_comp]

open Classical in
/-- The colimit differential evaluated on a degree-`1` cocone generator is the stage
differential followed by the degree-`0` cocone map. -/
private theorem colimDifferential_toColimCotangent {Λ : Type*} [Preorder Λ]
    (sys : RingMapSystemUnbundled Λ) (i : Λ) (x : (sys.NL i).Cotangent) :
    sys.colimDifferential (sys.toColimCotangent i x)
      = sys.toColimCotangentSpace i ((sys.NL i).cotangentComplex x) :=
  Module.DirectLimit.lift_of _ _ _

/-- If every stage of a system of ring maps has injective naive cotangent differential, so does
the colimit of the stage differentials: an element of the colimit killed by it is killed at some
stage, where injectivity applies. -/
private theorem colimDifferential_injective {Λ : Type*} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    [Nonempty Λ] (sys : RingMapSystemUnbundled Λ)
    (hinj : ∀ i, Function.Injective (sys.NL i).cotangentComplex) :
    Function.Injective sys.colimDifferential := by
  classical
  have := cotangentSpace_directedSystem sys
  rw [injective_iff_map_eq_zero]
  intro z
  refine Module.DirectLimit.induction_on z fun i x hz => ?_
  have hz' : sys.toColimCotangentSpace i ((sys.NL i).cotangentComplex x) = 0 := by
    rwa [← colimDifferential_toColimCotangent sys i x]
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact hz'
  have hmap : sys.cotMap hij x = 0 :=
    hinj j (by rwa [sys.cotMap_cotangentComplex hij x, map_zero])
  change sys.toColimCotangent i x = 0
  have heq : sys.toColimCotangent j (sys.cotMap hij x) =
      sys.toColimCotangent i x := Module.DirectLimit.of_f
  rw [← heq, hmap, map_zero]

/-- The direct limit of the underlying rings of a diagram of commutative rings, as a cocone. -/
private noncomputable def directLimitCocone {ι : Type u} [Preorder ι] (F : ι ⥤ CommRingCat.{u}) :
    Cocone F where
  pt := CommRingCat.of (Ring.DirectLimit (fun i => F.obj i)
    (fun _ _ h => (F.map (homOfLE h)).hom))
  ι.app i := CommRingCat.ofHom (Ring.DirectLimit.of (fun i => F.obj i)
    (fun _ _ h => (F.map (homOfLE h)).hom) i)
  ι.naturality i j h := CommRingCat.hom_ext <| RingHom.ext fun x =>
    Ring.DirectLimit.of_f (G := fun i => F.obj i)
      (f := fun i j h => (F.map (homOfLE h)).hom) (leOfHom h) x

/-- The direct-limit cocone is a colimit cocone, by the universal property of the direct
limit. -/
private noncomputable def directLimitCoconeIsColimit {ι : Type u} [Preorder ι]
    (F : ι ⥤ CommRingCat.{u}) : IsColimit (directLimitCocone F) where
  desc s := CommRingCat.ofHom (Ring.DirectLimit.lift (fun i => F.obj i)
    (fun _ _ h => (F.map (homOfLE h)).hom) s.pt (fun i => (s.ι.app i).hom)
    (fun i j h x => ConcreteCategory.congr_hom (s.w (homOfLE h)) x))
  fac s j := CommRingCat.hom_ext <| RingHom.ext fun x =>
    Ring.DirectLimit.lift_of s.pt (fun i => (s.ι.app i).hom)
      (fun i j h x => ConcreteCategory.congr_hom (s.w (homOfLE h)) x) j x
  uniq s m hm := by
    apply CommRingCat.hom_ext
    apply Ring.DirectLimit.hom_ext
    intro j
    apply RingHom.ext
    intro x
    exact (ConcreteCategory.congr_hom (hm j) x).trans
      (Ring.DirectLimit.lift_of s.pt (fun i => (s.ι.app i).hom)
        (fun i j h x => ConcreteCategory.congr_hom (s.w (homOfLE h)) x) j x).symm

/-- Any colimit of a diagram of commutative rings over a directed index is identified with the
direct limit of the underlying rings, compatibly with the cocone maps. -/
private theorem exists_ringEquiv_directLimit {ι : Type u} [Preorder ι] (F : ι ⥤ CommRingCat.{u})
    (c : Cocone F) (hc : IsColimit c) :
    ∃ e : Ring.DirectLimit (fun i => F.obj i)
        (fun _ _ h => (F.map (homOfLE h)).hom) ≃+* c.pt,
      ∀ i x, e (Ring.DirectLimit.of (fun i => F.obj i)
        (fun _ _ h => (F.map (homOfLE h)).hom) i x) = (c.ι.app i).hom x :=
  ⟨((directLimitCoconeIsColimit F).coconePointUniqueUpToIso hc).commRingCatIsoToRingEquiv,
    fun i x => congrArg (fun f : _ ⟶ c.pt => f.hom x) ((directLimitCoconeIsColimit F).fac c i)⟩

/-- If every stage of a directed system of ring maps has injective naive cotangent differential,
so does the colimit ring map. -/
theorem cotangentComplex_NLinf_injective {Λ : Type*} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    [Nonempty Λ] (sys : RingMapSystemUnbundled Λ)
    (hinj : ∀ i, Function.Injective (sys.NL i).cotangentComplex) :
    Function.Injective sys.NLinf.cotangentComplex := by
  classical
  have hcolim := sys.isIso_colim_NL
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hcolim.1.surjective x
  have hy : sys.comparisonCotangentSpace (sys.colimDifferential y) = 0 := by
    rw [sys.comparison_chain_map, hx]
  have hdy : sys.colimDifferential y = 0 := hcolim.2.1.injective (by simpa using hy)
  simp [colimDifferential_injective sys hinj (hdy.trans (map_zero _).symm)]

/-- The system of ring maps `A → D(i)` underlying a diagram of commutative `A`-algebras. -/
noncomputable def underRingMapSystem {A : Type u} [CommRing A] {ι : Type*} [Preorder ι]
    (D : ι ⥤ Under (CommRingCat.of A)) : RingMapSystemUnbundled ι where
  R _ := A
  S i := (D ⋙ Under.forget (CommRingCat.of A)).obj i
  commRingR := fun _ => inferInstance
  commRingS := fun _ => inferInstance
  fR := fun {_ _} _ => RingHom.id A
  fS := fun {_ _} h => ((D ⋙ Under.forget (CommRingCat.of A)).map (homOfLE h)).hom
  fR_id := fun _ _ => rfl
  fR_comp := fun {_ _ _} _ _ _ => rfl
  fS_id := fun i x => by
    change ((D ⋙ Under.forget (CommRingCat.of A)).map (𝟙 i)).hom x = x
    rw [CategoryTheory.Functor.map_id]
    rfl
  fS_comp := fun {_ _ _} hij hjk x =>
    congrArg (fun f : CommRingCat.Hom _ _ => f.hom x)
      ((D ⋙ Under.forget (CommRingCat.of A)).map_comp (homOfLE hij) (homOfLE hjk)).symm
  g := fun i => (D.obj i).hom.hom
  square := fun {i j} h x => by
    have hw := Under.w (D.map (homOfLE h))
    change (D.obj i).hom ≫ (D.map (homOfLE h)).right = (D.obj j).hom at hw
    exact congrArg (fun f : CommRingCat.Hom _ _ => f.hom x) hw

/-- A diagram of smooth `A`-algebras has injective naive cotangent differential at every
stage. -/
theorem underRingMapSystem_cotangentComplex_injective {A : Type u} [CommRing A] {ι : Type*}
    [Preorder ι] (D : ι ⥤ Under (CommRingCat.of A)) (hD : ∀ i, (D.obj i).hom.hom.Smooth)
    (i : ι) : Function.Injective ((underRingMapSystem D).NL i).cotangentComplex := by
  let : Algebra A ((underRingMapSystem D).S i) := ((underRingMapSystem D).g i).toAlgebra
  have hsm : Algebra.FormallySmooth A ((underRingMapSystem D).S i) :=
    (RingHom.smooth_algebraMap.mp (hD i)).formallySmooth
  have : Algebra.FormallySmooth ((underRingMapSystem D).R i)
      ((underRingMapSystem D).NL i).Ring := by
    change Algebra.FormallySmooth A (MvPolynomial ((underRingMapSystem D).S i) A)
    infer_instance
  exact (Algebra.Extension.cotangentComplex_injective_iff ((underRingMapSystem D).NL i)).mpr
    hsm.subsingleton_h1Cotangent

/-- An algebra that is a filtered colimit of smooth algebras and whose module of differentials
vanishes is formally smooth: the naive cotangent complex commutes with the colimit, its
differential is injective at each smooth stage, hence injective in the colimit, so
`H¹` vanishes; the vanishing of `Ω` makes it projective. -/
public theorem formallySmooth_of_indSmooth_of_formallyUnramified (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B] (hind : Stacks.Smoothing.IndSmooth A B)
    [Algebra.FormallyUnramified A B] : Algebra.FormallySmooth A B := by
  classical
  obtain ⟨J, _, _, pres, hstage⟩ := hind
  obtain ⟨ι, _, _, _, F, hfinal⟩ := IsFiltered.exists_directed J
  have : IsConnected ι := IsFiltered.isConnected ι
  let q := pres.reindex F
  let cB := (Under.forget (CommRingCat.of A)).mapCocone q.cocone
  let sys := underRingMapSystem q.diag
  obtain ⟨eA, heA⟩ := exists_ringEquiv_directLimit _ _ (isColimitConstCocone ι (CommRingCat.of A))
  obtain ⟨eB, heB⟩ := exists_ringEquiv_directLimit (q.diag ⋙ Under.forget (CommRingCat.of A)) cB
    (isColimitOfPreserves _ q.isColimit)
  have hcompat (x : sys.Rinf) : eB (sys.gInf x) = q.cocone.pt.hom.hom (eA x) := by
    refine Ring.DirectLimit.induction_on x fun i a => ?_
    have heA' : eA (sys.toRinf i a) = a := heA i a
    rw [show Ring.DirectLimit.of sys.R (fun _ _ h => sys.fR h) i a = sys.toRinf i a from rfl,
      ← sys.toSinf_g i a]
    refine (heB i (sys.g i a)).trans ?_
    change (cB.ι.app i).hom (sys.g i a) = q.cocone.pt.hom.hom (eA (sys.toRinf i a))
    rw [heA']
    exact ConcreteCategory.congr_hom (Under.w (q.cocone.ι.app i)) a
  let : Algebra A sys.Rinf := eA.symm.toRingHom.toAlgebra
  let : Algebra A sys.Sinf := (sys.gInf.comp eA.symm.toRingHom).toAlgebra
  have : IsScalarTower A sys.Rinf sys.Sinf := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let eBAlg : sys.Sinf ≃ₐ[A] B :=
    AlgEquiv.ofRingEquiv (f := eB) fun a => by
      change eB (sys.gInf (eA.symm a)) = q.cocone.pt.hom.hom a
      exact (hcompat _).trans (congrArg _ (eA.apply_symm_apply a))
  have : Algebra.FormallyUnramified A sys.Sinf := .of_equiv eBAlg.symm
  have : Algebra.FormallyUnramified sys.Rinf sys.Sinf := .of_restrictScalars A _ _
  have : Algebra.FormallySmooth sys.Rinf sys.Sinf :=
    ⟨inferInstance, (Algebra.Extension.subsingleton_h1Cotangent sys.NLinf).mpr
      (cotangentComplex_NLinf_injective sys
        (underRingMapSystem_cotangentComplex_injective q.diag fun i => hstage (F.obj i)))⟩
  let eAR : A ≃ₐ[A] sys.Rinf := AlgEquiv.ofRingEquiv (f := eA.symm) fun _ => rfl
  have : Algebra.FormallyEtale A sys.Rinf := .of_equiv eAR
  have : Algebra.FormallySmooth A sys.Sinf := .comp A sys.Rinf sys.Sinf
  exact Algebra.FormallySmooth.of_equiv eBAlg

/-! ### Excellence and formal étaleness of the completion map -/

/-- A regular ring homomorphism, in the sense of Tag `07BZ`, is a regular ring map in the sense
of Situation `07F2`: the two formulations differ only by cancelling the base change of the
residue field into a finite extension of it. -/
private theorem isRegularRingMap_of_isRegularRingHom (R : Type u) (Λ : Type u) [CommRing R]
    [CommRing Λ] [Algebra R Λ] (h : IsRegularRingHom (algebraMap R Λ)) :
    Stacks.Smoothing.IsRegularRingMap R Λ := by
  rw [isRegularRingHom_algebraMap_iff] at h
  refine ⟨RingHom.flat_algebraMap_iff.mp h.1, fun p hp K _ _ _ => ?_⟩
  let : Algebra R K :=
    ((algebraMap p.ResidueField K).comp (algebraMap R p.ResidueField)).toAlgebra
  have : IsScalarTower R p.ResidueField K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra Λ (p.Fiber Λ) := Algebra.TensorProduct.rightAlgebra
  let : Algebra p.ResidueField (p.Fiber Λ) := Algebra.TensorProduct.leftAlgebra
  let : Algebra K (K ⊗[p.ResidueField] p.Fiber Λ) := Algebra.TensorProduct.leftAlgebra
  let : Algebra (p.Fiber Λ) (K ⊗[p.ResidueField] p.Fiber Λ) :=
    Algebra.TensorProduct.rightAlgebra
  let e := Algebra.TensorProduct.cancelBaseChange R p.ResidueField K K Λ
  have hNoeth : IsNoetherianRing (K ⊗[R] Λ) := by
    have : IsNoetherianRing (p.Fiber Λ) := (h.2 p).1
    have : IsNoetherianRing (p.Fiber Λ ⊗[p.ResidueField] K) :=
      Algebra.FiniteType.isNoetherianRing (p.Fiber Λ) (p.Fiber Λ ⊗[p.ResidueField] K)
    have : IsNoetherianRing (K ⊗[p.ResidueField] p.Fiber Λ) :=
      isNoetherianRing_of_ringEquiv _
        (Algebra.TensorProduct.comm p.ResidueField (p.Fiber Λ) K).toRingEquiv
    exact isNoetherianRing_of_ringEquiv _ e.toRingEquiv
  have : IsRegularRing (K ⊗[p.ResidueField] p.Fiber Λ) :=
    (h.2 p).2.isRegularRing_tensorProduct K
  exact ⟨hNoeth, IsRegularRing.of_ringEquiv e.toRingEquiv⟩

/-- For a regular Noetherian local ring of prime characteristic whose residue field has finite
imperfection degree, failure of excellence makes the canonical map to the maximal-ideal-adic
completion fail to be formally étale. -/
public theorem not_formallyEtale_adicCompletion_of_not_isExcellent
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (p : ℕ) [Fact p.Prime] [CharP A p]
    [Module.Finite (frobenius (ResidueField A) (ringExpChar (ResidueField A))).fieldRange
      (ResidueField A)] (hA : ¬ IsExcellent A) :
    ¬ Algebra.FormallyEtale A (AdicCompletion (maximalIdeal A) A) := fun _ =>
  hA (isExcellent_of_isGRing_of_isRegularLocalRing A (isGRing_of_formallySmooth_adicCompletion A))

/-- Let `(A, 𝔪, κ)` be a Noetherian local ring of prime characteristic `p` with
`[κ : κᵖ] < ∞`. Then the canonical map `A → A^∧` to the `𝔪`-adic completion is flat and
formally unramified; if moreover `A` is regular but not excellent, it is not formally étale. -/
@[stacks 0G66]
public theorem flat_formallyUnramified_adicCompletion_and_not_formallyEtale
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (p : ℕ) [Fact p.Prime]
    [CharP A p]
    [Module.Finite (frobenius (ResidueField A) (ringExpChar (ResidueField A))).fieldRange
      (ResidueField A)] :
    Module.Flat A (AdicCompletion (maximalIdeal A) A) ∧
      Algebra.FormallyUnramified A (AdicCompletion (maximalIdeal A) A) ∧
      (IsRegularLocalRing A → ¬ IsExcellent A →
        ¬ Algebra.FormallyEtale A (AdicCompletion (maximalIdeal A) A)) :=
  ⟨AdicCompletion.flat_of_isNoetherian (maximalIdeal A),
    formallyUnramified_adicCompletion_maximalIdeal A p,
    fun _ hA => not_formallyEtale_adicCompletion_of_not_isExcellent A p hA⟩

/-- The forward implication of Stacks `0G68`: for a regular local ring of characteristic
`p > 0` whose residue field has finite imperfection degree, excellence makes the canonical map
to the maximal-ideal-adic completion formally étale.

This needs none of Lemma `0G66`: excellence makes the map regular, Néron–Popescu writes the
completion as a filtered colimit of smooth algebras, and formal unramifiedness upgrades that to
formal smoothness. -/
@[stacks 0G68 "the forward implication, with no carried hypotheses; see the module docstring"]
public theorem formallyEtale_adicCompletion_of_isExcellent
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (p : ℕ) [Fact p.Prime] [CharP A p]
    [Module.Finite (frobenius (ResidueField A) (ringExpChar (ResidueField A))).fieldRange
      (ResidueField A)] (excellent : IsExcellent A) :
    Algebra.FormallyEtale A (AdicCompletion (maximalIdeal A) A) := by
  have := formallyUnramified_adicCompletion_maximalIdeal A p
  have : Algebra.FormallySmooth A (AdicCompletion (maximalIdeal A) A) :=
    formallySmooth_of_indSmooth_of_formallyUnramified A _ <|
      Stacks.Smoothing.indSmooth_of_isRegularRingMap A _ <|
        isRegularRingMap_of_isRegularRingHom A _ <|
          isRegularRingHom_algebraMap_adicCompletion excellent.1.2.1 (maximalIdeal A)
  exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth

/-- A regular local ring of characteristic `p > 0` whose residue field has finite imperfection
degree is excellent if and only if the canonical map to its maximal-ideal-adic completion is
formally étale. -/
@[stacks 0G68 "both directions, with no carried hypotheses"]
public theorem isExcellent_iff_formallyEtale_adicCompletion_maximalIdeal
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (p : ℕ) [Fact p.Prime] [CharP A p]
    [Module.Finite (frobenius (ResidueField A) (ringExpChar (ResidueField A))).fieldRange
      (ResidueField A)] :
    IsExcellent A ↔ Algebra.FormallyEtale A (AdicCompletion (maximalIdeal A) A) :=
  ⟨formallyEtale_adicCompletion_of_isExcellent A p,
    not_imp_not.mp (not_formallyEtale_adicCompletion_of_not_isExcellent A p)⟩

end Stacks.Examples

end
