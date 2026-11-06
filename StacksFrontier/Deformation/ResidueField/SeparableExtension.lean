module

public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Henselian
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.ResidueField.Basic
public import StacksFrontier.Deformation.TangentSpace.SquareZero
public import StacksFrontier.RingTheory.AdicCompletion.TateModule.FiniteComplete
public import StacksFrontier.RingTheory.NoetherNormalization.Basic

/-!
# Extending the residue field of a complete local algebra along a separable extension

Let `Λ → k → l` be a finite tower of fields over a Noetherian ring (a
`Deformation.ChangeOfFieldsSituation`) with `l/k` separable, and let `R` be a Noetherian complete
local `Λ`-algebra with residue field `k`. Choose a primitive element `θ` of `l/k` with minimal
polynomial `f`, and a monic lift `F ∈ R[X]` of `f`. Then `R_l = R[X]/(F)` is a Noetherian complete
local `Λ`-algebra with residue field `l`, finite and free over `R`, so of the same dimension.

## Main definitions

* `Deformation.SeparableExtension.ring`: the ring `R[X]/(F)`.

## Main results

* `Deformation.SeparableExtension.isLocalRing`, `isNoetherianRing`, `isAdicComplete`,
  `maximalIdeal_eq_ker`: `R_l` is a Noetherian complete local ring, whose maximal ideal is the
  kernel of the evaluation `R_l → l` at `θ`.
* `Deformation.SeparableExtension.ringKrullDim_eq`: `dim R_l = dim R`.
* `Deformation.SeparableExtension.restrictedCoyonedaIso`: `R_l` prorepresents the functor
  `T ↦ Hom(R, T ×_l k)` on `𝒞_{Λ,l}`, the change of residue field of the functor prorepresented by
  `R` (Stacks 07W8). A point of `R_l` restricts to `R`; conversely a point `a` of `R` with values
  in `T ×_l k` extends uniquely, the adjoined root going to the unique root of `F^a` in `T` with
  residue `θ` (Hensel's lemma for the Artinian, hence Henselian, local ring `T`, with uniqueness
  because `θ` is a simple root of `f`).
-/

@[expose] public section

open CategoryTheory IsLocalRing Polynomial

universe u

namespace Deformation

namespace SeparableExtension

variable (S : ChangeOfFieldsSituation.{u, u, u}) [Algebra.IsSeparable S.k S.l]

/-- A primitive element of the separable extension `l/k`. -/
noncomputable def θ : S.l := (Field.exists_primitive_element S.k S.l).choose

/-- The primitive element `θ` generates `l` as a field over `k`. -/
theorem adjoin_θ : IntermediateField.adjoin S.k {θ S} = ⊤ :=
  (Field.exists_primitive_element S.k S.l).choose_spec

/-- The primitive element `θ` is integral over `k`. -/
theorem isIntegral_θ : IsIntegral S.k (θ S) := Algebra.IsIntegral.isIntegral _

/-- The primitive element `θ` generates `l` as a `k`-algebra. -/
theorem algebra_adjoin_θ : Algebra.adjoin S.k {θ S} = ⊤ := by
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (isIntegral_θ S).isAlgebraic,
    adjoin_θ S, IntermediateField.top_toSubalgebra]

variable (R : CompleteLocalAlgCat.{u, u, u} S.Λ S.k)

/-- A monic lift to `R[X]` of the minimal polynomial of `θ`. -/
noncomputable def F : R[X] :=
  (lifts_and_natDegree_eq_and_monic
    (mem_lifts_of_surjective (f := (residueHom R).toRingHom)
      (fun c => by
        obtain ⟨y, hy⟩ := R.residueEquiv.surjective c
        obtain ⟨a, rfl⟩ := residue_surjective y
        exact ⟨a, hy⟩) (minpoly S.k (θ S)))
    (minpoly.monic (isIntegral_θ S))).choose

/-- The reduction of `F` modulo the maximal ideal of `R` is the minimal polynomial of `θ`. -/
theorem F_map : (F S R).map (residueHom R).toRingHom = minpoly S.k (θ S) :=
  (lifts_and_natDegree_eq_and_monic
    (mem_lifts_of_surjective (f := (residueHom R).toRingHom)
      (fun c => by
        obtain ⟨y, hy⟩ := R.residueEquiv.surjective c
        obtain ⟨a, rfl⟩ := residue_surjective y
        exact ⟨a, hy⟩) (minpoly S.k (θ S)))
    (minpoly.monic (isIntegral_θ S))).choose_spec.1

/-- The polynomial `F` is monic. -/
theorem F_monic : (F S R).Monic :=
  (lifts_and_natDegree_eq_and_monic
    (mem_lifts_of_surjective (f := (residueHom R).toRingHom)
      (fun c => by
        obtain ⟨y, hy⟩ := R.residueEquiv.surjective c
        obtain ⟨a, rfl⟩ := residue_surjective y
        exact ⟨a, hy⟩) (minpoly S.k (θ S)))
    (minpoly.monic (isIntegral_θ S))).choose_spec.2.2

/-- The polynomial `F` has positive degree. -/
theorem F_degree_pos : 0 < (F S R).degree := by
  have h := congrArg Polynomial.natDegree (F_map S R)
  rw [(F_monic S R).natDegree_map] at h
  rw [← Polynomial.natDegree_pos_iff_degree_pos, h]
  exact minpoly.natDegree_pos (isIntegral_θ S)

/-- The ring `R[X]/(F)`. -/
abbrev ring := AdjoinRoot (F S R)

/-- `R[X]/(F)` is a finite `R`-module. -/
instance : Module.Finite R (ring S R) := (F_monic S R).finite_adjoinRoot

/-- `R[X]/(F)` is integral over `R`. -/
instance : Algebra.IsIntegral R (ring S R) := Algebra.IsIntegral.of_finite R _

/-- The structure map `R → R[X]/(F)` is injective. -/
theorem algebraMap_injective : Function.Injective (algebraMap R (ring S R)) :=
  AdjoinRoot.of.injective_of_monic_of_degree_pos (F_monic S R) (F_degree_pos S R)

/-- The evaluation `R_l → l` at `θ`. -/
noncomputable def toL : ring S R →+* S.l :=
  AdjoinRoot.lift ((algebraMap S.k S.l).comp (residueHom R).toRingHom) (θ S) (by
    rw [← Polynomial.eval₂_map, F_map, ← Polynomial.aeval_def]
    exact minpoly.aeval S.k (θ S))

/-- On `R`, the evaluation `R_l → l` is the residue map of `R` followed by `k → l`. -/
@[simp] theorem toL_of (r : R) :
    toL S R (AdjoinRoot.of (F S R) r) = algebraMap S.k S.l (residueHom R r) :=
  AdjoinRoot.lift_of _

/-- The evaluation `R_l → l` sends the adjoined root to `θ`. -/
@[simp] theorem toL_root : toL S R (AdjoinRoot.root (F S R)) = θ S := AdjoinRoot.lift_root _

/-- The evaluation `R_l → l` is surjective. -/
theorem toL_surjective : Function.Surjective (toL S R) := by
  intro y
  have hy : y ∈ Algebra.adjoin S.k {θ S} := algebra_adjoin_θ S ▸ Algebra.mem_top
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨_, hx ▸ toL_root S R⟩
  | algebraMap c =>
    obtain ⟨y, hy⟩ := R.residueEquiv.surjective c
    obtain ⟨a, rfl⟩ := residue_surjective y
    refine ⟨AdjoinRoot.of (F S R) a, ?_⟩
    rw [toL_of]
    change algebraMap S.k S.l (R.residueEquiv (residue R a)) = _
    rw [hy]
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, map_mul _ _ _⟩

/-- The kernel of the evaluation `R_l → l` is a maximal ideal. -/
theorem ker_toL_isMaximal : (RingHom.ker (toL S R)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (toL_surjective S R)

/-- The extension of the maximal ideal of `R` is maximal in `R_l`: the quotient is `k[X]/(f)`,
a field. -/
theorem map_maximalIdeal_isMaximal :
    ((maximalIdeal R).map (algebraMap R (ring S R))).IsMaximal := by
  let m := maximalIdeal R
  let q : (R ⧸ m)[X] := (F S R).map (Ideal.Quotient.mk m)
  let e : R ⧸ m ≃+* S.k := R.residueEquiv.toRingEquiv
  have he : (e : R ⧸ m →+* S.k).comp (Ideal.Quotient.mk m) = (residueHom R).toRingHom :=
    RingHom.ext fun _ => rfl
  have hq : Irreducible q := (MulEquiv.irreducible_iff (Polynomial.mapEquiv e)).mp <| by
    rw [Polynomial.mapEquiv_apply, Polynomial.map_map, he, F_map S R]
    exact minpoly.irreducible (isIntegral_θ S)
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  exact Ideal.Quotient.maximal_of_isField _ <| MulEquiv.isField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp
      (PrincipalIdealRing.isMaximal_of_irreducible hq))
    (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot m (F S R)).toMulEquiv

/-- Every maximal ideal of `R_l` contains the extension of the maximal ideal of `R`. -/
theorem map_maximalIdeal_le_of_isMaximal (N : Ideal (ring S R)) (hN : N.IsMaximal) :
    (maximalIdeal R).map (algebraMap R (ring S R)) ≤ N := by
  have hc : (N.comap (algebraMap R (ring S R))).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) N
  rw [Ideal.map_le_iff_le_comap, IsLocalRing.eq_maximalIdeal hc]

/-- The extension of the maximal ideal of `R` lies in the kernel of the evaluation `R_l → l`. -/
theorem map_maximalIdeal_le_ker : (maximalIdeal R).map (algebraMap R (ring S R)) ≤
    RingHom.ker (toL S R) :=
  map_maximalIdeal_le_of_isMaximal S R _ (ker_toL_isMaximal S R)

/-- Every maximal ideal of `R_l` is the extension of the maximal ideal of `R`. -/
theorem eq_map_maximalIdeal_of_isMaximal (N : Ideal (ring S R)) (hN : N.IsMaximal) :
    N = (maximalIdeal R).map (algebraMap R (ring S R)) :=
  ((map_maximalIdeal_isMaximal S R).eq_of_le hN.ne_top
    (map_maximalIdeal_le_of_isMaximal S R N hN)).symm

/-- `R_l` is a local ring. -/
instance isLocalRing : IsLocalRing (ring S R) :=
  IsLocalRing.of_unique_max_ideal
    ⟨_, map_maximalIdeal_isMaximal S R, eq_map_maximalIdeal_of_isMaximal S R⟩

/-- The maximal ideal of `R_l` is the extension of the maximal ideal of `R`. -/
theorem maximalIdeal_eq_map : maximalIdeal (ring S R) =
    (maximalIdeal R).map (algebraMap R (ring S R)) :=
  eq_map_maximalIdeal_of_isMaximal S R _ (maximalIdeal.isMaximal _)

/-- The maximal ideal of `R_l` is the kernel of the evaluation `R_l → l`. -/
theorem maximalIdeal_eq_ker : maximalIdeal (ring S R) = RingHom.ker (toL S R) :=
  (maximalIdeal_eq_map S R).trans
    ((map_maximalIdeal_isMaximal S R).eq_of_le (ker_toL_isMaximal S R).ne_top
      (map_maximalIdeal_le_ker S R))

/-- `R_l` is a Noetherian ring. -/
instance isNoetherianRing : IsNoetherianRing (ring S R) := inferInstance

/-- `R_l` is complete with respect to its maximal ideal. -/
instance isAdicComplete : IsAdicComplete (maximalIdeal (ring S R)) (ring S R) := by
  rw [maximalIdeal_eq_map]
  exact (IsAdicComplete.map_algebraMap_iff (maximalIdeal R) (ring S R)).mpr
    (AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing (maximalIdeal R) (ring S R))

/-- `R_l` has the same Krull dimension as `R`. -/
theorem ringKrullDim_eq : ringKrullDim (ring S R) = ringKrullDim R :=
  (ringKrullDim_eq_of_injective_isIntegral (algebraMap R (ring S R)) (algebraMap_injective S R)
    (algebraMap_isIntegral_iff.mpr inferInstance)).symm

/-! ### The complete local algebra with residue field `l` -/

/-- The evaluation `R_l → l` commutes with the structure maps from `Λ`. -/
theorem toL_algebraMap (a : S.Λ) :
    toL S R (algebraMap S.Λ (ring S R) a) = algebraMap S.Λ S.l a := by
  rw [IsScalarTower.algebraMap_apply S.Λ R (ring S R), AdjoinRoot.algebraMap_eq, toL_of,
    AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

/-- The identification of the residue field of `R_l` with `l`, through evaluation at `θ`. -/
noncomputable def residueEquiv : ResidueField (ring S R) ≃ₐ[S.Λ] S.l :=
  AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq (maximalIdeal_eq_ker S R)).trans
    (RingHom.quotientKerEquivOfSurjective (toL_surjective S R))) (toL_algebraMap S R)

/-- Under `residueEquiv`, the residue class of `z` is the evaluation of `z` at `θ`. -/
theorem residueEquiv_residue (z : ring S R) : residueEquiv S R (residue (ring S R) z) = toL S R z :=
  rfl

/-- **The extension of `R` with residue field `l`**, as a Noetherian complete local `Λ`-algebra. -/
noncomputable def obj : CompleteLocalAlgCat.{u, u, u} S.Λ S.l where
  carrier := ring S R
  completeLocal := ⟨inferInstance, inferInstance, inferInstance⟩
  residueEquiv := residueEquiv S R

/-- The extension `obj S R` has the same Krull dimension as `R`. -/
theorem ringKrullDim_obj : ringKrullDim (obj S R) = ringKrullDim R := ringKrullDim_eq S R

/-! ### The universal property -/

/-- The first projection `T ×_l k ⟶ T` of the comparison algebra. -/
noncomputable def proj (T : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l) :
    (comparisonFunctor S).functor.obj T →+* T :=
  (RingHom.pullbackFst (residueMap S T) (algebraMap S.k S.l)).comp
    ((comparisonFunctor S).pullbackEquiv T).toRingHom

omit [Algebra.IsSeparable S.k S.l] in
/-- The residue in `l` of the first projection of `x ∈ T ×_l k` is the image in `l` of the residue
of `x` in `k`. -/
theorem residueMap_proj (T : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l)
    (x : (comparisonFunctor S).functor.obj T) :
    residueMap S T (proj S T x) =
      algebraMap S.k S.l (((comparisonFunctor S).functor.obj T).residueEquiv
        (residue ((comparisonFunctor S).functor.obj T) x)) := by
  rw [(comparisonFunctor S).residue_snd]
  exact ((comparisonFunctor S).pullbackEquiv T x).property

omit [Algebra.IsSeparable S.k S.l] in
/-- The composite of a point of `R` over `T ×_l k` with the projection to `T` reduces, modulo the
maximal ideal of `T`, to the residue map of `R` followed by `k → l`. -/
theorem residueMap_proj_comp (T : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l)
    (α : R ⟶ artinianToComplete.obj ((comparisonFunctor S).functor.obj T)) :
    (residueMap S T).comp ((proj S T).comp α.hom.toRingHom) =
      (algebraMap S.k S.l).comp (residueHom R).toRingHom := by
  ext r
  exact (residueMap_proj S T _).trans (congrArg (algebraMap S.k S.l) (α.residue_comm r))

omit [Algebra.IsSeparable S.k S.l] in
/-- Reduction modulo the maximal ideal of `T` commutes with evaluation of polynomials. -/
theorem residueMap_eval (T : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l) (G : T[X]) (y : T) :
    residueMap S T (G.eval y) = (G.map (residueMap S T)).eval (residueMap S T y) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_hom]

/-- For a ring map `a : R → T` lifting `R → k → l`, the reduction of `F^a` modulo the maximal ideal
of `T` is the minimal polynomial of `θ`, viewed over `l`. -/
theorem map_residueMap_eq (T : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l) (a : R →+* T)
    (ha : (residueMap S T).comp a = (algebraMap S.k S.l).comp (residueHom R).toRingHom) :
    ((F S R).map a).map (residueMap S T) = (minpoly S.k (θ S)).map (algebraMap S.k S.l) := by
  rw [Polynomial.map_map, ha, ← Polynomial.map_map, F_map]

/-- **Hensel's lemma at a point.** For a ring map `a : R → T` lifting `R → k → l`, the polynomial
`F^a` has a root in `T` with residue `θ`. -/
theorem exists_root (T : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l) (a : R →+* T)
    (ha : (residueMap S T).comp a = (algebraMap S.k S.l).comp (residueHom R).toRingHom) :
    ∃ y : T, ((F S R).map a).IsRoot y ∧ residueMap S T y = θ S := by
  obtain ⟨y₀, hy₀⟩ : ∃ y : T, residueMap S T y = θ S :=
    (T.residueEquiv.surjective.comp residue_surjective) _
  have hmap := map_residueMap_eq S R T a ha
  have hsep : (minpoly S.k (θ S)).Separable := Algebra.IsSeparable.isSeparable S.k (θ S)
  have hroot : residueMap S T (((F S R).map a).eval y₀) = 0 := by
    rw [residueMap_eval, hmap, hy₀, Polynomial.eval_map_algebraMap, minpoly.aeval]
  have hder : residueMap S T ((((F S R).map a).derivative).eval y₀) ≠ 0 := by
    rw [residueMap_eval, ← Polynomial.derivative_map, hmap, hy₀, Polynomial.derivative_map,
      Polynomial.eval_map_algebraMap]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval S.k (θ S))
  have hmem : ∀ t : T, residueMap S T t = 0 ↔ t ∈ maximalIdeal T := by
    intro t
    change T.residueEquiv (residue T t) = 0 ↔ _
    rw [map_eq_zero_iff _ T.residueEquiv.injective, residue_eq_zero_iff]
  have hH : HenselianRing T (maximalIdeal T) := inferInstance
  obtain ⟨y, hy, hyy₀⟩ := hH.is_henselian ((F S R).map a) ((F_monic S R).map a) y₀
    ((hmem _).mp hroot)
    ((IsLocalRing.notMem_maximalIdeal.mp (fun h => hder ((hmem _).mpr h))).map _)
  refine ⟨y, hy, ?_⟩
  have : residueMap S T (y - y₀) = 0 := (hmem _).mpr hyy₀
  rwa [map_sub, sub_eq_zero, hy₀] at this

/-- **Uniqueness of the root.** Two roots of `F^a` with the same residue agree. -/
theorem root_unique (T : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l) (a : R →+* T)
    (ha : (residueMap S T).comp a = (algebraMap S.k S.l).comp (residueHom R).toRingHom)
    {y y' : T} (hy : ((F S R).map a).IsRoot y) (hy' : ((F S R).map a).IsRoot y')
    (hθ : residueMap S T y = θ S) (hθ' : residueMap S T y' = θ S) : y = y' := by
  have hmap := map_residueMap_eq S R T a ha
  have hsep : (minpoly S.k (θ S)).Separable := Algebra.IsSeparable.isSeparable S.k (θ S)
  have hmem : ∀ t : T, residueMap S T t = 0 ↔ t ∈ maximalIdeal T := by
    intro t
    change T.residueEquiv (residue T t) = 0 ↔ _
    rw [map_eq_zero_iff _ T.residueEquiv.injective, residue_eq_zero_iff]
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hy hy' ?_ ?_
  · rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← hmem, map_sub, hθ, hθ', sub_self]
  · by_contra hu
    rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← hmem] at hu
    rw [residueMap_eval, ← Polynomial.derivative_map, hmap, hθ, Polynomial.derivative_map,
      Polynomial.eval_map_algebraMap] at hu
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval S.k (θ S)) hu

omit [Algebra.IsSeparable S.k S.l] in
/-- The image of `c ∈ Λ` in `T ×_l k` has components the images of `c` in `T` and in `k`. -/
theorem pullbackEquiv_algebraMap_val (T : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l) (c : S.Λ) :
    ((comparisonFunctor S).pullbackEquiv T
      (algebraMap S.Λ ((comparisonFunctor S).functor.obj T) c)).val =
      (algebraMap S.Λ T c, algebraMap S.Λ S.k c) :=
  Prod.ext ((comparisonFunctor S).algebraMap_fst T c) ((comparisonFunctor S).algebraMap_snd T c)

/-- The ring map `R → T ×_l k`, `r ↦ (β(r), r mod 𝔪)`, attached to a point `β` of `R_l`. -/
noncomputable def restrictRingHom (T : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l)
    (β : obj S R ⟶ artinianToComplete.obj T) :
    R →+* (comparisonFunctor S).functor.obj T :=
  ((comparisonFunctor S).pullbackEquiv T).symm.toRingHom.comp
    (RingHom.codRestrict (((β.hom.toRingHom.comp (AdjoinRoot.of (F S R))) : R →+* T).prod
      (residueHom R).toRingHom) _
      (fun r => by
        change T.residueEquiv (residue T (β.hom (AdjoinRoot.of (F S R) r))) =
          algebraMap S.k S.l (residueHom R r)
        exact (β.residue_comm _).trans (toL_of S R r)))

/-- The components of `restrictRingHom S R T β r` in `T ×_l k` are `β(r)` and the residue of
`r`. -/
theorem pullbackEquiv_restrictRingHom_val (T : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l)
    (β : obj S R ⟶ artinianToComplete.obj T) (r : R) :
    ((comparisonFunctor S).pullbackEquiv T (restrictRingHom S R T β r)).val =
      (β.hom (AdjoinRoot.of (F S R) r), residueHom R r) := by
  simp only [restrictRingHom, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  rfl

/-- The point of `R` with values in `T ×_l k` underlying a point of `R_l` with values in `T`. -/
noncomputable def restrictPoint (T : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l)
    (β : obj S R ⟶ artinianToComplete.obj T) :
    R ⟶ artinianToComplete.obj ((comparisonFunctor S).functor.obj T) where
  hom :=
    { toRingHom := restrictRingHom S R T β
      commutes' := fun c => by
        apply ((comparisonFunctor S).pullbackEquiv T).injective
        apply Subtype.ext
        change ((comparisonFunctor S).pullbackEquiv T
          (restrictRingHom S R T β (algebraMap S.Λ R c))).val =
          ((comparisonFunctor S).pullbackEquiv T
            (algebraMap S.Λ ((comparisonFunctor S).functor.obj T) c)).val
        rw [pullbackEquiv_restrictRingHom_val, pullbackEquiv_algebraMap_val]
        refine Prod.ext ?_ ((residueHom R).commutes c)
        change β.hom (AdjoinRoot.of (F S R) (algebraMap S.Λ R c)) = algebraMap S.Λ T c
        rw [← AdjoinRoot.algebraMap_eq]
        exact (congrArg β.hom (IsScalarTower.algebraMap_apply S.Λ R (ring S R) c).symm).trans
          (β.hom.commutes c) }
  isLocal := ⟨fun r hu => by
    by_contra hr
    have h0 : residueHom R r = 0 := by
      change R.residueEquiv (residue R r) = 0
      rw [(residue_eq_zero_iff r).mpr ((mem_maximalIdeal r).mpr hr), map_zero]
    have h1 : ((comparisonFunctor S).functor.obj T).residueEquiv
        (residue ((comparisonFunctor S).functor.obj T) (restrictRingHom S R T β r)) = 0 := by
      rw [(comparisonFunctor S).residue_snd, pullbackEquiv_restrictRingHom_val]
      exact h0
    rw [map_eq_zero_iff _ (AlgEquiv.injective _), residue_eq_zero_iff, mem_maximalIdeal,
      mem_nonunits_iff] at h1
    exact h1 hu⟩
  residue_comm := fun r => by
    change ((comparisonFunctor S).functor.obj T).residueEquiv
        (residue ((comparisonFunctor S).functor.obj T) (restrictRingHom S R T β r)) = _
    rw [(comparisonFunctor S).residue_snd, pullbackEquiv_restrictRingHom_val]
    rfl

/-- The first projection of the restriction of a point `β` of `R_l` agrees with `β` on `R`. -/
theorem proj_restrictPoint (T : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l)
    (β : obj S R ⟶ artinianToComplete.obj T) (r : R) :
    proj S T ((restrictPoint S R T β).hom r) = β.hom (AdjoinRoot.of (F S R) r) :=
  congrArg Prod.fst (pullbackEquiv_restrictRingHom_val S R T β r)

/-- The point of `R_l` with values in `T` extending a point `α` of `R` with values in `T ×_l k`:
the adjoined root goes to the root of `F` with residue `θ` (Hensel). -/
noncomputable def extendRingHom (T : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l)
    (α : R ⟶ artinianToComplete.obj ((comparisonFunctor S).functor.obj T)) :
    ring S R →+* T :=
  AdjoinRoot.lift ((proj S T).comp α.hom.toRingHom)
    (exists_root S R T _ (residueMap_proj_comp S R T α)).choose (by
      rw [← Polynomial.eval_map]
      exact (exists_root S R T _ (residueMap_proj_comp S R T α)).choose_spec.1)

/-- On `R`, `extendRingHom S R T α` is `α` followed by the projection `T ×_l k → T`. -/
theorem extendRingHom_of (T : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l)
    (α : R ⟶ artinianToComplete.obj ((comparisonFunctor S).functor.obj T)) (r : R) :
    extendRingHom S R T α (AdjoinRoot.of (F S R) r) = proj S T (α.hom r) := AdjoinRoot.lift_of _

/-- `extendRingHom S R T α` sends the adjoined root to the chosen root of `F^a` in `T` with residue
`θ`. -/
theorem extendRingHom_root (T : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l)
    (α : R ⟶ artinianToComplete.obj ((comparisonFunctor S).functor.obj T)) :
    extendRingHom S R T α (AdjoinRoot.root (F S R)) =
      (exists_root S R T _ (residueMap_proj_comp S R T α)).choose :=
  AdjoinRoot.lift_root _

/-- The residue of `extendRingHom S R T α z` in `l` is the evaluation of `z` at `θ`. -/
theorem residueMap_extendRingHom (T : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l)
    (α : R ⟶ artinianToComplete.obj ((comparisonFunctor S).functor.obj T)) (z : ring S R) :
    residueMap S T (extendRingHom S R T α z) = toL S R z := by
  have h : (residueMap S T).comp (extendRingHom S R T α) = toL S R := by
    apply AdjoinRoot.ringHom_ext
    · ext r
      simp only [RingHom.comp_apply, extendRingHom_of, toL_of]
      exact RingHom.congr_fun (residueMap_proj_comp S R T α) r
    · simp only [RingHom.comp_apply, extendRingHom_root, toL_root]
      exact (exists_root S R T _ (residueMap_proj_comp S R T α)).choose_spec.2
  exact RingHom.congr_fun h z

/-- The point of `R_l` with values in `T` extending a point of `R` with values in `T ×_l k`. -/
noncomputable def extendPoint (T : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l)
    (α : R ⟶ artinianToComplete.obj ((comparisonFunctor S).functor.obj T)) :
    obj S R ⟶ artinianToComplete.obj T where
  hom :=
    { toRingHom := extendRingHom S R T α
      commutes' := fun c => by
        change extendRingHom S R T α (algebraMap S.Λ (ring S R) c) = algebraMap S.Λ T c
        rw [IsScalarTower.algebraMap_apply S.Λ R (ring S R), AdjoinRoot.algebraMap_eq,
          extendRingHom_of, AlgHom.commutes]
        exact congrArg Prod.fst (pullbackEquiv_algebraMap_val S T c) }
  isLocal := ⟨fun (z : ring S R) hu => by
    by_contra hz
    have h1 : T.residueEquiv (residue T (extendRingHom S R T α z)) = 0 :=
      (residueMap_extendRingHom S R T α z).trans
        (RingHom.mem_ker.mp ((maximalIdeal_eq_ker S R).le ((mem_maximalIdeal z).mpr hz)))
    rw [map_eq_zero_iff _ (AlgEquiv.injective _), residue_eq_zero_iff, mem_maximalIdeal,
      mem_nonunits_iff] at h1
    exact h1 hu⟩
  residue_comm := fun (z : ring S R) => residueMap_extendRingHom S R T α z

/-- Restricting the extension of a point `α` of `R` recovers `α`. -/
theorem restrictPoint_extendPoint (T : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l)
    (α : R ⟶ artinianToComplete.obj ((comparisonFunctor S).functor.obj T)) :
    restrictPoint S R T (extendPoint S R T α) = α := by
  apply CompleteLocalAlgCat.Hom.ext
  apply AlgHom.ext
  intro r
  apply ((comparisonFunctor S).pullbackEquiv T).injective
  apply Subtype.ext
  change ((comparisonFunctor S).pullbackEquiv T
    (restrictRingHom S R T (extendPoint S R T α) r)).val = _
  rw [pullbackEquiv_restrictRingHom_val]
  refine Prod.ext (extendRingHom_of S R T α r) ?_
  change residueHom R r = _
  rw [← (comparisonFunctor S).residue_snd]
  exact (α.residue_comm r).symm

/-- Extending the restriction of a point `β` of `R_l` recovers `β`. -/
theorem extendPoint_restrictPoint (T : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l)
    (β : obj S R ⟶ artinianToComplete.obj T) :
    extendPoint S R T (restrictPoint S R T β) = β := by
  apply CompleteLocalAlgCat.Hom.ext
  apply AlgHom.coe_ringHom_injective
  apply AdjoinRoot.ringHom_ext
  · ext r
    exact (extendRingHom_of S R T _ r).trans (proj_restrictPoint S R T β r)
  · change extendRingHom S R T (restrictPoint S R T β) (AdjoinRoot.root (F S R)) =
      β.hom (AdjoinRoot.root (F S R))
    rw [extendRingHom_root]
    let α := restrictPoint S R T β
    let a : R →+* T := (proj S T).comp α.hom.toRingHom
    have ha := residueMap_proj_comp S R T α
    have hy := (exists_root S R T a ha).choose_spec
    have ha' : a = (β.hom.toRingHom.comp (AdjoinRoot.of (F S R)) : R →+* T) :=
      RingHom.ext fun r => proj_restrictPoint S R T β r
    refine root_unique S R T a ha hy.1 ?_ hy.2 ?_
    · rw [Polynomial.IsRoot, Polynomial.eval_map, ha']
      let βr : ring S R →+* T := β.hom.toRingHom
      have h := Polynomial.hom_eval₂ (F S R) (AdjoinRoot.of (F S R)) βr (AdjoinRoot.root (F S R))
      rw [AdjoinRoot.eval₂_root, map_zero βr] at h
      exact h.symm
    · exact (β.residue_comm (AdjoinRoot.root (F S R))).trans (toL_root S R)

/-- Restriction of points of `R_l` to points of `R` is natural in `T`. -/
theorem restrictPoint_naturality {T T' : ArtinianLocalAlgCat.{u, u, u} S.Λ S.l} (f : T ⟶ T')
    (β : obj S R ⟶ artinianToComplete.obj T) :
    restrictPoint S R T' (β ≫ artinianToComplete.map f) =
      restrictPoint S R T β ≫ artinianToComplete.map ((comparisonFunctor S).functor.map f) := by
  apply CompleteLocalAlgCat.Hom.ext
  apply AlgHom.ext
  intro r
  apply ((comparisonFunctor S).pullbackEquiv T').injective
  apply Subtype.ext
  change ((comparisonFunctor S).pullbackEquiv T'
      (restrictRingHom S R T' (β ≫ artinianToComplete.map f) r)).val =
    ((comparisonFunctor S).pullbackEquiv T'
      (((comparisonFunctor S).functor.map f).hom (restrictRingHom S R T β r))).val
  rw [pullbackEquiv_restrictRingHom_val]
  refine Prod.ext ?_ ?_
  · rw [(comparisonFunctor S).map_fst]
    exact congrArg f.hom (proj_restrictPoint S R T β r).symm
  · rw [(comparisonFunctor S).map_snd]
    exact (congrArg Prod.snd (pullbackEquiv_restrictRingHom_val S R T β r)).symm

/-- **The extension prorepresents the change of residue field.** For a separable extension `l/k`
the functor `T ↦ Hom(R, T ×_l k)` on Artinian local `Λ`-algebras with residue field `l` is
prorepresented by `R_l = R[X]/(F)`. -/
noncomputable def restrictedCoyonedaIso :
    (comparisonFunctor S).functor ⋙ restrictedCoyoneda R ≅ restrictedCoyoneda (obj S R) :=
  (NatIso.ofComponents
    (fun T => Equiv.toIso
      { toFun := restrictPoint S R T
        invFun := extendPoint S R T
        left_inv := fun β => extendPoint_restrictPoint S R T β
        right_inv := fun α => restrictPoint_extendPoint S R T α })
    (fun {T T'} f => by
      ext β
      exact restrictPoint_naturality S R f β)).symm

end SeparableExtension

end Deformation

end
