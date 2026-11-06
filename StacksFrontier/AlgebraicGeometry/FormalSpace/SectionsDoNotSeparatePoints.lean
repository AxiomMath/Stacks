module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Field.Equiv
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentedCoproduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SparseEmbeddingSystem
public import StacksFrontier.SetTheory.Cardinal.SizeBound
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValued
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CommonBigSites

/-!
# An affine formal algebraic space whose functions do not separate points

Over a field `K` of characteristic zero, let `(V_s)` be an inverse system of `K`-vector spaces
with surjective transition maps and `lim V_s = 0`, each `V_s` equipped with a surjection
`V_s → K` with kernel `W_s`, and set `A_s = K[V_s]/(w w' : w, w' ∈ W_s)`. The transition maps
`A_s → A_t` are surjections with square-zero kernels, so `X = colim Spec(A_s)` is an affine
formal algebraic space, and each `A_s` surjects onto `K[t]` with square-zero kernel, so every
stage of the presentation has reduction `Spec(K[t])`. In characteristic zero the degree `d`
part of `A_s` is the system `(V_s)` again, whence `lim A_s = K`: the formal functions on `X`
form a field although `X_red = Spec(K[t])` has infinitely many points.

The system `(V_s)` is taken to be the free `K`-vector space on the set of injections
`s ↪ ℕ` with infinite complement, indexed by the countable subsets `s` of a fixed uncountable
set, ordered by inclusion; the transition maps are restriction of injections, which is
surjective, and a compatible family of injections over all countable subsets would make the
uncountable set countable, so the limit vanishes.

## Main results

* `exists_isAffineFormalAlgebraicSpace_sections_isField_reduction_infinite`: **Stacks 0CBD**.
* `AlgebraicGeometry.FormalSpace.isLocallySurjective_of_surjective_etale`: **Stacks 05VM**
  for a surjective étale morphism of presheaves, in any value universe.

## References

* [Stacks Project, Tag 0CBD](https://stacks.math.columbia.edu/tag/0CBD)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Polynomial

namespace AlgebraicGeometry.FormalSpace

universe u v w

/-! ### The ring `K[V]/(W W')` of a vector space with a chosen basis

For a `K`-vector space `V` free on a set `α`, together with the surjection `V → K` sending
every basis vector to `1` and with kernel `W`, the quotient `K[V]/(w w' : w, w' ∈ W)` is
realized as the subring of the square-zero extension of `K[X]` by `α →₀ K[X]` cut out by the
condition that the sum of the coordinates of the nilpotent part is the derivative of the
polynomial part: the basis vector indexed by `a` is sent to `(X, single a 1)`, so a monomial
of degree `d` in the basis vectors is sent to `(X ^ d, v)` with `∑ v = d X ^ (d - 1)`. -/

/-- The sum of the coordinates of a finitely supported family of polynomials. -/
private def sumCoeffs (R : Type u) [CommRing R] (α : Type v) :
    (α →₀ R[X]) →ₗ[R[X]] R[X] := Finsupp.lsum R[X] fun _ => LinearMap.id

private theorem sumCoeffs_mapDomain {R : Type u} [CommRing R]
    {α : Type v} {β : Type w} (f : α → β) (v : α →₀ R[X]) :
    sumCoeffs R β (Finsupp.mapDomain f v) = sumCoeffs R α v := by
  simp only [sumCoeffs, Finsupp.lsum_apply]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

/-- The ring `R[V]/(w w' : w, w' ∈ W)`, for `V` the free `R`-module on `α` and `W` the kernel
of the map `V → R` sending every basis vector to `1`: the pairs `(p, v)` in the square-zero
extension of `R[X]` by `α →₀ R[X]` whose nilpotent part has coordinate sum the derivative of
the polynomial part. -/
private def derivativeSubring (R : Type u) [CommRing R] (α : Type v) :
    Subring (TrivSqZeroExt R[X] (α →₀ R[X])) where
  carrier := {x | sumCoeffs R α x.snd = derivative x.fst}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change sumCoeffs R α (a.snd + b.snd) = derivative (a.fst + b.fst)
    rw [map_add, ha, hb, derivative_add]
  neg_mem' := by
    intro a ha
    change sumCoeffs R α (-a.snd) = derivative (-a.fst)
    rw [map_neg, ha, derivative_neg]
  mul_mem' := by
    intro a b ha hb
    change sumCoeffs R α (a * b).snd = derivative (a * b).fst
    simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, op_smul_eq_smul]
    rw [map_add, map_smul, map_smul, ha, hb, smul_eq_mul, smul_eq_mul, derivative_mul]
    ring

/-- The surjection `R[V]/(w w' : w, w' ∈ W) → R[X]` onto the polynomial part, which is the
quotient by the square-zero ideal generated by `W`. -/
private def derivativeProjection (R : Type u) [CommRing R] (α : Type v) :
    derivativeSubring R α →+* R[X] :=
  (TrivSqZeroExt.fstHom R[X] R[X] (α →₀ R[X])).toRingHom.comp
    (derivativeSubring R α).subtype

private theorem derivativeProjection_surjective (R : Type u) [CommRing R]
    (α : Type v) [Nonempty α] : Function.Surjective (derivativeProjection R α) := by
  intro p
  let a : α := Classical.arbitrary α
  refine ⟨⟨⟨p, Finsupp.single a p.derivative⟩, ?_⟩, rfl⟩
  change sumCoeffs R α (Finsupp.single a p.derivative) = p.derivative
  simp [sumCoeffs, Finsupp.lsum_single]

private theorem derivativeProjection_ker_mul (R : Type u) [CommRing R]
    (α : Type v) (x y : derivativeSubring R α)
    (hx : derivativeProjection R α x = 0)
    (hy : derivativeProjection R α y = 0) : x * y = 0 := by
  apply Subtype.ext
  apply TrivSqZeroExt.ext <;> simp_all [derivativeProjection]

/-- The transition map `R[V]/(w w' : w, w' ∈ W) → R[V']/(w w' : w, w' ∈ W')` induced by a map
of basis index sets, which on the nilpotent part sums the coordinates lying over a basis
vector. -/
private def derivativeMap {R : Type u} [CommRing R] {α : Type v} {β : Type w}
    (f : α → β) : derivativeSubring R α →+* derivativeSubring R β :=
  RingHom.codRestrict
    ((TrivSqZeroExt.map (Finsupp.lmapDomain R[X] R[X] f)).toRingHom.comp
      (derivativeSubring R α).subtype) (derivativeSubring R β) (by
      intro x
      change sumCoeffs R β (TrivSqZeroExt.map
        (Finsupp.lmapDomain R[X] R[X] f) x.val).snd =
        derivative (TrivSqZeroExt.map (Finsupp.lmapDomain R[X] R[X] f) x.val).fst
      simpa only [TrivSqZeroExt.snd_map, TrivSqZeroExt.fst_map,
        Finsupp.lmapDomain_apply, sumCoeffs_mapDomain] using
        (show sumCoeffs R α x.val.snd = derivative x.val.fst from x.property))

private theorem derivativeMap_fst {R : Type u} [CommRing R]
    {α : Type v} {β : Type w} (f : α → β) (x : derivativeSubring R α) :
    (derivativeMap f x).val.fst = x.val.fst :=
  TrivSqZeroExt.fst_map _ _

private theorem derivativeMap_snd {R : Type u} [CommRing R]
    {α : Type v} {β : Type w} (f : α → β) (x : derivativeSubring R α) :
    (derivativeMap f x).val.snd = Finsupp.mapDomain f x.val.snd :=
  TrivSqZeroExt.snd_map _ _

private theorem derivativeMap_surjective {R : Type u} [CommRing R]
    {α : Type v} {β : Type w} (f : α → β) (hf : Function.Surjective f) :
    Function.Surjective (derivativeMap (R := R) f) := by
  intro y
  obtain ⟨v, hv⟩ := Finsupp.mapDomain_surjective hf y.val.snd
  have hm : (⟨y.val.fst, v⟩ : TrivSqZeroExt R[X] (α →₀ R[X])) ∈
      derivativeSubring R α := by
    change sumCoeffs R α v = derivative y.val.fst
    rw [← sumCoeffs_mapDomain f v, hv]
    exact y.property
  exact ⟨⟨_, hm⟩, Subtype.ext (TrivSqZeroExt.ext (derivativeMap_fst _ _)
    ((derivativeMap_snd _ _).trans hv))⟩

private theorem derivativeMap_id {R : Type u} [CommRing R]
    {α : Type v} (x : derivativeSubring R α) : derivativeMap id x = x :=
  Subtype.ext (TrivSqZeroExt.ext (derivativeMap_fst _ _)
    (by simp only [derivativeMap_snd, Finsupp.mapDomain_id]))

private theorem derivativeMap_comp {R : Type u} [CommRing R]
    {α : Type v} {β : Type w} {γ : Type*} (f : α → β) (g : β → γ)
    (x : derivativeSubring R α) :
    derivativeMap (g ∘ f) x = derivativeMap g (derivativeMap f x) :=
  Subtype.ext (TrivSqZeroExt.ext (by simp only [derivativeMap_fst])
    (by simp only [derivativeMap_snd, Finsupp.mapDomain_comp]))

private theorem derivativeMap_ker_mul {R : Type u} [CommRing R]
    {α : Type v} {β : Type w} (f : α → β) (x y : derivativeSubring R α)
    (hx : derivativeMap f x = 0) (hy : derivativeMap f y = 0) : x * y = 0 :=
  derivativeProjection_ker_mul _ _ x y
    ((derivativeMap_fst f x).symm.trans (congrArg (fun z => z.val.fst) hx))
    ((derivativeMap_fst f y).symm.trans (congrArg (fun z => z.val.fst) hy))

/-- The structure map `R → R[V]/(w w' : w, w' ∈ W)` of the constants. -/
private def derivativeConstants (R : Type u) [CommRing R] (α : Type v) :
    R →+* derivativeSubring R α :=
  ((TrivSqZeroExt.inlHom R[X] (α →₀ R[X])).comp C).codRestrict
    (derivativeSubring R α) (fun r => by simp [derivativeSubring])

/-- An element of `R[V]/(w w' : w, w' ∈ W)` with vanishing nilpotent part is a constant, when
`R` is torsion free as an additive group: its polynomial part has zero derivative. -/
private theorem derivative_eq_constant_of_snd_eq_zero
    {R : Type u} [CommRing R] [IsAddTorsionFree R]
    {α : Type v} (x : derivativeSubring R α) (hx : x.val.snd = 0) :
    x = derivativeConstants R α (x.val.fst.coeff 0) := by
  have : HasUniqueDiv R :=
    ⟨fun _ hn a b h => eq_of_nsmul_eq_nsmul_of_addCommute hn (AddCommute.all a b) h⟩
  have hd : derivative x.val.fst = 0 := by
    rw [← x.property, hx, map_zero]
  exact Subtype.ext (TrivSqZeroExt.ext (eq_C_of_derivative_eq_zero hd) hx)


/-! ### The inverse limit of the rings of the system is the ground field -/

/-- The inverse system of rings `A_s = K[V_s]/(w w' : w, w' ∈ W_s)` attached to a system of
basis index sets. -/
private def derivativeFunctor (R : Type u) [CommRing R]
    {J : Type v} [Category J] (F : J ⥤ Type w) : J ⥤ CommRingCat.{max u w} where
  obj j := CommRingCat.of (derivativeSubring R (F.obj j))
  map f := CommRingCat.ofHom (derivativeMap (F.map f))
  map_id j := by
    ext x : 2
    change derivativeMap (F.map (𝟙 j)) x = x
    rw [F.map_id]
    exact derivativeMap_id x
  map_comp f g := by
    ext x : 2
    change derivativeMap (F.map (f ≫ g)) x =
      derivativeMap (F.map g) (derivativeMap (F.map f) x)
    rw [F.map_comp]
    exact derivativeMap_comp (F.map f) (F.map g) x

/-- The constants are compatible with the transition maps of the system. -/
private theorem derivativeMap_comp_derivativeConstants {R : Type u} [CommRing R]
    {α : Type v} {β : Type w} (f : α → β) :
    (derivativeMap (R := R) f).comp (derivativeConstants R α) = derivativeConstants R β :=
  RingHom.ext fun r => Subtype.ext (TrivSqZeroExt.ext (derivativeMap_fst _ _)
    ((derivativeMap_snd f (derivativeConstants R α r)).trans Finsupp.mapDomain_zero))

/-- The constants, as a section of the inverse system of rings of the system. -/
private def derivativeConstantSections (R : Type u) [CommRing R]
    {J : Type v} [Category J] (F : J ⥤ Type w) :
    R →+* RingCat.sectionsSubring (derivativeFunctor R F ⋙ forget₂ CommRingCat RingCat) :=
  (RingHom.pi fun j => derivativeConstants R (F.obj j)).codRestrict _ (by
    intro r i j f
    exact DFunLike.congr_fun (derivativeMap_comp_derivativeConstants (R := R) (F.map f)) r)

private theorem derivativeConstantSections_injective (R : Type u) [CommRing R]
    {J : Type v} [Category J] [Nonempty J] (F : J ⥤ Type w) :
    Function.Injective (derivativeConstantSections R F) := by
  intro r s h
  have he := congrArg (fun z => (z.val (Classical.arbitrary J)).val.fst.coeff 0) h
  change (C r).coeff 0 = (C s).coeff 0 at he
  simpa only [coeff_C_zero] using he

private theorem derivativeConstantSections_surjective (R : Type u) [CommRing R]
    [IsAddTorsionFree R] (α : Type w) [Uncountable α] :
    Function.Surjective (derivativeConstantSections R (sparseEmbeddingSystem α)) := by
  classical
  intro x
  have hz : ∀ s, (x.val (op s)).val.snd = 0 := by
    apply finsupp_sparseEmbedding_eq_zero
    intro s t h
    exact (derivativeMap_snd _ _).symm.trans
      (congrArg (fun y => y.val.snd) (x.property (homOfLE h).op))
  let z : CountableSubset α := ⟨∅, Set.countable_empty⟩
  refine ⟨(x.val (op z)).val.fst.coeff 0, ?_⟩
  apply Subtype.ext
  funext s
  obtain ⟨s⟩ := s
  have he' : (x.val (op s)).val.fst = (x.val (op z)).val.fst :=
    (derivativeMap_fst _ _).symm.trans (congrArg (fun y => y.val.fst)
      (x.property (homOfLE (show z ≤ s from Set.empty_subset _)).op))
  change derivativeConstants R (SparseEmbedding s) _ = x.val (op s)
  rw [derivative_eq_constant_of_snd_eq_zero (x.val (op s)) (hz s), he']
  rfl

/-- The inverse limit of the rings `A_s = K[V_s]/(w w' : w, w' ∈ W_s)` of the system over the
countable subsets of an uncountable set is the ground field, when that field has
characteristic zero. -/
private theorem derivativeSections_isField (K : Type u) [Field K] [CharZero K]
    (α : Type w) [Uncountable α] :
    IsField (RingCat.sectionsSubring
      (derivativeFunctor K (sparseEmbeddingSystem α) ⋙ forget₂ CommRingCat RingCat)) := by
  have : Nonempty (CountableSubset α) := ⟨⟨∅, Set.countable_empty⟩⟩
  exact (RingEquiv.ofBijective (derivativeConstantSections K (sparseEmbeddingSystem α))
    ⟨derivativeConstantSections_injective K _,
      derivativeConstantSections_surjective K α⟩).symm.toMulEquiv.isField (Field.toIsField K)

/-! ### The affine formal algebraic space of the system -/

/-- A surjection of rings with square-zero kernel induces a thickening of spectra. -/
private theorem specMap_isThickening_of_sqZero {R S : CommRingCat.{u}}
    (f : R ⟶ S) (hf : Function.Surjective f)
    (hker : ∀ x y, f x = 0 → f y = 0 → x * y = 0) :
    Stacks.Thickenings.IsThickening (Spec.map f) := by
  refine ⟨IsClosedImmersion.spec_of_surjective f hf, ?_⟩
  change Function.Surjective (PrimeSpectrum.comap f.hom)
  intro p
  have hp : p ∈ PrimeSpectrum.zeroLocus (RingHom.ker f.hom) := by
    intro x hx
    have hsq : x * x ∈ p.asIdeal := hker x x hx hx ▸ p.asIdeal.zero_mem
    exact (p.isPrime.mem_or_mem hsq).elim id id
  rwa [← range_comap_of_surjective S f.hom hf] at hp

/-- A surjection of rings with square-zero kernel induces a thickening of spectra. The kernel
condition is stated on elements rather than as nilpotence of the ideal, which is the form a
system of square-zero extensions supplies it in. -/
public alias specMap_isThickening_of_sqZero' := specMap_isThickening_of_sqZero

/-- The spectrum of a polynomial ring over an infinite field has infinitely many points. -/
private theorem infinite_polynomial_spectrum (K : Type u) [Field K] [Infinite K] :
    Infinite (PrimeSpectrum K[X]) := by
  let p (a : K) : PrimeSpectrum K[X] :=
    ⟨RingHom.ker (Polynomial.evalRingHom a), RingHom.ker_isPrime _⟩
  apply Infinite.of_injective p
  intro a b hab
  have ha : X - C a ∈ (p a).asIdeal := by simp [p, RingHom.mem_ker]
  rw [hab] at ha
  exact (sub_eq_zero.mp (by simpa [p, RingHom.mem_ker] using ha)).symm

/-- The directed diagram of affine schemes `Spec(A_s)` of the system, indexed by the countable
subsets of `α` ordered by inclusion. -/
private def derivativeSchemeDiagram (K : Type u) [CommRing K] (α : Type u) :
    CountableSubset α ⥤ Scheme.{u} :=
  (derivativeFunctor K (sparseEmbeddingSystem α)).rightOp ⋙ Scheme.Spec

private theorem derivativeSchemeDiagram_isThickening (K : Type u) [CommRing K]
    (α : Type u) {s t : CountableSubset α} (f : s ⟶ t) :
    Stacks.Thickenings.IsThickening ((derivativeSchemeDiagram K α).map f) :=
  specMap_isThickening_of_sqZero _
    (derivativeMap_surjective (sparseRestrict (leOfHom f)) (sparseRestrict_surjective (leOfHom f)))
    (derivativeMap_ker_mul (sparseRestrict (leOfHom f)))

/-- The map induced on inverse limits of section rings by a morphism of diagrams of rings. -/
private def ringSectionsMap {J : Type v} [Category J]
    {F G : J ⥤ CommRingCat.{u}} (f : F ⟶ G) :
    RingCat.sectionsSubring (F ⋙ forget₂ CommRingCat RingCat) →+*
      RingCat.sectionsSubring (G ⋙ forget₂ CommRingCat RingCat) where
  toFun x := ⟨fun j => f.app j (x.val j), by
    intro i j g
    change G.map g (f.app i (x.val i)) = f.app j (x.val j)
    calc
      _ = f.app j (F.map g (x.val i)) :=
        (congrArg (fun k : F.obj i ⟶ G.obj j => k (x.val i)) (f.naturality g)).symm
      _ = _ := congrArg (fun z => f.app j z) (x.property g)⟩
  map_one' := Subtype.ext <| funext fun j => map_one (f.app j).hom
  map_mul' x y := Subtype.ext <| funext fun j => map_mul (f.app j).hom _ _
  map_zero' := Subtype.ext <| funext fun j => map_zero (f.app j).hom
  map_add' x y := Subtype.ext <| funext fun j => map_add (f.app j).hom _ _

/-- Isomorphic diagrams of rings have isomorphic inverse limits. -/
private def ringSectionsEquiv {J : Type v} [Category J]
    {F G : J ⥤ CommRingCat.{u}} (e : F ≅ G) :
    RingCat.sectionsSubring (F ⋙ forget₂ CommRingCat RingCat) ≃+*
      RingCat.sectionsSubring (G ⋙ forget₂ CommRingCat RingCat) where
  __ := ringSectionsMap e.hom
  invFun := ringSectionsMap e.inv
  left_inv x := Subtype.ext <| funext fun j => (e.app j).hom_inv_id_apply (x.val j)
  right_inv x := Subtype.ext <| funext fun j => (e.app j).inv_hom_id_apply (x.val j)

/-- The global sections of the stages of the diagram of spectra are the rings of the system. -/
private def derivativeGlobalSectionsIso (K : Type u) [CommRing K] (α : Type u) :
    (derivativeSchemeDiagram K α).op ⋙ Scheme.Γ ≅
      derivativeFunctor K (sparseEmbeddingSystem α) :=
  NatIso.ofComponents (fun s => Scheme.ΓSpecIso _) fun f =>
    Scheme.ΓSpecIso_naturality ((derivativeFunctor K (sparseEmbeddingSystem α)).map f)

private theorem derivativeGlobalSections_isField (K : Type u) [Field K] [CharZero K]
    (α : Type u) [Uncountable α] :
    IsField (RingCat.sectionsSubring
      ((derivativeSchemeDiagram K α).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat)) :=
  (ringSectionsEquiv (derivativeGlobalSectionsIso K α)).toMulEquiv.isField
    (derivativeSections_isField K α)

/-- The diagram of spectra of the system, reindexed by the universe lift of its index set, as
the index of a presentation of a formal algebraic space must be. -/
private def liftedDerivativeDiagram (K : Type u) [CommRing K] (α : Type u) :
    ULift.{u + 1} (CountableSubset α) ⥤ Scheme.{u} :=
  ULift.orderIso.equivalence.functor ⋙ derivativeSchemeDiagram K α

/-- Reindexing an inverse system of rings along the universe lift of its index preorder does
not change its inverse limit. -/
private def ringSectionsUliftEquiv {I : Type u} [Preorder I]
    (F : Iᵒᵖ ⥤ CommRingCat.{v}) :
    RingCat.sectionsSubring
      (ULift.orderIso.{w, u}.equivalence.functor.op ⋙ F ⋙ forget₂ CommRingCat RingCat) ≃+*
      RingCat.sectionsSubring (F ⋙ forget₂ CommRingCat RingCat) where
  toFun x := ⟨fun j => x.val (op (ULift.up j.unop)), fun {i j} f =>
    x.property (homOfLE (show (ULift.up j.unop : ULift.{w} I) ≤ ULift.up i.unop
      from (leOfHom f.unop : j.unop ≤ i.unop))).op⟩
  invFun x := ⟨fun j => x.val (op j.unop.down), fun {i j} f =>
    x.property (homOfLE (show j.unop.down ≤ i.unop.down
      from (leOfHom f.unop : j.unop ≤ i.unop))).op⟩
  left_inv x := rfl
  right_inv x := rfl
  map_mul' x y := rfl
  map_add' x y := rfl

private theorem liftedDerivativeGlobalSections_isField
    (K : Type u) [Field K] [CharZero K] (α : Type u) [Uncountable α] :
    IsField (RingCat.sectionsSubring
      ((liftedDerivativeDiagram K α).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat)) :=
  (ringSectionsUliftEquiv ((derivativeSchemeDiagram K α).op ⋙ Scheme.Γ)).toMulEquiv.isField
    (derivativeGlobalSections_isField K α)

/-- The ground field, as a constant subring of every ring of the system. -/
private def derivativeConstantsNatTrans (K : Type u) [CommRing K] (α : Type u) :
    (Functor.const (CountableSubset α)ᵒᵖ).obj (CommRingCat.of K) ⟶
      derivativeFunctor K (sparseEmbeddingSystem α) where
  app s := CommRingCat.ofHom (derivativeConstants K ((sparseEmbeddingSystem α).obj s))
  naturality {s t} f := by
    ext r : 2
    change derivativeConstants K ((sparseEmbeddingSystem α).obj t) r =
      derivativeMap ((sparseEmbeddingSystem α).map f)
        (derivativeConstants K ((sparseEmbeddingSystem α).obj s) r)
    exact (DFunLike.congr_fun
      (derivativeMap_comp_derivativeConstants (R := K) ((sparseEmbeddingSystem α).map f)) r).symm

/-- The structure morphism `Spec(A_s) ⟶ Spec(K)` of a stage over the ground field. -/
private def derivativeStructureMap (K : Type u) [CommRing K] (α : Type u)
    (s : CountableSubset α) :
    (derivativeSchemeDiagram K α).obj s ⟶ Spec (CommRingCat.of K) :=
  Spec.map ((derivativeConstantsNatTrans K α).app (op s))

private theorem derivativeStructureMap_naturality (K : Type u) [CommRing K]
    (α : Type u) {s t : CountableSubset α} (f : s ⟶ t) :
    (derivativeSchemeDiagram K α).map f ≫ derivativeStructureMap K α t =
      derivativeStructureMap K α s := by
  change Spec.map ((derivativeFunctor K (sparseEmbeddingSystem α)).map f.op) ≫
      Spec.map ((derivativeConstantsNatTrans K α).app (op t)) =
      Spec.map ((derivativeConstantsNatTrans K α).app (op s))
  rw [← Spec.map_comp, ← (derivativeConstantsNatTrans K α).naturality f.op]
  simp

/-- A stage of the system as an affine scheme over `Spec(K)` in the big fppf site. -/
private def derivativeBigAffineObject (K : Type u) [CommRing K] (α : Type u)
    (B : BigFppfSite.{u}) (hS : B.Contains (Spec (CommRingCat.of K)))
    (hstage : ∀ s, B.Contains ((derivativeSchemeDiagram K α).obj s))
    (s : CountableSubset α) : BigAffineFppf B (Spec (CommRingCat.of K)) hS :=
  ⟨Over.mk (show B.obj (hstage s) ⟶ B.obj hS from
    ObjectProperty.homMk (derivativeStructureMap K α s)), by
      change IsAffine (Spec (CommRingCat.of (derivativeSubring K (SparseEmbedding s))))
      infer_instance⟩

/-- The presentation of the example: the directed diagram of the affine schemes `Spec(A_s)`
over `Spec(K)` in the big fppf site. -/
private def derivativeBigAffineDiagram (K : Type u) [CommRing K] (α : Type u)
    (B : BigFppfSite.{u}) (hS : B.Contains (Spec (CommRingCat.of K)))
    (hstage : ∀ s, B.Contains ((derivativeSchemeDiagram K α).obj s)) :
    ULift.{u + 1} (CountableSubset α) ⥤ BigAffineFppf B (Spec (CommRingCat.of K)) hS where
  obj s := derivativeBigAffineObject K α B hS hstage s.down
  map {s t} f := ObjectProperty.homMk (Over.homMk
      (ObjectProperty.homMk ((derivativeSchemeDiagram K α).map
        (homOfLE (show s.down ≤ t.down from (leOfHom f : s ≤ t))))) (by
      apply ObjectProperty.hom_ext
      exact derivativeStructureMap_naturality K α
        (homOfLE (show s.down ≤ t.down from (leOfHom f : s ≤ t)))))
  map_id s := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (derivativeSchemeDiagram K α).map_id s.down
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (derivativeSchemeDiagram K α).map_comp _ _

private theorem derivativeBigAffineDiagram_isThickening (K : Type u) [CommRing K]
    (α : Type u) (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (CommRingCat.of K)))
    (hstage : ∀ s, B.Contains ((derivativeSchemeDiagram K α).obj s))
    {s t : ULift.{u + 1} (CountableSubset α)} (f : s ⟶ t) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B (Spec (CommRingCat.of K)) hS).map
        ((derivativeBigAffineDiagram K α B hS hstage).map f)) :=
  derivativeSchemeDiagram_isThickening K α
    (homOfLE (show s.down ≤ t.down from (leOfHom f : s ≤ t)))

/-! ### The stages and their coproduct lie in a big fppf site -/

private theorem mk_polynomial_le_power (R : Type u) [Semiring R] :
    Cardinal.mk R[X] ≤ Cardinal.mk R ^ Cardinal.aleph0 := by
  simpa only [Cardinal.mk_arrow, Cardinal.mk_nat, Cardinal.lift_uzero, Cardinal.lift_aleph0] using
    Cardinal.mk_le_of_injective (f := fun p : R[X] => (⇑p.coeff : ℕ → R))
      (fun p q h => Polynomial.ext fun n => congrArg (fun c => c n) h)

private theorem mk_sparseEmbedding_le_power {α : Type u} (s : CountableSubset α) :
    Cardinal.mk (SparseEmbedding s) ≤ Cardinal.aleph0 ^ Cardinal.mk s.val := by
  simpa only [Cardinal.mk_arrow, Cardinal.mk_nat, Cardinal.lift_uzero, Cardinal.lift_aleph0] using
    Cardinal.mk_le_of_injective (f := fun e : SparseEmbedding s => (e.val : s.val → ℕ))
      (fun e f h => Subtype.ext (DFunLike.coe_injective h))

private theorem mk_finsupp_le_power (β R : Type u) [Zero R] :
    Cardinal.mk (β →₀ R) ≤ Cardinal.mk R ^ Cardinal.mk β := by
  simpa only [Cardinal.mk_arrow, Cardinal.lift_id] using
    Cardinal.mk_le_of_injective (f := fun v : β →₀ R => (v : β → R))
      (fun x y h => Finsupp.ext (congrFun h))

private theorem polynomial_card_lt {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ)
    (hlim : κ.IsStrongPrelimit) (R : Type u) [Semiring R] (hR : Cardinal.mk R < κ) :
    Cardinal.mk R[X] < κ :=
  (mk_polynomial_le_power R).trans_lt (Cardinal.power_lt_of_isStrongPrelimit hκ hlim hR hκ)

private theorem derivative_card_lt {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ)
    (hlim : κ.IsStrongPrelimit) (R : Type u) [CommRing R] (α : Type u)
    (hR : Cardinal.mk R < κ) (hα : Cardinal.mk α < κ) (s : CountableSubset α) :
    Cardinal.mk (derivativeSubring R (SparseEmbedding s)) < κ := by
  have he : Cardinal.mk (SparseEmbedding s) < κ :=
    (mk_sparseEmbedding_le_power s).trans_lt (Cardinal.power_lt_of_isStrongPrelimit hκ hlim hκ
      ((Cardinal.mk_subtype_le _).trans_lt hα))
  have hp := polynomial_card_lt hκ hlim R hR
  have hv : Cardinal.mk (SparseEmbedding s →₀ R[X]) < κ :=
    (mk_finsupp_le_power _ _).trans_lt (Cardinal.power_lt_of_isStrongPrelimit hκ hlim hp he)
  apply (Cardinal.mk_subtype_le _).trans_lt
  change Cardinal.mk (R[X] × (SparseEmbedding s →₀ R[X])) < κ
  simp only [Cardinal.mk_prod, Cardinal.lift_id]
  exact Cardinal.mul_lt_of_lt hκ.le hp hv

private theorem derivative_contains (K : Type u) [CommRing K] (α : Type u)
    (B : BigFppfSite.{u}) (hK : Cardinal.mk K < B.cutoff)
    (hα : Cardinal.mk α < B.cutoff) (s : CountableSubset α) :
    B.Contains ((derivativeSchemeDiagram K α).obj s) := by
  change (Spec (CommRingCat.of (derivativeSubring K (SparseEmbedding s)))).size < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff
    (derivative_card_lt B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit K α hK hα s)

private theorem derivative_card_le (K : Type u) [CommRing K] (α : Type u)
    (μ : Cardinal.{u}) (hμ : Cardinal.aleph0 ≤ μ)
    (hK : Cardinal.mk K ≤ μ) (hα : Cardinal.mk α ≤ μ) (s : CountableSubset α) :
    Cardinal.mk (derivativeSubring K (SparseEmbedding s)) ≤ 2 ^ ((2 : Cardinal.{u}) ^ μ) := by
  have hp : Cardinal.mk K[X] ≤ 2 ^ μ :=
    (mk_polynomial_le_power K).trans (Cardinal.power_le_two_power hμ hK hμ)
  have he : Cardinal.mk (SparseEmbedding s) ≤ 2 ^ μ :=
    (mk_sparseEmbedding_le_power s).trans
      (Cardinal.power_le_two_power hμ hμ ((Cardinal.mk_subtype_le _).trans hα))
  have hβ : Cardinal.aleph0 ≤ 2 ^ μ := hμ.trans (Cardinal.cantor μ).le
  have hγ : Cardinal.aleph0 ≤ 2 ^ ((2 : Cardinal.{u}) ^ μ) := hβ.trans (Cardinal.cantor _).le
  have hv : Cardinal.mk (SparseEmbedding s →₀ K[X]) ≤ 2 ^ ((2 : Cardinal.{u}) ^ μ) :=
    (mk_finsupp_le_power _ _).trans (Cardinal.power_le_two_power hβ hp he)
  apply (Cardinal.mk_subtype_le _).trans
  change Cardinal.mk (K[X] × (SparseEmbedding s →₀ K[X])) ≤ _
  simp only [Cardinal.mk_prod, Cardinal.lift_id]
  exact (mul_le_mul' (hp.trans (Cardinal.cantor _).le) hv).trans_eq
    (Cardinal.mul_eq_self hγ)

private theorem derivative_coproduct_contains (K : Type u) [CommRing K] (α : Type u)
    (B : BigFppfSite.{u}) (hK : Cardinal.mk K < B.cutoff)
    (hα : Cardinal.mk α < B.cutoff) :
    B.Contains (∐ fun s : ULift.{u + 1} (CountableSubset α) =>
      (derivativeSchemeDiagram K α).obj s.down) := by
  let μ := max Cardinal.aleph0 (max (Cardinal.mk K) (Cardinal.mk α))
  have hμ : Cardinal.aleph0 ≤ μ := le_max_left _ _
  have hKμ : Cardinal.mk K ≤ μ := (le_max_left _ _).trans (le_max_right _ _)
  have hαμ : Cardinal.mk α ≤ μ := (le_max_right _ _).trans (le_max_right _ _)
  have hμκ : μ < B.cutoff := max_lt B.aleph0_lt_cutoff (max_lt hK hα)
  have hγ : Cardinal.aleph0 ≤ 2 ^ ((2 : Cardinal.{u}) ^ μ) :=
    (hμ.trans (Cardinal.cantor μ).le).trans (Cardinal.cantor _).le
  change (∐ fun s : ULift.{u + 1} (CountableSubset α) =>
      (derivativeSchemeDiagram K α).obj s.down).size < B.cutoff
  let e : (∐ fun s : ULift.{u + 1} (CountableSubset α) =>
      (derivativeSchemeDiagram K α).obj s.down) ≅ ∐ (derivativeSchemeDiagram K α).obj :=
    Sigma.reindex (Equiv.ulift : ULift.{u + 1} (CountableSubset α) ≃ CountableSubset α)
      ((derivativeSchemeDiagram K α).obj)
  apply (Scheme.size_congr e).trans_lt
  apply (schemeSize_coproduct_le _ _ hγ ?_ ?_).trans_lt
    (B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit hμκ))
  · apply (Cardinal.mk_subtype_le _).trans
    rw [Cardinal.mk_set]
    exact (Cardinal.power_le_power_left (by norm_num) hαμ).trans (Cardinal.cantor _).le
  · intro s
    change (Spec (CommRingCat.of (derivativeSubring K (SparseEmbedding s)))).size ≤ _
    rw [Scheme.size_Spec]
    exact max_le hγ (derivative_card_le K α μ hμ hKμ hαμ s)

/-! ### The empty stage is the reduction -/

private theorem derivativeProjection_injective_of_subsingleton
    (K : Type u) [CommRing K] (β : Type v) [Subsingleton β] [Nonempty β] :
    Function.Injective (derivativeProjection K β) := by
  let b : β := Classical.arbitrary β
  have hs (v : β →₀ K[X]) : sumCoeffs K β v = v b := by
    have hv : v = Finsupp.single b (v b) := by
      ext i
      obtain rfl : i = b := Subsingleton.elim _ _
      simp
    conv_lhs => rw [hv]
    simp [sumCoeffs, Finsupp.lsum_single]
  intro x y hxy
  refine Subtype.ext (TrivSqZeroExt.ext hxy (Finsupp.ext fun i => ?_))
  obtain rfl : i = b := Subsingleton.elim _ _
  rw [← hs, ← hs, x.property, y.property]
  exact congrArg derivative hxy

private theorem sparseEmbedding_empty_subsingleton (α : Type u) :
    Subsingleton (SparseEmbedding (⟨∅, Set.countable_empty⟩ : CountableSubset α)) := by
  refine ⟨fun a b => Subtype.ext ?_⟩
  ext x
  exact False.elim x.property

attribute [local instance] sparseEmbedding_empty_subsingleton

/-- The stage of the system at the empty subset is the polynomial line: the vector space over
the empty subset is one dimensional, so its square-zero ideal is zero. -/
private def derivativeEmptyIso (K : Type u) [CommRing K] (α : Type u) :
    (derivativeSchemeDiagram K α).obj ⟨∅, Set.countable_empty⟩ ≅
      Spec (CommRingCat.of K[X]) := by
  let s : CountableSubset α := ⟨∅, Set.countable_empty⟩
  letI : Nonempty (SparseEmbedding s) := sparseEmbedding_nonempty s
  let e := RingEquiv.ofBijective (derivativeProjection K (SparseEmbedding s))
    ⟨derivativeProjection_injective_of_subsingleton K _, derivativeProjection_surjective K _⟩
  exact (Scheme.Spec.mapIso e.toCommRingCatIso.op).symm

/-- The empty stage of the system over an infinite field has infinitely many points. -/
private theorem infinite_derivativeSchemeDiagram_empty (K : Type u) [Field K] [Infinite K]
    (α : Type u) : Infinite ((derivativeSchemeDiagram K α).obj ⟨∅, Set.countable_empty⟩) := by
  have : Infinite (Spec (CommRingCat.of K[X])) := infinite_polynomial_spectrum K
  exact Infinite.of_injective (Scheme.homeoOfIso (derivativeEmptyIso K α)).symm
    (Scheme.homeoOfIso (derivativeEmptyIso K α)).symm.injective

/-! ### The coproduct of the stages is representable -/

attribute [local instance] bigFppfOver_subcanonical

attribute [local instance] sheaf_hasColimits

/-! ### A reduced representable thickening is the reduction

A thickening of sheaves whose base changes along represented sheaves are thickenings of schemes
is a monomorphism, a map to its target from a reduced scheme of the site lifts through it, and
consequently a reduced source lifts uniquely through it: the base change of the thickening along
any map from an algebraic space is then both a monomorphism and an epimorphism, hence an
isomorphism, because the sheaf category is balanced. -/

/-- A morphism which is its own base change along itself is a monomorphism as soon as one of
the two projections is. -/
private theorem mono_of_self_pullback_mono
    {C : Type*} [Category* C] {P X Y : C} {a b : P ⟶ X} {f : X ⟶ Y}
    (h : IsPullback a b f f) [Mono b] : Mono f := by
  let d := h.lift (𝟙 X) (𝟙 X) (by simp)
  have hda : d ≫ a = 𝟙 X := h.lift_fst _ _ _
  have hdb : d ≫ b = 𝟙 X := h.lift_snd _ _ _
  have hbd : b ≫ d = 𝟙 P := (cancel_mono b).mp (by simp [Category.assoc, hdb])
  have hab : a = b := by
    rw [← Category.id_comp a, ← hbd, Category.assoc, hda, Category.comp_id]
  exact ⟨fun {Z} g k hgk => (h.lift_fst g k hgk).symm.trans
    ((congrArg (fun t => h.lift g k hgk ≫ t) hab).trans (h.lift_snd g k hgk))⟩

/-- A morphism of fppf sheaves whose base changes along represented sheaves are thickenings of
schemes is a monomorphism. -/
private theorem mono_of_represented_thickening
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T : BigFppfOver B S hS} {X : FppfSheaf B S hS}
    (f : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X)
    (hf : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) f) : Mono f := by
  have : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (hf.rep.snd f)) :=
    (hf.property_snd f).1
  have : Mono (hf.rep.snd f) := (BigFppfOver.toScheme B S hS).mono_of_mono_map
    (inferInstance : Mono ((BigFppfOver.toScheme B S hS).map (hf.rep.snd f)))
  have := Sheaf.mono_sheafifiedYoneda_map (J := BigFppfOver.topology B S hS) (hf.rep.snd f)
  exact mono_of_self_pullback_mono (hf.rep.isPullback f)

/-- A morphism of presheaves on the big fppf site over `S` which is surjective and étale after
every base change along a universe-lifted represented presheaf is locally surjective. -/
private theorem isLocallySurjective_of_surjective_etale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (f : F ⟶ G)
    (hs : (MorphismProperty.relative (uliftYoneda.{w}) (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (he : (MorphismProperty.relative (uliftYoneda.{w}) (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f := by
  refine ⟨fun {T} y => ?_⟩
  let ξ : (uliftYoneda.{w}).obj T ⟶ G := uliftYonedaEquiv.symm y
  let q := hs.rep.snd ξ
  have hcover : Sieve.generate (Presieve.singleton q) ∈
      BigFppfOver.topology B S hS T := by
    change Sieve.generate (Presieve.singleton q) ∈ B.topology.over (B.obj hS) T
    rw [B.topology.mem_over_iff, Sieve.overEquiv_generate,
      ← Sieve.arrows_generate_map_eq_functorPushforward, Sieve.generate_sieve,
      Presieve.map_singleton]
    exact Space.singleton_mem_bigFppf_topology B q.left
      (hs.property_snd ξ) (he.property ξ (hs.rep.fst ξ) q (hs.rep.isPullback ξ))
  apply (BigFppfOver.topology B S hS).superset_covering _ hcover
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨⟩
  refine ⟨uliftYonedaEquiv (hs.rep.fst ξ), ?_⟩
  have hw := congrArg uliftYonedaEquiv (hs.rep.isPullback ξ).w
  have hn := uliftYonedaEquiv_naturality ξ q.op
  exact (uliftYonedaEquiv_comp _ _).symm.trans (hw.trans
    (by simpa only [q, Quiver.Hom.unop_op, ξ, Equiv.apply_symm_apply] using hn.symm))

/-- **Stacks 05VM for a surjective étale morphism, in any value universe.** A morphism of
presheaves on the big fppf site over `S` which is surjective and étale after every base change
along a universe-lifted represented presheaf is locally surjective: a single surjective étale
morphism of the site generates a covering sieve, and the section lifts over it. -/
alias isLocallySurjective_of_surjective_etale' := isLocallySurjective_of_surjective_etale

/-- A morphism to the target of a representable thickening whose source is a reduced scheme of
the site lifts through the thickening: its base change is a surjective closed immersion onto a
reduced scheme, hence an isomorphism. -/
private theorem reduced_lift_thickening
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : FppfSheaf B S hS} (f : Y ⟶ X)
    (hf : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) f)
    (T : BigFppfOver B S hS)
    (hT : IsReduced ((BigFppfOver.toScheme B S hS).obj T))
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X) :
    ∃ l, l ≫ f = g := by
  let q := hf.rep.snd g
  have hq := hf.property_snd g
  have : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map q) := hq.1
  have : Surjective ((BigFppfOver.toScheme B S hS).map q) := ⟨hq.2⟩
  have : IsIso ((BigFppfOver.toScheme B S hS).map q) :=
    isIso_of_isClosedImmersion_of_surjective _
  have : IsIso q := isIso_of_reflects_iso q (BigFppfOver.toScheme B S hS)
  refine ⟨inv ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q) ≫
    hf.rep.fst g, ?_⟩
  rw [Category.assoc, hf.rep.w g, IsIso.inv_hom_id_assoc]

/-- The universal property of the reduction, for a representable thickening with reduced
source: every morphism to the target from an algebraic space admitting a reduced scheme atlas
factors uniquely through it. -/
private theorem existsUnique_lift_of_reduced_thickening
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : FppfSheaf B S hS} (T : BigFppfOver B S hS)
    (ι : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X)
    (hι : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) ι)
    (U : FppfSheaf B S hS)
    (V : BigFppfOver B S hS) (q : (uliftYoneda.{u + 1}).obj V ⟶ U.obj)
    (hqs : (MorphismProperty.relative (uliftYoneda.{u + 1}) (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hqe : (MorphismProperty.relative (uliftYoneda.{u + 1}) (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hV : IsReduced ((BigFppfOver.toScheme B S hS).obj V))
    (g : U ⟶ X) :
    ∃! l : U ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T, l ≫ ι = g := by
  let J := BigFppfOver.topology B S hS
  let H := Sheaf.sheafifiedYoneda J
  have hmono : Mono ι := mono_of_represented_thickening B S hS ι hι
  let e := representedSheafIso B S hS V
  let q' : H.obj V ⟶ U := ⟨e.inv ≫ q⟩
  have : Presheaf.IsLocallySurjective J q :=
    isLocallySurjective_of_surjective_etale B S hS q hqs hqe
  have : Sheaf.IsLocallySurjective q' := by
    change Presheaf.IsLocallySurjective J (e.inv ≫ q)
    infer_instance
  have hepi : Epi q' := (Sheaf.isLocallySurjective_iff_epi q').mp inferInstance
  obtain ⟨l₀, hl₀⟩ := reduced_lift_thickening B S hS ι hι V hV (q' ≫ g)
  have : Epi (pullback.fst g ι) := epi_of_epi_fac (pullback.lift_fst q' l₀ (by rw [hl₀]))
  have : IsIso (pullback.fst g ι) := isIso_of_mono_of_epi _
  refine ⟨inv (pullback.fst g ι) ≫ pullback.snd g ι, ?_, ?_⟩
  · change (inv (pullback.fst g ι) ≫ pullback.snd g ι) ≫ ι = g
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  · intro m hm'
    apply (cancel_mono ι).mp
    rw [hm', Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

/-! ### The example -/

private theorem mk_ulift_set_nat : Cardinal.mk (ULift.{u} (Set ℕ)) = 2 ^ Cardinal.aleph0.{u} := by
  simp [Cardinal.mk_uLift, Cardinal.mk_set]

private theorem uncountable_ulift_set_nat : Uncountable (ULift.{u} (Set ℕ)) := by
  rw [← Cardinal.aleph0_lt_mk_iff, mk_ulift_set_nat]
  exact Cardinal.cantor _

private theorem mk_ulift_set_nat_lt_cutoff (B : BigFppfSite.{u}) :
    Cardinal.mk (ULift.{u} (Set ℕ)) < B.cutoff := by
  rw [mk_ulift_set_nat]
  exact B.cutoff_isStrongPrelimit B.aleph0_lt_cutoff

private theorem mk_ulift_rat_lt_cutoff (B : BigFppfSite.{u}) :
    Cardinal.mk (ULift.{u} ℚ) < B.cutoff :=
  (Cardinal.mk_le_aleph0 (α := ULift.{u} ℚ)).trans_lt B.aleph0_lt_cutoff

private theorem contains_spec_ulift_rat (B : BigFppfSite.{u}) :
    B.Contains (Spec (CommRingCat.of (ULift.{u} ℚ))) := by
  rw [BigFppfSite.Contains, Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff (mk_ulift_rat_lt_cutoff B)

private theorem isDirected_ulift_countableSubset (α : Type u) :
    IsDirected (ULift.{u + 1} (CountableSubset α)) (· ≤ ·) :=
  ⟨fun i j => ⟨ULift.up ⟨i.down.val ∪ j.down.val, i.down.property.union j.down.property⟩,
    Set.subset_union_left, Set.subset_union_right⟩⟩

/-- A big fppf site containing the spectrum of a characteristic zero field `K` and an
uncountable set `A`, both of size below its cutoff. -/
private theorem exists_site_field_set :
    ∃ (B : BigFppfSite.{u}) (K : Type u) (_ : Field K) (_ : CharZero K)
      (A : Type u) (_ : Uncountable A),
      Cardinal.mk K < B.cutoff ∧ Cardinal.mk A < B.cutoff ∧
        B.Contains (Spec (CommRingCat.of K)) := by
  obtain ⟨B, _⟩ := AlgebraicGeometry.exists_common_bigFppfSite.{u, 0}
    (fun e : PEmpty.{1} => (e.elim : BigFppfSite.{u}))
  exact ⟨B, ULift.{u} ℚ, inferInstance, (ULift.ringEquiv : ULift.{u} ℚ ≃+* ℚ).toRingHom.charZero,
    ULift.{u} (Set ℕ), uncountable_ulift_set_nat, mk_ulift_rat_lt_cutoff B,
    mk_ulift_set_nat_lt_cutoff B, contains_spec_ulift_rat B⟩

/-- The colimit of the stages of the system is an affine formal algebraic space. -/
private theorem derivative_isAffineFormalAlgebraicSpace (K : Type u) [CommRing K] (α : Type u)
    (B : BigFppfSite.{u}) (hK : Cardinal.mk K < B.cutoff) (hα : Cardinal.mk α < B.cutoff)
    (hS : B.Contains (Spec (CommRingCat.of K))) :
    IsAffineFormalAlgebraicSpace B (Spec (CommRingCat.of K)) hS
      (colimit (derivativeBigAffineDiagram K α B hS (derivative_contains K α B hK hα) ⋙
        BigAffineFppf.inclusion B (Spec (CommRingCat.of K)) hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B (Spec (CommRingCat.of K)) hS))) := by
  let D := derivativeBigAffineDiagram K α B hS (derivative_contains K α B hK hα)
  have : Nonempty (ULift.{u + 1} (CountableSubset α)) := ⟨ULift.up ⟨∅, Set.countable_empty⟩⟩
  have : IsDirected (ULift.{u + 1} (CountableSubset α)) (· ≤ ·) :=
    isDirected_ulift_countableSubset α
  have hD : ∀ ⦃i j : ULift.{u + 1} (CountableSubset α)⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B (Spec (CommRingCat.of K)) hS).map (D.map f)) :=
    fun {_ _} f => derivativeBigAffineDiagram_isThickening K α B hS _ f
  exact ⟨satisfiesSetTheoreticCondition_of_colimit B (Spec (CommRingCat.of K)) hS D hD _
      ⟨Iso.refl _⟩ (exists_represented_coproduct B (Spec (CommRingCat.of K)) hS
        (fun i => (BigAffineFppf.inclusion B (Spec (CommRingCat.of K)) hS).obj (D.obj i))
        (derivative_coproduct_contains K α B hK hα)),
    _, inferInstance, inferInstance, inferInstance, D, hD, ⟨Iso.refl _⟩⟩

/-- **Stacks 0CBD.** There is an affine formal algebraic space whose regular functions do not
separate points: writing `X = colim X_λ` as in Stacks 0AI7, the inverse limit of the rings
`Γ(X_λ, O_{X_λ})` is a field, while the reduction of `X` has infinitely many points. The
reduction is exhibited as a reduced affine scheme `T` of the site together with a
representable thickening `T ⟶ X` through which every morphism to `X` from a reduced algebraic
space factors uniquely, which determines it up to unique isomorphism. -/
@[stacks 0CBD]
public theorem exists_isAffineFormalAlgebraicSpace_sections_isField_reduction_infinite :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS),
      IsAffineFormalAlgebraicSpace B S hS X ∧
      (∃ (I : Type (u + 1)) (pre : Preorder I),
        letI : Preorder I := pre
        Nonempty I ∧ IsDirected I (· ≤ ·) ∧
          ∃ D : I ⥤ BigAffineFppf B S hS,
            (∀ ⦃i j : I⦄ (f : i ⟶ j),
              Stacks.Thickenings.IsThickening
                ((BigAffineFppf.toScheme B S hS).map (D.map f))) ∧
            Nonempty (X ≅ colimit
              (D ⋙ BigAffineFppf.inclusion B S hS ⋙
                Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) ∧
            (letI : CommRing (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections :=
              @Subring.toCommRing (∀ j, (sectionDiagram B S hS D).obj j) _
                (RingCat.sectionsSubring
                  (sectionDiagram B S hS D ⋙ forget₂ CommRingCat RingCat.{u}))
            IsField (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections)) ∧
      (∃ T : BigFppfOver B S hS,
        IsReduced ((BigFppfOver.toScheme B S hS).obj T) ∧
        Infinite ((BigFppfOver.toScheme B S hS).obj T) ∧
        ∃ ι : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X,
          (MorphismProperty.relative
            (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
            (MorphismProperty.inverseImage
              (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
              (BigFppfOver.toScheme B S hS))) ι ∧
          ∀ U : FppfSheaf B S hS, Space.IsAlgebraicSpaceULift.{u + 1} B S hS U.obj →
            (∃ (V : BigFppfOver B S hS) (p : (uliftYoneda.{u + 1}).obj V ⟶ U.obj),
              (MorphismProperty.relative (uliftYoneda.{u + 1})
                (MorphismProperty.inverseImage
                  (@Surjective.{u} : MorphismProperty Scheme.{u})
                  (BigFppfOver.toScheme B S hS))) p ∧
              (MorphismProperty.relative (uliftYoneda.{u + 1})
                (MorphismProperty.inverseImage
                  (@Etale.{u} : MorphismProperty Scheme.{u})
                  (BigFppfOver.toScheme B S hS))) p ∧
              IsReduced ((BigFppfOver.toScheme B S hS).obj V)) →
            ∀ g : U ⟶ X, ∃! l : U ⟶
              (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T, l ≫ ι = g) := by
  classical
  obtain ⟨B, K, _, _, A, _, hK, hA, hS⟩ := exists_site_field_set
  let hstage := derivative_contains K A B hK hA
  let D := derivativeBigAffineDiagram K A B hS hstage
  let I := ULift.{u + 1} (CountableSubset A)
  have : Nonempty I := ⟨ULift.up ⟨∅, Set.countable_empty⟩⟩
  have : IsDirected I (· ≤ ·) := isDirected_ulift_countableSubset A
  let E := D ⋙ BigAffineFppf.inclusion B (Spec (CommRingCat.of K)) hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B (Spec (CommRingCat.of K)) hS)
  let X := colimit E
  have hD : ∀ ⦃i j : I⦄ (f : i ⟶ j), Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B (Spec (CommRingCat.of K)) hS).map (D.map f)) :=
    fun {_ _} f => derivativeBigAffineDiagram_isThickening K A B hS hstage f
  refine ⟨B, Spec (CommRingCat.of K), hS, X,
    derivative_isAffineFormalAlgebraicSpace K A B hK hA hS, ?_, ?_⟩
  · exact ⟨I, inferInstance, inferInstance, inferInstance, D, hD, ⟨Iso.refl _⟩,
      liftedDerivativeGlobalSections_isField K A⟩
  · let i : I := ULift.up ⟨∅, Set.countable_empty⟩
    let T := (BigAffineFppf.inclusion B (Spec (CommRingCat.of K)) hS).obj (D.obj i)
    have hT : IsReduced ((BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hS).obj T) := by
      change IsReduced ((derivativeSchemeDiagram K A).obj ⟨∅, Set.countable_empty⟩)
      exact isReduced_of_isOpenImmersion (derivativeEmptyIso K A).hom
    have hι := isThickening_colimitι B (Spec (CommRingCat.of K)) hS D hD X (Iso.refl _) i
    refine ⟨T, hT, infinite_derivativeSchemeDiagram_empty K A,
      colimit.ι E i ≫ (Iso.refl X).hom, hι, ?_⟩
    rintro U - ⟨V, p, hps, hpe, hV⟩ g
    exact existsUnique_lift_of_reduced_thickening B (Spec (CommRingCat.of K)) hS T _ hι
      U V p hps hpe hV g

/-- The example of Stacks 0CBD, with the two features that obstruct McQuillan's criterion
collected for a single presentation: the inverse limit of the section rings is a field, while
one of the stages has infinitely many points. -/
public theorem exists_isAffineFormalAlgebraicSpace_sections_isField_infinite_stage :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS),
      IsAffineFormalAlgebraicSpace B S hS X ∧
      ∃ (I : Type (u + 1)) (pre : Preorder I),
        letI : Preorder I := pre
        Nonempty I ∧ IsDirected I (· ≤ ·) ∧
          ∃ D : I ⥤ BigAffineFppf B S hS,
            (∀ ⦃i j : I⦄ (f : i ⟶ j),
              Stacks.Thickenings.IsThickening
                ((BigAffineFppf.toScheme B S hS).map (D.map f))) ∧
            Nonempty (X ≅ colimit
              (D ⋙ BigAffineFppf.inclusion B S hS ⋙
                Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) ∧
            (letI : CommRing (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections :=
              @Subring.toCommRing (∀ j, (sectionDiagram B S hS D).obj j) _
                (RingCat.sectionsSubring
                  (sectionDiagram B S hS D ⋙ forget₂ CommRingCat RingCat.{u}))
            IsField (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections) ∧
            ∃ i : I, Infinite ((BigAffineFppf.toScheme B S hS).obj (D.obj i)) := by
  classical
  obtain ⟨B, K, _, _, A, _, hK, hA, hS⟩ := exists_site_field_set
  let hstage := derivative_contains K A B hK hA
  let D := derivativeBigAffineDiagram K A B hS hstage
  let I := ULift.{u + 1} (CountableSubset A)
  have : Nonempty I := ⟨ULift.up ⟨∅, Set.countable_empty⟩⟩
  have : IsDirected I (· ≤ ·) := isDirected_ulift_countableSubset A
  let E := D ⋙ BigAffineFppf.inclusion B (Spec (CommRingCat.of K)) hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B (Spec (CommRingCat.of K)) hS)
  let X := colimit E
  have hD : ∀ ⦃i j : I⦄ (f : i ⟶ j), Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B (Spec (CommRingCat.of K)) hS).map (D.map f)) :=
    fun {_ _} f => derivativeBigAffineDiagram_isThickening K A B hS hstage f
  let i : I := ULift.up ⟨∅, Set.countable_empty⟩
  refine ⟨B, Spec (CommRingCat.of K), hS, X,
    derivative_isAffineFormalAlgebraicSpace K A B hK hA hS, I, inferInstance, inferInstance,
    inferInstance, D, hD, ⟨Iso.refl _⟩, liftedDerivativeGlobalSections_isField K A, i,
    infinite_derivativeSchemeDiagram_empty K A⟩

end AlgebraicGeometry.FormalSpace

end
