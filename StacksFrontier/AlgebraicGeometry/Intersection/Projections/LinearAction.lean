module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModule
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation

/-!
# The action of the general linear group on the projective space of a module

A linear map `f : M →ₗ[R] N` induces an algebra homomorphism `Sym f` of symmetric algebras which
respects the grading by symmetric powers, hence a homomorphism of graded rings. When `f` is an
invertible endomorphism of `V` the image of the irrelevant ideal is again the irrelevant ideal,
so `Proj` turns it into a morphism `P(V) ⟶ P(V)` of the projective space of `V`. Since `Proj` is
contravariant this is a right action of `GL(V)`; inverting gives the left action by scheme
automorphisms, and its effective quotient is the projective general linear group of `V`.

## Main definitions

* `SymPow.gradedSymAlgMap`: the graded ring homomorphism of symmetric algebras induced by a
  linear map.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.map`: the morphism of projective spaces induced by
  an invertible linear map.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.generalLinearToAut`: the left action of `GL(V)` by
  scheme automorphisms of `P(V)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.ProjGenLinGroup`: the projective general linear
  group `PGL(V)`, namely `GL(V)` modulo the kernel of that action.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.toAut`: the induced faithful action of `PGL(V)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.ClosedPoints`: the closed points of `P(V)`, which
  `PGL(V)` also acts on.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.map_one` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.map_mul`: functoriality of the construction.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.map_eq_id_of_eq_smul_id`: a scalar multiple of the
  identity acts trivially, so the action really factors through a quotient of `GL(V)`.

## Implementation notes

The projective space of `V` is `AlgebraicGeometry.projectiveSpaceOfModule`, that is
`Proj (Sym_R V)` graded by symmetric powers, whose closed points over an algebraically closed
field are the one-dimensional quotients of `V`. Nothing in this file needs `V` to be
finite-dimensional or the base to be a field: the base is any commutative ring, except where a
unit of it is produced, and `map_eq_id_of_eq_smul_id` is stated for a scalar which is a unit.

The group `PGL(V)` is defined as the quotient of `GL(V)` by the kernel of its action on `P(V)`
rather than by the centre of `GL(V)`, so that the induced action is faithful by construction.
For a nontrivial module over a field the two subgroups agree: the kernel consists exactly of the
scalar multiples of the identity, which is
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_eq_smul_id_of_map_eq_id` together with
`map_eq_id_of_eq_smul_id`.

## References

* [Stacks Project, Tag 0B2U](https://stacks.math.columbia.edu/tag/0B2U)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public section

open CategoryTheory

namespace SymPow

section Functoriality

variable {R M N P : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/-- Functoriality of the symmetric algebra is compatible with composition. -/
public theorem symAlgMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    symAlgMap (g ∘ₗ f) = (symAlgMap g).comp (symAlgMap f) := by
  apply SymmetricAlgebra.algHom_ext
  ext m
  simp [symAlgMap_ι]

/-- `Sym` of a composite, applied to an element. -/
public theorem symAlgMap_comp_apply (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (x : SymmetricAlgebra R M) : symAlgMap (g ∘ₗ f) x = symAlgMap g (symAlgMap f x) :=
  DFunLike.congr_fun (symAlgMap_comp f g) x

/-- `Sym` of the identity is the identity. -/
public theorem symAlgMap_id : symAlgMap (LinearMap.id : M →ₗ[R] M) = AlgHom.id R _ := by
  apply SymmetricAlgebra.algHom_ext
  ext m
  simp [symAlgMap_ι]

/-- `Sym` of the identity, applied to an element. -/
public theorem symAlgMap_id_apply (x : SymmetricAlgebra R M) :
    symAlgMap (LinearMap.id : M →ₗ[R] M) x = x :=
  DFunLike.congr_fun symAlgMap_id x

/-- On the degree-`n` part, `Sym` of a scalar multiple of a linear map is the `n`-th power of
that scalar times `Sym` of the map. -/
public theorem symAlgMap_smul_homogeneous (c : R) (f : M →ₗ[R] N) {n : ℕ}
    {x : SymmetricAlgebra R M} (hx : x ∈ symmetricPower n R M) :
    symAlgMap (c • f) x = c ^ n • symAlgMap f x := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add a b i ha hb ia ib => simp only [map_add, ia, ib, smul_add]
  | mem_mul a ha i b hb ih =>
    obtain ⟨v, rfl⟩ := ha
    simp only [map_mul, symAlgMap_ι, LinearMap.smul_apply, map_smul, ih]
    rw [smul_mul_smul, pow_succ']

end Functoriality

section Graded

variable {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- The homomorphism of graded rings induced by a linear map: `Sym f` carries the degree-`n`
symmetric power of `M` into the degree-`n` symmetric power of `N`. -/
public noncomputable def gradedSymAlgMap (f : M →ₗ[R] N) :
    (fun n => symmetricPower n R M) →+*ᵍ (fun n => symmetricPower n R N) where
  __ := (symAlgMap f).toRingHom
  map_mem := fun {n} {x} hx => symAlgMap_mapsTo n f x hx

/-- The graded homomorphism induced by a linear map acts as the induced algebra
homomorphism. -/
public theorem gradedSymAlgMap_apply (f : M →ₗ[R] N) (x : SymmetricAlgebra R M) :
    gradedSymAlgMap f x = symAlgMap f x := rfl

/-- The graded homomorphism induced by the identity is the identity. -/
public theorem gradedSymAlgMap_id :
    gradedSymAlgMap (LinearMap.id : M →ₗ[R] M) = .id _ :=
  GradedRingHom.ext fun x => symAlgMap_id_apply x

/-- The graded homomorphism induced by a composite is the composite of the graded
homomorphisms. -/
public theorem gradedSymAlgMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    gradedSymAlgMap (g ∘ₗ f) = (gradedSymAlgMap g).comp (gradedSymAlgMap f) :=
  GradedRingHom.ext fun x => symAlgMap_comp_apply f g x

end Graded

end SymPow

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u v

variable (k : Type u) (V : Type v) [CommRing k] [AddCommGroup V] [Module k V]

/-- An invertible linear map induces a graded homomorphism of symmetric algebras whose image
contains the irrelevant ideal, which is Mathlib's hypothesis for `AlgebraicGeometry.Proj.map`. -/
public theorem irrelevant_le_map_gradedSymAlgMap (g : LinearMap.GeneralLinearGroup k V) :
    HomogeneousIdeal.irrelevant (fun n => SymPow.symmetricPower n k V) ≤
      (HomogeneousIdeal.irrelevant (fun n => SymPow.symmetricPower n k V)).map
        (SymPow.gradedSymAlgMap (g : V →ₗ[k] V)) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn x hx
  obtain ⟨y, hy⟩ := SymPow.symMap_surjective n (g : V →ₗ[k] V)
    g.toLinearEquiv.surjective ⟨x, hx⟩
  have hxy : SymPow.gradedSymAlgMap (g : V →ₗ[k] V) y = x := congrArg Subtype.val hy
  rw [← hxy]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ hn y.property)

/-- The morphism `Proj (Sym g)` of projective spaces induced by an invertible linear map `g`,
acting on one-dimensional quotients of `V` by precomposition with `g`. -/
public noncomputable def map (g : LinearMap.GeneralLinearGroup k V) :
    projectiveSpaceOfModule k V ⟶ projectiveSpaceOfModule k V :=
  Proj.map (SymPow.gradedSymAlgMap (g : V →ₗ[k] V)) (irrelevant_le_map_gradedSymAlgMap k V g)

/-- The identity induces the identity morphism. -/
@[simp]
public theorem map_one : map k V 1 = 𝟙 _ := by
  unfold map
  have h : ((1 : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) = LinearMap.id := rfl
  simp only [h, SymPow.gradedSymAlgMap_id, Proj.map_id]

/-- The construction is contravariantly functorial: a product acts by the composite in the
opposite order. -/
public theorem map_mul (g h : LinearMap.GeneralLinearGroup k V) :
    map k V (g * h) = map k V g ≫ map k V h := by
  unfold map
  have heq : ((g * h : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) =
      (g : V →ₗ[k] V) ∘ₗ (h : V →ₗ[k] V) := rfl
  simp only [heq, SymPow.gradedSymAlgMap_comp]
  exact Proj.map_comp _ _ (irrelevant_le_map_gradedSymAlgMap k V h)
    (irrelevant_le_map_gradedSymAlgMap k V g)

/-- A linear endomorphism which is a scalar multiple of the identity acts on the degree-`n`
part of the symmetric algebra as multiplication by the `n`-th power of that scalar. -/
public theorem gradedSymAlgMap_apply_of_eq_smul_id {g : LinearMap.GeneralLinearGroup k V}
    {c : k} (hg : (g : V →ₗ[k] V) = c • LinearMap.id) {n : ℕ} {x : SymmetricAlgebra k V}
    (hx : x ∈ SymPow.symmetricPower n k V) :
    SymPow.gradedSymAlgMap (g : V →ₗ[k] V) x = c ^ n • x := by
  rw [SymPow.gradedSymAlgMap_apply, hg, SymPow.symAlgMap_smul_homogeneous c LinearMap.id hx,
    SymPow.symAlgMap_id_apply]

/-- A unit scalar multiple of the identity fixes every point of `P(V)`: in each degree it acts
by a unit, so it preserves every homogeneous ideal. -/
public theorem map_apply_of_eq_smul_id (g : LinearMap.GeneralLinearGroup k V) (c : kˣ)
    (hg : (g : V →ₗ[k] V) = (c : k) • LinearMap.id)
    (p : projectiveSpaceOfModule k V) : map k V g p = p := by
  have hmem (d : k) {y : SymmetricAlgebra k V} (hy : y ∈ p.asHomogeneousIdeal.toIdeal) :
      d • y ∈ p.asHomogeneousIdeal.toIdeal :=
    Submodule.smul_mem (p.asHomogeneousIdeal.toIdeal.restrictScalars k) d hy
  apply ProjectiveSpectrum.ext
  ext x
  show SymPow.gradedSymAlgMap (g : V →ₗ[k] V) x ∈ p.asHomogeneousIdeal.toIdeal ↔
    x ∈ p.asHomogeneousIdeal.toIdeal
  rw [p.asHomogeneousIdeal.isHomogeneous.mem_iff, p.asHomogeneousIdeal.isHomogeneous.mem_iff]
  refine forall_congr' fun n => ?_
  rw [← GradedRingHom.map_directSumDecompose, gradedSymAlgMap_apply_of_eq_smul_id k V hg
    (DirectSum.decompose (fun n => SymPow.symmetricPower n k V) x n).property]
  refine ⟨fun hx => ?_, hmem _⟩
  simpa [smul_smul, ← mul_pow] using hmem (((c⁻¹ : kˣ) : k) ^ n) hx

/-- At a prime of the symmetric algebra, the map of local rings induced by a scalar multiple of
the identity is the identity: numerator and denominator of a homogeneous fraction have the same
degree, so the two scalars cancel. -/
public theorem localRingHom_val_eq_self {g : LinearMap.GeneralLinearGroup k V} {c : k}
    (hg : (g : V →ₗ[k] V) = c • LinearMap.id)
    (P : Ideal (SymmetricAlgebra k V)) [P.IsPrime]
    (hI : P = P.comap (SymPow.gradedSymAlgMap (g : V →ₗ[k] V)).toRingHom)
    (t : HomogeneousLocalization.AtPrime (fun n => SymPow.symmetricPower n k V) P) :
    Localization.localRingHom P P
        (SymPow.gradedSymAlgMap (g : V →ₗ[k] V)).toRingHom hI t.val = t.val := by
  obtain ⟨⟨n, a, b, hb⟩, rfl⟩ := t.mk_surjective
  rw [HomogeneousLocalization.val_mk, Localization.localRingHom_mk]
  apply Localization.mk_eq_mk_iff.mpr
  apply Localization.r_of_eq
  show (b : SymmetricAlgebra k V) * SymPow.gradedSymAlgMap (g : V →ₗ[k] V) a =
    SymPow.gradedSymAlgMap (g : V →ₗ[k] V) b * a
  rw [gradedSymAlgMap_apply_of_eq_smul_id k V hg a.property,
    gradedSymAlgMap_apply_of_eq_smul_id k V hg b.property]
  simp [Algebra.smul_def, mul_left_comm, mul_comm]

/-- A unit scalar multiple of the identity induces the identity morphism, so the action of
`GL(V)` on `P(V)` factors through a quotient. -/
public theorem map_eq_id_of_eq_smul_id (g : LinearMap.GeneralLinearGroup k V) (c : kˣ)
    (hg : (g : V →ₗ[k] V) = (c : k) • LinearMap.id) : map k V g = 𝟙 _ := by
  have hpoint := map_apply_of_eq_smul_id k V g c hg
  have hbase : (map k V g).base =
      (𝟙 (projectiveSpaceOfModule k V) :
        projectiveSpaceOfModule k V ⟶ projectiveSpaceOfModule k V).base := by
    ext p
    exact hpoint p
  apply Scheme.Hom.ext hbase
  intro U
  ext s : 2
  apply Subtype.ext
  funext p
  apply HomogeneousLocalization.val_injective
  have : p.val.asHomogeneousIdeal.toIdeal.IsPrime := p.val.isPrime
  show (HomogeneousLocalization.localRingHom (SymPow.gradedSymAlgMap (g : V →ₗ[k] V)) _ _ rfl
    (s.val ⟨map k V g p.val, _⟩)).val = (s.val p).val
  refine (HomogeneousLocalization.val_localRingHom _).trans ?_
  have hlocal (q : U) (hqp : q = p)
      (hI : q.val.asHomogeneousIdeal.toIdeal =
        p.val.asHomogeneousIdeal.toIdeal.comap
          (SymPow.gradedSymAlgMap (g : V →ₗ[k] V)).toRingHom) :
      let := q.val.isPrime
      Localization.localRingHom q.val.asHomogeneousIdeal.toIdeal
          p.val.asHomogeneousIdeal.toIdeal
          (SymPow.gradedSymAlgMap (g : V →ₗ[k] V)).toRingHom hI (s.val q).val = (s.val p).val := by
    subst q
    exact localRingHom_val_eq_self k V hg _ hI (s.val p)
  exact hlocal ⟨map k V g p.val, _⟩ (Subtype.ext (hpoint p.val)) rfl

/-- The left action of the general linear group of `V` by scheme automorphisms of `P(V)`. The
inverse accounts for the contravariance of `Proj`. -/
public noncomputable def generalLinearToAut :
    LinearMap.GeneralLinearGroup k V →* Aut (projectiveSpaceOfModule k V) where
  toFun g :=
    .of
      { hom := map k V g⁻¹
        inv := map k V g
        hom_inv_id := by rw [← map_mul, inv_mul_cancel, map_one]
        inv_hom_id := by rw [← map_mul, mul_inv_cancel, map_one] }
  map_one' := Aut.ext (Iso.ext (map_one k V))
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    change map k V (g * h)⁻¹ = map k V h⁻¹ ≫ map k V g⁻¹
    rw [mul_inv_rev, map_mul]

/-- The projective general linear group `PGL(V)`: the general linear group of `V` modulo the
kernel of its action by scheme automorphisms of `P(V)`. -/
public noncomputable abbrev ProjGenLinGroup :=
  LinearMap.GeneralLinearGroup k V ⧸ (generalLinearToAut k V).ker

/-- The faithful action of `PGL(V)` by scheme automorphisms of `P(V)`. -/
public noncomputable def toAut :
    ProjGenLinGroup k V →* Aut (projectiveSpaceOfModule k V) :=
  QuotientGroup.lift _ (generalLinearToAut k V) le_rfl

public noncomputable instance : MulAction (ProjGenLinGroup k V) (projectiveSpaceOfModule k V) :=
  let toEnd : Aut (projectiveSpaceOfModule k V) →*
      Function.End (projectiveSpaceOfModule k V) :=
    { toFun e p := e.asIso.hom p
      map_one' := rfl
      map_mul' _ _ := rfl }
  MulAction.ofEndHom (toEnd.comp (toAut k V))

/-- The closed points of `P(V)`. Over an algebraically closed field and for finite-dimensional
`V` these are the one-dimensional quotients of `V`. -/
public abbrev ClosedPoints := {p : projectiveSpaceOfModule k V // IsClosed ({p} : Set _)}

public noncomputable instance : MulAction (ProjGenLinGroup k V) (ClosedPoints k V) :=
  let toEnd : Aut (projectiveSpaceOfModule k V) →* Function.End (ClosedPoints k V) :=
    { toFun e p := ⟨e.asIso.hom p.val, by
        have h := (Scheme.homeoOfIso e.asIso).isClosedMap _ p.property
        rw [Set.image_singleton] at h
        exact h⟩
      map_one' := funext fun _ => Subtype.ext rfl
      map_mul' _ _ := funext fun _ => Subtype.ext rfl }
  MulAction.ofEndHom (toEnd.comp (toAut k V))

/-- The class of `g` in `PGL(V)` acts as the scheme morphism `Proj (Sym g⁻¹)`. -/
public theorem mk_smul_eq_map (g : LinearMap.GeneralLinearGroup k V)
    (p : projectiveSpaceOfModule k V) :
    (g : ProjGenLinGroup k V) • p = map k V g⁻¹ p := rfl

/-- The action on closed points is the restriction of the action on all points. -/
public theorem coe_smul_closedPoints (g : ProjGenLinGroup k V) (p : ClosedPoints k V) :
    (g • p).val = g • p.val := rfl

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
