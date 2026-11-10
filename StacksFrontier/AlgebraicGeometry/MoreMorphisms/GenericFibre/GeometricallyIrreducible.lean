module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Smooth.Fiber
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.GeometricComponents
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.ComponentsOverFiniteSeparableExtension
public import StacksFrontier.RingTheory.Spectrum.Prime.IrreducibleFibres

/-!
# Making the components of the generic fibre geometrically irreducible

For a quasi-compact morphism `f : X ⟶ Y` locally of finite type onto an irreducible scheme, there
is a nonempty open `V` of `Y` and a finite étale surjective cover `g : Y' ⟶ V` by an irreducible
affine scheme such that every irreducible component of the generic fibre of the base change
`X ×_Y Y' ⟶ Y'` is geometrically irreducible.

The cover is produced from a single polynomial. Pick a nonempty affine open `V₀ = Spec A` of `Y`
and let `K = κ(η₀)` be its function field. By Stacks 054R there is a finite separable extension
`K'/K` over which every irreducible component of the generic fibre becomes geometrically
irreducible. Write `K' = K(α)`, clear denominators in the minimal polynomial of `α` to get a
monic `Q ∈ A[T]`, and set `B = A[T]/(Q)`. Then `B` is finite free over `A`, its fibre over the
generic point is the field `K'`, so `Spec B` is irreducible and has a unique point over the
generic point; `Spec B → Spec A` is étale there, hence étale after inverting one element, which
cuts out the open `V`. Finally the generic fibre of the base change is, as an arrow, isomorphic
to the base change of the generic fibre to `K'`, so Stacks 054R applies to it.

## Main results

* `AlgebraicGeometry.exists_nonemptyOpen_finiteEtale_cover_geometricallyIrreducible_genericFiber`
  constructs the open subscheme and the finite étale cover.

## Implementation notes

Both fibre products of the source are retained: `X_V = V ×_Y X` and `X' = Y' ×_Y X`, and the
statement records through `IsPullback g' f' fV g` that `X'` is also `Y' ×_V X_V`. An irreducible
component is equipped with its reduced induced closed subscheme structure, through
`Scheme.IdealSheafData.vanishingIdeal`, exactly as in Stacks 054R.

The ring-theoretic half of the construction — étaleness of `A[T]/(Q)` away from the derivative
and the spreading out of étaleness over the fibre — is
`Stacks.GeometricComponents.isEtaleAt_of_derivative_notMem` and
`Stacks.GeometricComponents.exists_notMem_etale_localizationAway`.

## References

* [Stacks Project, Tag 0551](https://stacks.math.columbia.edu/tag/0551)
* [Stacks Project, Tag 054R](https://stacks.math.columbia.edu/tag/054R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Polynomial
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- A monic polynomial over the residue field of a prime becomes, after rescaling its roots by
a unit, the reduction of a monic polynomial over the ring itself. -/
private lemma exists_monic_lift_scaled {R : Type u} [CommRing R] (p : Ideal R)
    [p.IsPrime] (q : p.ResidueField[X]) (hq : q.Monic) :
    ∃ c : p.ResidueField, IsUnit c ∧ ∃ f : R[X], f.Monic ∧
      f.map (algebraMap R p.ResidueField) = q.scaleRoots c := by
  let A := R ⧸ p
  let M := nonZeroDivisors A
  let b := IsLocalization.commonDenom M q.support q.coeff
  let c := algebraMap A p.ResidueField b
  have hlifts : q.scaleRoots c ∈ Polynomial.lifts (algebraMap A p.ResidueField) :=
    IsLocalization.scaleRoots_commonDenom_mem_lifts M q
      (by rw [hq.leadingCoeff]; exact one_mem (algebraMap A p.ResidueField).range)
  have hlifts' : q.scaleRoots c ∈ Polynomial.lifts (algebraMap R p.ResidueField) := by
    rw [Polynomial.lifts_iff_coeff_lifts] at hlifts ⊢
    intro i
    obtain ⟨a, ha⟩ := hlifts i
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨r, by rw [← ha, Ideal.algebraMap_quotient_residueField_mk]⟩
  obtain ⟨f, hfmap, -, hfmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts' ((monic_scaleRoots_iff c).mpr hq)
  exact ⟨c, IsLocalization.map_units p.ResidueField b, f, hfmonic, hfmap⟩

/-- The residue field of a point of an affine open, computed in the ring of functions on that
open. -/
private noncomputable def affineOpen_residueFieldEquiv {Y : Scheme.{u}}
    (V : Y.Opens) (hV : IsAffineOpen V) (x : V.toScheme) :
    (hV.primeIdealOf x).asIdeal.ResidueField ≃+* V.toScheme.residueField x := by
  let p := hV.primeIdealOf x
  let f : V.toScheme ⟶ Spec Γ(Y, V) := hV.isoSpec.hom
  have : IsOpenImmersion f := inferInstance
  let e₂ : (Spec Γ(Y, V)).residueField p ≅ V.toScheme.residueField x :=
    @asIso CommRingCat _ _ _ (f.residueFieldMap x)
      (Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion f x)
  exact ((Scheme.Spec.residueFieldIso (.of Γ(Y, V)) p).symm ≪≫ e₂).commRingCatIsoToRingEquiv

/-- An irreducible scheme has a nonempty affine open. -/
private lemma exists_nonempty_affineOpen (Y : Scheme.{u}) [IrreducibleSpace Y] :
    ∃ V : Y.Opens, V.1.Nonempty ∧ IsAffineOpen V := by
  obtain ⟨V, hV, hη, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := genericPoint Y) (U := ⊤) (by simp)
  exact ⟨V, ⟨_, hη⟩, hV⟩

/-- The spectrum of the ring of functions on a nonempty affine open of an irreducible scheme is
irreducible. -/
private lemma irreducibleSpace_affineOpen_sections {Y : Scheme.{u}}
    [IrreducibleSpace Y] (V : Y.Opens) (hV : IsAffineOpen V)
    [Nonempty V.toScheme] : IrreducibleSpace (PrimeSpectrum Γ(Y, V)) := by
  have : IrreducibleSpace V.toScheme := V.ι.isOpenEmbedding.irreducibleSpace
  exact hV.isoSpec.schemeIsoToHomeo.irreducibleSpace_iff.mp inferInstance

/-- The prime corresponding to the generic point of an irreducible affine open is dense in the
spectrum of the ring of functions. -/
private lemma dense_primeIdealOf_genericPoint {Y : Scheme.{u}}
    (V : Y.Opens) (hV : IsAffineOpen V) [IrreducibleSpace V.toScheme] :
    Dense ({hV.primeIdealOf (genericPoint V.toScheme)} : Set (Spec Γ(Y, V))) := by
  let e := hV.isoSpec.schemeIsoToHomeo
  have hg := (genericPoint_spec V.toScheme).image e.continuous
  have he : closure (e '' (Set.univ : Set V.toScheme)) = Set.univ := by
    rw [Set.image_univ_of_surjective e.surjective, closure_univ]
  apply dense_iff_closure_eq.mpr
  have hmap : e (genericPoint V.toScheme) = hV.isoSpec.hom (genericPoint V.toScheme) := rfl
  have hcl := hg.def
  rwa [he, hmap] at hcl

/-- A continuous surjection maps a generic point of the whole space to a generic point. -/
private lemma isGenericPoint_univ_map {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {x : α} (hx : IsGenericPoint x Set.univ) {f : α → β} (hf : Continuous f)
    (hs : Function.Surjective f) : IsGenericPoint (f x) Set.univ := by
  simpa [Set.image_univ_of_surjective hs] using hx.image hf

/-- Base changing a fibre product along a further morphism to the base is again a pullback
square. -/
private lemma baseChange_isPullback {X Y Z W : Scheme.{u}}
    (i : W ⟶ Y) (f : X ⟶ Y) (g : Z ⟶ W) :
    IsPullback
      (pullback.lift (pullback.fst (g ≫ i) f ≫ g) (pullback.snd (g ≫ i) f)
        (by rw [Category.assoc]; exact pullback.condition))
      (pullback.fst (g ≫ i) f) (pullback.fst i f) g := by
  apply IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback i f).flip
  simpa only [pullback.lift_snd] using (IsPullback.of_hasPullback (g ≫ i) f).flip

/-- Surjectivity, finiteness and étaleness pass to the base change of a cover of an open of the
base. -/
private lemma baseChange_surjective_finite_etale {X Y Z W : Scheme.{u}}
    (i : W ⟶ Y) (f : X ⟶ Y) (g : Z ⟶ W)
    [Surjective g] [IsFinite g] [Etale g] :
    let g' := pullback.lift (pullback.fst (g ≫ i) f ≫ g) (pullback.snd (g ≫ i) f)
      (by rw [Category.assoc]; exact pullback.condition)
    Surjective g' ∧ IsFinite g' ∧ Etale g' := by
  have h := baseChange_isPullback i f g
  exact ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback h.flip inferInstance,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback h.flip inferInstance,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback h.flip inferInstance⟩

/-- The minimal polynomial of a unit multiple of the root of an irreducible monic polynomial is
the polynomial with rescaled roots. -/
private lemma minpoly_smul_root_eq_scaleRoots {K : Type u} [Field K]
    {P : K[X]} (hP : Irreducible P) (hmonic : P.Monic) {c : K} (hc : IsUnit c) :
    minpoly K (c • AdjoinRoot.root P) = P.scaleRoots c := by
  have : Fact (Irreducible P) := ⟨hP⟩
  have hroot : minpoly K (AdjoinRoot.root P) = P := by
    rw [AdjoinRoot.minpoly_root hP.ne_zero, hmonic.leadingCoeff, inv_one, C_1, mul_one]
  have := IsIntegrallyClosed.minpoly_smul (R := K) (S := AdjoinRoot P)
    (r := c) (s := AdjoinRoot.root P) hc.ne_zero (AdjoinRoot.isIntegral_root hP.ne_zero)
  rwa [hroot] at this

/-- Rescaling the roots of an irreducible monic polynomial by a unit keeps it irreducible. -/
private lemma irreducible_scaleRoots_of_isUnit {K : Type u} [Field K]
    {P : K[X]} (hP : Irreducible P) (hmonic : P.Monic) {c : K} (hc : IsUnit c) :
    Irreducible (P.scaleRoots c) := by
  have : Fact (Irreducible P) := ⟨hP⟩
  rw [← minpoly_smul_root_eq_scaleRoots hP hmonic hc]
  exact minpoly.irreducible ((AdjoinRoot.isIntegral_root hP.ne_zero).smul c)

/-- Rescaling the roots of an irreducible monic separable polynomial by a unit keeps it
separable. -/
private lemma separable_scaleRoots_of_isUnit {K : Type u} [Field K]
    {P : K[X]} (hP : Irreducible P) (hmonic : P.Monic) (hsep : P.Separable)
    {c : K} (hc : IsUnit c) : (P.scaleRoots c).Separable := by
  have : Fact (Irreducible P) := ⟨hP⟩
  have hrootsep : IsSeparable K (AdjoinRoot.root P) := by
    have h1 := minpoly_smul_root_eq_scaleRoots hP hmonic isUnit_one
    rw [one_smul, Polynomial.scaleRoots_one] at h1
    change (minpoly K (AdjoinRoot.root P)).Separable
    rwa [h1]
  have hscaledsep : IsSeparable K (c • AdjoinRoot.root P) := by
    rw [Algebra.smul_def]
    exact Field.isSeparable_mul (isSeparable_algebraMap c) hrootsep
  change (minpoly K (c • AdjoinRoot.root P)).Separable at hscaledsep
  rwa [minpoly_smul_root_eq_scaleRoots hP hmonic hc] at hscaledsep

/-- The fibre of `R[T]/(Q)` over a prime is the quotient of the residue field's polynomial ring
by the reduction of `Q`. -/
private noncomputable def fiber_adjoinRootAlgEquiv
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K] (Q : R[X]) :
    K ⊗[R] AdjoinRoot Q ≃ₐ[K] AdjoinRoot (Q.map (algebraMap R K)) := by
  let g : (K ⊗[R] R)[X] :=
    Q.map (Algebra.TensorProduct.includeRight : R →ₐ[R] K ⊗[R] R).toRingHom
  have hg : g.map (Algebra.TensorProduct.rid R K K) = Q.map (algebraMap R K) := by
    dsimp [g]
    rw [Polynomial.map_map]
    congr 1
    ext r
    simp [Algebra.smul_def]
  exact (AdjoinRoot.tensorAlgEquiv Q g rfl).trans
    (AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid R K K) g
      (Q.map (algebraMap R K)) (hg ▸ Associated.refl _))

/-- If the reduction of `Q` over the residue field of `p` is irreducible, the fibre of
`R[T]/(Q)` over `p` is a field. -/
private lemma isField_fiber_adjoinRoot {R K : Type u} [CommRing R] [Field K]
    [Algebra R K] (Q : R[X]) (hQ : Irreducible (Q.map (algebraMap R K))) :
    IsField (K ⊗[R] AdjoinRoot Q) :=
  (fiber_adjoinRootAlgEquiv Q).toRingEquiv.isField
    ((AdjoinRoot.isField_iff_irreducible).2 hQ)

/-- If the fibre of `S` over a prime `p` of `R` is a field, there is exactly one prime of `S`
over `p`. -/
@[instance_reducible]
private noncomputable def unique_primesOver_of_isField_fiber {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
    (h : IsField (p.Fiber S)) : Unique (p.primesOver S) := by
  let : Field (p.Fiber S) := h.toField
  exact (PrimeSpectrum.primesOverOrderIsoFiber R S p).toEquiv.unique

/-- Spreading out étaleness over the fibre, in the form needed here: a module-finite finitely
presented algebra with a unique prime over `p`, étale there, becomes étale after inverting one
element outside `p`. -/
private lemma exists_base_basicOpen_etale
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : Ideal R) [p.IsPrime] [Unique (p.primesOver S)]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hq : Algebra.IsEtaleAt R q) :
    ∃ r : R, r ∉ p ∧ Algebra.Etale R (Localization.Away (algebraMap R S r)) := by
  refine Stacks.GeometricComponents.exists_notMem_etale_localizationAway p ?_
  intro q' _ hq'over
  obtain rfl : q' = q := congrArg Subtype.val
    (Subsingleton.elim (⟨q', ‹_›, hq'over⟩ : p.primesOver S) ⟨q, inferInstance, inferInstance⟩)
  exact hq

/-- If `R → Localization.Away (algebraMap R S r)` is étale, so is the localization map
`R_r → S_{r}`. -/
private lemma etale_awayMap_of_etale_awayTarget
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (r : R) (h : Algebra.Etale R (Localization.Away (algebraMap R S r))) :
    (Localization.awayMap (algebraMap R S) r).Etale := by
  let φ := Localization.awayMap (algebraMap R S) r
  let : Algebra (Localization.Away r) (Localization.Away (algebraMap R S r)) := φ.toAlgebra
  have : Algebra.Etale R (Localization.Away r) := Algebra.Etale.of_isLocalizationAway r
  have : Algebra.Etale R (Localization.Away (algebraMap R S r)) := h
  have hst : IsScalarTower R (Localization.Away r)
      (Localization.Away (algebraMap R S r)) := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change algebraMap R _ z = φ (algebraMap R (Localization.Away r) z)
    simpa [φ, Localization.awayMap, IsLocalization.Away.map] using
      (IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S r)) z)
  exact Algebra.Etale.of_restrictScalars R _ _

/-- Rescaling the roots of a polynomial by a unit does not change the algebra it generates. -/
private noncomputable def adjoinRoot_scaleRootsEquiv
    {K : Type u} [Field K] (P : K[X]) (c : K) (hc : c ≠ 0) :
    AdjoinRoot (P.scaleRoots c) ≃ₐ[K] AdjoinRoot P := by
  let Q := P.scaleRoots c
  have hrootP : (aeval (AdjoinRoot.root P)) P = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hrootQ : (aeval (AdjoinRoot.root Q)) Q = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hQinv : Q.scaleRoots c⁻¹ = P := by
    change (P.scaleRoots c).scaleRoots c⁻¹ = P
    rw [← Polynomial.scaleRoots_mul, mul_inv_cancel₀ hc, Polynomial.scaleRoots_one]
  have hF : (aeval (c * AdjoinRoot.root P)) Q = 0 :=
    Polynomial.scaleRoots_aeval_eq_zero hrootP
  have hG : (aeval (c⁻¹ * AdjoinRoot.root Q)) P = 0 := by
    rw [← hQinv]
    exact Polynomial.scaleRoots_aeval_eq_zero hrootQ
  let F : AdjoinRoot Q →ₐ[K] AdjoinRoot P :=
    AdjoinRoot.liftAlgHom Q (Algebra.ofId K _) (c * AdjoinRoot.root P) hF
  let G : AdjoinRoot P →ₐ[K] AdjoinRoot Q :=
    AdjoinRoot.liftAlgHom P (Algebra.ofId K _) (c⁻¹ * AdjoinRoot.root Q) hG
  have hFroot : F (AdjoinRoot.root Q) = c * AdjoinRoot.root P :=
    AdjoinRoot.liftAlgHom_root Q (Algebra.ofId K _) _ hF
  have hGroot : G (AdjoinRoot.root P) = c⁻¹ * AdjoinRoot.root Q :=
    AdjoinRoot.liftAlgHom_root P (Algebra.ofId K _) _ hG
  have hGF : G.comp F = AlgHom.id K (AdjoinRoot Q) := by
    apply AdjoinRoot.algHom_ext
    change G (F (AdjoinRoot.root Q)) = AdjoinRoot.root Q
    rw [hFroot, map_mul]
    change G ((algebraMap K (AdjoinRoot P)) c) * G (AdjoinRoot.root P) = _
    rw [AlgHom.commutes, hGroot]
    change (AdjoinRoot.of Q) c * ((AdjoinRoot.of Q) c⁻¹ * AdjoinRoot.root Q) = _
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
  have hFG : F.comp G = AlgHom.id K (AdjoinRoot P) := by
    apply AdjoinRoot.algHom_ext
    change F (G (AdjoinRoot.root P)) = AdjoinRoot.root P
    rw [hGroot, map_mul]
    change F ((algebraMap K (AdjoinRoot Q)) c⁻¹) * F (AdjoinRoot.root Q) = _
    rw [AlgHom.commutes, hFroot]
    change (AdjoinRoot.of P) c⁻¹ * ((AdjoinRoot.of P) c * AdjoinRoot.root P) = _
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  exact AlgEquiv.ofAlgHom F G hFG hGF

/-- The canonical map from the fibre of `S` over a prime `p` to the residue field of a prime of
`S` over `p`. -/
private noncomputable def fiberToResidueField
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver p q
    letI : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) := inferInstance
    p.Fiber S →ₐ[p.ResidueField] q.ResidueField :=
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  letI : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) := inferInstance
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (IsScalarTower.toAlgHom R S q.ResidueField) (fun _ _ => Commute.all _ _)

/-- When the fibre of a module-finite algebra over a prime `p` is a field, it is the residue
field at the unique prime over `p`. -/
private noncomputable def fiberEquivResidueField
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (h : IsField (p.Fiber S)) : p.Fiber S ≃+* q.ResidueField := by
  let : Field (p.Fiber S) := h.toField
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  let : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) := inferInstance
  exact RingEquiv.ofBijective (fiberToResidueField p q).toRingHom
    ⟨(fiberToResidueField p q).injective, Ideal.Fiber.lift_residueField_surjective p q⟩

/-- The identification of the fibre with the residue field is the identity on the residue field
of the base prime. -/
private lemma fiberEquivResidueField_algebraMap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (h : IsField (p.Fiber S)) (z : p.ResidueField) :
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver p q
    letI : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) := inferInstance
    fiberEquivResidueField p q h (algebraMap p.ResidueField (p.Fiber S) z) =
      algebraMap p.ResidueField q.ResidueField z := by
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  let : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) := inferInstance
  exact (fiberToResidueField p q).commutes z

/-- Naturality of the identification of the residue field of a point of an affine scheme with
the residue field of the corresponding prime. -/
private lemma spec_residueFieldMap_natural
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (q : Spec (.of S)) :
    letI : ((Spec.map (CommRingCat.ofHom φ)) q).asIdeal.IsPrime :=
      ((Spec.map (CommRingCat.ofHom φ)) q).isPrime
    letI : q.asIdeal.IsPrime := q.isPrime
    (Scheme.Spec.residueFieldIso (.of R) (Spec.map (CommRingCat.ofHom φ) q)).hom ≫
      CommRingCat.ofHom (Ideal.ResidueField.map _ q.asIdeal φ rfl) =
      (Spec.map (CommRingCat.ofHom φ)).residueFieldMap q ≫
        (Scheme.Spec.residueFieldIso (.of S) q).hom := by
  let p : Spec (.of R) := Spec.map (CommRingCat.ofHom φ) q
  have : p.asIdeal.IsPrime := p.isPrime
  have : q.asIdeal.IsPrime := q.isPrime
  have : IsLocalRing ((Spec (.of R)).presheaf.stalk p) :=
    (Spec.locallyRingedSpaceObj (.of R)).isLocalRing p
  have : IsLocalRing ((Spec (.of S)).presheaf.stalk q) :=
    (Spec.locallyRingedSpaceObj (.of S)).isLocalRing q
  let a := Spec.stalkIso (.of R) p
  let b := Spec.stalkIso (.of S) q
  have : IsLocalHom a.hom.hom := isLocalHom_of_iso a
  have : IsLocalHom b.hom.hom := isLocalHom_of_iso b
  let ell := CommRingCat.ofHom (Localization.localRingHom p.asIdeal q.asIdeal φ rfl)
  have : IsLocalHom ell.hom :=
    Localization.isLocalHom_localRingHom p.asIdeal q.asIdeal φ rfl
  have heA : (Scheme.Spec.residueFieldIso (.of R) p).hom =
      CommRingCat.ofHom (IsLocalRing.ResidueField.map a.hom.hom) :=
    rfl
  have heB : (Scheme.Spec.residueFieldIso (.of S) q).hom =
      CommRingCat.ofHom (IsLocalRing.ResidueField.map b.hom.hom) :=
    rfl
  have hmEq : CommRingCat.ofHom (Ideal.ResidueField.map p.asIdeal q.asIdeal φ rfl) =
      CommRingCat.ofHom (IsLocalRing.ResidueField.map ell.hom) :=
    rfl
  have hstalk' : a.hom ≫ ell =
      (Spec.map (CommRingCat.ofHom φ)).stalkMap q ≫ b.hom := by
    rw [← Iso.comp_inv_eq, Category.assoc]
    exact Scheme.localRingHom_comp_stalkIso (CommRingCat.ofHom φ) q
  have : IsLocalHom ((Spec.map (CommRingCat.ofHom φ)).stalkMap q).hom :=
    (Spec.map (CommRingCat.ofHom φ)).prop q
  have hring : ell.hom.comp a.hom.hom =
      b.hom.hom.comp ((Spec.map (CommRingCat.ofHom φ)).stalkMap q).hom :=
    congrArg (fun k => CommRingCat.Hom.hom k) hstalk'
  have hmapEq : IsLocalRing.ResidueField.map (ell.hom.comp a.hom.hom) =
      IsLocalRing.ResidueField.map
        (b.hom.hom.comp ((Spec.map (CommRingCat.ofHom φ)).stalkMap q).hom) := by
    dsimp [p] at hring ⊢
    refine RingHom.ext fun z => ?_
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp [IsLocalRing.ResidueField.map, hring]
  change (Scheme.Spec.residueFieldIso (.of R) p).hom ≫
      CommRingCat.ofHom (Ideal.ResidueField.map p.asIdeal q.asIdeal φ rfl) =
    (Spec.map (CommRingCat.ofHom φ)).residueFieldMap q ≫
      (Scheme.Spec.residueFieldIso (.of S) q).hom
  rw [heA, heB, hmEq]
  ext z
  exact (IsLocalRing.ResidueField.map_map a.hom.hom ell.hom z).trans
    ((congrArg (fun g : _ →+* _ => g z) hmapEq).trans
      (IsLocalRing.ResidueField.map_map _ b.hom.hom z).symm)

/-- Composing the residue field maps of the two directions of an isomorphism of schemes gives
the transport along the corresponding equality of points. -/
private lemma residueFieldMap_iso_cancel
    {A B : Scheme.{u}} (e : A ≅ B) (a : A) (b : B) (h : e.inv b = a) :
    let hb : b = e.hom a := by simpa using congrArg e.hom h
    e.hom.residueFieldMap a ≫ (A.residueFieldCongr h).inv ≫ e.inv.residueFieldMap b =
      (B.residueFieldCongr hb).inv := by
  have hb : b = e.hom a := by simpa using congrArg e.hom h
  subst b
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_inv]
  have heq : h = Scheme.hom_inv_apply e a := Subsingleton.elim _ _
  rw [heq]
  have hcomp : e.inv.residueFieldMap (e.hom a) ≫ e.hom.residueFieldMap a =
      (A.residueFieldCongr (Scheme.hom_inv_apply e a)).hom := by
    have hh := Scheme.Hom.residueFieldMap_congr e.hom_inv_id a
    rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_id] at hh
    simpa using hh
  apply (cancel_mono (e.hom.residueFieldMap a)).mp
  simp only [Category.assoc, hcomp, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- Transporting a ring isomorphism out of a residue field along an equality of points is
composition with the residue field congruence. -/
private lemma residueFieldRingEquiv_cast
    {X : Scheme.{u}} {x y : X} (h : x = y)
    {K : Type u} [CommRing K] (e : X.residueField y ≃+* K) :
    CommRingCat.ofHom (h.symm ▸ e).toRingHom =
      (X.residueFieldCongr h).hom ≫ CommRingCat.ofHom e.toRingHom := by
  cases h
  rfl

/-- Cancelling the residue field congruence of the identification of a point of an affine scheme
with its prime. -/
private lemma spec_residueFieldIso_congr_map
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (q : Spec (.of S)) (a : Spec (.of R))
    (h : (Spec.map (CommRingCat.ofHom φ)) q = a)
    (hOver : a.asIdeal = q.asIdeal.comap φ) :
    letI : a.asIdeal.IsPrime := a.isPrime
    letI : q.asIdeal.IsPrime := q.isPrime
    letI : ((Spec.map (CommRingCat.ofHom φ)) q).asIdeal.IsPrime :=
      ((Spec.map (CommRingCat.ofHom φ)) q).isPrime
    (Scheme.Spec.residueFieldIso (.of R) a).inv ≫
      ((Spec (.of R)).residueFieldCongr h).inv ≫
      (Scheme.Spec.residueFieldIso (.of R) ((Spec.map (CommRingCat.ofHom φ)) q)).hom ≫
      CommRingCat.ofHom (Ideal.ResidueField.map _ q.asIdeal φ rfl) =
      CommRingCat.ofHom (Ideal.ResidueField.map a.asIdeal q.asIdeal φ hOver) := by
  cases h
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_inv,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Geometric irreducibility of the components of a morphism transports along an isomorphism of
the source compatible with the structure morphisms. -/
private lemma geometricallyIrreducible_components_of_iso
    {A B S : Scheme.{u}} (e : A ≅ B) (f : A ⟶ S) (g : B ⟶ S)
    (hfg : e.hom ≫ g = f)
    (h : ∀ Z : irreducibleComponents B,
      GeometricallyIrreducible
        ((Scheme.IdealSheafData.vanishingIdeal
          ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩).subschemeι ≫ g)) :
    ∀ Z : irreducibleComponents A,
      GeometricallyIrreducible
        ((Scheme.IdealSheafData.vanishingIdeal
          ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩).subschemeι ≫ f) := by
  intro Z
  let ZB : irreducibleComponents B := ⟨e.hom '' Z.1,
    image_mem_irreducibleComponents_of_isPreirreducible_fiber e.hom
      e.hom.continuous e.hom.homeomorph.isOpenMap
      (fun _ => (Set.subsingleton_singleton.preimage e.hom.homeomorph.injective).isPreirreducible)
      e.hom.homeomorph.surjective Z.2⟩
  let I := Scheme.IdealSheafData.vanishingIdeal
    ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩
  let J := Scheme.IdealSheafData.vanishingIdeal
    ⟨ZB.1, isClosed_of_mem_irreducibleComponents ZB.1 ZB.2⟩
  have hIJ : I.map e.hom = J := by
    dsimp only [I]
    rw [Scheme.IdealSheafData.map_vanishingIdeal]
    exact congrArg Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.ext (by simpa [ZB] using
        (isClosed_of_mem_irreducibleComponents ZB.1 ZB.2).closure_eq))
  have hJI : J.map e.inv = I := by
    rw [← hIJ, ← Scheme.IdealSheafData.map_comp, e.hom_inv_id, Scheme.IdealSheafData.map_id]
  let t := Scheme.IdealSheafData.subschemeMap I J e.hom (le_of_eq hIJ.symm)
  let v := Scheme.IdealSheafData.subschemeMap J I e.inv (le_of_eq hJI.symm)
  have ht : t ≫ J.subschemeι = I.subschemeι ≫ e.hom :=
    Scheme.IdealSheafData.subschemeMap_subschemeι I J e.hom _
  have hv : v ≫ I.subschemeι = J.subschemeι ≫ e.inv :=
    Scheme.IdealSheafData.subschemeMap_subschemeι J I e.inv _
  have htv : t ≫ v = 𝟙 _ := by
    apply (cancel_mono I.subschemeι).mp
    rw [Category.assoc, hv, ← Category.assoc, ht]
    simp
  have hvt : v ≫ t = 𝟙 _ := by
    apply (cancel_mono J.subschemeι).mp
    rw [Category.assoc, ht, ← Category.assoc, hv]
    simp
  let eSub : I.subscheme ≅ J.subscheme := ⟨t, v, htv, hvt⟩
  have : IsIso t := eSub.isIso_hom
  change GeometricallyIrreducible (I.subschemeι ≫ f)
  have htfg : t ≫ (J.subschemeι ≫ g) = I.subschemeι ≫ f := by
    rw [← Category.assoc, ht, Category.assoc, hfg]
  rw [← htfg]
  have : MorphismProperty.RespectsIso @GeometricallyIrreducible :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIrreducible
    t (J.subschemeι ≫ g)).mpr (h ZB)

/-- Geometric irreducibility of the components of a morphism transports along an isomorphism of
arrows. -/
private lemma geometricallyIrreducible_components_of_arrow_iso
    {A B S T : Scheme.{u}} (f : A ⟶ S) (g : B ⟶ T) (e : Arrow.mk f ≅ Arrow.mk g)
    (h : ∀ Z : irreducibleComponents B,
      GeometricallyIrreducible
        ((Scheme.IdealSheafData.vanishingIdeal
          ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩).subschemeι ≫ g)) :
    ∀ Z : irreducibleComponents A,
      GeometricallyIrreducible
        ((Scheme.IdealSheafData.vanishingIdeal
          ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩).subschemeι ≫ f) := by
  have : MorphismProperty.RespectsIso @GeometricallyIrreducible :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  apply geometricallyIrreducible_components_of_iso (Comma.leftIso e) f
    (g ≫ (Comma.rightIso e).inv)
  · exact (Arrow.iso_w' e.symm).symm
  · intro Z
    exact (MorphismProperty.cancel_right_of_respectsIso
      @GeometricallyIrreducible _ (Comma.rightIso e).inv).mpr (h Z)

/-- The arrows presenting the fibres over two equal points of the base are isomorphic. -/
private noncomputable def fiberArrowIsoOfEq
    {A S : Scheme.{u}} (f : A ⟶ S) {x y : S} (h : x = y) :
    Arrow.mk (f.fiberToSpecResidueField x) ≅ Arrow.mk (f.fiberToSpecResidueField y) := by
  cases h
  exact Iso.refl _

/-- Compatibility of `fiberArrowIsoOfEq` with the residue field map of a morphism into the
base. -/
private lemma spec_residueFieldMap_congr
    {A S T : Scheme.{u}} (f : A ⟶ S) (β : T ⟶ S) (t : T) {y : S} (h : β t = y) :
    Spec.map (β.residueFieldMap t) ≫ (fiberArrowIsoOfEq f h).hom.right =
      Spec.map ((S.residueFieldCongr h).inv ≫ β.residueFieldMap t) := by
  cases h
  simp [fiberArrowIsoOfEq]

/-- **Stacks Project, Tag 0551.** After passing to a nonempty open of an irreducible base, a
finite type morphism has a finite etale surjective base change from an irreducible affine
scheme whose generic fibre has geometrically irreducible irreducible components. -/
@[stacks 0551]
theorem exists_nonemptyOpen_finiteEtale_cover_geometricallyIrreducible_genericFiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (V : Y.Opens) (_ : V.1.Nonempty)
      (Y' : Scheme.{u}) (g : Y' ⟶ V.toScheme)
      (_ : Surjective g) (_ : IsFinite g) (_ : Etale g)
      (_ : IrreducibleSpace Y') (_ : IsAffine Y'),
      let X_V := pullback V.ι f
      let fV : X_V ⟶ V.toScheme := pullback.fst V.ι f
      let X' := pullback (g ≫ V.ι) f
      let f' : X' ⟶ Y' := pullback.fst (g ≫ V.ι) f
      let g' : X' ⟶ X_V := pullback.lift
        (pullback.fst (g ≫ V.ι) f ≫ g)
        (pullback.snd (g ≫ V.ι) f) (by
          rw [Category.assoc]
          exact pullback.condition)
      IsPullback g' f' fV g ∧
        Surjective g' ∧ IsFinite g' ∧ Etale g' ∧
        ∀ (η : Y'), IsGenericPoint η Set.univ →
          ∀ Z : irreducibleComponents (f'.fiber η),
            GeometricallyIrreducible
              ((Scheme.IdealSheafData.vanishingIdeal (X := f'.fiber η)
                  ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩).subschemeι ≫
                f'.fiberToSpecResidueField η) := by
  obtain ⟨V₀, hV₀, hAffine₀⟩ := exists_nonempty_affineOpen Y
  let : Nonempty V₀.toScheme := ⟨⟨hV₀.some, hV₀.some_mem⟩⟩
  let : IrreducibleSpace V₀.toScheme := V₀.ι.isOpenEmbedding.irreducibleSpace
  let f₀ : pullback V₀.ι f ⟶ V₀.toScheme := pullback.fst V₀.ι f
  have hf₀ : LocallyOfFiniteType f₀ := by dsimp [f₀]; infer_instance
  have hqc₀ : QuasiCompact f₀ := by dsimp [f₀]; infer_instance
  let η₀ := genericPoint V₀.toScheme
  have hfη₀ : LocallyOfFiniteType (f₀.fiberToSpecResidueField η₀) :=
    let := hf₀
    Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField f₀ η₀
  let := hfη₀
  obtain ⟨k', hk', hAlg, hFin, hSep, hGeom⟩ :=
    exists_finite_separable_extension_geometricallyIrreducible_components
      (V₀.toScheme.residueField η₀) (f₀.fiber η₀) (f₀.fiberToSpecResidueField η₀)
      (let := hf₀
       let := hqc₀
       finite_irreducibleComponents_fiber f₀ η₀)
  let : Field k' := hk'
  let : Algebra (V₀.toScheme.residueField η₀) k' := hAlg
  let : FiniteDimensional (V₀.toScheme.residueField η₀) k' := hFin
  let : Algebra.IsSeparable (V₀.toScheme.residueField η₀) k' := hSep
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (V₀.toScheme.residueField η₀) k'
  let P := minpoly (V₀.toScheme.residueField η₀) α
  have hPmonic : P.Monic :=
    minpoly.monic (Algebra.IsSeparable.isIntegral (V₀.toScheme.residueField η₀) α)
  have hPirred : Irreducible P :=
    minpoly.irreducible (Algebra.IsSeparable.isIntegral (V₀.toScheme.residueField η₀) α)
  have hPsep : P.Separable :=
    Algebra.IsSeparable.isSeparable (V₀.toScheme.residueField η₀) α
  let e : AdjoinRoot P ≃ₐ[V₀.toScheme.residueField η₀] k' :=
    (IntermediateField.adjoinRootEquivAdjoin (V₀.toScheme.residueField η₀)
      (Algebra.IsSeparable.isIntegral (V₀.toScheme.residueField η₀) α)).trans
      ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)
  let p : Ideal Γ(Y, V₀) := (hAffine₀.primeIdealOf η₀).asIdeal
  let eK : p.ResidueField ≃+* V₀.toScheme.residueField η₀ :=
    affineOpen_residueFieldEquiv V₀ hAffine₀ η₀
  let Pp : p.ResidueField[X] := P.map eK.symm.toRingHom
  have hPp : Pp.Monic := hPmonic.map eK.symm.toRingHom
  have hPpsep : Pp.Separable := hPsep.map
  have hPpirred : Irreducible Pp := by
    change Irreducible ((Polynomial.mapEquiv eK.symm) P)
    exact hPirred.map (Polynomial.mapEquiv eK.symm)
  obtain ⟨c, hc, Q, hQmonic, hQmap⟩ := exists_monic_lift_scaled p Pp hPp
  have hQgenericIrred : Irreducible (Q.map (algebraMap Γ(Y, V₀) p.ResidueField)) := by
    rw [hQmap]
    exact irreducible_scaleRoots_of_isUnit hPpirred hPp hc
  have hQgenericSep : (Q.map (algebraMap Γ(Y, V₀) p.ResidueField)).Separable := by
    rw [hQmap]
    exact separable_scaleRoots_of_isUnit hPpirred hPp hPpsep hc
  let B := AdjoinRoot Q
  have hPpmap : Pp.map eK.toRingHom = P := by
    dsimp [Pp]
    rw [Polynomial.map_map]
    simp
  let eFiber : p.Fiber B ≃+* k' :=
    ((fiber_adjoinRootAlgEquiv Q).toRingEquiv.trans
      (AdjoinRoot.algEquivOfEq p.ResidueField
        (Q.map (algebraMap Γ(Y, V₀) p.ResidueField))
        (Pp.scaleRoots c) hQmap).toRingEquiv).trans
      ((adjoinRoot_scaleRootsEquiv Pp c hc.ne_zero).toRingEquiv.trans
        ((AdjoinRoot.mapRingEquiv eK Pp P (hPpmap ▸ Associated.refl P)).trans e.toRingEquiv))
  have heFiber : ∀ z : p.ResidueField,
      eFiber (algebraMap p.ResidueField (p.Fiber B) z) =
        algebraMap (V₀.toScheme.residueField η₀) k' (eK z) := by
    intro z
    let eT : p.Fiber B ≃ₐ[p.ResidueField]
        AdjoinRoot (Q.map (algebraMap Γ(Y, V₀) p.ResidueField)) :=
      fiber_adjoinRootAlgEquiv Q
    let eEq := AdjoinRoot.algEquivOfEq p.ResidueField
      (Q.map (algebraMap Γ(Y, V₀) p.ResidueField)) (Pp.scaleRoots c) hQmap
    let eSc := adjoinRoot_scaleRootsEquiv Pp c hc.ne_zero
    let eMap := AdjoinRoot.mapRingEquiv eK Pp P (hPpmap ▸ Associated.refl P)
    change e (eMap (eSc (eEq (eT (algebraMap p.ResidueField (p.Fiber B) z))))) = _
    rw [eT.commutes z, eEq.commutes z, eSc.commutes z]
    change e (eMap ((AdjoinRoot.of Pp) z)) = _
    rw [AdjoinRoot.coe_mapRingEquiv, AdjoinRoot.map_of]
    exact e.commutes (eK z)
  have hBfree : Module.Free Γ(Y, V₀) B := hQmonic.free_adjoinRoot
  have hBfinite : Module.Finite Γ(Y, V₀) B := hQmonic.finite_adjoinRoot
  let : Module.Free Γ(Y, V₀) B := hBfree
  let : Module.Finite Γ(Y, V₀) B := hBfinite
  have hBfp : Algebra.FinitePresentation Γ(Y, V₀) B := inferInstance
  let : Algebra.FinitePresentation Γ(Y, V₀) B := hBfp
  have hBfiberField : IsField (p.ResidueField ⊗[Γ(Y, V₀)] B) :=
    isField_fiber_adjoinRoot Q hQgenericIrred
  let : IsDomain (p.Fiber B) := hBfiberField.isDomain
  let : Unique (p.primesOver B) := unique_primesOver_of_isField_fiber p hBfiberField
  let qf : Ideal (p.Fiber B) := ⊥
  let : qf.IsPrime := inferInstance
  let q : Ideal B := qf.comap
    (Algebra.TensorProduct.includeRight : B →ₐ[Γ(Y, V₀)] p.Fiber B)
  let : q.IsPrime := inferInstance
  let : q.LiesOver p := inferInstance
  let : IrreducibleSpace (PrimeSpectrum Γ(Y, V₀)) :=
    irreducibleSpace_affineOpen_sections V₀ hAffine₀
  have hpDense : Dense ({hAffine₀.primeIdealOf η₀} : Set (PrimeSpectrum Γ(Y, V₀))) :=
    dense_primeIdealOf_genericPoint V₀ hAffine₀
  have hBspecIrred : IrreducibleSpace (PrimeSpectrum B) := by
    apply irreducibleSpace_primeSpectrum_of_flat_finitePresentation
      Γ(Y, V₀) B {hAffine₀.primeIdealOf η₀} hpDense
    intro r hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    let : Field (p.Fiber B) := hBfiberField.toField
    exact (PrimeSpectrum.preimageHomeomorphFiber Γ(Y, V₀) B
      (hAffine₀.primeIdealOf η₀)).irreducibleSpace_iff.mpr inferInstance
  have hderiv : AdjoinRoot.mk Q Q.derivative ∉ q := by
    intro hd
    let z : p.Fiber B := Algebra.TensorProduct.includeRight (AdjoinRoot.root Q)
    have hx : aeval z Q = 0 := by
      rw [Polynomial.aeval_algHom_apply
        (Algebra.TensorProduct.includeRight : B →ₐ[Γ(Y, V₀)] p.Fiber B) (AdjoinRoot.root Q) Q]
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
    have hx' : aeval z (Q.map (algebraMap Γ(Y, V₀) p.ResidueField)) = 0 := by
      rw [← Polynomial.aeval_eq_aeval_map
        (R := Γ(Y, V₀)) (T := p.ResidueField) (S := p.Fiber B) (by ext r; rfl) Q z]
      exact hx
    have hxd := hQgenericSep.aeval_derivative_ne_zero hx'
    rw [Polynomial.derivative_map,
      ← Polynomial.aeval_eq_aeval_map
        (R := Γ(Y, V₀)) (T := p.ResidueField) (S := p.Fiber B) (by ext r; rfl) Q.derivative z,
      Polynomial.aeval_algHom_apply
        (Algebra.TensorProduct.includeRight : B →ₐ[Γ(Y, V₀)] p.Fiber B)
        (AdjoinRoot.root Q) Q.derivative,
      AdjoinRoot.aeval_eq] at hxd
    exact hxd (show (Algebra.TensorProduct.includeRight :
      B →ₐ[Γ(Y, V₀)] p.Fiber B) (AdjoinRoot.mk Q Q.derivative) = 0 from hd)
  have hqEtale : Algebra.IsEtaleAt Γ(Y, V₀) q :=
    Stacks.GeometricComponents.isEtaleAt_of_derivative_notMem hQmonic q hderiv
  obtain ⟨r, hr, hBetaleR⟩ := exists_base_basicOpen_etale p q hqEtale
  let V : Y.Opens := Y.basicOpen r
  have hVaff : IsAffineOpen V := hAffine₀.basicOpen r
  have hVne : V.1.Nonempty := by
    have hx : hAffine₀.primeIdealOf η₀ ∈ PrimeSpectrum.basicOpen r :=
      (PrimeSpectrum.mem_basicOpen _ _).mpr hr
    change (Y.basicOpen r).1.Nonempty
    rw [← hAffine₀.fromSpec_image_basicOpen]
    exact ⟨_, ⟨_, hx, rfl⟩⟩
  let g₀ : Spec (.of B) ⟶ V₀.toScheme :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V₀) B)) ≫ hAffine₀.isoSpec.inv
  let U : V₀.toScheme.Opens := V₀.toScheme.basicOpen (V₀.topIso.inv r)
  have hUV : V₀.ι ''ᵁ U = V := by
    simpa [U, V] using V₀.ι_image_basicOpen_topIso_inv r
  let α' : U.toScheme ≅ V.toScheme := V₀.ι.isoImage U ≪≫ Y.isoOfEq hUV
  let Y' : Scheme.{u} := (g₀ ⁻¹ᵁ U).toScheme
  let g : Y' ⟶ V.toScheme := (g₀ ∣_ U) ≫ α'.hom
  have hmFinite : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V₀) B))) :=
    (IsFinite.SpecMap_iff _).mpr ((RingHom.finite_algebraMap).mpr hBfinite)
  have hg₀Finite : IsFinite g₀ := by
    dsimp [g₀]
    let := hmFinite
    infer_instance
  have hrestFinite : IsFinite (g₀ ∣_ U) := by
    let := hg₀Finite
    infer_instance
  have hgFinite : IsFinite g := by
    dsimp [g]
    let := hrestFinite
    infer_instance
  have hQdeg : 0 < Q.degree := by
    rw [← hQmonic.degree_map (algebraMap Γ(Y, V₀) p.ResidueField)]
    exact hQgenericIrred.degree_pos
  let : FaithfulSMul Γ(Y, V₀) B :=
    AdjoinRoot.faithfulSMul_of_monic_of_degree_pos hQmonic hQdeg
  have hmSurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V₀) B))) :=
    ⟨Algebra.IsIntegral.comap_surjective Γ(Y, V₀) B⟩
  have hg₀Surj : Surjective g₀ := by
    dsimp [g₀]
    let := hmSurj
    infer_instance
  have hrestSurj : Surjective (g₀ ∣_ U) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict g₀ U).flip hg₀Surj
  have hgSurj : Surjective g := by
    dsimp [g]
    let := hrestSurj
    infer_instance
  have hYaff : IsAffine Y' := by
    let : IsAffine V.toScheme := hVaff
    let := hgFinite
    exact isAffine_of_isAffineHom g
  have hYnonempty : Nonempty Y' := by
    obtain ⟨v, hv⟩ := hVne
    obtain ⟨y', _⟩ := hgSurj.surj ⟨v, hv⟩
    exact ⟨y'⟩
  have hYirred : IrreducibleSpace Y' := by
    let : IrreducibleSpace (Spec (.of B)) := hBspecIrred
    let : Nonempty Y' := hYnonempty
    exact (g₀ ⁻¹ᵁ U).ι.isOpenEmbedding.irreducibleSpace
  let : IrreducibleSpace (Spec (.of B)) := hBspecIrred
  have hqGeneric : (⟨q, inferInstance⟩ : Spec (.of B)) = genericPoint (Spec (.of B)) := by
    let s : Spec (.of B) ⟶ Spec Γ(Y, V₀) :=
      Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V₀) B))
    have hpGeneric : IsGenericPoint (hAffine₀.primeIdealOf η₀) Set.univ :=
      isGenericPoint_def.mpr (dense_iff_closure_eq.mp hpDense)
    have hsGeneric : IsGenericPoint (s (genericPoint (Spec (.of B)))) Set.univ :=
      isGenericPoint_univ_map (genericPoint_spec _) s.continuous hmSurj.surj
    have hsEq : s (genericPoint (Spec (.of B))) = hAffine₀.primeIdealOf η₀ :=
      hsGeneric.eq hpGeneric
    have hmη : (genericPoint (Spec (.of B))).asIdeal ∈ p.primesOver B := by
      refine ⟨(genericPoint (Spec (.of B))).isPrime, ⟨?_⟩⟩
      exact (congrArg PrimeSpectrum.asIdeal hsEq).symm
    have hqm : q ∈ p.primesOver B := ⟨inferInstance, inferInstance⟩
    apply PrimeSpectrum.ext
    exact congrArg Subtype.val (Subsingleton.elim
      (⟨q, hqm⟩ : p.primesOver B) ⟨(genericPoint (Spec (.of B))).asIdeal, hmη⟩)
  have hVirred : IrreducibleSpace V.toScheme := by
    let : Nonempty V.toScheme := ⟨⟨hVne.some, hVne.some_mem⟩⟩
    exact V.ι.isOpenEmbedding.irreducibleSpace
  have hSpecEtale : Etale
      ((Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V₀) B))) ∣_
        PrimeSpectrum.basicOpen r) := by
    have hAway : (Localization.awayMap (algebraMap Γ(Y, V₀) B) r).Etale :=
      etale_awayMap_of_etale_awayTarget r hBetaleR
    have hSpecAway : Etale (Spec.map (CommRingCat.ofHom
        (Localization.awayMap (algebraMap Γ(Y, V₀) B) r))) :=
      HasRingHomProperty.Spec_iff.mpr hAway
    let : MorphismProperty.RespectsIso @Etale :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.arrow_mk_iso_iff @Etale
      (SpecMapRestrictBasicOpenIso
        (CommRingCat.ofHom (algebraMap Γ(Y, V₀) B)) r)).mpr hSpecAway
  have hpreU : hAffine₀.isoSpec.inv ⁻¹ᵁ U = PrimeSpectrum.basicOpen r := by
    change hAffine₀.isoSpec.inv ⁻¹ᵁ
      V₀.toScheme.basicOpen (V₀.topIso.inv r) = PrimeSpectrum.basicOpen r
    rw [Scheme.preimage_basicOpen_top]
    rw [← basicOpen_eq_of_affine]
    congr 1
    rw [hAffine₀.isoSpec_inv_appTop]
    have hh := congrArg
      (fun φ : Γ(Y, V₀) ⟶ Γ(Y, V₀) => ((φ ≫ (Scheme.ΓSpecIso Γ(Y, V₀)).inv).hom) r)
      (Iso.inv_hom_id V₀.topIso)
    simpa only [Category.id_comp, CommRingCat.hom_comp, RingHom.comp_apply] using hh
  have hRestEtale : Etale (g₀ ∣_ U) := by
    have hs : Etale
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V₀) B)) ∣_
          hAffine₀.isoSpec.inv ⁻¹ᵁ U) :=
      (let : MorphismProperty.RespectsIso @Etale :=
          MorphismProperty.IsStableUnderBaseChange.respectsIso
       MorphismProperty.arrow_mk_iso_iff @Etale
        (morphismRestrictEq
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V₀) B))) hpreU)).mpr hSpecEtale
    dsimp [g₀]
    rw [morphismRestrict_comp]
    let := hs
    infer_instance
  have hgEtale : Etale g := by
    dsimp [g]
    let := hRestEtale
    infer_instance
  let : Surjective g := hgSurj
  let : IsFinite g := hgFinite
  let : Etale g := hgEtale
  let : IrreducibleSpace Y' := hYirred
  let : IsAffine Y' := hYaff
  refine ⟨V, hVne, Y', g, hgSurj, hgFinite, hgEtale, hYirred, hYaff, ?_⟩
  dsimp
  have hpb := baseChange_isPullback V.ι f g
  obtain ⟨hsurj', hfinite', hetale'⟩ := baseChange_surjective_finite_etale V.ι f g
  exact ⟨hpb, hsurj', hfinite', hetale', by
    intro η hη Z
    have hgη : IsGenericPoint (g η) Set.univ :=
      isGenericPoint_univ_map hη g.continuous hgSurj.surj
    have hηeq : η = genericPoint Y' := hη.eq (genericPoint_spec Y')
    have hgηeq : g η = genericPoint V.toScheme := hgη.eq (genericPoint_spec V.toScheme)
    have hηq : (g₀ ⁻¹ᵁ U).ι η = (⟨q, inferInstance⟩ : Spec (.of B)) := by
      rw [hηeq]
      let : IrreducibleSpace (Spec (.of B)) := hBspecIrred
      rw [genericPoint_eq_of_isOpenImmersion, ← hqGeneric]
    let eOpen : Y'.residueField η ≃+* (Spec (.of B)).residueField ((g₀ ⁻¹ᵁ U).ι η) :=
      (asIso ((g₀ ⁻¹ᵁ U).ι.residueFieldMap η)).commRingCatIsoToRingEquiv.symm
    let eSpec : (Spec (.of B)).residueField ((g₀ ⁻¹ᵁ U).ι η) ≃+* q.ResidueField :=
      hηq.symm ▸ (Scheme.Spec.residueFieldIso (.of B)
        (⟨q, inferInstance⟩ : Spec (.of B))).commRingCatIsoToRingEquiv
    let eResidue : Y'.residueField η ≃+* k' :=
      eOpen.trans (eSpec.trans ((fiberEquivResidueField p q hBfiberField).symm.trans eFiber))
    let β : Y' ⟶ V₀.toScheme := (g₀ ⁻¹ᵁ U).ι ≫ g₀
    have hβ : β ≫ V₀.ι = g ≫ V.ι := by
      dsimp only [β, g, α']
      simp only [Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι,
        Scheme.Hom.isoImage_hom_ι]
      rw [← morphismRestrict_ι_assoc]
    let ξ : pullback (g ≫ V.ι) f ⟶ pullback V₀.ι f :=
      pullback.lift (pullback.fst (g ≫ V.ι) f ≫ β) (pullback.snd (g ≫ V.ι) f) (by
        simpa only [Category.assoc, hβ] using
          (pullback.condition :
            pullback.fst (g ≫ V.ι) f ≫ (g ≫ V.ι) = pullback.snd (g ≫ V.ι) f ≫ f))
    have hξ : IsPullback ξ (pullback.fst (g ≫ V.ι) f) (pullback.fst V₀.ι f) β := by
      apply IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
        (IsPullback.of_hasPullback V₀.ι f).flip
      simpa only [ξ, pullback.lift_snd, hβ] using
        (IsPullback.of_hasPullback (g ≫ V.ι) f).flip
    have hg₀η₀ : g₀ (genericPoint (Spec (.of B))) = η₀ := by
      exact (isGenericPoint_univ_map (genericPoint_spec _) g₀.continuous hg₀Surj.surj).eq
        (genericPoint_spec V₀.toScheme)
    have hgq : g₀ (⟨q, inferInstance⟩ : Spec (.of B)) = η₀ := by
      rw [hqGeneric]
      exact hg₀η₀
    have hβη : β η = η₀ := by
      change g₀ ((g₀ ⁻¹ᵁ U).ι η) = η₀
      rw [hηq]
      exact hgq
    have hFiberPB := isPullback_fiberToSpecResidueField_of_isPullback hξ η
    let eFiberPB := hFiberPB.isoPullback
    have heFiberPB : eFiberPB.hom ≫
        pullback.snd (pullback.fst V₀.ι f |>.fiberToSpecResidueField (β η))
          (Spec.map (β.residueFieldMap η)) =
        (pullback.fst (g ≫ V.ι) f).fiberToSpecResidueField η := hFiberPB.isoPullback_hom_snd
    let θ : V₀.toScheme.residueField η₀ ⟶ Y'.residueField η :=
      (V₀.toScheme.residueFieldCongr hβη).inv ≫ β.residueFieldMap η
    let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver p q
    let : IsScalarTower Γ(Y, V₀) (Localization.AtPrime p) (Localization.AtPrime q) :=
      inferInstance
    let s : Spec (.of B) ⟶ Spec Γ(Y, V₀) :=
      Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V₀) B))
    let qSpec : Spec (.of B) := ⟨q, inferInstance⟩
    have hqbase : hAffine₀.isoSpec.inv (s qSpec) = η₀ := hgq
    have hsq : s qSpec = hAffine₀.primeIdealOf η₀ := by
      change s qSpec = hAffine₀.isoSpec.hom η₀
      simpa using congrArg hAffine₀.isoSpec.hom hqbase
    have hnat := spec_residueFieldMap_natural (algebraMap Γ(Y, V₀) B) qSpec
    have hcancel := residueFieldMap_iso_cancel hAffine₀.isoSpec η₀ (s qSpec) hqbase
    have hopen :
        (g₀ ⁻¹ᵁ U).ι.residueFieldMap η ≫ CommRingCat.ofHom eOpen.toRingHom =
        𝟙 ((Spec (.of B)).residueField ((g₀ ⁻¹ᵁ U).ι η)) := by
      change (g₀ ⁻¹ᵁ U).ι.residueFieldMap η ≫
        (asIso ((g₀ ⁻¹ᵁ U).ι.residueFieldMap η)).inv = 𝟙 _
      exact (asIso ((g₀ ⁻¹ᵁ U).ι.residueFieldMap η)).hom_inv_id
    let j : Y' ⟶ Spec (.of B) := (g₀ ⁻¹ᵁ U).ι
    let o : Y'.residueField η ⟶ (Spec (.of B)).residueField (j η) :=
      CommRingCat.ofHom eOpen.toRingHom
    let eSpecHom : (Spec (.of B)).residueField (j η) ⟶ CommRingCat.of q.ResidueField :=
      CommRingCat.ofHom eSpec.toRingHom
    have heSpec : eSpecHom =
        ((Spec (.of B)).residueFieldCongr hηq).hom ≫
          (Scheme.Spec.residueFieldIso (.of B) qSpec).hom :=
      residueFieldRingEquiv_cast hηq
        (Scheme.Spec.residueFieldIso (.of B) qSpec).commRingCatIsoToRingEquiv
    have hsnat : s.residueFieldMap (j η) ≫ eSpecHom =
        ((Spec Γ(Y, V₀)).residueFieldCongr (congrArg s hηq)).hom ≫
          s.residueFieldMap qSpec ≫ (Scheme.Spec.residueFieldIso (.of B) qSpec).hom := by
      rw [heSpec]
      simpa only [Category.assoc] using
        congrArg (fun t => t ≫ (Scheme.Spec.residueFieldIso (.of B) qSpec).hom)
          (Scheme.Hom.residueFieldMap_congr' (f := s) hηq)
    have hAffineNat :
        hAffine₀.isoSpec.inv.residueFieldMap (s (j η)) ≫
          ((Spec Γ(Y, V₀)).residueFieldCongr (congrArg s hηq)).hom =
        (V₀.toScheme.residueFieldCongr
          (congrArg hAffine₀.isoSpec.inv (congrArg s hηq))).hom ≫
          hAffine₀.isoSpec.inv.residueFieldMap (s qSpec) :=
      Scheme.Hom.residueFieldMap_congr' (f := hAffine₀.isoSpec.inv) (congrArg s hηq)
    have hCongCancel :
        (V₀.toScheme.residueFieldCongr hβη).inv ≫
          (V₀.toScheme.residueFieldCongr
            (congrArg hAffine₀.isoSpec.inv (congrArg s hηq))).hom =
        (V₀.toScheme.residueFieldCongr hqbase).inv := by
      have hh : hβη.symm.trans (congrArg hAffine₀.isoSpec.inv (congrArg s hηq)) =
          hqbase.symm := Subsingleton.elim _ _
      calc
        _ = (V₀.toScheme.residueFieldCongr
            (hβη.symm.trans
              (congrArg hAffine₀.isoSpec.inv (congrArg s hηq)))).hom :=
          Scheme.residueFieldCongr_trans_hom V₀.toScheme hβη.symm
            (congrArg hAffine₀.isoSpec.inv (congrArg s hηq))
        _ = _ := by rw [hh, Scheme.residueFieldCongr_inv]
    have heKiso : CommRingCat.ofHom eK.toRingHom =
        (Scheme.Spec.residueFieldIso (.of Γ(Y, V₀)) (hAffine₀.primeIdealOf η₀)).inv ≫
          hAffine₀.isoSpec.hom.residueFieldMap η₀ := by rfl
    have hBridge :
        CommRingCat.ofHom eK.toRingHom ≫ θ ≫ o ≫ eSpecHom =
        CommRingCat.ofHom (Ideal.ResidueField.map p q
          (algebraMap Γ(Y, V₀) B) (q.over_def p)) := by
      calc
        _ = CommRingCat.ofHom eK.toRingHom ≫
            (V₀.toScheme.residueFieldCongr hβη).inv ≫
            g₀.residueFieldMap (j η) ≫
            (j.residueFieldMap η ≫ o) ≫ eSpecHom := by
          simp only [θ, β, j, o, Scheme.residueFieldMap_comp]
          cat_disch
        _ = CommRingCat.ofHom eK.toRingHom ≫
            (V₀.toScheme.residueFieldCongr hβη).inv ≫
            g₀.residueFieldMap (j η) ≫ eSpecHom := by
          rw [show j.residueFieldMap η ≫ o = 𝟙 _ from hopen]
          cat_disch
        _ = _ := by
          change CommRingCat.ofHom eK.toRingHom ≫
            (V₀.toScheme.residueFieldCongr hβη).inv ≫
            (s ≫ hAffine₀.isoSpec.inv).residueFieldMap (j η) ≫ eSpecHom = _
          rw [Scheme.residueFieldMap_comp]
          calc
            _ = (CommRingCat.ofHom eK.toRingHom ≫
                (V₀.toScheme.residueFieldCongr hβη).inv ≫
                hAffine₀.isoSpec.inv.residueFieldMap (s (j η))) ≫
                (s.residueFieldMap (j η) ≫ eSpecHom) := by cat_disch
            _ = _ := by
              rw [hsnat]
              calc
                _ = CommRingCat.ofHom eK.toRingHom ≫
                    (V₀.toScheme.residueFieldCongr hβη).inv ≫
                    (V₀.toScheme.residueFieldCongr
                      (congrArg hAffine₀.isoSpec.inv (congrArg s hηq))).hom ≫
                    hAffine₀.isoSpec.inv.residueFieldMap (s qSpec) ≫
                    s.residueFieldMap qSpec ≫
                    (Scheme.Spec.residueFieldIso (.of B) qSpec).hom := by
                  convert congrArg
                    (fun t => CommRingCat.ofHom eK.toRingHom ≫
                      (V₀.toScheme.residueFieldCongr hβη).inv ≫ t ≫
                      s.residueFieldMap qSpec ≫
                      (Scheme.Spec.residueFieldIso (.of B) qSpec).hom)
                    hAffineNat using 1
                _ = CommRingCat.ofHom eK.toRingHom ≫
                    (V₀.toScheme.residueFieldCongr hqbase).inv ≫
                    hAffine₀.isoSpec.inv.residueFieldMap (s qSpec) ≫
                    s.residueFieldMap qSpec ≫
                    (Scheme.Spec.residueFieldIso (.of B) qSpec).hom := by
                  convert congrArg
                    (fun t => CommRingCat.ofHom eK.toRingHom ≫ t ≫
                      hAffine₀.isoSpec.inv.residueFieldMap (s qSpec) ≫
                      s.residueFieldMap qSpec ≫
                      (Scheme.Spec.residueFieldIso (.of B) qSpec).hom)
                    hCongCancel using 1
                _ = _ := by
                  have hcl :
                      hAffine₀.isoSpec.hom.residueFieldMap η₀ ≫
                          (V₀.toScheme.residueFieldCongr hqbase).inv ≫
                          hAffine₀.isoSpec.inv.residueFieldMap (s qSpec) =
                        ((Spec Γ(Y, V₀)).residueFieldCongr hsq).inv := hcancel
                  rw [heKiso]
                  calc
                    _ = (Scheme.Spec.residueFieldIso (.of Γ(Y, V₀))
                          (hAffine₀.primeIdealOf η₀)).inv ≫
                        (hAffine₀.isoSpec.hom.residueFieldMap η₀ ≫
                          (V₀.toScheme.residueFieldCongr hqbase).inv ≫
                          hAffine₀.isoSpec.inv.residueFieldMap (s qSpec)) ≫
                        s.residueFieldMap qSpec ≫
                        (Scheme.Spec.residueFieldIso (.of B) qSpec).hom := by
                          cat_disch
                    _ = (Scheme.Spec.residueFieldIso (.of Γ(Y, V₀))
                          (hAffine₀.primeIdealOf η₀)).inv ≫
                        ((Spec Γ(Y, V₀)).residueFieldCongr hsq).inv ≫
                        s.residueFieldMap qSpec ≫
                        (Scheme.Spec.residueFieldIso (.of B) qSpec).hom :=
                          congrArg
                            (fun t => (Scheme.Spec.residueFieldIso (.of Γ(Y, V₀))
                              (hAffine₀.primeIdealOf η₀)).inv ≫ t ≫
                              s.residueFieldMap qSpec ≫
                              (Scheme.Spec.residueFieldIso (.of B) qSpec).hom) hcl
                    _ = _ := by
                      rw [← hnat]
                      exact spec_residueFieldIso_congr_map
                        (algebraMap Γ(Y, V₀) B) qSpec
                        (hAffine₀.primeIdealOf η₀) hsq (q.over_def p)
    have hθ : eResidue.toRingHom.comp θ.hom =
        algebraMap (V₀.toScheme.residueField (genericPoint V₀.toScheme)) k' := by
      apply RingHom.ext
      intro z
      obtain ⟨w, rfl⟩ := eK.surjective z
      simp only [RingHom.comp_apply]
      rw [← heFiber w]
      have hbase : eSpec (eOpen (θ (eK w))) =
          algebraMap p.ResidueField q.ResidueField w := by
        have hh := congrArg
          (fun t : CommRingCat.of p.ResidueField ⟶ CommRingCat.of q.ResidueField => t w)
          hBridge
        change eSpec (eOpen (θ (eK w))) =
          (Ideal.ResidueField.map p q (algebraMap Γ(Y, V₀) B) (q.over_def p)) w at hh
        exact hh
      change eFiber ((fiberEquivResidueField p q hBfiberField).symm
        (eSpec (eOpen (θ (eK w))))) = _
      rw [hbase]
      congr 1
      exact (Equiv.symm_apply_eq _).mpr
        (fiberEquivResidueField_algebraMap p q hBfiberField w).symm
    let ePoint := fiberArrowIsoOfEq f₀ hβη
    let ePullPoint : pullback (f₀.fiberToSpecResidueField (β η))
        (Spec.map (β.residueFieldMap η)) ≅
        pullback (f₀.fiberToSpecResidueField η₀) (Spec.map θ) :=
      asIso (pullback.map _ _ _ _ ePoint.hom.left (𝟙 _) ePoint.hom.right
        ePoint.hom.w.symm (by
          simpa only [Category.id_comp] using spec_residueFieldMap_congr f₀ β η hβη))
    let eBase : Spec (Y'.residueField η) ≅ Spec (.of k') :=
      Scheme.Spec.mapIso eResidue.symm.toCommRingCatIso.op
    have hθ' : eResidue.symm.toRingHom.comp
        (algebraMap (V₀.toScheme.residueField η₀) k') = θ.hom := by
      ext z
      apply eResidue.injective
      change eResidue (eResidue.symm
        ((algebraMap (V₀.toScheme.residueField η₀) k') z)) = eResidue (θ z)
      rw [eResidue.apply_symm_apply]
      exact (RingHom.congr_fun hθ z).symm
    have hSpecθ : Spec.map θ = eBase.hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (V₀.toScheme.residueField η₀) k')) := by
      change Spec.map θ =
        Spec.map (CommRingCat.ofHom eResidue.symm.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (V₀.toScheme.residueField η₀) k'))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun t => Spec.map (CommRingCat.ofHom t)) hθ'.symm
    let ePullField : pullback (f₀.fiberToSpecResidueField η₀) (Spec.map θ) ≅
        pullback (f₀.fiberToSpecResidueField η₀)
          (Spec.map (CommRingCat.ofHom
            (algebraMap (V₀.toScheme.residueField η₀) k'))) :=
      asIso (pullback.map _ _ _ _ (𝟙 _) eBase.hom (𝟙 _)
        (by simp) (by
          change Spec.map θ ≫ 𝟙 _ = eBase.hom ≫
            Spec.map (CommRingCat.ofHom (algebraMap (V₀.toScheme.residueField η₀) k'))
          simpa only [Category.comp_id] using hSpecθ))
    let eTotal := eFiberPB ≪≫ ePullPoint ≪≫ ePullField
    have hFieldSnd : ePullField.hom ≫ pullback.snd
        (f₀.fiberToSpecResidueField η₀)
        (Spec.map (CommRingCat.ofHom
          (algebraMap (V₀.toScheme.residueField η₀) k'))) =
        pullback.snd (f₀.fiberToSpecResidueField η₀) (Spec.map θ) ≫ eBase.hom := by
      simp only [ePullField, asIso_hom, pullback.map, pullback.lift_snd]
    have hPointSnd : ePullPoint.hom ≫
        pullback.snd (f₀.fiberToSpecResidueField η₀) (Spec.map θ) =
        pullback.snd (f₀.fiberToSpecResidueField (β η))
          (Spec.map (β.residueFieldMap η)) := by
      simp only [ePullPoint, asIso_hom, pullback.map, pullback.lift_snd, Category.comp_id]
    have hTotal : eTotal.hom ≫ pullback.snd
        (f₀.fiberToSpecResidueField η₀)
        (Spec.map (CommRingCat.ofHom
          (algebraMap (V₀.toScheme.residueField η₀) k'))) =
        (pullback.fst (g ≫ V.ι) f).fiberToSpecResidueField η ≫ eBase.hom := by
      calc
        _ = (eFiberPB.hom ≫ ePullPoint.hom) ≫ (ePullField.hom ≫ pullback.snd _ _) := by
              change (eFiberPB.hom ≫ (ePullPoint.hom ≫ ePullField.hom)) ≫
                pullback.snd _ _ = _
              cat_disch
        _ = (eFiberPB.hom ≫ ePullPoint.hom) ≫ (pullback.snd _ _ ≫ eBase.hom) := by
              rw [hFieldSnd]
        _ = (eFiberPB.hom ≫ (ePullPoint.hom ≫ pullback.snd _ _)) ≫ eBase.hom := by cat_disch
        _ = (eFiberPB.hom ≫ pullback.snd _ _) ≫ eBase.hom :=
              congrArg (fun t => (eFiberPB.hom ≫ t) ≫ eBase.hom) hPointSnd
        _ = _ := congrArg (fun t => t ≫ eBase.hom) heFiberPB
    let eArrow : Arrow.mk ((pullback.fst (g ≫ V.ι) f).fiberToSpecResidueField η) ≅
        Arrow.mk (pullback.snd (f₀.fiberToSpecResidueField η₀)
          (Spec.map (CommRingCat.ofHom
            (algebraMap (V₀.toScheme.residueField η₀) k')))) :=
      Arrow.isoMk' _ _ eTotal eBase hTotal
    exact (geometricallyIrreducible_components_of_arrow_iso _ _ eArrow hGeom) Z⟩

end AlgebraicGeometry
