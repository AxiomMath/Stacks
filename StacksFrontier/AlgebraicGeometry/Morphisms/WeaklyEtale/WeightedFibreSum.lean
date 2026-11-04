module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.FieldTheory.SeparableClosure
public import StacksCore.Tactic.StacksAttribute

/-!
# Weighted sums over the fibres of a locally quasi-finite morphism

For a locally quasi-finite morphism with finite fibres, an integer-valued function on the source
can be summed over each fibre, with each value weighted by the separable degree of the
corresponding residue-field extension. This weighted fibre sum commutes with cartesian base
change.

## Main definitions

* `AlgebraicGeometry.separableDegreeWeightedFiberSum` is the fibrewise sum weighted by separable
  residue degrees.

## Main results

* `AlgebraicGeometry.separableDegreeWeightedFiberSum_comp_of_isPullback` says that the weighted
  fibre sum commutes with cartesian base change.

## Implementation notes

The weighted sum is expressed as a `finsum` over all points of the source, with terms outside
the relevant fibre set to zero. Under the finite-fibre hypothesis of the theorem this is the
finite sum in the source. The algebra structure on each residue field is the one induced by the
scheme morphism.

The proof of base-change invariance counts, for an algebraically closed field `K` over the
residue field of the target point, the `K`-points of the fibre: the separable degree of a
residue-field extension is exactly the number of liftings of the chosen embedding, so both sides
become the same sum over `K`-points.

## References

* [Stacks Project, Tag 0F39](https://stacks.math.columbia.edu/tag/0F39)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The residue field extension at a point of a locally quasi-finite morphism is finite. -/
private lemma residueFieldMap_finite
    {U V : Scheme.{u}} (f : U ⟶ V) [LocallyQuasiFinite f] (x : U) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (V.residueField (f x)) (U.residueField x) := by
  let : Algebra (V.presheaf.stalk (f x)) (U.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have hstalk : RingHom.QuasiFinite (f.stalkMap x).hom := f.quasiFiniteAt x
  have hres : RingHom.QuasiFinite (U.residue x).hom :=
    RingHom.QuasiFinite.of_finite <| RingHom.Finite.of_surjective _ (U.residue_surjective x)
  have hcomp : RingHom.QuasiFinite
      ((f.residueFieldMap x).hom.comp (V.residue (f x)).hom) := by
    have heq := congrArg CommRingCat.Hom.hom (Scheme.residue_residueFieldMap f x)
    change (f.residueFieldMap x).hom.comp (V.residue (f x)).hom =
      (U.residue x).hom.comp (f.stalkMap x).hom at heq
    rw [heq]
    exact hres.comp hstalk
  let : Algebra (V.residueField (f x)) (U.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have : Algebra.QuasiFinite (V.residueField (f x)) (U.residueField x) :=
    RingHom.quasiFinite_algebraMap.mp <| (RingHom.QuasiFinite.comp_iff
      (.of_finite <| .of_surjective _ (V.residue_surjective (f x)))).mp hcomp
  exact Module.Finite.of_quasiFinite

/-- Ring homomorphisms `E →+* K` compatible with the structure maps from `F` are the
`F`-algebra homomorphisms `E →ₐ[F] K`. -/
private noncomputable def algebraExtensionsEquivAlgHom
    {F E K : Type u} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K] :
    {φ : E →+* K // φ.comp (algebraMap F E) = algebraMap F K} ≃ (E →ₐ[F] K) where
  toFun φ := AlgHom.mk' φ.1 fun c x ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    simpa only [RingHom.comp_apply] using congrArg (· * φ.1 x) (DFunLike.congr_fun φ.2 c)
  invFun φ := ⟨φ.toRingHom, φ.comp_algebraMap⟩
  left_inv _ := Subtype.ext (RingHom.ext fun _ ↦ rfl)
  right_inv _ := AlgHom.ext fun _ ↦ rfl

/-- The separable degree of an algebraic field extension `E/F` is the number of embeddings of
`E` into an algebraically closed field `K` over `F`. -/
private lemma finSepDegree_eq_natCard_extensions
    {F E K : Type u} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K] [Algebra.IsAlgebraic F E] [IsAlgClosed K] :
    Field.finSepDegree F E =
      Nat.card {φ : E →+* K // φ.comp (algebraMap F E) = algebraMap F K} := by
  rw [Field.finSepDegree_eq_of_isAlgClosed F E K]
  exact Nat.card_congr (algebraExtensionsEquivAlgHom (F := F) (E := E) (K := K)).symm

/-- Morphisms of residue fields in `CommRingCat` over a fixed one are the corresponding ring
homomorphisms. -/
private noncomputable def residueField_extension_lifts_equiv
    {U V : Scheme.{u}} (f : U ⟶ V) (x : U) {K : Type u} [Field K]
    (ψ : V.residueField (f x) ⟶ .of K) :
    {φ : U.residueField x ⟶ .of K // f.residueFieldMap x ≫ φ = ψ} ≃
      {φ : U.residueField x →+* K //
        φ.comp (f.residueFieldMap x).hom = ψ.hom} where
  toFun φ := ⟨φ.1.hom, congrArg CommRingCat.Hom.hom φ.2⟩
  invFun φ := ⟨CommRingCat.ofHom φ.1, CommRingCat.hom_ext φ.2⟩
  left_inv _ := Subtype.ext (CommRingCat.hom_ext rfl)
  right_inv _ := Subtype.ext rfl

/-- The number of embeddings of the residue field at `x` into an algebraically closed field `K`
extending a given embedding of the residue field at `f x` is the separable degree of the residue
field extension. -/
lemma residueField_extension_lifts_card
    {U V : Scheme.{u}} (f : U ⟶ V) [LocallyQuasiFinite f]
    (x : U) {K : Type u} [Field K] [IsAlgClosed K]
    (ψ : V.residueField (f x) ⟶ .of K) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Field.finSepDegree (V.residueField (f x)) (U.residueField x) =
      Nat.card {φ : U.residueField x ⟶ .of K // f.residueFieldMap x ≫ φ = ψ} := by
  let F := V.residueField (f x)
  let E := U.residueField x
  let α : F →+* E := (f.residueFieldMap x).hom
  let β : F →+* K := ψ.hom
  let : Algebra F E := α.toAlgebra
  let : Algebra F K := β.toAlgebra
  have : Module.Finite F E := residueFieldMap_finite f x
  exact (finSepDegree_eq_natCard_extensions (F := F) (E := E) (K := K)).trans
    (Nat.card_congr (residueField_extension_lifts_equiv f x ψ).symm)

/-- There are finitely many embeddings of the residue field at `x` into an algebraically closed
field extending a given embedding of the residue field at `f x`. -/
lemma finite_residueField_extension_lifts
    {U V : Scheme.{u}} (f : U ⟶ V) [LocallyQuasiFinite f]
    (x : U) {K : Type u} [Field K] [IsAlgClosed K]
    (ψ : V.residueField (f x) ⟶ .of K) :
    Finite {φ : U.residueField x ⟶ .of K // f.residueFieldMap x ≫ φ = ψ} := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have : Module.Finite (V.residueField (f x)) (U.residueField x) := residueFieldMap_finite f x
  refine Nat.finite_of_card_ne_zero ?_
  rw [← residueField_extension_lifts_card f x ψ]
  exact NeZero.ne _

/-- The universal property of a pullback square, as an equivalence of sets of arrows over a
fixed map to the base change. -/
private noncomputable def pullbackArrowEquiv {A U U' V V' : Scheme.{u}}
    (f : U ⟶ V) (h : U' ⟶ U) (f' : U' ⟶ V') (g : V' ⟶ V)
    (sq : IsPullback h f' f g) (z : A ⟶ V') :
    {p : A ⟶ U' // p ≫ f' = z} ≃
      {p : A ⟶ U // p ≫ f = z ≫ g} where
  toFun p := ⟨p.1 ≫ h, by rw [Category.assoc, sq.w, ← Category.assoc, p.2]⟩
  invFun p := ⟨sq.lift p.1 z p.2, sq.lift_snd _ _ _⟩
  left_inv p :=
    Subtype.ext <| sq.hom_ext (sq.lift_fst _ _ _) ((sq.lift_snd _ _ _).trans p.2.symm)
  right_inv p := Subtype.ext (sq.lift_fst _ _ _)

/-- The `K`-points of `U` over a fixed `K`-point of `V`, in terms of the `Scheme.residueField`
description of `K`-points. -/
noncomputable def specPointFiberEquiv
    {U V : Scheme.{u}} {K : Type u} [Field K]
    (f : U ⟶ V) (a : Spec (.of K) ⟶ V) :
    {q : Spec (.of K) ⟶ U // q ≫ f = a} ≃
      {d : Σ x : U, U.residueField x ⟶ .of K //
        f d.1 = a (IsLocalRing.closedPoint K) ∧
          Spec.map d.2 ≫ U.fromSpecResidueField d.1 ≫ f = a} :=
  Equiv.subtypeEquiv (Scheme.SpecToEquivOfField K U) fun q ↦ by
    have he := congrArg (fun q : Spec (.of K) ⟶ U ↦ q ≫ f)
      ((Scheme.SpecToEquivOfField K U).left_inv q)
    exact ⟨fun h ↦ ⟨congrArg (fun q : Spec (.of K) ⟶ V ↦ q (IsLocalRing.closedPoint K)) h,
      he.trans h⟩, fun h ↦ he.symm.trans h.2⟩

/-- The `K`-points of `U` over a fixed `K`-point of `V`, grouped by their image point. -/
noncomputable def specPointFiberSigmaEquiv
    {U V : Scheme.{u}} {K : Type u} [Field K]
    (f : U ⟶ V) (a : Spec (.of K) ⟶ V) :
    {q : Spec (.of K) ⟶ U // q ≫ f = a} ≃
      Σ x : {x : U // f x = a (IsLocalRing.closedPoint K)},
        {φ : U.residueField x.1 ⟶ .of K //
          Spec.map φ ≫ U.fromSpecResidueField x.1 ≫ f = a} :=
  (specPointFiberEquiv f a).trans
    (Equiv.subtypeSigmaEquivSigma
      (α := U) (β := fun x => U.residueField x ⟶ .of K)
      (p := fun x => f x = a (IsLocalRing.closedPoint K))
      (q := fun x φ => Spec.map φ ≫ U.fromSpecResidueField x ≫ f = a))

/-- The residue field description of the `K`-point of `V` obtained by composing a `K`-point of
`U` with `f`. -/
lemma specPointFiber_comp_apply
    {U V : Scheme.{u}} {K : Type u} [Field K] (f : U ⟶ V)
    (x : U) (φ : U.residueField x ⟶ .of K) :
    Scheme.SpecToEquivOfField K V (Spec.map φ ≫ U.fromSpecResidueField x ≫ f) =
      ⟨f x, f.residueFieldMap x ≫ φ⟩ := by
  apply_fun (Scheme.SpecToEquivOfField K V).symm
  simp only [Equiv.symm_apply_apply]
  rw [Scheme.SpecToEquivOfField_symm_apply]
  simp only [Spec.map_comp, Category.assoc,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]

/-- The `K`-points of `U` over the `K`-point of `V` determined by an embedding `ψ` of the residue
field at `v`: they are the points of the fibre of `f` over `v` together with an embedding of
their residue field extending `ψ`. -/
noncomputable def specPointFiberFieldSigmaEquiv
    {U V : Scheme.{u}} {K : Type u} [Field K]
    (f : U ⟶ V) (v : V) (ψ : V.residueField v ⟶ .of K) :
    {q : Spec (.of K) ⟶ U // q ≫ f = Spec.map ψ ≫ V.fromSpecResidueField v} ≃
      Σ x : {x : U // f x = v},
        {φ : U.residueField x.1 ⟶ .of K // f.residueFieldMap x.1 ≫ φ =
          (V.residueFieldCongr x.2).hom ≫ ψ} := by
  let a : Spec (.of K) ⟶ V := Spec.map ψ ≫ V.fromSpecResidueField v
  have haCoord : Scheme.SpecToEquivOfField K V a = ⟨v, ψ⟩ := by
    apply_fun (Scheme.SpecToEquivOfField K V).symm
    simp only [Equiv.symm_apply_apply]
    rw [Scheme.SpecToEquivOfField_symm_apply]
  have hpoint : a (IsLocalRing.closedPoint K) = v := by
    rw [← Scheme.SpecToEquivOfField_apply_fst, haCoord]
  refine (specPointFiberSigmaEquiv f a).trans
    (Equiv.sigmaCongr (Equiv.subtypeEquivRight fun x ↦ by rw [hpoint]) fun x ↦
      Equiv.subtypeEquiv (Equiv.refl _) fun φ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩)
  · have h' := congrArg (Scheme.SpecToEquivOfField K V) h
    rw [haCoord, specPointFiber_comp_apply, Scheme.SpecToEquivOfField_eq_iff] at h'
    exact h'.2
  · have hfx : f x.1 = v := x.2.trans hpoint
    have h' : f.residueFieldMap x.1 ≫ φ = (V.residueFieldCongr hfx).hom ≫ ψ := h
    calc
      Spec.map φ ≫ U.fromSpecResidueField x.1 ≫ f =
          Spec.map (f.residueFieldMap x.1 ≫ φ) ≫ V.fromSpecResidueField (f x.1) := by
        simp only [Spec.map_comp, Category.assoc,
          Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
      _ = Spec.map ((V.residueFieldCongr hfx).hom ≫ ψ) ≫
          V.fromSpecResidueField (f x.1) := by rw [h']
      _ = Spec.map ψ ≫ V.fromSpecResidueField v := by
        rw [Spec.map_comp, Category.assoc,
          Scheme.residueFieldCongr_fromSpecResidueField hfx]

/-- The base change of a locally quasi-finite morphism is locally quasi-finite. -/
private lemma locallyQuasiFinite_of_isPullback
    {U U' V V' : Scheme.{u}} {f : U ⟶ V} {h : U' ⟶ U} {f' : U' ⟶ V'} {g : V' ⟶ V}
    (sq : IsPullback h f' f g) [LocallyQuasiFinite f] : LocallyQuasiFinite f' := by
  rw [← sq.isoPullback_hom_snd]
  infer_instance

/-- Having finite fibres is stable under base change for a locally quasi-finite morphism: the
fibre of the base change is an affine scheme which is artinian over the residue field. -/
lemma finite_preimage_singleton_of_isPullback
    {U U' V V' : Scheme.{u}} (f : U ⟶ V) (h : U' ⟶ U)
    (f' : U' ⟶ V') (g : V' ⟶ V) (sq : IsPullback h f' f g)
    [LocallyQuasiFinite f] (hfinite : ∀ v, (f ⁻¹' {v}).Finite) (v' : V') :
    (f' ⁻¹' {v'}).Finite := by
  classical
  let y := g v'
  have := locallyQuasiFinite_of_isPullback sq
  have : Finite (f.fiber y) := (f.fiberHomeo y).finite_iff.mpr
    (Set.finite_coe_iff.mpr (hfinite y))
  have : LocallyQuasiFinite (f.fiberToSpecResidueField y) := by
    change LocallyQuasiFinite (Limits.pullback.snd f (V.fromSpecResidueField y))
    infer_instance
  have : IsFinite (f.fiberToSpecResidueField y) :=
    IsFinite.of_locallyQuasiFinite (f.fiberToSpecResidueField y)
  have hpull := isPullback_fiberToSpecResidueField_of_isPullback sq v'
  have h₁ : IsFinite
      (Limits.pullback.snd (f.fiberToSpecResidueField y)
        (Spec.map (g.residueFieldMap v'))) := by infer_instance
  have h₂ : IsFinite hpull.isoPullback.hom := by infer_instance
  have : IsFinite (f'.fiberToSpecResidueField v') := by
    rw [← hpull.isoPullback_hom_snd]
    exact MorphismProperty.IsStableUnderComposition.comp_mem (P := @IsFinite) _ _ h₂ h₁
  have : CompactSpace (f'.fiber v') :=
    QuasiCompact.compactSpace_of_compactSpace (f'.fiberToSpecResidueField v')
  have : IsArtinianScheme (f'.fiber v') :=
    { toIsLocallyArtinian := inferInstance, toCompactSpace := inferInstance }
  exact Set.finite_coe_iff.mp ((f'.fiberHomeo v').finite_iff.mp inferInstance)

/-- A `finsum` over the source of a map with the terms outside one finite fibre set to zero is
the finite sum over that fibre. -/
private lemma finsum_if_fiber_eq_sum {U V : Scheme.{u}} [DecidableEq V] (f : U ⟶ V)
    (v : V) (hfinite : (f ⁻¹' {v}).Finite) (a : U → ℤ) :
    (∑ᶠ x : U, if f x = v then a x else 0) = ∑ x ∈ hfinite.toFinset, a x := by
  classical
  rw [finsum_eq_sum_of_support_subset (s := hfinite.toFinset)]
  · exact Finset.sum_congr rfl fun x hx ↦ by simp_all
  · intro x hx
    by_contra h
    simp_all

/-- The sum over a fibre of a scheme morphism, weighting the value at each
point by the separable degree of its residue field over that of its image. -/
@[sga "1 I 10.7" "more general", sga "1 IX 5.4"]
noncomputable def separableDegreeWeightedFiberSum {U V : Scheme.{u}} (f : U ⟶ V)
    (w : U → ℤ) : V → ℤ := by
  classical
  exact fun v ↦ ∑ᶠ u : U, if f u = v then
    letI := (f.residueFieldMap u).hom.toAlgebra
    w u * (Field.finSepDegree (V.residueField (f u)) (U.residueField u) : ℤ)
  else 0

/-- For a morphism with finite fibres the weighted fibre sum is the finite sum over the
fibre. -/
private lemma separableDegreeWeightedFiberSum_apply_eq_sum
    {U V : Scheme.{u}} (f : U ⟶ V) (w : U → ℤ)
    (hfinite : ∀ v, (f ⁻¹' {v}).Finite) (v : V) :
    separableDegreeWeightedFiberSum f w v =
      ∑ x ∈ (hfinite v).toFinset,
        (letI := (f.residueFieldMap x).hom.toAlgebra
         w x * (Field.finSepDegree (V.residueField (f x)) (U.residueField x) : ℤ)) := by
  classical
  unfold separableDegreeWeightedFiberSum
  exact finsum_if_fiber_eq_sum f v (hfinite v) _

/-- A locally quasi-finite morphism with finite fibres has finitely many `K`-points above a
given `K`-point of the base, for `K` algebraically closed. -/
private lemma finite_specPointFiber_field
    {U V : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (f : U ⟶ V) [LocallyQuasiFinite f] (v : V)
    (ψ : V.residueField v ⟶ .of K) (hfiber : (f ⁻¹' {v}).Finite) :
    Finite {q : Spec (.of K) ⟶ U //
      q ≫ f = Spec.map ψ ≫ V.fromSpecResidueField v} := by
  classical
  let X := {x : U // f x = v}
  let L : X → Type u := fun x =>
    {φ : U.residueField x.1 ⟶ .of K //
      f.residueFieldMap x.1 ≫ φ = (V.residueFieldCongr x.2).hom ≫ ψ}
  have : Finite X := Set.finite_coe_iff.mpr hfiber
  have : ∀ x : X, Finite (L x) := fun x =>
    finite_residueField_extension_lifts f x.1 ((V.residueFieldCongr x.2).hom ≫ ψ)
  exact .of_equiv _ (specPointFiberFieldSigmaEquiv f v ψ).symm

/-- The sum of an integer-valued function over a finite type. -/
private noncomputable def finiteTypeSum {α : Type*} [Finite α] (w : α → ℤ) : ℤ := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  exact ∑ x, w x

/-- The second description of the weighted fibre sum from the source: it is the plain sum of `w`
over the `K`-points of `U` above a chosen `K`-point of `V`, for `K` algebraically closed. -/
private lemma weightedFiberSum_eq_geometricPointSum
    {U V : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (f : U ⟶ V) [LocallyQuasiFinite f] (v : V)
    (ψ : V.residueField v ⟶ .of K) (hfiber : (f ⁻¹' {v}).Finite)
    (w : U → ℤ)
    [Finite {q : Spec (.of K) ⟶ U //
      q ≫ f = Spec.map ψ ≫ V.fromSpecResidueField v}] :
    (∑ x ∈ hfiber.toFinset,
      (letI := (f.residueFieldMap x).hom.toAlgebra
       w x * (Field.finSepDegree (V.residueField (f x)) (U.residueField x) : ℤ))) =
      finiteTypeSum (fun q : {q : Spec (.of K) ⟶ U //
        q ≫ f = Spec.map ψ ≫ V.fromSpecResidueField v} =>
        w (q.1 (IsLocalRing.closedPoint K))) := by
  classical
  let X := {x : U // f x = v}
  let L : X → Type u := fun x =>
    {φ : U.residueField x.1 ⟶ .of K //
      f.residueFieldMap x.1 ≫ φ = (V.residueFieldCongr x.2).hom ≫ ψ}
  let Q := {q : Spec (.of K) ⟶ U //
    q ≫ f = Spec.map ψ ≫ V.fromSpecResidueField v}
  have : Finite X := Set.finite_coe_iff.mpr hfiber
  have : ∀ x : X, Finite (L x) := fun x =>
    finite_residueField_extension_lifts f x.1 ((V.residueFieldCongr x.2).hom ≫ ψ)
  let : ∀ x : X, Fintype (L x) := fun x => Fintype.ofFinite (L x)
  let : Fintype Q := Fintype.ofFinite Q
  let : Fintype X := Fintype.ofFinite X
  change _ = ∑ q : Q, w (q.1 (IsLocalRing.closedPoint K))
  have hcard (x : X) :
      (letI := (f.residueFieldMap x.1).hom.toAlgebra
       Field.finSepDegree (V.residueField (f x.1)) (U.residueField x.1)) =
        Fintype.card (L x) := by
    let := (f.residueFieldMap x.1).hom.toAlgebra
    simpa [L, Nat.card_eq_fintype_card] using
      (residueField_extension_lifts_card f x.1 ((V.residueFieldCongr x.2).hom ≫ ψ))
  calc
    _ = ∑ x : X, w x.1 * (Fintype.card (L x) : ℤ) := by
      let eX : {x : U // x ∈ hfiber.toFinset} ≃ X :=
        Equiv.subtypeEquiv (Equiv.refl _) fun x ↦ by
          simp only [hfiber.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff,
            Equiv.refl_apply]
      rw [← Finset.sum_attach, Finset.attach_eq_univ]
      exact Fintype.sum_equiv eX
        (fun x => letI := (f.residueFieldMap x.1).hom.toAlgebra
          w x.1 * (Field.finSepDegree (V.residueField (f x.1)) (U.residueField x.1) : ℤ))
        (fun x => w x.1 * (Fintype.card (L x) : ℤ)) fun x ↦ by
        let := (f.residueFieldMap x.1).hom.toAlgebra
        have hx : (eX x).1 = x.1 := rfl
        rw [← hx, hcard (eX x)]
    _ = ∑ d : Σ x : X, L x, w d.1.1 := by
      rw [Fintype.sum_sigma]
      exact Fintype.sum_congr _ _ fun x ↦ by simp [mul_comm]
    _ = ∑ q : Q, w (q.1 (IsLocalRing.closedPoint K)) :=
      (Fintype.sum_equiv (specPointFiberFieldSigmaEquiv f v ψ)
        (fun q => w (q.1 (IsLocalRing.closedPoint K))) (fun d => w d.1.1) fun _ ↦ rfl).symm

/-- Weighted fibre sums by separable residue degrees commute with cartesian
base change. -/
@[stacks 0F39]
theorem separableDegreeWeightedFiberSum_comp_of_isPullback
    {U U' V V' : Scheme.{u}} (f : U ⟶ V) (h : U' ⟶ U)
    (f' : U' ⟶ V') (g : V' ⟶ V) (sq : IsPullback h f' f g)
    [LocallyQuasiFinite f] (hfinite : ∀ v, (f ⁻¹' {v}).Finite) (w : U → ℤ) :
    separableDegreeWeightedFiberSum f w ∘ g =
      separableDegreeWeightedFiberSum f' (w ∘ h) := by
  classical
  have := locallyQuasiFinite_of_isPullback sq
  have hfinite' : ∀ v', (f' ⁻¹' {v'}).Finite :=
    finite_preimage_singleton_of_isPullback f h f' g sq hfinite
  funext v'
  rw [Function.comp_apply]
  let K := AlgebraicClosure (V'.residueField v')
  let : Field K := inferInstance
  have : IsAlgClosed K := inferInstance
  let ψ : V'.residueField v' ⟶ .of K :=
    CommRingCat.ofHom (algebraMap (V'.residueField v') K)
  let y := g v'
  let ψ₀ : V.residueField y ⟶ .of K := g.residueFieldMap v' ≫ ψ
  let z : Spec (.of K) ⟶ V' := Spec.map ψ ≫ V'.fromSpecResidueField v'
  have hz : z ≫ g = Spec.map ψ₀ ≫ V.fromSpecResidueField y := by
    dsimp [z, ψ₀, y]
    simp only [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      Spec.map_comp]
  let Q' := {q : Spec (.of K) ⟶ U' // q ≫ f' = z}
  let Q := {q : Spec (.of K) ⟶ U //
    q ≫ f = Spec.map ψ₀ ≫ V.fromSpecResidueField y}
  have : Finite Q' := finite_specPointFiber_field f' v' ψ (hfinite' v')
  have : Finite Q := finite_specPointFiber_field f y ψ₀ (hfinite y)
  let : Fintype Q' := Fintype.ofFinite Q'
  let : Fintype Q := Fintype.ofFinite Q
  have hgeom :
      (∑ q : Q', (w ∘ h) (q.1 (IsLocalRing.closedPoint K))) =
        ∑ q : Q, w (q.1 (IsLocalRing.closedPoint K)) :=
    Fintype.sum_equiv ((pullbackArrowEquiv f h f' g sq z).trans
        (Equiv.subtypeEquivRight fun q ↦ by simp [hz] : _ ≃ Q))
      (fun q => w (h (q.1 (IsLocalRing.closedPoint K))))
      (fun q => w (q.1 (IsLocalRing.closedPoint K))) fun _ ↦ rfl
  have hleft := weightedFiberSum_eq_geometricPointSum f' v' ψ
    (hfinite' v') (w ∘ h)
  have hright := weightedFiberSum_eq_geometricPointSum f y ψ₀ (hfinite y) w
  change _ = ∑ q : Q', (w ∘ h) (q.1 (IsLocalRing.closedPoint K)) at hleft
  change _ = ∑ q : Q, w (q.1 (IsLocalRing.closedPoint K)) at hright
  rw [separableDegreeWeightedFiberSum_apply_eq_sum f w hfinite y,
    separableDegreeWeightedFiberSum_apply_eq_sum f' (w ∘ h) hfinite' v']
  exact hright.trans (hgeom.symm.trans hleft.symm)

end AlgebraicGeometry
