module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectMorphismFactor
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic
public import Mathlib.RingTheory.Localization.Cardinality
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Reaching points in the closure of an image of algebraic stacks (Stacks 0CL2)

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact 1-morphism of algebraic stacks over `S` and let `y` be a
point of `|𝒴|` lying in the closure of the image of `|f|`. Then `y` is the image of the closed
point of a valuation-ring diagram whose generic point maps into `𝒳`: there is a valuation ring
`A` with fraction field `K`, a 1-morphism `Spec K ⟶ 𝒳`, a 1-morphism `Spec A ⟶ 𝒴` and a
2-morphism filling the square, with the closed point of `Spec A` going to `y`.

## Main definitions

* `AlgebraicGeometry.Stack.closedPointFieldValuedPoint`: the closed point of a represented
  spectrum, read as a field-valued point of the category fibred in groupoids it represents.

## Main results

* `AlgebraicGeometry.Stack.exists_valuationRing_of_mem_closure_range_pointsMap`:
  **Stacks 0CL2**.

## Implementation notes

The solid part of the diagram is packaged by `AlgebraicGeometry.Stack.ValuativeSquare`, so the
statement produces a valuative square whose special point hits `y`; membership of the spectrum
of the residue field of the closed point in the chosen big fppf site is recorded as a separate
existential, since nothing in the square mentions it.

The proof transports a point of a stack to a point of a scheme twice over, and the two passages
are kept apart on purpose.

* On the slice model `schemeFibredCategory B S hS U` of a scheme `U` over `S` the passage is
  `schemePoint`. The bridge `schemePoint_spacePointMap` identifies it, along the
  equivalence `AlgebraicGeometry.Stack.schemeFibredCategoryEquivalence` with the category of
  elements of the presheaf `U` represents, with the point map
  `AlgebraicGeometry.Space.pointsToScheme` of Stacks 03BX, clause (1). That bridge is what
  makes `schemePoint` a bijection, and it is what transfers openness of the chart — available
  only for a chart by an *algebraic space*, through
  `AlgebraicGeometry.Stack.isOpenMap_spacePointMap` — to the slice model.
* A 1-morphism of slice models comes from a morphism of the site, recovered by
  `schemeMapOfFunctor` from the value of the based functor at the terminal object of the source
  slice; the compatibility of that recovery with `schemePoint` is `schemePoint_naturality`, and
  `basedNatTransOfSchemeMapEq` is the converse direction of 2-Yoneda that fills the valuative
  square.

The valuation ring produced in the affine case has to be *small*: its spectrum must lie in the
big fppf site, which is a cardinality condition. `affine_valuation_diagram_sized` therefore
repeats the construction of the affine valuative diagram of Stacks 02JQ while recording
that the valuation ring is a subring of a residue field of the source, hence no larger than the
source.

## References

* [Stacks Project, Tag 0CL2](https://stacks.math.columbia.edu/tag/0CL2)
-/

@[expose] public section

open CategoryTheory IsLocalRing CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

/-- **Stacks 0CL2.** The closed point of a represented spectrum, read as a field-valued point of
the category fibred in groupoids it represents: the field is the residue field of the point, and
the section is the morphism of site objects out of its spectrum.

This is the point whose image under the special arrow of the valuative square produced by
`AlgebraicGeometry.Stack.exists_valuationRing_of_mem_closure_range_pointsMap` is the prescribed
point of the target. -/
noncomputable def closedPointFieldValuedPoint
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (z : U.left.1)
    (hz : B.Contains (Spec (.of (U.left.1.residueField z)))) :
    FieldValuedPoint B S hS (schemeFibredCategory B S hS U).val where
  carrier := U.left.1.residueField z
  field := inferInstance
  base := Space.residueFieldObject B S hS U z hz
  isSpec := Iso.refl _
  obj := Over.mk (Space.residueFieldMap B S hS U z hz)
  «over» := rfl

/-! ### Small valuation rings -/

/-- A ring no larger than one whose spectrum lies in the chosen big fppf site has its own
spectrum in that site. -/
private theorem spec_mem_of_ring_cardinality_bound
    (B : BigFppfSite.{u}) {R A : Type u} [CommRing R] [CommRing A]
    (hR : B.Contains (Spec (.of R)))
    (hA : Cardinal.mk A ≤ max Cardinal.aleph0 (Cardinal.mk R)) :
    B.Contains (Spec (.of A)) :=
  Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit hR hA

/-- A residue field of a ring is no larger than the ring: it is a localization of a
quotient. -/
private theorem residueField_cardinality_bound
    {R : Type u} [CommRing R] (I : Ideal R) [I.IsPrime] :
    Cardinal.mk I.ResidueField ≤ max Cardinal.aleph0 (Cardinal.mk R) :=
  (IsLocalization.cardinalMk_le (nonZeroDivisors (R ⧸ I))).trans
    (Cardinal.mk_quotient_le.trans (le_max_right _ _))

/-- **The affine valuative diagram of Stacks 02JQ, with a cardinality bound.** Given a ring map
`φ : R →+* S` and primes `p` of `R` and `q` of `S` with `φ⁻¹ q ≤ p`, there is a valuation ring
`A` with fraction field `K` making the square over `Spec φ` commute and sending the closed point
of `Spec A` to `p`, and `A` is no larger than `S`.

The library's unsized form of this statement is
`AlgebraicGeometry.exists_valuationRing_of_image_point`, which records no bound on the size of
the valuation ring. The bound is what puts `Spec A` into the chosen big fppf site, so it is
carried here: `A` is a subring of a residue field of `S`. -/
private theorem affine_valuation_diagram_sized
    {R T : Type u} [CommRing R] [CommRing T] (φ : R →+* T)
    (p : PrimeSpectrum R) (q : PrimeSpectrum T)
    (hpq : q.asIdeal.comap φ ≤ p.asIdeal) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (_ : Cardinal.mk A ≤ max Cardinal.aleph0 (Cardinal.mk T))
      (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K)
      (g : Spec (.of K) ⟶ Spec (.of T)) (h : Spec (.of A) ⟶ Spec (.of R)),
      g ≫ Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ h ∧
      h (closedPoint A) = p := by
  let K := q.asIdeal.ResidueField
  let _ : Field K := inferInstance
  let _ : IsLocalRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime p.asIdeal) p.asIdeal
  have hden : p.asIdeal.primeCompl ≤ Submonoid.comap φ q.asIdeal.primeCompl :=
    fun _ hs hq => hs (hpq hq)
  let θ : Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal :=
    IsLocalization.map (Localization.AtPrime q.asIdeal) φ hden
  let ψ : Localization.AtPrime p.asIdeal →+* K :=
    (IsLocalRing.residue (Localization.AtPrime q.asIdeal)).comp θ
  let _ : Nontrivial K := inferInstance
  obtain ⟨V, hV, hVlocal⟩ := IsLocalRing.exists_factor_valuationRing ψ
  let A := V
  let _ : IsLocalRing A := V.isLocalRing
  let _ : Algebra A K := inferInstance
  let _ : IsFractionRing A K := inferInstance
  let ρ : Localization.AtPrime p.asIdeal →+* A := ψ.codRestrict V.toSubring hV
  let _ : IsLocalHom ρ := hVlocal
  let r : R →+* A := ρ.comp (algebraMap R (Localization.AtPrime p.asIdeal))
  let g : Spec (.of K) ⟶ Spec (.of T) :=
    Spec.map (CommRingCat.ofHom (algebraMap T K))
  let h : Spec (.of A) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom r)
  have hcomm : (algebraMap A K).comp r = (algebraMap T K).comp φ := by
    ext x
    show (IsLocalRing.residue (Localization.AtPrime q.asIdeal))
        (θ (algebraMap R (Localization.AtPrime p.asIdeal) x)) = algebraMap T K (φ x)
    calc
      _ = (IsLocalRing.residue (Localization.AtPrime q.asIdeal))
          ((algebraMap T (Localization.AtPrime q.asIdeal)) (φ x)) :=
            congrArg (IsLocalRing.residue (Localization.AtPrime q.asIdeal))
              (DFunLike.congr_fun (IsLocalization.map_comp hden) x)
      _ = algebraMap T K (φ x) :=
        IsScalarTower.algebraMap_apply T (Localization.AtPrime q.asIdeal) K (φ x)
  have hclosed : h (closedPoint A) = p := by
    show PrimeSpectrum.comap r (IsLocalRing.closedPoint A) = p
    rw [PrimeSpectrum.comap_comp]
    show PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal))
      (PrimeSpectrum.comap ρ (IsLocalRing.closedPoint A)) = p
    rw [IsLocalRing.comap_closedPoint ρ]
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap R (Localization.AtPrime p.asIdeal))
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) = p.asIdeal
    exact IsLocalization.AtPrime.under_maximalIdeal
      (Localization.AtPrime p.asIdeal) p.asIdeal
  refine ⟨A, inferInstance, inferInstance, inferInstance,
    (Cardinal.mk_subtype_le (fun x : K => x ∈ V)).trans
      (residueField_cardinality_bound q.asIdeal),
    K, inferInstance, inferInstance, inferInstance, g, h, ?_, hclosed⟩
  show Spec.map (CommRingCat.ofHom (algebraMap T K)) ≫
      Spec.map (CommRingCat.ofHom φ) =
    Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ Spec.map (CommRingCat.ofHom r)
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext hcomm.symm)

/-- **A point of an affine scheme in the closure of the image of a morphism of affine schemes is
reached by a small valuation ring.** The prime is in the zero locus of the kernel, so it
dominates the contraction of some prime of the source. -/
private theorem exists_valuation_diagram_of_mem_closure_affine_range
    {R T : Type u} [CommRing R] [CommRing T] (φ : R →+* T)
    (p : PrimeSpectrum R)
    (hp : p ∈ closure (Set.range (PrimeSpectrum.comap φ))) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (_ : Cardinal.mk A ≤ max Cardinal.aleph0 (Cardinal.mk T))
      (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K)
      (g : Spec (.of K) ⟶ Spec (.of T)) (h : Spec (.of A) ⟶ Spec (.of R)),
      g ≫ Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ h ∧
      h (closedPoint A) = p := by
  rw [PrimeSpectrum.closure_range_comap] at hp
  have hker : RingHom.ker φ ≤ p.asIdeal := by
    change p ∈ PrimeSpectrum.zeroLocus (RingHom.ker φ) at hp
    simpa using hp
  obtain ⟨Q, _, hQ, hQle⟩ :=
    p.asIdeal.exists_ideal_comap_le_prime (⊥ : Ideal T)
      (by simpa [RingHom.ker] using hker)
  exact affine_valuation_diagram_sized φ p ⟨Q, hQ⟩ hQle

/-- A morphism from the spectrum of a field into a scheme whose image lies in the range of an
open immersion from an affine scheme factors through that open immersion. -/
private theorem exists_lift_field_map_through_openImmersion
    {R : Type u} [CommRing R] {K : Type u} [Field K]
    {X : Scheme.{u}} (i : Spec (.of R) ⟶ X) [IsOpenImmersion i]
    (m : Spec (.of K) ⟶ X)
    (hm : m (IsLocalRing.closedPoint K) ∈ Set.range i) :
    ∃ l : Spec (.of K) ⟶ Spec (.of R), l ≫ i = m := by
  have hrange : Set.range m ⊆ Set.range i := by
    rintro z ⟨q, rfl⟩
    rwa [show q = IsLocalRing.closedPoint K from Subsingleton.elim _ _]
  exact ⟨IsOpenImmersion.lift i m hrange,
    IsOpenImmersion.lift_fac i m hrange⟩

/-! ### Points of a represented category fibred in groupoids -/

section Represented

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A transport cancels against its inverse inside a composite.

The statement is about an abstract category on purpose: the goals it is applied to mention the
object part of a `CategoryTheory.BasedCategory.ofFunctor`, which is a semireducible
definition, and are therefore not type-correct at `implicit` transparency — so `rw` and
`simp only` decline to act on them, exactly as the docstring of
`CategoryTheory.CatFiberedInGroupoids.based` describes. Stated here with opaque morphisms, the
step is an ordinary `simp`. -/
private theorem eqToHom_cancel_fac {C : Type*} [Category C] {X Y Z T Q : C}
    (h : X = Y) (h' : Y = X) (g : X ⟶ Z) (e : Z = T) (k : T ⟶ Q) :
    eqToHom h ≫ (eqToHom h' ≫ g ≫ eqToHom e) ≫ k = g ≫ eqToHom e ≫ k := by
  cases h
  simp

/-- Two transport-conjugates of one morphism agree. This is the shape the naturality square of
`basedNatTransOfSchemeMapEq` reduces to; see `eqToHom_cancel_fac` for why it is stated about an
abstract category. -/
private theorem eqToHom_conj_eq {C : Type*} [Category C] {A A' D D' E E' : C}
    (h₁ : A = A') (g : A' ⟶ D) (h₂ : D = D') (h₃ : D' = E)
    (h₄ : A = E') (h₅ : E' = A') (h₆ : D = E) :
    eqToHom h₁ ≫ g ≫ eqToHom h₂ ≫ eqToHom h₃ =
      eqToHom h₄ ≫ eqToHom h₅ ≫ g ≫ eqToHom h₆ := by
  cases h₁
  cases h₂
  cases h₃
  cases h₅
  simp

/-- The morphism of the big fppf category over `S` underlying a 1-morphism of represented
categories fibred in groupoids: the value of the based functor at the terminal object of the
source slice, read through the identification of its base with the source object. -/
def schemeMapOfFunctor {W U : BigFppfOver B S hS}
    (b : (schemeFibredCategory B S hS W).based ⥤ᵇ (schemeFibredCategory B S hS U).based) :
    W ⟶ U :=
  eqToHom (b.w_obj (Over.mk (𝟙 W))).symm ≫ (b.obj (Over.mk (𝟙 W))).hom

/-- The value of a 1-morphism of represented categories fibred in groupoids at an arbitrary
object of the source slice is the structure morphism of that object followed by the underlying
morphism of the site. -/
theorem schemeMapOfFunctor_naturality {W U : BigFppfOver B S hS}
    (b : (schemeFibredCategory B S hS W).based ⥤ᵇ (schemeFibredCategory B S hS U).based)
    (V : Over W) :
    eqToHom (b.w_obj V).symm ≫ (b.obj V).hom =
      V.hom ≫ schemeMapOfFunctor B S hS b := by
  have ht : (Over.forget U).IsHomLift V.hom (b.map (Over.mkIdTerminal.from V)) :=
    Functor.TwoYoneda.isHomLift_map_from_mkIdTerminal _ _ b V
  refine Eq.trans (congrArg (fun k => eqToHom (b.w_obj V).symm ≫ k)
    (Over.w (b.map (Over.mkIdTerminal.from V))).symm) ?_
  refine Eq.trans (congrArg
    (fun k => eqToHom (b.w_obj V).symm ≫ k ≫ (b.obj (Over.mk (𝟙 W))).hom)
    (IsHomLift.fac' (Over.forget U) V.hom (b.map (Over.mkIdTerminal.from V)))) ?_
  exact eqToHom_cancel_fac _ _ _ _ _

/-- The morphism of the site underlying the 1-morphism induced by a morphism of the site is
that morphism. -/
theorem schemeMapOfFunctor_overMapBased {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    schemeMapOfFunctor B S hS (overMapBased B S hS g) = g := by
  show (𝟙 U) ≫ (𝟙 U) ≫ g = g
  simp

/-- The morphism of the site underlying a 1-morphism precomposed with the one induced by a
morphism of the site. -/
theorem schemeMapOfFunctor_comp_overMapBased {Q W U : BigFppfOver B S hS} (g : Q ⟶ W)
    (b : (schemeFibredCategory B S hS W).based ⥤ᵇ (schemeFibredCategory B S hS U).based) :
    schemeMapOfFunctor B S hS (BasedFunctor.comp (overMapBased B S hS g) b) =
      g ≫ schemeMapOfFunctor B S hS b := by
  refine Eq.trans (schemeMapOfFunctor_naturality B S hS b
    ((Over.map g).obj (Over.mk (𝟙 Q)))) ?_
  exact congrArg (fun t => t ≫ schemeMapOfFunctor B S hS b) (Category.id_comp g)

/-- The morphism of the site underlying a composite of two induced 1-morphisms is the composite
of the morphisms of the site. -/
private theorem schemeMapOfFunctor_comp_overMapBased_overMapBased {Q W U : BigFppfOver B S hS}
    (g : Q ⟶ W) (g' : W ⟶ U) :
    schemeMapOfFunctor B S hS (BasedFunctor.comp (overMapBased B S hS g) (overMapBased B S hS g')) =
      g ≫ g' :=
  (schemeMapOfFunctor_comp_overMapBased B S hS g (overMapBased B S hS g')).trans
    (congrArg (fun t => g ≫ t) (schemeMapOfFunctor_overMapBased B S hS g'))

/-- **Two 1-morphisms of represented categories fibred in groupoids with the same underlying
morphism of the site are 2-isomorphic.** The component at an object of the source slice is the
transport between the two values, which is a morphism over the base because both values have
the given morphism of the site as structure morphism, by `schemeMapOfFunctor_naturality`. -/
def basedNatTransOfSchemeMapEq {W U : BigFppfOver B S hS}
    (F G : (schemeFibredCategory B S hS W).based ⥤ᵇ (schemeFibredCategory B S hS U).based)
    (h : schemeMapOfFunctor B S hS F = schemeMapOfFunctor B S hS G) :
    BasedNatTrans F G where
  app t := Over.homMk (eqToHom ((F.w_obj t).trans (G.w_obj t).symm)) (by
    apply (cancel_epi (eqToHom (F.w_obj t).symm)).mp
    refine Eq.trans (eqToHom_trans_assoc (F.w_obj t).symm
      ((F.w_obj t).trans (G.w_obj t).symm) (G.obj t).hom) ?_
    exact (schemeMapOfFunctor_naturality B S hS G t).trans
      ((congrArg (fun k => t.hom ≫ k) h.symm).trans
        (schemeMapOfFunctor_naturality B S hS F t).symm))
  naturality t t' aa := by
    apply Over.OverMorphism.ext
    change (F.map aa).left ≫ eqToHom ((F.w_obj t').trans (G.w_obj t').symm) =
      eqToHom ((F.w_obj t).trans (G.w_obj t).symm) ≫ (G.map aa).left
    have _ : (schemeFibredCategory B S hS W).based.p.IsHomLift aa.left aa :=
      IsHomLift.map (Over.forget W) aa
    have _ : (Over.forget U).IsHomLift aa.left (F.map aa) :=
      BasedFunctor.preserves_isHomLift F aa.left aa
    have _ : (Over.forget U).IsHomLift aa.left (G.map aa) :=
      BasedFunctor.preserves_isHomLift G aa.left aa
    have hF := IsHomLift.fac' (Over.forget U) aa.left (F.map aa)
    have hG := IsHomLift.fac' (Over.forget U) aa.left (G.map aa)
    change (F.map aa).left = _ at hF
    change (G.map aa).left = _ at hG
    rw [hF, hG]
    simp only [Category.assoc]
    exact eqToHom_conj_eq _ _ _ _ _ _ _
  isHomLift' t := IsHomLift.of_fac' _ _ _ (F.w_obj t) (G.w_obj t) (by
    change eqToHom ((F.w_obj t).trans (G.w_obj t).symm) =
      eqToHom (F.w_obj t) ≫ 𝟙 _ ≫ eqToHom (G.w_obj t).symm
    simp)

/-- The point of the scheme underlying `U` determined by a field-valued point of the category
fibred in groupoids represented by `U`: the image of the closed point of the field spectrum
under the structure morphism of the object. -/
noncomputable def schemePointOfField {U : BigFppfOver B S hS}
    (p : FieldValuedPoint B S hS (schemeFibredCategory B S hS U).based) :
    (BigFppfOver.toScheme B S hS).obj U :=
  (BigFppfOver.toScheme B S hS).map (eqToHom p.over.symm ≫ p.obj.hom)
    (p.isSpec.inv (IsLocalRing.closedPoint p.carrier))

/-- A morphism of field-valued points of a represented category fibred in groupoids does not
move the underlying scheme point: the source field spectrum is a one-point space. -/
private theorem schemePointOfField_eq_of_hom {U : BigFppfOver B S hS}
    (p q : FieldValuedPoint B S hS (schemeFibredCategory B S hS U).based)
    (a : p.obj ⟶ q.obj) :
    schemePointOfField B S hS p = schemePointOfField B S hS q := by
  let T := BigFppfOver.toScheme B S hS
  let e : T.obj q.obj.left ≅ Spec (.of q.carrier) :=
    T.mapIso (eqToIso q.over) ≪≫ q.isSpec
  have : Subsingleton (T.obj q.obj.left) :=
    ⟨fun x y => e.schemeIsoToHomeo.injective (Subsingleton.elim _ _)⟩
  unfold schemePointOfField
  show T.map p.obj.hom _ = T.map q.obj.hom _
  rw [← Over.w a, T.map_comp]
  exact congrArg (T.map q.obj.hom) (Subsingleton.elim _ _)

/-- The point of the scheme underlying `U` determined by a point of the category fibred in
groupoids represented by `U`. -/
noncomputable def schemePoint (U : BigFppfOver B S hS) :
    points B S hS (schemeFibredCategory B S hS U).based
        (schemeFibredCategory B S hS U).property →
      (BigFppfOver.toScheme B S hS).obj U :=
  Quotient.lift (schemePointOfField B S hS) (by
    rintro p q ⟨r, ⟨a⟩, ⟨b⟩⟩
    exact (schemePointOfField_eq_of_hom B S hS r p a).symm.trans
      (schemePointOfField_eq_of_hom B S hS r q b))

/-- Applying a 1-morphism of represented categories fibred in groupoids to a point moves the
underlying scheme point along the underlying morphism of schemes. -/
theorem schemePoint_naturality {W U : BigFppfOver B S hS}
    (b : (schemeFibredCategory B S hS W).based ⥤ᵇ (schemeFibredCategory B S hS U).based)
    (p : points B S hS (schemeFibredCategory B S hS W).based
      (schemeFibredCategory B S hS W).property) :
    schemePoint B S hS U
        (pointsMap B S hS (schemeFibredCategory B S hS W).based
          (schemeFibredCategory B S hS W).property
          (schemeFibredCategory B S hS U).property b p) =
      (BigFppfOver.toScheme B S hS).map (schemeMapOfFunctor B S hS b)
        (schemePoint B S hS W p) := by
  induction p using Quotient.inductionOn with
  | h p =>
    let T := BigFppfOver.toScheme B S hS
    show T.map (eqToHom ((b.w_obj p.obj).trans p.over).symm ≫ (b.obj p.obj).hom) _ =
      T.map (schemeMapOfFunctor B S hS b) (T.map (eqToHom p.over.symm ≫ p.obj.hom) _)
    have heq : eqToHom ((b.w_obj p.obj).trans p.over).symm ≫ (b.obj p.obj).hom =
        eqToHom p.over.symm ≫ p.obj.hom ≫ schemeMapOfFunctor B S hS b := by
      refine Eq.trans (eqToHom_trans_assoc p.over.symm (b.w_obj p.obj).symm
        (b.obj p.obj).hom).symm ?_
      exact congrArg (fun k => eqToHom p.over.symm ≫ k)
        (schemeMapOfFunctor_naturality B S hS b p.obj)
    rw [heq]
    simp only [Functor.map_comp]
    rfl

/-- A morphism of the site out of a scheme over `S`, as a morphism of site objects. -/
private def siteHomOfScheme {U V : BigFppfOver B S hS}
    (g : U.left.1 ⟶ V.left.1)
    (hg : g ≫ B.inclusion.map V.hom = B.inclusion.map U.hom) : U ⟶ V :=
  Over.homMk (⟨g⟩ : U.left ⟶ V.left) (B.inclusion.map_injective hg)

/-- **The two models of the points of a scheme over `S` agree.** The point of the scheme
determined by a point of the slice model, reached through the equivalence with the category of
elements of the represented presheaf, is the point of the scheme of Stacks 03BX. -/
theorem schemePoint_spacePointMap (U : BigFppfOver B S hS)
    (r : Space.points B S hS (yoneda.obj U)) :
    schemePoint B S hS U
        (spacePointMap B S hS (yoneda.obj U) (schemeFibredCategory B S hS U)
          (schemeFibredCategoryEquivalence B S hS U).inverse r) =
      Space.pointsToScheme B S hS U r := by
  induction r using Quot.inductionOn with
  | h p =>
    rw [spacePointMap_class]
    rfl

/-- The point map of the equivalence from the category fibred in groupoids represented by the
space of `U` to the slice model of `U` is surjective. -/
private theorem spacePointMap_inverse_surjective (U : BigFppfOver B S hS) :
    Function.Surjective (spacePointMap B S hS (yoneda.obj U) (schemeFibredCategory B S hS U)
      (schemeFibredCategoryEquivalence B S hS U).inverse) :=
  (spacePointMap_surjective_iff_pointsMap_surjective B S hS (yoneda.obj U)
    (schemeFibredCategory B S hS U) (schemeFibredCategoryEquivalence B S hS U).inverse).2
    (pointsMap_surjective_of_basedEquivalence B S hS
      (𝒜 := fibredCategory B S hS (yoneda.obj U)) (𝒞 := schemeFibredCategory B S hS U)
      (schemeFibredCategoryEquivalence B S hS U).symm)

/-- Every point of the scheme underlying `U` comes from a point of the category fibred in
groupoids represented by `U`. -/
theorem schemePoint_surjective (U : BigFppfOver B S hS) :
    Function.Surjective (schemePoint B S hS U) := by
  intro x
  obtain ⟨r, hr⟩ := Space.surjective_pointsToScheme B S hS U x
  refine ⟨spacePointMap B S hS (yoneda.obj U) (schemeFibredCategory B S hS U)
    (schemeFibredCategoryEquivalence B S hS U).inverse r, ?_⟩
  rwa [schemePoint_spacePointMap]

/-- Distinct points of the category fibred in groupoids represented by `U` have distinct
underlying scheme points. -/
theorem schemePoint_injective (U : BigFppfOver B S hS) :
    Function.Injective (schemePoint B S hS U) := by
  intro x x' hxx'
  obtain ⟨r, hr⟩ := spacePointMap_inverse_surjective B S hS U x
  obtain ⟨r', hr'⟩ := spacePointMap_inverse_surjective B S hS U x'
  rw [← hr, ← hr'] at hxx' ⊢
  rw [schemePoint_spacePointMap, schemePoint_spacePointMap] at hxx'
  exact congrArg _ (Space.injective_pointsToScheme B S hS U hxx')

end Represented

/-- A point in the closure of the image of a quasi-compact 1-morphism of algebraic stacks is
reached by the closed point of a valuative square. **Stacks 0CL2.** -/
@[stacks 0CL2]
theorem exists_valuationRing_of_mem_closure_range_pointsMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hf : IsQuasiCompactMorphism.{u, w} B S hS f)
    (y : points B S hS 𝒴.val.val (Classical.choose 𝒴.property))
    (hy : y ∈ @closure _
      (pointTopology B S hS 𝒴.val)
      (Set.range
      (pointsMap B S hS 𝒳.val.val (Classical.choose 𝒳.property)
        (Classical.choose 𝒴.property) f.hom.hom))) :
    ∃ (q : ValuativeSquare B S hS f)
      (hz : B.Contains
        (Spec (.of ((Spec (.of q.R)).residueField (IsLocalRing.closedPoint q.R))))),
      pointClass B S hS 𝒴.val.val
        (Classical.choose 𝒴.property)
        (fieldValuedPointMap B S hS
          (schemeFibredCategory B S hS
            (siteObject B S hS q.ring_mem q.base)).val
          q.y.hom
          (closedPointFieldValuedPoint B S hS
            (siteObject B S hS q.ring_mem q.base)
            (IsLocalRing.closedPoint q.R) hz)) = y := by
  classical
  -- the atlas of `𝒴` supplied by the algebraic-stack condition
  have hcopy := 𝒴.property
  obtain ⟨_hFib, -, -, U, a, hrepa, hAtlas⟩ := hcopy
  have hU := isAlgebraicSpace_yoneda B S hS U
  let e := schemeFibredCategoryEquivalence B S hS U
  let _ : Functor.IsEquivalence e.inverse.toFunctor := e.equiv.isEquivalence_inverse
  let _ : Functor.IsEquivalence (BasedFunctor.id 𝒴.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒴.val.val.obj))
  let 𝒰 : AlgebraicStacks.{u, w} B S hS :=
    ⟨schemeFibredCategory B S hS U, isAlgebraicStack_schemeFibredCategory B S hS U⟩
  let α : 𝒰 ⟶ 𝒴 :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom a)
  have hαSurj := (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS
    α hrepa).2 (fun V z hz G hG hE => (hAtlas V z hz G hG hE).1)
  -- the atlas, read as a chart by the algebraic space `yoneda.obj U`
  let b := BasedFunctor.comp e.inverse a
  have hbSmooth : IsRelativelySmooth B S hS
      (Bicategory.InducedBicategory.mkHom b :
        fibredCategory B S hS (yoneda.obj U) ⟶ 𝒴.val) := by
    refine isRelativelySmooth_of_equivalences B S hS _
      (Bicategory.InducedBicategory.mkHom a : schemeFibredCategory B S hS U ⟶ 𝒴.val)
      e.inverse (BasedFunctor.id 𝒴.val.val) (Iso.refl _) ⟨hrepa, ?_⟩
    intro V z hz G hG hE
    exact (hAtlas V z hz G hG hE).2
  let pa := spacePointMap B S hS (yoneda.obj U) 𝒴.val b
  let ι := spacePointMap B S hS (yoneda.obj U) (schemeFibredCategory B S hS U) e.inverse
  have hpa : pa = pointsMap B S hS (schemeFibredCategory B S hS U).val
      (schemeFibredCategory B S hS U).property 𝒴.val.property a ∘ ι :=
    spacePointMap_comp B S hS (yoneda.obj U) (schemeFibredCategory B S hS U) 𝒴.val
      e.inverse a
  have hpaSurj : Function.Surjective pa := by
    rw [hpa]; exact hαSurj.comp (spacePointMap_inverse_surjective B S hS U)
  have hpaOpen : @IsOpenMap _ _ (Space.pointTopology B S hS (yoneda.obj U))
      (pointTopology B S hS 𝒴.val) pa := by
    refine isOpenMap_spacePointMap B S hS (yoneda.obj U) hU 𝒴.val 𝒴.property b ?_
    intro V z hz G hG hE
    have hsm := hbSmooth.2 V z hz G hG hE
    exact ⟨Space.isFlat_of_isSmooth B S hS _ hsm,
      Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsm⟩
  -- a point of the atlas above `y`, and the point of its scheme it determines
  let _ : TopologicalSpace (points B S hS 𝒴.val.val 𝒴.val.property) :=
    pointTopology B S hS 𝒴.val
  let _ : TopologicalSpace (Space.points B S hS (yoneda.obj U)) :=
    Space.pointTopology B S hS (yoneda.obj U)
  obtain ⟨q₀, hq₀⟩ := hpaSurj y
  let x := ι q₀
  have hx : pointsMap B S hS (schemeFibredCategory B S hS U).val
      (schemeFibredCategory B S hS U).property 𝒴.val.property a x = y := by
    rw [← hq₀, hpa]; rfl
  let T := (BigFppfOver.toScheme B S hS).obj U
  let z : T := schemePoint B S hS U x
  have hz : z = Space.schemePointsHomeomorph B S hS U q₀ :=
    schemePoint_spacePointMap B S hS U q₀
  let pf := pointsMap B S hS 𝒳.val.val (Classical.choose 𝒳.property)
    (Classical.choose 𝒴.property) f.hom.hom
  let E : Set T := Space.schemePointsHomeomorph B S hS U '' (pa ⁻¹' Set.range pf)
  have hzE : z ∈ closure E := by
    rw [hz, ← Homeomorph.image_closure]
    exact Set.mem_image_of_mem _
      (hpaOpen.preimage_closure_subset_closure_preimage (by rw [Set.mem_preimage, hq₀]; exact hy))
  -- an affine open neighbourhood of `z` in the atlas
  obtain ⟨R, i, hi, hzi, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (U := ⊤) (Set.mem_univ z)
  have hVmem : B.Contains (Spec (.of R)) :=
    Scheme.size_lt_of_isOpenImmersion i U.left.property
  let vbase : B.obj hVmem ⟶ U.left := B.inclusion.preimage
    (show B.inclusion.obj (B.obj hVmem) ⟶ B.inclusion.obj U.left from i)
  have hvbase : B.inclusion.map vbase = i := B.inclusion.map_preimage _
  let V : BigFppfOver B S hS := Over.mk (vbase ≫ U.hom)
  let vi : V ⟶ U := Over.homMk vbase (by rfl)
  let 𝒱 : AlgebraicStacks.{u, w} B S hS :=
    ⟨schemeFibredCategory B S hS V, isAlgebraicStack_schemeFibredCategory B S hS V⟩
  have hVqc : IsQuasiCompactStack.{u, w} B S hS 𝒱.val 𝒱.property := by
    let eV := schemeFibredCategoryEquivalence B S hS V
    let _ : TopologicalSpace (Space.points B S hS (yoneda.obj V)) :=
      Space.pointTopology B S hS (yoneda.obj V)
    let _ : TopologicalSpace (points B S hS 𝒱.val.val 𝒱.val.property) :=
      pointTopology B S hS 𝒱.val
    let _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj V) := by
      show CompactSpace (Spec (.of R)); infer_instance
    let _ : CompactSpace (Space.points B S hS (yoneda.obj V)) :=
      (Space.schemePointsHomeomorph B S hS V).symm.compactSpace
    exact Function.Surjective.compactSpace
      (continuous_spacePointMap B S hS (yoneda.obj V)
        (isAlgebraicSpace_yoneda B S hS V) 𝒱.val eV.inverse)
      (spacePointMap_inverse_surjective B S hS V)
  -- the base change of `f` along the affine chart, and an affine chart of it
  let aV := BasedFunctor.comp (overMapBased B S hS vi) a
  let g : 𝒱 ⟶ 𝒴 :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom aV)
  let sq := twoFibreProductSquareAlgebraicStacks B S hS g f
  have hsq : Bicategory.IsTwoFibreProduct sq :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f
  have hPqc : IsQuasiCompactStack.{u, w} B S hS sq.pt.val sq.pt.property := hf 𝒱 g hVqc
  obtain ⟨W, hWaff, bW, hbWSurj, hbWSmooth⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS sq.pt).1 hPqc
  let c := bW ≫ sq.fst
  let m := (BigFppfOver.toScheme B S hS).map (schemeMapOfFunctor B S hS c.hom.hom)
  -- every point of the affine chart in the closure set lifts to the chart of the base change
  obtain ⟨v, hiv⟩ := hzi
  have hvclosure : v ∈ closure (Set.range m) := by
    refine closure_mono (s := i ⁻¹' E) ?_
      (i.isOpenEmbedding.isOpenMap.preimage_closure_subset_closure_preimage
        (by rw [Set.mem_preimage, hiv]; exact hzE))
    rintro v' ⟨r, ⟨x', hxr⟩, hr⟩
    obtain ⟨vPt, hvPt⟩ := schemePoint_surjective B S hS V v'
    have hvi : pointsMap B S hS (schemeFibredCategory B S hS V).val
        (schemeFibredCategory B S hS V).property
        (schemeFibredCategory B S hS U).property (overMapBased B S hS vi) vPt = ι r := by
      apply schemePoint_injective B S hS U
      rw [schemePoint_naturality, schemeMapOfFunctor_overMapBased,
        schemePoint_spacePointMap]
      show B.inclusion.map vbase (schemePoint B S hS V vPt) = _
      rw [hvbase, hvPt]
      exact hr.symm
    have hgpt : pointsMap B S hS 𝒱.val.val (Classical.choose 𝒱.property)
        (Classical.choose 𝒴.property) g.hom.hom vPt = pf x' := by
      rw [show g.hom.hom = BasedFunctor.comp (overMapBased B S hS vi) a from rfl,
        ← pointsMap_comp B S hS (schemeFibredCategory B S hS V).val
          (schemeFibredCategory B S hS V).property
          (schemeFibredCategory B S hS U).property 𝒴.val.property
          (overMapBased B S hS vi) a vPt, hvi]
      rw [hpa] at hxr
      exact hxr.symm
    obtain ⟨pP, hpP, -⟩ :=
      exists_point_of_isTwoFibreProduct_algebraicStacks B S hS sq hsq vPt x' hgpt
    obtain ⟨wPt, hwPt⟩ := hbWSurj pP
    -- surjectivity of `bW` is stated at `AlgebraicStacks.pointsMap`; the rewrite below needs the
    -- same equation at the map on points of the underlying categories fibred in groupoids
    have hwPt' : pointsMap B S hS (schemeFibredCategory B S hS W).val
        (schemeFibredCategory B S hS W).property sq.pt.val.property bW.hom.hom wPt = pP := hwPt
    refine ⟨schemePoint B S hS W wPt, ?_⟩
    rw [← schemePoint_naturality B S hS c.hom.hom wPt]
    have hc : pointsMap B S hS (schemeFibredCategory B S hS W).val
        (schemeFibredCategory B S hS W).property
        (schemeFibredCategory B S hS V).property c.hom.hom wPt = vPt := by
      rw [show c.hom.hom = BasedFunctor.comp bW.hom.hom sq.fst.hom.hom from rfl,
        ← pointsMap_comp B S hS (schemeFibredCategory B S hS W).val
          (schemeFibredCategory B S hS W).property sq.pt.val.property
          (schemeFibredCategory B S hS V).property bW.hom.hom sq.fst.hom.hom wPt, hwPt']
      exact hpP
    rw [hc, hvPt]
  -- the valuation ring, read off the affine coordinates of the chart
  let _ : IsAffine W.left.1 := hWaff
  let eW := W.left.1.isoSpec
  let φ := (Spec.preimage (eW.inv ≫ m)).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = eW.inv ≫ m := Spec.map_preimage _
  have hcl : v ∈ closure (Set.range (PrimeSpectrum.comap φ)) := by
    have hr : Set.range (PrimeSpectrum.comap φ) = Set.range m := by
      show Set.range (Spec.map (CommRingCat.ofHom φ)) = _
      rw [hφ]
      ext t
      constructor
      · rintro ⟨r, rfl⟩
        exact ⟨eW.inv r, rfl⟩
      · rintro ⟨r, rfl⟩
        exact ⟨eW.hom r, congrArg m
          (congrArg (fun t : W.left.1 ⟶ W.left.1 => t r) eW.hom_inv_id)⟩
    rwa [hr]
  obtain ⟨A, hA, hAd, hAv, hAsize, K, hK, hAK, hAF, k, h, hcomm, hclosed⟩ :=
    exists_valuation_diagram_of_mem_closure_affine_range φ v hcl
  let gen := Spec.map (CommRingCat.ofHom (algebraMap A K))
  have hAmem : B.Contains (Spec (.of A)) :=
    spec_mem_of_ring_cardinality_bound B
      (by change Scheme.size (Spec _) < B.cutoff
          exact (Scheme.size_congr eW).symm.trans_lt W.left.2) hAsize
  have hKmem : B.Contains (Spec (.of K)) :=
    spec_mem_of_ring_cardinality_bound B hAmem
      ((IsLocalization.cardinalMk_le (nonZeroDivisors A)).trans (le_max_right _ _))
  let base := h ≫ B.inclusion.map V.hom
  let Aobj := siteObject B S hS hAmem base
  let Kobj := siteObject B S hS hKmem (gen ≫ base)
  let hOver : Aobj ⟶ V := siteHomOfScheme B S hS h rfl
  let jOver : Kobj ⟶ Aobj := siteHomOfScheme B S hS gen rfl
  have hkm : (k ≫ eW.inv) ≫ m = gen ≫ h := by
    rw [Category.assoc, ← hφ]
    exact hcomm
  have hm_base : m ≫ B.inclusion.map V.hom = B.inclusion.map W.hom :=
    congrArg B.inclusion.map (Over.w (schemeMapOfFunctor B S hS c.hom.hom))
  let kOver : Kobj ⟶ W := siteHomOfScheme B S hS (k ≫ eW.inv) (by
    rw [← hm_base, ← Category.assoc, hkm, Category.assoc]
    rfl)
  let jCat := schemeFibredCategoryMap B S hS jOver
  let hCat := schemeFibredCategoryMap B S hS hOver
  let kCat := schemeFibredCategoryMap B S hS kOver
  let viCat := schemeFibredCategoryMap B S hS vi
  have hj : schemeMapOfFunctor B S hS (jCat ≫ hCat).hom = jOver ≫ hOver :=
    schemeMapOfFunctor_comp_overMapBased_overMapBased B S hS jOver hOver
  have hkc : schemeMapOfFunctor B S hS (kCat ≫ c.hom).hom =
      kOver ≫ schemeMapOfFunctor B S hS c.hom.hom :=
    schemeMapOfFunctor_comp_overMapBased B S hS kOver c.hom.hom
  have hmaps : schemeMapOfFunctor B S hS (jCat ≫ hCat).hom =
      schemeMapOfFunctor B S hS (kCat ≫ c.hom).hom := by
    rw [hj, hkc]
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    exact hkm.symm
  let η : (jCat ≫ hCat) ⟶ (kCat ≫ c.hom) :=
    Bicategory.InducedBicategory.mkHom₂ (basedNatTransOfSchemeMapEq B S hS _ _ hmaps)
  let xx := (kCat ≫ bW.hom) ≫ sq.snd.hom
  let yy := hCat ≫ g.hom
  let γ : (jCat ≫ yy) ⟶ (xx ≫ f.hom) :=
    (α_ jCat hCat g.hom).inv ≫ (η ▷ g.hom) ≫ (α_ kCat c.hom g.hom).hom ≫
      (kCat ◁ ((α_ bW.hom sq.fst.hom g.hom).hom ≫ (bW.hom ◁ sq.iso.hom.hom) ≫
        (α_ bW.hom sq.snd.hom f.hom).inv)) ≫
      (α_ kCat (bW.hom ≫ sq.snd.hom) f.hom).inv
  let qsq : ValuativeSquare B S hS f :=
    { R := A
      K := K
      ring_mem := hAmem
      field_mem := hKmem
      base := base
      genericMap := jOver
      genericMap_left := rfl
      j := jCat
      j_canonical := rfl
      x := xx
      y := yy
      γ := γ }
  have hres := BigFppfSite.residueField_spec_contains B hAmem (closedPoint A)
  refine ⟨qsq, hres, ?_⟩
  -- the closed point of the valuation spectrum lands on `y`
  let special := pointClass B S hS (schemeFibredCategory B S hS Aobj).val
    (schemeFibredCategory B S hS Aobj).property
    (closedPointFieldValuedPoint B S hS Aobj (closedPoint A) hres)
  have hspecial : schemePoint B S hS Aobj special = closedPoint A :=
    (Spec (.of A)).fromSpecResidueField_apply (closedPoint A) _
  have hhv : schemeMapOfFunctor B S hS (hCat ≫ viCat).hom = hOver ≫ vi :=
    schemeMapOfFunctor_comp_overMapBased_overMapBased B S hS hOver vi
  have hmhv : (BigFppfOver.toScheme B S hS).map
      (schemeMapOfFunctor B S hS (hCat ≫ viCat).hom) = h ≫ i := by
    rw [hhv]
    show B.inclusion.map (hOver.left ≫ vbase) = _
    rw [B.inclusion.map_comp, hvbase]
    rfl
  have htarget : pointsMap B S hS (schemeFibredCategory B S hS Aobj).val
      (schemeFibredCategory B S hS Aobj).property
      (schemeFibredCategory B S hS U).property (hCat ≫ viCat).hom special = x := by
    apply schemePoint_injective B S hS U
    rw [schemePoint_naturality, hmhv, hspecial]
    show i (h (closedPoint A)) = schemePoint B S hS U x
    exact (congrArg i hclosed).trans hiv
  show pointsMap B S hS (schemeFibredCategory B S hS Aobj).val
    (schemeFibredCategory B S hS Aobj).property
    (Classical.choose 𝒴.property) yy.hom special = y
  refine Eq.trans (pointsMap_comp B S hS (schemeFibredCategory B S hS Aobj).val
    (schemeFibredCategory B S hS Aobj).property
    (schemeFibredCategory B S hS U).property 𝒴.val.property
    (hCat ≫ viCat).hom a special).symm ?_
  rw [htarget]
  exact hx

end AlgebraicGeometry.Stack

end
