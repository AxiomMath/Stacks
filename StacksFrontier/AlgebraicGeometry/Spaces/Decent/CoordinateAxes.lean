module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.Homology.Tor.ChangeOfRings

/-!
# The coordinate axes and the relation swapping them away from the origin

Over a field `k`, let `U` be the spectrum of `k[x, y] / (xy)`, the union of the two
coordinate axes. This file constructs the origin of `U`, the automorphism `σ` interchanging
the two axes, the graph of `σ`, and the relation obtained as the disjoint union of the
diagonal of `U` with the graph of `σ` away from the origin. That relation maps
monomorphically to `U ×ₖ U`.

## Main definitions

* `AlgebraicGeometry.Space.EtaleRelation.CoordinateAxesQuotientSetup` packages the ground
  field.
* `AlgebraicGeometry.Space.EtaleRelation.coordinateAxes` is `Spec(k[x, y] / (xy))`.
* `AlgebraicGeometry.Space.EtaleRelation.coordinateSwapIso` interchanges the two
  coordinates.
* `AlgebraicGeometry.Space.EtaleRelation.origin` and
  `AlgebraicGeometry.Space.EtaleRelation.puncturedCoordinateAxes` are the origin and its
  open complement.
* `AlgebraicGeometry.Space.EtaleRelation.relationScheme`,
  `AlgebraicGeometry.Space.EtaleRelation.relationMap` and the two projections
  `AlgebraicGeometry.Space.EtaleRelation.relationLeft`,
  `AlgebraicGeometry.Space.EtaleRelation.relationRight` are the relation, its map to
  `U ×ₖ U`, and the two maps to `U` that map induces.

## Main results

* `AlgebraicGeometry.Space.EtaleRelation.relationLeft_inl'`,
  `AlgebraicGeometry.Space.EtaleRelation.relationRight_inl'`,
  `AlgebraicGeometry.Space.EtaleRelation.relationLeft_inr'` and
  `AlgebraicGeometry.Space.EtaleRelation.relationRight_inr'` compute the two projections on
  each summand of the relation.
* `AlgebraicGeometry.Space.EtaleRelation.coe_puncturedCoordinateAxes` identifies the chosen
  open with the complement of the origin.
* `AlgebraicGeometry.Space.EtaleRelation.relationMap_mono` says that the relation maps
  monomorphically to `U ×ₖ U`.

## Implementation notes

The setup bundles the field; all the remaining data are constructed from it rather than
chosen independently. The coordinate ring, its variables and its defining ideal are the
nodal-ring construction of `CochainComplex.DerivedChangeOfRings`. The relation scheme is the
coproduct `U ⨿ (U \ {0})`; its map to the fibre product restricts to the diagonal on the
first summand and to the graph of the coordinate swap on the second summand, so the
coproduct retains exactly the two displayed components.

Monicity is proved through `AlgebraicGeometry.SurjectiveOnStalks.mono_of_injective`:
injectivity on points is checked summand by summand, using that the coordinate swap fixes
only the origin, and surjectivity on stalks is Zariski-local on the source, where each
summand gives a closed immersion.

## References

* [Stacks Project, Example 72.10.4 (Tag 0ENU)](https://stacks.math.columbia.edu/tag/0ENU)
-/

@[expose] public section

open CategoryTheory Limits
open CommRingCat
open CochainComplex.DerivedChangeOfRings

noncomputable section

universe u

namespace AlgebraicGeometry.Space.EtaleRelation

/-- The ground field for the coordinate-axes quotient construction. -/
structure CoordinateAxesQuotientSetup where
  /-- The ground field. -/
  k : Type u
  /-- The field structure on the ground field. -/
  field : Field k

/-- The ground field of the setup, with its recorded field structure. -/
instance (S : CoordinateAxesQuotientSetup.{u}) : Field S.k := S.field

/-- The automorphism of `k[x, y]` interchanging `x` and `y`. -/
def swapPolynomialEquiv (S : CoordinateAxesQuotientSetup.{u}) :
    PolynomialRing S.k ≃ₐ[S.k] PolynomialRing S.k :=
  MvPolynomial.renameEquiv S.k (Equiv.swap false true)

/-- The automorphism of `k[x, y] / (xy)` induced by interchanging `x` and `y`. -/
def swapRingEquiv (S : CoordinateAxesQuotientSetup.{u}) :
    NodalRing S.k ≃ₐ[S.k] NodalRing S.k :=
  Ideal.quotientEquivAlg (nodalRelationIdeal S.k) (nodalRelationIdeal S.k)
    (swapPolynomialEquiv S) (by
      simp [nodalRelationIdeal, xVariable, yVariable, swapPolynomialEquiv,
        Ideal.map_span, mul_comm])

/-- The union `U = Spec(k[x, y] / (xy))` of the coordinate axes. -/
abbrev coordinateAxes (S : CoordinateAxesQuotientSetup.{u}) : Scheme.{u} :=
  Spec (.of (NodalRing S.k))

/-- The structure morphism `U ⟶ Spec k`. -/
def baseMap (S : CoordinateAxesQuotientSetup.{u}) :
    coordinateAxes S ⟶ Spec (.of S.k) :=
  Spec.map (CommRingCat.ofHom (algebraMap S.k (NodalRing S.k)))

/-- The automorphism of `U` which interchanges its two coordinate axes. -/
def coordinateSwapIso (S : CoordinateAxesQuotientSetup.{u}) :
    coordinateAxes S ≅ coordinateAxes S :=
  Scheme.Spec.mapIso (swapRingEquiv S).toCommRingCatIso.op

/-- The morphism underlying the automorphism interchanging the two coordinate axes. -/
abbrev coordinateSwap (S : CoordinateAxesQuotientSetup.{u}) :
    coordinateAxes S ⟶ coordinateAxes S :=
  (coordinateSwapIso S).hom

/-- Evaluation at `(0, 0)` on `k[x, y]`. -/
def originPolynomialMap (S : CoordinateAxesQuotientSetup.{u}) :
    PolynomialRing S.k →+* S.k :=
  MvPolynomial.eval₂Hom (RingHom.id S.k) 0

/-- Evaluation at the origin on `k[x, y] / (xy)`. -/
def originRingMap (S : CoordinateAxesQuotientSetup.{u}) :
    NodalRing S.k →+* S.k :=
  Ideal.Quotient.lift (nodalRelationIdeal S.k) (originPolynomialMap S) (by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
        obtain rfl := hp
        simp [originPolynomialMap]
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul a b _ hb => rw [smul_eq_mul, map_mul, hb, mul_zero])

/-- The origin `0_U` of the coordinate axes. -/
def origin (S : CoordinateAxesQuotientSetup.{u}) : coordinateAxes S :=
  Spec.map (CommRingCat.ofHom (originRingMap S)) default

/-- The global section of `U` given by the first coordinate. -/
def xSection (S : CoordinateAxesQuotientSetup.{u}) : Γ(coordinateAxes S, ⊤) :=
  (Scheme.ΓSpecIso (.of (NodalRing S.k))).inv (xClass S.k)

/-- The global section of `U` given by the second coordinate. -/
def ySection (S : CoordinateAxesQuotientSetup.{u}) : Γ(coordinateAxes S, ⊤) :=
  (Scheme.ΓSpecIso (.of (NodalRing S.k))).inv (yClass S.k)

/-- The punctured coordinate axes `U \ {0_U}`, written as `D(x) ∪ D(y)`. -/
def puncturedCoordinateAxes (S : CoordinateAxesQuotientSetup.{u}) :
    (coordinateAxes S).Opens :=
  (coordinateAxes S).basicOpen (xSection S) ⊔
    (coordinateAxes S).basicOpen (ySection S)

/-- The fibre product `U ×ₖ U`. -/
abbrev selfProduct (S : CoordinateAxesQuotientSetup.{u}) : Scheme.{u} :=
  pullback (baseMap S) (baseMap S)

/-- The diagonal `U ⟶ U ×ₖ U`. -/
def diagonal (S : CoordinateAxesQuotientSetup.{u}) :
    coordinateAxes S ⟶ selfProduct S :=
  pullback.diagonal (baseMap S)

/-- The graph `u ↦ (u, σ(u))` of the coordinate-swap automorphism. -/
def twistedDiagonal (S : CoordinateAxesQuotientSetup.{u}) :
    coordinateAxes S ⟶ selfProduct S :=
  pullback.lift (𝟙 _) (coordinateSwap S) (by
    rw [Category.id_comp]
    dsimp [baseMap, coordinateSwap, coordinateSwapIso]
    rw [← Spec.map_comp]
    congr 1
    ext a
    simp [swapRingEquiv, swapPolynomialEquiv])

/-- The scheme `R = U ⨿ (U \ {0_U})` underlying the relation. -/
abbrev relationScheme (S : CoordinateAxesQuotientSetup.{u}) : Scheme.{u} :=
  coordinateAxes S ⨿ puncturedCoordinateAxes S

/-- The map `R ⟶ U ×ₖ U`, equal to the diagonal on `U` and to the graph of the
coordinate swap on `U \ {0_U}`. -/
noncomputable def relationMap (S : CoordinateAxesQuotientSetup.{u}) :
    relationScheme S ⟶ selfProduct S :=
  coprod.desc (diagonal S)
    ((puncturedCoordinateAxes S).ι ≫ twistedDiagonal S)

/-- The first projection `R ⟶ U`. -/
def relationLeft (S : CoordinateAxesQuotientSetup.{u}) :
    relationScheme S ⟶ coordinateAxes S :=
  relationMap S ≫ pullback.fst _ _

/-- The second projection `R ⟶ U`. -/
def relationRight (S : CoordinateAxesQuotientSetup.{u}) :
    relationScheme S ⟶ coordinateAxes S :=
  relationMap S ≫ pullback.snd _ _

/-- The first projection restricts to the identity on the first summand. -/
theorem relationLeft_inl' (S : CoordinateAxesQuotientSetup.{u}) :
    (coprod.inl : coordinateAxes S ⟶ relationScheme S) ≫ relationLeft S = 𝟙 _ := by
  dsimp [relationLeft, relationMap]
  rw [← Category.assoc, coprod.inl_desc, diagonal, pullback.diagonal_fst]

/-- The second projection restricts to the identity on the first summand. -/
theorem relationRight_inl' (S : CoordinateAxesQuotientSetup.{u}) :
    (coprod.inl : coordinateAxes S ⟶ relationScheme S) ≫ relationRight S = 𝟙 _ := by
  dsimp [relationRight, relationMap]
  rw [← Category.assoc, coprod.inl_desc, diagonal, pullback.diagonal_snd]

/-- The first projection restricts to the open inclusion on the second summand. -/
theorem relationLeft_inr' (S : CoordinateAxesQuotientSetup.{u}) :
    (coprod.inr : (↑(puncturedCoordinateAxes S) : Scheme) ⟶ relationScheme S) ≫
      relationLeft S = (puncturedCoordinateAxes S).ι := by
  dsimp [relationLeft, relationMap]
  rw [← Category.assoc, coprod.inr_desc, Category.assoc, twistedDiagonal,
    pullback.lift_fst, Category.comp_id]

/-- The second projection restricts to the open inclusion followed by the coordinate swap on
the second summand. -/
theorem relationRight_inr' (S : CoordinateAxesQuotientSetup.{u}) :
    (coprod.inr : (↑(puncturedCoordinateAxes S) : Scheme) ⟶ relationScheme S) ≫
      relationRight S = (puncturedCoordinateAxes S).ι ≫ coordinateSwap S := by
  dsimp [relationRight, relationMap]
  rw [← Category.assoc, coprod.inr_desc, Category.assoc, twistedDiagonal,
    pullback.lift_snd]

/-- Evaluation at the origin is surjective. -/
private lemma originRingMap_surjective (S : CoordinateAxesQuotientSetup.{u}) :
    Function.Surjective (originRingMap S) := by
  intro a
  refine ⟨(nodalRingMap S.k) (MvPolynomial.C a), ?_⟩
  simp [originRingMap, originPolynomialMap]

/-- The prime of the origin is the kernel of evaluation at the origin. -/
private lemma origin_asIdeal (S : CoordinateAxesQuotientSetup.{u}) :
    (origin S).asIdeal = RingHom.ker (originRingMap S) := by
  ext a
  show (originRingMap S) a ∈ (⊥ : Ideal S.k) ↔ (originRingMap S) a = 0
  simp

/-- A point of `U` containing both coordinates is the origin. -/
private lemma origin_eq_of_mem (S : CoordinateAxesQuotientSetup.{u})
    (p : coordinateAxes S) (hx : xClass S.k ∈ p.asIdeal)
    (hy : yClass S.k ∈ p.asIdeal) : p = origin S := by
  have hpoly :
      (Ideal.Quotient.mk p.asIdeal).comp (nodalRingMap S.k) =
        ((Ideal.Quotient.mk p.asIdeal).comp (algebraMap S.k (NodalRing S.k))).comp
          (originPolynomialMap S) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, originPolynomialMap, MvPolynomial.eval₂Hom_C,
        RingHom.id_apply]
      rw [MvPolynomial.C_eq_algebraMap]
      simp only [Ideal.Quotient.mk_algebraMap]
    · intro i
      cases i
      · simp only [RingHom.comp_apply, originPolynomialMap,
          MvPolynomial.eval₂Hom_X', Pi.zero_apply, map_zero]
        show (Ideal.Quotient.mk p.asIdeal) (xClass S.k) = 0
        exact (Ideal.Quotient.eq_zero_iff_mem).mpr hx
      · simp only [RingHom.comp_apply, originPolynomialMap,
          MvPolynomial.eval₂Hom_X', Pi.zero_apply, map_zero]
        show (Ideal.Quotient.mk p.asIdeal) (yClass S.k) = 0
        exact (Ideal.Quotient.eq_zero_iff_mem).mpr hy
  have hle : RingHom.ker (originRingMap S) ≤ p.asIdeal := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    have hb : originPolynomialMap S b = 0 := by
      simpa [originRingMap, RingHom.mem_ker] using ha
    have := RingHom.congr_fun hpoly b
    simpa [hb] using this
  have hm : (RingHom.ker (originRingMap S)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (originRingMap_surjective S)
  exact PrimeSpectrum.ext ((hm.eq_of_le p.2.ne_top hle).symm.trans (origin_asIdeal S).symm)

/-- The open `D(x) ∪ D(y)` is exactly the complement of the origin in `U`. -/
theorem coe_puncturedCoordinateAxes (S : CoordinateAxesQuotientSetup.{u}) :
    (puncturedCoordinateAxes S : Set (coordinateAxes S)) = {origin S}ᶜ := by
  have hxopen : (coordinateAxes S).basicOpen (xSection S) =
      PrimeSpectrum.basicOpen (xClass S.k) := basicOpen_eq_of_affine _
  have hyopen : (coordinateAxes S).basicOpen (ySection S) =
      PrimeSpectrum.basicOpen (yClass S.k) := basicOpen_eq_of_affine _
  ext p
  show p ∈ ((coordinateAxes S).basicOpen (xSection S) ⊔
    (coordinateAxes S).basicOpen (ySection S)) ↔ p ≠ origin S
  rw [TopologicalSpace.Opens.mem_sup, hxopen, hyopen]
  show (xClass S.k ∉ p.asIdeal ∨ yClass S.k ∉ p.asIdeal) ↔ _
  constructor
  · rintro (hx | hy) rfl
    · exact hx (by simp [origin_asIdeal, originRingMap, originPolynomialMap, xClass])
    · exact hy (by simp [origin_asIdeal, originRingMap, originPolynomialMap, yClass])
  · intro hp
    by_contra! h
    exact hp (origin_eq_of_mem S p h.1 h.2)

/-- The coordinate swap is a morphism over the ground field. -/
private lemma coordinateSwap_comp_baseMap (S : CoordinateAxesQuotientSetup.{u}) :
    coordinateSwap S ≫ baseMap S = baseMap S := by
  dsimp [coordinateSwap, coordinateSwapIso, baseMap]
  rw [← Spec.map_comp]
  congr 1
  ext a
  simp [swapRingEquiv, swapPolynomialEquiv]

/-- The diagonal of `U` over the ground field is a closed immersion. -/
private lemma diagonal_isClosedImmersion (S : CoordinateAxesQuotientSetup.{u}) :
    IsClosedImmersion (diagonal S) := by
  unfold diagonal
  infer_instance

/-- The graph of the coordinate swap is a closed immersion. -/
private lemma twistedDiagonal_isClosedImmersion (S : CoordinateAxesQuotientSetup.{u}) :
    IsClosedImmersion (twistedDiagonal S) := by
  let e : selfProduct S ≅
      pullback (coordinateSwap S ≫ baseMap S) (baseMap S) :=
    pullback.congrHom (coordinateSwap_comp_baseMap S).symm rfl
  let g : coordinateAxes S ⟶
      pullback (coordinateSwap S ≫ baseMap S) (baseMap S) :=
    pullback.lift (𝟙 _) (coordinateSwap S) (by simp)
  have hg : IsClosedImmersion g := by
    dsimp [g]
    infer_instance
  have hfst : e.inv ≫ pullback.fst (baseMap S) (baseMap S) =
      pullback.fst (coordinateSwap S ≫ baseMap S) (baseMap S) := by
    dsimp [e]
    rw [pullback.congrHom_inv]
    dsimp [pullback.map]
    rw [pullback.lift_fst]
    simp
  have hsnd : e.inv ≫ pullback.snd (baseMap S) (baseMap S) =
      pullback.snd (coordinateSwap S ≫ baseMap S) (baseMap S) := by
    dsimp [e]
    rw [pullback.congrHom_inv]
    dsimp [pullback.map]
    rw [pullback.lift_snd]
    simp
  have h : twistedDiagonal S = g ≫ e.inv := by
    ext
    · dsimp [twistedDiagonal, g]
      rw [Category.assoc, hfst, pullback.lift_fst, pullback.lift_fst]
    · dsimp [twistedDiagonal, g]
      rw [Category.assoc, hsnd, pullback.lift_snd, pullback.lift_snd]
  rw [h]
  infer_instance

/-- The only fixed point of the coordinate swap is the origin. -/
private lemma coordinateSwap_eq_origin_of_fixed (S : CoordinateAxesQuotientSetup.{u})
    (p : coordinateAxes S) (hp : coordinateSwap S p = p) : p = origin S := by
  have hp' : Ideal.comap ((swapRingEquiv S).toRingEquiv) p.asIdeal = p.asIdeal := by
    have hfun : coordinateSwap S p =
        PrimeSpectrum.comap ((swapRingEquiv S).toRingEquiv) p := rfl
    exact congrArg PrimeSpectrum.asIdeal (hfun.symm.trans hp)
  have hswapX : (swapRingEquiv S).toRingEquiv (xClass S.k) = yClass S.k := by
    simp [swapRingEquiv, swapPolynomialEquiv, xClass, yClass, nodalRingMap,
      xVariable, yVariable]
  have hxy : xClass S.k ∈ p.asIdeal ↔ yClass S.k ∈ p.asIdeal := by
    rw [← hswapX, ← Ideal.mem_comap (f := (swapRingEquiv S).toRingEquiv), hp']
  have hmul : xClass S.k * yClass S.k = 0 := by
    show Ideal.Quotient.mk (nodalRelationIdeal S.k)
      (xVariable S.k * yVariable S.k) = 0
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (by simp))
  obtain hx | hy := Ideal.IsPrime.mem_or_mem_of_mul_eq_zero p.2 hmul
  · have hy : yClass S.k ∈ p.asIdeal := hxy.mp hx
    exact origin_eq_of_mem S p hx hy
  · have hx : xClass S.k ∈ p.asIdeal := hxy.mpr hy
    exact origin_eq_of_mem S p hx hy

/-- On the first summand, the first projection of the relation is the identity. -/
private lemma relationLeft_inl (S : CoordinateAxesQuotientSetup.{u})
    (x : coordinateAxes S) :
    relationLeft S ((coprod.inl : coordinateAxes S ⟶ relationScheme S) x) = x := by
  rw [← Scheme.Hom.comp_apply (f := (coprod.inl : coordinateAxes S ⟶ relationScheme S))
    (g := relationLeft S) (x := x)]
  simpa using congrArg (fun f => f x) (relationLeft_inl' S)

/-- On the second summand, the first projection of the relation is the open inclusion. -/
private lemma relationLeft_inr (S : CoordinateAxesQuotientSetup.{u})
    (x : (↑(puncturedCoordinateAxes S) : Scheme)) :
    relationLeft S ((coprod.inr : (↑(puncturedCoordinateAxes S) : Scheme) ⟶
      relationScheme S) x) = (puncturedCoordinateAxes S).ι x := by
  rw [← Scheme.Hom.comp_apply
    (f := (coprod.inr : (↑(puncturedCoordinateAxes S) : Scheme) ⟶ relationScheme S))
    (g := relationLeft S) (x := x)]
  exact congrArg (fun f => f x) (relationLeft_inr' S)

/-- On the first summand, the second projection of the relation is the identity. -/
private lemma relationRight_inl (S : CoordinateAxesQuotientSetup.{u})
    (x : coordinateAxes S) :
    relationRight S ((coprod.inl : coordinateAxes S ⟶ relationScheme S) x) = x := by
  rw [← Scheme.Hom.comp_apply (f := (coprod.inl : coordinateAxes S ⟶ relationScheme S))
    (g := relationRight S) (x := x)]
  simpa using congrArg (fun f => f x) (relationRight_inl' S)

/-- On the second summand, the second projection of the relation is the open inclusion
followed by the coordinate swap. -/
private lemma relationRight_inr (S : CoordinateAxesQuotientSetup.{u})
    (x : (↑(puncturedCoordinateAxes S) : Scheme)) :
    relationRight S ((coprod.inr : (↑(puncturedCoordinateAxes S) : Scheme) ⟶
      relationScheme S) x) = coordinateSwap S ((puncturedCoordinateAxes S).ι x) := by
  rw [← Scheme.Hom.comp_apply
    (f := (coprod.inr : (↑(puncturedCoordinateAxes S) : Scheme) ⟶ relationScheme S))
    (g := relationRight S) (x := x)]
  exact congrArg (fun f => f x) (relationRight_inr' S)

/-- Equal images under the relation have equal first projections. -/
private lemma relationLeft_eq_of_relationMap_eq (S : CoordinateAxesQuotientSetup.{u})
    {x y : relationScheme S} (h : relationMap S x = relationMap S y) :
    relationLeft S x = relationLeft S y := by
  simp only [relationLeft, Scheme.Hom.comp_apply, h]

/-- Equal images under the relation have equal second projections. -/
private lemma relationRight_eq_of_relationMap_eq (S : CoordinateAxesQuotientSetup.{u})
    {x y : relationScheme S} (h : relationMap S x = relationMap S y) :
    relationRight S x = relationRight S y := by
  simp only [relationRight, Scheme.Hom.comp_apply, h]

/-- A point of the punctured axes is not fixed by the coordinate swap. -/
private lemma false_of_coordinateSwap_fixed_punctured (S : CoordinateAxesQuotientSetup.{u})
    (b : (↑(puncturedCoordinateAxes S) : Scheme))
    (hfix : coordinateSwap S ((puncturedCoordinateAxes S).ι b) =
      (puncturedCoordinateAxes S).ι b) : False := by
  have hm : ((puncturedCoordinateAxes S).ι b : coordinateAxes S) ∈
      ({origin S}ᶜ : Set (coordinateAxes S)) := by
    rw [← coe_puncturedCoordinateAxes S]
    exact b.2
  exact hm (coordinateSwap_eq_origin_of_fixed S _ hfix)

/-- The relation is injective on points. -/
private lemma relationMap_injective (S : CoordinateAxesQuotientSetup.{u}) :
    Function.Injective (relationMap S) := by
  intro a b hab
  let e := coprodMk (coordinateAxes S) (puncturedCoordinateAxes S)
  have hab' : relationMap S (e (e.symm a)) = relationMap S (e (e.symm b)) := by
    rw [e.apply_symm_apply a, e.apply_symm_apply b]
    exact hab
  apply e.symm.injective
  rcases hs : e.symm a with a | a <;> rcases ht : e.symm b with b | b
  all_goals rw [hs, ht] at hab'
  all_goals simp only [e, coprodMk_inl, coprodMk_inr] at hab'
  all_goals have hl := relationLeft_eq_of_relationMap_eq S hab'
  all_goals have hr := relationRight_eq_of_relationMap_eq S hab'
  · simp only [relationLeft_inl] at hl
    exact congrArg Sum.inl hl
  · simp only [relationLeft_inl, relationLeft_inr, relationRight_inl, relationRight_inr] at hl hr
    exact (false_of_coordinateSwap_fixed_punctured S b (hr.symm.trans hl)).elim
  · simp only [relationLeft_inl, relationLeft_inr, relationRight_inl, relationRight_inr] at hl hr
    exact (false_of_coordinateSwap_fixed_punctured S a (hr.trans hl.symm)).elim
  · simp only [relationLeft_inr] at hl
    exact congrArg Sum.inr ((puncturedCoordinateAxes S).ι.isOpenEmbedding.injective hl)

/-- Surjectivity on stalks of `i ≫ f` for an open immersion `i` passes to the open
subscheme `i.opensRange`. -/
private lemma surjectiveOnStalks_opensRange_comp {X Y Z : Scheme} (i : X ⟶ Y)
    [IsOpenImmersion i] (f : Y ⟶ Z) (hi : SurjectiveOnStalks (i ≫ f)) :
    SurjectiveOnStalks (i.opensRange.ι ≫ f) := by
  rw [show i.opensRange.ι ≫ f = i.isoOpensRange.inv ≫ (i ≫ f) by simp]
  have := hi
  infer_instance

/-- The relation is surjective on stalks. -/
private lemma relationMap_surjectiveOnStalks (S : CoordinateAxesQuotientSetup.{u}) :
    SurjectiveOnStalks (relationMap S) := by
  have : IsClosedImmersion (diagonal S) := diagonal_isClosedImmersion S
  have : IsClosedImmersion (twistedDiagonal S) := twistedDiagonal_isClosedImmersion S
  let U : Bool → (relationScheme S).Opens := fun b =>
    if b then (coprod.inl : coordinateAxes S ⟶ relationScheme S).opensRange
    else (coprod.inr : _ ⟶ relationScheme S).opensRange
  have hU : iSup U = ⊤ := by
    ext x
    obtain ⟨(x | x), rfl⟩ :=
      (coprodMk (coordinateAxes S) (puncturedCoordinateAxes S)).surjective x
    · simp [U, coprodMk_inl, Scheme.Hom.mem_opensRange]
    · simp [U, coprodMk_inr, Scheme.Hom.mem_opensRange]
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @SurjectiveOnStalks)
    (f := relationMap S) U hU]
  intro b
  cases b
  · refine surjectiveOnStalks_opensRange_comp _ _ ?_
    rw [relationMap, coprod.inr_desc]
    infer_instance
  · refine surjectiveOnStalks_opensRange_comp _ _ ?_
    rw [relationMap, coprod.inl_desc]
    infer_instance

/-- The displayed relation maps monomorphically to `U ×ₖ U`. -/
theorem relationMap_mono (S : CoordinateAxesQuotientSetup.{u}) :
    Mono (relationMap S) := by
  have : SurjectiveOnStalks (relationMap S) := relationMap_surjectiveOnStalks S
  exact SurjectiveOnStalks.mono_of_injective (relationMap_injective S)

end AlgebraicGeometry.Space.EtaleRelation

end

end
