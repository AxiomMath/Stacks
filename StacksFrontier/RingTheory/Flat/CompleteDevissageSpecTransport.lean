module

public import StacksFrontier.Algebra.Module.RingEquivTransport
public import StacksFrontier.RingTheory.Flat.CompleteDevissage

/-!
# Transporting a complete dévissage along isomorphisms of the data

A complete dévissage of `N/S/R` at a prime `q` of `S` (Stacks 05HZ) is a statement about the
three rings `R`, `S`, `N` themselves. The geometric form of Stacks 05I0 produces one for the
*global sections* of the data — `Γ(Spec A, ⊤)`, `Γ(Spec B, ⊤)` and `Γ(Ñ, ⊤)` — and those are
only *isomorphic* to `A`, `B` and `N`, never equal: the rings `Γ(Spec B, ⊤)` and `B` are
identified by `AlgebraicGeometry.Scheme.ΓSpecIso` and by nothing finer, so

```lean
example (B : Type) [CommRing B] : (Γ(Spec (CommRingCat.of B), ⊤) : Type) = B := rfl   -- fails
```

This file closes that gap: it carries `Module.CompleteDevissage`,
`Module.NonemptyCompleteDevissageAt` and `Module.CompleteDevissageAt` across an isomorphism of
the base ring, an isomorphism of the algebra and an additive isomorphism of the module which
intertwine the structure map and the action.

## Main definitions

* `Module.CompleteDevissage.ofRingEquiv`: a complete dévissage of `N/S/R` over `r` (Stacks 05HX)
  becomes one of `N'/S'/R'` over the transported prime.
* `Module.NonemptyCompleteDevissageAt.ofRingEquiv` and `Module.CompleteDevissageAt.ofRingEquiv`:
  the same for the pointed notion of Stacks 05HZ.
* `Module.nonempty_completeDevissageAt_ofRingEquiv`: the `Nonempty` form, which is what a
  consumer stating an existence hypothesis applies.

## Main results

The transport needs a change of base ring in every condition of the dévissage, and these are the
pieces that carry it.

* `Algebra.FiniteType.of_ringEquiv`: the `Algebra.FiniteType` companion of
  `Algebra.FinitePresentation.of_ringEquiv`.
* `AlgebraicGeometry.GeometricallyIrreducible.postcomp`: geometrically irreducible fibres survive
  postcomposition with an isomorphism, which is what a change of base ring does to `Spec`.
* `PurelyTranscendental.of_ringEquiv_base`: pure transcendence of an extension does not depend on
  which model of the base field is used.
* `Ideal.residueFieldRingEquivOfRingEquiv` and `Ideal.fiberRingEquivOfRingEquiv`: the residue
  field and the fibre ring `κ(p) ⊗[R] B` of Mathlib's `Ideal.Fiber` under a change of base ring.
* `TensorProduct.congrRingEquiv`: the fibre module `κ(p) ⊗[R] B ⊗[B] M` under the same change.
* `Module.support_eq_comap_preimage` and `topologicalKrullDimAt_support_eq`: the support of a
  module and the local dimension of that support under an isomorphism of the base ring.
* `Algebra.relativeDimension_eq_of_ringEquiv`: the relative dimension is *unchanged* by a change
  of base ring along an isomorphism.

## Implementation notes

**Universes.** `Module.CompleteDevissage R S N r` puts its stage algebras in the universe of `R`
and its stage modules in the universe of `N`, so a transport that changed those universes would
have to replace the stage data as well. The transport here keeps `R`, `S` and `N` in their own
universes and takes `R'`, `S'`, `N'` in the same three, which is the shape every application has
— the two models of one ring always live in one universe — and lets the whole stage diagram,
including the maps `toLeft`, `toRight` and `alpha`, be reused verbatim.

**Whole structure, not field by field.** The transport is stated for `Module.CompleteDevissage`
and `Module.NonemptyCompleteDevissageAt` as wholes rather than as a family of field-wise lemmas
to be reassembled by the consumer. Nothing forces that choice from the outside, but it is much
the cheaper one here: the stage types `A i`, `B i`, `M i`, the maps `toLeft i`, `toRight i` and
the maps `alpha i` are *literally* the old ones, because only the `R`-algebra structures change
and `AlgHom.mk f h |>.toRingHom` is `f`. So twelve of the eighteen fields of
`Module.CompleteDevissage` and eight of the twelve of `Module.NonemptyCompleteDevissageAt` are
discharged by `D.field`, and a field-wise formulation would have to restate each of them against
a hypothetical reassembled structure, with the `Module.compHom` instances of `alpha` and
`cokerEquiv` spelled out by hand. No `HEq` arises: the only data fields whose *type* changes are
`toA₀` and `initialEquiv`, and those change along `eS` and `eN` within a fixed type.

**`Module.CompleteDevissage.ofRingEquiv` is `@[reducible]`.** The pointed transport builds its
`toCompleteDevissage` field from it and then has to state the remaining fields against the
*transported* stage algebras, which are the old ones — so instance search is asked for
`Algebra R' ((D.ofRingEquiv ‹…›).B i)` with `i` indexed by `D.stepCount`. Instance search
unfolds only reducible definitions, so without the attribute every such synthesis fails even
though the two index types are definitionally equal. The instance that is genuinely new on an
old stage algebra, `Algebra R' (D.B i)`, is still passed by hand with `inferInstanceAs`, as the
`Prop`-valued fields do not take it from a `letI`.

**What the change of base ring costs.** Four conditions are not formal. Smoothness of `B i` is
`RingHom.Smooth.comp` against `RingHom.Smooth.of_bijective`; geometric irreducibility of the
fibres is postcomposition with `Spec.map` of an isomorphism; pure transcendence of the residue
extension is `PurelyTranscendental.of_ringEquiv_base`, whose hypothesis is checked by
`Ideal.ResidueField.ringHom_ext` because a ring map out of a residue field is determined on the
image of the ring; and the two support conditions go through the isomorphism
`Ideal.fiberRingEquivOfRingEquiv` of the fibre rings. The relative dimension needs no isomorphism
at all: `Algebra.relativeDimensionAt` is the local dimension of the *set-theoretic* fibre
`comap (algebraMap R B) ⁻¹' {p}` inside `Spec B`, and that subset of `Spec B` is unchanged, since
`comap (algebraMap R' B)` is `comap eR.symm ∘ comap (algebraMap R B)` with `comap eR.symm`
injective.

## References

* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TensorProduct TopologicalSpace

universe u u' v v' w w'

/-! ### Finite type and geometric irreducibility under a change of base ring -/

/-- **Finite type of an algebra under an isomorphism of the data.** If `eR : R ≃+* R'` and
`eS : S ≃+* S'` intertwine the two structure maps and `S` is an `R`-algebra of finite type, then
`S'` is an `R'`-algebra of finite type. This is the `Algebra.FiniteType` companion of
`Algebra.FinitePresentation.of_ringEquiv`. -/
public theorem Algebra.FiniteType.of_ringEquiv {R : Type u} [CommRing R] {R' : Type u'}
    [CommRing R'] {S : Type v} [CommRing S] {S' : Type v'} [CommRing S'] [Algebra R S]
    [Algebra R' S'] (eR : R ≃+* R') (eS : S ≃+* S')
    (h : ∀ x : R, algebraMap R' S' (eR x) = eS (algebraMap R S x))
    [Algebra.FiniteType R S] : Algebra.FiniteType R' S' := by
  refine RingHom.finiteType_algebraMap.mp ?_
  have hcomp : algebraMap R' S'
      = eS.toRingHom.comp ((algebraMap R S).comp eR.symm.toRingHom) := by
    ext y
    have hy := h (eR.symm y)
    rw [eR.apply_symm_apply] at hy
    simpa using hy
  rw [hcomp]
  exact RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ eS.surjective)
    (RingHom.FiniteType.comp (RingHom.finiteType_algebraMap.mpr ‹_›)
      (RingHom.FiniteType.of_surjective _ eR.symm.surjective))

/-- A morphism with geometrically irreducible fibres still has them after composing with an
isomorphism of the target: the property is `AlgebraicGeometry.geometrically (IrreducibleSpace ·)`,
which respects isomorphisms. Replacing the base ring of an algebra by an isomorphic one does
exactly this to `Spec` of its structure map. -/
public theorem AlgebraicGeometry.GeometricallyIrreducible.postcomp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (e : Y ⟶ Z) [IsIso e] [GeometricallyIrreducible f] :
    GeometricallyIrreducible (f ≫ e) := by
  have h : @GeometricallyIrreducible = geometrically (IrreducibleSpace ·) :=
    GeometricallyIrreducible.eq_geometrically
  have hthis : geometrically (IrreducibleSpace ·) f := h ▸ ‹GeometricallyIrreducible f›
  exact h ▸ MorphismProperty.RespectsIso.postcomp
    (P := geometrically (IrreducibleSpace ·)) e f hthis

/-- Bijectivity of the scalar extension of a map to the residue field of an ideal does not see
which proof of primality is used, nor which of two equal ideals is named. This is the form in
which the fibre condition of a complete dévissage is transported, the extended ideal `rB` being
the same ideal of `B` computed from two different base rings. -/
public theorem bijective_baseChange_congr {B : Type u} [CommRing B] {M : Type w} [AddCommGroup M]
    [Module B M] {n : ℕ} {I J : Ideal B} (hIJ : I = J) (hI : I.IsPrime) (hJ : J.IsPrime)
    (α : (Fin n →₀ B) →ₗ[B] M)
    (h : Function.Bijective (α.baseChange (@Ideal.ResidueField B _ J hJ))) :
    Function.Bijective (α.baseChange (@Ideal.ResidueField B _ I hI)) := by
  subst hIJ
  exact h

/-! ### Pure transcendence under a change of base field -/

/-- **Pure transcendence does not depend on the model of the base field.** If `psi : K ≃+* K'`
identifies two models of the base and the two structure maps to `L` agree through it, then `L` is
purely transcendental over `K'` as soon as it is over `K`: the same transcendence basis works,
because the images of `K` and of `K'` in `L` coincide and `MvPolynomial.mapEquiv psi` identifies
the two polynomial rings over the basis. -/
public theorem PurelyTranscendental.of_ringEquiv_base {K : Type u} {K' : Type u'} {L : Type v}
    [Field K] [Field K'] [Field L] [Algebra K L] [Algebra K' L] (psi : K ≃+* K')
    (hpsi : ∀ x : K, algebraMap K' L (psi x) = algebraMap K L x)
    [PurelyTranscendental K L] : PurelyTranscendental K' L := by
  obtain ⟨s, hsi, hsa⟩ := PurelyTranscendental.exists_basis K L
  have hcomp : (algebraMap K' L).comp (psi : K →+* K') = algebraMap K L := RingHom.ext hpsi
  have hrange : Set.range (algebraMap K L) = Set.range (algebraMap K' L) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨psi x, hpsi x⟩
    · rintro _ ⟨y, rfl⟩
      exact ⟨psi.symm y, by rw [← hpsi (psi.symm y), psi.apply_symm_apply]⟩
  refine ⟨s, ?_, ?_⟩
  · replace hsi := algebraicIndependent_iff.mp hsi
    refine algebraicIndependent_iff.mpr ?_
    intro q hq
    obtain ⟨p, rfl⟩ := (MvPolynomial.mapEquiv (↥s) psi).surjective q
    rw [MvPolynomial.mapEquiv_apply] at hq ⊢
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, hcomp, ← MvPolynomial.aeval_def] at hq
    rw [hsi p hq, map_zero]
  · apply SetLike.coe_injective
    rw [IntermediateField.coe_top, ← IntermediateField.coe_toSubfield,
      IntermediateField.adjoin_toSubfield, ← hrange, ← IntermediateField.adjoin_toSubfield,
      IntermediateField.coe_toSubfield, hsa, IntermediateField.coe_top]

/-! ### The residue field and the fibre ring under a change of base ring -/

/-- The isomorphism of residue fields induced by an isomorphism `eR : R ≃+* R'` of the ambient
rings carrying a prime `p` of `R` to a prime `p'` of `R'`. It is Mathlib's
`Ideal.ResidueField.map`, which is bijective here because `eR` is surjective on stalks. -/
public noncomputable def Ideal.residueFieldRingEquivOfRingEquiv {R : Type u} [CommRing R]
    {R' : Type u'} [CommRing R'] (eR : R ≃+* R') (p : Ideal R) [p.IsPrime]
    (p' : Ideal R') [p'.IsPrime] (hp : p = p'.comap eR.toRingHom) :
    p.ResidueField ≃+* p'.ResidueField :=
  RingEquiv.ofBijective (Ideal.ResidueField.map p p' eR.toRingHom hp)
    (eR.surjectiveOnStalks.residueFieldMap_bijective p p' hp)

/-- `Ideal.residueFieldRingEquivOfRingEquiv` commutes with the two structure maps. -/
@[simp]
public lemma Ideal.residueFieldRingEquivOfRingEquiv_algebraMap {R : Type u} [CommRing R]
    {R' : Type u'} [CommRing R'] (eR : R ≃+* R') (p : Ideal R) [p.IsPrime]
    (p' : Ideal R') [p'.IsPrime] (hp : p = p'.comap eR.toRingHom) (r : R) :
    Ideal.residueFieldRingEquivOfRingEquiv eR p p' hp (algebraMap R p.ResidueField r)
      = algebraMap R' p'.ResidueField (eR r) :=
  Ideal.ResidueField.map_algebraMap p p' eR.toRingHom hp r

/-- The isomorphism `κ(p) ⊗[R] B ≃ κ(p') ⊗[R'] B` of fibre rings induced by an isomorphism
`eR : R ≃+* R'` of base rings acting on one and the same algebra `B` through intertwined
structure maps. It is built from `Algebra.TensorProduct.lift` in both directions, over `R` one way
and over `R'` the other, the two round trips being the identity on the generators. -/
public noncomputable def Ideal.fiberRingEquivOfRingEquiv {R : Type u} [CommRing R]
    {R' : Type u'} [CommRing R'] {B : Type v} [CommRing B] [Algebra R B] [Algebra R' B]
    (eR : R ≃+* R') (hmap : ∀ r : R, algebraMap R' B (eR r) = algebraMap R B r)
    (p : Ideal R) [p.IsPrime] (p' : Ideal R') [p'.IsPrime] (hp : p = p'.comap eR.toRingHom) :
    p.Fiber B ≃+* p'.Fiber B :=
  letI : Algebra R (p'.Fiber B) := ((algebraMap R' (p'.Fiber B)).comp eR.toRingHom).toAlgebra
  letI : Algebra R' (p.Fiber B) := ((algebraMap R (p.Fiber B)).comp eR.symm.toRingHom).toAlgebra
  let e := Ideal.residueFieldRingEquivOfRingEquiv eR p p' hp
  have hmap' : ∀ r : R', algebraMap R B (eR.symm r) = algebraMap R' B r := fun r => by
    rw [← hmap (eR.symm r), eR.apply_symm_apply]
  have he : ∀ r : R, e (algebraMap R p.ResidueField r) = algebraMap R' p'.ResidueField (eR r) :=
    Ideal.residueFieldRingEquivOfRingEquiv_algebraMap eR p p' hp
  have hes : ∀ r : R', e.symm (algebraMap R' p'.ResidueField r)
      = algebraMap R p.ResidueField (eR.symm r) := fun r => e.injective <| by
    rw [RingEquiv.apply_symm_apply, Ideal.residueFieldRingEquivOfRingEquiv_algebraMap,
      eR.apply_symm_apply]
  let F : p.Fiber B →+* p'.Fiber B :=
    (Algebra.TensorProduct.lift (A := p.ResidueField) (B := B) (C := p'.Fiber B) (S := R)
      { __ := (Algebra.TensorProduct.includeLeftRingHom (R := R') (B := B)).comp e.toRingHom
        commutes' := fun r => by simp [RingHom.algebraMap_toAlgebra, he r] }
      { __ := (Algebra.TensorProduct.includeRight (R := R')
          (A := p'.ResidueField) (B := B)).toRingHom
        commutes' := fun r => by simp [RingHom.algebraMap_toAlgebra, ← hmap r] }
      fun _ _ => Commute.all _ _).toRingHom
  let G : p'.Fiber B →+* p.Fiber B :=
    (Algebra.TensorProduct.lift (A := p'.ResidueField) (B := B) (C := p.Fiber B) (S := R')
      { __ := (Algebra.TensorProduct.includeLeftRingHom (R := R) (B := B)).comp e.symm.toRingHom
        commutes' := fun r => by simp [RingHom.algebraMap_toAlgebra, hes r] }
      { __ := (Algebra.TensorProduct.includeRight (R := R)
          (A := p.ResidueField) (B := B)).toRingHom
        commutes' := fun r => by simp [RingHom.algebraMap_toAlgebra, ← hmap' r] }
      fun _ _ => Commute.all _ _).toRingHom
  have hF : ∀ (x : p.ResidueField) (b : B), F (x ⊗ₜ[R] b) = e x ⊗ₜ[R'] b := fun x b => by
    change e x ⊗ₜ[R'] (1 : B) * ((1 : p'.ResidueField) ⊗ₜ[R'] b) = e x ⊗ₜ[R'] b
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hG : ∀ (y : p'.ResidueField) (b : B), G (y ⊗ₜ[R'] b) = e.symm y ⊗ₜ[R] b := fun y b => by
    change e.symm y ⊗ₜ[R] (1 : B) * ((1 : p.ResidueField) ⊗ₜ[R] b) = e.symm y ⊗ₜ[R] b
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  { toFun := F
    invFun := G
    left_inv := fun x => by
      refine TensorProduct.induction_on x (by simp) (fun x b => ?_) (fun y z hy hz => ?_)
      · rw [hF, hG, RingEquiv.symm_apply_apply]
      · rw [map_add, map_add, hy, hz]
    right_inv := fun y => by
      refine TensorProduct.induction_on y (by simp) (fun y b => ?_) (fun u v hu hv => ?_)
      · rw [hG, hF, RingEquiv.apply_symm_apply]
      · rw [map_add, map_add, hu, hv]
    map_mul' := map_mul F
    map_add' := map_add F }

/-- `Ideal.fiberRingEquivOfRingEquiv` on a generator. -/
@[simp]
public lemma Ideal.fiberRingEquivOfRingEquiv_tmul {R : Type u} [CommRing R]
    {R' : Type u'} [CommRing R'] {B : Type v} [CommRing B] [Algebra R B] [Algebra R' B]
    (eR : R ≃+* R') (hmap : ∀ r : R, algebraMap R' B (eR r) = algebraMap R B r)
    (p : Ideal R) [p.IsPrime] (p' : Ideal R') [p'.IsPrime] (hp : p = p'.comap eR.toRingHom)
    (x : p.ResidueField) (b : B) :
    Ideal.fiberRingEquivOfRingEquiv eR hmap p p' hp (x ⊗ₜ[R] b)
      = (Ideal.residueFieldRingEquivOfRingEquiv eR p p' hp x) ⊗ₜ[R'] b := by
  show Ideal.residueFieldRingEquivOfRingEquiv eR p p' hp x ⊗ₜ[R'] (1 : B) *
      ((1 : p'.ResidueField) ⊗ₜ[R'] b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- `Ideal.fiberRingEquivOfRingEquiv` is the identity on the image of the algebra, so it is an
isomorphism of `B`-algebras for the `Algebra.TensorProduct.rightAlgebra` structures. -/
public lemma Ideal.fiberRingEquivOfRingEquiv_includeRight {R : Type u} [CommRing R]
    {R' : Type u'} [CommRing R'] {B : Type v} [CommRing B] [Algebra R B] [Algebra R' B]
    (eR : R ≃+* R') (hmap : ∀ r : R, algebraMap R' B (eR r) = algebraMap R B r)
    (p : Ideal R) [p.IsPrime] (p' : Ideal R') [p'.IsPrime] (hp : p = p'.comap eR.toRingHom)
    (b : B) :
    Ideal.fiberRingEquivOfRingEquiv eR hmap p p' hp
        (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField) b)
      = Algebra.TensorProduct.includeRight (R := R') (A := p'.ResidueField) b := by
  rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply,
    Ideal.fiberRingEquivOfRingEquiv_tmul, map_one]

/-! ### The fibre module under a change of base ring -/

/-- An isomorphism of `B`-algebras, presented as a ring isomorphism commuting with the two
structure maps, read as a `B`-linear equivalence. -/
public noncomputable def RingEquiv.toLinearEquivOfAlgebraMap {B : Type u} [CommRing B]
    {T : Type v} [CommRing T] [Algebra B T] {T' : Type v'} [CommRing T'] [Algebra B T']
    (Φ : T ≃+* T') (hΦ : ∀ b : B, Φ (algebraMap B T b) = algebraMap B T' b) : T ≃ₗ[B] T' :=
  AddEquiv.toLinearEquiv Φ.toAddEquiv fun b t => by
    change Φ (b • t) = b • Φ t
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hΦ]

/-- Tensoring an isomorphism of `B`-algebras with a `B`-module. This is how the fibre module of a
complete dévissage, `κ(p) ⊗[R] B ⊗[B] M`, follows the fibre ring across a change of base ring. -/
public noncomputable def TensorProduct.congrRingEquiv {B : Type u} [CommRing B] {T : Type v}
    [CommRing T] [Algebra B T] {T' : Type v'} [CommRing T'] [Algebra B T'] (Φ : T ≃+* T')
    (hΦ : ∀ b : B, Φ (algebraMap B T b) = algebraMap B T' b) (M : Type w) [AddCommGroup M]
    [Module B M] : TensorProduct B T M ≃+ TensorProduct B T' M :=
  (TensorProduct.congr (Φ.toLinearEquivOfAlgebraMap hΦ) (LinearEquiv.refl B M)).toAddEquiv

/-- `TensorProduct.congrRingEquiv` on a generator. -/
@[simp]
public lemma TensorProduct.congrRingEquiv_tmul {B : Type u} [CommRing B] {T : Type v}
    [CommRing T] [Algebra B T] {T' : Type v'} [CommRing T'] [Algebra B T'] (Φ : T ≃+* T')
    (hΦ : ∀ b : B, Φ (algebraMap B T b) = algebraMap B T' b) (M : Type w) [AddCommGroup M]
    [Module B M] (t : T) (m : M) :
    TensorProduct.congrRingEquiv Φ hΦ M (t ⊗ₜ[B] m) = Φ t ⊗ₜ[B] m := rfl

/-- `TensorProduct.congrRingEquiv` is semilinear over `Φ`: this is the compatibility that
`Module.support_eq_comap_preimage` and `topologicalKrullDimAt_support_eq` consume, and which
neither `TensorProduct.congr` nor `LinearEquiv` states, both being linear over `B` alone. -/
public lemma TensorProduct.congrRingEquiv_smul {B : Type u} [CommRing B] {T : Type v}
    [CommRing T] [Algebra B T] {T' : Type v'} [CommRing T'] [Algebra B T'] (Φ : T ≃+* T')
    (hΦ : ∀ b : B, Φ (algebraMap B T b) = algebraMap B T' b) (M : Type w) [AddCommGroup M]
    [Module B M] (t : T) (x : TensorProduct B T M) :
    TensorProduct.congrRingEquiv Φ hΦ M (t • x)
      = Φ t • TensorProduct.congrRingEquiv Φ hΦ M x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t₀ m =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.congrRingEquiv_tmul,
        TensorProduct.congrRingEquiv_tmul, map_mul, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-! ### Support and local dimension under a change of base ring -/

/-- The Krull dimension of a subspace at a point does not depend on which of two equal
descriptions of the subspace is used. -/
public theorem topologicalKrullDimAt_congr_set {X : Type*} [TopologicalSpace X] {s t : Set X}
    (h : s = t) (x : X) (hs : x ∈ s) (ht : x ∈ t) :
    topologicalKrullDimAt ↥s ⟨x, hs⟩ = topologicalKrullDimAt ↥t ⟨x, ht⟩ := by
  subst h
  rfl

/-- The Krull dimension of a subspace does not depend on which of two equal descriptions of the
subspace is used. -/
public theorem topologicalKrullDim_congr_set {X : Type*} [TopologicalSpace X] {s t : Set X}
    (h : s = t) : topologicalKrullDim ↥s = topologicalKrullDim ↥t := by
  subst h
  rfl

/-- **The support of a module under an isomorphism of the base ring.** If `e : T ≃+* T'` and
`g : M ≃+ M'` satisfy `g (t • m) = e t • g m`, then the support of `M'` is the preimage of the
support of `M` under `PrimeSpectrum.comap e`. The proof is `Module.notMem_support_iff'`, which
describes non-membership by a scalar outside the prime killing each element. -/
public theorem Module.support_eq_comap_preimage {T : Type u} [CommRing T] {T' : Type u'}
    [CommRing T'] (e : T ≃+* T') {M : Type v} [AddCommGroup M] [Module T M] {M' : Type v'}
    [AddCommGroup M'] [Module T' M'] (g : M ≃+ M')
    (hg : ∀ (t : T) (m : M), g (t • m) = e t • g m) :
    Module.support T' M' = PrimeSpectrum.comap e.toRingHom ⁻¹' Module.support T M := by
  ext p'
  rw [Set.mem_preimage, ← not_iff_not, Module.notMem_support_iff', Module.notMem_support_iff']
  have hiff : ∀ t : T, t ∈ (PrimeSpectrum.comap e.toRingHom p').asIdeal ↔ e t ∈ p'.asIdeal :=
    fun _ => Iff.rfl
  constructor
  · intro h m
    obtain ⟨t', ht', hm⟩ := h (g m)
    refine ⟨e.symm t', fun hmem => ht' ?_, g.injective ?_⟩
    · rwa [hiff, e.apply_symm_apply] at hmem
    · rw [hg, e.apply_symm_apply, hm, map_zero]
  · intro h m'
    obtain ⟨t, ht, hm⟩ := h (g.symm m')
    refine ⟨e t, fun hmem => ht ((hiff t).mpr hmem), ?_⟩
    have hz := congrArg g hm
    rwa [hg, g.apply_symm_apply, map_zero] at hz

/-- **The local dimension of the support of a module under an isomorphism of the base ring.**
`PrimeSpectrum.homeomorphOfRingEquiv` restricts to a homeomorphism of the two supports by
`Module.support_eq_comap_preimage`, and the dimension at a point is a homeomorphism invariant. -/
public theorem topologicalKrullDimAt_support_eq {T : Type u} [CommRing T] {T' : Type u'}
    [CommRing T'] (e : T ≃+* T') {M : Type v} [AddCommGroup M] [Module T M] {M' : Type v'}
    [AddCommGroup M'] [Module T' M'] (g : M ≃+ M')
    (hg : ∀ (t : T) (m : M), g (t • m) = e t • g m)
    {p : PrimeSpectrum T} (hp : p ∈ Module.support T M)
    {p' : PrimeSpectrum T'} (hp' : p' ∈ Module.support T' M')
    (hpp' : PrimeSpectrum.comap e.toRingHom p' = p) :
    topologicalKrullDimAt ↥(Module.support T M) ⟨p, hp⟩
      = topologicalKrullDimAt ↥(Module.support T' M') ⟨p', hp'⟩ := by
  have hset := Module.support_eq_comap_preimage e g hg
  have hcancel : ∀ x : PrimeSpectrum T,
      PrimeSpectrum.comap e.toRingHom (PrimeSpectrum.comap e.symm.toRingHom x) = x :=
    fun x => (PrimeSpectrum.homeomorphOfRingEquiv e).symm_apply_apply x
  have hcond : ∀ x : PrimeSpectrum T,
      x ∈ Module.support T M ↔
        (PrimeSpectrum.homeomorphOfRingEquiv e x) ∈ Module.support T' M' := by
    intro x
    rw [hset, Set.mem_preimage]
    exact (iff_of_eq (congrArg _ (hcancel x))).symm
  have hpt : PrimeSpectrum.homeomorphOfRingEquiv e p = p' := by
    have hinj : Function.Injective (PrimeSpectrum.comap e.toRingHom) :=
      (PrimeSpectrum.homeomorphOfRingEquiv e).symm.injective
    exact hinj ((hcancel p).trans hpp'.symm)
  rw [topologicalKrullDimAt_eq_of_homeomorph
    (Homeomorph.subtype (PrimeSpectrum.homeomorphOfRingEquiv e) hcond) ⟨p, hp⟩]
  congr 1
  exact Subtype.ext hpt

/-! ### Relative dimension under a change of base ring -/

/-- The fibre of `Spec B → Spec R'` over `p'` is the fibre of `Spec B → Spec R` over the
contracted prime. -/
private theorem preimage_singleton_comap_eq {R : Type u} [CommRing R]
    {R' : Type u'} [CommRing R'] {B : Type v} [CommRing B] [Algebra R B] [Algebra R' B]
    (eR : R ≃+* R') (hmap : ∀ x : R, algebraMap R' B (eR x) = algebraMap R B x)
    (p' : PrimeSpectrum R') :
    PrimeSpectrum.comap (algebraMap R' B) ⁻¹' {p'}
      = PrimeSpectrum.comap (algebraMap R B) ⁻¹' {PrimeSpectrum.comap eR.toRingHom p'} := by
  have h1 : (algebraMap R' B).comp eR.toRingHom = algebraMap R B := RingHom.ext hmap
  have hinj := PrimeSpectrum.comap_injective_of_surjective eR.toRingHom eR.surjective
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  rw [← h1, PrimeSpectrum.comap_comp_apply]
  exact ⟨fun h => congrArg _ h, fun h => hinj h⟩

/-- **The relative dimension at a prime is unchanged by a change of base ring along an
isomorphism.** `Algebra.relativeDimensionAt` is the local dimension of the subspace
`comap (algebraMap R B) ⁻¹' {p}` of `Spec B` at `q`, and that subspace is literally the same set
for `R` and for `R'`, because `comap (algebraMap R' B)` is `comap eR.symm` composed with
`comap (algebraMap R B)` and `comap eR.symm` is injective. -/
public theorem Algebra.relativeDimensionAt_eq_of_ringEquiv {R : Type u} [CommRing R]
    {R' : Type u'} [CommRing R'] {B : Type v} [CommRing B] [Algebra R B] [Algebra R' B]
    (eR : R ≃+* R') (hmap : ∀ x : R, algebraMap R' B (eR x) = algebraMap R B x)
    (q : Ideal B) [q.IsPrime] :
    Algebra.relativeDimensionAt R' q = Algebra.relativeDimensionAt R q := by
  have hset := preimage_singleton_comap_eq eR hmap
    (PrimeSpectrum.comap (algebraMap R' B) ⟨q, ‹_›⟩)
  rw [← PrimeSpectrum.comap_comp_apply, (RingHom.ext hmap : (algebraMap R' B).comp eR.toRingHom
    = algebraMap R B)] at hset
  exact topologicalKrullDimAt_congr_set hset _ rfl rfl

/-- **The fibre of `Spec B → Spec R'` over a prime is, as a subspace of `Spec B`, the fibre of
`Spec B → Spec R` over the contracted prime.** The two structure maps differ by the isomorphism
`eR` of the base, so the two conditions cutting out the fibre differ by the bijection
`PrimeSpectrum.comap eR`. -/
public theorem PrimeSpectrum.comap_preimage_singleton_eq_of_ringEquiv {R : Type u} [CommRing R]
    {R' : Type u'} [CommRing R'] {B : Type v} [CommRing B] [Algebra R B] [Algebra R' B]
    (eR : R ≃+* R') (hmap : ∀ x : R, algebraMap R' B (eR x) = algebraMap R B x)
    (p' : PrimeSpectrum R') :
    PrimeSpectrum.comap (algebraMap R' B) ⁻¹' {p'}
      = PrimeSpectrum.comap (algebraMap R B) ⁻¹' {PrimeSpectrum.comap eR.toRingHom p'} :=
  preimage_singleton_comap_eq eR hmap p'

/-- **The relative dimension is unchanged by a change of base ring along an isomorphism**, being
the supremum of `Algebra.relativeDimensionAt R' q` over the primes `q` of `B`, which does not
move. -/
public theorem Algebra.relativeDimension_eq_of_ringEquiv {R : Type u} [CommRing R]
    {R' : Type u'} [CommRing R'] {B : Type v} [CommRing B] [Algebra R B] [Algebra R' B]
    (eR : R ≃+* R') (hmap : ∀ x : R, algebraMap R' B (eR x) = algebraMap R B x) :
    Algebra.relativeDimension R' B = Algebra.relativeDimension R B :=
  iSup_congr fun Q => Algebra.relativeDimensionAt_eq_of_ringEquiv eR hmap Q.asIdeal

/-! ### The fibre support of a complete dévissage under a change of base ring -/

section Fiber

variable {R : Type u} [CommRing R] {R' : Type u'} [CommRing R'] {B : Type v} [CommRing B]
  [Algebra R B] [Algebra R' B] (eR : R ≃+* R')
  (hmap : ∀ x : R, algebraMap R' B (eR x) = algebraMap R B x)
  (p : Ideal R) [p.IsPrime] (p' : Ideal R') [p'.IsPrime] (hp : p = p'.comap eR.toRingHom)

/-- The point of the fibre ring cut out by a prime `lp` of `B` over `p` is carried to the point
cut out by `lp` over `p'` by `Ideal.fiberRingEquivOfRingEquiv`. Both points contract to `lp`
along `Algebra.TensorProduct.includeRight`, which is the inverse of
`PrimeSpectrum.primesOverOrderIsoFiber`, and the isomorphism of fibre rings commutes with
`includeRight`. -/
public theorem fiber_point_comap_eq (lp : Ideal B) (hlp : lp ∈ p.primesOver B)
    (hlp' : lp ∈ p'.primesOver B) :
    PrimeSpectrum.comap (Ideal.fiberRingEquivOfRingEquiv eR hmap p p' hp).toRingHom
        (PrimeSpectrum.primesOverOrderIsoFiber R' B p' ⟨lp, hlp'⟩)
      = PrimeSpectrum.primesOverOrderIsoFiber R B p ⟨lp, hlp⟩ := by
  set Φ := Ideal.fiberRingEquivOfRingEquiv eR hmap p p' hp with hΦdef
  set iso := PrimeSpectrum.primesOverOrderIsoFiber R B p with hiso
  set iso' := PrimeSpectrum.primesOverOrderIsoFiber R' B p' with hiso'
  have key : ((iso.symm (PrimeSpectrum.comap Φ.toRingHom (iso' ⟨lp, hlp'⟩))) : Ideal B) = lp := by
    have hrhs : ((iso'.symm (iso' ⟨lp, hlp'⟩)) : Ideal B) = lp := by
      rw [iso'.symm_apply_apply]
    refine Eq.trans (Ideal.ext fun x => ?_) hrhs
    show Φ (Algebra.TensorProduct.includeRight x) ∈ (iso' ⟨lp, hlp'⟩).asIdeal ↔ _
    rw [hΦdef, Ideal.fiberRingEquivOfRingEquiv_includeRight]
    exact Iff.rfl
  have hsub : iso.symm (PrimeSpectrum.comap Φ.toRingHom (iso' ⟨lp, hlp'⟩)) = ⟨lp, hlp⟩ :=
    Subtype.ext key
  have hmain := congrArg iso hsub
  rwa [iso.apply_symm_apply] at hmain

include eR hmap hp in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **The support condition of a pointed complete dévissage under a change of base ring.** The
point of the fibre belongs to the support of the fibre module for `p` if and only if it does
for `p'`, by `Module.support_eq_comap_preimage` along `Ideal.fiberRingEquivOfRingEquiv`. -/
public theorem mem_support_fiber_iff (M : Type w) [AddCommGroup M] [Module B M] (lp : Ideal B)
    (hlp : lp ∈ p.primesOver B) (hlp' : lp ∈ p'.primesOver B) :
    PrimeSpectrum.primesOverOrderIsoFiber R B p ⟨lp, hlp⟩ ∈
        Module.support (p.Fiber B) (TensorProduct B (p.Fiber B) M) ↔
      PrimeSpectrum.primesOverOrderIsoFiber R' B p' ⟨lp, hlp'⟩ ∈
        Module.support (p'.Fiber B) (TensorProduct B (p'.Fiber B) M) := by
  have hΦ : ∀ b : B, Ideal.fiberRingEquivOfRingEquiv eR hmap p p' hp
      (algebraMap B (p.Fiber B) b) = algebraMap B (p'.Fiber B) b := fun b =>
    Ideal.fiberRingEquivOfRingEquiv_includeRight eR hmap p p' hp b
  rw [Module.support_eq_comap_preimage (Ideal.fiberRingEquivOfRingEquiv eR hmap p p' hp)
      (TensorProduct.congrRingEquiv _ hΦ M) (TensorProduct.congrRingEquiv_smul _ hΦ M),
    Set.mem_preimage, fiber_point_comap_eq eR hmap p p' hp lp hlp hlp']

include eR hmap hp in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **The dimension condition of a pointed complete dévissage under a change of base ring.** The
local dimension of the support of the fibre module at the point of the fibre is the same for `p`
and for `p'`. -/
public theorem topologicalKrullDimAt_support_fiber_eq (M : Type w) [AddCommGroup M] [Module B M]
    (lp : Ideal B) (hlp : lp ∈ p.primesOver B) (hlp' : lp ∈ p'.primesOver B)
    (hmem : PrimeSpectrum.primesOverOrderIsoFiber R B p ⟨lp, hlp⟩ ∈
      Module.support (p.Fiber B) (TensorProduct B (p.Fiber B) M))
    (hmem' : PrimeSpectrum.primesOverOrderIsoFiber R' B p' ⟨lp, hlp'⟩ ∈
      Module.support (p'.Fiber B) (TensorProduct B (p'.Fiber B) M)) :
    topologicalKrullDimAt ↥(Module.support (p.Fiber B) (TensorProduct B (p.Fiber B) M))
        ⟨PrimeSpectrum.primesOverOrderIsoFiber R B p ⟨lp, hlp⟩, hmem⟩
      = topologicalKrullDimAt ↥(Module.support (p'.Fiber B) (TensorProduct B (p'.Fiber B) M))
        ⟨PrimeSpectrum.primesOverOrderIsoFiber R' B p' ⟨lp, hlp'⟩, hmem'⟩ := by
  have hΦ : ∀ b : B, Ideal.fiberRingEquivOfRingEquiv eR hmap p p' hp
      (algebraMap B (p.Fiber B) b) = algebraMap B (p'.Fiber B) b := fun b =>
    Ideal.fiberRingEquivOfRingEquiv_includeRight eR hmap p p' hp b
  exact topologicalKrullDimAt_support_eq _ (TensorProduct.congrRingEquiv _ hΦ M)
    (TensorProduct.congrRingEquiv_smul _ hΦ M) hmem hmem'
    (fiber_point_comap_eq eR hmap p p' hp lp hlp hlp')

end Fiber

/-! ### The transport of a complete dévissage -/

namespace Module

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
  {R' : Type u} {S' : Type v} {N' : Type w} [CommRing R'] [CommRing S'] [Algebra R' S']
  [Algebra.FiniteType R' S'] [AddCommGroup N'] [Module S' N'] [Module.Finite S' N']

/-- **A complete dévissage transported along isomorphisms of the data (Stacks 05HX).** Let
`eR : R ≃+* R'`, `eS : S ≃+* S'` and `eN : N ≃+ N'` intertwine the structure map `R → S` and the
action of `S` on `N`, and let `r` and `r'` be primes corresponding under `eR`. A complete
dévissage of `N/S/R` over `r` becomes one of `N'/S'/R'` over `r'`.

The whole stage diagram is reused: the stage algebras and modules, the maps between them and the
maps `alpha i` are literally the old ones, only the `R'`-algebra structures being new. -/
@[reducible] public noncomputable def CompleteDevissage.ofRingEquiv
    (eR : R ≃+* R') (eS : S ≃+* S') (eN : N ≃+ N')
    (halg : ∀ x : R, algebraMap R' S' (eR x) = eS (algebraMap R S x))
    (hsmul : ∀ (s : S) (n : N), eN (s • n) = eS s • eN n)
    {r : Ideal R} [r.IsPrime] {r' : Ideal R'} [r'.IsPrime]
    (hr : r = Ideal.comap eR.toRingHom r')
    (D : CompleteDevissage R S N r) : CompleteDevissage R' S' N' r' := by
  letI instA : ∀ i, Algebra R' (D.A i) :=
    fun i => ((algebraMap R (D.A i)).comp eR.symm.toRingHom).toAlgebra
  letI instB : ∀ i, Algebra R' (D.B i) :=
    fun i => ((algebraMap R (D.B i)).comp eR.symm.toRingHom).toAlgebra
  have hSinv : ∀ y : R', eS.symm (algebraMap R' S' y) = algebraMap R S (eR.symm y) := by
    intro y
    have hy := halg (eR.symm y)
    rw [eR.apply_symm_apply] at hy
    rw [hy, eS.symm_apply_apply]
  have hAmap : ∀ (i) (y : R'), algebraMap R' (D.A i) y = algebraMap R (D.A i) (eR.symm y) :=
    fun _ _ => rfl
  have hBmap : ∀ (i) (y : R'), algebraMap R' (D.B i) y = algebraMap R (D.B i) (eR.symm y) :=
    fun _ _ => rfl
  letI modB : ∀ i, Module (D.B i) (D.M i) :=
    fun i => Module.compHom (D.M i) (D.toLeft i).toRingHom
  let toA0' : S' →ₐ[R'] D.A 0 :=
    AlgHom.mk (D.toA₀.toRingHom.comp eS.symm.toRingHom) (fun y => by
      change D.toA₀ (eS.symm (algebraMap R' S' y)) = algebraMap R' (D.A 0) y
      rw [hSinv y, hAmap]
      exact D.toA₀.commutes _)
  letI mod0D : Module S (D.M 0) := Module.compHom (D.M 0) D.toA₀.toRingHom
  letI mod0 : Module S' (D.M 0) := Module.compHom (D.M 0) toA0'.toRingHom
  have hmapr : ∀ {A : Type u} [CommRing A] (f : R →+* A),
      Ideal.map (f.comp eR.symm.toRingHom) r' = Ideal.map f r := by
    intro A _ f
    rw [← Ideal.map_map, hr]
    exact congrArg (Ideal.map f) (Ideal.map_symm eR)
  exact
    { stepCount := D.stepCount
      A := D.A
      B := D.B
      M := D.M
      commRingA := D.commRingA
      commRingB := D.commRingB
      algebraRA := instA
      algebraRB := instB
      addCommGroupM := D.addCommGroupM
      moduleAM := D.moduleAM
      toA₀ := toA0'
      toLeft := fun i => AlgHom.mk (D.toLeft i).toRingHom (fun y => by
        rw [hAmap, hBmap]
        exact (D.toLeft i).commutes _)
      toRight := fun i => AlgHom.mk (D.toRight i).toRingHom (fun y => by
        rw [hAmap, hBmap]
        exact (D.toRight i).commutes _)
      multiplicity := D.multiplicity
      alpha := D.alpha
      finiteM := D.finiteM
      initial_surjective := D.initial_surjective.comp eS.symm.surjective
      initial_finitePresentation :=
        RingHom.FinitePresentation.comp D.initial_finitePresentation eS.symm.finitePresentation
      transition_surjective := D.transition_surjective
      transition_finitePresentation := D.transition_finitePresentation
      left_finite := D.left_finite
      smooth := fun i => by
        refine RingHom.smooth_algebraMap.mp ?_
        have hc : (algebraMap R' (D.B i)) = (algebraMap R (D.B i)).comp eR.symm.toRingHom := rfl
        rw [hc]
        exact RingHom.Smooth.comp (RingHom.Smooth.of_bijective eR.symm.bijective)
          (RingHom.smooth_algebraMap.mpr (D.smooth i))
      geometricallyIrreducibleFibers := fun i => by
        have hc : (algebraMap R' (D.B i)) = (algebraMap R (D.B i)).comp eR.symm.toRingHom := rfl
        have hiso : IsIso (CommRingCat.ofHom eR.symm.toRingHom) :=
          (ConcreteCategory.isIso_iff_bijective _).mpr eR.symm.bijective
        rw [hc, CommRingCat.ofHom_comp, Spec.map_comp]
        exact GeometricallyIrreducible.postcomp _ _
      initialEquiv := AddEquiv.toLinearEquiv (eN.symm.trans D.initialEquiv.toAddEquiv)
        (fun c x => by
          have h1 : eN.symm (c • x) = eS.symm c • eN.symm x := by
            refine eN.injective ?_
            rw [hsmul, eN.apply_symm_apply, eN.apply_symm_apply, eS.apply_symm_apply]
          change D.initialEquiv (eN.symm (c • x)) = _
          rw [h1]
          exact D.initialEquiv.map_smul _ _)
      cokerEquiv := D.cokerEquiv
      map_isPrime := fun i => by
        have hc : Ideal.map (algebraMap R' (D.B i)) r' = Ideal.map (algebraMap R (D.B i)) r :=
          hmapr (algebraMap R (D.B i))
        rw [hc]
        exact D.map_isPrime i
      fiber_bijective := fun i =>
        bijective_baseChange_congr (J := Ideal.map (algebraMap R (D.B i)) r)
          (hmapr (algebraMap R (D.B i))) _ (D.map_isPrime i) _ (D.fiber_bijective i)
      final_surjective := D.final_surjective }

/-- **A pointed complete dévissage transported along isomorphisms of the data (Stacks 05HZ).**
With the data of `Module.CompleteDevissage.ofRingEquiv` and primes `q`, `q'` of `S`, `S'`
corresponding under `eS`, a nonempty complete dévissage of `N/S/R` at `q` becomes one of
`N'/S'/R'` at `q'`.

The stage primes are literally the old ones, being primes of the unchanged stage algebras. What
the change of base ring touches is the residue field of the prime below, where pure transcendence
moves by `PurelyTranscendental.of_ringEquiv_base`, and the fibre ring, where the support and
dimension conditions move by `mem_support_fiber_iff` and
`topologicalKrullDimAt_support_fiber_eq`. -/
public noncomputable def NonemptyCompleteDevissageAt.ofRingEquiv
    (eR : R ≃+* R') (eS : S ≃+* S') (eN : N ≃+ N')
    (halg : ∀ x : R, algebraMap R' S' (eR x) = eS (algebraMap R S x))
    (hsmul : ∀ (s : S) (n : N), eN (s • n) = eS s • eN n)
    {q : Ideal S} [q.IsPrime] {q' : Ideal S'} [q'.IsPrime]
    (hq : q = Ideal.comap eS.toRingHom q')
    (D : NonemptyCompleteDevissageAt R S N q) :
    NonemptyCompleteDevissageAt R' S' N' q' := by
  have hr : q.under R = Ideal.comap eR.toRingHom (q'.under R') := by
    have hcomp : (algebraMap R' S').comp eR.toRingHom = eS.toRingHom.comp (algebraMap R S) :=
      RingHom.ext halg
    calc q.under R = Ideal.comap (algebraMap R S) (Ideal.comap eS.toRingHom q') := by rw [← hq]
      _ = Ideal.comap (eS.toRingHom.comp (algebraMap R S)) q' := Ideal.comap_comap _ _
      _ = Ideal.comap ((algebraMap R' S').comp eR.toRingHom) q' := by rw [hcomp]
      _ = Ideal.comap eR.toRingHom (q'.under R') := (Ideal.comap_comap _ _).symm
  have hRcancel : ∀ I : Ideal R',
      Ideal.comap eR.symm.toRingHom (Ideal.comap eR.toRingHom I) = I := by
    intro I
    have hid : eR.toRingHom.comp eR.symm.toRingHom = RingHom.id R' :=
      RingHom.ext fun y => eR.apply_symm_apply y
    rw [Ideal.comap_comap, hid, Ideal.comap_id]
  have hScancel : ∀ I : Ideal S',
      Ideal.comap eS.symm.toRingHom (Ideal.comap eS.toRingHom I) = I := by
    intro I
    have hid : eS.toRingHom.comp eS.symm.toRingHom = RingHom.id S' :=
      RingHom.ext fun y => eS.apply_symm_apply y
    rw [Ideal.comap_comap, hid, Ideal.comap_id]
  let C := D.toCompleteDevissage
  let Dc := C.ofRingEquiv eR eS eN halg hsmul hr
  letI modB : ∀ i : Fin (C.stepCount + 1), Module (C.B i) (C.M i) :=
    fun i => Module.compHom (C.M i) (C.toLeft i).toRingHom
  letI algR' : ∀ i : Fin (C.stepCount + 1), Algebra R' (C.B i) :=
    fun i => inferInstanceAs (Algebra R' (Dc.B i))
  have hBmap : ∀ (i : Fin (C.stepCount + 1)) (x : R),
      algebraMap R' (C.B i) (eR x) = algebraMap R (C.B i) x := by
    intro i x
    change algebraMap R (C.B i) (eR.symm (eR x)) = _
    rw [eR.symm_apply_apply]
  have hliesOver : ∀ i : Fin (C.stepCount + 1),
      @Ideal.LiesOver R' _ (Dc.B i) _ _ (D.lowerPrime i) (q'.under R') := by
    intro i
    refine ⟨?_⟩
    have hunder : @Ideal.under R' _ (Dc.B i) _ _ (D.lowerPrime i)
        = Ideal.comap eR.symm.toRingHom ((D.lowerPrime i).under R) :=
      (Ideal.comap_comap _ _).symm
    rw [hunder, ← (D.lowerPrime_liesOver i).over, hr, hRcancel]
  exact
    { toCompleteDevissage := Dc
      lowerPrime := D.lowerPrime
      lowerPrime_isPrime := D.lowerPrime_isPrime
      lowerPrime_liesOver := hliesOver
      residueField_purelyTranscendental := fun i => by
        let _ : (D.lowerPrime i).IsPrime := D.lowerPrime_isPrime i
        let alg : Algebra (q.under R).ResidueField (D.lowerPrime i).ResidueField :=
          (Ideal.ResidueField.mapₐ (q.under R) (D.lowerPrime i)
            (Algebra.ofId R (C.B i))
            (D.lowerPrime_liesOver i).over).toRingHom.toAlgebra
        let alg' : Algebra (q'.under R').ResidueField (D.lowerPrime i).ResidueField :=
          (Ideal.ResidueField.mapₐ (q'.under R') (D.lowerPrime i)
            (Algebra.ofId R' (C.B i))
            (hliesOver i).over).toRingHom.toAlgebra
        have hpt : PurelyTranscendental (q.under R).ResidueField (D.lowerPrime i).ResidueField :=
          D.residueField_purelyTranscendental i
        refine PurelyTranscendental.of_ringEquiv_base
          (Ideal.residueFieldRingEquivOfRingEquiv eR (q.under R) (q'.under R') hr) ?_
        intro x
        have hhom : ((algebraMap (q'.under R').ResidueField (D.lowerPrime i).ResidueField).comp
            (Ideal.residueFieldRingEquivOfRingEquiv eR (q.under R) (q'.under R') hr).toRingHom)
            = algebraMap (q.under R).ResidueField (D.lowerPrime i).ResidueField := by
          refine Ideal.ResidueField.ringHom_ext (RingHom.ext fun y => ?_)
          simp only [RingHom.coe_comp, Function.comp_apply]
          change algebraMap (q'.under R').ResidueField (D.lowerPrime i).ResidueField
              (Ideal.residueFieldRingEquivOfRingEquiv eR (q.under R) (q'.under R') hr
                (algebraMap R (q.under R).ResidueField y)) = _
          rw [Ideal.residueFieldRingEquivOfRingEquiv_algebraMap]
          refine Eq.trans ?_ (Ideal.ResidueField.map_algebraMap (q.under R) (D.lowerPrime i)
            (Algebra.ofId R (C.B i)).toRingHom (D.lowerPrime_liesOver i).over y).symm
          refine Eq.trans (Ideal.ResidueField.map_algebraMap (q'.under R') (D.lowerPrime i)
            (Algebra.ofId R' (C.B i)).toRingHom (hliesOver i).over (eR y)) ?_
          exact congrArg (algebraMap (C.B i) (D.lowerPrime i).ResidueField) (hBmap i y)
        exact congrFun (congrArg (fun f : (q.under R).ResidueField →+*
          (D.lowerPrime i).ResidueField => (f : _ → _)) hhom) x
      upperPrime := D.upperPrime
      upperPrime_isPrime := D.upperPrime_isPrime
      upperPrime_under := D.upperPrime_under
      upperPrime_unique := D.upperPrime_unique
      initial_under := by
        have h1 : ∀ I : Ideal (C.A 0), Ideal.comap Dc.toA₀.toRingHom I
              = Ideal.comap eS.symm.toRingHom (Ideal.comap C.toA₀.toRingHom I) :=
          fun I => (Ideal.comap_comap _ _).symm
        rw [h1, D.initial_under, hq, hScancel]
      transition_under := D.transition_under
      lowerPrime_mem_fiberSupport := fun i =>
        (mem_support_fiber_iff eR (hBmap i) (q.under R) (q'.under R') hr
          (C.M i) (D.lowerPrime i)
          ⟨D.lowerPrime_isPrime i, D.lowerPrime_liesOver i⟩
          ⟨D.lowerPrime_isPrime i, hliesOver i⟩).mp (D.lowerPrime_mem_fiberSupport i)
      relativeDimension_eq_support := fun i => by
        rw [Algebra.relativeDimension_eq_of_ringEquiv eR (hBmap i),
          D.relativeDimension_eq_support i]
        exact topologicalKrullDimAt_support_fiber_eq eR (hBmap i) (q.under R) (q'.under R') hr
          (C.M i) (D.lowerPrime i) ⟨D.lowerPrime_isPrime i, D.lowerPrime_liesOver i⟩
          ⟨D.lowerPrime_isPrime i, hliesOver i⟩ _ _ }

/-- **A complete dévissage at a prime transported along isomorphisms of the data
(Stacks 05HZ).** The empty dévissage transports because `eN` carries a zero module to a zero
module; the nonempty one is `Module.NonemptyCompleteDevissageAt.ofRingEquiv`. -/
public noncomputable def CompleteDevissageAt.ofRingEquiv
    (eR : R ≃+* R') (eS : S ≃+* S') (eN : N ≃+ N')
    (halg : ∀ x : R, algebraMap R' S' (eR x) = eS (algebraMap R S x))
    (hsmul : ∀ (s : S) (n : N), eN (s • n) = eS s • eN n)
    {q : Ideal S} [q.IsPrime] {q' : Ideal S'} [q'.IsPrime]
    (hq : q = Ideal.comap eS.toRingHom q')
    (D : CompleteDevissageAt R S N q) : CompleteDevissageAt R' S' N' q' :=
  match D with
  | .empty hz => .empty (by have := hz; exact Function.Injective.subsingleton eN.symm.injective)
  | .nonempty data => .nonempty (data.ofRingEquiv eR eS eN halg hsmul hq)

/-- **The existence of a complete dévissage at a prime transported along isomorphisms of the
data.** This is the form a consumer applies: a hypothesis
`Nonempty (Module.CompleteDevissageAt R S N q)` obtained for one model of the data yields the
same statement for any other, so a dictionary proved for `Γ(Spec A, ⊤)`, `Γ(Spec B, ⊤)` and
`Γ(Ñ, ⊤)` can be read as a statement about `A`, `B` and `N`. -/
public theorem nonempty_completeDevissageAt_ofRingEquiv
    (eR : R ≃+* R') (eS : S ≃+* S') (eN : N ≃+ N')
    (halg : ∀ x : R, algebraMap R' S' (eR x) = eS (algebraMap R S x))
    (hsmul : ∀ (s : S) (n : N), eN (s • n) = eS s • eN n)
    {q : Ideal S} [q.IsPrime] {q' : Ideal S'} [q'.IsPrime]
    (hq : q = Ideal.comap eS.toRingHom q')
    (h : Nonempty (CompleteDevissageAt R S N q)) :
    Nonempty (CompleteDevissageAt R' S' N' q') :=
  h.elim fun D => ⟨D.ofRingEquiv eR eS eN halg hsmul hq⟩

end Module

end
