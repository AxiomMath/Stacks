module

public import StacksFrontier.RingTheory.Flat.DevissageQuotientBase

/-!
# The fibre ring of a dévissage stage under a surjective base change

`StacksFrontier.RingTheory.Flat.DevissageQuotientBase` analyses the base change of a complete
dévissage along a surjection `R → R ⧸ J` of the base with `J ⊆ r`, the base change the induction
step of Stacks 05PG performs when it replaces `A` by `A/J`, and
`StacksFrontier.RingTheory.Flat.DevissageQuotientBaseAssembly` assembles the *unpointed* dévissage
`Module.CompleteDevissage.quotientBase`. The two conditions of Stacks 05HZ that the *pointed*
dévissage still owes — the fibre-support condition and the dimension condition — both read the
fibre ring `κ(r) ⊗_R Bᵢ` of a stage, and both transport along an identification of that fibre ring
with the fibre ring of the base-changed stage. This file supplies that identification.

## The identification

For `J ⊆ r` the residue field of `r` does not move: `R → R ⧸ J` is surjective, hence surjective on
stalks, so `κ(r) ≅ κ(r/J)` (`Stacks.Flatness.quotResidueFieldEquiv`). Consequently

`κ(r) ⊗_R Bᵢ  ≅  κ(r/J) ⊗_{R/J} (Bᵢ/JBᵢ)`,

the two maps being built from the two factors in either direction. The forward map is the
identification of residue fields on the left and the quotient map `Bᵢ → Bᵢ/JBᵢ` on the right. The
backward map is the inverse identification on the left and, on the right, the quotient map of
`Bᵢ → κ(r) ⊗_R Bᵢ`, which kills `JBᵢ` because `J ⊆ r` kills `J` in `κ(r)`
(`Stacks.Flatness.quotIncludeRight`). Both are identities on the image of `Bᵢ`, which is what makes
the identification one of `Bᵢ`-algebras and so lets the fibre *module* follow it.

## Main definitions

* `Stacks.Flatness.tensorProductDescOfCompat`: a ring homomorphism out of `K ⊗_R B` built from
  compatible ring homomorphisms on the two factors, the target being an algebra over an
  `R`-algebra `R'` rather than over `R`. This is what lets both directions be written without
  naming the `R`-algebra structure of the target, which is a composite in both cases.
* `Stacks.Flatness.quotResidueFieldEquiv`: the identification `κ(r) ≅ κ(r/J)` for `J ⊆ r`.
* `Stacks.Flatness.quotIncludeRight`: the map `B ⧸ JB → κ(r) ⊗_R B` induced by
  `Algebra.TensorProduct.includeRight`.
* `Stacks.Flatness.quotFiberRingEquiv`: **the identification of fibre rings**
  `κ(r) ⊗_R B ≅ κ(r/J) ⊗_{R/J} (B/JB)`.

## Main results

* `Stacks.Flatness.quotFiberForward_tmul` and `Stacks.Flatness.quotFiberBackward_tmul_mk`: the two
  maps on generators.
* `Stacks.Flatness.quotFiberRingEquiv_includeRight`: the identification is the identity on the
  image of `B`, so it is an isomorphism of `B`-algebras for the
  `Algebra.TensorProduct.rightAlgebra` structures. This is the hypothesis `hΦ` of
  `Module.support_eq_comap_preimage` and `topologicalKrullDimAt_support_eq`.

## Implementation notes

`Stacks.Flatness.tensorProductDescOfCompat` exists because `Algebra.TensorProduct.lift` asks for
the target to be an algebra over the ring the tensor product is taken over, and in both directions
here that structure is a *composite* — `R → R/J → κ(r/J) ⊗_{R/J} (B/JB)` one way and
`R/J → κ(r) ⊗_R B` the other, the latter existing only because `J ⊆ r`. Carrying those structures
as `letI`s at the use site puts the instance `IsScalarTower R R C` that `lift` also asks for out of
reach of instance synthesis; stating the compatibility as a hypothesis about `algebraMap R' C`
instead keeps every instance of the statement a genuine one.

The two maps are not stated as `R`- or `R/J`-algebra homomorphisms but as plain ring
homomorphisms, for the same reason: an `AlgHom` would have to name one of those composite
structures in its type, and no consumer of the identification wants it.

## References

* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Stacks.Flatness

/-! ### A ring homomorphism out of a tensor product -/

/-- **A ring homomorphism out of `K ⊗_R B`** built from ring homomorphisms `f` on `K` and `g` on
`B` which agree on the image of `R`, the target being an algebra over an `R`-algebra `R'` and the
agreement being with `R → R' → C`.

`Algebra.TensorProduct.lift` asks instead for the target to carry an `R`-algebra structure, and
building that structure at the use site hides the instance `IsScalarTower R R C` that `lift` also
needs. Here the structure is built inside the definition and the compatibility is a hypothesis, so
every instance in the statement is a genuine one. -/
public noncomputable def tensorProductDescOfCompat {R : Type u} [CommRing R] {K : Type v}
    [CommRing K] [Algebra R K] {B : Type w} [CommRing B] [Algebra R B] {R' : Type*} [CommRing R']
    [Algebra R R'] {C : Type*} [CommRing C] [Algebra R' C] (f : K →+* C) (g : B →+* C)
    (hf : ∀ x : R, f (algebraMap R K x) = algebraMap R' C (algebraMap R R' x))
    (hg : ∀ x : R, g (algebraMap R B x) = algebraMap R' C (algebraMap R R' x)) :
    (K ⊗[R] B) →+* C := by
  letI : Algebra R C := ((algebraMap R' C).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R C := IsScalarTower.left R
  exact (Algebra.TensorProduct.lift (S := R)
    { __ := f, commutes' := fun x => hf x }
    { __ := g, commutes' := fun x => hg x }
    fun _ _ => Commute.all _ _).toRingHom

/-- `Stacks.Flatness.tensorProductDescOfCompat` on a generator. -/
public theorem tensorProductDescOfCompat_tmul {R : Type u} [CommRing R] {K : Type v} [CommRing K]
    [Algebra R K] {B : Type w} [CommRing B] [Algebra R B] {R' : Type*} [CommRing R']
    [Algebra R R'] {C : Type*} [CommRing C] [Algebra R' C] (f : K →+* C) (g : B →+* C)
    (hf : ∀ x : R, f (algebraMap R K x) = algebraMap R' C (algebraMap R R' x))
    (hg : ∀ x : R, g (algebraMap R B x) = algebraMap R' C (algebraMap R R' x))
    (x : K) (b : B) :
    tensorProductDescOfCompat f g hf hg (x ⊗ₜ[R] b) = f x * g b := rfl

/-! ### The residue field of a prime containing the ideal quotiented out -/

variable {R : Type u} [CommRing R]

/-- The structure map `R → R ⧸ J` is surjective. -/
public theorem surjective_algebraMap_quotient (J : Ideal R) :
    Function.Surjective (algebraMap R (R ⧸ J)) := by
  rw [Ideal.Quotient.algebraMap_eq]
  exact Ideal.Quotient.mk_surjective

/-- The kernel of the structure map `R → R ⧸ J` is `J`. -/
public theorem ker_algebraMap_quotient (J : Ideal R) :
    Ideal.comap (algebraMap R (R ⧸ J)) (⊥ : Ideal (R ⧸ J)) = J := by
  rw [Ideal.Quotient.algebraMap_eq]
  exact Ideal.mk_ker

/-- **A prime containing `J` is the contraction of its image in `R ⧸ J`.** -/
public theorem eq_comap_map_quotient (J r : Ideal R) (hJ : J ≤ r) :
    r = (Ideal.map (algebraMap R (R ⧸ J)) r).comap (algebraMap R (R ⧸ J)) := by
  rw [Ideal.comap_map_of_surjective _ (surjective_algebraMap_quotient J),
    ker_algebraMap_quotient J, sup_eq_left.mpr hJ]

/-- **The residue field of a prime containing `J` is unchanged in `R ⧸ J`.** A surjection is
surjective on stalks, and `RingHom.SurjectiveOnStalks.residueFieldMap_bijective` turns that into
bijectivity of the induced map of residue fields. -/
public noncomputable def quotResidueFieldEquiv (J r : Ideal R) [r.IsPrime]
    [(Ideal.map (algebraMap R (R ⧸ J)) r).IsPrime] (hJ : J ≤ r) :
    r.ResidueField ≃+* (Ideal.map (algebraMap R (R ⧸ J)) r).ResidueField :=
  RingEquiv.ofBijective
    (Ideal.ResidueField.map r (Ideal.map (algebraMap R (R ⧸ J)) r)
      (algebraMap R (R ⧸ J)) (eq_comap_map_quotient J r hJ))
    ((RingHom.surjectiveOnStalks_of_surjective
        (surjective_algebraMap_quotient J)).residueFieldMap_bijective _ _
      (eq_comap_map_quotient J r hJ))

/-- `Stacks.Flatness.quotResidueFieldEquiv` commutes with the two structure maps. -/
public theorem quotResidueFieldEquiv_algebraMap (J r : Ideal R) [r.IsPrime]
    [(Ideal.map (algebraMap R (R ⧸ J)) r).IsPrime] (hJ : J ≤ r) (x : R) :
    quotResidueFieldEquiv J r hJ (algebraMap R r.ResidueField x)
      = algebraMap (R ⧸ J) (Ideal.map (algebraMap R (R ⧸ J)) r).ResidueField
          (algebraMap R (R ⧸ J) x) :=
  Ideal.ResidueField.map_algebraMap _ _ _ _ x

/-- `Stacks.Flatness.quotResidueFieldEquiv` read backwards on the image of `R`. -/
public theorem quotResidueFieldEquiv_symm_algebraMap (J r : Ideal R) [r.IsPrime]
    [(Ideal.map (algebraMap R (R ⧸ J)) r).IsPrime] (hJ : J ≤ r) (x : R) :
    (quotResidueFieldEquiv J r hJ).symm
        (algebraMap (R ⧸ J) (Ideal.map (algebraMap R (R ⧸ J)) r).ResidueField
          (algebraMap R (R ⧸ J) x))
      = algebraMap R r.ResidueField x :=
  (quotResidueFieldEquiv J r hJ).injective (by
    rw [RingEquiv.apply_symm_apply, quotResidueFieldEquiv_algebraMap])

/-! ### The two structure maps of a quotient algebra -/

/-- The two routes from `R` to `B ⧸ JB` — through `B` and through `R ⧸ J` — agree. -/
public theorem algebraMap_quot_comp (J : Ideal R) (B : Type v) [CommRing B] [Algebra R B]
    (x : R) :
    algebraMap B (B ⧸ Ideal.map (algebraMap R B) J) (algebraMap R B x)
      = algebraMap (R ⧸ J) (B ⧸ Ideal.map (algebraMap R B) J) (algebraMap R (R ⧸ J) x) := by
  rw [Ideal.Quotient.algebraMap_eq (I := Ideal.map (algebraMap R B) J),
    Ideal.Quotient.algebraMap_eq (I := J),
    Ideal.Quotient.algebraMap_quotient_map_quotient]

/-- The structure map of the fibre ring factors through the residue field. -/
public theorem algebraMap_fiber_eq (r : Ideal R) [r.IsPrime] (B : Type v) [CommRing B]
    [Algebra R B] (x : R) :
    algebraMap R (r.Fiber B) x
      = Algebra.TensorProduct.includeLeftRingHom (algebraMap R r.ResidueField x) :=
  ((Algebra.TensorProduct.includeLeft (R := R) (A := r.ResidueField)
    (B := B) (S := R)).commutes x).symm

/-- **An ideal inside `r` dies in the fibre ring of `r`.** -/
public theorem algebraMap_fiber_eq_zero (J r : Ideal R) [r.IsPrime] (hJ : J ≤ r)
    (B : Type v) [CommRing B] [Algebra R B] {x : R} (hx : x ∈ J) :
    algebraMap R (r.Fiber B) x = 0 := by
  rw [algebraMap_fiber_eq r B x, Ideal.algebraMap_residueField_eq_zero.mpr (hJ hx), map_zero]

/-- `R ⧸ J` acts on the fibre ring of `r`, for `J ⊆ r`. -/
@[instance_reducible]
public noncomputable def algebraQuotRFiber (J r : Ideal R) [r.IsPrime] (hJ : J ≤ r)
    (B : Type v) [CommRing B] [Algebra R B] : Algebra (R ⧸ J) (r.Fiber B) :=
  (Ideal.Quotient.lift J (algebraMap R (r.Fiber B))
    (fun _ ha => algebraMap_fiber_eq_zero J r hJ B ha)).toAlgebra

/-- **`B → κ(r) ⊗_R B` kills `JB`**, for `J ⊆ r`, so it descends to `B ⧸ JB`. -/
public noncomputable def quotIncludeRight (J r : Ideal R) [r.IsPrime] (hJ : J ≤ r)
    (B : Type v) [CommRing B] [Algebra R B] :
    (B ⧸ Ideal.map (algebraMap R B) J) →+* r.Fiber B :=
  Ideal.Quotient.lift (Ideal.map (algebraMap R B) J)
    ((Algebra.TensorProduct.includeRight (R := R) (A := r.ResidueField) (B := B)) :
      B →+* r.Fiber B)
    (fun a ha => by
      refine (Ideal.map_le_iff_le_comap.mpr (fun c hc => ?_) :
        Ideal.map (algebraMap R B) J ≤ RingHom.ker
          ((Algebra.TensorProduct.includeRight (R := R) (A := r.ResidueField) (B := B)) :
            B →+* r.Fiber B)) ha
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change Algebra.TensorProduct.includeRight (algebraMap R B c) = 0
      rw [(Algebra.TensorProduct.includeRight (R := R) (A := r.ResidueField)
        (B := B)).commutes c]
      exact algebraMap_fiber_eq_zero J r hJ B hc)

/-- `Stacks.Flatness.quotIncludeRight` on the class of an element. -/
public theorem quotIncludeRight_mk (J r : Ideal R) [r.IsPrime] (hJ : J ≤ r)
    (B : Type v) [CommRing B] [Algebra R B] (b : B) :
    quotIncludeRight J r hJ B (algebraMap B (B ⧸ Ideal.map (algebraMap R B) J) b)
      = Algebra.TensorProduct.includeRight (R := R) (A := r.ResidueField) b := by
  rw [Ideal.Quotient.algebraMap_eq]
  rfl

/-! ### The identification of fibre rings -/

/-- The product of the two inclusions into a tensor product is the pure tensor. -/
private theorem includeLeftRingHom_mul_includeRight {S A B : Type*} [CommRing S] [CommRing A]
    [CommRing B] [Algebra S A] [Algebra S B] (x : A) (b : B) :
    Algebra.TensorProduct.includeLeftRingHom (R := S) (A := A) (B := B) x *
      Algebra.TensorProduct.includeRight b = x ⊗ₜ[S] b := by
  change x ⊗ₜ[S] (1 : B) * ((1 : A) ⊗ₜ[S] b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The forward map of the identification of fibre rings: the identification of residue fields on
the left factor and the quotient map `B → B ⧸ JB` on the right. -/
public noncomputable def quotFiberForward (J r : Ideal R) [r.IsPrime]
    [(Ideal.map (algebraMap R (R ⧸ J)) r).IsPrime] (hJ : J ≤ r)
    (B : Type v) [CommRing B] [Algebra R B] :
    r.Fiber B →+*
      (Ideal.map (algebraMap R (R ⧸ J)) r).Fiber (B ⧸ Ideal.map (algebraMap R B) J) :=
  tensorProductDescOfCompat (R' := R ⧸ J)
    ((Algebra.TensorProduct.includeLeftRingHom
        (R := R ⧸ J) (A := (Ideal.map (algebraMap R (R ⧸ J)) r).ResidueField)
        (B := B ⧸ Ideal.map (algebraMap R B) J)).comp
      (quotResidueFieldEquiv J r hJ).toRingHom)
    (((Algebra.TensorProduct.includeRight (R := R ⧸ J)
        (A := (Ideal.map (algebraMap R (R ⧸ J)) r).ResidueField)
        (B := B ⧸ Ideal.map (algebraMap R B) J)) :
      (B ⧸ Ideal.map (algebraMap R B) J) →+*
        (Ideal.map (algebraMap R (R ⧸ J)) r).Fiber (B ⧸ Ideal.map (algebraMap R B) J)).comp
      (algebraMap B (B ⧸ Ideal.map (algebraMap R B) J)))
    (fun x => by
      change Algebra.TensorProduct.includeLeftRingHom
          (quotResidueFieldEquiv J r hJ (algebraMap R r.ResidueField x)) = _
      rw [quotResidueFieldEquiv_algebraMap J r hJ x]
      rfl)
    (fun x => by
      change Algebra.TensorProduct.includeRight
          (algebraMap B (B ⧸ Ideal.map (algebraMap R B) J) (algebraMap R B x)) = _
      rw [algebraMap_quot_comp J B x]
      exact Algebra.TensorProduct.includeRight.commutes _)

/-- The forward map of the identification of fibre rings on a generator. -/
public theorem quotFiberForward_tmul (J r : Ideal R) [r.IsPrime]
    [(Ideal.map (algebraMap R (R ⧸ J)) r).IsPrime] (hJ : J ≤ r)
    (B : Type v) [CommRing B] [Algebra R B] (x : r.ResidueField) (b : B) :
    quotFiberForward J r hJ B (x ⊗ₜ[R] b)
      = (quotResidueFieldEquiv J r hJ x) ⊗ₜ[R ⧸ J]
          (algebraMap B (B ⧸ Ideal.map (algebraMap R B) J) b) := by
  exact includeLeftRingHom_mul_includeRight _ _

/-- The backward map of the identification of fibre rings: the inverse identification of residue
fields on the left factor and `Stacks.Flatness.quotIncludeRight` on the right. -/
public noncomputable def quotFiberBackward (J r : Ideal R) [r.IsPrime]
    [(Ideal.map (algebraMap R (R ⧸ J)) r).IsPrime] (hJ : J ≤ r)
    (B : Type v) [CommRing B] [Algebra R B] :
    (Ideal.map (algebraMap R (R ⧸ J)) r).Fiber (B ⧸ Ideal.map (algebraMap R B) J) →+*
      r.Fiber B :=
  letI : Algebra (R ⧸ J) (r.Fiber B) := algebraQuotRFiber J r hJ B
  tensorProductDescOfCompat (R := R ⧸ J) (R' := R ⧸ J)
    ((Algebra.TensorProduct.includeLeftRingHom (R := R) (A := r.ResidueField) (B := B)).comp
      (quotResidueFieldEquiv J r hJ).symm.toRingHom)
    (quotIncludeRight J r hJ B)
    (fun y => by
      obtain ⟨x, rfl⟩ := surjective_algebraMap_quotient J y
      change Algebra.TensorProduct.includeLeftRingHom
          ((quotResidueFieldEquiv J r hJ).symm
            (algebraMap (R ⧸ J) (Ideal.map (algebraMap R (R ⧸ J)) r).ResidueField
              (algebraMap R (R ⧸ J) x))) = _
      rw [quotResidueFieldEquiv_symm_algebraMap J r hJ x, ← algebraMap_fiber_eq r B x,
        Ideal.Quotient.algebraMap_eq (I := J)]
      rfl)
    (fun y => by
      obtain ⟨x, rfl⟩ := surjective_algebraMap_quotient J y
      rw [← algebraMap_quot_comp J B x, quotIncludeRight_mk,
        (Algebra.TensorProduct.includeRight (R := R) (A := r.ResidueField) (B := B)).commutes x,
        Ideal.Quotient.algebraMap_eq (I := J)]
      rfl)

/-- The backward map of the identification of fibre rings on a generator. -/
public theorem quotFiberBackward_tmul (J r : Ideal R) [r.IsPrime]
    [(Ideal.map (algebraMap R (R ⧸ J)) r).IsPrime] (hJ : J ≤ r)
    (B : Type v) [CommRing B] [Algebra R B]
    (y : (Ideal.map (algebraMap R (R ⧸ J)) r).ResidueField)
    (c : B ⧸ Ideal.map (algebraMap R B) J) :
    quotFiberBackward J r hJ B (y ⊗ₜ[R ⧸ J] c)
      = Algebra.TensorProduct.includeLeftRingHom
            ((quotResidueFieldEquiv J r hJ).symm y) *
          quotIncludeRight J r hJ B c := rfl

/-- The backward map of the identification of fibre rings on a generator whose right factor is the
class of an element of `B`. -/
public theorem quotFiberBackward_tmul_mk (J r : Ideal R) [r.IsPrime]
    [(Ideal.map (algebraMap R (R ⧸ J)) r).IsPrime] (hJ : J ≤ r)
    (B : Type v) [CommRing B] [Algebra R B]
    (y : (Ideal.map (algebraMap R (R ⧸ J)) r).ResidueField) (b : B) :
    quotFiberBackward J r hJ B
        (y ⊗ₜ[R ⧸ J] (algebraMap B (B ⧸ Ideal.map (algebraMap R B) J) b))
      = ((quotResidueFieldEquiv J r hJ).symm y) ⊗ₜ[R] b := by
  rw [quotFiberBackward_tmul, quotIncludeRight_mk]
  exact includeLeftRingHom_mul_includeRight _ _

/-- **The fibre ring of a dévissage stage is unchanged by the quotient base change.** For an
ideal `J ⊆ r` of `R`,

`κ(r) ⊗_R B  ≅  κ(r/J) ⊗_{R/J} (B/JB)`.

The residue field of `r` does not move, `R → R ⧸ J` being surjective and hence surjective on
stalks, and the two maps built from that identification and the quotient maps of `B` are mutually
inverse on generators. This is the identification of fibre rings the pointed base change of a
complete dévissage along `R → R ⧸ J` needs, the fibre-support condition and the dimension
condition of Stacks 05HZ both being read in the fibre ring. -/
public noncomputable def quotFiberRingEquiv (J r : Ideal R) [r.IsPrime]
    [(Ideal.map (algebraMap R (R ⧸ J)) r).IsPrime] (hJ : J ≤ r)
    (B : Type v) [CommRing B] [Algebra R B] :
    r.Fiber B ≃+*
      (Ideal.map (algebraMap R (R ⧸ J)) r).Fiber (B ⧸ Ideal.map (algebraMap R B) J) where
  toFun := quotFiberForward J r hJ B
  invFun := quotFiberBackward J r hJ B
  map_mul' := map_mul _
  map_add' := map_add _
  left_inv := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x b =>
        rw [quotFiberForward_tmul, quotFiberBackward_tmul_mk, RingEquiv.symm_apply_apply]
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  right_inv := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul y c =>
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
        rw [show (Ideal.Quotient.mk (Ideal.map (algebraMap R B) J) b)
            = algebraMap B (B ⧸ Ideal.map (algebraMap R B) J) b from
          (Ideal.Quotient.algebraMap_eq (Ideal.map (algebraMap R B) J)) ▸ rfl,
          quotFiberBackward_tmul_mk, quotFiberForward_tmul, RingEquiv.apply_symm_apply]
    | add z w hz hw => rw [map_add, map_add, hz, hw]

/-- **The identification of fibre rings is the identity on the image of `B`.** So it is an
isomorphism of `B`-algebras for the `Algebra.TensorProduct.rightAlgebra` structures, which is the
compatibility that `Module.support_eq_comap_preimage` and `topologicalKrullDimAt_support_eq`
consume. -/
public theorem quotFiberRingEquiv_includeRight (J r : Ideal R) [r.IsPrime]
    [(Ideal.map (algebraMap R (R ⧸ J)) r).IsPrime] (hJ : J ≤ r)
    (B : Type v) [CommRing B] [Algebra R B] (b : B) :
    quotFiberRingEquiv J r hJ B
        (Algebra.TensorProduct.includeRight (R := R) (A := r.ResidueField) b)
      = Algebra.TensorProduct.includeRight
          (R := R ⧸ J) (A := (Ideal.map (algebraMap R (R ⧸ J)) r).ResidueField)
          (algebraMap B (B ⧸ Ideal.map (algebraMap R B) J) b) := by
  show quotFiberForward J r hJ B ((1 : r.ResidueField) ⊗ₜ[R] b) = _
  rw [quotFiberForward_tmul, map_one]
  rfl

end Stacks.Flatness

end
