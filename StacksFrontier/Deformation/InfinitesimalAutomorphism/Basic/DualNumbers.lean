module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Derivation.Basic
public import StacksFrontier.Deformation.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Dual numbers, derivations and field objects

The ring isomorphism underlying an isomorphism of `𝒞_Λ`, the functoriality of the dual numbers
in the coefficient ring, derivations as automorphisms of the dual numbers, and the bijectivity of
morphisms of `𝒞_Λ` between objects whose carriers are fields.
-/

@[expose] public section

namespace Deformation

/-! ### The ring isomorphism underlying an isomorphism of the base category -/

section
universe u v w

/-- The ring isomorphism between the carriers of two isomorphic objects of `𝒞_Λ`, given by the
underlying algebra map of the isomorphism. -/
def ringEquivOfIso {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (e : A ≅ B) : A ≃+* B :=
  (AlgEquiv.ofAlgHom e.hom.hom e.inv.hom
    (congrArg (fun f : B ⟶ B => f.hom) e.inv_hom_id)
    (congrArg (fun f : A ⟶ A => f.hom) e.hom_inv_id)).toRingEquiv

end

/-! ### Functoriality of the dual numbers in the coefficient ring -/

/-- The ring map `R[ε] → S[ε]` induced by a ring map `R → S`, acting on each of the two
coordinates. -/
def dualNumberRingHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    DualNumber R →+* DualNumber S where
  toFun x := TrivSqZeroExt.inl (f x.fst) + TrivSqZeroExt.inr (f x.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

/-- The constant coordinate of `dualNumberRingHom f x` is the image of the constant coordinate
of `x`. -/
theorem dualNumberRingHom_fst {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : DualNumber R) : (dualNumberRingHom f x).fst = f x.fst :=
  add_zero _

/-- The `ε`-coordinate of `dualNumberRingHom f x` is the image of the `ε`-coordinate of `x`. -/
theorem dualNumberRingHom_snd {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : DualNumber R) : (dualNumberRingHom f x).snd = f x.snd :=
  zero_add _

/-- The ring isomorphism `R[ε] ≃ S[ε]` induced by a ring isomorphism `R ≃ S`. -/
def dualNumberRingEquiv {R S : Type*} [CommRing R] [CommRing S] (f : R ≃+* S) :
    DualNumber R ≃+* DualNumber S :=
  { dualNumberRingHom f.toRingHom with
    invFun := dualNumberRingHom f.symm.toRingHom
    left_inv := fun x => by ext <;> simp [dualNumberRingHom]
    right_inv := fun x => by ext <;> simp [dualNumberRingHom] }

/-! ### Derivations as automorphisms of the dual numbers -/

section
universe w m

/-- The `k`-algebra endomorphism `x + yε ↦ x + (D x + y)ε` of `P[ε]` attached to a
`k`-derivation `D` of `P`. -/
@[sga "3 II 3.14", sga "3 VIIA 6.4.3" "special case"]
def derivationDualNumberAlgHom {k : Type w} {P : Type (max w m)} [Field k] [CommRing P]
    [Algebra k P] (D : Derivation k P P) : DualNumber P →ₐ[k] DualNumber P := by
  let f : P →ₐ[k] DualNumber P :=
    { toFun := fun x => TrivSqZeroExt.inl x + TrivSqZeroExt.inr (D x)
      map_one' := by simp [D.map_one_eq_zero]
      map_mul' := by
        intro x y
        rw [D.leibniz]
        ext <;> (simp [add_mul, mul_add, add_assoc, add_comm]; try ring)
      map_zero' := by simp
      map_add' := by
        intro x y
        ext <;> simp [map_add]
      commutes' := by
        intro r
        ext
        · simp [TrivSqZeroExt.algebraMap_eq_inl']
        · simp [TrivSqZeroExt.algebraMap_eq_inl', D.map_algebraMap] }
  exact DualNumber.lift ⟨(f, DualNumber.eps), DualNumber.eps_mul_eps,
    fun _ => DualNumber.commute_eps_left _⟩

/-- The value of `derivationDualNumberAlgHom D` on a constant. -/
theorem derivationDualNumberAlgHom_inl {k : Type w} {P : Type (max w m)} [Field k]
    [CommRing P] [Algebra k P] (D : Derivation k P P) (x : P) :
    derivationDualNumberAlgHom D (TrivSqZeroExt.inl x) =
      TrivSqZeroExt.inl x + TrivSqZeroExt.inr (D x) := by
  simp [derivationDualNumberAlgHom, DualNumber.lift_apply_inl]

/-- The automorphism attached to a derivation fixes `ε`. -/
@[sga "3 VIIA 6.4.3" "partial"]
theorem derivationDualNumberAlgHom_eps {k : Type w} {P : Type (max w m)} [Field k]
    [CommRing P] [Algebra k P] (D : Derivation k P P) :
    derivationDualNumberAlgHom D DualNumber.eps = DualNumber.eps := by
  unfold derivationDualNumberAlgHom
  exact DualNumber.lift_apply_eps _

/-- A pure `ε`-term of `P[ε]` is a constant times `ε`. -/
theorem inr_eq_inl_mul_eps {P : Type*} [CommRing P] (x : P) :
    TrivSqZeroExt.inr x = TrivSqZeroExt.inl x * DualNumber.eps := by
  calc
    TrivSqZeroExt.inr x = TrivSqZeroExt.inr (x • (1 : P)) := by simp
    _ = TrivSqZeroExt.inl x * TrivSqZeroExt.inr 1 :=
      (TrivSqZeroExt.inl_mul_inr x (1 : P)).symm
    _ = TrivSqZeroExt.inl x * DualNumber.eps := rfl

/-- Multiplying an element of `P[ε]` by `ε` keeps only its constant coordinate. -/
theorem inl_add_inr_mul_eps {P : Type*} [CommRing P] (x y : P) :
    (TrivSqZeroExt.inl x + TrivSqZeroExt.inr y) * DualNumber.eps = TrivSqZeroExt.inr x := by
  change (TrivSqZeroExt.inl x + TrivSqZeroExt.inr y) *
    TrivSqZeroExt.inr 1 = TrivSqZeroExt.inr x
  rw [add_mul, TrivSqZeroExt.inl_mul_inr, TrivSqZeroExt.inr_mul_inr, add_zero]
  simp

/-- An algebra endomorphism of `P[ε]` fixing `ε` and sending `inl x` to `inl x + inr y` fixes
`inr x`. -/
private theorem map_inr_eq_inr_of_map_inl {k : Type*} {P : Type*} [Field k] [CommRing P]
    [Algebra k P] (f : DualNumber P →ₐ[k] DualNumber P) (heps : f DualNumber.eps = DualNumber.eps)
    (x y : P) (h : f (TrivSqZeroExt.inl x) = TrivSqZeroExt.inl x + TrivSqZeroExt.inr y) :
    f (TrivSqZeroExt.inr x) = TrivSqZeroExt.inr x := by
  conv_lhs => rw [inr_eq_inl_mul_eps, map_mul, heps, h]
  exact inl_add_inr_mul_eps x y

/-- The automorphism attached to a derivation fixes every pure `ε`-term. -/
@[sga "3 VIIA 6.4.3" "partial"]
theorem derivationDualNumberAlgHom_inr {k : Type w} {P : Type (max w m)} [Field k]
    [CommRing P] [Algebra k P] (D : Derivation k P P) (x : P) :
    derivationDualNumberAlgHom D (TrivSqZeroExt.inr x) = TrivSqZeroExt.inr x :=
  map_inr_eq_inr_of_map_inl _ (derivationDualNumberAlgHom_eps D) x (D x)
    (derivationDualNumberAlgHom_inl D x)

/-- An algebra endomorphism of `P[ε]` is the automorphism attached to `D` if it sends `inl x` to
`inl x + inr (D x)` and fixes every pure `ε`-term. -/
private theorem eq_derivationDualNumberAlgHom {k : Type w} {P : Type (max w m)} [Field k]
    [CommRing P] [Algebra k P] (D : Derivation k P P) (g : DualNumber P →ₐ[k] DualNumber P)
    (hl : ∀ x, g (TrivSqZeroExt.inl x) = TrivSqZeroExt.inl x + TrivSqZeroExt.inr (D x))
    (hr : ∀ x, g (TrivSqZeroExt.inr x) = TrivSqZeroExt.inr x) :
    g = derivationDualNumberAlgHom D := by
  apply DualNumber.algHom_ext'
  · refine AlgHom.ext fun x => ?_
    change g (TrivSqZeroExt.inl x) = derivationDualNumberAlgHom D (TrivSqZeroExt.inl x)
    rw [derivationDualNumberAlgHom_inl]
    exact hl x
  · refine LinearMap.ext fun x => ?_
    change g (x • DualNumber.eps) = derivationDualNumberAlgHom D (x • DualNumber.eps)
    rw [← DualNumber.inr_eq_smul_eps, hr, derivationDualNumberAlgHom_inr]

/-- Addition of derivations corresponds to composition of the attached automorphisms. -/
theorem derivationDualNumberAlgHom_add {k : Type w} {P : Type (max w m)} [Field k]
    [CommRing P] [Algebra k P] (D E : Derivation k P P) :
    derivationDualNumberAlgHom (D + E) =
      (derivationDualNumberAlgHom D).comp (derivationDualNumberAlgHom E) := by
  symm
  refine eq_derivationDualNumberAlgHom _ _ (fun x => ?_) fun x => ?_
  · rw [AlgHom.comp_apply, derivationDualNumberAlgHom_inl E x, map_add,
      derivationDualNumberAlgHom_inl D x, derivationDualNumberAlgHom_inr D (E x),
      Derivation.add_apply]
    ext <;> simp [add_assoc]
  · rw [AlgHom.comp_apply, derivationDualNumberAlgHom_inr, derivationDualNumberAlgHom_inr]

/-- The zero derivation gives the identity automorphism. -/
theorem derivationDualNumberAlgHom_zero {k : Type w} {P : Type (max w m)} [Field k]
    [CommRing P] [Algebra k P] :
    derivationDualNumberAlgHom (0 : Derivation k P P) = AlgHom.id k (DualNumber P) := by
  symm
  refine eq_derivationDualNumberAlgHom _ _ (fun x => ?_) fun x => rfl
  simp

/-- The `k`-algebra automorphism of `P[ε]` attached to a `k`-derivation of `P`; its inverse
is the automorphism of the negated derivation. -/
@[sga "3 VIIA 6.4.3" "special case"]
def derivationDualNumberAlgEquiv {k : Type w} {P : Type (max w m)} [Field k] [CommRing P]
    [Algebra k P] (D : Derivation k P P) : DualNumber P ≃ₐ[k] DualNumber P :=
  AlgEquiv.ofAlgHom (derivationDualNumberAlgHom D) (derivationDualNumberAlgHom (-D))
    (by rw [← derivationDualNumberAlgHom_add, add_neg_cancel,
      derivationDualNumberAlgHom_zero])
    (by rw [← derivationDualNumberAlgHom_add, neg_add_cancel,
      derivationDualNumberAlgHom_zero])

/-- The `k`-derivation of `P` read off from an endomorphism of `P[ε]` that is the identity on
constant parts: it is the `ε`-coefficient of the image of a constant. -/
@[sga "3 II 3.14", sga "3 VIIA 1.5" "special case"]
def derivationOfDualNumberAlgHom {k : Type w} {P : Type (max w m)} [Field k] [CommRing P]
    [Algebra k P] (f : DualNumber P →ₐ[k] DualNumber P)
    (hred : ∀ x, (f (TrivSqZeroExt.inl x)).fst = x) :
    Derivation k P P := by
  refine
    { toLinearMap :=
        { toFun := fun x => (f (TrivSqZeroExt.inl x)).snd
          map_add' := ?_
          map_smul' := ?_ }
      map_one_eq_zero' := ?_
      leibniz' := ?_ }
  · intro x y
    simp only [map_add, TrivSqZeroExt.inl_add, map_add, TrivSqZeroExt.snd_add]
  · intro r x
    have h := congrArg TrivSqZeroExt.snd (f.toLinearMap.map_smul r (TrivSqZeroExt.inl x))
    change (f (r • TrivSqZeroExt.inl x)).snd = r • (f (TrivSqZeroExt.inl x)).snd at h
    rw [← TrivSqZeroExt.inl_smul] at h
    simpa only [TrivSqZeroExt.snd_smul, RingHom.id_apply] using h
  · change (f (TrivSqZeroExt.inl (1 : P))).snd = 0
    have h : f (TrivSqZeroExt.inl (1 : P)) = TrivSqZeroExt.inl (1 : P) := by
      simpa only [TrivSqZeroExt.inl_one] using map_one f
    simpa only [TrivSqZeroExt.snd_inl] using congrArg TrivSqZeroExt.snd h
  · intro x y
    have h := congrArg TrivSqZeroExt.snd
      (map_mul f (TrivSqZeroExt.inl x) (TrivSqZeroExt.inl y))
    simp only [TrivSqZeroExt.inl_mul_inl, DualNumber.snd_mul, hred] at h
    change (f (TrivSqZeroExt.inl (x * y))).snd =
      x • (f (TrivSqZeroExt.inl y)).snd + y • (f (TrivSqZeroExt.inl x)).snd
    rw [smul_eq_mul, smul_eq_mul]
    rw [mul_comm (f (TrivSqZeroExt.inl x)).snd y] at h
    exact h

/-- An endomorphism of `P[ε]` which is the identity on constant parts and fixes `ε` is the
automorphism attached to the derivation it defines. -/
@[sga "3 II 3.14" "partial", sga "3 VIIA 1.5" "Inverse clause", sga "3 VIIA 2.5" "partial"]
theorem derivationDualNumberAlgHom_derivationOfDualNumberAlgHom
    {k : Type w} {P : Type (max w m)} [Field k] [CommRing P] [Algebra k P]
    (f : DualNumber P →ₐ[k] DualNumber P) (hred : ∀ x, (f (TrivSqZeroExt.inl x)).fst = x)
    (heps : f DualNumber.eps = DualNumber.eps) :
    derivationDualNumberAlgHom (derivationOfDualNumberAlgHom f hred) = f := by
  let D := derivationOfDualNumberAlgHom f hred
  have hcoord (x : P) :
      f (TrivSqZeroExt.inl x) = TrivSqZeroExt.inl x + TrivSqZeroExt.inr (D x) := by
    apply TrivSqZeroExt.ext
    · simpa using hred x
    · simp [D, derivationOfDualNumberAlgHom]
  exact (eq_derivationDualNumberAlgHom D f hcoord
    fun x => map_inr_eq_inr_of_map_inl f heps x (D x) (hcoord x)).symm

/-- The two coordinates of the value of the automorphism attached to a derivation. -/
@[sga "3 VIIA 6.4.3" "special case"]
theorem derivationDualNumberAlgHom_coordinates {k : Type w} {P : Type (max w m)} [Field k]
    [CommRing P] [Algebra k P] (D : Derivation k P P) (z : DualNumber P) :
    (derivationDualNumberAlgHom D z).fst = z.fst ∧
      (derivationDualNumberAlgHom D z).snd = D z.fst + z.snd := by
  have hz : z = TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inr z.snd := by ext <;> simp
  rw [hz]
  simp only [map_add, derivationDualNumberAlgHom_inl, derivationDualNumberAlgHom_inr]
  simp

/-- The automorphism attached to a derivation fixes the image of `k[ε]` in `P[ε]`. -/
@[sga "3 VIIA 6.4.3" "partial"]
theorem derivationDualNumberAlgHom_scalar {k : Type w} {P : Type (max w m)} [Field k]
    [CommRing P] [Algebra k P] (D : Derivation k P P) (r : DualNumber k) :
    derivationDualNumberAlgHom D (dualNumberRingHom (algebraMap k P) r) =
      dualNumberRingHom (algebraMap k P) r := by
  apply TrivSqZeroExt.ext
  · exact (derivationDualNumberAlgHom_coordinates D _).1
  · rw [(derivationDualNumberAlgHom_coordinates D _).2]
    simp [dualNumberRingHom]

end

/-! ### Morphisms of the base category between objects whose carriers are fields -/

section
universe u w

/-- A morphism of `𝒞_Λ` between objects whose carriers are fields is bijective: it is
injective because the source is a field, and surjective because both residue fields are
identified with `k`. -/
theorem artinianLocalAlgHom_bijective_of_isField {Λ : Type u} {k : Type w} [CommRing Λ]
    [Field k] [Algebra Λ k] (A B : ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hA : IsField A) (hB : IsField B) (f : A ⟶ B) : Function.Bijective f.hom := by
  let : Field A := hA.toField
  let : Field B := hB.toField
  refine ⟨f.hom.toRingHom.injective, fun y => ?_⟩
  obtain ⟨q, hq⟩ := A.residueEquiv.surjective (B.residueEquiv (IsLocalRing.residue B y))
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective q
  refine ⟨x, (IsLocalRing.residue B).injective ?_⟩
  apply B.residueEquiv.injective
  rw [f.residue_comm, hx, hq]

end

end Deformation
