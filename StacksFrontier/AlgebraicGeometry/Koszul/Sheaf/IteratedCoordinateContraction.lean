module

public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.CoordinateContractionStalk
public import StacksFrontier.RingTheory.Koszul.ContractionDeterminant

/-!
# The iterated coordinate contraction at a stalk is the duality pairing

Let `O♯` be a sheaf of commutative rings on a space `X`, let `F = (O♯)ʳ` be the finite free sheaf
of `O♯`-modules on `r` generators and let `A` be a bundle of tensor, exterior and symmetric
algebras of `F`. For a tuple `j : Fin i → {1, …, r}` of indices the `i`-fold composite of
coordinate contractions

`δ_{j₀} ∘ ⋯ ∘ δ_{j_{i-1}} : ⋀ⁱ(F) ⟶ ⋀⁰(F)`

lowers the exterior degree all the way to zero. This file constructs that composite and computes
the map it induces on stalks: under the identification of the stalk of `⋀ⁿ(F)` with the exterior
power `⋀ⁿ_{O_x}((O_x)ʳ)`, it is the `i`-fold iterate of ring-level contractions by the coordinate
projections `pr_{j₀}, …, pr_{j_{i-1}}`, and the scalar it produces — the degree-zero coefficient of
the result — is the linear form

`Koszul.listContractionDual i (List.ofFn fun k => pr_{j k})`.

That linear form is the one `Koszul.pairingDual_ιMulti` identifies with the duality pairing of
exterior powers, so `Koszul.bijective_of_listContractionDual` applies to any linear map agreeing
with it on wedges: for `(O_x)ʳ` free of finite rank, such a map is bijective. The composite above
is therefore the local model of the comparison of Stacks 0BQY in degree `i`, and the recognition
lemma supplies its invertibility with no inverse constructed.

## Main definitions

* `Koszul.tupleD`: **the iterate of the ring-level contractions** by the entries of a tuple of
  linear forms, from the `n`-th exterior power to the zeroth.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.tupleCoordKoszulD`: **the `i`-fold composite of
  coordinate contractions**, from the `i`-th exterior power of a sheaf of modules to the zeroth,
  contracting by the first entry of the tuple first.
* `Stacks.RegularSequence.KoszulChainData.tupleCoordKoszulD`: the same composite on the terms of
  the Koszul chain complex, `K_i ⟶ K_0`, and
  `Stacks.RegularSequence.KoszulChainData.tupleCoordKoszulDOf`: the same composite at
  independently named degrees, `K_p ⟶ K_q` for `q + i = p`.

## Main results

* `Stacks.RegularSequence.stalkLin_id` and `Stacks.RegularSequence.stalkLin_comp`: the map induced
  on stalks by a morphism of presheaves of modules is functorial.
* `Koszul.listContractionDual_eq_tupleD`: **the iterate of the ring-level contractions computes
  the duality pairing**: its degree-zero coefficient is `Koszul.listContractionDual`.
* `SheafOfModules.TensorExteriorSymmetricAlgebras`
  `.exteriorKoszulStalkEquiv_stalkLin_tupleCoordKoszulD`: **the `i`-fold composite at a stalk is
  the iterate of the contractions by the coordinate projections.**
* `SheafOfModules.TensorExteriorSymmetricAlgebras`
  `.listContractionDual_exteriorKoszulStalkEquiv`: **the scalar it produces is
  `Koszul.listContractionDual`**, the duality pairing against the wedge of those projections.
* `Stacks.RegularSequence.KoszulChainData.tupleCoordKoszulD_eq`: the composite on the terms of the
  complex is the composite on the exterior powers, conjugated by the identification of a term with
  an exterior power.

## Implementation notes

**The degrees are natural numbers and the recursion is on the arity.** The composite is indexed by
a tuple `Fin i → ι` and recurses on `i`, so its source is the `i`-th exterior power and its target
the zeroth, with no transport anywhere: `A.exteriorPower (i + 1)` is the source of the contraction
out of degree `i + 1` on the nose. Indexing instead by a list and a base degree would put
`A.exteriorPower (n + l.length)` in the source, and while the base case would then need only the
transport along `n + 0 = n`, which is definitional, the top-level use at `n = 0` would need the one
along `0 + l.length = l.length`, which is not.

**The ring-level iterate is taken between exterior powers, not inside the exterior algebra.**
`Koszul.listContraction` is an endomorphism of the whole exterior algebra, so comparing it directly
with the stalk identification — which lands in a homogeneous piece — puts a coercion out of a
submodule around every term of every intermediate goal, and a rewrite under such a coercion is what
makes those proofs exhaust their heartbeats rather than fail. `Koszul.tupleD` is the same iterate
taken between the homogeneous pieces, where the sheaf-side induction has clean types; the passage
to the exterior algebra, and hence to `Koszul.listContractionDual`, is a separate statement about
modules with no sheaf in it.

**The first entry is contracted first**, matching the convention of `Koszul.listContraction` and
hence the order in which a composition product of degree-one Ext classes acts. This is what makes
the stalk formula read as `Koszul.listContractionDual i (List.ofFn j)` with no reversal.

## References

* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 0622](https://stacks.math.columbia.edu/tag/0622)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf Opposite TopologicalSpace
open scoped ExteriorAlgebra

namespace Koszul

/-! ### The iterate of the ring-level contractions -/

section Tuple

universe t s

variable {R : Type t} [CommRing R] {E : Type s} [AddCommGroup E] [Module R E]

/-- **The iterate of the ring-level contractions** by the entries of a tuple of linear forms, from
the `n`-th exterior power to the zeroth, contracting by the first entry first. -/
def tupleD : (n : ℕ) → (Fin n → Module.Dual R E) → ((⋀[R]^n E) →ₗ[R] ⋀[R]^0 E)
  | 0 => fun _ => LinearMap.id
  | n + 1 => fun f => (tupleD n fun k => f k.succ).comp (Koszul.d (f 0) n)

/-- The iterate of the contractions by the empty tuple is the identity of `⋀⁰ E`. -/
@[simp]
theorem tupleD_zero (f : Fin 0 → Module.Dual R E) :
    tupleD 0 f = (LinearMap.id : (⋀[R]^0 E) →ₗ[R] ⋀[R]^0 E) := rfl

/-- The iterate of the contractions by a tuple of length `n + 1` is contraction by its first entry
followed by the iterate of the contractions by the remaining entries. -/
@[simp]
theorem tupleD_succ (n : ℕ) (f : Fin (n + 1) → Module.Dual R E) :
    tupleD (n + 1) f = (tupleD n fun k => f k.succ).comp (Koszul.d (f 0) n) := rfl

/-- Evaluated at `y`, the iterate of the contractions by a tuple of length `n + 1` is the iterate
by the remaining entries applied to the contraction of `y` by the first entry. -/
theorem tupleD_succ_apply (n : ℕ) (f : Fin (n + 1) → Module.Dual R E) (y : ⋀[R]^(n + 1) E) :
    tupleD (n + 1) f y = tupleD n (fun k => f k.succ) (Koszul.d (f 0) n y) := rfl

/-- **The iterate of the ring-level contractions computes the duality pairing.** Its degree-zero
coefficient, read off by the augmentation of the exterior algebra, is the linear form
`Koszul.listContractionDual` of the list of the tuple's entries.

The induction is on the arity: for the empty tuple both sides are the degree-zero coefficient of
the argument, and one more contraction on the left is one more entry at the head of the list on the
right. -/
theorem listContractionDual_eq_tupleD (n : ℕ) (f : Fin n → Module.Dual R E) (y : ⋀[R]^n E) :
    listContractionDual n (List.ofFn f) y =
      ExteriorAlgebra.algebraMapInv ((tupleD n f y : ⋀[R]^0 E) : ExteriorAlgebra R E) := by
  induction n with
  | zero => rw [List.ofFn_zero, listContractionDual_apply, listContraction_nil]; rfl
  | succ n ih =>
    rw [List.ofFn_succ, listContractionDual_apply, listContraction_cons_apply,
      tupleD_succ_apply, ← ih (fun k => f k.succ) (Koszul.d (f 0) n y),
      listContractionDual_apply, d_apply_coe]

end Tuple

end Koszul

namespace Stacks.RegularSequence

/-! ### Functoriality of the map induced on stalks -/

section Stalks

universe u

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
  {M N P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}

/-- **The identity induces the identity on stalks.** Every element of a stalk is a germ, and the
identity carries a section to itself. -/
theorem stalkLin_id (x : ↥X) (m : ↑(TopCat.Presheaf.stalk M.presheaf x)) :
    stalkLin (𝟙 M) x m = m := by
  obtain ⟨U, hx, s, rfl⟩ := exists_germAddHom_eq M m
  exact stalkLin_germAddHom (𝟙 M) U hx s

/-- **The map induced on stalks by a composite is the composite of the induced maps.** Checked on
germs, where each side carries a section to the germ of its image. -/
theorem stalkLin_comp (ψ : M ⟶ N) (χ : N ⟶ P) (x : ↥X)
    (m : ↑(TopCat.Presheaf.stalk M.presheaf x)) :
    stalkLin (ψ ≫ χ) x m = stalkLin χ x (stalkLin ψ x m) := by
  obtain ⟨U, hx, s, rfl⟩ := exists_germAddHom_eq M m
  rw [stalkLin_germAddHom, stalkLin_germAddHom, stalkLin_germAddHom]
  rfl

end Stalks

end Stacks.RegularSequence

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

/-! ### The iterated coordinate contraction on the exterior powers -/

section Tuple

universe v u w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {ι : Type w} [DecidableEq ι] [Finite ι]
  (A : TensorExteriorSymmetricAlgebras J (SheafOfModules.free (R := toRingCat J Osharp) ι))

/-- **The `i`-fold composite of coordinate contractions**, `⋀ⁱ(F) ⟶ ⋀⁰(F)`, contracting by the
first entry of the tuple first. -/
def tupleCoordKoszulD : (i : ℕ) → (Fin i → ι) → (A.exteriorPower i ⟶ A.exteriorPower 0)
  | 0 => fun _ => 𝟙 (A.exteriorPower 0)
  | i + 1 => fun f => A.coordKoszulDNat (f 0) i ≫ tupleCoordKoszulD i fun k => f k.succ

/-- The composite of coordinate contractions by the empty tuple is the identity of `⋀⁰(F)`. -/
@[simp]
theorem tupleCoordKoszulD_zero (f : Fin 0 → ι) :
    A.tupleCoordKoszulD 0 f = 𝟙 (A.exteriorPower 0) := rfl

/-- The composite of coordinate contractions by a tuple of length `i + 1` is the contraction by its
first entry followed by the composite of the contractions by the remaining entries. -/
@[simp]
theorem tupleCoordKoszulD_succ (i : ℕ) (f : Fin (i + 1) → ι) :
    A.tupleCoordKoszulD (i + 1) f =
      A.coordKoszulDNat (f 0) i ≫ A.tupleCoordKoszulD i fun k => f k.succ := rfl

end Tuple

/-! ### The iterated coordinate contraction at a stalk -/

section Stalk

universe u

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {r : ℕ}
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (Stacks.RegularSequence.koszulFreeSheaf Osharp r))

/-- **The `i`-fold composite of coordinate contractions at a stalk is the iterate of the
contractions by the coordinate projections.** Under the identification of the stalk of `⋀ⁿ((O♯)ʳ)`
with `⋀ⁿ_{O_x}((O_x)ʳ)`, the map that `δ_{j₀} ∘ ⋯ ∘ δ_{j_{i-1}}` induces on stalks is
`Koszul.tupleD` at `pr_{j₀}, …, pr_{j_{i-1}}`.

The induction is on `i`: the empty composite is the identity on both sides, and a composite of
length `i + 1` is the single contraction `δ_{j₀}`, which at a stalk is contraction by `pr_{j₀}` by
`exteriorKoszulStalkEquiv_stalkLin_coordKoszulD`, followed by the composite of length `i`. -/
theorem exteriorKoszulStalkEquiv_stalkLin_tupleCoordKoszulD (i : ℕ) (f : Fin i → Fin r)
    (x : ↥X) (m : ↑(TopCat.Presheaf.stalk (A.exteriorPower i).val.presheaf x)) :
    Stacks.SheafOfModules.exteriorKoszulStalkEquiv A 0 x
        (Stacks.RegularSequence.stalkLin
          (A.tupleCoordKoszulD i fun k => ULift.up (f k)).val x m) =
      Koszul.tupleD i
        (fun k => (LinearMap.proj (f k) :
          Module.Dual ↑(TopCat.Presheaf.stalk Osharp.obj x)
            (Fin r → ↑(TopCat.Presheaf.stalk Osharp.obj x))))
        (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A i x m) := by
  induction i with
  | zero =>
    rw [A.tupleCoordKoszulD_zero, SheafOfModules.id_val,
      Stacks.RegularSequence.stalkLin_id, Koszul.tupleD_zero, LinearMap.id_apply]
  | succ i ih =>
    have hone := A.exteriorKoszulStalkEquiv_stalkLin_coordKoszulD (f 0) i x m
    refine Eq.trans (congrArg
      (fun φ : A.exteriorPower (i + 1) ⟶ A.exteriorPower 0 =>
        Stacks.SheafOfModules.exteriorKoszulStalkEquiv A 0 x
          (Stacks.RegularSequence.stalkLin (SheafOfModules.Hom.val φ) x m))
      (A.tupleCoordKoszulD_succ i fun k => ULift.up (f k))) ?_
    refine Eq.trans (congrArg
      (fun z => Stacks.SheafOfModules.exteriorKoszulStalkEquiv A 0 x z)
      (Stacks.RegularSequence.stalkLin_comp
        (A.coordKoszulDNat (ULift.up (f 0)) i).val
        (A.tupleCoordKoszulD i fun k => ULift.up (f k.succ)).val x m)) ?_
    refine Eq.trans (ih (fun k => f k.succ)
      (Stacks.RegularSequence.stalkLin
        (A.coordKoszulDNat (ULift.up (f 0)) i).val x m)) ?_
    exact congrArg
      (fun z : ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^i
          (Fin r → ↑(TopCat.Presheaf.stalk Osharp.obj x)) =>
        Koszul.tupleD i
          (fun k => (LinearMap.proj (f k.succ) :
            Module.Dual ↑(TopCat.Presheaf.stalk Osharp.obj x)
              (Fin r → ↑(TopCat.Presheaf.stalk Osharp.obj x)))) z)
      hone

/-- **The scalar produced by the `i`-fold composite of coordinate contractions at a stalk is the
duality pairing against the wedge of the coordinate projections.** Reading the degree-zero result
through the augmentation of the exterior algebra turns the iterate into the linear form
`Koszul.listContractionDual i (List.ofFn fun k => pr_{j k})`, which `Koszul.pairingDual_ιMulti`
identifies with `exteriorPower.pairingDual` on the wedge of those projections.

`Koszul.bijective_of_listContractionDual` therefore applies to any linear map out of
`⋀ⁱ(((O_x)ʳ)^∨)` agreeing with this form on wedges, and gives its bijectivity. -/
theorem listContractionDual_exteriorKoszulStalkEquiv (i : ℕ) (f : Fin i → Fin r) (x : ↥X)
    (m : ↑(TopCat.Presheaf.stalk (A.exteriorPower i).val.presheaf x)) :
    Koszul.listContractionDual i
        (List.ofFn fun k => (LinearMap.proj (f k) :
          Module.Dual ↑(TopCat.Presheaf.stalk Osharp.obj x)
            (Fin r → ↑(TopCat.Presheaf.stalk Osharp.obj x))))
        (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A i x m) =
      ExteriorAlgebra.algebraMapInv
        ((Stacks.SheafOfModules.exteriorKoszulStalkEquiv A 0 x
            (Stacks.RegularSequence.stalkLin
              (A.tupleCoordKoszulD i fun k => ULift.up (f k)).val x m) :
          ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^0
            (Fin r → ↑(TopCat.Presheaf.stalk Osharp.obj x))) :
          ExteriorAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
            (Fin r → ↑(TopCat.Presheaf.stalk Osharp.obj x))) := by
  rw [Koszul.listContractionDual_eq_tupleD,
    A.exteriorKoszulStalkEquiv_stalkLin_tupleCoordKoszulD i f x m]

end Stalk

end SheafOfModules.TensorExteriorSymmetricAlgebras

namespace Stacks.RegularSequence.KoszulChainData

/-! ### The iterated coordinate contraction on the terms of the Koszul chain complex -/

section Chain

universe v u w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {ι : Type w} [DecidableEq ι] [Finite ι]
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras J
    (SheafOfModules.free (R := toRingCat J Osharp) ι)}
  {g : SheafOfModules.free (R := toRingCat J Osharp) ι ⟶
    SheafOfModules.unit (toRingCat J Osharp)} (K : KoszulChainData A g)

/-- **The coordinate contraction between the terms of adjacent nonnegative degrees** of the Koszul
chain complex, `δⱼ : K_{n+1} ⟶ K_n`. -/
def coordKoszulDNat (j : ι) (n : ℕ) :
    K.chain.X ((n + 1 : ℕ) : ℤ) ⟶ K.chain.X ((n : ℕ) : ℤ) :=
  K.coordKoszulD j (show ((n : ℕ) : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring)

/-- **The `i`-fold composite of coordinate contractions on the terms of the Koszul chain
complex**, `K_i ⟶ K_0`, contracting by the first entry of the tuple first. -/
def tupleCoordKoszulD :
    (i : ℕ) → (Fin i → ι) → (K.chain.X ((i : ℕ) : ℤ) ⟶ K.chain.X ((0 : ℕ) : ℤ))
  | 0 => fun _ => 𝟙 (K.chain.X ((0 : ℕ) : ℤ))
  | i + 1 => fun f => K.coordKoszulDNat (f 0) i ≫ tupleCoordKoszulD i fun k => f k.succ

/-- The composite of coordinate contractions by the empty tuple is the identity of `K_0`. -/
@[simp]
theorem tupleCoordKoszulD_zero (f : Fin 0 → ι) :
    K.tupleCoordKoszulD 0 f = 𝟙 (K.chain.X ((0 : ℕ) : ℤ)) := rfl

/-- The composite of coordinate contractions by a tuple of length `i + 1` on the terms of the
Koszul chain complex is `δ_{f 0} : K_{i+1} ⟶ K_i` followed by the composite of the contractions by
the remaining entries. -/
@[simp]
theorem tupleCoordKoszulD_succ (i : ℕ) (f : Fin (i + 1) → ι) :
    K.tupleCoordKoszulD (i + 1) f =
      K.coordKoszulDNat (f 0) i ≫ K.tupleCoordKoszulD i fun k => f k.succ := rfl

/-- **The `i`-fold composite of coordinate contractions at independently named degrees**,
`K_p ⟶ K_q` for degrees with `q + i = p`, contracting by the first entry of the tuple first. The
empty composite is the transport along `p = q`. -/
def tupleCoordKoszulDOf :
    (i : ℕ) → (Fin i → ι) → ∀ {p q : ℤ}, q + (i : ℤ) = p → (K.chain.X p ⟶ K.chain.X q)
  | 0 => fun _ {p q} h => eqToHom (congrArg K.chain.X (show p = q by push_cast at h; omega))
  | i + 1 => fun f {p q} h =>
      K.coordKoszulD (f 0) (show p - 1 + 1 = p by ring) ≫
        tupleCoordKoszulDOf i (fun k => f k.succ)
          (show q + (i : ℤ) = p - 1 by push_cast at h ⊢; omega)

/-- The composite of coordinate contractions by the empty tuple from `K_p` to `K_q`, where
`q = p`, is the transport along that equality of degrees. -/
@[simp]
theorem tupleCoordKoszulDOf_zero (f : Fin 0 → ι) {p q : ℤ} (h : q + ((0 : ℕ) : ℤ) = p) :
    K.tupleCoordKoszulDOf 0 f h =
      eqToHom (congrArg K.chain.X (show p = q by push_cast at h; omega)) := rfl

/-- The composite of coordinate contractions by a tuple of length `i + 1` from `K_p` to `K_q` is
the contraction `K_p ⟶ K_{p-1}` by its first entry followed by the composite of the contractions by
the remaining entries from `K_{p-1}` to `K_q`. -/
@[simp]
theorem tupleCoordKoszulDOf_succ (i : ℕ) (f : Fin (i + 1) → ι) {p q : ℤ}
    (h : q + ((i + 1 : ℕ) : ℤ) = p) :
    K.tupleCoordKoszulDOf (i + 1) f h =
      K.coordKoszulD (f 0) (show p - 1 + 1 = p by ring) ≫
        K.tupleCoordKoszulDOf i (fun k => f k.succ)
          (show q + (i : ℤ) = p - 1 by push_cast at h ⊢; omega) := rfl

/-- The coordinate contraction between adjacent terms of the complex is the one between the
exterior powers, read through the identification of a term with an exterior power. -/
theorem coordKoszulDNat_eq (j : ι) (n : ℕ) :
    K.coordKoszulDNat j n =
      (K.chainXIso ((n + 1 : ℕ) : ℤ)).inv ≫ A.coordKoszulDNat j n ≫
        (K.chainXIso ((n : ℕ) : ℤ)).hom := rfl

/-- **The `i`-fold composite on the terms of the complex is the `i`-fold composite on the exterior
powers, conjugated** by the identification of a term of the complex with an exterior power. The
inner identifications cancel in pairs, which is `Stacks.iso_conj_comp`. -/
theorem tupleCoordKoszulD_eq (i : ℕ) (f : Fin i → ι) :
    K.tupleCoordKoszulD i f =
      (K.chainXIso ((i : ℕ) : ℤ)).inv ≫ A.tupleCoordKoszulD i f ≫
        (K.chainXIso ((0 : ℕ) : ℤ)).hom := by
  induction i with
  | zero =>
    rw [K.tupleCoordKoszulD_zero,
      SheafOfModules.TensorExteriorSymmetricAlgebras.tupleCoordKoszulD_zero,
      Category.id_comp, Iso.inv_hom_id]
  | succ i ih =>
    rw [K.tupleCoordKoszulD_succ, K.coordKoszulDNat_eq, ih (fun k => f k.succ),
      Stacks.iso_conj_comp,
      SheafOfModules.TensorExteriorSymmetricAlgebras.tupleCoordKoszulD_succ]

end Chain

end Stacks.RegularSequence.KoszulChainData

end
