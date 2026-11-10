module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SelfProductConormal

/-!
# The conormal module of the diagonal as a square-zero divided power quotient

Fix a global crystalline situation `(p, (S, I, γ), X)` and let `(U(1), T(1), δ(1))` be a product
of an object `(U, T, δ)` of the small crystalline site `Cris(X/S)` with itself, presented by a
limit binary fan with projections `pr₀, pr₁`.  Over an open `V` of `T` write
`W = p₀⁻¹V ⊓ p₁⁻¹V` for the open of `T(1)` it determines, `R = Γ(W, 𝒪_{T(1)})`,
`A = Γ(V, 𝒪_T)`, `J = J_{T(1)}(W)` with its divided powers `δ(1)`, and let `K ⊆ R` be the
diagonal ideal with `K^{[2]}` its divided square and `K/K^{[2]}` the conormal module.

This module realises `K/K^{[2]}` as the square-zero part of a quotient of `R`.  The diagonal
`Δ : T ⟶ T(1)` has a section map `Δ^♯ : R ⟶ A` cut down to `V`, which splits both
coprojections; so every `y ∈ R` has a canonical representative `y - p₀^♯(Δ^♯ y)` of `K`, and the
graph `y ↦ (Δ^♯ y, [y - p₀^♯(Δ^♯ y)])` is a surjective ring homomorphism
`R ⟶ A ⊕ K/K^{[2]}` onto the trivial square-zero extension, with kernel exactly `K^{[2]}`.
Transporting the divided powers of `J` along it makes `A ⊕ K/K^{[2]}` a divided power ring in
which `Δ^♯` and the class map are the two coordinates of a divided power.

This is the algebraic shape of the second assertion of [Stacks, Tag 07J1], the one in which the
divided power universal property of `Ω_{T/S,δ}` can be applied: the ring-level statement
[Stacks, Tag 07HT] identifies `K/K^{[2]}` with the divided power differentials precisely by
comparing maps into such a square-zero extension.  The comparison map itself is built in
`StacksFrontier/AlgebraicGeometry/Crystalline/SelfProductConormal.lean`; nothing here claims it is
an isomorphism.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.sectionDpow` — the divided powers of a divided power
  scheme on sections over an open, spelled on `Γ(V, 𝒪)`.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductDiagonalSection_isDPMorphism` — the map
  `Δ^♯ : R ⟶ A` on sections of the ambient diagonal cut down to `V` (defined in
  `SelfProductConormal.lean`) is a divided power homomorphism.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductClassRep` — the representative
  `y - p₀^♯(Δ^♯ y)` of `K` attached to a section `y` of `𝒪_{T(1)}` over `W`.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductClassOf` — its class in `K/K^{[2]}`.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductGraphRingHom` — the graph
  `y ↦ (Δ^♯ y, [y - p₀^♯(Δ^♯ y)])`, a ring homomorphism to `TrivSqZeroExt A (K/K^{[2]})`.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductSquareZeroIdeal` — the image of
  `J_{T(1)}(W)` in that square-zero extension.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductSquareZeroDividedPowers` — the divided
  powers it carries, transported from `δ(1)` along the graph.

## Main results

* `Crystalline.GlobalCrystallineSituation.ker_smallSelfProductDiagonalSection` — the kernel of
  `Δ^♯` cut down to `V` is the diagonal ideal `K` on `W`; restriction along the equality of opens
  `Δ⁻¹W = V` is injective, so cutting down does not change the kernel.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductDiagonalSection_firstCoprojectionSection`
  and `smallSelfProductDiagonalSection_secondCoprojectionSection` — `Δ^♯` splits both
  coprojections.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductDiagonalSection_mem_ideal_iff` — a
  section of `𝒪_{T(1)}` over `W` lies in `J_{T(1)}` exactly when its image under `Δ^♯` lies in
  `J_T`.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductClassOf_add`,
  `smallSelfProductClassOf_first`, `smallSelfProductClassOf_second`,
  `smallSelfProductClassOf_kernel`, `smallSelfProductClassOf_mul` and
  `smallSelfProductClassOf_dpow` — additivity, the vanishing on the first coprojection, the
  agreement with `smallSelfProductDifference` on the second, the agreement with
  `smallSelfProductClass` on `K`, the Leibniz rule and the divided power chain rule.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductGraphRingHom_surjective` and
  `smallSelfProductGraphRingHom_ker` — the graph is surjective with kernel `K^{[2]}`, so
  `TrivSqZeroExt A (K/K^{[2]})` is the quotient `R/K^{[2]}`.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductGraphRingHom_isDPMorphism` and
  `smallSelfProductSquareZeroDividedPowers_coordinates` — the graph is a homomorphism of divided
  power rings, and a divided power of order `n > 0` in the square-zero extension has
  coordinates `(γ_n a, γ_{n-1} a · m)`.

## Implementation notes

The square-zero extension needs a right action of `A` on `K/K^{[2]}`, which for a commutative
ring is the left action read through `MulOpposite`; the two instances
`smallSelfProductConormalOppositeModule` and `smallSelfProductConormalIsCentralScalar` supply it
and are global, so that the declarations here can be used from other modules without
re-introducing them.

The divided power structure of a divided power scheme is carried by `Crystalline.sectionIdeal`,
an ideal of the sections of the structure sheaf read through the sheaf of the scheme; the
sections of the conormal module, and the opens of a scheme generally, are indexed by `Γ(V, 𝒪)`,
read through the presheaf.  The two are the same ring and not the same expression, so instance
search finds no action of the first on a module over the second, and a statement letting a
divided power act on the conormal module cannot be written with the divided powers of the scheme
directly.  `sectionDpow` is that operation with its argument and value spelled on `Γ(V, 𝒪)`; it
is the divided power of the structure, by `sectionDpow_eq`, and only exists to carry the second
spelling.

The divided powers of the quotient come from `DividedPowers.Quotient.OfSurjective.dividedPowers`,
whose side condition is that the kernel of the surjection meet the divided power ideal in a
sub-divided-power ideal.  Here the kernel is `K^{[2]}`, which is contained in `J_{T(1)}` and is a
sub-divided-power ideal of it by `smallSelfProductDividedSquare_isSubDPIdeal`, so the
intersection is `K^{[2]}` itself.

The arithmetic behind the divided power chain rule — that translating the argument of a divided
power of positive order by an element of `K` changes it by the linear term, modulo the divided
powers of order at least two of `K` — is
`dpow_add_sub_sub_mem_secondDividedPowerIdeal` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SelfProductConormal.lean`.  The public
`smallSelfProductDifference_dpow` does not substitute for it: that lemma is about the particular
elements `p₁^♯ f - p₀^♯ f` of `K`, whereas `smallSelfProductClassOf_dpow` has to translate by an
arbitrary element of `K`.

## References

* [Stacks Project, Tag 07J1](https://stacks.math.columbia.edu/tag/07J1)
* [Stacks Project, Tag 07HT](https://stacks.math.columbia.edu/tag/07HT)
* [Stacks Project, Tag 07HV](https://stacks.math.columbia.edu/tag/07HV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} {B D : CrystallineThickening S} {pr₀ pr₁ : D ⟶ B}

/-! ### Three auxiliary facts -/

/-- **The divided powers of a divided power scheme on sections over an open, spelled on
`Γ(V, 𝒪)`.**  The divided power structure of a divided power scheme is carried by
`Crystalline.sectionIdeal`, an ideal of the sections of the structure sheaf read through the
sheaf of the scheme rather than through its presheaf.  That is the same ring as `Γ(V, 𝒪)` but
not the same expression, so a module indexed by `Γ(V, 𝒪)` — the conormal module, for one — has
no action of it that instance search can find.  This records the operation with its argument and
value spelled on `Γ(V, 𝒪)`, which is what lets a divided power act on such a module. -/
def sectionDpow (X : DividedPowerScheme.{u}) (V : X.scheme.Opens) (n : ℕ)
    (a : Γ(X.scheme, V)) : Γ(X.scheme, V) :=
  (X.dividedPowers.dividedPowers (op V)).dpow n a

/-- The divided power on sections is the divided power of the structure, in its own spelling. -/
theorem sectionDpow_eq (X : DividedPowerScheme.{u}) (V : X.scheme.Opens) (n : ℕ)
    (a : Γ(X.scheme, V)) :
    sectionDpow X V n a = (X.dividedPowers.dividedPowers (op V)).dpow n a := rfl

/-! ### The diagonal on sections over an open of `T` -/

section DiagonalSection

/-- The diagonal on sections cut down to `V` is a homomorphism of divided power rings. -/
theorem smallSelfProductDiagonalSection_isDPMorphism (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    (D.obj.thickening.target.dividedPowers.dividedPowers
        (op (smallSelfProductOpen pr₀ pr₁ V))).IsDPMorphism
      (B.obj.thickening.target.dividedPowers.dividedPowers (op V))
      (smallSelfProductDiagonalSection h V).hom :=
  appLE_isDPMorphism (smallSelfProductAmbientDiagonal h) (smallSelfProductOpen pr₀ pr₁ V) V
    (le_of_eq (diagonal_preimage_smallSelfProductOpen h V).symm)

/-- **The kernel of `Δ^♯` cut down to `V` is the diagonal ideal `K` over `p₀⁻¹V ⊓ p₁⁻¹V`.**
Cutting down is the map on sections over that open followed by restriction along the equality of
opens `Δ⁻¹(p₀⁻¹V ⊓ p₁⁻¹V) = V`, and restriction along an equality of opens is an isomorphism,
hence injective, so the kernel is unchanged. -/
theorem ker_smallSelfProductDiagonalSection (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    RingHom.ker (smallSelfProductDiagonalSection h V).hom =
      smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V) := by
  have he := (diagonal_preimage_smallSelfProductOpen h V).symm
  have : IsIso (homOfLE (le_of_eq he)) := by
    change IsIso (eqToHom he)
    infer_instance
  have hinj := (ConcreteCategory.bijective_of_isIso
    (B.obj.thickening.target.scheme.presheaf.map (homOfLE (le_of_eq he)).op)).1
  exact RingHom.ker_comp_of_injective _ hinj

/-- **A section of `𝒪_{T(1)}` in the diagonal ideal is killed by `Δ^♯` cut down to `V`.** -/
theorem smallSelfProductDiagonalSection_eq_zero (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    {y : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)}
    (hy : y ∈ smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V)) :
    smallSelfProductDiagonalSection h V y = 0 :=
  RingHom.mem_ker.mp ((ker_smallSelfProductDiagonalSection h V).ge hy)

end DiagonalSection

/-! ### The canonical representative of a section in the diagonal ideal -/

section ClassOf

/-- **The representative `y - p₀^♯(Δ^♯ y)` of the diagonal ideal attached to a section `y` of
`𝒪_{T(1)}` over `p₀⁻¹V ⊓ p₁⁻¹V`.**  It lies in `K` because `Δ^♯` splits the first
coprojection, so `Δ^♯` kills it. -/
def smallSelfProductClassRep (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    (y : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) :
    ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V)) :=
  ⟨y - firstCoprojectionSection pr₀ pr₁ V (smallSelfProductDiagonalSection h V y), by
    rw [← ker_smallSelfProductDiagonalSection h V, RingHom.mem_ker, map_sub,
      smallSelfProductDiagonalSection_firstCoprojectionSection, sub_self]⟩

/-- The section underlying the canonical representative is `y - p₀^♯(Δ^♯ y)`. -/
@[simp]
theorem smallSelfProductClassRep_coe (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    (y : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) :
    (smallSelfProductClassRep h V y :
        Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) =
      y - firstCoprojectionSection pr₀ pr₁ V (smallSelfProductDiagonalSection h V y) := rfl

/-- **The class of `y - p₀^♯(Δ^♯ y)` in the conormal module `K/K^{[2]}`.**  Every section of
`𝒪_{T(1)}` over `p₀⁻¹V ⊓ p₁⁻¹V` has such a class, not only those in `K`. -/
def smallSelfProductClassOf (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    (y : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) :
    smallSelfProductConormal h V :=
  smallSelfProductClass h V (smallSelfProductClassRep h V y)

/-- **A class in the conormal module vanishes exactly when its representative lies in the divided
square.** -/
theorem smallSelfProductClass_eq_zero (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    (k : ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V))) :
    smallSelfProductClass h V k = 0 ↔
      (k : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) ∈
        smallSelfProductDividedSquare h (smallSelfProductOpen pr₀ pr₁ V) :=
  Submodule.Quotient.mk_eq_zero (smallSelfProductDiagonalRelations h V)

/-- The canonical representative is additive in the section. -/
theorem smallSelfProductClassRep_add (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    (x y : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) :
    smallSelfProductClassRep h V (x + y) =
      smallSelfProductClassRep h V x + smallSelfProductClassRep h V y := by
  apply Subtype.ext
  change x + y - firstCoprojectionSection pr₀ pr₁ V
      (smallSelfProductDiagonalSection h V (x + y)) =
    (x - firstCoprojectionSection pr₀ pr₁ V (smallSelfProductDiagonalSection h V x)) +
      (y - firstCoprojectionSection pr₀ pr₁ V (smallSelfProductDiagonalSection h V y))
  rw [map_add, map_add]
  ring

/-- Taking the class of `y - p₀^♯(Δ^♯ y)` is additive. -/
theorem smallSelfProductClassOf_add (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    (x y : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) :
    smallSelfProductClassOf h V (x + y) =
      smallSelfProductClassOf h V x + smallSelfProductClassOf h V y := by
  rw [smallSelfProductClassOf, smallSelfProductClassRep_add]
  exact smallSelfProductClass_add h V _ _

/-- **The class of a section pulled back along the first coprojection vanishes.**  Its canonical
representative is zero, `Δ^♯` splitting the first coprojection. -/
theorem smallSelfProductClassOf_first (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) (b : Γ(B.obj.thickening.target.scheme, V)) :
    smallSelfProductClassOf h V (firstCoprojectionSection pr₀ pr₁ V b) = 0 := by
  have hr : smallSelfProductClassRep h V (firstCoprojectionSection pr₀ pr₁ V b) = 0 := by
    apply Subtype.ext
    change firstCoprojectionSection pr₀ pr₁ V b - firstCoprojectionSection pr₀ pr₁ V
      (smallSelfProductDiagonalSection h V (firstCoprojectionSection pr₀ pr₁ V b)) = 0
    rw [smallSelfProductDiagonalSection_firstCoprojectionSection, sub_self]
  rw [smallSelfProductClassOf, hr]
  exact map_zero (smallSelfProductDiagonalRelations h V).mkQ

/-- **On a section of the diagonal ideal the class of `y - p₀^♯(Δ^♯ y)` is the class of `y`.** -/
theorem smallSelfProductClassOf_kernel (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    (k : ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V))) :
    smallSelfProductClassOf h V
        (k : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) =
      smallSelfProductClass h V k := by
  refine congrArg (smallSelfProductClass h V) (Subtype.ext ?_)
  change (k : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) -
      firstCoprojectionSection pr₀ pr₁ V (smallSelfProductDiagonalSection h V k) =
    (k : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V))
  rw [smallSelfProductDiagonalSection_eq_zero h V k.property, map_zero, sub_zero]

/-- **On a section pulled back along the second coprojection the class of `y - p₀^♯(Δ^♯ y)` is
the difference of the two coprojections.**  This identifies
`Crystalline.GlobalCrystallineSituation.smallSelfProductDifference` as a value of
`smallSelfProductClassOf`. -/
theorem smallSelfProductClassOf_second (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) (f : Γ(B.obj.thickening.target.scheme, V)) :
    smallSelfProductClassOf h V (secondCoprojectionSection pr₀ pr₁ V f) =
      smallSelfProductDifference h V f := by
  refine congrArg (smallSelfProductClass h V) (Subtype.ext ?_)
  change secondCoprojectionSection pr₀ pr₁ V f - firstCoprojectionSection pr₀ pr₁ V
      (smallSelfProductDiagonalSection h V (secondCoprojectionSection pr₀ pr₁ V f)) =
    secondCoprojectionSection pr₀ pr₁ V f - firstCoprojectionSection pr₀ pr₁ V f
  rw [smallSelfProductDiagonalSection_secondCoprojectionSection]

/-- **The Leibniz rule for the class of `y - p₀^♯(Δ^♯ y)`.**  The error term is the product of
the two canonical representatives, which lies in `K²` and hence in `K^{[2]}`. -/
theorem smallSelfProductClassOf_mul (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    (x y : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) :
    smallSelfProductClassOf h V (x * y) =
      smallSelfProductDiagonalSection h V x • smallSelfProductClassOf h V y +
        smallSelfProductDiagonalSection h V y • smallSelfProductClassOf h V x := by
  rw [smallSelfProductClassOf, smallSelfProductClassOf, smallSelfProductClassOf,
    ← smallSelfProductClass_smul, ← smallSelfProductClass_smul, ← smallSelfProductClass_add]
  refine smallSelfProductClass_eq h V ?_
  convert sq_le_smallSelfProductDividedSquare h _ (pow_two (smallSelfProductDiagonalIdeal h _) ▸
    Ideal.mul_mem_mul (smallSelfProductClassRep h V x).property
      (smallSelfProductClassRep h V y).property) using 1
  simp only [smallSelfProductClassRep_coe, map_mul, Submodule.coe_add, Submodule.coe_smul,
    smul_eq_mul]
  ring

/-- `Δ^♯` maps `J_{T(1)}` into `J_T`. -/
private theorem smallSelfProductDiagonalSection_mem_ideal_of_mem
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) (V : B.obj.thickening.target.scheme.Opens)
    {y : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)}
    (hy : y ∈ D.obj.thickening.target.ideal.obj (op (smallSelfProductOpen pr₀ pr₁ V))) :
    smallSelfProductDiagonalSection h V y ∈ B.obj.thickening.target.ideal.obj (op V) :=
  (smallSelfProductDiagonalSection_isDPMorphism h V).ideal_comp (Ideal.mem_map_of_mem _ hy)

/-- `p₀^♯` maps `J_T` into `J_{T(1)}`. -/
private theorem firstCoprojectionSection_mem_ideal (pr₀ pr₁ : D ⟶ B)
    (V : B.obj.thickening.target.scheme.Opens) {b : Γ(B.obj.thickening.target.scheme, V)}
    (hb : b ∈ B.obj.thickening.target.ideal.obj (op V)) :
    firstCoprojectionSection pr₀ pr₁ V b ∈
      D.obj.thickening.target.ideal.obj (op (smallSelfProductOpen pr₀ pr₁ V)) :=
  (firstCoprojectionSection_isDPMorphism pr₀ pr₁ V).ideal_comp (Ideal.mem_map_of_mem _ hb)

/-- **The divided power chain rule for the class of `y - p₀^♯(Δ^♯ y)`.**  Writing `y` as
`p₀^♯(Δ^♯ y)` plus an element of `K`, the addition formula for `δ(1)_n` has
`δ(1)_{n-1}(p₀^♯(Δ^♯ y))` times that element as its linear term, and all later terms carry a
divided power of order at least two of an element of `K`, hence lie in `K^{[2]}`. -/
theorem smallSelfProductClassOf_dpow (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) (n : ℕ) (hn : 0 < n)
    (y : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V))
    (hy : y ∈ D.obj.thickening.target.ideal.obj (op (smallSelfProductOpen pr₀ pr₁ V))) :
    smallSelfProductClassOf h V
        ((D.obj.thickening.target.dividedPowers.dividedPowers
          (op (smallSelfProductOpen pr₀ pr₁ V))).dpow n y) =
      sectionDpow B.obj.thickening.target V (n - 1)
          (smallSelfProductDiagonalSection h V y) •
        smallSelfProductClassOf h V y := by
  have hqy := smallSelfProductDiagonalSection_mem_ideal_of_mem h V hy
  have hkK : y - firstCoprojectionSection pr₀ pr₁ V
      (smallSelfProductDiagonalSection h V y) ∈
      smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V) :=
    (smallSelfProductClassRep h V y).property
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have e1 : smallSelfProductDiagonalSection h V
      (sectionDpow D.obj.thickening.target (smallSelfProductOpen pr₀ pr₁ V) (m + 1) y) =
      sectionDpow B.obj.thickening.target V (m + 1)
        (smallSelfProductDiagonalSection h V y) :=
    (smallSelfProductDiagonalSection_isDPMorphism h V).map_dpow hy
  have e2 : ∀ k : ℕ, firstCoprojectionSection pr₀ pr₁ V
      (sectionDpow B.obj.thickening.target V k
        (smallSelfProductDiagonalSection h V y)) =
      sectionDpow D.obj.thickening.target (smallSelfProductOpen pr₀ pr₁ V) k
        (firstCoprojectionSection pr₀ pr₁ V
          (smallSelfProductDiagonalSection h V y)) :=
    fun _ ↦ (firstCoprojectionSection_isDPMorphism pr₀ pr₁ V).map_dpow hqy
  change smallSelfProductClass h V (smallSelfProductClassRep h V
      (sectionDpow D.obj.thickening.target (smallSelfProductOpen pr₀ pr₁ V) (m + 1) y)) =
    sectionDpow B.obj.thickening.target V m (smallSelfProductDiagonalSection h V y) •
      smallSelfProductClass h V (smallSelfProductClassRep h V y)
  rw [← smallSelfProductClass_smul]
  refine smallSelfProductClass_eq h V ?_
  change sectionDpow D.obj.thickening.target (smallSelfProductOpen pr₀ pr₁ V) (m + 1) y -
        firstCoprojectionSection pr₀ pr₁ V (smallSelfProductDiagonalSection h V
          (sectionDpow D.obj.thickening.target (smallSelfProductOpen pr₀ pr₁ V)
            (m + 1) y)) -
      firstCoprojectionSection pr₀ pr₁ V
          (sectionDpow B.obj.thickening.target V m
            (smallSelfProductDiagonalSection h V y)) *
        (y - firstCoprojectionSection pr₀ pr₁ V
          (smallSelfProductDiagonalSection h V y)) ∈
    smallSelfProductDividedSquare h (smallSelfProductOpen pr₀ pr₁ V)
  refine secondDividedPowerIdeal_le_smallSelfProductDividedSquare h
    (smallSelfProductOpen pr₀ pr₁ V) ?_
  rw [e1, e2, e2]
  exact dpow_sub_sub_mem_secondDividedPowerIdeal
    (D.obj.thickening.target.dividedPowers.dividedPowers
      (op (smallSelfProductOpen pr₀ pr₁ V)))
    (smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V))
    (firstCoprojectionSection pr₀ pr₁ V (smallSelfProductDiagonalSection h V y)) y m
    (firstCoprojectionSection_mem_ideal pr₀ pr₁ V hqy) hkK
    (smallSelfProductDiagonalIdeal_le h _ hkK)

/-- **A section of `𝒪_{T(1)}` over `p₀⁻¹V ⊓ p₁⁻¹V` lies in `J_{T(1)}` exactly when its image
under `Δ^♯` lies in `J_T`.**  One direction is that `Δ^♯` is a homomorphism of divided power
rings; for the other, split the section as `p₀^♯(Δ^♯ y)` plus an element of `K`, and `K` is
contained in `J_{T(1)}`. -/
theorem smallSelfProductDiagonalSection_mem_ideal_iff (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    (y : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) :
    smallSelfProductDiagonalSection h V y ∈ B.obj.thickening.target.ideal.obj (op V) ↔
      y ∈ D.obj.thickening.target.ideal.obj (op (smallSelfProductOpen pr₀ pr₁ V)) := by
  refine ⟨fun hy ↦ ?_, smallSelfProductDiagonalSection_mem_ideal_of_mem h V⟩
  have hsum : firstCoprojectionSection pr₀ pr₁ V
        (smallSelfProductDiagonalSection h V y) +
      (y - firstCoprojectionSection pr₀ pr₁ V
        (smallSelfProductDiagonalSection h V y)) ∈
      D.obj.thickening.target.ideal.obj (op (smallSelfProductOpen pr₀ pr₁ V)) :=
    add_mem (firstCoprojectionSection_mem_ideal pr₀ pr₁ V hy)
      (smallSelfProductDiagonalIdeal_le h (smallSelfProductOpen pr₀ pr₁ V)
        (smallSelfProductClassRep h V y).property)
  rwa [add_sub_cancel] at hsum

end ClassOf

/-! ### The graph of the class map as a square-zero extension -/

section Graph

/-- **The conormal module is a right module over the sections of `𝒪_T`**, the action being the
left one read through `MulOpposite`; the ring of sections is commutative, so this loses nothing.
It is what makes the trivial square-zero extension of the conormal module a ring. -/
instance smallSelfProductConormalOppositeModule (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    Module Γ(B.obj.thickening.target.scheme, V)ᵐᵒᵖ (smallSelfProductConormal h V) :=
  Module.compHom _ (RingEquiv.toOpposite Γ(B.obj.thickening.target.scheme, V)).symm.toRingHom

/-- The left and right actions of the sections of `𝒪_T` on the conormal module agree. -/
instance smallSelfProductConormalIsCentralScalar (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    IsCentralScalar Γ(B.obj.thickening.target.scheme, V) (smallSelfProductConormal h V) :=
  ⟨fun _ _ ↦ rfl⟩

/-- **The graph `y ↦ (Δ^♯ y, [y - p₀^♯(Δ^♯ y)])` of the class map**, a ring homomorphism from the
sections of `𝒪_{T(1)}` over `p₀⁻¹V ⊓ p₁⁻¹V` to the trivial square-zero extension of the conormal
module `K/K^{[2]}` by `Γ(V, 𝒪_T)`.  Multiplicativity is the Leibniz rule for the class map. -/
def smallSelfProductGraphRingHom (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V) →+*
      TrivSqZeroExt Γ(B.obj.thickening.target.scheme, V) (smallSelfProductConormal h V) where
  toFun y := ⟨smallSelfProductDiagonalSection h V y, smallSelfProductClassOf h V y⟩
  map_one' := TrivSqZeroExt.ext (map_one _) (show smallSelfProductClassOf h V 1 = 0 by
    simpa only [map_one] using smallSelfProductClassOf_first h V 1)
  map_mul' x y := by
    refine TrivSqZeroExt.ext (map_mul _ _ _) ?_
    change smallSelfProductClassOf h V (x * y) =
      smallSelfProductDiagonalSection h V x • smallSelfProductClassOf h V y +
        MulOpposite.op (smallSelfProductDiagonalSection h V y) •
          smallSelfProductClassOf h V x
    rw [op_smul_eq_smul]
    exact smallSelfProductClassOf_mul h V x y
  map_zero' := TrivSqZeroExt.ext (map_zero _) (show smallSelfProductClassOf h V 0 = 0 by
    simpa only [map_zero] using smallSelfProductClassOf_first h V 0)
  map_add' x y := TrivSqZeroExt.ext (map_add _ _ _) (smallSelfProductClassOf_add h V x y)

/-- The first coordinate of the graph is `Δ^♯`. -/
theorem smallSelfProductGraphRingHom_fst (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    (y : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) :
    (smallSelfProductGraphRingHom h V y).fst = smallSelfProductDiagonalSection h V y := rfl

/-- The second coordinate of the graph is the class of `y - p₀^♯(Δ^♯ y)`. -/
theorem smallSelfProductGraphRingHom_snd (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    (y : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) :
    (smallSelfProductGraphRingHom h V y).snd = smallSelfProductClassOf h V y := rfl

/-- **The graph is surjective.**  A pair `(b, m)` is hit by `p₀^♯ b` plus any representative of
`m`: the first coprojection is split by `Δ^♯` and has vanishing class, while a section of `K`
is killed by `Δ^♯` and has itself as class. -/
theorem smallSelfProductGraphRingHom_surjective (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    Function.Surjective (smallSelfProductGraphRingHom h V) := by
  rintro ⟨b, m⟩
  obtain ⟨k, rfl⟩ := Submodule.mkQ_surjective (smallSelfProductDiagonalRelations h V) m
  refine ⟨firstCoprojectionSection pr₀ pr₁ V b +
    (k : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)), ?_⟩
  apply TrivSqZeroExt.ext
  · change smallSelfProductDiagonalSection h V (firstCoprojectionSection pr₀ pr₁ V b +
      (k : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V))) = b
    rw [map_add, smallSelfProductDiagonalSection_firstCoprojectionSection,
      smallSelfProductDiagonalSection_eq_zero h V k.property, add_zero]
  · change smallSelfProductClassOf h V (firstCoprojectionSection pr₀ pr₁ V b +
      (k : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V))) = _
    rw [smallSelfProductClassOf_add, smallSelfProductClassOf_first, zero_add]
    exact smallSelfProductClassOf_kernel h V k

/-- **The kernel of the graph is the divided square `K^{[2]}`.**  A section is killed exactly
when `Δ^♯` kills it — so it lies in `K` — and its class in `K/K^{[2]}` vanishes, which for a
section of `K` is membership in `K^{[2]}`; conversely `K^{[2]}` is contained in `K`, so both
coordinates vanish on it. -/
theorem smallSelfProductGraphRingHom_ker (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    RingHom.ker (smallSelfProductGraphRingHom h V) =
      smallSelfProductDividedSquare h (smallSelfProductOpen pr₀ pr₁ V) := by
  apply le_antisymm
  · intro y hy
    have hz := RingHom.mem_ker.mp hy
    have hq : smallSelfProductDiagonalSection h V y = 0 := congrArg TrivSqZeroExt.fst hz
    have hc : smallSelfProductClassOf h V y = 0 := congrArg TrivSqZeroExt.snd hz
    have hyK : y ∈ smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V) :=
      (ker_smallSelfProductDiagonalSection h V).le (RingHom.mem_ker.mpr hq)
    exact (smallSelfProductClass_eq_zero h V ⟨y, hyK⟩).mp
      ((smallSelfProductClassOf_kernel h V ⟨y, hyK⟩).symm.trans hc)
  · intro y hy
    have hyK := smallSelfProductDividedSquare_le h (smallSelfProductOpen pr₀ pr₁ V) hy
    refine RingHom.mem_ker.mpr
      (TrivSqZeroExt.ext (smallSelfProductDiagonalSection_eq_zero h V hyK) ?_)
    change smallSelfProductClassOf h V y = 0
    exact (smallSelfProductClassOf_kernel h V ⟨y, hyK⟩).trans
      ((smallSelfProductClass_eq_zero h V ⟨y, hyK⟩).mpr hy)

end Graph

/-! ### The divided power structure on the square-zero extension -/

section SquareZeroDividedPowers

/-- **The image of `J_{T(1)}` in the square-zero extension `A ⊕ K/K^{[2]}`.**  The graph is
surjective, so this is the divided power ideal of the quotient `R/K^{[2]}` read through the
identification with the square-zero extension. -/
def smallSelfProductSquareZeroIdeal (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    Ideal (TrivSqZeroExt Γ(B.obj.thickening.target.scheme, V)
      (smallSelfProductConormal h V)) :=
  Ideal.map (smallSelfProductGraphRingHom h V)
    (D.obj.thickening.target.ideal.obj (op (smallSelfProductOpen pr₀ pr₁ V)))

/-- The ideal of the square-zero extension is the image of `J_{T(1)}`, by definition. -/
theorem smallSelfProductSquareZeroIdeal_eq (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    smallSelfProductSquareZeroIdeal h V =
      Ideal.map (smallSelfProductGraphRingHom h V)
        (D.obj.thickening.target.ideal.obj (op (smallSelfProductOpen pr₀ pr₁ V))) := rfl

/-- **The kernel of the graph meets `J_{T(1)}` in a sub-divided-power ideal.**  The kernel is
the divided square `K^{[2]}`, which is contained in `J_{T(1)}` and is preserved by its divided
structure, so the intersection is `K^{[2]}` itself.  This is the side condition under which the
divided powers descend along the graph. -/
theorem smallSelfProductGraphRingHom_inf_isSubDPIdeal
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) (V : B.obj.thickening.target.scheme.Opens) :
    (D.obj.thickening.target.dividedPowers.dividedPowers
        (op (smallSelfProductOpen pr₀ pr₁ V))).IsSubDPIdeal
      (RingHom.ker (smallSelfProductGraphRingHom h V) ⊓
        D.obj.thickening.target.ideal.obj (op (smallSelfProductOpen pr₀ pr₁ V))) := by
  have hker := smallSelfProductGraphRingHom_ker h V
  have hsub := smallSelfProductDividedSquare_isSubDPIdeal h (smallSelfProductOpen pr₀ pr₁ V)
  exact ⟨fun _ hx ↦ hx.2, fun n hn _ hx ↦ ⟨hker.ge (hsub.dpow_mem n hn (hker.le hx.1)),
    (D.obj.thickening.target.dividedPowers.dividedPowers
      (op (smallSelfProductOpen pr₀ pr₁ V))).dpow_mem hn hx.2⟩⟩

/-- **The divided powers of the square-zero extension**, transported from `δ(1)` along the
graph.  The side condition is that the kernel of the graph meet `J_{T(1)}` in a
sub-divided-power ideal; the kernel is `K^{[2]}`, which is contained in `J_{T(1)}` and is a
sub-divided-power ideal of it. -/
def smallSelfProductSquareZeroDividedPowers (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    DividedPowers (smallSelfProductSquareZeroIdeal h V) :=
  DividedPowers.Quotient.OfSurjective.dividedPowers
    (D.obj.thickening.target.dividedPowers.dividedPowers
      (op (smallSelfProductOpen pr₀ pr₁ V)))
    (smallSelfProductGraphRingHom_surjective h V)
    (smallSelfProductSquareZeroIdeal_eq h V)
    (smallSelfProductGraphRingHom_inf_isSubDPIdeal h V)

/-- The graph is a homomorphism of divided power rings for the transported structure. -/
theorem smallSelfProductGraphRingHom_isDPMorphism (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    (D.obj.thickening.target.dividedPowers.dividedPowers
        (op (smallSelfProductOpen pr₀ pr₁ V))).IsDPMorphism
      (smallSelfProductSquareZeroDividedPowers h V) (smallSelfProductGraphRingHom h V) :=
  DividedPowers.Quotient.OfSurjective.isDPMorphism
    (D.obj.thickening.target.dividedPowers.dividedPowers
      (op (smallSelfProductOpen pr₀ pr₁ V)))
    (smallSelfProductGraphRingHom_surjective h V)
    (smallSelfProductSquareZeroIdeal_eq h V)
    (smallSelfProductGraphRingHom_inf_isSubDPIdeal h V)

/-- **An element of the square-zero extension lies in its divided power ideal exactly when its
first coordinate lies in `J_T`.**  Both directions go through a preimage under the graph, where
the statement is `smallSelfProductDiagonalSection_mem_ideal_iff`. -/
theorem smallSelfProductSquareZeroIdeal_mem_iff (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    (x : TrivSqZeroExt Γ(B.obj.thickening.target.scheme, V)
      (smallSelfProductConormal h V)) :
    x ∈ smallSelfProductSquareZeroIdeal h V ↔
      x.fst ∈ B.obj.thickening.target.ideal.obj (op V) := by
  obtain ⟨y, rfl⟩ := smallSelfProductGraphRingHom_surjective h V x
  refine ⟨fun hx ↦ ?_, fun hx ↦ (smallSelfProductSquareZeroIdeal_eq h V).ge
    (Ideal.mem_map_of_mem _ ((smallSelfProductDiagonalSection_mem_ideal_iff h V y).mp hx))⟩
  obtain ⟨z, hz, he⟩ := (Ideal.mem_map_iff_of_surjective
    (smallSelfProductGraphRingHom h V)
    (smallSelfProductGraphRingHom_surjective h V)).mp
      ((smallSelfProductSquareZeroIdeal_eq h V).le hx)
  have heq : smallSelfProductDiagonalSection h V z =
    smallSelfProductDiagonalSection h V y := congrArg TrivSqZeroExt.fst he
  change smallSelfProductDiagonalSection h V y ∈ B.obj.thickening.target.ideal.obj (op V)
  rw [← heq]
  exact (smallSelfProductDiagonalSection_mem_ideal_iff h V z).mpr hz

/-- **The two coordinates of a divided power of positive order in the square-zero extension.**
The first is the divided power of the first coordinate, and the second is the divided power of
order one less of the first coordinate acting on the second: that is the divided power chain rule
for the class map, read through the graph. -/
theorem smallSelfProductSquareZeroDividedPowers_coordinates
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) (V : B.obj.thickening.target.scheme.Opens) (n : ℕ)
    (hn : 0 < n)
    (x : TrivSqZeroExt Γ(B.obj.thickening.target.scheme, V)
      (smallSelfProductConormal h V))
    (hx : x ∈ smallSelfProductSquareZeroIdeal h V) :
    ((smallSelfProductSquareZeroDividedPowers h V).dpow n x).fst =
        sectionDpow B.obj.thickening.target V n x.fst ∧
      ((smallSelfProductSquareZeroDividedPowers h V).dpow n x).snd =
        sectionDpow B.obj.thickening.target V (n - 1) x.fst • x.snd := by
  obtain ⟨y, rfl⟩ := smallSelfProductGraphRingHom_surjective h V x
  have hy : y ∈ D.obj.thickening.target.ideal.obj (op (smallSelfProductOpen pr₀ pr₁ V)) :=
    (smallSelfProductDiagonalSection_mem_ideal_iff h V y).mp
      ((smallSelfProductSquareZeroIdeal_mem_iff h V _).mp hx)
  have hdp := (smallSelfProductGraphRingHom_isDPMorphism h V).map_dpow (n := n) hy
  exact ⟨(congrArg TrivSqZeroExt.fst hdp.symm).trans
      ((smallSelfProductDiagonalSection_isDPMorphism h V).map_dpow hy),
    (congrArg TrivSqZeroExt.snd hdp.symm).trans (smallSelfProductClassOf_dpow h V n hn y hy)⟩

end SquareZeroDividedPowers

end Crystalline.GlobalCrystallineSituation

end
