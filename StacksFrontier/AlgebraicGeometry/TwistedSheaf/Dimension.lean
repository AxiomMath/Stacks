module

public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Uniqueness
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeNeTop
public import StacksFrontier.Data.ENat.WithBotNatCast

/-!
# The descent measure of Tag 0BEM

The induction behind [Stacks, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM) descends on
the dimension of the support of the coherent sheaf, and
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf` therefore takes the measure as a
parameter `dim : X.Modules → ℕ` together with the hypothesis `hdim` bounding it by
`topologicalKrullDim (Supp ℱ)`. That hypothesis is not geometry: it is satisfiable because a
scheme proper over a field has *finite* dimension, so the dimension of a nonempty support is a
natural number and can be used as the measure outright. This file proves that and instantiates
the measure, leaving the two geometric inputs of the tag as the only hypotheses.

Finiteness of the dimension is read off the local rings rather than off a chain argument. The
dimension of a scheme is the supremum of the Krull dimensions of its local rings
(`AlgebraicGeometry.topologicalKrullDim_eq_iSup_krullDimOfRing_stalk`, Tag 04MU), the local ring
at a point of an affine open `U` is a localization of `Γ(X, U)` and so has Krull dimension at
most that of `Γ(X, U)`, and `Γ(X, U)` is a finitely generated algebra over the base field, whose
Krull dimension is finite because it is a quotient of a polynomial ring in finitely many
variables. A proper scheme is quasi-compact, so finitely many affine opens suffice and the
supremum is bounded by the largest of their dimensions.

## Main definitions

* `AlgebraicGeometry.natDimSupp` is the dimension of the support of a sheaf of modules as a
  natural number: the descent measure of Tag 0BEM.

## Main results

* `ringKrullDim_ne_top_of_finiteType`: the Krull dimension of a finitely generated algebra over
  a field is finite.
* `AlgebraicGeometry.ringKrullDim_stalk_le_of_isAffineOpen`: the local ring at a point of an
  affine open has Krull dimension at most that of the ring of sections of that open.
* `AlgebraicGeometry.topologicalKrullDim_ne_top_of_locallyOfFiniteType`: a quasi-compact scheme
  locally of finite type over a field has finite dimension.
* `AlgebraicGeometry.coe_natDimSupp_eq`: on nonempty support the measure agrees with the
  dimension of the support, which is the hypothesis `hdim` of
  `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf`.
* `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_natDimSupp`: Tag 0BEM from its two
  geometric inputs alone, with the descent measure supplied.

## Implementation notes

`ringKrullDim_ne_top_of_finiteType` is stated in the root namespace, as Mathlib would state it.
Three `private` copies of it exist in the tree
(`StacksFrontier/RingTheory/CohenMacaulay/OpenLocus.lean`,
`StacksFrontier/RingTheory/RelativeDimension/ValuationRing.lean`, and
`StacksFrontier/AlgebraicGeometry/Variety/Defs/Dimension/MaximalChain.lean`, the last under the name
`ringKrullDim_ne_top_of_finiteType_aux`); this is the public home, and those three should be
repointed at it rather than a fourth copy being made.

The field the sections are an algebra over is `Γ(Spec k, ⊤)` rather than `k` itself, carrying
the field structure transported along `AlgebraicGeometry.Scheme.ΓSpecIso`. That is the shape in
which `AlgebraicGeometry.Scheme.Hom.finiteType_appLE` delivers finite generation, and no
comparison with `k` is needed since only finiteness of the dimension is used.

No tag attribute is attached. Finiteness of the dimension of a scheme of finite type over a
field is not one of the Stacks statements the development tracks, and Tag 0BEM itself is still
conditional on its two geometric inputs.

## References

* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 04MU](https://stacks.math.columbia.edu/tag/04MU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/- `natCast_ne_top_withBot` was re-proved here. It is public in
`StacksFrontier/Data/ENat/WithBotNatCast.lean:23`, the module that exists for exactly this --
its docstring records that several modules had each proved the `WithBot ℕ∞` form for
themselves. The uses below name that one. -/


private theorem coe_unbotD_toNat_eq {x : WithBot ℕ∞} (hb : x ≠ ⊥) (ht : x ≠ ⊤) :
    ((((x.unbotD 0).toNat : ℕ) : WithBot ℕ∞)) = x := by
  induction x with
  | bot => exact absurd rfl hb
  | coe y =>
    induction y with
    | top => exact absurd rfl ht
    | coe m => simp

/-- **An element of `WithBot ℕ∞` other than `⊤` is bounded by a natural number.** This is the
step that turns a finiteness statement about the dimension of a scheme into an explicit natural
number bound, as the dimension hypotheses of the intersection-theory files require. -/
theorem exists_natCast_le_of_ne_top {x : WithBot ℕ∞} (hx : x ≠ ⊤) :
    ∃ n : ℕ, x ≤ (n : WithBot ℕ∞) := by
  by_cases hb : x = ⊥
  · exact ⟨0, hb ▸ bot_le⟩
  · exact ⟨_, (coe_unbotD_toNat_eq hb hx).ge⟩

/-- **The local ring at a point of an affine open has Krull dimension at most that of the ring
of sections of that open.** The local ring is the localization of `Γ(X, U)` at the prime
corresponding to the point, so its dimension is the height of that prime. -/
theorem ringKrullDim_stalk_le_of_isAffineOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (x : U) :
    ringKrullDim (X.presheaf.stalk (x : X)) ≤ ringKrullDim Γ(X, U) := by
  have := hU.isLocalization_stalk x
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf x).asIdeal
    (X.presheaf.stalk (x : X))]
  exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'

/-- **The ring of sections of an affine open of a scheme locally of finite type over a field is
a finitely generated algebra over that field**, so its Krull dimension is finite. -/
theorem ringKrullDim_ne_top_of_locallyOfFiniteType (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (V : X.affineOpens) :
    ringKrullDim Γ(X, (V : X.Opens)) ≠ ⊤ := by
  let : Field Γ(Spec (.of k), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  let : Algebra (Γ(Spec (.of k), ⊤)) (Γ(X, (V : X.Opens))) :=
    (f.appLE ⊤ (V : X.Opens) (by simp)).hom.toAlgebra
  have hft : (f.appLE ⊤ (V : X.Opens) (by simp)).hom.FiniteType :=
    f.finiteType_appLE (isAffineOpen_top _) V.2 (by simp)
  let : Algebra.FiniteType (Γ(Spec (.of k), ⊤)) (Γ(X, (V : X.Opens))) :=
    (RingHom.finiteType_algebraMap).mp hft
  exact ringKrullDim_ne_top_of_finiteType (κ := Γ(Spec (.of k), ⊤))

/-- **A quasi-compact scheme locally of finite type over a field has finite dimension.** The
dimension is the supremum of the Krull dimensions of the local rings, each of which is bounded
by the dimension of the ring of sections of an affine open containing the point; finitely many
affine opens cover a quasi-compact scheme, so the supremum is bounded by the largest of those
finitely many dimensions. -/
theorem topologicalKrullDim_ne_top_of_locallyOfFiniteType (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [CompactSpace X] :
    topologicalKrullDim X ≠ ⊤ := by
  classical
  obtain ⟨s, hs, hcov⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
    (show IsCompact ((⊤ : X.Opens) : Set X) by simpa using isCompact_univ (X := X))
  have key : ∀ V : X.affineOpens, ∃ n : ℕ,
      ringKrullDim Γ(X, (V : X.Opens)) ≤ (n : WithBot ℕ∞) := fun V =>
    exists_natCast_le_of_ne_top (ringKrullDim_ne_top_of_locallyOfFiniteType k f V)
  choose n hn using key
  refine ne_top_of_le_ne_top (b := ((hs.toFinset.sup n : ℕ) : WithBot ℕ∞))
    (natCast_ne_top_withBot _) ?_
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk X]
  refine iSup_le fun x => ?_
  have hx : x ∈ (⊤ : X.Opens) := trivial
  rw [hcov] at hx
  simp only [Opens.mem_iSup] at hx
  obtain ⟨V, hV, hxV⟩ := hx
  calc ringKrullDim (X.presheaf.stalk x)
      ≤ ringKrullDim Γ(X, (V : X.Opens)) := ringKrullDim_stalk_le_of_isAffineOpen V.2 ⟨x, hxV⟩
    _ ≤ (n V : WithBot ℕ∞) := hn V
    _ ≤ ((hs.toFinset.sup n : ℕ) : WithBot ℕ∞) :=
        Nat.cast_le.2 (Finset.le_sup (f := n) (hs.mem_toFinset.mpr hV))

/-- **A scheme proper over a field has finite dimension.** A proper morphism is quasi-compact
and locally of finite type, and the spectrum of a field is quasi-compact. -/
theorem topologicalKrullDim_ne_top_of_isProper (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] : topologicalKrullDim X ≠ ⊤ :=
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  topologicalKrullDim_ne_top_of_locallyOfFiniteType k f

/-- **The support of a sheaf of modules on a scheme proper over a field has finite dimension**,
being a subspace of the scheme. -/
theorem topologicalKrullDim_supp_ne_top (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules) :
    topologicalKrullDim (SheafOfModules.supp F) ≠ ⊤ :=
  ne_top_of_le_ne_top (topologicalKrullDim_ne_top_of_isProper k f)
    (topologicalKrullDim_subspace_le X (SheafOfModules.supp F))

/-- **The dimension of the support of a sheaf of modules, as a natural number**: the measure the
induction of [Stacks, Tag 0BEM] descends on. The value on empty support is `0`, which is junk —
the dimension of the empty space is `⊥` — and is never used: the empty-support case of the tag
is closed separately by
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_supp_eq_empty`. -/
noncomputable def natDimSupp {X : Scheme.{u}} (F : X.Modules) : ℕ :=
  ((topologicalKrullDim (SheafOfModules.supp F)).unbotD 0).toNat

/-- **On nonempty support the measure is the dimension of the support.** This is the hypothesis
`hdim` of `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf`, discharged. -/
theorem coe_natDimSupp_eq (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] (F : X.Modules) (hF : SheafOfModules.supp F ≠ ∅) :
    ((natDimSupp F : ℕ) : WithBot ℕ∞) = topologicalKrullDim (SheafOfModules.supp F) :=
  coe_unbotD_toNat_eq (fun h => hF ((topologicalKrullDim_supp_eq_bot_iff F).1 h))
    (topologicalKrullDim_supp_ne_top k f F)

/-- **[Stacks, Tag 0BEM] from its two geometric inputs alone.** This is
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf` with the descent measure instantiated as
the dimension of the support (`AlgebraicGeometry.natDimSupp`) and its bound `hdim` discharged by
`AlgebraicGeometry.coe_natDimSupp_eq`.

What remains are exactly the source's own two geometric inputs, one per paragraph of its proof:
`hbase` is Tag 0AYT on zero-dimensional support, and `hstep` is the first-difference identity it
obtains from a regular meromorphic section of `𝓛_i` and its ideal of denominators. Everything
else in Tag 0BEM is discharged. -/
theorem exists_eulerPolynomial_twistedSheaf_of_natDimSupp (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] {r : ℕ} (L : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
    (hbase : ∀ (G : X.Modules) (hG : SheafOfModules.IsCoherent G), natDimSupp G = 0 →
      ∃ P : MvPolynomial (Fin r) ℚ, P.totalDegree ≤ 0 ∧
        ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
          = (@eulerCharacteristic k _ X f _ (twistedSheaf G L n)
              (@twistedSheaf_isCoherent X r G L _ hG n) : ℚ))
    (hstep : ∀ (G : X.Modules) (hG : SheafOfModules.IsCoherent G), natDimSupp G ≠ 0 →
      ∀ i : Fin r,
      ∃ (G₁ G₂ : X.Modules) (hG₁ : SheafOfModules.IsCoherent G₁)
        (hG₂ : SheafOfModules.IsCoherent G₂),
        natDimSupp G₁ < natDimSupp G ∧ natDimSupp G₂ < natDimSupp G ∧
        ∀ n : Fin r → ℤ,
          (@eulerCharacteristic k _ X f _ (twistedSheaf G L (Function.update n i (n i + 1)))
              (@twistedSheaf_isCoherent X r G L _ hG _) : ℚ)
            - (@eulerCharacteristic k _ X f _ (twistedSheaf G L n)
                (@twistedSheaf_isCoherent X r G L _ hG n) : ℚ)
            = (@eulerCharacteristic k _ X f _ (twistedSheaf G₁ L n)
                (@twistedSheaf_isCoherent X r G₁ L _ hG₁ n) : ℚ)
              - (@eulerCharacteristic k _ X f _ (twistedSheaf G₂ L n)
                  (@twistedSheaf_isCoherent X r G₂ L _ hG₂ n) : ℚ))
    (F : X.Modules) (hF : SheafOfModules.IsCoherent F) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤
        topologicalKrullDim (SheafOfModules.supp F)) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
        = (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
            (@twistedSheaf_isCoherent X r F L _ hF n) : ℚ) :=
  exists_eulerPolynomial_twistedSheaf k f L natDimSupp hbase hstep F hF
    fun hsupp => le_of_eq (coe_natDimSupp_eq k f F hsupp)

end AlgebraicGeometry

end
