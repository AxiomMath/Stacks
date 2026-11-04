module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulGlobalHomCochain
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtComputation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InternalHomOfProductOfUnits
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.LocalKernel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.InternalHomTermwiseSplitTarget

/-!
# The tower of the Koszul formula of Tag 0A0E is the Koszul complex with coefficients

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪`, let `ℱ` be a sheaf
of `𝒪`-modules and let `K^n = K(𝒪, f_1^{n+1}, …, f_r^{n+1})` be the Koszul complex
`AlgebraicGeometry.RingedSite.koszulPowerComplex` of [Stacks, Tag 0913], in the grading of that
tag: `∏_{|S| = p} 𝒪` in degree `p` for `0 ≤ p ≤ r`.

The tower of the Koszul formula of [Stacks, Tag 0A0E] —
`AlgebraicGeometry.RingedSite.tensorDerivedDualSystem` at the Koszul tower — is
`n ↦ K ⊗^𝐋_𝒪 (K^n)^∨`, the derived tensor products with the `𝒪`-duals `Hom_𝒪(K^n, 𝒪)`, which
live in degrees `-r, …, 0`. This file identifies that tower, at `K = ℱ[0]`, with the tower of
Koszul complexes with coefficients in `ℱ`,
`AlgebraicGeometry.RingedSite.koszulPowerComplexOn` — the only computable sheaf Koszul complex
of this library — **shifted by `r`**:

`ℱ ⊗^𝐋_𝒪 (K^n)^∨  ≅  Q(K(𝒪, f_1^{n+1}, …, f_r^{n+1}) ⊗ ℱ)[r]`,  naturally in `n`.

The shift by `r` is not a defect of the comparison: it is the grading discrepancy that the
"What this leaves open" section of `KoszulSectionsProjection.lean` records, and it is forced.
The dual `(K^n)^∨` is concentrated in degrees `-r, …, 0` with `H^0` the quotient
`ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ`, while `koszulPowerComplexOn` is concentrated in degrees
`0, …, r` with that quotient in degree `r`; the Koszul complex is self-dual only up to the shift
by `r` and a sign twist, which is what the file proves.

For the same reason the transitions of the two towers are **not** those of
`AlgebraicGeometry.RingedSite.koszulPowerSystemOn`, which is a direct system: dualizing the
Koszul tower reverses it, and under the complement reindexing the transition from the `(n+2)`-nd
to the `(n+1)`-st level multiplies the factor indexed by `T` by `∏_{i ∉ T} f_i`. That inverse
system is `AlgebraicGeometry.RingedSite.koszulDualSystemOn`.

## Main definitions

* `AlgebraicGeometry.RingedSite.termDualIso`: the `𝒪`-dual of a term of an alternating Čech
  complex is the product of the duals of its factors, with the projections given by
  precomposition with the inclusions of the factors.
* `CategoryTheory.AlternatingCech.dualSign`: the sign
  `ε_A = (-1)^{∑_{j ∈ A} j + (0 + 1 + ⋯ + #A)}` by which the self-duality of the Koszul complex
  is twisted, and `CategoryTheory.AlternatingCech.complEquiv`, complementation as a bijection
  between the indices of complementary cardinalities.
* `AlgebraicGeometry.RingedSite.koszulDualIsoAt` and
  `AlgebraicGeometry.RingedSite.koszulDualComplexIsoAt`: the degreewise comparison, and
  `AlgebraicGeometry.RingedSite.koszulDualComplexIsoCoeff`: **the comparison of complexes**
  `SheafHom•_𝒪(K^n, ℱ[0]) ≅ (K^n ⊗ ℱ)[r]`.
* `AlgebraicGeometry.RingedSite.koszulDualSystemOn`: the dual Koszul tower with coefficients, as
  an inverse system of complexes, and
  `AlgebraicGeometry.RingedSite.koszulDualSystemComplexIso`: **the comparison of towers of
  complexes.**
* `AlgebraicGeometry.RingedSite.koszulTensorDualSystemCoefficientIso`: **the identification of
  the tower of [Stacks, Tag 0A0E] at a sheaf of modules with the shifted dual Koszul tower with
  coefficients**, and `AlgebraicGeometry.RingedSite.koszulTensorDualCoefficientIso`, the same at
  a fixed `n`.

## Main results

* `AlgebraicGeometry.RingedSite.d_comp_homDegreeProjection`: **the differential of the internal
  Hom complex of [Stacks, Tag 0A8Z], read against the product description of its terms** of
  [Stacks, Tag 08JH]. The degree-`n` term of `SheafHom•(E, F)` is the product over `q` of
  `SheafHom(E^{-q}, F^{n-q})` by `AlgebraicGeometry.RingedSite.homDegreeIsLimit`; this says that
  its differential is, in that description, `d_F ∘ -` plus `(-1)^{n+1}` times `- ∘ d_E`.
  `AlgebraicGeometry.RingedSite.homDegreeIsoSingle_d` is the case of a target concentrated in
  degree zero, where only the second term survives, and
  `AlgebraicGeometry.RingedSite.homDegreeIsoSingle_homMap` the companion statement for a
  morphism of sources.
* `AlgebraicGeometry.RingedSite.internalHomPre_koszulScalar`: **precomposition with
  multiplication by a monomial in the `f_i` is multiplication by that monomial** on the internal
  Hom sheaf out of the structure sheaf. This is what makes the dual of the Koszul system a
  Koszul system again, with coefficients in `Hom_𝒪(𝒪, ℱ)`.
* `AlgebraicGeometry.RingedSite.internalHomPre_d_comp_koszulDualFactor`: **the `𝒪`-dual of the
  Koszul differential is the contraction.**
* `CategoryTheory.AlternatingCech.dualSign_mul_cechSign`: **the sign identity behind the
  self-duality**, and `AlgebraicGeometry.RingedSite.koszulDualIsoAt_d`: **the differential
  square** it makes commute.
* `AlgebraicGeometry.RingedSite.koszulDualIsoAt_trans`: the same for the transitions of the two
  towers, where no sign and no reindexing enter.

## What this closes, and what it does not

The section "What this leaves open" of `KoszulSectionsProjection.lean` names two missing inputs
for the derived form of the projection formula against the Koszul complexes. The first,
K-flatness of the `𝒪`-dual of the Koszul complex, **is not missing**: it is
`AlgebraicGeometry.RingedSite.isKFlat_koszulPowerDualComplex` of `KoszulKFlat.lean`, whose own
module documentation already records that note as stale. The second — the identification of the
dual with `koszulPowerComplexOn` — is what this file proves, and it is proved through the
internal Hom complex rather than through the total tensor complex: that route needs the
*left* tensor factor to be K-flat, which the arbitrary coefficient sheaf is not.

Nothing here carries a `@[stacks]` attribute. [Stacks, Tag 0A0E] is registered on
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem_completion`
of `KoszulPerfectDual.lean`, and what is proved here is an identification of the tower appearing
in that formula, not the formula.

## Implementation notes

The internal Hom complex of [Stacks, Tag 0A8Z] is produced by `Classical.choice`, so its terms
and differential are opaque; everything below goes through the characterising data
`AlgebraicGeometry.RingedSite.SheafHomComplex.sectionsIso` and the product description
`AlgebraicGeometry.RingedSite.homDegreeProjection` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/StrictlyPerfect/HomComplexOfAStrictlyPerfectComplex.lean`. The proof of `d_comp_homDegreeProjection` is the
pattern of `AlgebraicGeometry.RingedSite.homUnitEvaluation_d` of `StacksFrontier/CategoryTheory/Sites/Cohomology/StrictlyPerfect/InternalHomUnitSource.lean`:
the cochain identity `CochainComplex.HomComplex.δ_v` is stated once for an arbitrary cochain and
then applied with `congrArg`, rather than rewritten in a goal that mentions a section of an
opaque term — such a goal is not type-correct at `implicit` transparency, so no `rw` can touch
it.

**Two spellings of one object, and why the statements are ascribed.** A dual of a Koszul term is
a product of copies of `Hom_𝒪(𝒪, ℱ)`, but the inclusion of a factor has target
`Hom_𝒪((K^n)^p-factor, ℱ)` and the Koszul complex with coefficients spells the same object as
`(koszulPowerFunctorOn …).obj S`. These are definitionally equal and not syntactically equal, so
a goal mixing them is not type-correct at `implicit` transparency and `rw` fails on it. Every
statement below is therefore phrased in one spelling — `koszulDualFactor`, `koszulDualDiff`,
`koszulDualTransX` and `koszulDualTermIso` exist only to ascribe a type — and the passage between
spellings is always a `rfl` step or a term-mode `exact`, never a rewrite.

**Every degree is a free variable with an equation.** `AlternatingCech.d F p` has target
`term F (p+1)`, while a comparison of complexes meets `C.d i j` at arbitrary adjacent `i`, `j`;
`(-(m+1)) + 1` and `-m` are equal and not definitionally equal. The lemmas are therefore stated
with the degrees as variables constrained by equations, which `subst` and `omega` make canonical
inside the proof: `koszulDualTermIso_d` and `koszulDualComplexIsoAt_d` are the two instances.

The four `.val`-level lemmas `zsmul_val₀`, `units_zsmul_val₀`, `add_val_app_apply₀` and
`units_zsmul_val_app_apply₀` restate for an arbitrary sheaf of rings what
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/HomComplex.lean` and
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/EvaluatingSections.lean` prove `private`ly or only in the slice spelling; a `private`
declaration cannot be named from another module, and the cochain components of the internal Hom
complex live over the slice site, so the slice-only versions do not apply.

## References

* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.AlternatingCech

variable {r : ℕ}

/-- The triangular sign exponent. -/
def triangleSum (p : ℕ) : ℕ := ∑ i ∈ Finset.range (p + 1), i

/-- The triangular sum satisfies `triangleSum (p + 1) = triangleSum p + (p + 1)`. -/
theorem triangleSum_succ (p : ℕ) : triangleSum (p + 1) = triangleSum p + (p + 1) :=
  Finset.sum_range_succ _ _

/-- The sign by which the `𝒪`-dual of the Koszul complex is twisted. -/
def dualSign (A : Finset (Fin r)) : ℤ :=
  (-1) ^ ((∑ j ∈ A, (j : ℕ)) + triangleSum A.card)

/-- The dual sign squares to `1`. -/
theorem dualSign_mul_self (A : Finset (Fin r)) : dualSign A * dualSign A = 1 := by
  rw [dualSign, ← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

/-- Removing an element `k` of `B` changes the dual sign by `(-1) ^ (#B + k)`. -/
theorem dualSign_erase {B : Finset (Fin r)} {k : Fin r} (hk : k ∈ B) :
    dualSign B = dualSign (B.erase k) * (-1) ^ (B.card + (k : ℕ)) := by
  obtain ⟨c, hc⟩ : ∃ c, B.card = c + 1 :=
    ⟨B.card - 1, by have := Finset.card_pos.2 ⟨k, hk⟩; omega⟩
  have hcard : (B.erase k).card = c := by
    rw [Finset.card_erase_of_mem hk, hc]
    omega
  have hsum : ∑ j ∈ B, (j : ℕ) = (∑ j ∈ B.erase k, (j : ℕ)) + (k : ℕ) :=
    (Finset.sum_erase_add _ _ hk).symm
  rw [dualSign, dualSign, hcard, hsum, hc, triangleSum_succ, ← pow_add]
  congr 1
  omega

/-- The elements below `k` in `B` and in its complement together number `k`. -/
theorem filter_card_add_compl (B : Finset (Fin r)) (k : Fin r) :
    (B.filter (· < k)).card + (Bᶜ.filter (· < k)).card = (k : ℕ) := by
  classical
  have hdisj : Disjoint (B.filter (· < k)) (Bᶜ.filter (· < k)) :=
    Finset.disjoint_filter_filter (disjoint_compl_right)
  have hunion : (B.filter (· < k)) ∪ (Bᶜ.filter (· < k)) =
      Finset.univ.filter (· < k) := by
    rw [← Finset.filter_union, Finset.union_compl]
  rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have : Finset.univ.filter (fun j : Fin r => j < k) = Finset.Iio k := by
    ext j
    simp
  rw [this, Fin.card_Iio]

/-- The product of the Čech signs at `k` of a subset and of its complement is `(-1) ^ k`. -/
theorem cechSign_mul_compl (B : Finset (Fin r)) (k : Fin r) :
    Cech.cechSign B k * Cech.cechSign Bᶜ k = (-1) ^ (k : ℕ) := by
  rw [Cech.cechSign, Cech.cechSign, ← pow_add, filter_card_add_compl]

/-- **The sign identity behind the self-duality of the Koszul complex.** Multiplying the dual
twist at a subset `B` of cardinality `q + 1` by the Čech sign of the complement picks up
`(-1)^{q+1}` against the Čech sign of `B` itself. -/
theorem dualSign_mul_cechSign (q : ℤ) {B : Finset (Fin r)} (hB : (B.card : ℤ) = q + 1)
    {k : Fin r} (hk : k ∈ B) :
    dualSign B * Cech.cechSign (insert k Bᶜ) k =
      ((q + 1).negOnePow : ℤ) * (Cech.cechSign B k * dualSign (B.erase k)) := by
  have hsq : Cech.cechSign B k * Cech.cechSign B k = 1 := by
    rw [Cech.cechSign, ← pow_add]
    exact Even.neg_one_pow ⟨_, rfl⟩
  have hcompl : Cech.cechSign Bᶜ k = Cech.cechSign B k * (-1 : ℤ) ^ (k : ℕ) := by
    rw [← cechSign_mul_compl B k, ← mul_assoc, hsq, one_mul]
  have hpow : ((-1 : ℤ)) ^ (B.card + (k : ℕ)) * (-1 : ℤ) ^ (k : ℕ) =
      ((q + 1).negOnePow : ℤ) := by
    rw [← pow_add, show B.card + (k : ℕ) + (k : ℕ) = B.card + 2 * (k : ℕ) by ring, pow_add,
      pow_mul, neg_one_sq, one_pow, mul_one, ← Int.coe_negOnePow_natCast, hB]
  rw [Cech.cechSign_insert, dualSign_erase hk, hcompl]
  linear_combination (dualSign (B.erase k) * Cech.cechSign B k) * hpow

end CategoryTheory.AlternatingCech

namespace AlgebraicGeometry.RingedSite

open CochainComplex.HomComplex

universe w m

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A sum of morphisms of sheaves of modules acts on sections by addition. -/
theorem add_val_app_apply₀ {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (f g : A ⟶ B)
    (W : X.Cᵒᵖ) (x : A.val.obj W) :
    (f + g).val.app W x = f.val.app W x + g.val.app W x := by
  with_unfolding_all rfl

/-- A unit multiple of a morphism of sheaves of modules acts on sections by scaling. -/
theorem units_zsmul_val_app_apply₀
    {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : A ⟶ B) (c : ℤˣ)
    (W : X.Cᵒᵖ) (x : A.val.obj W) :
    (c • f).val.app W x = c • (f.val.app W x) :=
  zsmul_val_app_apply (c : ℤ) f W x

/-- Precomposition on internal Hom sheaves, on a section. -/
theorem internalHomPre_val_app_apply
    {A B C : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (g : A ⟶ B)
    (U : X.C) (a : (internalHomSheaf X B C).val.obj (op U)) :
    (internalHomPre X (C := C) g).val.app (op U) a =
      ((SheafOfModules.overFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map g).val ≫ a := rfl

/-- Precomposition on internal Hom sheaves, evaluated on a local section. -/
theorem internalHomPre_val_app_app_apply
    {A B C : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (g : A ⟶ B)
    (U : X.C) (a : (internalHomSheaf X B C).val.obj (op U)) (W : (Over U)ᵒᵖ)
    (y : ((SheafOfModules.overFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj A).val.obj W) :
    (((internalHomPre X (C := C) g).val.app (op U) a).app W) y =
      (a.app W) ((((SheafOfModules.overFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map g).val.app W) y) := rfl

/-- Postcomposition on internal Hom sheaves, on a section. -/
theorem internalHomPost_val_app_eq_comp
    {A B C : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (g : B ⟶ C)
    (U : X.C) (a : (internalHomSheaf X A B).val.obj (op U)) :
    (internalHomPost X (A := A) g).val.app (op U) a =
      a ≫ ((SheafOfModules.overFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map g).val := rfl

/-- An integer multiple of a morphism of sheaves of modules, on the underlying presheaves. -/
theorem zsmul_val₀ {C₀ : Type*} [Category C₀] {J : GrothendieckTopology C₀}
    {R : Sheaf J RingCat.{w}} {A B : SheafOfModules.{m} R} (c : ℤ) (f : A ⟶ B) :
    (c • f).val = c • f.val := by
  show (SheafOfModules.forget R).map (c • f) = _
  rw [Functor.map_zsmul]
  rfl

/-- A unit multiple of a morphism of sheaves of modules, on the underlying presheaves. -/
theorem units_zsmul_val₀ {C₀ : Type*} [Category C₀] {J : GrothendieckTopology C₀}
    {R : Sheaf J RingCat.{w}} {A B : SheafOfModules.{m} R} (c : ℤˣ) (f : A ⟶ B) :
    (c • f).val = c • f.val := zsmul_val₀ (c : ℤ) f

/-- Transport of a cochain component along an equality of the target degree. -/
theorem Cochain.v_transport {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜]
    {E F : CochainComplex 𝒜 ℤ} {t : ℤ} (z : Cochain E F t) (p q q' : ℤ)
    (hpq : p + t = q) (hpq' : p + t = q') :
    z.v p q' hpq' = z.v p q hpq ≫ eqToHom (congrArg F.X (show q = q' by omega)) := by
  obtain rfl : q = q' := by omega
  rw [eqToHom_refl, Category.comp_id]

/-- **The differential of the internal Hom complex, against the product projections.** -/
theorem d_comp_homDegreeProjection
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n Q : ℤ) :
    (sheafHomComplex X E F).obj.d n (n + 1) ≫ homDegreeProjection X E F (n + 1) (Q + 1) =
      homDegreeProjection X E F n (Q + 1) ≫
          internalHomPost X (F.d (n - (Q + 1)) (n + 1 - (Q + 1))) +
        (n + 1).negOnePow • (homDegreeProjection X E F n Q ≫
          internalHomPre X (E.d (-(Q + 1)) (-Q)) ≫
            internalHomPost X (eqToHom (congrArg F.X
              (show n - Q = n + 1 - (Q + 1) by omega)))) := by
  ext U s
  have hc : AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U.unop).hom.f (n + 1))
        (((sheafHomComplex X E F).obj.d n (n + 1)).val.app U s) =
      δ n (n + 1) (AddCommGrpCat.Hom.hom
        (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n) s) :=
    (congrArg (fun z => AddCommGrpCat.Hom.hom z s)
      (((sheafHomComplex X E F).sectionsIso U.unop).hom.comm n (n + 1))).symm
  have key : ∀ z : Cochain (restrictComplex X E U.unop) (restrictComplex X F U.unop) n,
      (δ n (n + 1) z).v (-(Q + 1)) (n + 1 - (Q + 1)) (by omega) =
        z.v (-(Q + 1)) (n - (Q + 1)) (by omega) ≫
            (restrictComplex X F U.unop).d (n - (Q + 1)) (n + 1 - (Q + 1)) +
          (n + 1).negOnePow • (((restrictComplex X E U.unop).d (-(Q + 1)) (-Q) ≫
            z.v (-Q) (n - Q) (by omega)) ≫ eqToHom (congrArg (restrictComplex X F U.unop).X
              (show n - Q = n + 1 - (Q + 1) by omega))) := fun z => by
    rw [δ_v n (n + 1) rfl z (-(Q + 1)) (n + 1 - (Q + 1)) (by omega) (n - (Q + 1)) (-Q)
      (by omega) (by omega),
      Cochain.v_transport z (-Q) (n - Q) (n + 1 - (Q + 1)) (by omega) (by omega),
      Category.assoc]
  simp only [comp_val_app_apply' X, add_val_app_apply₀ X, units_zsmul_val_app_apply₀ X]
  conv_rhs => rw [internalHomPost_val_app_eq_comp, internalHomPost_val_app_eq_comp,
    internalHomPre_val_app_apply, homDegreeProjection_val_app_apply,
    homDegreeProjection_val_app_apply]
  conv_lhs => rw [homDegreeProjection_val_app_apply, hc]
  have h := key (AddCommGrpCat.Hom.hom
    (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n) s)
  refine (congrArg SheafOfModules.Hom.val h).trans ?_
  rw [SheafOfModules.add_val, units_zsmul_val₀, SheafOfModules.comp_val,
    SheafOfModules.comp_val, SheafOfModules.comp_val,
    Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_obj_d, eqToHom_map]
  rfl

/-- Postcomposition with a transport of the target is a transport. -/
theorem internalHomPost_eqToHom
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {B B' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (h : B = B') :
    internalHomPost X (A := A) (eqToHom h) =
      eqToHom (congrArg (internalHomSheaf X A) h) := by
  subst h
  rw [eqToHom_refl, internalHomPost_id, eqToHom_refl]

/-- Precomposition on internal Hom sheaves commutes with a transport of the target. -/
theorem internalHomPre_eqToHom
    {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (g : A ⟶ B)
    {C C' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (h : C = C') :
    internalHomPre X (C := C) g ≫ eqToHom (congrArg (internalHomSheaf X A) h) =
      eqToHom (congrArg (internalHomSheaf X B) h) ≫ internalHomPre X (C := C') g := by
  subst h
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]

/-- The complex concentrated in degree zero at a sheaf of modules. -/
abbrev singleSheafComplex (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ComplexShape.up ℤ) 0).obj N

/-- The degreewise identification `homDegreeIsoSingle` is a projection followed by a transport. -/
private theorem homDegreeIsoSingle_hom_eq (X : RingedSite.{u, u, u})
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (m : ℤ) :
    (homDegreeIsoSingle X E N m).hom =
      homDegreeProjection X E (singleSheafComplex X N) m m ≫
        eqToHom (congrArg (internalHomSheaf X (E.X (-m)))
          (show (singleSheafComplex X N).X (m - m) = N by rw [sub_self]; rfl)) := rfl

/-- **The differential of the internal Hom complex into a sheaf in degree zero**, read through
the degreewise identification `homDegreeIsoSingle`: it is the dual of the differential of the
source, up to the sign of the Hom complex. -/
theorem homDegreeIsoSingle_d
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (m : ℤ) :
    (sheafHomComplex X E (singleSheafComplex X N)).obj.d m (m + 1) ≫
        (homDegreeIsoSingle X E N (m + 1)).hom =
      (m + 1).negOnePow • ((homDegreeIsoSingle X E N m).hom ≫
        internalHomPre X (E.d (-(m + 1)) (-m))) := by
  have hcore : (homDegreeProjection X E (singleSheafComplex X N) m m ≫
        internalHomPre X (E.d (-(m + 1)) (-m)) ≫
          internalHomPost X (eqToHom (congrArg (singleSheafComplex X N).X
            (show m - m = m + 1 - (m + 1) by omega)))) ≫
          eqToHom (congrArg (internalHomSheaf X (E.X (-(m + 1))))
            (show (singleSheafComplex X N).X (m + 1 - (m + 1)) = N by rw [sub_self]; rfl)) =
      (homDegreeProjection X E (singleSheafComplex X N) m m ≫
          eqToHom (congrArg (internalHomSheaf X (E.X (-m)))
            (show (singleSheafComplex X N).X (m - m) = N by rw [sub_self]; rfl))) ≫
        internalHomPre X (E.d (-(m + 1)) (-m)) := by
    rw [Category.assoc, Category.assoc, internalHomPost_eqToHom, eqToHom_trans,
      internalHomPre_eqToHom, ← Category.assoc]
    congr 1
    rw [sub_self]
    rfl
  rw [homDegreeIsoSingle_hom_eq, homDegreeIsoSingle_hom_eq, ← Category.assoc,
    d_comp_homDegreeProjection X E (singleSheafComplex X N) m m,
    HomologicalComplex.single_obj_d, internalHomPost_zero', comp_zero, zero_add]
  simp only [Units.smul_def]
  rw [Preadditive.zsmul_comp, hcore]

/-- **The map of internal Hom complexes induced by a morphism of sources**, read through the
degreewise identification `homDegreeIsoSingle` for a target concentrated in degree zero: it is
precomposition with the corresponding component of that morphism. -/
theorem homDegreeIsoSingle_homMap
    {E E' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : E' ⟶ E) (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (m : ℤ) :
    (homMap X k (𝟙 (singleSheafComplex X N))).f m ≫ (homDegreeIsoSingle X E' N m).hom =
      (homDegreeIsoSingle X E N m).hom ≫ internalHomPre X (k.f (-m)) := by
  rw [homDegreeIsoSingle_hom_eq, homDegreeIsoSingle_hom_eq, ← Category.assoc,
    homDegreeProjection_homMap, Category.assoc,
    internalHomPre_eqToHom, ← Category.assoc]
  rw [sub_self]
  rfl

section Dual

open CategoryTheory.AlternatingCech

attribute [local instance] hasFiniteBiproducts_sheafOfModules

variable {r : ℕ}

/-- **The `𝒪`-dual of a degree of an alternating Čech complex is the product of the duals of its
factors.** The projections are precomposition with the inclusions of the factors. -/
def termDualIso
    (F : Finset (Fin r) ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (p : ℤ)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    internalHomSheaf X (term F p) N ≅
      ∏ᶜ fun S : Idx r p => internalHomSheaf X (F.obj S.1) N where
  hom := Limits.Pi.lift fun S => internalHomPre X (termι F S)
  inv := ∑ S : Idx r p, Limits.Pi.π (fun T : Idx r p => internalHomSheaf X (F.obj T.1) N) S ≫
    internalHomPre X (Limits.Pi.π (fun T : Idx r p => F.obj T.1) S)
  hom_inv_id := by
    have hstep : ∀ S : Idx r p,
        (Limits.Pi.lift fun T : Idx r p => internalHomPre X (C := N) (termι F T)) ≫
            (Limits.Pi.π (fun T : Idx r p => internalHomSheaf X (F.obj T.1) N) S ≫
              internalHomPre X (Limits.Pi.π (fun T : Idx r p => F.obj T.1) S)) =
          internalHomPre X (Limits.Pi.π (fun T : Idx r p => F.obj T.1) S ≫ termι F S) := fun S => by
      rw [← Category.assoc, Limits.Pi.lift_π, internalHomPre_comp]
    rw [Preadditive.comp_sum, Finset.sum_congr rfl fun S _ => hstep S, ← internalHomPre_sum,
      π_comp_termι_sum, internalHomPre_id]
  inv_hom_id := by
    refine Limits.Pi.hom_ext _ _ fun S' => ?_
    have hstep : ∀ S : Idx r p,
        (Limits.Pi.π (fun T : Idx r p => internalHomSheaf X (F.obj T.1) N) S ≫
              internalHomPre X (Limits.Pi.π (fun T : Idx r p => F.obj T.1) S)) ≫
            internalHomPre X (C := N) (termι F S') =
          Limits.Pi.π (fun T : Idx r p => internalHomSheaf X (F.obj T.1) N) S ≫
            internalHomPre X (termι F S' ≫ Limits.Pi.π (fun T : Idx r p => F.obj T.1) S) :=
        fun S => by rw [Category.assoc, internalHomPre_comp]
    rw [Category.assoc, Limits.Pi.lift_π, Category.id_comp, Preadditive.sum_comp,
      Finset.sum_congr rfl fun S _ => hstep S, Finset.sum_eq_single S']
    · rw [termι_comp_π_self, internalHomPre_id, Category.comp_id]
    · intro S _ hS
      rw [termι_comp_π_of_ne F (Ne.symm hS), internalHomPre_zero, comp_zero]
    · exact fun h => absurd (Finset.mem_univ S') h

/-- The projections of `termDualIso`. -/
@[reassoc]
theorem termDualIso_hom_π
    (F : Finset (Fin r) ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (p : ℤ)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (S : Idx r p) :
    (termDualIso X F p N).hom ≫
        Limits.Pi.π (fun T : Idx r p => internalHomSheaf X (F.obj T.1) N) S =
      internalHomPre X (termι F S) :=
  Limits.Pi.lift_π _ _

end Dual

/-- Precomposition on internal Hom sheaves, as an additive map in the morphism. -/
def internalHomPreAddHom (A B C : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (A ⟶ B) →+ (internalHomSheaf X B C ⟶ internalHomSheaf X A C) :=
  AddMonoidHom.mk' (fun g => internalHomPre X g) (fun g g' => internalHomPre_add X g g')

/-- Precomposition on internal Hom sheaves is `ℤ`-linear in the morphism. -/
theorem internalHomPre_zsmul
    {A B C : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (c : ℤ) (g : A ⟶ B) :
    internalHomPre X (C := C) (c • g) = c • internalHomPre X (C := C) g :=
  map_zsmul (internalHomPreAddHom X A B C) c g

section DualDifferential

open CategoryTheory.AlternatingCech

attribute [local instance] hasFiniteBiproducts_sheafOfModules

variable {r : ℕ}

/-- **The `𝒪`-dual of the alternating Čech differential is the contraction.** Read through
`termDualIso`, the dual of `d` has, at the factor indexed by `S`, the signed sum over the
elements `i ∉ S` of the transition out of the factor indexed by `S ∪ \{i\}`. -/
theorem internalHomPre_d_comp_termDualIso
    (F : Finset (Fin r) ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (p : ℤ) (S : Idx r p) :
    internalHomPre X (C := N) (AlternatingCech.d F p) ≫ (termDualIso X F p N).hom ≫
        Limits.Pi.π (fun T : Idx r p => internalHomSheaf X (F.obj T.1) N) S =
      (termDualIso X F (p + 1) N).hom ≫ ∑ i : {i : Fin r // i ∉ S.1},
        Cech.cechSign (insertIdx S i).1 i.1 •
          (Limits.Pi.π (fun T : Idx r (p + 1) => internalHomSheaf X (F.obj T.1) N)
              (insertIdx S i) ≫
            internalHomPre X (F.map (homOfLE (subset_insertIdx S i)))) := by
  have hstep : ∀ i : {i : Fin r // i ∉ S.1},
      internalHomPre X (C := N) (Cech.cechSign (insertIdx S i).1 i.1 •
          (F.map (homOfLE (subset_insertIdx S i)) ≫ termι F (insertIdx S i))) =
        (termDualIso X F (p + 1) N).hom ≫ (Cech.cechSign (insertIdx S i).1 i.1 •
          (Limits.Pi.π (fun T : Idx r (p + 1) => internalHomSheaf X (F.obj T.1) N)
              (insertIdx S i) ≫
            internalHomPre X (F.map (homOfLE (subset_insertIdx S i))))) := fun i => by
    rw [internalHomPre_zsmul, ← internalHomPre_comp, Preadditive.comp_zsmul, ← Category.assoc,
      termDualIso_hom_π]
  rw [termDualIso_hom_π, internalHomPre_comp, termι_comp_d, internalHomPre_sum,
    Finset.sum_congr rfl fun i _ => hstep i, ← Preadditive.comp_sum]

end DualDifferential

section Complement

open CategoryTheory.AlternatingCech

variable {r : ℕ}

/-- **The complement of a subset**, as an index of complementary cardinality. -/
def Idx.compl {p q : ℤ} (hpq : p + q = (r : ℤ)) (S : Idx r p) : Idx r q :=
  ⟨S.1ᶜ, by
    have h2 := S.2
    have hle : S.1.card ≤ r := by
      simpa using Finset.card_le_univ S.1
    have hc : (S.1ᶜ.card : ℤ) = (r : ℤ) - (S.1.card : ℤ) := by
      rw [Finset.card_compl]
      simp only [Fintype.card_fin]
      omega
    omega⟩

/-- The underlying subset of the complement index is the complement of the subset. -/
@[simp]
theorem Idx.val_compl {p q : ℤ} (hpq : p + q = (r : ℤ)) (S : Idx r p) :
    (Idx.compl hpq S).1 = S.1ᶜ :=
  rfl

/-- **Complementation is a bijection between the indices of complementary cardinalities.** -/
def complEquiv {p q : ℤ} (hpq : p + q = (r : ℤ)) : Idx r p ≃ Idx r q where
  toFun := Idx.compl hpq
  invFun := Idx.compl (by omega : q + p = (r : ℤ))
  left_inv S := Subtype.ext (by simp)
  right_inv T := Subtype.ext (by simp)

/-- The complementation bijection sends an index to the complement of its subset. -/
@[simp]
theorem complEquiv_apply {p q : ℤ} (hpq : p + q = (r : ℤ)) (S : Idx r p) :
    (complEquiv hpq S).1 = S.1ᶜ :=
  rfl

end Complement

section KoszulScalarDual

open scoped IsMulCommutative


variable [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **Precomposition with multiplication by a monomial is multiplication by that monomial on the
internal Hom sheaf out of the structure sheaf.** -/
theorem internalHomPre_koszulScalar (e : Fin r → ℕ)
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    internalHomPre X (C := G) (koszulScalar X f e) =
      koszulScalarOn X f e (internalHomSheaf X
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) G) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun a => ?_))
  refine PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  have hscal : (koszulRingValue X f e (op W.unop.left) :
        (ORestr X.O.obj U.unop).obj W) =
      fRestr X.O.obj U.unop (koszulRingValue X f e U) W :=
    (koszulValue_map X f e W.unop.hom.op).symm
  have h1 : ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U.unop).map
        (koszulScalar X f e)).val.app W y =
      fRestr X.O.obj U.unop (koszulRingValue X f e U) W • y := by
    rw [← hscal]
    rfl
  exact Eq.trans (congrArg (ModuleCat.Hom.hom (a.app W)) h1) (map_smul _ _ _)

end KoszulScalarDual

section SignedReindex

variable {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜]

/-- **A signed reindexing of a product of copies of one object.** The factors are permuted by a
bijection of the index types and each is multiplied by a sign. -/
def signedPiIso {ι κ : Type} (e : κ ≃ ι) (sgn : κ → ℤ) (hsgn : ∀ k, sgn k * sgn k = 1) (M : 𝒜)
    [HasProduct (fun _ : ι => M)] [HasProduct (fun _ : κ => M)] :
    ∏ᶜ (fun _ : ι => M) ≅ ∏ᶜ (fun _ : κ => M) where
  hom := Pi.lift fun k => sgn k • Pi.π (fun _ : ι => M) (e k)
  inv := Pi.lift fun i => sgn (e.symm i) • Pi.π (fun _ : κ => M) (e.symm i)
  hom_inv_id := by
    refine Pi.hom_ext _ _ fun i => ?_
    rw [Category.assoc, Pi.lift_π, Preadditive.comp_zsmul, Pi.lift_π, smul_smul,
      e.apply_symm_apply, hsgn, one_smul, Category.id_comp]
  inv_hom_id := by
    refine Pi.hom_ext _ _ fun k => ?_
    rw [Category.assoc, Pi.lift_π, Preadditive.comp_zsmul, Pi.lift_π, smul_smul,
      e.symm_apply_apply, hsgn, one_smul, Category.id_comp]

/-- The `k`-th component of the signed reindexing is `sgn k` times the projection onto the
factor `e k`. -/
@[reassoc]
theorem signedPiIso_hom_π {ι κ : Type} (e : κ ≃ ι) (sgn : κ → ℤ)
    (hsgn : ∀ k, sgn k * sgn k = 1) (M : 𝒜)
    [HasProduct (fun _ : ι => M)] [HasProduct (fun _ : κ => M)] (k : κ) :
    (signedPiIso e sgn hsgn M).hom ≫ Pi.π (fun _ : κ => M) k =
      sgn k • Pi.π (fun _ : ι => M) (e k) :=
  Pi.lift_π _ _

end SignedReindex

section KoszulDual

open CategoryTheory.AlternatingCech

open scoped IsMulCommutative

attribute [local instance]
  hasFiniteBiproducts_sheafOfModules

variable [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (ℱ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ)

/-- `Hom_𝒪(𝒪, ℱ)`, the sheaf of modules in which the `𝒪`-dual of the Koszul complex takes its
coefficients. -/
abbrev unitHomSheaf : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  internalHomSheaf X (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℱ

/-- **The dual of the inclusion of a factor of a Koszul term**: the `S`-component of the
`𝒪`-dual of the degree-`p` term, as a morphism to `Hom_𝒪(𝒪, ℱ)`. -/
def koszulDualFactor (p : ℤ) (S : Idx r p) :
    internalHomSheaf X (term (koszulPowerFunctor X f n) p) ℱ ⟶ unitHomSheaf X ℱ :=
  internalHomPre X (termι (koszulPowerFunctor X f n) S)

/-- **The `𝒪`-dual of a term of the Koszul complex is the product of copies of `Hom_𝒪(𝒪, ℱ)`
indexed by the subsets of the complementary cardinality.** The identification carries the factor
indexed by a subset `S` to the factor indexed by its complement, twisted by
`CategoryTheory.AlternatingCech.dualSign`. The target is the degree-`q` term of
`AlgebraicGeometry.RingedSite.koszulPowerComplexOn` with coefficients in `Hom_𝒪(𝒪, ℱ)`, in the
spelling as a product of copies of one object. -/
def koszulDualIsoAt (p q : ℤ) (hpq : p + q = (r : ℤ)) :
    internalHomSheaf X (term (koszulPowerFunctor X f n) p) ℱ ≅
      ∏ᶜ fun _ : Idx r q => unitHomSheaf X ℱ :=
  termDualIso X (koszulPowerFunctor X f n) p ℱ ≪≫
    signedPiIso (complEquiv (show q + p = (r : ℤ) by omega)) (fun T : Idx r q => dualSign T.1)
      (fun T => dualSign_mul_self T.1) (unitHomSheaf X ℱ)

/-- **The projections of the dual identification**: at the factor indexed by `T` it is
precomposition with the inclusion of the factor indexed by the complement of `T`, times
`dualSign T`. -/
@[reassoc]
theorem koszulDualIsoAt_hom_π (p q : ℤ) (hpq : p + q = (r : ℤ)) (T : Idx r q) :
    (koszulDualIsoAt X f ℱ n p q hpq).hom ≫
        Pi.π (fun _ : Idx r q => unitHomSheaf X ℱ) T =
      dualSign T.1 • koszulDualFactor X f ℱ n p
        (Idx.compl (show q + p = (r : ℤ) by omega) T) := by
  have h : (koszulDualIsoAt X f ℱ n p q hpq).hom ≫
        Pi.π (fun _ : Idx r q => unitHomSheaf X ℱ) T =
      (termDualIso X (koszulPowerFunctor X f n) p ℱ).hom ≫
        ((signedPiIso (complEquiv (show q + p = (r : ℤ) by omega))
            (fun T : Idx r q => dualSign T.1) (fun T => dualSign_mul_self T.1)
            (unitHomSheaf X ℱ)).hom ≫
          Pi.π (fun _ : Idx r q => unitHomSheaf X ℱ) T) := rfl
  exact h.trans (Eq.trans (congrArg
    (fun z => (termDualIso X (koszulPowerFunctor X f n) p ℱ).hom ≫ z)
    (signedPiIso_hom_π (complEquiv (show q + p = (r : ℤ) by omega))
      (fun T : Idx r q => dualSign T.1) (fun T => dualSign_mul_self T.1)
      (unitHomSheaf X ℱ) T))
    (Eq.trans (Preadditive.comp_zsmul _ _ _)
      (congrArg (fun z => dualSign T.1 • z)
        (termDualIso_hom_π X (koszulPowerFunctor X f n) p ℱ _))))

/-- **The Koszul differential with coefficients in `Hom_𝒪(𝒪, ℱ)`**, read between the products of
copies of that sheaf. This is the differential of
`AlgebraicGeometry.RingedSite.koszulPowerComplexOn`. -/
def koszulDualDiff (q : ℤ) :
    (∏ᶜ fun _ : Idx r q => unitHomSheaf X ℱ) ⟶
      ∏ᶜ fun _ : Idx r (q + 1) => unitHomSheaf X ℱ :=
  AlternatingCech.d (koszulPowerFunctorOn X f (unitHomSheaf X ℱ) n) q

/-- The components of the Koszul differential with coefficients: into the factor indexed by `B`
it is the signed sum, over the elements `k` of `B`, of multiplication by `f_k^{n+1}` out of the
factor indexed by `B ∖ \{k\}`. -/
@[reassoc]
theorem koszulDualDiff_π (q : ℤ) (B : Idx r (q + 1)) :
    koszulDualDiff X f ℱ n q ≫ Pi.π (fun _ : Idx r (q + 1) => unitHomSheaf X ℱ) B =
      ∑ k ∈ B.1.attach, Cech.cechSign B.1 k.1 •
        (Pi.π (fun _ : Idx r q => unitHomSheaf X ℱ) (Idx.erase B k) ≫
          koszulScalarOn X f (koszulExp n (Idx.erase B k).1 B.1) (unitHomSheaf X ℱ)) :=
  d_comp_pi (koszulPowerFunctorOn X f (unitHomSheaf X ℱ) n) q B

/-- **The `𝒪`-dual of the alternating Čech differential of the Koszul system is the
contraction.** Out of the dual of the factor indexed by `S` it is the signed sum, over the
elements `i` not in `S`, of multiplication by `f_i^{n+1}` after the dual of the factor indexed
by `S ∪ \{i\}`. -/
theorem internalHomPre_d_comp_koszulDualFactor (j : ℤ) (S : Idx r j) :
    internalHomPre X (C := ℱ) (AlternatingCech.d (koszulPowerFunctor X f n) j) ≫
        koszulDualFactor X f ℱ n j S =
      ∑ i : {i : Fin r // i ∉ S.1}, Cech.cechSign (insertIdx S i).1 i.1 •
        (koszulDualFactor X f ℱ n (j + 1) (insertIdx S i) ≫
          koszulScalarOn X f (koszulExp n S.1 (insertIdx S i).1) (unitHomSheaf X ℱ)) := by
  refine Eq.trans (internalHomPre_comp X (termι (koszulPowerFunctor X f n) S) _) ?_
  refine Eq.trans (congrArg (fun φ => internalHomPre X (C := ℱ) φ)
    (termι_comp_d (F := koszulPowerFunctor X f n) S)) ?_
  refine Eq.trans (internalHomPre_sum X _ _) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Eq.trans (internalHomPre_zsmul X _ _) ?_
  refine congrArg (fun z => Cech.cechSign (insertIdx S i).1 i.1 • z) ?_
  refine Eq.trans (internalHomPre_comp X _ _).symm ?_
  exact congrArg (fun z => koszulDualFactor X f ℱ n (j + 1) (insertIdx S i) ≫ z)
    (internalHomPre_koszulScalar X f _ ℱ)

/-- **The dual identification carries the dual of the Koszul differential to the Koszul
differential with coefficients**, up to the sign `(-1)^{q+1}`. -/
theorem koszulDualIsoAt_d (j q : ℤ) (hq : (j + 1) + q = (r : ℤ)) :
    internalHomPre X (C := ℱ) (AlternatingCech.d (koszulPowerFunctor X f n) j) ≫
        (koszulDualIsoAt X f ℱ n j (q + 1) (by omega)).hom =
      ((q + 1).negOnePow : ℤ) • ((koszulDualIsoAt X f ℱ n (j + 1) q hq).hom ≫
        koszulDualDiff X f ℱ n q) := by
  refine Pi.hom_ext _ _ fun B => ?_
  have hB : (B.1.card : ℤ) = q + 1 := B.2
  have hc : (q + 1) + j = (r : ℤ) := by omega
  have hmem : ∀ x : Fin r, x ∉ (Idx.compl hc B).1 ↔ x ∈ B.1 := fun x => by simp
  rw [Category.assoc, koszulDualIsoAt_hom_π, Preadditive.comp_zsmul,
    internalHomPre_d_comp_koszulDualFactor, Finset.smul_sum, Preadditive.zsmul_comp,
    Category.assoc, koszulDualDiff_π, Preadditive.comp_sum, Finset.smul_sum,
    ← Finset.univ_eq_attach]
  refine Fintype.sum_equiv (Equiv.subtypeEquivRight hmem) _ _ fun i => ?_
  rw [Preadditive.comp_zsmul, ← Category.assoc, koszulDualIsoAt_hom_π, Preadditive.zsmul_comp,
    smul_smul, smul_smul, smul_smul]
  have hiB : i.1 ∈ B.1 := (hmem i.1).1 i.2
  have hidx : insertIdx (Idx.compl hc B) i =
      Idx.compl (show q + (j + 1) = (r : ℤ) by omega)
        (Idx.erase B ((Equiv.subtypeEquivRight hmem) i)) :=
    Subtype.ext (Finset.compl_erase).symm
  have hsets : (insert i.1 (B.1ᶜ)) \ (B.1ᶜ) = B.1 \ (B.1.erase i.1) := by
    ext x
    by_cases hx : x = i.1 <;> simp [hx, hiB]
  have hexp : koszulExp n (Idx.compl hc B).1
        (insertIdx (Idx.compl hc B) i).1 =
      koszulExp n (Idx.erase B ((Equiv.subtypeEquivRight hmem) i)).1 B.1 := by
    funext x
    exact if_congr (Iff.of_eq (congrArg (fun s : Finset (Fin r) => x ∈ s) hsets)) rfl rfl
  have hsign : dualSign B.1 *
        Cech.cechSign (insertIdx (Idx.compl hc B) i).1 i.1 =
      ((q + 1).negOnePow : ℤ) * (Cech.cechSign B.1 ((Equiv.subtypeEquivRight hmem) i).1 *
        dualSign (Idx.erase B ((Equiv.subtypeEquivRight hmem) i)).1) :=
    dualSign_mul_cechSign q hB hiB
  rw [hsign, hexp, hidx, mul_assoc]

/-- **The dual identification of a Koszul term, in the spelling of the two complexes.** This is
`AlgebraicGeometry.RingedSite.koszulDualIsoAt` with its source and target read as terms of the
Koszul complex and of the Koszul complex with coefficients, which is what the comparison of
complexes needs. -/
def koszulDualTermIso (p q : ℤ) (hpq : p + q = (r : ℤ)) :
    internalHomSheaf X ((koszulPowerComplex X f n).X p) ℱ ≅
      (koszulPowerComplexOn X f (unitHomSheaf X ℱ) n).X q :=
  koszulDualIsoAt X f ℱ n p q hpq

/-- **The dual identification carries the dual of the Koszul differential to the Koszul
differential with coefficients**, up to the sign `(-1)^{q'}`, at any spelling of the degrees. -/
theorem koszulDualTermIso_d (j p q q' : ℤ) (hjp : j + 1 = p) (hq : p + q = (r : ℤ))
    (hq' : j + q' = (r : ℤ)) :
    internalHomPre X (C := ℱ) ((koszulPowerComplex X f n).d j p) ≫
        (koszulDualTermIso X f ℱ n j q' hq').hom =
      ((q' : ℤ).negOnePow : ℤ) • ((koszulDualTermIso X f ℱ n p q hq).hom ≫
        (koszulPowerComplexOn X f (unitHomSheaf X ℱ) n).d q q') := by
  subst hjp
  obtain rfl : q' = q + 1 := by omega
  have hKd : (koszulPowerComplex X f n).d j (j + 1) =
      AlternatingCech.d (koszulPowerFunctor X f n) j :=
    complex_d (koszulPowerFunctor X f n) j
  have hCd : koszulDualDiff X f ℱ n q =
      (koszulPowerComplexOn X f (unitHomSheaf X ℱ) n).d q (q + 1) :=
    (complex_d (koszulPowerFunctorOn X f (unitHomSheaf X ℱ) n) q).symm
  refine Eq.trans (congrArg (fun φ : (koszulPowerComplex X f n).X j ⟶
      (koszulPowerComplex X f n).X (j + 1) =>
    internalHomPre X (C := ℱ) φ ≫ (koszulDualTermIso X f ℱ n j (q + 1) hq').hom) hKd) ?_
  refine Eq.trans (koszulDualIsoAt_d X f ℱ n j q hq) ?_
  exact congrArg (fun ψ => ((q + 1 : ℤ).negOnePow : ℤ) •
    ((koszulDualTermIso X f ℱ n (j + 1) q hq).hom ≫ ψ)) hCd

/-- **The degreewise comparison between the `𝒪`-dual of the Koszul complex and the Koszul
complex with coefficients in `Hom_𝒪(𝒪, ℱ)`**, at complementary degrees. -/
def koszulDualComplexIsoAt (m q : ℤ) (hq : -m + q = (r : ℤ)) :
    (sheafHomComplex X (koszulPowerComplex X f n) (singleSheafComplex X ℱ)).obj.X m ≅
      (koszulPowerComplexOn X f (unitHomSheaf X ℱ) n).X q :=
  homDegreeIsoSingle X (koszulPowerComplex X f n) ℱ m ≪≫
    koszulDualTermIso X f ℱ n (-m) q hq

/-- The degreewise comparison is `homDegreeIsoSingle` followed by `koszulDualTermIso`. -/
private theorem koszulDualComplexIsoAt_hom (X : RingedSite.{u, u, u})
    [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
    (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (ℱ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ) (m q : ℤ)
    (hq : -m + q = (r : ℤ)) :
    (koszulDualComplexIsoAt X f ℱ n m q hq).hom =
      (homDegreeIsoSingle X (koszulPowerComplex X f n) ℱ m).hom ≫
        (koszulDualTermIso X f ℱ n (-m) q hq).hom := rfl

/-- **The comparison is compatible with the differentials**, up to the sign `(-1)^r` of the
`r`-fold shift. -/
theorem koszulDualComplexIsoAt_d (m m' q q' : ℤ) (hm : m + 1 = m') (hq : -m + q = (r : ℤ))
    (hq' : -m' + q' = (r : ℤ)) :
    (sheafHomComplex X (koszulPowerComplex X f n) (singleSheafComplex X ℱ)).obj.d m m' ≫
        (koszulDualComplexIsoAt X f ℱ n m' q' hq').hom =
      (koszulDualComplexIsoAt X f ℱ n m q hq).hom ≫
        (((r : ℤ).negOnePow : ℤ) •
          (koszulPowerComplexOn X f (unitHomSheaf X ℱ) n).d q q') := by
  subst hm
  obtain rfl : q' = q + 1 := by omega
  have hsign : ((m + 1 : ℤ).negOnePow : ℤ) * ((q + 1 : ℤ).negOnePow : ℤ) =
      ((r : ℤ).negOnePow : ℤ) := by
    rw [← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨m + 1, by omega⟩
  rw [koszulDualComplexIsoAt_hom, koszulDualComplexIsoAt_hom, ← Category.assoc,
    homDegreeIsoSingle_d]
  simp only [Units.smul_def]
  rw [Preadditive.zsmul_comp, Category.assoc,
    koszulDualTermIso_d X f ℱ n (-(m + 1)) (-m) q (q + 1) (by omega) hq (by omega),
    Preadditive.comp_zsmul, smul_smul, hsign, Preadditive.comp_zsmul, Category.assoc]

/-- **The `𝒪`-dual of the Koszul complex is the `r`-fold shift of the Koszul complex with
coefficients in `Hom_𝒪(𝒪, ℱ)`.** This is the self-duality of the Koszul complex, with
coefficients: the internal Hom complex `SheafHom•_𝒪(K^n, ℱ[0])`, which lives in degrees
`-r, …, 0`, is the Koszul complex with coefficients of [Stacks, Tag 0913], which lives in
degrees `0, …, r`, shifted by `r`. -/
def koszulDualComplexIso :
    (sheafHomComplex X (koszulPowerComplex X f n) (singleSheafComplex X ℱ)).obj ≅
      (koszulPowerComplexOn X f (unitHomSheaf X ℱ) n)⟦(r : ℤ)⟧ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun m => koszulDualComplexIsoAt X f ℱ n m (m + (r : ℤ)) (by omega))
    (fun i j hij => by
      have hij' : i + 1 = j := hij
      rw [CochainComplex.shiftFunctor_obj_d']
      simp only [Units.smul_def]
      exact (koszulDualComplexIsoAt_d X f ℱ n i j (i + (r : ℤ)) (j + (r : ℤ)) hij'
        (by omega) (by omega)).symm)

/-! ### Transporting the coefficients along an isomorphism -/

/-- **An isomorphism of coefficient sheaves induces one of the Koszul systems with
coefficients.** The transition maps are multiplications by monomials in the chosen global
sections, which are natural in the sheaf of modules. -/
def koszulPowerFunctorOnMapIso
    {M M' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (α : M ≅ M') :
    koszulPowerFunctorOn X f M n ≅ koszulPowerFunctorOn X f M' n :=
  NatIso.ofComponents (fun _ => α) fun {S T} _ =>
    ((Stacks.SheafOfModules.globalSectionToEnd ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (koszulFamily X f (koszulExp n S T))).naturality α.hom).symm

/-- **An isomorphism of coefficient sheaves induces one of the Koszul complexes with
coefficients.** -/
def koszulPowerComplexOnMapIso
    {M M' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (α : M ≅ M') :
    koszulPowerComplexOn X f M n ≅ koszulPowerComplexOn X f M' n :=
  AlternatingCech.mapIso (koszulPowerFunctorOnMapIso X f n α)



/-! ### The dual Koszul tower with coefficients -/

/-- **The transition of the dual Koszul tower with coefficients**: at the factor indexed by `T`
it is multiplication by `∏_{i ∉ T} f_i`. This is what the `𝒪`-dual turns the transition
`AlgebraicGeometry.RingedSite.koszulPowerTrans` of the Koszul tower into, under the
identification of the factor indexed by `S` with the factor indexed by its complement. -/
def koszulDualTransOn (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (m : ℕ) :
    koszulPowerFunctorOn X f M (m + 1) ⟶ koszulPowerFunctorOn X f M m where
  app T := koszulScalarOn X f (fun i => if i ∈ Tᶜ then 1 else 0) M
  naturality {S T} g := by
    have hST : S ⊆ T := leOfHom g
    change koszulScalarOn X f (koszulExp (m + 1) S T) M ≫ koszulScalarOn X f _ M =
      koszulScalarOn X f _ M ≫ koszulScalarOn X f (koszulExp m S T) M
    rw [koszulScalarOn_comp, koszulScalarOn_comp]
    refine koszulScalarOn_congr X f (fun i => ?_) M
    by_cases hiT : i ∈ T
    · by_cases hiS : i ∈ S <;>
        simp [koszulExp, hiT, hiS, Finset.mem_sdiff, Pi.add_apply, Finset.mem_compl] <;>
        omega
    · simp [koszulExp, hiT, Finset.mem_sdiff, Pi.add_apply, Finset.mem_compl,
        show i ∉ S from fun hiS => hiT (hST hiS)]

/-- The transition of the dual Koszul tower of complexes with coefficients. -/
def koszulDualComplexOnMap (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (m : ℕ) :
    koszulPowerComplexOn X f M (m + 1) ⟶ koszulPowerComplexOn X f M m :=
  AlternatingCech.map (koszulDualTransOn X f M m)

/-- **The dual Koszul tower with coefficients**, as an inverse system of complexes: the Koszul
complexes with coefficients in `M` on the positive powers of `f_1, …, f_r`, with the transitions
that the `𝒪`-dual of the Koszul tower carries. -/
def koszulDualSystemOn (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  Functor.ofOpSequence (koszulDualComplexOnMap X f M)

/-- The `m`-th term of the dual Koszul tower with coefficients is
`koszulPowerComplexOn X f M m`. -/
@[simp]
theorem koszulDualSystemOn_obj
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (m : ℕ) :
    (koszulDualSystemOn X f M).obj (op m) = koszulPowerComplexOn X f M m :=
  rfl

/-- The transition from level `m + 1` to level `m` of the dual Koszul tower with coefficients is
`koszulDualComplexOnMap X f M m`. -/
theorem koszulDualSystemOn_map_succ
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (m : ℕ) :
    (koszulDualSystemOn X f M).map (homOfLE (Nat.le_add_right m 1)).op =
      koszulDualComplexOnMap X f M m :=
  Functor.ofOpSequence_map_homOfLE_succ _ m



/-! ### The comparison is compatible with the transitions of the two towers -/

/-- **The `𝒪`-dual of the transition of the Koszul tower is multiplication by the monomial
indexed by the subset.** -/
theorem internalHomPre_mapX_comp_koszulDualFactor (m : ℕ) (p : ℤ) (S : Idx r p) :
    internalHomPre X (C := ℱ) (AlternatingCech.mapX (koszulPowerTrans X f m) p) ≫
        koszulDualFactor X f ℱ m p S =
      koszulDualFactor X f ℱ (m + 1) p S ≫
        koszulScalarOn X f (fun i => if i ∈ S.1 then 1 else 0) (unitHomSheaf X ℱ) := by
  refine Eq.trans (internalHomPre_comp X (termι (koszulPowerFunctor X f m) S) _) ?_
  refine Eq.trans (congrArg (fun φ => internalHomPre X (C := ℱ) φ)
    (termι_comp_mapX (koszulPowerTrans X f m) S)) ?_
  refine Eq.trans (internalHomPre_comp X _ _).symm ?_
  exact congrArg (fun z => koszulDualFactor X f ℱ (m + 1) p S ≫ z)
    (internalHomPre_koszulScalar X f _ ℱ)

/-- The transition of the dual Koszul tower with coefficients, between the products of copies of
`Hom_𝒪(𝒪, ℱ)`. -/
def koszulDualTransX (m : ℕ) (q : ℤ) :
    (∏ᶜ fun _ : Idx r q => unitHomSheaf X ℱ) ⟶ ∏ᶜ fun _ : Idx r q => unitHomSheaf X ℱ :=
  AlternatingCech.mapX (koszulDualTransOn X f (unitHomSheaf X ℱ) m) q

/-- The components of that transition: at the factor indexed by `T` it is multiplication by
`∏_{i ∉ T} f_i`. -/
@[reassoc]
theorem koszulDualTransX_π (m : ℕ) (q : ℤ) (T : Idx r q) :
    koszulDualTransX X f ℱ m q ≫ Pi.π (fun _ : Idx r q => unitHomSheaf X ℱ) T =
      Pi.π (fun _ : Idx r q => unitHomSheaf X ℱ) T ≫
        koszulScalarOn X f (fun i => if i ∈ (T.1)ᶜ then 1 else 0) (unitHomSheaf X ℱ) :=
  mapX_comp_pi (koszulDualTransOn X f (unitHomSheaf X ℱ) m) T

/-- **The dual identification carries the dual of the transition of the Koszul tower to the
transition of the dual Koszul tower with coefficients.** No sign and no reindexing enter: both
transitions multiply the factor indexed by `T` by `∏_{i ∉ T} f_i`. -/
theorem koszulDualIsoAt_trans (m : ℕ) (p q : ℤ) (hpq : p + q = (r : ℤ)) :
    internalHomPre X (C := ℱ) (AlternatingCech.mapX (koszulPowerTrans X f m) p) ≫
        (koszulDualIsoAt X f ℱ m p q hpq).hom =
      (koszulDualIsoAt X f ℱ (m + 1) p q hpq).hom ≫ koszulDualTransX X f ℱ m q := by
  refine Pi.hom_ext _ _ fun T => ?_
  rw [Category.assoc, koszulDualIsoAt_hom_π, Preadditive.comp_zsmul,
    internalHomPre_mapX_comp_koszulDualFactor, Category.assoc, koszulDualTransX_π,
    ← Category.assoc, koszulDualIsoAt_hom_π, Preadditive.zsmul_comp]
  rfl

/-- **The transition square in the spelling of the two towers of complexes.** -/
theorem koszulDualTermIso_trans (m : ℕ) (p q : ℤ) (hpq : p + q = (r : ℤ)) :
    internalHomPre X (C := ℱ) ((koszulPowerComplexMap X f m).f p) ≫
        (koszulDualTermIso X f ℱ m p q hpq).hom =
      (koszulDualTermIso X f ℱ (m + 1) p q hpq).hom ≫
        (koszulDualComplexOnMap X f (unitHomSheaf X ℱ) m).f q :=
  koszulDualIsoAt_trans X f ℱ m p q hpq

/-- **The comparison of complexes is compatible with the transitions of the two towers.** -/
theorem koszulDualComplexIsoAt_trans (m : ℕ) (k q : ℤ) (hq : -k + q = (r : ℤ)) :
    (homMap X (koszulPowerComplexMap X f m) (𝟙 (singleSheafComplex X ℱ))).f k ≫
        (koszulDualComplexIsoAt X f ℱ m k q hq).hom =
      (koszulDualComplexIsoAt X f ℱ (m + 1) k q hq).hom ≫
        (koszulDualComplexOnMap X f (unitHomSheaf X ℱ) m).f q := by
  rw [koszulDualComplexIsoAt_hom, koszulDualComplexIsoAt_hom, ← Category.assoc,
    homDegreeIsoSingle_homMap, Category.assoc,
    koszulDualTermIso_trans, ← Category.assoc]



/-! ### The comparison at the coefficients `ℱ` -/

/-- **`Hom_𝒪(𝒪, ℱ) ≅ ℱ`.** -/
def unitHomSheafIso : unitHomSheaf X ℱ ≅ ℱ :=
  Stacks.SheafOfModules.InternalHom.unitSheafInternalHomIso X ℱ

/-- **The isomorphism of coefficient sheaves is compatible with the transitions of the dual
Koszul towers.** Both transitions are multiplications by monomials in the chosen global
sections, which are natural in the sheaf of modules. -/
theorem koszulPowerComplexOnMapIso_dualTrans
    {M M' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (α : M ≅ M')
    (m : ℕ) :
    koszulDualComplexOnMap X f M m ≫ (koszulPowerComplexOnMapIso X f m α).hom =
      (koszulPowerComplexOnMapIso X f (m + 1) α).hom ≫ koszulDualComplexOnMap X f M' m := by
  refine Eq.trans (AlternatingCech.map_comp _ _).symm ?_
  refine Eq.trans (congrArg AlternatingCech.map ?_) (AlternatingCech.map_comp _ _)
  refine NatTrans.ext (funext fun T => ?_)
  exact (Stacks.SheafOfModules.globalSectionToEnd ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (koszulFamily X f (fun i => if i ∈ Tᶜ then 1 else 0))).naturality α.hom |>.symm

/-- **The `𝒪`-dual of the Koszul complex is the `r`-fold shift of the Koszul complex with
coefficients in `ℱ`**: the self-duality of the Koszul complex, with coefficients in a sheaf of
modules. -/
def koszulDualComplexIsoCoeff :
    (sheafHomComplex X (koszulPowerComplex X f n) (singleSheafComplex X ℱ)).obj ≅
      (koszulPowerComplexOn X f ℱ n)⟦(r : ℤ)⟧ :=
  koszulDualComplexIso X f ℱ n ≪≫
    (shiftFunctor (CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (r : ℤ)).mapIso
      (koszulPowerComplexOnMapIso X f n (unitHomSheafIso X ℱ))

/-! ### The two towers of complexes -/

/-- **The tower `n ↦ SheafHom•_𝒪(K^n, ℱ[0])`** of internal Hom complexes against the Koszul
tower, as an inverse system of complexes of `𝒪`-modules. -/
def koszulSheafHomSystemOf :
    ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (koszulPowerSystem X f).op ⋙ (sheafHomComplexBifunctor X).flip.obj (singleSheafComplex X ℱ)

/-- The transition from level `m + 1` to level `m` of the tower of internal Hom complexes is
induced by precomposition with the Koszul transition `koszulPowerComplexMap X f m`. -/
theorem koszulSheafHomSystemOf_map_succ (m : ℕ) :
    (koszulSheafHomSystemOf X f ℱ).map (homOfLE (Nat.le_add_right m 1)).op =
      homMap X (koszulPowerComplexMap X f m) (𝟙 (singleSheafComplex X ℱ)) := by
  rw [show (koszulSheafHomSystemOf X f ℱ).map (homOfLE (Nat.le_add_right m 1)).op =
      ((sheafHomComplexBifunctor X).map
        (op ((koszulPowerSystem X f).map (homOfLE (Nat.le_add_right m 1))))).app
          (singleSheafComplex X ℱ) from rfl,
    koszulPowerSystem_map_succ]
  exact sheafHomComplexBifunctor_map_app X _ (singleSheafComplex X ℱ)

/-- **One step of the comparison of towers.** -/
theorem koszulDualComplexIsoCoeff_trans (m : ℕ) :
    homMap X (koszulPowerComplexMap X f m) (𝟙 (singleSheafComplex X ℱ)) ≫
        (koszulDualComplexIsoCoeff X f ℱ m).hom =
      (koszulDualComplexIsoCoeff X f ℱ (m + 1)).hom ≫
        (shiftFunctor (CochainComplex
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (r : ℤ)).map
          (koszulDualComplexOnMap X f ℱ m) := by
  refine HomologicalComplex.hom_ext _ _ fun k => ?_
  have hcomp : ∀ j : ℕ, (koszulDualComplexIsoCoeff X f ℱ j).hom.f k =
      (koszulDualComplexIsoAt X f ℱ j k (k + (r : ℤ)) (by omega)).hom ≫
        (koszulPowerComplexOnMapIso X f j (unitHomSheafIso X ℱ)).hom.f (k + (r : ℤ)) :=
    fun _ => rfl
  have hcoeff := congrArg
    (fun φ : koszulPowerComplexOn X f (unitHomSheaf X ℱ) (m + 1) ⟶
        koszulPowerComplexOn X f ℱ m => φ.f (k + (r : ℤ)))
    (koszulPowerComplexOnMapIso_dualTrans X f (unitHomSheafIso X ℱ) m)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hcomp, hcomp,
    CochainComplex.shiftFunctor_map_f', ← Category.assoc, koszulDualComplexIsoAt_trans,
    Category.assoc, Category.assoc]
  exact congrArg (fun z => (koszulDualComplexIsoAt X f ℱ (m + 1) k (k + (r : ℤ))
    (by omega)).hom ≫ z) hcoeff

/-- **The two towers of complexes are isomorphic**: the tower of internal Hom complexes against
the Koszul tower is the `r`-fold shift of the dual Koszul tower with coefficients in `ℱ`. -/
def koszulDualSystemComplexMap :
    koszulSheafHomSystemOf X f ℱ ⟶
      koszulDualSystemOn X f ℱ ⋙
        shiftFunctor (CochainComplex
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (r : ℤ) :=
  NatTrans.ofOpSequence (fun m => (koszulDualComplexIsoCoeff X f ℱ m).hom) fun m => by
    rw [koszulSheafHomSystemOf_map_succ]
    rw [show (koszulDualSystemOn X f ℱ ⋙
          shiftFunctor (CochainComplex
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (r : ℤ)).map
            (homOfLE (Nat.le_add_right m 1)).op =
        (shiftFunctor (CochainComplex
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (r : ℤ)).map
          ((koszulDualSystemOn X f ℱ).map (homOfLE (Nat.le_add_right m 1)).op) from rfl,
      koszulDualSystemOn_map_succ]
    exact koszulDualComplexIsoCoeff_trans X f ℱ m

/-- The comparison `koszulDualSystemComplexMap X f ℱ` of the two towers of complexes is an
isomorphism. -/
instance isIso_koszulDualSystemComplexMap : IsIso (koszulDualSystemComplexMap X f ℱ) := by
  have h (m : ℕᵒᵖ) : IsIso ((koszulDualSystemComplexMap X f ℱ).app m) := by
    change IsIso (koszulDualComplexIsoCoeff X f ℱ m.unop).hom
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- **The two towers of complexes are isomorphic.** -/
def koszulDualSystemComplexIso :
    koszulSheafHomSystemOf X f ℱ ≅
      koszulDualSystemOn X f ℱ ⋙
        shiftFunctor (CochainComplex
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (r : ℤ) :=
  asIso (koszulDualSystemComplexMap X f ℱ)

end KoszulDual

/-! ## The tower of the Koszul formula of Tag 0A0E at a sheaf of modules -/

section Derived

open CategoryTheory.AlternatingCech

open scoped IsMulCommutative

attribute [local instance] HasDerivedCategory.standard hasFiniteBiproducts_sheafOfModules

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (ℱ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The tower of internal Hom complexes against the Koszul tower computes the tower of derived
internal Homs**, as a morphism of functors `ℕᵒᵖ ⥤ D(𝒪)`. At each `n` it is the comparison of
[Stacks, Tag 08JH], taken at the explicit derived internal Hom built from
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`, and its naturality in `n` is
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality`. -/
def koszulDerivedSheafHomSystemComparison :
    koszulSheafHomSystemOf X f ℱ ⋙ DerivedCategory.Q ⟶
      derivedSheafHomSystem X (koszulPowerSystem X f ⋙ DerivedCategory.Q)
        (DerivedCategory.Q.obj (singleSheafComplex X ℱ)) :=
  NatTrans.ofOpSequence
    (fun m => strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X)
      (koszulPowerComplex X f m) (singleSheafComplex X ℱ))
    (fun m => by
      have hcmp := strictlyPerfectHomComparison_naturality X (derivedInternalHomOfBifunctor X)
        (koszulPowerComplex X f (m + 1)) (koszulPowerComplex X f m)
        (singleSheafComplex X ℱ) (singleSheafComplex X ℱ)
        (koszulPowerComplexMap X f m) (𝟙 (singleSheafComplex X ℱ))
      simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hcmp
      simp only [derivedSheafHomSystem, Functor.comp_map, koszulSheafHomSystemOf_map_succ,
        koszulPowerSystem_map_succ, Functor.flip_obj_map, Functor.op_map, Quiver.Hom.unop_op,
        derivedInternalHomOfBifunctor_hom] at hcmp ⊢
      exact hcmp)

/-- The comparison `koszulDerivedSheafHomSystemComparison X f ℱ` of the tower of internal Hom
complexes with the tower of derived internal Homs is an isomorphism. -/
instance isIso_koszulDerivedSheafHomSystemComparison :
    IsIso (koszulDerivedSheafHomSystemComparison X f ℱ) := by
  have h (m : ℕᵒᵖ) : IsIso ((koszulDerivedSheafHomSystemComparison X f ℱ).app m) := by
    change IsIso (strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X)
      (koszulPowerComplex X f m.unop) (singleSheafComplex X ℱ))
    exact isIso_strictlyPerfectHomComparison_koszulPowerComplex X
      (derivedInternalHomOfBifunctor X) f m.unop (singleSheafComplex X ℱ)
  exact NatIso.isIso_of_isIso_app _

/-- **The tower of the Koszul formula of [Stacks, Tag 0A0E] at a sheaf of modules `ℱ` is the
`r`-fold shift of the dual Koszul tower with coefficients in `ℱ`**:

`ℱ ⊗^𝐋_𝒪 (K^n)^∨  ≅  Q(K(𝒪, f_1^{n+1}, …, f_r^{n+1}) ⊗ ℱ)[r]`,

naturally in `n`, where the right-hand side is
`AlgebraicGeometry.RingedSite.koszulPowerComplexOn`, the Koszul complex with coefficients in `ℱ`
of [Stacks, Tag 0913], shifted by the number `r` of sections. The shift is the grading
discrepancy of the source's proof: `(K^n)^∨` lives in degrees `-r, …, 0` and the Koszul complex
with coefficients in degrees `0, …, r`.

The isomorphism is the composite of three: the identification of the tower of
[Stacks, Tag 0A0E] with the tower of derived internal Homs,
`AlgebraicGeometry.RingedSite.koszulTensorDualSystemIso`; the comparison of [Stacks, Tag 08JH],
which is invertible at the strictly perfect Koszul complexes; and the self-duality of the Koszul
complex with coefficients, `AlgebraicGeometry.RingedSite.koszulDualSystemComplexIso`. -/
def koszulTensorDualSystemCoefficientIso :
    tensorDerivedDualSystem X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
        (koszulPowerSystem X f ⋙ DerivedCategory.Q)
        (DerivedCategory.Q.obj (singleSheafComplex X ℱ)) ≅
      (koszulDualSystemOn X f ℱ ⋙
          shiftFunctor (CochainComplex
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (r : ℤ)) ⋙
        DerivedCategory.Q :=
  koszulTensorDualSystemIso X f (DerivedCategory.Q.obj (singleSheafComplex X ℱ)) ≪≫
    (asIso (koszulDerivedSheafHomSystemComparison X f ℱ)).symm ≪≫
      Functor.isoWhiskerRight (koszulDualSystemComplexIso X f ℱ) DerivedCategory.Q

/-- **The identification of [Stacks, Tag 0A0E]'s tower with the Koszul complex with
coefficients, at a fixed `n`:**

`ℱ ⊗^𝐋_𝒪 Hom_𝒪(K^n, 𝒪)  ≅  Q(K(𝒪, f_1^{n+1}, …, f_r^{n+1}) ⊗ ℱ)[r]`. -/
def koszulTensorDualCoefficientIso (n : ℕ) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj (singleSheafComplex X ℱ))).obj
        (((derivedSheafHomBifunctor X).obj
          (op (DerivedCategory.Q.obj (koszulPowerComplex X f n)))).obj
            (derivedStructureSheaf X)) ≅
      DerivedCategory.Q.obj ((koszulPowerComplexOn X f ℱ n)⟦(r : ℤ)⟧) :=
  (koszulTensorDualSystemCoefficientIso X f ℱ).app (op n)

end Derived

end AlgebraicGeometry.RingedSite

end
