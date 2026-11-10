module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.FactorSolutions

/-!
# The shared tame extension and the all-perfect-core family

The constructed shared Kummer extension of the tame case, the input preparation for shared
residue absorption in the all-perfect-core (constant-numerator) family, and the normalization to
base-origin coefficients modulo `pi ^ N`.
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.EppTheorem

universe uA uB uK uL

/-! ### Constructing the shared extension in the tame case -/

section SharedTame

variable (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ R : Type uK)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra A K₁] [Algebra B L]
    [Algebra K L] [Algebra K K₁]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing B L]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra A R] [Algebra.IsIntegral A R] [IsDiscreteValuationRing.IsExtension A R]
    [Algebra R K₁] [IsFractionRing R K₁] [IsScalarTower A R K₁]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    {n : ℕ} (E : Fin n → Type (max uL uK))
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, Algebra L (E i)] [∀ i, Algebra K₁ (E i)]
    [∀ i, Module.Finite L (E i)]

include A B K L K₁ R in
/-- **The shared extension of the tame case, constructed.**

`factorSolutions_of_tame` takes the prescribed `K₂` and its divisibility as given. Here the
extension is *built*: for any `e ≥ 2` divisible by every factor's ramification index over `R`,
the Kummer extension `K₂ = K₁(π₁^{1/e})` has local ramification index exactly `e` over `R`
(`Stacks.KummerExtension.exists_ramificationIdx_eq`), so the divisibility holds at its unique
  maximal ideal
and `FactorSolutions` follows.

Taking `e` to be the least common multiple of the factors' ramification indices — or any common
multiple at least `2` — makes this unconditional in the tame case. The point is that a *single*
`K₂`, written down before any factor is examined, serves all of them: that is the synchronization
the all-factor route needs, and Abhyankar's lemma in its prescribed-extension form
(`IsDiscreteValuationRing.isWeakSolution_of_tame_of_ramificationIndex_dvd`) is what makes one
extension usable at every factor at once.

The wild case is not settled by this and is not claimed: there the endgame is the degree-`p`
Artin--Schreier reduction, which in the tree still produces its own extension rather than
accepting a prescribed one. -/
theorem exists_sharedExtension_factorSolutions_of_tame
    (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i)
    (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i = algebraMap L (E i) l)
    (hright : ∀ i (x : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) i =
      algebraMap K₁ (E i) x)
    (e : ℕ) (he : 2 ≤ e) :
    letI : ∀ i, Algebra B (E i) := fun i =>
      ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
    letI : ∀ i, IsScalarTower B L (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ i, Algebra A (E i) := fun i =>
      ((algebraMap B (E i)).comp (algebraMap A B)).toAlgebra
    letI : ∀ i, IsScalarTower A B (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ i, Algebra R (E i) := fun i =>
      ((algebraMap K₁ (E i)).comp (algebraMap R K₁)).toAlgebra
    letI : ∀ i, IsScalarTower R K₁ (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ i, FaithfulSMul R (E i) := fun i =>
      (faithfulSMul_iff_algebraMap_injective R (E i)).mpr
        ((algebraMap K₁ (E i)).injective.comp (IsFractionRing.injective R K₁))
    letI : ∀ i, IsScalarTower A R (E i) := fun i =>
      IsScalarTower.of_algebraMap_eq fun a =>
        (algebraMap_reducedFactor_base_eq_of_tower A B K L K₁ E decomp hleft hright i a).trans
          (congrArg (algebraMap K₁ (E i)) (IsScalarTower.algebraMap_apply A R K₁ a))
    letI : ∀ i, IsDiscreteValuationRing (integralClosure B (E i)) := fun i =>
      isDiscreteValuationRing_integralClosure_factor B L (E i)
    letI : ∀ i, Algebra R (integralClosure B (E i)) := fun i =>
      algebraIntegralClosureBase A B R (E i)
    letI : ∀ i, IsDiscreteValuationRing.IsExtension R (integralClosure B (E i)) := fun i =>
      isExtension_base_integralClosure_factor A B R L (E i)
    (∀ i, (ringChar (IsLocalRing.ResidueField R) = 0 ∨
        Nat.Coprime (ringChar (IsLocalRing.ResidueField R))
            (IsDiscreteValuationRing.ramificationIndex R (integralClosure B (E i))) ∧
          Algebra.IsSeparableExtension (IsLocalRing.ResidueField R)
            (IsLocalRing.ResidueField (integralClosure B (E i)))) ∧
        IsDiscreteValuationRing.ramificationIndex R (integralClosure B (E i)) ∣ e) →
    ∃ (K₂ : Type uK) (_ : Field K₂) (_ : Algebra K₁ K₂) (_ : Algebra R K₂)
      (_ : IsScalarTower R K₁ K₂) (_ : Module.Finite K₁ K₂),
      FactorSolutions A B K L K₁ K₂ R E decomp hleft hright := by
  intro htame
  obtain ⟨π₁, hπ₁⟩ := IsDiscreteValuationRing.exists_irreducible R
  let : Fact (Irreducible (Stacks.KummerExtension.kummerPoly K₁ π₁ e)) :=
    ⟨Stacks.KummerExtension.kummerPoly_irreducible K₁ π₁ e (by omega) hπ₁⟩
  refine ⟨Stacks.KummerExtension.K1 K₁ π₁ e, inferInstance, inferInstance, inferInstance,
    inferInstance,
    Module.finite_of_finrank_pos
      (by rw [Stacks.KummerExtension.finrank_K1 K₁ π₁ e he hπ₁]; omega), ?_⟩
  obtain ⟨hR₂dvr, hR₂ext, -, -, -⟩ :=
    IsDiscreteValuationRing.integralClosure_isCompleteDVR R K₁ (Stacks.KummerExtension.K1 K₁ π₁ e)
  let := hR₂dvr
  let := hR₂ext
  obtain ⟨m, hmmax, hmlo, -, hmidx⟩ := Stacks.KummerExtension.exists_ramificationIdx_eq K₁ π₁ e he
    hπ₁
  let : m.IsMaximal := hmmax
  let : m.LiesOver (IsLocalRing.maximalIdeal R) := hmlo
  have hmidx' : m.ramificationIdx R = e := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal R) m
      (IsDiscreteValuationRing.not_a_field R)]
    exact hmidx
  exact factorSolutions_of_tame A B K L K₁ (Stacks.KummerExtension.K1 K₁ π₁ e) R E decomp hleft
    hright
    fun i => ⟨(htame i).1, fun q hq => by
      rw [IsLocalRing.eq_maximalIdeal hq, ← IsLocalRing.eq_maximalIdeal hmmax, hmidx']
      exact (htame i).2⟩

end SharedTame

-- A shared-`K₂` construction by adjoining an exact `p ^ r`-th root of a uniformizer does not
-- work.  In residue characteristic `p` the
-- ambient field has `char K₁ = p`, so `X ^ (p ^ r) - π₁` has zero derivative and `K₁(π₁^{1/p^r})`
-- is purely inseparable over `K₁`.  Every prescribed solver the wild route ends in carries
-- `[Algebra.IsSeparable K E]` — `exists_isWeakSolution_of_baseChanged_artinSchreier_residue`
-- among them — so an exact `p ^ r`-th root can never feed it: the unit correction in
-- `exists_baseChanged_laurent_reduction` is essential, not cosmetic.  The separable construction
-- is `IsDiscreteValuationRing.exists_isGalois_totallyRamified_orbitExtension_forall_depth`, whose
-- orbit relation `∏ v : V, (α - algebraMap A K₁ v) = algebraMap A K₁ π` with deeply `π`-divisible
-- `v` yields `α ^ (p ^ rank) = π · u` with `u ≡ 1`, via `pow_card_sub_mem_span_pow_of_prod_eq`;
-- its shared parameters come from `exists_shared_orbit_parameters`.

/-! ### The all-perfect-core family: input preparation for shared residue absorption

`exists_prepared_wild_laurent_of_charP` (the wild preparation of a degree-`p` layer) returns a wild
set `J` and, off it, the statement that each Laurent coefficient is a `p ^ m`-th power for
**every** `m`.  When `J` is empty that covers the whole range: every coefficient lies in the
perfect core of the member's own residue field.  This is Epp's **constant-numerator** branch, and
it is a different endgame, not a degenerate case of the wild one — the wild construction is driven
throughout by a coefficient possessing a *terminal* root, one that is not itself a `p`-th power,
and a perfect-core coefficient has none at any depth.

The branch's intended shape, with the quantifier order it must have:

1. one shared weakly unramified base change `R → R₂` absorbing **every** member's coefficients at
   one depth, giving their `p ^ N`-th roots in `κ_{R₂}` read in any common residue overfield;
2. hence, at every member, a Laurent presentation whose numerator is *constant* — defined over the
   base rather than over the member;
3. hence one Artin--Schreier extension `K₂` of the **base** field, obtained from the finitely many
   base numerators, over which every member's layer becomes weakly unramified.

Step 1 exists as
`EppTheorem.EppCondition.exists_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield`,
proved from Epp's condition at every member.  It takes the depth `N` as a free input and the
coefficients as a **`Finset` per member**, with the proof that each of their elements lies in
the perfect core.  It lives in
`StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedResidueAbsorption`, which this module does
not import; nothing below depends on it, and what is below is the data it consumes.

**What this section proves is step 1's input, and nothing else.**  Steps 2 and 3 are not proved,
here or anywhere in the tree.  Step 3 in particular is where the base residue field is genuinely
interrogated and where the one shared `K₂` would have to be produced, and it is the remaining
obligation of the whole wild case.  No claim is made that
the constant-numerator branch follows from what is here. -/

section ConstantNumerator

/-- **The `J = ∅` case makes the prepared family's tame clause unconditional.**

`exists_prepared_wild_laurent_of_charP` states the perfect-core property of a coefficient only off
the wild set.  When every member's wild set is empty the side condition is vacuous, so the property
holds across each member's whole coefficient range.  That unconditional form is what the support
construction below consumes. -/
theorem forall_pow_eq_of_wild_eq_empty
    {ι : Type*} {F : ι → Type*} [∀ i, Field (F i)] {p : ℕ}
    (n : ι → ℕ) (J : ι → Finset ℕ) (coeff : ∀ i, ℕ → F i)
    (hJ : ∀ i, J i = ∅)
    (htame : ∀ i, ∀ k ∈ Finset.range (n i), k ∉ J i →
      ∀ m : ℕ, ∃ y : F i, y ^ p ^ m = coeff i k) :
    ∀ i, ∀ k ∈ Finset.range (n i), ∀ m : ℕ, ∃ y : F i, y ^ p ^ m = coeff i k :=
  fun i k hk => htame i k hk (by simp [hJ i])

/-- **The coefficient support of an all-perfect-core family, in the form absorption consumes.**

From the unconditional perfect-core property across every member's coefficient range, one gets a
finite set `s i` of residue-field elements per member which contains every coefficient of that
member and all of whose elements lie in `perfectCore (F i) p`.  That pair — the `Finset` and the
membership proof — is exactly what
`Stacks.EppTheorem.EppCondition.exists_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield`
  takes,
alongside a depth it leaves free.

The support is `(Finset.range (n i)).image (coeff i)`, so it is finite for the reason that matters
here: the pole order is finite at each member and the family is indexed by finitely many members
downstream, which is what lets one base change serve all of them.  The containment clause is
recorded because absorption supplies roots only for the elements it is handed, and the descent step
needs them for *every* coefficient.

This is step 1's input only.  It does not produce the base change, and it says nothing about the
Artin--Schreier descent or the shared `K₂` that the branch still needs. -/
theorem exists_coeffSupport_forall_mem_perfectCore
    {ι : Type*} {F : ι → Type*} [∀ i, Field (F i)] {p : ℕ} [∀ i, ExpChar (F i) p]
    (n : ι → ℕ) (coeff : ∀ i, ℕ → F i)
    (h : ∀ i, ∀ k ∈ Finset.range (n i), ∀ m : ℕ, ∃ y : F i, y ^ p ^ m = coeff i k) :
    ∃ s : ∀ i, Finset (F i),
      (∀ i, ∀ k ∈ Finset.range (n i), coeff i k ∈ s i) ∧
        ∀ i, ∀ x ∈ s i, x ∈ perfectCore (F i) p := by
  classical
  refine ⟨fun i => (Finset.range (n i)).image (coeff i),
    fun i k hk => Finset.mem_image_of_mem _ hk, fun i x hx => ?_⟩
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
  exact mem_perfectCore_iff.mpr (h i k hk)


/-- **Absorption's roots, re-indexed by coefficient position: the simultaneous root selection.**

This is the composition of `exists_coeffSupport_forall_mem_perfectCore` with the shared residue
absorption in `EppSharedResidueAbsorption.lean`,
`EppTheorem.EppCondition.exists_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield`.
That theorem supplies a `p ^ N`-th root in the **one** base residue field `G` for each element
of the finite set `s i` it is handed, compared inside a residue overfield `Om i` because `F i`
and `G`
need not be comparable directly.  What a caller actually needs is a root for each *coefficient
index*, and the bridge is the containment clause `hmem` — which is why
`exists_coeffSupport_forall_mem_perfectCore` records it.

The quantifier order is preserved exactly: `G`, `N` and the comparison maps are fixed before
`forall i`, and the conclusion is a single root function family over that same data.  Nothing is
chosen per member except the root itself, and no member's root is used to obtain another's.

Absorption is **not** imported here.  It lives in `EppSharedResidueAbsorption.lean`, which
sits above this file in the import order: `EppKuhlmannCompleteCase` imports only
`PerfectCore`, while absorption imports `EppSharedFamilySupport`, so the dependency direction
forbids the import outright rather than merely discouraging it.  Its conclusion is instead the
hypothesis `habs`, in its own shape, so the two compose by application.

(The `perfectCore` membership lemma is the root-namespace `mem_perfectCore_of_pow_eq` of
`EppConditionAscent.lean`; nothing here needs it.)

**This is not step 2, only its selection half**, and the way it continues is *re-entry*, which is
worth stating because the obvious alternative is false.

The missing input is **not** a ring map `G -> F i`, equivalently a base change `R2 -> B i`
compatible with the absorption: such a map does not exist in general.  The new base residue field
need not embed into the *original* factor's residue field
at all; absorption compares them inside an overfield precisely because no such embedding is
available.

The correct architecture replaces the member instead of mapping into it.  After the base change one
re-enters with the *post-base-change* member — the conjugate factor of the base-changed extension,
and the integral closure of `B i` in it, call it `Bi2` — for which the structural map `R2 -> Bi2`
exists by construction, hence `kappa(R2) -> kappa(Bi2)`.  Then:

* the **common residue overfield is used only to select and transport the root**, which is what the
  previous lemma does, and nothing else is asked of it;
* the comparison is then instantiated at `Om i := kappa(Bi2)` — legitimate because absorption
  quantifies over the overfield *universally*, and `kappa(Bi2)` receives both `kappa(B i)` and
  `kappa(R2)` — so the selected root becomes an element of `kappa(Bi2)`;
* and the normalization is carried out in `Bi2`, where the root is the residue of an actual ring
  element and a numerator over the base can be assembled.

The structural maps that re-entry needs are already public, in
`StacksFrontier.RingTheory.DiscreteValuationRing.EppFactorPackage`:
`algebraIntegralClosureBase` for `R2 -> Bi2`, `isLocalHom_algebraMap_of_tower` for its locality and
hence the residue map, and `isDiscreteValuationRing_integralClosure_factor`,
`isFractionRing_integralClosure_factor`, `isExtension_base_integralClosure_factor` for the rest.
So re-entry is available rather than missing; what is not done is the assembly. -/
theorem exists_forall_rootBase_pow_eq
    {ι : Type*} {F : ι → Type*} {G : Type*} {Om : ι → Type*}
    [∀ i, Field (F i)] [Field G] [∀ i, Field (Om i)]
    (fOm : ∀ i, F i →+* Om i) (gOm : ∀ i, G →+* Om i)
    (p N : ℕ) (n : ι → ℕ) (coeff : ∀ i, ℕ → F i) (s : ∀ i, Finset (F i))
    (hmem : ∀ i, ∀ k ∈ Finset.range (n i), coeff i k ∈ s i)
    (habs : ∀ i, ∀ x ∈ s i, ∃ z : G, gOm i z ^ p ^ N = fOm i x) :
    ∃ rootBase : ι → ℕ → G,
      ∀ i, ∀ k ∈ Finset.range (n i),
        gOm i (rootBase i k) ^ p ^ N = fOm i (coeff i k) := by
  have h : ∀ i, ∀ k ∈ Finset.range (n i), ∃ z : G, gOm i z ^ p ^ N = fOm i (coeff i k) :=
    fun i k hk => habs i (coeff i k) (hmem i k hk)
  choose! rootBase hroot using h
  exact ⟨rootBase, hroot⟩


/-- **Re-entry: a selected root is the image of a base element in the post-base-change member.**

The step after `exists_forall_rootBase_pow_eq`.  There the root is chosen in the shared base
residue field `G` and compared inside an overfield; here the comparison has been instantiated at
the *post-base-change* member's own residue field, and the root is realised as the image under
`algebraMap R2 (S i)` of an element of the **base ring** `R2`.

**Why it has to be done this way.**  Choosing the lift by surjectivity of the member's own residue
map, obtaining some `w : S i` with `res i w = g i (rootBase i k)`, does **not** identify the lift
as coming from the base.  Residue-surjectivity produces an arbitrary preimage in `S i`;
nothing says it lies in the image of `R2`, and the constant-numerator property is exactly the
statement that the numerator's coefficients *do*.

The correct order is to lift **in the base first**: `rootBase i k` lies in `G`, the residue field
of `R2`, so surjectivity of `resB` gives `v i k : R2` with `resB (v i k) = rootBase i k`; the
coefficient of the numerator is then `algebraMap R2 (S i) (v i k)` **by construction**, and the
residue square `hsq` transports the power equation to it.  What the conclusion exhibits is
therefore a base element together with the fact that its image in the member has the required
residue — which is the constant-numerator property, rather than an assertion about it.

`S i` is to be read as the re-entered member `Bi2` — the integral closure of `B i` in a conjugate
factor of the base-changed extension — `Algebra R2 (S i)` as the structural map that re-entry makes
available, `res i` as the member's residue map, and `hsq` as the residue square of the local
homomorphism `R2 -> S i`.  No map into the *original* factor's residue field is used or needed, and
none should be sought, since in general there is none.

Stated with abstract surjections rather than `IsLocalRing.residue` so that it stays in this file,
whose imports are deliberately light; at the call site `resB` and `res i` are residue maps and
`hresB` is surjectivity of the base one.

This is still not the assembly.  What remains of step 2 is to combine these base coefficients into
each member's Laurent numerator and to upgrade the equality of residues to a congruence modulo
`pi ^ n`.  The arithmetic for the combination is settled elsewhere — an `F_p`-combination of
Frobenius-power numerators has a `p`-th power leading coefficient — but the pole-order reduction
**does** have to be iterated to termination: the claim that minimality removes the iteration was
made upstream and has since been disproved, so it must not be relied on here. -/
theorem exists_forall_baseLift_pow_eq
    {ι : Type*} {F : ι → Type*} {R2 : Type*} {G : Type*} {S : ι → Type*} {kap : ι → Type*}
    [∀ i, Field (F i)] [CommRing R2] [Field G] [∀ i, CommRing (S i)] [∀ i, Field (kap i)]
    [∀ i, Algebra R2 (S i)]
    (resB : R2 →+* G) (hresB : Function.Surjective resB)
    (res : ∀ i, S i →+* kap i)
    (f : ∀ i, F i →+* kap i) (g : ∀ i, G →+* kap i)
    (hsq : ∀ i, ∀ x : R2, res i (algebraMap R2 (S i) x) = g i (resB x))
    (p N : ℕ) (n : ι → ℕ) (coeff : ∀ i, ℕ → F i) (rootBase : ι → ℕ → G)
    (hroot : ∀ i, ∀ k ∈ Finset.range (n i),
      g i (rootBase i k) ^ p ^ N = f i (coeff i k)) :
    ∃ v : ι → ℕ → R2,
      ∀ i, ∀ k ∈ Finset.range (n i),
        resB (v i k) = rootBase i k ∧
          res i (algebraMap R2 (S i) (v i k)) ^ p ^ N = f i (coeff i k) := by
  classical
  have h : ∀ (i : ι) (k : ℕ), ∃ x : R2, resB x = rootBase i k := fun i k => hresB _
  choose v hv using h
  refine ⟨v, fun i k hk => ⟨hv i k, ?_⟩⟩
  rw [hsq i (v i k), hv i k]
  exact hroot i k hk

/-- **A Laurent numerator built from base-origin coefficients is the image of a base numerator.**

If every coefficient of a Laurent expansion, and the uniformizer it is expanded in, are images
under a field homomorphism `phi` of elements of the base, then the whole expansion is the image of
the corresponding expansion over the base.  That is the **constant-numerator** property, as an
identity rather than an assertion about one.

This is what `exists_forall_baseLift_pow_eq` is for: that lemma produces the coefficients
`v i k : R2` and exhibits the member's coefficient as `algebraMap R2 (S i) (v i k)`, and this one
assembles them, showing the assembled numerator lies in the image of the base.  Read `phi` as the
composite `Frac R2 → E i` and `t` as the image of the base uniformizer, which is legitimate because
a uniformizer of `R` stays one after a weakly unramified base change.

The proof is `map_add`, `map_sum`, `map_mul`, `map_pow` and `map_inv₀`; nothing is assumed about
the pole order or the coefficients beyond their being of base origin.  What this does **not** do is
establish the congruence the Artin--Schreier reduction consumes: residues determine elements only
modulo the maximal ideal, whereas the reduction needs agreement modulo `pi ^ n` because the `k`-th
coefficient is multiplied by `pi ^ -(n - k)`.  Bridging that gap needs the truncated lifting datum
`liftMod : kappa(B) →+* B ⧸ m ^ n`, which lives with the Artin--Schreier machinery and not here. -/
theorem laurent_numerator_eq_algebraMap {K0 M : Type*} [Field K0] [Field M] (φ : K0 →+* M)
    (n : ℕ) (v : ℕ → K0) (t b : K0) :
    (∑ k ∈ Finset.range n, φ (v k) * (φ t)⁻¹ ^ (n - k)) + φ b
      = φ ((∑ k ∈ Finset.range n, v k * t⁻¹ ^ (n - k)) + b) := by
  rw [map_add, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [map_mul, map_pow, map_inv₀]

end ConstantNumerator

/-! ### Step 2: normalization to base-origin coefficients modulo `pi ^ N` -/

section Normalization

/-- The transported section: residue and truncation compatibilities along a local ring map. -/
private theorem residue_mk_algebraMap_sigma
    {F B S : Type*} [Field F] [CommRing B] [IsLocalRing B]
    [CommRing S] [IsLocalRing S] [Algebra B S] [IsLocalHom (algebraMap B S)]
    (N : ℕ) (f : F →+* IsLocalRing.ResidueField B) (sigma : F → B)
    (hsigma : ∀ x, IsLocalRing.residue B (sigma x) = f x)
    (sq : F →+* B ⧸ (IsLocalRing.maximalIdeal B) ^ N)
    (hsq : ∀ x, Ideal.Quotient.mk _ (sigma x) = sq x) (x : F) :
    IsLocalRing.residue S (algebraMap B S (sigma x)) =
      IsLocalRing.ResidueField.map (algebraMap B S) (f x) ∧
    Ideal.Quotient.mk _ (algebraMap B S (sigma x)) =
      IsDiscreteValuationRing.truncationMap B S N (sq x) :=
  ⟨by rw [← IsLocalRing.ResidueField.map_residue, hsigma],
    by rw [← hsq, IsDiscreteValuationRing.truncationMap_mk]⟩

/-- **A residue-field section modulo `m ^ N` transports along a local ring map.**

The pointwise lift is mapped into the target ring, while its multiplicativity modulo `m ^ N` is
transported through the canonical map on truncations.  This is the datum needed when an original
Laurent presentation is re-entered in a conjugate factor after a base change. -/
theorem exists_residueField_lift_mod_pow_map
    {F B S : Type*} [Field F] [CommRing B] [IsLocalRing B]
    [CommRing S] [IsLocalRing S] [Algebra B S] [IsLocalHom (algebraMap B S)]
    (N : ℕ) (f : F →+* IsLocalRing.ResidueField B) (sigma : F → B)
    (hsigma : ∀ x, IsLocalRing.residue B (sigma x) = f x)
    (sq : F →+* B ⧸ (IsLocalRing.maximalIdeal B) ^ N)
    (hsq : ∀ x, Ideal.Quotient.mk _ (sigma x) = sq x) :
    ∃ (fS : F →+* IsLocalRing.ResidueField S) (sigmaS : F → S)
      (sqS : F →+* S ⧸ (IsLocalRing.maximalIdeal S) ^ N),
      (∀ x, IsLocalRing.residue S (sigmaS x) = fS x) ∧
        ∀ x, Ideal.Quotient.mk _ (sigmaS x) = sqS x := by
  exact ⟨(IsLocalRing.ResidueField.map (algebraMap B S)).comp f, fun x => algebraMap B S (sigma x),
    (IsDiscreteValuationRing.truncationMap B S N).comp sq,
    fun x => (residue_mk_algebraMap_sigma N f sigma hsigma sq hsq x).1,
    fun x => (residue_mk_algebraMap_sigma N f sigma hsigma sq hsq x).2⟩

/-- **A Laurent expansion transports through a compatible factor square.**

This is the field-level half of re-entry.  The coefficients and integral term are mapped through
the lower ring map, while the parameter is mapped through the fraction-field map; compatibility of
the square identifies the two resulting expressions. -/
theorem laurent_expansion_map
    {B S L E : Type*} [CommRing B] [CommRing S] [Field L] [Field E]
    [Algebra B S] [Algebra B L] [Algebra S E] [Algebra L E]
    (hB : ∀ x : B, algebraMap L E (algebraMap B L x) =
      algebraMap S E (algebraMap B S x))
    (t : B) (tS : S) (ht : algebraMap B S t = tS)
    (N : ℕ) (sigma : ℕ → B) (b : B) (xi : L)
    (hexp : xi = (∑ k ∈ Finset.range N,
      algebraMap B L (sigma k) *
        (algebraMap B L t)⁻¹ ^ (N - k)) + algebraMap B L b) :
    algebraMap L E xi = (∑ k ∈ Finset.range N,
      algebraMap S E (algebraMap B S (sigma k)) *
        (algebraMap S E tS)⁻¹ ^ (N - k)) +
          algebraMap S E (algebraMap B S b) := by
  rw [hexp, map_add, map_sum]
  congr 1
  · exact Finset.sum_congr rfl fun k _ => by rw [map_mul, map_pow, map_inv₀, hB, hB, ht]
  · exact hB b

/-- **Re-entry transports all data consumed by constant-Laurent normalization.**

The original coefficient section and its truncated ring homomorphism are transported to the
post-base-change factor, the Laurent identity is mapped through the factor square, and a root from
the new base residue field is identified with the transported original coefficient root. -/
theorem exists_transported_constant_laurent_data
    {A F B S L E : Type*} [CommRing A] [IsLocalRing A] [Field F]
    [CommRing B] [IsLocalRing B] [CommRing S] [IsLocalRing S] [Field L] [Field E]
    [Algebra A S] [IsLocalHom (algebraMap A S)]
    [Algebra B S] [IsLocalHom (algebraMap B S)]
    [Algebra B L] [Algebra S E] [Algebra L E]
    (hB : ∀ x : B, algebraMap L E (algebraMap B L x) =
      algebraMap S E (algebraMap B S x))
    (p N : ℕ) (tA : A) (tB : B) (ht : algebraMap B S tB = algebraMap A S tA)
    (f : F →+* IsLocalRing.ResidueField B) (sigma : F → B)
    (hsigma : ∀ x, IsLocalRing.residue B (sigma x) = f x)
    (sq : F →+* B ⧸ (IsLocalRing.maximalIdeal B) ^ N)
    (hsq : ∀ x, Ideal.Quotient.mk _ (sigma x) = sq x)
    (coeff rootCoeff : ℕ → F)
    (hrootCoeff : ∀ k, k ∈ Finset.range N → rootCoeff k ^ (p ^ N) = coeff k)
    (rootBase : ℕ → IsLocalRing.ResidueField A)
    (hrootBase : ∀ k, k ∈ Finset.range N →
      algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField S) (rootBase k) =
        IsLocalRing.ResidueField.map (algebraMap B S) (f (rootCoeff k)))
    (xi : L) (b : B)
    (hexp : xi = (∑ k ∈ Finset.range N,
      algebraMap B L (sigma (coeff k)) * (algebraMap B L tB)⁻¹ ^ (N - k)) +
        algebraMap B L b) :
    ∃ (fS : F →+* IsLocalRing.ResidueField S) (sigmaS : F → S)
      (sqS : F →+* S ⧸ (IsLocalRing.maximalIdeal S) ^ N),
      (∀ x, IsLocalRing.residue S (sigmaS x) = fS x) ∧
      (∀ x, Ideal.Quotient.mk _ (sigmaS x) = sqS x) ∧
      (∀ k, k ∈ Finset.range N →
        rootCoeff k ^ (p ^ N) = coeff k) ∧
      (∀ k, k ∈ Finset.range N →
        algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField S) (rootBase k) =
          fS (rootCoeff k)) ∧
      algebraMap L E xi = (∑ k ∈ Finset.range N,
        algebraMap S E (sigmaS (coeff k)) *
          (algebraMap S E (algebraMap A S tA))⁻¹ ^ (N - k)) +
            algebraMap S E (algebraMap B S b) := by
  have h := residue_mk_algebraMap_sigma (S := S) N f sigma hsigma sq hsq
  exact ⟨(IsLocalRing.ResidueField.map (algebraMap B S)).comp f, fun x => algebraMap B S (sigma x),
    (IsDiscreteValuationRing.truncationMap B S N).comp sq,
    fun x => (h x).1, fun x => (h x).2, hrootCoeff, hrootBase,
    laurent_expansion_map hB tB (algebraMap A S tA) ht N (fun k => sigma (coeff k)) b xi hexp⟩

/-- **Sums of congruent coefficients are congruent.**

If two coefficient families agree modulo an ideal at every index of a finite range, the two
weighted sums agree modulo that ideal, for any weights.  Used at `t k = pi ^ k` to pass from
per-coefficient agreement to agreement of whole Laurent numerators. -/
theorem sum_sub_sum_mem_of_forall_sub_mem {S : Type*} [CommRing S] (I : Ideal S)
    (n : ℕ) (u w t : ℕ → S) (h : ∀ k ∈ Finset.range n, u k - w k ∈ I) :
    (∑ k ∈ Finset.range n, u k * t k) - (∑ k ∈ Finset.range n, w k * t k) ∈ I := by
  rw [← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun k hk => ?_
  rw [← sub_mul]
  exact I.mul_mem_right _ (h k hk)

/-- **The normalization step: every coefficient of an all-perfect-core family agrees with a base
element modulo `m ^ N`, simultaneously across the family.**

This is what the residue-level work of the constant-numerator branch was missing.  A residue
equality only pins an element modulo the maximal ideal, whereas the Artin--Schreier reduction needs
agreement modulo `pi ^ N`, because the `k`-th coefficient of a Laurent numerator is multiplied by
`pi ^ -(n - k)` and a first-order error there is still a pole.  The device that closes the gap is
the **truncated lifting datum** `s : kappa(S) →+* S ⧸ m ^ N` of
`IsDiscreteValuationRing.exists_residueField_lift_mod_pow`: because `s` is a ring homomorphism into
the truncation, an equality of residues upgrades to a congruence modulo `m ^ N`.

The engine is `IsDiscreteValuationRing.exists_sub_algebraMap_mem_pow_of_pow_eq`, applied at every
member and every coefficient index and then `choose`-d into functions, so the base elements are
produced for the whole family at once.  The hypothesis is that each coefficient is the image of a
`p ^ N`-th power **from the base residue field** -- which is exactly what shared residue absorption
followed by re-entry supplies, and is why `N` has to be the depth fixed for the whole family before
any member is examined.

Only one base change is involved: `R2` is the single absorbed base, and no member contributes an
extension of its own. -/
theorem exists_forall_coeffLift_sub_algebraMap_mem_pow
    {ι : Type*} {R2 : Type*} {S : ι → Type*}
    [CommRing R2] [IsLocalRing R2] [∀ i, CommRing (S i)] [∀ i, IsLocalRing (S i)]
    [∀ i, Algebra R2 (S i)] [∀ i, IsLocalHom (algebraMap R2 (S i))]
    (p : ℕ) [Fact p.Prime] [∀ i, CharP (S i) p] (N : ℕ)
    (σ : ∀ i, IsLocalRing.ResidueField (S i) → S i)
    (hσ : ∀ i, ∀ x, IsLocalRing.residue (S i) (σ i x) = x)
    (sq : ∀ i, IsLocalRing.ResidueField (S i) →+*
      S i ⧸ (IsLocalRing.maximalIdeal (S i)) ^ N)
    (hsq : ∀ i, ∀ x, Ideal.Quotient.mk _ (σ i x) = sq i x)
    (n : ι → ℕ) (root : ι → ℕ → IsLocalRing.ResidueField R2) :
    ∃ base : ι → ℕ → R2, ∀ i, ∀ k ∈ Finset.range (n i),
      σ i (algebraMap (IsLocalRing.ResidueField R2) (IsLocalRing.ResidueField (S i))
          (root i k ^ (p ^ N))) - algebraMap R2 (S i) (base i k)
        ∈ (IsLocalRing.maximalIdeal (S i)) ^ N := by
  classical
  have h : ∀ (i : ι) (k : ℕ), ∃ a₀ : R2,
      σ i (algebraMap (IsLocalRing.ResidueField R2) (IsLocalRing.ResidueField (S i))
          (root i k ^ (p ^ N))) - algebraMap R2 (S i) a₀
        ∈ (IsLocalRing.maximalIdeal (S i)) ^ N := fun i k =>
    IsDiscreteValuationRing.exists_sub_algebraMap_mem_pow_of_pow_eq p N (σ i) (hσ i) (sq i)
      (hsq i) (root i k ^ (p ^ N)) (root i k) rfl
  choose base hbase using h
  exact ⟨base, fun i k _ => hbase i k⟩

/-- **Family normalization from roots compared in the post-base-change residue fields.**

This is the all-conjugate form of
`IsDiscreteValuationRing.exists_sub_algebraMap_mem_pow_of_pow_eq_over_residueField`.
For member `i`, `F i` is the original coefficient residue field and `S i` is the re-entered
conjugate DVR.  The chosen coefficient lifts `σ i` and their truncated ring homomorphisms have
been transported from the original DVR to `S i`; no section of the whole residue field of `S i`
is required.

Each coefficient has a root `rootCoeff i k` in `F i`.  Normal residue absorption supplies a root
`rootBase i k` in the one shared base residue field, and `hrootBase` identifies their images in
the residue field of the re-entered member.  The one-coefficient normalization theorem then
produces an element of the shared base ring congruent to the transported coefficient lift modulo
the common depth.  Finite choice packages these elements for the whole family at once. -/
theorem exists_forall_coeffLift_sub_algebraMap_mem_pow_of_residueField
    {ι : Type*} {R2 : Type*} {F S : ι → Type*}
    [CommRing R2] [IsLocalRing R2]
    [∀ i, Field (F i)] [∀ i, CommRing (S i)] [∀ i, IsLocalRing (S i)]
    [∀ i, Algebra R2 (S i)] [∀ i, IsLocalHom (algebraMap R2 (S i))]
    (p : ℕ) [Fact p.Prime] [∀ i, CharP (S i) p] (N : ℕ)
    (f : ∀ i, F i →+* IsLocalRing.ResidueField (S i))
    (σ : ∀ i, F i → S i)
    (hσ : ∀ i x, IsLocalRing.residue (S i) (σ i x) = f i x)
    (sq : ∀ i, F i →+* S i ⧸ (IsLocalRing.maximalIdeal (S i)) ^ N)
    (hsq : ∀ i x, Ideal.Quotient.mk _ (σ i x) = sq i x)
    (n : ι → ℕ) (coeff rootCoeff : ∀ i, ℕ → F i)
    (hrootCoeff : ∀ i k, k ∈ Finset.range (n i) →
      rootCoeff i k ^ (p ^ N) = coeff i k)
    (rootBase : ι → ℕ → IsLocalRing.ResidueField R2)
    (hrootBase : ∀ i k, k ∈ Finset.range (n i) →
      algebraMap (IsLocalRing.ResidueField R2)
          (IsLocalRing.ResidueField (S i)) (rootBase i k) = f i (rootCoeff i k)) :
    ∃ base : ι → ℕ → R2, ∀ i k, k ∈ Finset.range (n i) →
      σ i (coeff i k) - algebraMap R2 (S i) (base i k) ∈
        (IsLocalRing.maximalIdeal (S i)) ^ N := by
  have h : ∀ i, ∀ k ∈ Finset.range (n i), ∃ a₀ : R2,
      σ i (coeff i k) - algebraMap R2 (S i) a₀ ∈ (IsLocalRing.maximalIdeal (S i)) ^ N :=
    fun i k hk =>
      IsDiscreteValuationRing.exists_sub_algebraMap_mem_pow_of_pow_eq_over_residueField
        p N (f i) (σ i) (hσ i) (sq i) (hsq i) (coeff i k) (rootCoeff i k)
        (hrootCoeff i k hk) (rootBase i k) (hrootBase i k hk)
  choose! base hbase using h
  exact ⟨base, hbase⟩

/-- **The all-conjugate constant-parameter normalization.**

After normal residue absorption, each transported Laurent coefficient has a `p ^ N`-th root
coming from the shared base residue field.  The preceding theorem upgrades that residue equality
to congruence modulo the `N`-th power of the factor's maximal ideal.  Since the factor is weakly
unramified over the shared base, the image of a base uniformizer is again a uniformizer; hence the
congruence is exactly modulo its `N`-th power.  The Laurent principal part therefore differs from
one defined over the shared fraction field only by an integral element.

The conclusion is the input shape of the split-constant-class solver, simultaneously for every
conjugate factor.  In particular, no transported minimality statement is required. -/
theorem exists_forall_base_parameter_add_integral_of_constant_laurent
    {iota : Type*} {R K : Type*} {F S L : iota → Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [∀ i, Field (F i)] [∀ i, CommRing (S i)] [∀ i, IsDomain (S i)]
    [∀ i, IsDiscreteValuationRing (S i)] [∀ i, Field (L i)]
    [∀ i, Algebra R (S i)] [∀ i, IsDiscreteValuationRing.IsExtension R (S i)]
    [∀ i, Algebra R (L i)] [∀ i, Algebra (S i) (L i)] [∀ i, Algebra K (L i)]
    [∀ i, IsScalarTower R (S i) (L i)] [∀ i, IsScalarTower R K (L i)]
    (p : ℕ) [Fact p.Prime] [∀ i, CharP (S i) p] (N : ℕ)
    (pi : R) (hpi : Irreducible pi)
    (hweak : ∀ i, IsDiscreteValuationRing.IsWeaklyUnramified R (S i))
    (f : ∀ i, F i →+* IsLocalRing.ResidueField (S i))
    (sigma : ∀ i, F i → S i)
    (hsigma : ∀ i x, IsLocalRing.residue (S i) (sigma i x) = f i x)
    (sq : ∀ i, F i →+* (S i) ⧸ (IsLocalRing.maximalIdeal (S i)) ^ N)
    (hsq : ∀ i x, Ideal.Quotient.mk _ (sigma i x) = sq i x)
    (coeff rootCoeff : ∀ i, ℕ → F i)
    (hrootCoeff : ∀ i k, k ∈ Finset.range N →
      rootCoeff i k ^ (p ^ N) = coeff i k)
    (rootBase : iota → ℕ → IsLocalRing.ResidueField R)
    (hrootBase : ∀ i k, k ∈ Finset.range N →
      algebraMap (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField (S i)) (rootBase i k) = f i (rootCoeff i k))
    (xi : ∀ i, L i) (b : ∀ i, S i)
    (hexp : ∀ i, xi i = (∑ k ∈ Finset.range N,
      algebraMap (S i) (L i) (sigma i (coeff i k)) *
        (algebraMap (S i) (L i) (algebraMap R (S i) pi))⁻¹ ^ (N - k)) +
          algebraMap (S i) (L i) (b i)) :
    ∃ (xi0 : iota → K) (b' : ∀ i, S i), ∀ i,
      xi i = algebraMap K (L i) (xi0 i) + algebraMap (S i) (L i) (b' i) := by
  classical
  obtain ⟨base, hbase⟩ :=
    exists_forall_coeffLift_sub_algebraMap_mem_pow_of_residueField
      p N f sigma hsigma sq hsq (fun _ => N) coeff rootCoeff hrootCoeff rootBase hrootBase
  have h : ∀ i, ∃ (c : K) (d : S i),
      xi i = algebraMap K (L i) c + algebraMap (S i) (L i) d := by
    intro i
    have hpiS : Irreducible (algebraMap R (S i) pi) :=
      IsDiscreteValuationRing.irreducible_algebraMap_of_isWeaklyUnramified (hweak i) hpi
    have hpow : (IsLocalRing.maximalIdeal (S i)) ^ N =
        Ideal.span {algebraMap R (S i) pi ^ N} := by
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hpiS,
        Ideal.span_singleton_pow]
    have ht : algebraMap R (L i) pi ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply R K (L i)]
      simpa only [map_zero] using (algebraMap K (L i)).injective.ne
        ((IsFractionRing.injective R K).ne hpi.ne_zero)
    exact IsDiscreteValuationRing.exists_base_parameter_add_integral_of_coefficients_lift
      pi ht N (fun k => sigma i (coeff i k)) (b i) (xi i) (base i) (hexp i)
        (fun k hk => by rw [← hpow]; exact hbase i k hk)
  choose xi0 b' hxi using h
  exact ⟨xi0, b', hxi⟩

end Normalization

end Stacks.EppTheorem

end
