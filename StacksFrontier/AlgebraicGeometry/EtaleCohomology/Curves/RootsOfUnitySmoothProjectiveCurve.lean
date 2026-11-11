module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DegreeZero.RootsOfUnityCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.ConstantRootsOfUnity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.ConstantRootsOfUnitySupplement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Etale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.ExactSequence
public import StacksFrontier.AlgebraicGeometry.InvertibleFunctions.ProperVariety
public import StacksFrontier.AlgebraicGeometry.Picard.CurveDegree
public import StacksFrontier.AlgebraicGeometry.Picard.SmallEtaleFirstCohomologyComparison

/-!
# Étale cohomology of the roots of unity on a smooth projective curve

Let `X` be a smooth projective curve over an algebraically closed field `k` and let `n ≥ 1` be
invertible in `k`. This file computes the étale cohomology of the sheaf `μ_n` of `n`-th roots of
unity on the small étale site of `X` in the two degrees that are reachable:

* `q = 0`: pullback along the structure morphism identifies `μ_n(k)` with `H⁰_ét(X, μ_n)`. This
  is `AlgebraicGeometry.baseRootsToEtaleH0_bijective_of_isCurve`, proved elsewhere and used
  here.
* `q = 1`: the canonical map through the Kummer sequence identifies `H¹_ét(X, μ_n)` with
  `Pic⁰(X)[n]`, the `n`-torsion of the degree-zero Picard group.

It then transports both along the isomorphism of abelian sheaves `μ_n ≅ 𝐙/n𝐙` of
`AlgebraicGeometry.constantZModSheafIsoRootsOfUnitySheaf` to give the source's second,
noncanonical list in the same two degrees: `H⁰_ét(X, 𝐙/n𝐙) ≅ 𝐙/n𝐙` and
`H¹_ét(X, 𝐙/n𝐙) ≅ Pic⁰(X)[n]`. Noncanonical is literal: the sheaf isomorphism is induced by an
isomorphism `𝐙/n𝐙 ≅ μ_n(k)`, of which there are `φ(n)`, so the identifications are asserted as
the existence of an isomorphism rather than of a named map.

## The `q = 1` argument

The Kummer sequence `0 ⟶ μ_n ⟶ 𝐆_m ⟶ 𝐆_m ⟶ 0` on `X_étale` is short exact because `n` is
invertible on `X` (Stacks Tag 03PL), and its long exact sequence pins the map
`H¹_ét(X, μ_n) ⟶ H¹_ét(X, 𝐆_m)` from both sides:

* its kernel is the image of the Kummer boundary of the global units,
  `AlgebraicGeometry.exists_kummerBoundary_iff`, and that boundary kills exactly the `n`-th
  powers, `AlgebraicGeometry.kummerBoundary_eq_zero_iff`. On a proper variety over an
  algebraically closed field every invertible global function is a constant,
  `AlgebraicGeometry.forall_units_mem_range_of_isAlgClosed`, hence an `n`-th power, because `k`
  is algebraically closed. So the map is injective;
* its image is the `n`-torsion, `AlgebraicGeometry.exists_kummerFirstCohomologyMap_iff`, since
  the second map of the Kummer sequence is `n • 𝟙` and therefore induces multiplication by `n`
  on cohomology.

Stacks Tag 03P8 on the small étale site,
`Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivZariskiPicardGroup`, replaces
`H¹_ét(X, 𝐆_m)` by `Pic(X)`, so the canonical map is an isomorphism onto `Pic(X)[n]`. Finally a
torsion class of `Pic(X)` has degree zero,
`AlgebraicGeometry.mem_picardDegreeZero_of_nsmul_eq_zero`, because `𝐙` is torsion free; so
`Pic(X)[n] = Pic⁰(X)[n]`.

## Main definitions

* `AlgebraicGeometry.kummerSmallEtale` — the Kummer sequence on the small étale site of `X`.
* `AlgebraicGeometry.etaleH1UnitsEquivPicard` — Stacks Tag 03P8 on the small étale site, stated
  for the middle term of the Kummer sequence.
* `AlgebraicGeometry.etaleH1RootsOfUnityToPicard` — the canonical map
  `H¹_ét(X, μ_n) ⟶ Pic(X)`.
* `AlgebraicGeometry.curvePicardDegreeZero` and
  `AlgebraicGeometry.curvePicardDegreeZeroTorsion` — `Pic⁰(X)` and `Pic⁰(X)[n]`.
* `AlgebraicGeometry.etaleH1RootsOfUnityToCurvePicardDegreeZeroTorsion` — the canonical map
  `H¹_ét(X, μ_n) ⟶ Pic⁰(X)[n]`.

## Main results

* `AlgebraicGeometry.injective_etaleH1RootsOfUnityToPicard` and
  `AlgebraicGeometry.mem_range_etaleH1RootsOfUnityToPicard_iff` — the canonical map
  `H¹_ét(X, μ_n) ⟶ Pic(X)` is injective with image the `n`-torsion.
* `AlgebraicGeometry.bijective_etaleH1RootsOfUnityToCurvePicardDegreeZeroTorsion` —
  **`H¹_ét(X, μ_n) = Pic⁰(X)[n]`.**
* `AlgebraicGeometry.etaleH0RootsOfUnityAddEquiv` — `H⁰_ét(X, μ_n) = μ_n(Γ(X, 𝒪_X))` as
  abelian groups, and `AlgebraicGeometry.etaleH0RootsOfUnity_card` its order.
* `AlgebraicGeometry.nonempty_etaleH0ConstantZModAddEquiv` and
  `AlgebraicGeometry.nonempty_etaleH1ConstantZModAddEquiv` — **`H⁰_ét(X, 𝐙/n𝐙) ≅ 𝐙/n𝐙`** and
  **`H¹_ét(X, 𝐙/n𝐙) ≅ Pic⁰(X)[n]`**, the reachable degrees of the noncanonical list.
* `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve` — the four clauses
  together; this is where Stacks Tag 03RQ is registered.

## Implementation notes

The sheaf of units appears in two spellings on the small étale site: `unitsSheaf` of the units
of global functions on the étale `X`-schemes, which the Kummer sequence is built from, and
`Stacks.Cohomology.Torsors.Generators.unitsAddSheaf` of the small étale *ringed* site, which
Stacks Tag 03P8 is stated for. The two underlying presheaves are the same composite of functors
and the sheaf conditions are proofs of one proposition, so the two sheaves are equal by `rfl` —
but not at reducible transparency, so `rw` across the two spellings fails its motive check.
`AlgebraicGeometry.etaleH1UnitsEquivPicard` restates the identification once in the Kummer
spelling, and everything downstream stays there.

**Which clauses of Tag 03RQ are not here.** The source's first list has four clauses and its
second, noncanonical list has four more; degrees `0` and `1` of both lists are here, and see
the note on `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve` for the
complete accounting. In brief:

* `q = 2`, `H²_ét(X, μ_n) = 𝐙/n𝐙`, and `q ≥ 3`, `H^q_ét(X, μ_n) = 0`, both need Stacks Tag
  03RM, the vanishing of `H^q_ét(X, 𝐆_m)` for `q ≥ 2` on a smooth curve. That tag is proved as
  `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_smoothCurve`, but over an
  explicit hypothesis `h03Q9` which bundles Stacks Tag 03Q9 with two further steps of the source's
  proof; the library has Tag 03Q9 itself, as `AlgebraicGeometry.stalkHigherDirectImageIso`, but
  does not discharge that bundled hypothesis from it, so it cannot discharge a clause here. The sheaf-level fundamental
  exact sequence of Stacks Tag 03RI and Stacks Tag 03RJ are not hypotheses of it: they are
  proved as `Stacks.EtaleCohomology.fundamentalSequence_shortExact` and
  `Stacks.EtaleCohomology.isZero_rightDerived_genericPointDirectImage_multiplicativeSheaf`. It is
  also stated on Mathlib's small étale site, for `Stacks.Kummer.multiplicativeSheaf`, so a
  comparison of sites would be needed in addition. The clause `q = 2` needs further Stacks
  Tag 03RP, the surjectivity of multiplication by `n` on `Pic⁰`: the exact sequence
  `0 → Pic⁰(X) → Pic(X) → 𝐙 → 0` gives `Pic(X)/n·Pic(X) = 𝐙/n𝐙` only once `Pic⁰(X)` is
  `n`-divisible, which is what makes `Pic⁰` an abelian variety. Of Tag 03RP the library records
  commutativity of a proper geometrically integral group scheme, on
  `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`, and the surjectivity of
  `[n]` on an abelian variety whose `[n]` is flat, on
  `Stacks.Groupoids.surjective_zpow_id_left_of_flat` and
  `Stacks.Groupoids.exists_zpow_eq_of_flat`; what it has not got is an abelian variety to apply
  those to, having the Picard *functor* `Stacks.PicardFunctor.picardFunctor` but no
  representability of it for a curve, hence no `Pic⁰` as a scheme and no abelian-variety
  structure on it.
* the `q = 2` and `q ≥ 3` clauses of the second list rest on those of the first and are absent
  for the same reason. Its `q = 1` clause is stated here as `Pic⁰(X)[n]`; the shape
  `(𝐙/n𝐙)^{2g}` the source gives it is Stacks Tag 0BA0 together with Stacks Tag 03RP, needing
  `Pic⁰` as a `g`-dimensional abelian variety, and the genus enters nowhere in what is proved
  here.

Those two accounts remain accurate for this file. What has since been proved, elsewhere and
conditionally, is in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityDegreeTwoPicard`, which
carries degree two and the degrees `q ≥ 3` of the first list on this same site and at this same
coefficient universe, and in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAllDegrees`, which transports
them to the second list, puts `AlgebraicGeometry.genus` into its degree one, and assembles all
eight clauses. The cohomological half of degree two is unconditional there: the Kummer
connecting homomorphism is a canonical map `Pic(X) ⟶ H²_ét(X, μ_n)` whose kernel is `n·Pic(X)`
and whose image is the kernel of `H²(X, μ_n) ⟶ H²(X, 𝐆_m)`, proved under exactly the hypotheses
this file's clauses already carry. Of the three hypotheses those files carry, two are no longer
open: Stacks Tag 03RM on this site is
`AlgebraicGeometry.subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve`, unconditional, and the
surjectivity of `AlgebraicGeometry.picardDegree` is
`AlgebraicGeometry.surjective_curvePicardDegree`; the assemblies with both supplied are in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAllDegreesGmVanishing`. What
stays conditional is the `n`-divisibility of `Pic⁰(X)`, and — for the second list's degree one
only — the identification `Pic⁰(X)[n] ≅ (𝐙/n𝐙)^{2g}`.

The `HasExt` hypothesis is carried rather than discharged because the universe in which the
`Ext`-groups live is a parameter of `HasExt` and is not determined by the site, exactly as in
`StacksFrontier/AlgebraicGeometry/Picard/SmallEtaleSiteFirstCohomology.lean`.

## References

* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
* [Stacks Project, Tag 03P8](https://stacks.math.columbia.edu/tag/03P8)
* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe t u

namespace AlgebraicGeometry

open AlgebraicGeometry.SmallEtale (zariskiStructureIsSheaf)

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

/-- The Kummer sequence `μ_n ⟶ 𝐆_m ⟶ 𝐆_m` on the small étale site of a scheme `X` of a big
étale site. -/
abbrev kummerSmallEtale (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (n : ℕ) :
    ShortComplex (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}) :=
  kummerSequence (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
    (unitsPresheaf_isSheaf_smallEtale B X hX) n

section KScheme

/-! ### What needs no properness

The Kummer sequence is short exact on the small étale site of any `k`-scheme on which `n` is
invertible, and the identification of `H¹_ét(X, 𝐆_m)` with `Pic(X)` and the description of the
image of `H¹_ét(X, μ_n)` in it as the `n`-torsion hold there too: properness enters only through
the *injectivity* of that map, which is where the global units have to be `n`-th powers. These
are therefore stated here, before any properness hypothesis, so that the affine curve of
[Stacks, Tag 03RR] can use them; see
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAffineCurve`. -/

variable (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  (B : BigEtaleSite.{u}) (hX : B.Contains X) (n : ℕ)

/-- A natural number invertible in a field is nonzero. -/
theorem ne_zero_of_isUnit_natCast (hn : IsUnit (n : k)) : n ≠ 0 := by
  rintro rfl
  simp at hn

include f in
/-- A natural number invertible in the base field is an invertible global function. -/
theorem isUnit_natCast_globalSections (hn : IsUnit (n : k)) :
    IsUnit ((n : ℕ) : Γ(X, ⊤)) := by
  simpa only [map_natCast] using hn.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

include f in
/-- The Kummer sequence is short exact on the small étale site of a `k`-scheme when `n` is
invertible in `k`. -/
@[sga "4 IX 3.2" "special case", sga "4½ Arcata 2.2.5" "special case"]
theorem kummerSmallEtale_shortExact (hn : IsUnit (n : k)) :
    (kummerSmallEtale B X hX n).ShortExact :=
  kummerSequence_shortExact_smallEtale B X hX n (isUnit_natCast_globalSections k X f n hn)

variable [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]

/-- **Stacks Tag 03P8 on the small étale site, in the Kummer spelling of `𝐆_m`.** The sheaf of
units of the small étale ringed site and the middle term of the Kummer sequence are the same
abelian sheaf, so `Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivZariskiPicardGroup` is an
identification of `H¹_ét(X, 𝐆_m)` with `Pic(X)` in this spelling too.

The two spellings agree definitionally but not at reducible transparency, so the identification
is restated here rather than transported; everything downstream then stays in one spelling. -/
def etaleH1UnitsEquivPicard :
    Sheaf.H (kummerSmallEtale B X hX n).X₂ 1 ≃+ schemePicard X :=
  Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivZariskiPicardGroup B X hX

/-- **The canonical map `H¹_ét(X, μ_n) ⟶ Pic(X)`**: the map induced by the inclusion
`μ_n ⟶ 𝐆_m` of the Kummer sequence, followed by the identification
`H¹_ét(X, 𝐆_m) = Pic(X)` of Stacks Tag 03P8. -/
def etaleH1RootsOfUnityToPicard :
    Sheaf.H (kummerSmallEtale B X hX n).X₁ 1 →+ schemePicard X :=
  (etaleH1UnitsEquivPicard X B hX n).toAddMonoidHom.comp
    (Sheaf.H.map (kummerSmallEtale B X hX n).f 1)

/-- `etaleH1RootsOfUnityToPicard` is the map induced by `μ_n ⟶ 𝐆_m` on `H¹_ét` followed by the
identification `H¹_ét(X, 𝐆_m) = Pic(X)`. -/
@[simp] theorem etaleH1RootsOfUnityToPicard_apply
    (x : Sheaf.H (kummerSmallEtale B X hX n).X₁ 1) :
    etaleH1RootsOfUnityToPicard X B hX n x =
      etaleH1UnitsEquivPicard X B hX n (Sheaf.H.map (kummerSmallEtale B X hX n).f 1 x) :=
  rfl

include f in
/-- **The image of `H¹_ét(X, μ_n)` in `Pic(X)` is exactly the `n`-torsion**: the second map of
the Kummer sequence induces multiplication by `n` on first cohomology. -/
@[sga "4 IX 4.7" "partial", sga "4½ Arcata 2.2.4" "Exactness at H¹(X"]
theorem mem_range_etaleH1RootsOfUnityToPicard_iff (hn : IsUnit (n : k))
    (y : schemePicard X) :
    (∃ x, etaleH1RootsOfUnityToPicard X B hX n x = y) ↔ n • y = 0 := by
  have key := exists_kummerFirstCohomologyMap_iff (SmallEtale.topology B X hX)
    (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX) n
    (kummerSmallEtale_shortExact k X f B hX n hn)
  refine ⟨?_, fun hy => ?_⟩
  · rintro ⟨x, rfl⟩
    rw [etaleH1RootsOfUnityToPicard_apply, ← map_nsmul, (key _).1 ⟨x, rfl⟩, map_zero]
  · have hy' : n • (etaleH1UnitsEquivPicard X B hX n).symm y = 0 := by
      rw [← map_nsmul, hy, map_zero]
    obtain ⟨x, hx⟩ := (key _).2 hy'
    exact ⟨x, by rw [etaleH1RootsOfUnityToPicard_apply, hx, AddEquiv.apply_symm_apply]⟩

end KScheme

section ProperVariety

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [IsProperVariety k f] (B : BigEtaleSite.{u}) (hX : B.Contains X) (n : ℕ)

include f in
/-- Every invertible global function on a proper variety over an algebraically closed field is
an `n`-th power, for every `n ≥ 1`. -/
theorem exists_units_pow_eq_of_isAlgClosed (hn0 : n ≠ 0) (s : Γ(X, ⊤)ˣ) :
    ∃ u : Γ(X, ⊤)ˣ, s = u ^ n := by
  obtain ⟨c, hc⟩ := forall_units_mem_range_of_isAlgClosed k f s
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (c : k) (Nat.pos_of_ne_zero hn0)
  have hd0 : d ≠ 0 := ne_zero_pow hn0 (hd ▸ c.ne_zero)
  refine ⟨Units.map (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).toMonoidHom
    (Units.mk0 d hd0), ?_⟩
  rw [← hc, ← map_pow]
  exact congrArg _ (Units.ext (by simpa using hd.symm))

variable [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]

include f in
/-- **The canonical map `H¹_ét(X, μ_n) ⟶ H¹_ét(X, 𝐆_m)` is injective** on a proper variety over
an algebraically closed field: its kernel is the group of global units modulo `n`-th powers,
and every global unit is an `n`-th power. -/
theorem injective_kummerSmallEtale_firstCohomologyMap (hn : IsUnit (n : k)) (hn0 : n ≠ 0) :
    Function.Injective (Sheaf.H.map (kummerSmallEtale B X hX n).f 1) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := (exists_kummerBoundary_iff (SmallEtale.topology B X hX)
    (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX) n
    (kummerSmallEtale_shortExact k X f B hX n hn) (SmallEtale.finalIsTerminal B X hX) x).2 hx
  exact (kummerBoundary_eq_zero_iff (SmallEtale.topology B X hX)
    (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX) n
    (kummerSmallEtale_shortExact k X f B hX n hn) (SmallEtale.finalIsTerminal B X hX) a).2
    (exists_units_pow_eq_of_isAlgClosed k X f n hn0 a)

include f in
/-- **The canonical map `H¹_ét(X, μ_n) ⟶ Pic(X)` is injective** on a proper variety over an
algebraically closed field. -/
theorem injective_etaleH1RootsOfUnityToPicard (hn : IsUnit (n : k)) (hn0 : n ≠ 0) :
    Function.Injective (etaleH1RootsOfUnityToPicard X B hX n) :=
  (etaleH1UnitsEquivPicard X B hX n).injective.comp
    (injective_kummerSmallEtale_firstCohomologyMap k X f B hX n hn hn0)

end ProperVariety

section Curve

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [IsCurve k f] [IsProjectiveVariety k f] (B : BigEtaleSite.{u}) (hX : B.Contains X) (n : ℕ)

include f in
omit [IsAlgClosed k] [IsProjectiveVariety k f] in
/-- A curve has topological Krull dimension at most one. -/
theorem topologicalKrullDim_le_one_of_isCurve : topologicalKrullDim X ≤ 1 :=
  (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le

/-- `Pic⁰(X)`, the degree-zero Picard group of a projective curve. -/
abbrev curvePicardDegreeZero : AddSubgroup (schemePicard X) :=
  picardDegreeZero k f (topologicalKrullDim_le_one_of_isCurve k X f)

/-- `Pic⁰(X)[n]`, the `n`-torsion of the degree-zero Picard group of a projective curve. -/
def curvePicardDegreeZeroTorsion : AddSubgroup ↥(curvePicardDegreeZero k X f) where
  carrier := {x | n • x = 0}
  add_mem' ha hb := by simp_all [smul_add]
  zero_mem' := by simp
  neg_mem' ha := by simp_all

omit [IsAlgClosed k] in
/-- A degree-zero class lies in `Pic⁰(X)[n]` exactly when `n` kills it. -/
@[simp] theorem mem_curvePicardDegreeZeroTorsion_iff
    (x : ↥(curvePicardDegreeZero k X f)) :
    x ∈ curvePicardDegreeZeroTorsion k X f n ↔ n • x = 0 := Iff.rfl

variable [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]

/-- **The canonical map `H¹_ét(X, μ_n) ⟶ Pic⁰(X)[n]`** of a smooth projective curve over an
algebraically closed field: the canonical map to `Pic(X)` has image in the `n`-torsion, and a
torsion class has degree zero. -/
def etaleH1RootsOfUnityToCurvePicardDegreeZeroTorsion (hn : IsUnit (n : k)) :
    Sheaf.H (kummerSmallEtale B X hX n).X₁ 1 →+
      ↥(curvePicardDegreeZeroTorsion k X f n) :=
  ((etaleH1RootsOfUnityToPicard X B hX n).codRestrict (curvePicardDegreeZero k X f)
    (fun x => mem_picardDegreeZero_of_nsmul_eq_zero k f
      (topologicalKrullDim_le_one_of_isCurve k X f)
      (ne_zero_of_isUnit_natCast k n hn) _
      ((mem_range_etaleH1RootsOfUnityToPicard_iff k X f B hX n hn _).1
        ⟨x, rfl⟩))).codRestrict (curvePicardDegreeZeroTorsion k X f n)
    (fun x => Subtype.ext (by
      simpa using (mem_range_etaleH1RootsOfUnityToPicard_iff k X f B hX n hn _).1 ⟨x, rfl⟩))

omit [IsAlgClosed k] in
/-- The class in `Pic(X)` of the image of `x` in `Pic⁰(X)[n]` is the image of `x` under
`etaleH1RootsOfUnityToPicard`. -/
@[simp] theorem etaleH1RootsOfUnityToCurvePicardDegreeZeroTorsion_coe
    (hn : IsUnit (n : k)) (x : Sheaf.H (kummerSmallEtale B X hX n).X₁ 1) :
    ((etaleH1RootsOfUnityToCurvePicardDegreeZeroTorsion k X f B hX n hn x :
        ↥(curvePicardDegreeZero k X f)) : schemePicard X) =
      etaleH1RootsOfUnityToPicard X B hX n x :=
  rfl

/-- **`H¹_ét(X, μ_n) = Pic⁰(X)[n]`** for a smooth projective curve over an algebraically closed
field, with `n` invertible in the field: the canonical map is bijective. -/
theorem bijective_etaleH1RootsOfUnityToCurvePicardDegreeZeroTorsion (hn : IsUnit (n : k)) :
    Function.Bijective
      (etaleH1RootsOfUnityToCurvePicardDegreeZeroTorsion k X f B hX n hn) := by
  refine ⟨fun x y hxy => injective_etaleH1RootsOfUnityToPicard k X f B hX n hn
    (ne_zero_of_isUnit_natCast k n hn)
    (congrArg (fun z : ↥(curvePicardDegreeZeroTorsion k X f n) =>
      ((z : ↥(curvePicardDegreeZero k X f)) : schemePicard X)) hxy), ?_⟩
  rintro ⟨⟨y, hy0⟩, hytors⟩
  obtain ⟨x, hx⟩ := (mem_range_etaleH1RootsOfUnityToPicard_iff k X f B hX n hn y).2
    (congrArg Subtype.val hytors)
  exact ⟨x, Subtype.ext (Subtype.ext hx)⟩

/-! ### Constant coefficients

The source's second list of identifications is obtained from the first by the isomorphism of
abelian sheaves `μ_n ≅ 𝐙/n𝐙` on the small étale site,
`AlgebraicGeometry.constantZModSheafIsoRootsOfUnitySheaf`. That isomorphism depends on a choice
of isomorphism `𝐙/n𝐙 ≅ μ_n(k)`, which is what makes the resulting identifications
noncanonical: they are asserted as the existence of an isomorphism, not of a named map. -/

/-- Cohomology transports along an isomorphism of abelian sheaves. -/
def sheafHAddEquivOfIso {C : Type*} [Category C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{t} (Sheaf J AddCommGrpCat.{u})]
    {F G : Sheaf J AddCommGrpCat.{u}} (e : F ≅ G) (q : ℕ) :
    Sheaf.H.{t, u} F q ≃+ Sheaf.H.{t, u} G q :=
  ((Sheaf.functorH J q).mapIso e).addCommGroupIsoToAddEquiv

/-- `μ_n` on the small étale site, in the spelling the degree-zero comparison of Tag 03RR is
stated in; the first term of `AlgebraicGeometry.kummerSmallEtale` by definition. -/
@[sga "4 IX 3.0", sga "4½ Arcata 2.2.4"]
abbrev smallEtaleRootsOfUnitySheaf (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (n : ℕ) : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u} :=
  rootsOfUnitySheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
    (unitsPresheaf_isSheaf_smallEtale B X hX) n

/-- **`H⁰_ét(X, μ_n) = μ_n(Γ(X, 𝒪_X))` as abelian groups.** The underlying bijection is
`AlgebraicGeometry.etaleH0EquivRootsOfUnitySections`; additivity is read off from its
characterisation by the inclusion `μ_n ⟶ 𝐆_m`. -/
def etaleH0RootsOfUnityAddEquiv :
    Sheaf.H (smallEtaleRootsOfUnitySheaf B X hX n) 0 ≃+
      Additive ↥(_root_.rootsOfUnity n (Scheme.Γ.obj (Opposite.op X))) where
  toEquiv := etaleH0EquivRootsOfUnitySections B X hX n
  map_add' x y := by
    apply Subtype.ext
    change (etaleH0EquivRootsOfUnitySections B X hX n (x + y)).1 =
      (etaleH0EquivRootsOfUnitySections B X hX n x).1 *
        (etaleH0EquivRootsOfUnitySections B X hX n y).1
    rw [etaleH0EquivRootsOfUnitySections_val, etaleH0EquivRootsOfUnitySections_val,
      etaleH0EquivRootsOfUnitySections_val, map_add]
    exact (congrArg Additive.toMul (map_add _ _ _)).trans (toMul_add _ _)

include f in
omit [IsAlgClosed k] [IsCurve k f] in
/-- The global functions of a curve over a field form a domain, the curve being integral. -/
theorem isDomain_globalSections : IsDomain (Scheme.Γ.obj (Opposite.op X)) :=
  inferInstanceAs (IsDomain Γ(X, ⊤))

include f in
omit [IsCurve k f] in
/-- The degree-zero roots-of-unity cohomology of a smooth projective curve over an
algebraically closed field has exactly `n` elements: the global roots of unity of an integral
scheme over an algebraically closed field are the constants, and `k` has `n` of them. -/
theorem etaleH0RootsOfUnity_card (hn : IsUnit (n : k)) :
    Nat.card (Sheaf.H (smallEtaleRootsOfUnitySheaf B X hX n) 0) = n := by
  calc
    _ = Nat.card (Additive ↥(_root_.rootsOfUnity n (Scheme.Γ.obj (Opposite.op X)))) :=
      Nat.card_congr (etaleH0RootsOfUnityAddEquiv X B hX n).toEquiv
    _ = Nat.card ↥(_root_.rootsOfUnity n (Scheme.Γ.obj (Opposite.op X))) :=
      Nat.card_congr Additive.toMul
    _ = Nat.card ↥(_root_.rootsOfUnity n (Scheme.Γ.obj (Opposite.op (Spec (.of k))))) :=
      (Nat.card_eq_of_bijective ((rootsOfUnitySections n).map f.op)
        (rootsOfUnitySections_bijective_of_isIntegral k f n
          (Nat.pos_of_ne_zero (ne_zero_of_isUnit_natCast k n hn)))).symm
    _ = Nat.card ↥(_root_.rootsOfUnity n k) :=
      Nat.card_congr ((Scheme.ΓSpecIso
        (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.restrictRootsOfUnity n).toEquiv
    _ = n := by
      have : NeZero n := ⟨ne_zero_of_isUnit_natCast k n hn⟩
      have : NeZero (n : k) := ⟨hn.ne_zero⟩
      exact HasEnoughRootsOfUnity.natCard_rootsOfUnity k n

include f in
omit [IsCurve k f] in
/-- **`H⁰_ét(X, 𝐙/n𝐙) ≅ 𝐙/n𝐙`**, the `q = 0` clause of the noncanonical list of Stacks Tag
03RQ: the constant sheaf is `μ_n`, whose degree-zero cohomology is the cyclic group `μ_n(k)` of
order `n`. -/
theorem nonempty_etaleH0ConstantZModAddEquiv [Smooth f] (hn : IsUnit (n : k)) :
    Nonempty (Sheaf.H
      ((constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod n)))) 0 ≃+ ZMod n) := by
  have : NeZero n := ⟨ne_zero_of_isUnit_natCast k n hn⟩
  have : IsDomain (Scheme.Γ.obj (Opposite.op X)) := isDomain_globalSections k X f
  have : IsAddCyclic (Sheaf.H (smallEtaleRootsOfUnitySheaf B X hX n) 0) :=
    (etaleH0RootsOfUnityAddEquiv X B hX n).symm.isAddCyclic.mp inferInstance
  have hc : Nat.card (Sheaf.H (smallEtaleRootsOfUnitySheaf B X hX n) 0) =
      Nat.card (ZMod n) := by
    rw [etaleH0RootsOfUnity_card k X f B hX n hn, Nat.card_zmod]
  exact ⟨(sheafHAddEquivOfIso (SmallEtale.topology B X hX)
    (constantZModSheafIsoRootsOfUnitySheaf B k f hX n
      (Nat.pos_of_ne_zero (ne_zero_of_isUnit_natCast k n hn)) hn) 0).trans
    (addEquivOfAddCyclicCardEq hc)⟩

include f in
/-- **`H¹_ét(X, 𝐙/n𝐙) ≅ Pic⁰(X)[n]`**, the `q = 1` clause of the noncanonical list of Stacks
Tag 03RQ: the constant sheaf is `μ_n`, whose first cohomology is `Pic⁰(X)[n]`. -/
theorem nonempty_etaleH1ConstantZModAddEquiv [Smooth f] (hn : IsUnit (n : k)) :
    Nonempty (Sheaf.H
      ((constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod n)))) 1 ≃+
      ↥(curvePicardDegreeZeroTorsion k X f n)) :=
  ⟨(sheafHAddEquivOfIso (SmallEtale.topology B X hX)
    (constantZModSheafIsoRootsOfUnitySheaf B k f hX n
      (Nat.pos_of_ne_zero (ne_zero_of_isUnit_natCast k n hn)) hn) 1).trans
    (AddEquiv.ofBijective _
      (bijective_etaleH1RootsOfUnityToCurvePicardDegreeZeroTorsion k X f B hX n hn))⟩

/-- **The étale cohomology of a smooth projective curve with roots-of-unity and with constant
cyclic coefficients, in degrees `0` and `1`.** Let `X` be a smooth projective curve over an
algebraically closed field `k` and let `n ≥ 1` be invertible in `k`. Then:

* `H⁰_ét(X, μ_n) = μ_n(k)`, by pullback along the structure morphism;
* `H¹_ét(X, μ_n) = Pic⁰(X)[n]`, by the canonical map through the Kummer sequence and the
  identification `H¹_ét(X, 𝐆_m) = Pic(X)` of Stacks Tag 03P8;
* `H⁰_ét(X, 𝐙/n𝐙) ≅ 𝐙/n𝐙`;
* `H¹_ét(X, 𝐙/n𝐙) ≅ Pic⁰(X)[n]`.

The first two identifications are canonical: each is asserted of a named map, not merely of
some isomorphism. The last two are the source's noncanonical ones, obtained from the first two
along `AlgebraicGeometry.constantZModSheafIsoRootsOfUnitySheaf`, the isomorphism of abelian
sheaves `μ_n ≅ 𝐙/n𝐙`; they are asserted as the existence of an isomorphism, since the
isomorphism of sheaves itself depends on a choice of isomorphism `𝐙/n𝐙 ≅ μ_n(k)`.

This is a partial form of [Stacks, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ); the full
statement is `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus`. -/
theorem etaleCohomology_rootsOfUnity_smoothProjectiveCurve [Smooth f] (hn : IsUnit (n : k)) :
    Function.Bijective (baseRootsToEtaleH0 B k X hX f n) ∧
      Function.Bijective
        (etaleH1RootsOfUnityToCurvePicardDegreeZeroTorsion k X f B hX n hn) ∧
      Nonempty (Sheaf.H
        ((constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} (ZMod n)))) 0 ≃+ ZMod n) ∧
      Nonempty (Sheaf.H
        ((constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} (ZMod n)))) 1 ≃+
        ↥(curvePicardDegreeZeroTorsion k X f n)) :=
  ⟨baseRootsToEtaleH0_bijective_of_isCurve B k X hX f n hn,
    bijective_etaleH1RootsOfUnityToCurvePicardDegreeZeroTorsion k X f B hX n hn,
    nonempty_etaleH0ConstantZModAddEquiv k X f B hX n hn,
    nonempty_etaleH1ConstantZModAddEquiv k X f B hX n hn⟩

end Curve

end AlgebraicGeometry

end
