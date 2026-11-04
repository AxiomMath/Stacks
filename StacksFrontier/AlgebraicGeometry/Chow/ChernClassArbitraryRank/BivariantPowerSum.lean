module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PowerSumAlternatingSum
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.RankLocusChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ComplexChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorPowerSumsTotal
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup

/-!
# The power sums `P_p(ℰ)` of a finite locally free module in the bivariant ring

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be locally of
finite type over `S`. The *bivariant ring* of `X` is `Stacks.Chow.TotalChowClass`, the product
`∏_{p ≥ 0} A^p(X)` of the Chow cohomology groups of Stacks 0B7E under the Cauchy product of the
composites of Stacks 0B75; its degree-`p` component is `A^p(X)`.

For a finite locally free module of *constant* rank `r` the power sum `P_p(ℰ)` already lives
there: it is `Stacks.Chow.modulePowerSum`, Newton's recursion of Stacks 0F9B applied to the
components of the total Chern class `Stacks.Chow.totalChern` with the rank as the degree-zero
term. This file does two things with it.

* It identifies the operation of `P_p(ℰ)` on a test scheme `g : T ⟶ X` with the cap-operator
  power sum `Stacks.Chow.powerSumChernElem` of the pullback `g^*ℰ`
  (`Stacks.Chow.op_modulePowerSum`). Since a total class is determined by its operations
  (`Stacks.Chow.TotalChowClass.ext_op`), this is what carries an identity between cap-operator
  power sums — valid on every test scheme — to an identity in the bivariant ring.
* It removes the constant-rank hypothesis. The rank of a finite locally free module is a locally
  constant function, so `X` is the disjoint union of the open and closed loci `X_r` where it is
  `r` (`Stacks.Chow.isClopenDecomposition_rankLociFamily`), and `Stacks.Chow.TotalChowClass.glue`
  — Stacks 0FDZ in every degree — assembles the constant-rank power sums on the `X_r` into a
  single total class `Stacks.Chow.modulePowerSumArbitraryRank`, whose degree-`p` component is a
  class `P_p(ℰ) ∈ A^p(X)` for `ℰ` finite locally free of no assumed rank.

## Main definitions

* `Stacks.Chow.modulePowerSumArbitraryRank` — the power sum `P_p(ℰ)` of a finite locally free
  module whose rank need not be constant, as an element of the bivariant ring.
* `Stacks.Chow.modulePowerSumComponentArbitraryRank` — its degree-`p` component, the class
  `P_p(ℰ) ∈ A^p(X)`.

## Main results

* `Stacks.Chow.powerSumChernElem_eq_newtonPowerSum` — the cap-operator power sum of Stacks 0F9B
  is Newton's recursion in the ring of graded cap families.
* `Stacks.Chow.op_modulePowerSum` — the operation of `P_p(ℰ)` on a test scheme `g : T ⟶ X` is
  the cap-operator power sum of `g^*ℰ`.
* `Stacks.Chow.modulePowerSum_congr`, `Stacks.Chow.res_modulePowerSum` — `P_p` of a module of
  constant rank depends only on the isomorphism class, and restricts to `P_p` of the pullback.
* `Stacks.Chow.res_modulePowerSumArbitraryRank_rankLocus`,
  `Stacks.Chow.res_modulePowerSumArbitraryRank_of_constantRank` — the restriction of `P_p(ℰ)`
  along any morphism over which `ℰ` acquires a constant rank is the constant-rank power sum
  there. This is the characterization every identity below is read through.
* `Stacks.Chow.eq_modulePowerSumArbitraryRank_of_res_eq` — `P_p(ℰ)` is the only total class with
  those restrictions.

## Implementation notes

### Why the identification with the cap operators is the whole point

`Stacks.Chow.TotalChowClass` is a ring but not a commutative one, its multiplication being
composition of bivariant classes, so the universal power-sum polynomial of Stacks 0F9B cannot be
evaluated in it by `AlgebraicGeometry.powerSumOfChernClasses`, which goes through
`MvPolynomial.eval₂Hom`. Newton's recursion `AlgebraicGeometry.newtonPowerSum` writes every
product with a Chern class on the left and so evaluates in any ring; it is Stacks 0F9B's `P_p`
wherever that polynomial can be evaluated, by
`AlgebraicGeometry.newtonPowerSum_eq_powerSumOfChernClasses`. The operation on a test scheme is a
ring homomorphism into the graded cap families
(`Stacks.Chow.TotalChowClass.opRingHom`), and a ring homomorphism commutes with the recursion
(`AlgebraicGeometry.map_newtonPowerSum`), so the operation of `P_p` is the `P_p` of the
operations — which, the Chern classes of Stacks 0B7H being built from the cap products of
Stacks 02U6, is `Stacks.Chow.powerSumChernElem` of the pullback.

### The rank hypothesis is an argument, not an instance

`Stacks.Chow.modulePowerSum` takes the constant rank as an explicit hypothesis rather than an
instance, because the ranks vary over the loci and the instance cannot be inferred there. The
statements below follow that convention; the rank of a pullback is
`AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback`, Stacks 02U9.

### The two spellings of finite local freeness

A tensor product of finite locally free modules is finite locally free, Stacks 0FDK; the
instance `AlgebraicGeometry.isFiniteLocallyFree_tensorObj` is stated for the class
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree` and for the spelling
`AlgebraicGeometry.Scheme.Modules.tensorObjRingedSpace` of the tensor product, while the rank loci
of `StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.RankLoci` are cut out using
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` and
`AlgebraicGeometry.Scheme.Modules.tensorObj`. The two tensor products are the same object and the
two classes have the same single field, so `Stacks.Chow.isFiniteLocallyFree_tensorObj` reads the
instance at the spelling used here.

## References

* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02U9](https://stacks.math.columbia.edu/tag/02U9)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Finite local freeness of a tensor product -/

/-- **Stacks 0FDK at the spelling used for the rank loci.** A tensor product of finite locally
free `𝒪_X`-modules is finite locally free. This is
`AlgebraicGeometry.isFiniteLocallyFree_tensorObj`, read for the class
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` and the tensor product
`AlgebraicGeometry.Scheme.Modules.tensorObj`. -/
instance isFiniteLocallyFree_tensorObj {X : Scheme.{u}} (E₁ E₂ : X.Modules)
    [h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E₁]
    [h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E₂] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Scheme.Modules.tensorObj E₁ E₂) :=
  ⟨(@AlgebraicGeometry.isFiniteLocallyFree_tensorObj X E₁ E₂
      ⟨h₁.exists_isFiniteLocallyFreeData⟩
      ⟨h₂.exists_isFiniteLocallyFreeData⟩).exists_isFiniteLocallyFreeData⟩

/-! ### The cap-operator power sum as Newton's recursion -/

section Operation

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The cap-operator power sum is Newton's recursion.** `Stacks.Chow.powerSumChernElem`, the
value of the universal power-sum polynomial of Stacks 0F9B at the rank and the Chern classes
inside the commutative subring they generate, is `AlgebraicGeometry.newtonPowerSum` started at
the rank and fed the homogeneous components of the total Chern class, computed in the whole ring
of graded cap families. The inclusion of the subring is a ring homomorphism, so it carries the
recursion to the recursion. -/
theorem powerSumChernElem_eq_newtonPowerSum (F : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (p : ℕ) :
    powerSumChernElem C sX F r p
      = AlgebraicGeometry.newtonPowerSum ((r : ℕ) : GradedCapFamily (chowGroup C sX))
          (fun i : ℕ+ ↦ homComponent (i : ℕ) (GenuineChern.chernFamily C sX F r)) p := by
  have hmap := AlgebraicGeometry.map_newtonPowerSum (Subring.subtype (chernSubring C sX))
    ((r : ℕ) : chernSubring C sX) (fun i : ℕ+ ↦ chernClassSub C sX F r (i : ℕ)) p
  simp only [Subring.coe_subtype, map_natCast, coe_chernClassSub] at hmap
  rw [powerSumChernElem, ← AlgebraicGeometry.newtonPowerSum_eq_powerSumOfChernClasses]
  exact hmap

/-- **The operation of the power sum of a module of constant rank.** On a test scheme
`g : T ⟶ X` the total class `P_p(ℰ)` of the bivariant ring operates as the cap-operator power sum
`P_p(g^*ℰ)` of Stacks 0F9B. The operation is a ring homomorphism and commutes with taking
homogeneous components, so it commutes with Newton's recursion; the total Chern class operates as
the total Chern class of the pullback, by `Stacks.Chow.op_totalChern`. -/
theorem op_modulePowerSum (F : X.Modules) (r : ℕ)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r) (p : ℕ)
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] :
    haveI := hF
    haveI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g F r
    (modulePowerSum C sX F r hF p).op g
      = powerSumChernElem C (g ≫ sX) ((Scheme.Modules.pullback g).obj F) r p := by
  let := hF
  let := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g F r
  rw [modulePowerSum, TotalChowClass.op_newtonPowerSum, op_totalChern,
    powerSumChernElem_eq_newtonPowerSum]
  congr 1
  rw [TotalChowClass.op_zsmul, TotalChowClass.op_one, zsmul_eq_mul, mul_one, Int.cast_natCast]

/-- **The power sum of a module of constant rank depends only on its isomorphism class**, and on
the rank only through its value. Both sides operate on every test scheme by the cap-operator
power sum of the pullback, and those agree by
`Stacks.Chow.powerSumChernElem_congr`. -/
theorem modulePowerSum_congr {F F' : X.Modules} {r r' : ℕ}
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r)
    (hF' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' r')
    (e : F' ≅ F) (h : r' = r) (p : ℕ) :
    modulePowerSum C sX F' r' hF' p = modulePowerSum C sX F r hF p := by
  refine TotalChowClass.ext_op fun g _ ↦ ?_
  let := hF
  let := hF'
  let := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g F r
  let := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g F' r'
  rw [op_modulePowerSum, op_modulePowerSum]
  exact powerSumChernElem_congr C (g ≫ sX) ((Scheme.Modules.pullback g).mapIso e) h p

end Operation

/-! ### Restriction of the power sum of a module of constant rank -/

section Restriction

variable (C : ChowSituation.{u}) {X X' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX']

/-- **Restriction of the power sum of a module of constant rank.** For `h : X' ⟶ X` the
restriction of `P_p(ℰ)` along `h` is `P_p(h^*ℰ)`: restriction is a ring homomorphism and commutes
with taking homogeneous components, so it commutes with Newton's recursion, and it carries the
total Chern class to the total Chern class of the pullback. -/
theorem res_modulePowerSum (F : X.Modules) (r : ℕ)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r)
    (h : X' ⟶ X) [LocallyOfFiniteType h] (hs : h ≫ sX = sX') (p : ℕ) :
    haveI := hF
    TotalChowClass.res h hs (modulePowerSum C sX F r hF p)
      = modulePowerSum C sX' ((Scheme.Modules.pullback h).obj F) r
          (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback h F r) p := by
  let := hF
  rw [modulePowerSum, AlgebraicGeometry.map_newtonPowerSum, modulePowerSum, map_zsmul, map_one]
  congr 1
  funext i
  rw [TotalChowClass.res_homComponent, TotalChowClass.res_totalChern]

end Restriction

/-! ### The power sum of a module whose rank is not constant -/

section ArbitraryRank

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (E : X.Modules) [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- On a member of the family of rank loci of `ℰ` the restriction of `ℰ` is finite locally free
of the constant rank indexing that member: the family is the rank loci themselves, reindexed in
the universe of the scheme. -/
theorem isFiniteLocallyFreeOfRank_pullback_rankLociFamily (r : ULift.{u} ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (rankLociFamily E r).ι).obj E) r.down :=
  isFiniteLocallyFreeOfRank_pullback_rankLocus E r.down

/-- **The power sum `P_p(ℰ)` of a finite locally free module whose rank need not be constant**, as
an element of the bivariant ring `∏_{q ≥ 0} A^q(X)`: on the open and closed locus `X_r` where the
rank of `ℰ` is `r` the module has constant rank and `P_p(ℰ|_{X_r})` is available, and these are
assembled over the rank loci by Stacks 0FDZ in every degree. -/
def modulePowerSumArbitraryRank (p : ℕ) : TotalChowClass C sX :=
  TotalChowClass.glue (isClopenDecomposition_rankLociFamily E) fun r ↦
    modulePowerSum C ((rankLociFamily E r).ι ≫ sX)
      ((Scheme.Modules.pullback (rankLociFamily E r).ι).obj E) r.down
      (isFiniteLocallyFreeOfRank_pullback_rankLociFamily E r) p

/-- **The restriction of `P_p(ℰ)` to a member of the family of rank loci** is the power sum of
the constant-rank restriction there. This is the form the index type of Stacks 0FDZ takes. -/
theorem res_modulePowerSumArbitraryRank_rankLociFamily (p : ℕ) (r : ULift.{u} ℕ) :
    TotalChowClass.res (rankLociFamily E r).ι rfl (modulePowerSumArbitraryRank C sX E p)
      = modulePowerSum C ((rankLociFamily E r).ι ≫ sX)
          ((Scheme.Modules.pullback (rankLociFamily E r).ι).obj E) r.down
          (isFiniteLocallyFreeOfRank_pullback_rankLociFamily E r) p :=
  TotalChowClass.res_glue (isClopenDecomposition_rankLociFamily E) _ r

/-- **The restriction of `P_p(ℰ)` to a rank locus** is the power sum of the constant-rank
restriction `ℰ|_{X_r}`. -/
theorem res_modulePowerSumArbitraryRank_rankLocus (p r : ℕ) :
    TotalChowClass.res (rankLocus E r).ι rfl (modulePowerSumArbitraryRank C sX E p)
      = modulePowerSum C ((rankLocus E r).ι ≫ sX)
          ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r
          (isFiniteLocallyFreeOfRank_pullback_rankLocus E r) p :=
  res_modulePowerSumArbitraryRank_rankLociFamily C sX E p (ULift.up r)

/-- **`P_p(ℰ)` is the only total class with those restrictions to the rank loci.** -/
theorem eq_modulePowerSumArbitraryRank_of_res_eq (p : ℕ) {c : TotalChowClass C sX}
    (h : ∀ r : ℕ, TotalChowClass.res (rankLocus E r).ι rfl c
      = modulePowerSum C ((rankLocus E r).ι ≫ sX)
          ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r
          (isFiniteLocallyFreeOfRank_pullback_rankLocus E r) p) :
    c = modulePowerSumArbitraryRank C sX E p :=
  TotalChowClass.eq_glue (isClopenDecomposition_rankLociFamily E) fun r ↦ h r.down

/-- **The degree-`p` component `P_p(ℰ) ∈ A^p(X)`** of the power sum of a finite locally free
module whose rank need not be constant. -/
def modulePowerSumComponentArbitraryRank (p : ℕ) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sX (p : ℤ) :=
  modulePowerSumArbitraryRank C sX E p p

/-- The degree-`p` component of `P_p(ℰ)` is the class `P_p(ℰ) ∈ A^p(X)`. -/
theorem modulePowerSumComponentArbitraryRank_eq (p : ℕ) :
    modulePowerSumComponentArbitraryRank C sX E p = modulePowerSumArbitraryRank C sX E p p :=
  rfl

/-- **Characterization of `P_p(ℰ)`.** Along every `h : X' ⟶ X` over which the pullback `h^*ℰ`
has constant rank `r`, the restriction of `P_p(ℰ)` is the constant-rank power sum `P_p(h^*ℰ)`.
The rank loci of `ℰ` pull back to a decomposition of `X'` into open and closed subschemes, and on
a nonempty member of it the rank of the pullback is both `r` and the index of the locus, the rank
of a finite locally free module on a nonempty scheme being determined; an empty member carries
only one total class. -/
theorem res_modulePowerSumArbitraryRank_of_constantRank {X' : Scheme.{u}} {sX' : X' ⟶ C.S}
    [LocallyOfFiniteType sX'] (h : X' ⟶ X) [LocallyOfFiniteType h] (hs : h ≫ sX = sX') (r : ℕ)
    (hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback h).obj E) r) (p : ℕ) :
    TotalChowClass.res h hs (modulePowerSumArbitraryRank C sX E p)
      = modulePowerSum C sX' ((Scheme.Modules.pullback h).obj E) r hr p := by
  have hU := isClopenDecomposition_rankLociFamily E
  refine TotalChowClass.eq_of_res_eq (hU.preimage h) fun r' ↦ ?_
  have ha : ∀ r', h ⁻¹ᵁ rankLociFamily E r' ≤ h ⁻¹ᵁ rankLociFamily E (id r') := fun _ ↦ le_rfl
  have hfac : (h ⁻¹ᵁ rankLociFamily E r').ι ≫ h =
      pieceMap h (fun r' ↦ h ⁻¹ᵁ rankLociFamily E r') (rankLociFamily E) id ha r' ≫
        (rankLociFamily E r').ι :=
    (pieceMap_comp_ι h _ _ id ha r').symm
  have hpm : pieceMap h (fun r' ↦ h ⁻¹ᵁ rankLociFamily E r') (rankLociFamily E) id ha r' ≫
      ((rankLociFamily E r').ι ≫ sX) = (h ⁻¹ᵁ rankLociFamily E r').ι ≫ sX' := by
    rw [← Category.assoc, ← hfac, Category.assoc, hs]
  rw [TotalChowClass.res_res, TotalChowClass.res_congr hfac _ (by rw [Category.assoc, hpm]),
    ← TotalChowClass.res_res (rankLociFamily E r').ι rfl _ hpm,
    res_modulePowerSumArbitraryRank_rankLociFamily, res_modulePowerSum, res_modulePowerSum]
  rcases isEmpty_or_nonempty (h ⁻¹ᵁ rankLociFamily E r').toScheme with _ | hne
  · exact (TotalChowClass.subsingleton_of_isEmpty _).elim _ _
  · obtain ⟨w⟩ := hne
    have := isFiniteLocallyFreeOfRank_pullback_rankLociFamily E r'
    have := hr
    have h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (h ⁻¹ᵁ rankLociFamily E r').ι).obj
          ((Scheme.Modules.pullback h).obj E)) r'.down :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
        (pullbackPullbackIsoOfComp hfac E).symm
        (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ r'.down)
    have hrank : r'.down = r :=
      AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_unique _ h1
        (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ r) w
    exact modulePowerSum_congr C _ _ _ (pullbackPullbackIsoOfComp hfac.symm E) hrank p

/-- **`P_p(ℰ)` for a module of globally constant rank** is the constant-rank power sum: the
rank-`r` locus is the whole of `X` and every other rank locus is empty, so the assembly over the
rank loci has a single piece. -/
theorem modulePowerSumArbitraryRank_eq_modulePowerSum (r : ℕ)
    (hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) (p : ℕ) :
    modulePowerSumArbitraryRank C sX E p = modulePowerSum C sX E r hr p := by
  let := hr
  refine (eq_modulePowerSumArbitraryRank_of_res_eq C sX E p fun r' ↦ ?_).symm
  rw [res_modulePowerSum]
  rcases eq_or_ne r' r with rfl | hne
  · rfl
  · have hb : ((rankLocus E r' : X.Opens) : Set X) = ∅ := by
      rw [rankLocus_eq_bot_of_ne E r r' hne]; rfl
    have : IsEmpty (rankLocus E r').toScheme :=
      ⟨fun y ↦ (Set.eq_empty_iff_forall_notMem.1 hb) y.1 y.2⟩
    exact (TotalChowClass.subsingleton_of_isEmpty _).elim _ _

end ArbitraryRank

end Stacks.Chow

end
