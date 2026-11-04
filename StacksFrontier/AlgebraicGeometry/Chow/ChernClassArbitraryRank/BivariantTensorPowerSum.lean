module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.BivariantPowerSum

/-!
# Stacks 0F9D in the bivariant ring, for finite locally free modules of any rank

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `ℰ₁` and `ℰ₂` be finite locally free `𝒪_X`-modules — of no assumed
rank — and let `P_p` be the universal power-sum polynomial of Stacks 0F9B. This file proves the
more precise conclusion of [Stacks, Tag 0F9D](https://stacks.math.columbia.edu/tag/0F9D),

  `P_p(ℰ₁ ⊗_{𝒪_X} ℰ₂) = ∑_{p₁ + p₂ = p} C(p, p₁) P_{p₁}(ℰ₁) P_{p₂}(ℰ₂)`,

in `A^p(X)`: the classes are the components of the elements
`Stacks.Chow.modulePowerSumArbitraryRank` of the bivariant ring
`Stacks.Chow.TotalChowClass = ∏_{q ≥ 0} A^q(X)` and every product is the composition of bivariant
classes of Stacks 0B75, which is that ring's multiplication.

## How the ranks are removed

The rank of a finite locally free module is locally constant, so `X` is the disjoint union of the
open and closed loci where it takes each value. For *two* modules the identity cannot be read on
either decomposition alone: it is read on the common refinement, the loci where `ℰ₁` has constant
rank `r` and `ℰ₂` has constant rank `s`, which is `Stacks.Chow.eq_of_res_eq_of_constantModuleRanks`
below — the rank loci of `ℰ₁`, refined inside each of them by the rank loci of the restriction of
`ℰ₂`. On such a locus `ℰ₁ ⊗ ℰ₂` has constant rank `r · s` by Stacks 02U9, the power sums are the
constant-rank ones by
`Stacks.Chow.res_modulePowerSumArbitraryRank_of_constantRank`, and the identity there is
`Stacks.Chow.modulePowerSum_tensorObj`. Restriction is a homomorphism of rings
(`Stacks.Chow.TotalChowClass.res`), so it carries the right-hand side term by term.

## How the constant-rank identity reaches the bivariant ring

A total class is determined by its operations on the test schemes
(`Stacks.Chow.TotalChowClass.ext_op`) and the operation on each test scheme is a ring
homomorphism, carrying the bivariant power sum of a module to the cap-operator power sum of its
pullback (`Stacks.Chow.op_modulePowerSum`). So the constant-rank identity in the bivariant ring is
the cap-operator identity `Stacks.Chow.powerSumChernElem_tensorObj` — the splitting-principle
argument of the source, performed there — read on *every* test scheme `g : T ⟶ X` at once, for the
pullbacks `g^*ℰ₁` and `g^*ℰ₂`. That is strictly more than the identity of cap operators on the
Chow groups of `X` itself, and it is what makes the conclusion an identity of bivariant classes.

## Main results

* `Stacks.Chow.modulePowerSum_tensorObj` — the identity in the bivariant ring for modules of
  constant ranks.
* `Stacks.Chow.eq_of_res_eq_of_constantModuleRanks` — two total classes agreeing after restriction
  along every morphism over which both modules acquire constant ranks are equal.
* `Stacks.Chow.modulePowerSumArbitraryRank_tensorObj` — **Stacks 0F9D**, the identity in the
  bivariant ring with no rank assumed.
* `Stacks.Chow.modulePowerSumComponentArbitraryRank_tensorObj` — **Stacks 0F9D**, the same
  identity read in `A^p(X)`.

## References

* [Stacks Project, Tag 0F9D](https://stacks.math.columbia.edu/tag/0F9D)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 02U9](https://stacks.math.columbia.edu/tag/02U9)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### The identity for modules of constant ranks -/

section ConstantRank

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **Stacks 0F9D in the bivariant ring, for constant ranks.** For `ℰ₁` of rank `r` and `ℰ₂` of
rank `s`,

  `P_p(ℰ₁ ⊗ ℰ₂) = ∑_{p₁ + p₂ = p} C(p, p₁) P_{p₁}(ℰ₁) P_{p₂}(ℰ₂)`

in `∏_{q ≥ 0} A^q(X)`. Both sides operate on every test scheme `g : T ⟶ X` by the corresponding
cap-operator identity for the pullbacks `g^*ℰ₁` and `g^*ℰ₂`, which is
`Stacks.Chow.powerSumChernElem_tensorObj`; the pullback of a tensor product is the tensor product
of the pullbacks by Stacks 01CD. -/
theorem modulePowerSum_tensorObj (F₁ F₂ : X.Modules) (r s : ℕ)
    (h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F₁ r)
    (h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F₂ s) (p : ℕ) :
    haveI := h₁
    haveI := h₂
    modulePowerSum C sX (Scheme.Modules.tensorObj F₁ F₂) (r * s)
        (isFiniteLocallyFreeOfRank_tensorObj_mul F₁ F₂ r s) p
      = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p,
          (p.choose q.1 : TotalChowClass C sX) *
            (modulePowerSum C sX F₁ r h₁ q.1 * modulePowerSum C sX F₂ s h₂ q.2) := by
  have := h₁
  have := h₂
  have := isFiniteLocallyFreeOfRank_tensorObj_mul F₁ F₂ r s
  refine TotalChowClass.ext_op fun g _ ↦ ?_
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g F₁ r
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g F₂ s
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g
    (Scheme.Modules.tensorObj F₁ F₂) (r * s)
  have := isFiniteLocallyFreeOfRank_tensorObj_mul ((Scheme.Modules.pullback g).obj F₁)
    ((Scheme.Modules.pullback g).obj F₂) r s
  rw [op_modulePowerSum, TotalChowClass.op_sum]
  have hterm : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal p,
      ((p.choose q.1 : TotalChowClass C sX) *
          (modulePowerSum C sX F₁ r h₁ q.1 * modulePowerSum C sX F₂ s h₂ q.2)).op g
        = (p.choose q.1 : GradedCapFamily (chowGroup C (g ≫ sX))) *
            (powerSumChernElem C (g ≫ sX) ((Scheme.Modules.pullback g).obj F₁) r q.1 *
              powerSumChernElem C (g ≫ sX) ((Scheme.Modules.pullback g).obj F₂) s q.2) := by
    intro q _
    rw [TotalChowClass.op_mul, TotalChowClass.op_mul, op_modulePowerSum, op_modulePowerSum]
    congr 1
    exact map_natCast (TotalChowClass.opRingHom g) _
  rw [Finset.sum_congr rfl hterm,
    powerSumChernElem_congr C (g ≫ sX) (pullbackTensorObjIso g F₁ F₂) rfl p]
  exact powerSumChernElem_tensorObj C (g ≫ sX) ((Scheme.Modules.pullback g).obj F₁)
    ((Scheme.Modules.pullback g).obj F₂) r s p

end ConstantRank

/-! ### The common refinement of two rank decompositions -/

section Refinement

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (E₁ E₂ : X.Modules)
  [hE₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E₁]
  [hE₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E₂]

/-- **Two total classes agreeing wherever two modules have constant ranks are equal.** The rank
loci of `ℰ₁` decompose `X` into open and closed subschemes, and inside each of them the preimages
of the rank loci of `ℰ₂` decompose it further; on a member of that common refinement both
pullbacks have constant ranks, and restriction along the two inclusions is restriction along their
composite. This is Stacks 0FDZ in every degree, applied twice. -/
theorem eq_of_res_eq_of_constantModuleRanks {c d : TotalChowClass C sX}
    (H : ∀ (Z : Scheme.{u}) (sZ : Z ⟶ C.S) (_ : LocallyOfFiniteType sZ) (g : Z ⟶ X)
      (_ : LocallyOfFiniteType g) (hs : g ≫ sX = sZ) (r s : ℕ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback g).obj E₁) r →
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback g).obj E₂) s →
      TotalChowClass.res g hs c = TotalChowClass.res g hs d) :
    c = d := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_rankLociFamily E₁) fun r ↦ ?_
  refine TotalChowClass.eq_of_res_eq
    ((isClopenDecomposition_rankLociFamily E₂).preimage (rankLociFamily E₁ r).ι) fun s ↦ ?_
  set U : X.Opens := rankLociFamily E₁ r with hUdef
  set V : (U : Scheme.{u}).Opens := U.ι ⁻¹ᵁ rankLociFamily E₂ s with hVdef
  have ha : ∀ s, U.ι ⁻¹ᵁ rankLociFamily E₂ s ≤ U.ι ⁻¹ᵁ rankLociFamily E₂ (id s) :=
    fun _ ↦ le_rfl
  have hfac : V.ι ≫ U.ι =
      pieceMap U.ι (fun s ↦ U.ι ⁻¹ᵁ rankLociFamily E₂ s) (rankLociFamily E₂) id ha s ≫
        (rankLociFamily E₂ s).ι :=
    (pieceMap_comp_ι U.ι _ _ id ha s).symm
  have := isFiniteLocallyFreeOfRank_pullback_rankLociFamily E₁ r
  have := isFiniteLocallyFreeOfRank_pullback_rankLociFamily E₂ s
  have hcomp : ∀ (E : X.Modules) (n : ℕ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pullback U.ι).obj E)) n →
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (V.ι ≫ U.ι)).obj E) n := fun E n h ↦
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Scheme.Modules.pullbackComp V.ι U.ι).app E) h
  have h₁ := hcomp E₁ _ (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback V.ι
    ((Scheme.Modules.pullback U.ι).obj E₁) r.down)
  have h₂ := hcomp E₂ _ (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (pullbackPullbackIsoOfComp hfac E₂).symm
    (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _
      ((Scheme.Modules.pullback (rankLociFamily E₂ s).ι).obj E₂) s.down))
  rw [TotalChowClass.res_res, TotalChowClass.res_res]
  exact H _ _ inferInstance (V.ι ≫ U.ι) inferInstance (by rw [Category.assoc]) r.down s.down h₁ h₂

end Refinement

/-! ### Stacks 0F9D with no rank assumed -/

section ArbitraryRank

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (E₁ E₂ : X.Modules)
  [hE₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E₁]
  [hE₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E₂]

/-- **Stacks 0F9D, the source's more precise identity, in the bivariant ring.** Let `(S, δ)` be
the situation of Stacks 02QL, let `X` be locally of finite type over `S` and let `ℰ₁` and `ℰ₂` be
finite locally free `𝒪_X`-modules, of no assumed rank. Then for every `p ≥ 0`

  `P_p(ℰ₁ ⊗_{𝒪_X} ℰ₂) = ∑_{p₁ + p₂ = p} C(p, p₁) P_{p₁}(ℰ₁) P_{p₂}(ℰ₂)`

in `∏_{q ≥ 0} A^q(X)`, the bivariant ring of `X`, whose multiplication is the composition of
bivariant classes of Stacks 0B75. In degree zero the identity reads `rk(ℰ₁ ⊗ ℰ₂) = rk(ℰ₁) rk(ℰ₂)`
and in degree one `c₁(ℰ₁ ⊗ ℰ₂) = rk(ℰ₂) c₁(ℰ₁) + rk(ℰ₁) c₁(ℰ₂)`, both as locally constant
functions on `X`. -/
@[stacks 0F9D "the source's more precise identity P_p(E_1 tensor E_2) = sum over p_1 + p_2 = p \
of binom(p, p_1) P_{p_1}(E_1) P_{p_2}(E_2), with hypotheses EXACTLY the source's: Situation 02QL \
as the ChowSituation C, X locally of finite type over its base, and E_1, E_2 finite locally free \
O_X-modules -- NO rank is assumed, the predicate being \
AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree and not ...OfRank.  The identity is read \
IN THE BIVARIANT RING: Stacks.Chow.TotalChowClass is the product over q >= 0 of the Chow \
cohomology groups A^q(X) of Stacks 0B7E, whose multiplication is the Cauchy product of the \
composites of bivariant classes of Stacks 0B75 and whose unit is the identity class of Stacks \
0FBS, so each product P_{p_1}(E_1) P_{p_2}(E_2) is a composition of bivariant classes and not a \
composite of cap operators; Stacks.Chow.modulePowerSumComponentArbitraryRank_tensorObj reads the \
same identity in the single group A^p(X).  P_p(F) is \
Stacks.Chow.modulePowerSumArbitraryRank, Newton's recursion of Stacks 0F9B \
(AlgebraicGeometry.newtonPowerSum, which is the universal power-sum polynomial of that tag by \
AlgebraicGeometry.newtonPowerSum_eq_powerSumOfChernClasses) applied to the bivariant Chern \
classes c_i(F) of Stacks 0B7H, Stacks.Chow.GenuineChern.chernClass, assembled over the rank loci \
of F by Stacks 0FDZ.  THE RANK DECOMPOSITION IS PERFORMED, not assumed: the rank of a finite \
locally free module is locally constant (Stacks.Chow.moduleRank), its loci are open and closed \
and cover X (Stacks.Chow.isClopenDecomposition_rankLociFamily), the identity for two modules is \
read on the common refinement of their two decompositions \
(Stacks.Chow.eq_of_res_eq_of_constantModuleRanks), on a member of which E_1 tensor E_2 has \
constant rank r * s by Stacks 02U9, and restriction of total classes is a ring homomorphism.  The \
constant-rank case is Stacks.Chow.modulePowerSum_tensorObj, obtained from \
Stacks.Chow.powerSumChernElem_tensorObj -- where the splitting principle of Stacks 02UL is \
performed -- read on EVERY test scheme g : T -> X for the pullbacks g^*E_1, g^*E_2 at once, \
which is what Stacks 0B76 needs for a bivariant class.  The division by p! is omitted only \
because it is a scalar; Stacks.Chow.totalChernCharacterArbitraryRank_tensorObj performs \
it"]
theorem modulePowerSumArbitraryRank_tensorObj (p : ℕ) :
    modulePowerSumArbitraryRank C sX (Scheme.Modules.tensorObj E₁ E₂) p
      = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p,
          (p.choose q.1 : TotalChowClass C sX) *
            (modulePowerSumArbitraryRank C sX E₁ q.1 *
              modulePowerSumArbitraryRank C sX E₂ q.2) := by
  refine eq_of_res_eq_of_constantModuleRanks C sX E₁ E₂ fun Z sZ _ g _ hs r s h₁ h₂ ↦ ?_
  have := h₁
  have := h₂
  have hT : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj (Scheme.Modules.tensorObj E₁ E₂)) (r * s) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (pullbackTensorObjIso g E₁ E₂).symm
      (isFiniteLocallyFreeOfRank_tensorObj_mul _ _ r s)
  rw [res_modulePowerSumArbitraryRank_of_constantRank C sX _ g hs (r * s) hT p, map_sum]
  have hterm : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal p,
      TotalChowClass.res g hs ((p.choose q.1 : TotalChowClass C sX) *
          (modulePowerSumArbitraryRank C sX E₁ q.1 * modulePowerSumArbitraryRank C sX E₂ q.2))
        = (p.choose q.1 : TotalChowClass C sZ) *
            (modulePowerSum C sZ ((Scheme.Modules.pullback g).obj E₁) r h₁ q.1 *
              modulePowerSum C sZ ((Scheme.Modules.pullback g).obj E₂) s h₂ q.2) := by
    intro q _
    rw [map_mul, map_mul, map_natCast,
      res_modulePowerSumArbitraryRank_of_constantRank C sX E₁ g hs r h₁ q.1,
      res_modulePowerSumArbitraryRank_of_constantRank C sX E₂ g hs s h₂ q.2]
  rw [Finset.sum_congr rfl hterm,
    modulePowerSum_congr C sZ (isFiniteLocallyFreeOfRank_tensorObj_mul _ _ r s) hT
      (pullbackTensorObjIso g E₁ E₂) rfl p]
  exact modulePowerSum_tensorObj C sZ ((Scheme.Modules.pullback g).obj E₁)
    ((Scheme.Modules.pullback g).obj E₂) r s h₁ h₂ p

/-- **Stacks 0F9D, the source's more precise identity, read in `A^p(X)`.** An equality of two
elements of the Chow cohomology group `A^p(X)` of Stacks 0B7E: the class `P_p(ℰ₁ ⊗ ℰ₂)` is the
sum over `p₁ + p₂ = p` of the classes `C(p, p₁) P_{p₁}(ℰ₁) P_{p₂}(ℰ₂)` of `A^p(X)`, each formed
by the composition of bivariant classes of Stacks 0B75 inside the bivariant ring and read in
degree `p`. This is `Stacks.Chow.modulePowerSumArbitraryRank_tensorObj` in degree `p`, the
components of a finite sum of total classes being the sum of their components. -/
@[stacks 0F9D "the same identity P_p(E_1 tensor E_2) = sum over p_1 + p_2 = p of \
binom(p, p_1) P_{p_1}(E_1) P_{p_2}(E_2) read as an equality of two elements of the SINGLE GROUP \
A^p(X) = Stacks.Chow.chowCohomologyComponent of Stacks 0B7E at the Gysin system \
Stacks.Chow.gysinSystemOfInvertible of the genuine first Chern class, which is where the source \
states it.  Hypotheses EXACTLY the source's: Situation 02QL as C, X locally of finite type over \
its base, E_1 and E_2 finite locally free with NO rank assumed.  Each product on the right is \
formed in the bivariant ring Stacks.Chow.TotalChowClass, i.e. is a Cauchy product of the \
compositions of bivariant classes of Stacks 0B75, read in degree p, so the right-hand side is a \
sum over the antidiagonal of p of elements of A^p(X), which is the shape the source displays; \
the degree-p component of Stacks.Chow.modulePowerSumArbitraryRank is \
Stacks.Chow.modulePowerSumComponentArbitraryRank by definition.  See \
Stacks.Chow.modulePowerSumArbitraryRank_tensorObj for the same identity in every degree at once \
and for how the rank decomposition and the splitting principle are performed"]
theorem modulePowerSumComponentArbitraryRank_tensorObj (p : ℕ) :
    modulePowerSumComponentArbitraryRank C sX (Scheme.Modules.tensorObj E₁ E₂) p
      = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p,
          ((p.choose q.1 : TotalChowClass C sX) *
            (modulePowerSumArbitraryRank C sX E₁ q.1 *
              modulePowerSumArbitraryRank C sX E₂ q.2)) p := by
  rw [modulePowerSumComponentArbitraryRank_eq,
    modulePowerSumArbitraryRank_tensorObj C sX E₁ E₂ p, TotalChowClass.sum_apply]

end ArbitraryRank

end Stacks.Chow

end
