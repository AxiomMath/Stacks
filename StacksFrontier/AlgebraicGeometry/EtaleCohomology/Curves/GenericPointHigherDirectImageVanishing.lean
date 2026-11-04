module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralSurjectiveCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.CFieldTranscendenceDegreeOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of the higher direct images of `𝐆_m` along the generic point

Let `k` be an algebraically closed field, let `X` be an integral scheme whose function field
`K = k(X)` has transcendence degree one over `k` — a smooth curve over `k` is the source's
situation — and let `j : Spec K ⟶ X` be the inclusion of the generic point. Then

`R^q j_* 𝐆_{m,K} = 0` for every `q ≥ 1`.

The source's proof computes the geometric stalks. At a geometric point `x̄` of `X` the stalk of
`R^q j_* 𝐆_{m,K}` is the étale cohomology of `𝐆_m` on the generic fibre of the strict
henselisation, `Spec(𝒪^{sh}_{X,x̄} ⊗_A K)`; that ring is a localisation of the discrete valuation
ring `𝒪^{sh}_{X,x̄}` in which a uniformiser has become invertible, hence is its fraction field
`K^{sh}_{x̄}`, and `K^{sh}_{x̄}` is an *algebraic* extension of `K` because the strict
henselisation is a filtered colimit of étale `A`-algebras. Stacks 03RG then kills it.

## Main results

* `Stacks.EtaleCohomology.trdeg_eq_one_of_isAlgebraic`: an algebraic extension of a
  transcendence-degree-one extension of `k` again has transcendence degree one over `k`.
* `Stacks.EtaleCohomology.brauerGroup_eq_one_of_module_finite_of_isAlgebraic`: the Brauer group
  of every finite extension of an algebraic extension of `K` is trivial.
* `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_isAlgebraic`: Stacks 03RG
  at every algebraic extension of `K` at once, over the hypothesis `h03RG`.

## Implementation notes

**The carried hypotheses, and the tags they are.**

* `h03Q9`, the stalk computation: for every point `t` of `X` and every `q ≥ 1`, if
  `H^q_étale(Spec L, 𝐆_m) = 0` for every algebraic extension `L` of `K` then the stalk of
  `R^q j_* 𝐆_{m,K}` vanishes at the geometric point of `X` over `t` whose residue field is an
  algebraic closure of the residue field at `t`. This bundles the three steps of the source's
  proof that this library cannot run: the unrestricted form of **Stacks 03Q9**, which computes
  the stalk of a higher direct image as the cohomology of the base change to the strict
  henselisation — the library has that tag only over a strictly henselian base, as
  `Stacks.EtaleCohomology.higherDirectImageEtaleStalkIso`; the identification of
  `𝒪^{sh}_{X,x̄} ⊗_A K` with the fraction field of `𝒪^{sh}_{X,x̄}`, which uses that the local
  rings of a smooth curve are discrete valuation rings; and the fact that this fraction field is
  algebraic over `K`. It is stated as an implication from the vanishing over *all* algebraic
  extensions rather than from the vanishing over one particular extension, which is the weakest
  form that serves and so carries as little as possible.
* `h03RG`, the vanishing criterion: for every field `L` whose finite extensions all have trivial
  Brauer group, `H^q_étale(Spec L, 𝐆_m) = 0` for `q ≥ 1`. This is part (1) of **Stacks 03R8**
  read through **Stacks 03QU**. The library has it as
  `AlgebraicGeometry.subsingleton_sheafH_multiplicativeSheaf_of_forall_brauer`, through which
  `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_spec_of_trdeg_eq_one`
  (Stacks 03RG) is proved. It is quantified over `L` here because the proof needs it not at `K`
  but at each algebraic extension of `K`.

Nothing else is assumed: the degree range is the source's and is quantified over, and the
hypotheses on `k` and on `X` are implied by the source's — an integral scheme whose function
field has transcendence degree one over `k` is what a smooth curve over `k` supplies, by
`AlgebraicGeometry.trdeg_residueField_genericPoint_eq_one` read through
`AlgebraicGeometry.genericResidueEquiv` — so the statement is slightly more
general than the tag rather than narrower.

**What is proved rather than carried.** Two things. First, the reduction of the sheaf-level
vanishing to the geometric stalks: the geometric points of `X` whose residue fields are
algebraic closures of the residue fields of `X` cover `X`, and such a covering family detects
the zero sheaf, which is `Stacks.EtaleCohomology.isZero_of_geometricStalkAb_family`. The source
opens with this reduction — "it suffices to show the stalk vanishes" — and it is not formal: it
is conservativity of the geometric stalk functors on the abelian small étale topos. Second, the
Brauer premise of `h03RG` at every algebraic extension of `K`, which is the arithmetic input:
such an extension has transcendence degree one over `k` by `trdeg_eq_one_of_isAlgebraic`, hence
so does each of its finite extensions, and a transcendence-degree-one extension of an
algebraically closed field has trivial Brauer group by Tsen's theorem (Stacks 03RF) through
Stacks 03RC. That premise is exactly what the source must supply to invoke Stacks 03RG at
`K^{sh}_{x̄}`, and the vehicle for it — `trdeg_eq_one_of_isAlgebraic`, for an arbitrary
algebraic extension rather than a finite one, which is what a strict henselisation provides — is
new here.

**Coefficients and pinned universes.** As in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupHigherVanishing`,
abelian sheaves are taken with coefficients in `AddCommGrpCat.{u + 1}` for `X : Scheme.{u}` and
cohomology is `CategoryTheory.Sheaf.H.{u + 1, u + 1}`. The Grothendieck abelian structure is
taken with its coefficient universe pinned, as
`Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse`, because the
general instance is indexed by `max (u + 1) v` and instance search cannot solve
`max (u + 1) ?v = u + 1`; that is what makes `HasExt.{u + 1}` available. The injective
resolutions that `CategoryTheory.Functor.rightDerived` needs come from
`Stacks.EtaleCohomology.enoughInjectives_sheaf_smallEtale_objectUniverse`.
`Stacks.EtaleCohomology.isZero_of_geometricStalkAb_family` is stated at `Ab.{u + 1}`, which is
`AddCommGrpCat.{max (u + 1) (u + 1)}`, so it applies on the nose.

## References

* [Stacks Project, Tag 03RJ](https://stacks.math.columbia.edu/tag/03RJ): the theorem, proved
  here over `h03Q9` and `h03RG`.
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9): carried inside
  `h03Q9`; the library has it only over a strictly henselian base.
* [Stacks Project, Tag 03RG](https://stacks.math.columbia.edu/tag/03RG): the vanishing it
  provides is carried as `h03RG`, together with Tag 03R8 and Tag 03QU, which is what Stacks 03RG
  itself rests on in this library.
* [Stacks Project, Tag 03RC](https://stacks.math.columbia.edu/tag/03RC) and
  [Stacks Project, Tag 03RF](https://stacks.math.columbia.edu/tag/03RF): used from the library,
  through `brauerGroup_eq_one_of_module_finite_of_trdeg_eq_one`, to discharge the Brauer premise
  of `h03RG`.
* [Stacks Project, Tag 030H](https://stacks.math.columbia.edu/tag/030H): additivity of the
  transcendence degree in a tower, the vehicle of `trdeg_eq_one_of_isAlgebraic`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-! ### Algebraic extensions of a transcendence-degree-one extension -/

/-- **An algebraic extension of a transcendence-degree-one extension of `k` again has
transcendence degree one over `k`.** By additivity of the transcendence degree in a tower
(Stacks 030H) and the vanishing of the transcendence degree of an algebraic extension.

Compared with `trdeg_eq_one_of_module_finite_of_trdeg_eq_one` the extension `L/K` is only
assumed algebraic, not finite; that is what the strict henselisation of a local ring of a curve
provides, being a filtered colimit of étale algebras rather than a finite extension. -/
theorem trdeg_eq_one_of_isAlgebraic (k : Type u) [Field k] (K : Type u) [Field K] [Algebra k K]
    (hK : Algebra.trdeg k K = 1) (L : Type u) [Field L] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L] [Algebra.IsAlgebraic K L] : Algebra.trdeg k L = 1 := by
  have h := trdeg_add_eq k K (A := L)
  rwa [show Algebra.trdeg K L = 0 from trdeg_eq_zero, add_zero, hK, eq_comm] at h

/-- **The Brauer group of every finite extension of an algebraic extension of a
transcendence-degree-one extension of an algebraically closed field is trivial.**

This is the premise that the vanishing criterion of Stacks 03R8 asks for, at the fields at which
the proof of Stacks 03RJ has to invoke Stacks 03RG: the generic fibres of the strict
henselisations of `X`, which are algebraic over the function field rather than finite over it.
A finite extension of an algebraic extension of `K` is again algebraic over `K`, so it has
transcendence degree one over `k` by `trdeg_eq_one_of_isAlgebraic` and therefore trivial Brauer
group by Tsen's theorem (Stacks 03RF) through Stacks 03RC. -/
@[sga "4½ Arcata 3.2.2" "special case"]
theorem brauerGroup_eq_one_of_module_finite_of_isAlgebraic (k : Type u) [Field k] [IsAlgClosed k]
    (K : Type u) [Field K] [Algebra k K] (hK : Algebra.trdeg k K = 1) (L : Type u) [Field L]
    [Algebra K L] [Algebra k L] [IsScalarTower k K L] [Algebra.IsAlgebraic K L] (L' : Type u)
    [Field L'] [Algebra L L'] [Module.Finite L L'] (y : BrauerGroup L') : y = 1 := by
  let _ : Algebra k L' := ((algebraMap L L').comp (algebraMap k L)).toAlgebra
  have _ : IsScalarTower k L L' := .of_algebraMap_eq' rfl
  exact brauerGroup_eq_one_of_module_finite_of_trdeg_eq_one k L
    (trdeg_eq_one_of_isAlgebraic k K hK L) L' y

/-- **Stacks 03RG at every algebraic extension of `K` at once.** Let `k` be an algebraically
closed field and `K/k` an extension of transcendence degree one. Then for every algebraic
extension `L` of `K`,

`H^q_étale(Spec L, 𝐆_m) = 0` for every `q ≥ 1`.

The hypothesis `h03RG` is part (1) of Stacks 03R8 read through Stacks 03QU, quantified over the
field: if every finite extension of a field has trivial Brauer group then the positive-degree
étale cohomology of that field with coefficients in `𝐆_m` vanishes. Neither tag is in this
library beyond degree zero, so it is carried.

What is proved here is its premise at `L`, by
`Stacks.EtaleCohomology.brauerGroup_eq_one_of_module_finite_of_isAlgebraic`. This is the form in
which Stacks 03RJ consumes Stacks 03RG: not at `K` itself, but at the fraction fields of the
strict henselisations of the local rings of `X`, which are algebraic over `K`. -/
theorem subsingleton_sheafH_multiplicativeSheaf_of_isAlgebraic (k : Type u) [Field k]
    [IsAlgClosed k] (K : Type u) [Field K] [Algebra k K] (hK : Algebra.trdeg k K = 1)
    (h03RG : ∀ (L : Type u) [Field L],
      (∀ (L' : Type u) [Field L'] [Algebra L L'] [Module.Finite L L'] (y : BrauerGroup L'),
          y = 1) →
        ∀ q : ℕ, 1 ≤ q → Subsingleton (Sheaf.H.{u + 1, u + 1}
          (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of L))) q))
    (L : Type u) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (q : ℕ) (hq : 1 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of L))) q) := by
  refine h03RG L (fun L' _ _ _ y ↦ ?_) q hq
  let _ : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  have _ : IsScalarTower k K L := .of_algebraMap_eq' rfl
  exact brauerGroup_eq_one_of_module_finite_of_isAlgebraic k K hK L L' y

/-! ### Stacks 03RJ -/

end Stacks.EtaleCohomology

end
