module

public import StacksFrontier.AlgebraicGeometry.Curves.SheafDerivationDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DerivationGluing

/-!
# Gluing vector fields along an open cover

Let `Y` be a scheme over a field `k`. A family of `k`-derivations of `𝒪_Y`, each defined on the
opens contained in one member of an open cover of `Y` and agreeing on the opens contained in two
members of the cover, glues to a unique vector field on `Y` in the sense of Section 53.26.

This is the scheme-level reading of
`AlgebraicGeometry.SheafOfModules.existsUnique_sheafDerivation_of_cover`, which glues relative
derivations on a ringed space by reading them as differential operators of order at most one;
`Stacks.Curves.SheafDerivationOf` is such a relative derivation on the ringed space underlying
`Y`, by definition.

## Main results

* `Stacks.Curves.sheafDerivationOf_eq` — a vector field on a `k`-scheme is a relative derivation
  of the ringed space underlying it.
* `Stacks.Curves.existsUnique_sheafDerivationOf_of_cover` — **a compatible family of
  `k`-derivations on the members of an open cover glues to a unique vector field.**

## Implementation notes

The hypotheses are stated for the data the gluing of differential operators consumes: a
`DiffOp.RawOp` over each member of the cover, that is an additive map on `Γ(Y, W)` for every open
`W` contained in that member, compatible with restriction inside it. The Leibniz rule and the
vanishing are then conditions on each of those maps; the vanishing is written through
`DiffOp.sectionRingHom` of the structural map `g⁻¹ 𝒪_{Spec k} ⟶ 𝒪_Y`, which is the form in which
the order condition and the `d_app` field of a derivation both speak about the base.

## What is not done here

This file does not itself prove the sheaf-level left-to-right direction of Tag 0E68, which is
`Stacks.Curves.existsUnique_extend_normalization_of_hasAtWorstNodalSingularities`. That
direction needs, on a cover of the normalization `X^ν`, derivations of `Γ(X^ν, V)` extending a
given vector field on `X`, and the ring-theoretic extension supplying them is
`Stacks.Curves.exists_leibniz_extension_normalizationSections`: a `k`-derivation of `Γ(X, U)`
does extend to the integral closure of `Γ(X, U)` in its total ring of fractions, for `U` an
affine open. The semilocal statement
`Stacks.Curves.existsUnique_extend_integralClosure_of_isNodalAlgebra` is available only at a
local ring, and the step over an affine open is got from it not by removing its locality but by
the local-to-global principle
`Stacks.DerivationExtension.existsUnique_extend_integralClosure_of_forall_maximal`, whose input
is one such local extension at each maximal ideal.

The rest of this section records a different route to that extension, which the development did
not need: `Stacks.DerivationExtension.existsUnique_extend_integralClosure_of_adjoin` asks for
the integral closure to be generated as a `Γ(X, U)`-algebra by elements satisfying a polynomial
relation whose formal derivative at the element is invertible in the closure, so on that route
what was missing was not the extension but those generators.

The invertibility must not be asked for of the quadratic relation. At a node the integral closure
is `A + A t` with `t ^ 2 = a + c t`, the degree-two relation has derivative `u = 2 t - c`, and
`u ^ 2 = 4 a + c ^ 2` lies in the image of `A`
(`Stacks.DerivationExtension.sq_two_mul_sub_algebraMap`): so `u` is a unit of the closure exactly
when an element of `A` vanishes nowhere on the normalization of the whole of `Spec A`, which on
an affine curve it does not — on the nodal cubic `y ^ 2 = x ^ 3 + x ^ 2` the element `u` vanishes
at a *smooth* point, and rescaling `t` only rescales `u`. What is true, and is what the local
proof's `u ^ 2` having nonzero residue amounts to globally, is that `u` is comaximal in the
closure with a conductor element: an `α : Γ(X, U)` with `α t` again a section over `U`, whose
degree-one relation `α X - α t` has derivative `α`
(`Stacks.DerivationExtension.exists_relation_aeval_derivative_eq_algebraMap`). Since the relations
of `t` are closed under `Γ(X, U)[t]`-linear combination
(`Stacks.DerivationExtension.exists_relation_aeval_derivative_add_of_mem_adjoin`), comaximality is
all the hypothesis of the extension needs, and comaximality is a condition at the maximal ideals:
`Stacks.DerivationExtension.existsUnique_extend_integralClosure_apply_eq_zero_of_forall_isMaximal`.
The `Fixes` conditions come from the same conductor element and are no longer separate.

What is left is the geometry: a single `t` generating the integral closure of `Γ(X, U)` over
`Γ(X, U)`, a conductor element comaximal with its `u`, and the two residues at a node with
`ε₁ t - ε₂ t = 1`.

Two of those three are no longer missing as ring theory. Writing `A = Γ(X, U)`, `A'` for the
integral closure and `R` for the image of `A` in it:

* The single generator is a statement about the *module* `A' / R` and nothing else: `A' = A + A t`
  forces `t ^ 2 ∈ A + A t`, so the quadratic relation is free
  (`Stacks.DerivationExtension.exists_quadratic_of_sup_span_eq_top`) and
  `Algebra.adjoin A {t} = A'` follows
  (`Stacks.DerivationExtension.adjoin_eq_integralClosure_of_sup_span_eq_top`). That module is
  cyclic as soon as finitely many pairwise comaximal ideals `Iᵢ` have `(∏ Iᵢ) A' ⊆ A` and each
  `R + Iᵢ A'` is a coatom —
  `Stacks.DerivationExtension.exists_adjoin_eq_integralClosure_of_isCoatom`, whose engine is
  `Stacks.CyclicComaximal.exists_sup_span_singleton_eq_top`. This is *not* "locally cyclic implies
  cyclic", which is false; it is the Chinese remainder theorem, and it needs the support to be
  finitely many comaximal points.
* The conductor element comaximal with `u` is prime avoidance:
  `Stacks.DerivationExtension.exists_mem_mul_add_mul_eq_one_of_finite` produces it from the
  finiteness of the set of maximal ideals of `A'` containing `u` together with the fact that none
  of them contracts to an ideal containing the conductor.
  `Stacks.DerivationExtension.existsUnique_extend_integralClosure_apply_eq_zero_of_conductor`
  packages that with the extension.

So what the geometry would still owe that route, for `U` an affine open meeting the nodes
`x₁, …, xₙ`, is only:
`(∏ 𝔪ᵢ) A' ⊆ A`; that each `A' / (A + 𝔪ᵢ A')` is a simple `A`-module, which is the global form of
`Ring.deltaInvariant 𝒪_{X, xᵢ} = 1`; that `V(u)` is finite in `A'` and misses the nodes; and the
two residues.

Those two module conditions now hold *after localizing at a node*. The identification they need
is `Stacks.Curves.nonempty_algEquiv_localization_integralClosure_fractionRing`: the localization
of `A'` at the complement of a prime is the integral closure of `A_𝔪` in the total ring of
fractions of `A_𝔪`, as an `A_𝔪`-algebra. Transporting the two node-local computations through it
gives `Stacks.Curves.isCoatom_range_algebraMap_localization_integralClosure_of_isNodalAlgebra`
(the image of `A_𝔪` in `A' ⊗_A A_𝔪` is a coatom) and
`Stacks.Curves.map_maximalIdeal_le_range_algebraMap_localization_integralClosure`
(`𝔪 (A' ⊗_A A_𝔪) ⊆ A_𝔪`), both stated at one node, which is the granularity the caveat below
forces anyway.

What is not done is the descent of those two from the localizations back to `A`. It needs the
localization of `LinearMap.range (Algebra.linearMap A A')` at `𝔪.primeCompl` to be the range of
`Algebra.linearMap A_𝔪 (A' ⊗_A A_𝔪)`, so that the `A`-module `A' / A` — finite over `A` by
`module_finite_integralClosure_fractionRing` — has the computed localizations at the nodes; and,
for `(∏ 𝔪ᵢ) A' ⊆ A`, that `A' / A` vanishes away from the nodes. The finiteness of the node locus
is `AlgebraicGeometry.finite_singularLocus_inter_of_isAffineOpen`.

The vanishing away from the nodes is
`Stacks.Curves.range_algebraMap_localization_integralClosure_eq_top_of_isRegularLocalRing`: at a
prime whose local ring is regular the image of `A_𝔭` in `A' ⊗_A A_𝔭` is all of it, the `= ⊤`
counterpart of the coatom above, at the same submodule. Its mechanism is that a regular local
ring is integrally closed, `isIntegrallyClosed_of_isRegularLocalRing`, which carries no
hypothesis on the dimension — it is Stacks 0567 rather than the dimension-one structure theory —
so neither does the vanishing. The dimension of `A` is needed only for the finiteness of the
node locus, and for every singular point of `U` to be a node.

One structural caveat on the third ingredient, the residues. The conductor condition that
`Stacks.DerivationExtension.apply_eq_zero_of_mul_eq` asks of `ε₁` is that every `b : A` with
`ε₁ b = 0` carries `t` back into `A`, that is `𝔪₁ ⊆ {α : α A' ⊆ A}` for the maximal ideal
`𝔪₁ = ker (ε₁ ∘ algebraMap A A')`. When `A' = A + A t` that conductor is the annihilator of
`A' / A`, hence the intersection of the maximal ideals of the nodes, so the condition forces `U`
to meet exactly one node. The residues are therefore to be supplied on a cover refined so that
each member contains at most one node — on which `ε₁ t - ε₂ t` can moreover be normalised to `1`
by rescaling `t` by a scalar of `k`, since a scalar multiple of a generator is a generator.

The step from such a ring extension to the data this gluing consumes is no longer missing:
`Stacks.AlgebraicGeometry.DifferentialsAffine.exists_rawOp_of_leibniz` turns a `k`-derivation of
the coordinate ring of an affine open into an operator over that open, and
`Stacks.Curves.existsUnique_sheafDerivationOf_of_affineCover` glues such operators into a vector
field while asking for the vanishing on the base only over `Γ(Spec k, ⊤)`.

## References

* [Stacks Project, Tag 0E66](https://stacks.math.columbia.edu/tag/0E66)
* [Stacks Project, Tag 09CR](https://stacks.math.columbia.edu/tag/09CR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))

/-- A vector field on a `k`-scheme is a relative derivation of the ringed space underlying it.
Definitional; recorded because the gluing of relative derivations is stated for a ringed space
and `Stacks.Curves.SheafDerivationOf` for a scheme. -/
theorem sheafDerivationOf_eq :
    SheafDerivationOf g =
      AlgebraicGeometry.SheafOfModules.SheafDerivation
        (X := Y.toLocallyRingedSpace.toSheafedSpace) (inverseImageStructureMap g)
        (SheafOfModules.unit (SheafOfModules.underlyingRingSheaf Y.sheaf)) :=
  rfl

/-- **Gluing vector fields along an open cover.** A family of `k`-derivations of `𝒪_Y`, each
defined on the opens contained in one member of an open cover of `Y` and agreeing on the opens
contained in two members, glues to a unique vector field on `Y`.

This is the construction of a vector field from local data: the glued operator has order at most
one because the order is local on the base, and an operator of order at most one which obeys the
Leibniz rule and annihilates the scalars from `g⁻¹ 𝒪_{Spec k}` is a derivation. -/
theorem existsUnique_sheafDerivationOf_of_cover {ι : Type*} (U : ι → Y.Opens)
    (hU : ⨆ i, U i = ⊤)
    (d : ∀ i, DiffOp.RawOp (SheafOfModules.unit Y.ringCatSheaf)
      (SheafOfModules.unit Y.ringCatSheaf) (U i))
    (hnat : ∀ i, (d i).IsNatural)
    (hleib : ∀ (i : ι) (W : Over (U i)) (a b : Y.ringCatSheaf.obj.obj (op W.left)),
      (d i).unitOp W (a * b) = a * (d i).unitOp W b + b * (d i).unitOp W a)
    (hker : ∀ (i : ι) (W : Over (U i))
      (a : (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat g.base).obj (Spec (.of k)).sheaf)).obj.obj
          (op W.left)),
      (d i).unitOp W (DiffOp.sectionRingHom
        (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap g)) (op W.left) a) = 0)
    (hagree : DiffOp.AgreeOnCover U d) :
    ∃! D : SheafDerivationOf g,
      ∀ i, (SheafOfModules.globalOpOfSheafDerivation (inverseImageStructureMap g) D).restrict
        (U i) = d i :=
  SheafOfModules.existsUnique_sheafDerivation_of_cover (inverseImageStructureMap g) U
    (fun p => Opens.mem_iSup.1 (hU ▸ Opens.mem_top p)) d hnat hleib hker hagree

end Stacks.Curves

end
