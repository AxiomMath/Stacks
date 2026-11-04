module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.SieveToFamily
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.Over
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-compact objects of a big fppf site

A quasi-compact scheme is a quasi-compact object of a big fppf site, in the sense of
Stacks 090H: every covering of it is refined by one factoring through finitely many of its
members.

The argument is the one the source gives. A covering sieve of `X` contains a chosen covering
family `E` (`AlgebraicGeometry.BigFppfSite.exists_isCovering_sieve₀_le`), whose members are
flat and locally of finite presentation, hence open maps, and jointly surjective
(`AlgebraicGeometry.BigFppfSite.fppfCovering`). Their images therefore form an open cover of
`X`, so finitely many of them already cover it: the resulting *finite* subfamily is again an
fppf covering. It need not satisfy the site's cardinality bound as it stands, but
`AlgebraicGeometry.BigFppfSite.fppf_has_representative` replaces it by a chosen covering family
with the same set of arrows, and arrows of the subfamily are arrows of `E`, hence lie in the
sieve we started from and factor through finitely many of its members.

The same statement for the big fppf site of a scheme `S` is the localized case, which is
`CategoryTheory.GrothendieckTopology.isQuasiCompactObject_over` applied to the above.

## Main results

* `AlgebraicGeometry.BigFppfSite.isQuasiCompactObject_of_compactSpace`: a quasi-compact scheme
  is a quasi-compact object of a big fppf site.
* `AlgebraicGeometry.BigFppfOver.isQuasiCompactObject_of_compactSpace`: an object of the big
  fppf site of `S` with quasi-compact underlying scheme is a quasi-compact object of that site.
* `AlgebraicGeometry.BigFppfOver.isQuasiCompactObject_top`: the terminal object `S ⟶ S` of the
  big fppf site of a quasi-compact `S` is a quasi-compact object. This is the case the sections
  functor of Stacks 0935 is evaluated at.

## Implementation notes

Replacing the finite subfamily by a chosen covering family is the only place where the
cardinality bound `AlgebraicGeometry.BigFppfSite.coveringBound` intervenes, and nothing weaker
is available: the bound is an arbitrary cardinal, so a finite family is not automatically below
it, while the site axioms produce new families only with the index type of an old one. The
representative's index type is in turn uncontrolled, which is harmless because combinatorial
equivalence identifies its *arrows* with those of the finite subfamily, and it is the arrows
that carry the factorization through `𝒰`.

No affine opens are needed. Openness of a flat morphism locally of finite presentation applies
to the members of `E` themselves, so the finite subcover can be extracted from their images
directly rather than from images of affine opens of their sources, as in
`AlgebraicGeometry.FppfCovering.exists_finite_affineOpens_cover`.

## References

* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w vC uC u

/-- Transport a covering family across the equality of targets contained in a combinatorial
equivalence of coverings. The transported family satisfies whatever property the original one
did, and each of its members factors through a member of the family it is equivalent to.

The equality of targets is a hypothesis of this lemma rather than a component of a hypothesis,
so that it can be substituted; destructuring
`CategoryTheory.Covering.CombEquiv` in place leaves the equality inside a transport that
`subst` cannot reach. -/
private lemma exists_combEquiv_factor {C : Type uC} [CategoryTheory.Category.{vC} C]
    {P : Covering.{uC, vC, w} C → Prop} {U V : C} (hUV : U = V)
    {E : PreZeroHypercover.{w} U} {F : PreZeroHypercover.{w} V} (hP : P ⟨V, F⟩)
    (h : (hUV ▸ E).CombinatoriallyEquivalent F) :
    ∃ G : PreZeroHypercover.{w} U, P ⟨U, G⟩ ∧
      ∃ (β : G.I₀ → E.I₀) (hX : ∀ j, G.X j = E.X (β j)),
        ∀ j, G.f j = eqToHom (hX j) ≫ E.f (β j) := by
  subst hUV
  exact ⟨F, hP, h.2⟩

namespace AlgebraicGeometry

/-- **A quasi-compact scheme is a quasi-compact object of a big fppf site** (Stacks 090H).

Every covering sieve of `X` contains a chosen covering family; the members of that family are
open maps and jointly surjective, so finitely many of their images already cover the
quasi-compact `X`, and the finite subfamily they form refines the given covering through
finitely many of its members. -/
public theorem BigFppfSite.isQuasiCompactObject_of_compactSpace (B : BigFppfSite.{u})
    (X : B.Schemes) (hX : CompactSpace (B.inclusion.obj X)) :
    B.topology.IsQuasiCompactObject X := by
  classical
  intro 𝒰 h𝒰
  obtain ⟨E, hE, hle⟩ := B.exists_isCovering_sieve₀_le h𝒰
  have hjfl := B.jointlySurjective_and_flat_and_lfp_of_isCovering hE
  obtain ⟨T, hT⟩ := (@isCompact_univ _ _ hX).elim_finite_subcover
    (fun i : E.I₀ => Set.range (B.inclusion.map (E.f i)))
    (fun i => ((B.fppfCovering hE).isOpenMap i).isOpen_range)
    (fun x _ => Set.mem_iUnion.mpr (hjfl.1 x))
  have hfppf : IsFppfCovering (κ := B.cutoff) ⟨X, E.restrictIndex ((↑) : T → E.I₀)⟩ := by
    rw [IsFppfCovering, Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map,
      show Scheme.fppfPrecoverage =
        Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation) from rfl,
      Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun (i : ↥T) => hjfl.2 i.1⟩
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ x))
    exact ⟨⟨i, hi⟩, hx⟩
  obtain ⟨F, hF, hXX, hcomb⟩ := B.fppf_has_representative _ hfppf
  obtain ⟨E', hF, β, hβX, hβf⟩ :=
    exists_combEquiv_factor (U := X) (V := F.1)
      (E := E.restrictIndex ((↑) : T → E.I₀)) (F := F.2)
      (P := fun G => CovBounded (IsFppfCovering (κ := B.cutoff)) B.coveringBound G)
      hXX hF hcomb
  choose s α hα using fun c : ↥T =>
    (Sieve.mem_ofArrows_iff _ _ _).1 (hle _ (E.sieve₀_f ↑c))
  refine ⟨E', { s₀ := fun j => s (β j)
                h₀ := fun j => eqToHom (hβX j) ≫ α (β j)
                w₀ := fun j => ?_ }, ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans ((congrArg _ (hα (β j)).symm).trans (hβf j).symm)
  · exact Precoverage.generate_mem_toGrothendieck ⟨E', rfl, hF⟩
  · exact (Set.finite_range s).subset (by rintro _ ⟨j, rfl⟩; exact ⟨β j, rfl⟩)

/-- **An object of the big fppf site of `S` with quasi-compact underlying scheme is a
quasi-compact object** (Stacks 090H). The topology of the big fppf site of `S` is the localized
topology, so this is `AlgebraicGeometry.BigFppfSite.isQuasiCompactObject_of_compactSpace`
transported along `CategoryTheory.GrothendieckTopology.isQuasiCompactObject_over`. -/
@[sga "4 VI 1.6.2" "partial"]
public theorem BigFppfOver.isQuasiCompactObject_of_compactSpace (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (X : BigFppfOver B S hS)
    (hX : CompactSpace ((BigFppfOver.toScheme B S hS).obj X)) :
    (BigFppfOver.topology B S hS).IsQuasiCompactObject X :=
  GrothendieckTopology.isQuasiCompactObject_over _ X
    (B.isQuasiCompactObject_of_compactSpace X.left hX)

/-- **The terminal object of the big fppf site of a quasi-compact scheme is a quasi-compact
object** (Stacks 090H). This is the object at which the sections functor of Stacks 0935 is
evaluated to compute the global sections of a sheaf of modules on the big fppf site of `S`. -/
public theorem BigFppfOver.isQuasiCompactObject_top (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hcomp : CompactSpace S) :
    (BigFppfOver.topology B S hS).IsQuasiCompactObject (Over.mk (𝟙 (B.obj hS))) :=
  BigFppfOver.isQuasiCompactObject_of_compactSpace B S hS _ hcomp

end AlgebraicGeometry

end
