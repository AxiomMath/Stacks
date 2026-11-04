module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.IsomorphismFunctorRepresentability

/-!
# Affine test schemes suffice for the isomorphism locus of a module map

Let `f : X ⟶ S` be a morphism of schemes and `u : F ⟶ G` a homomorphism of quasi-coherent
modules on `X`.  `Stacks.Flatness.ModuleMapBaseChangeSituation.isomorphismFunctor` is the
subterminal functor on schemes over `S` recording where the base change of `u` becomes an
isomorphism.

A monomorphism `W ⟶ S` represents that functor as soon as it does so *on affine schemes over
`S`*: the condition on an arbitrary `T` is tested on an affine open cover of `T`, where the
factorizations through `W` exist by hypothesis and glue because `W ⟶ S` is a monomorphism, and
conversely a factorization through `W` propagates the condition from `W` itself, which is settled
on an affine open cover of `W`.  Both halves use that the isomorphism condition is Zariski local
on the base, a special case of the fpqc sheaf property of Tag 05MJ.

## Main results

* `Stacks.Flatness.ModuleMapBaseChangeSituation.isIsomorphismAfterBaseChange_of_openCover`: the
  isomorphism condition is Zariski local on the base.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.isoFactorizationCriterion_of_affineTests`: a
  monomorphism into the base through which exactly the affine schemes making `u` an isomorphism
  factor satisfies the factorization criterion on every scheme over the base.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.representableByOfAffineTests`: such a
  monomorphism represents the isomorphism functor.

## References

* [Stacks Project, Tag 05MJ](https://stacks.math.columbia.edu/tag/05MJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Flatness.ModuleMapBaseChangeSituation

variable (D : ModuleMapBaseChangeSituation.{u})

/-- A family of morphisms over the base into an object whose structure morphism is a
monomorphism, indexed by an open cover of the source, glues to a single morphism over the base:
two members agree on an overlap because they agree after composition with the monomorphism. -/
theorem exists_comp_eq_of_openCover {S : Scheme.{u}} (T W : Over S) (hW : Mono W.hom)
    (𝒰 : T.left.OpenCover)
    (h : ∀ i, ∃ g : 𝒰.X i ⟶ W.left, g ≫ W.hom = 𝒰.f i ≫ T.hom) :
    ∃ g : T.left ⟶ W.left, g ≫ W.hom = T.hom := by
  choose g hg using h
  have := hW
  have hc : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j := by
    intro i j
    refine (cancel_mono W.hom).mp ?_
    rw [Category.assoc, Category.assoc, hg, hg, ← Category.assoc, ← Category.assoc,
      pullback.condition]
  refine ⟨𝒰.glueMorphisms g hc, Scheme.Cover.hom_ext 𝒰 _ _ fun i ↦ ?_⟩
  rw [← Category.assoc, 𝒰.ι_glueMorphisms g hc i, hg]

/-- **The isomorphism condition after base change is Zariski local on the base.**  An open cover
is in particular an fpqc covering, so this is a special case of the fpqc locality of Tag
05MJ. -/
theorem isIsomorphismAfterBaseChange_of_openCover (T : Over D.S) (𝒰 : T.left.OpenCover)
    (h : ∀ i, D.IsIsomorphismAfterBaseChange (Over.mk (𝒰.f i ≫ T.hom))) :
    D.IsIsomorphismAfterBaseChange T :=
  (D.isIsomorphismAfterBaseChange_iff_fpqcCover T
      ⟨𝒰.toPreZeroHypercover,
        Scheme.zariskiPrecoverage_le_fpqcPrecoverage _ 𝒰.mem₀⟩).2 h

/-- **Affine test schemes suffice for the factorization criterion.**  If a monomorphism
`i : Z ⟶ S` has the property that an *affine* scheme over `S` makes `u` an isomorphism exactly
when its structure morphism factors through `i`, then the same holds for every scheme over
`S`. -/
theorem isoFactorizationCriterion_of_affineTests {Z : Scheme.{u}} (i : Z ⟶ D.S) (hi : Mono i)
    (h : ∀ T : Over D.S, IsAffine T.left →
      (D.IsIsomorphismAfterBaseChange T ↔ ∃ g : T.left ⟶ Z, g ≫ i = T.hom)) :
    D.IsoFactorizationCriterion i := by
  have hiso : D.IsIsomorphismAfterBaseChange (Over.mk i) := by
    refine D.isIsomorphismAfterBaseChange_of_openCover (Over.mk i) Z.affineCover fun j ↦ ?_
    exact (h (Over.mk (Z.affineCover.f j ≫ i)) (by dsimp; infer_instance)).2
      ⟨Z.affineCover.f j, rfl⟩
  intro T
  refine ⟨fun hT ↦ ?_, fun ⟨g, hg⟩ ↦ D.isIsomorphismAfterBaseChange_of_hom
    (T := Over.mk i) (Over.homMk g hg) hiso⟩
  refine exists_comp_eq_of_openCover T (Over.mk i) hi T.left.affineCover fun j ↦ ?_
  exact (h (Over.mk (T.left.affineCover.f j ≫ T.hom)) (by dsimp; infer_instance)).1
    (D.isIsomorphismAfterBaseChange_of_hom (Over.homMk (T.left.affineCover.f j) rfl) hT)

/-- A monomorphism into the base through which exactly the affine schemes over the base making
`u` an isomorphism factor represents the isomorphism functor. -/
noncomputable def representableByOfAffineTests {Z : Scheme.{u}} (i : Z ⟶ D.S) (hi : Mono i)
    (h : ∀ T : Over D.S, IsAffine T.left →
      (D.IsIsomorphismAfterBaseChange T ↔ ∃ g : T.left ⟶ Z, g ≫ i = T.hom)) :
    D.isomorphismFunctor.RepresentableBy (Over.mk i) :=
  D.representableByOfIsoFactorizationCriterion i hi
    (D.isoFactorizationCriterion_of_affineTests i hi h)

end Stacks.Flatness.ModuleMapBaseChangeSituation

end
