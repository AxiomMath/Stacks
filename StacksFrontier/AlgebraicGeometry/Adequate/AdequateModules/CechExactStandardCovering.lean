module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineLocal
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.CoveringSheafCondition
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.ProductAlgebra
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsCoveringSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringsBaseChange

/-!
# The Čech condition of Tag 06VH for the product algebra of a standard affine covering

`Stacks.Adequate.cechExactOn_affineSectionFunctor_of_hasFactoringCovering` derives the Čech
condition of [Stacks, Tag 06VH] for the affine-section functor from the `τ`-sheaf condition of
the site, at the price of one hypothesis: every base change `Spec(C₀ ⊗_A A') ⟶ Spec(C₀)` of
`Spec(A') ⟶ Spec(A)` must be *covered*, in the sense of
`Stacks.Adequate.BigSite.HasFactoringCovering`. This module discharges that hypothesis for the
algebra the source's proof of [Stacks, Tag 06VI] uses, `A' = A'₁ × ⋯ × A'ₘ` the product of a
finite standard affine `τ`-covering of [Stacks, Tag 06VB], and so states the Čech condition
there with no hypothesis at all.

## Main results

* `Stacks.Adequate.hasFactoringCovering_of_proj` — **the morphism `Spec(C₀ ⊗_A A') ⟶ Spec(C₀)`
  is covered as soon as `A'` admits a map to each member of a finite standard affine
  `τ`-covering of `Spec A`.** This is the hypothesis of
  `Stacks.Adequate.cechExactOn_affineSectionFunctor_of_hasFactoringCovering`, discharged.
* `Stacks.Adequate.cechExactOn_affineSectionFunctor_pi` — **the Čech condition of
  [Stacks, Tag 06VH] for the affine-section functor at the product algebra of a finite standard
  affine `τ`-covering, unconditionally.**

## Implementation notes

**Only the projections are used, not the product.** What the factoring family needs of `A'` is a
family of `A`-algebra maps `A' ⟶ A'ⱼ` to the members of the covering, and nothing else: the
factoring morphism out of `Spec(C₀ ⊗_A A'ⱼ)` is `Spec` of the map out of the pushout
`C₁ = C₀ ⊗_A A'` determined by `C₀ ⟶ C₀ ⊗_A A'ⱼ` on one side and
`A' ⟶ A'ⱼ ⟶ C₀ ⊗_A A'ⱼ` on the other, and the pushout property is exactly the hypothesis
`IsColimit (BinaryCofan.mk …)` already carried by
`Stacks.Adequate.cechExactOn_affineSectionFunctor_of_hasFactoringCovering`. So
`Stacks.Adequate.hasFactoringCovering_of_proj` is stated at the projections, and the product is
only substituted in `Stacks.Adequate.cechExactOn_affineSectionFunctor_pi`.

That is why none of the identification
`C₀ ⊗_A (A'₁ × ⋯ × A'ₘ) ≅ (C₀ ⊗_A A'₁) × ⋯ × (C₀ ⊗_A A'ₘ)`,
`AlgebraicGeometry.specPiIso`, the coproduct injections of a disjoint union of spectra, nor the
identification of a binary cofan with a tensor product appears below: a map *out* of the
pushout `C₁` is constructed from the universal property directly, and it is the composite with
`iB` — which the universal property computes to be `C₀ ⟶ C₀ ⊗_A A'ⱼ` — and not the morphism
`Spec(C₀ ⊗_A A'ⱼ) ⟶ Spec(C₁)` itself, that has to be a `τ`-covering morphism.

**The three facts about the pieces come from one base change.** The family
`{Spec(C₀ ⊗_A A'ⱼ) ⟶ Spec(C₀)}` is the base change of `{Spec(A'ⱼ) ⟶ Spec(A)}` along
`Spec(C₀) ⟶ Spec(A)`, so `AlgebraicGeometry.IsStandardCovering.pullback_fst` delivers at once
that each member is a `τ`-covering morphism
(`AlgebraicGeometry.ExtendingFunctors.coveringMorphismProperty_of_isStandardCovering`), that the
members are jointly surjective, and — with `Stacks.Adequate.BigSite.size_lt_of_isStandardCovering`
— that each `Spec(C₀ ⊗_A A'ⱼ)` is again a scheme of the site, which is what lets it be an object
of `AdequateFunctor.AlgebrasInSite`. All three are then transported from `Spec C₀ ×_{Spec A}
Spec A'ⱼ` to `Spec(C₀ ⊗_A A'ⱼ)` along the single isomorphism
`AlgebraicGeometry.pullbackSpecIso`, by `AlgebraicGeometry.Scheme.size_congr`,
`CategoryTheory.MorphismProperty.RespectsIso.precomp` and
`Stacks.Adequate.range_comp_of_isIso`.

The covering is indexed by `Fin n`, as in [Stacks, Tag 06VI], while
`Stacks.Adequate.BigSite.HasFactoringCovering` asks for an index type in `Type u`, the universe
in which the index type of a coproduct of schemes of `Scheme.{u}` lives; `ULift` bridges the two.

The whole argument is uniform in `τ` and in the chosen big site: the five-way eliminator for the
field `Stacks.Adequate.BigSite.chosen` is never unfolded here, it has already been run inside
`Stacks.Adequate.BigSite.size_lt_of_isStandardCovering` and
`Stacks.Adequate.sieve_generate_mem_topology_of_coveringMorphismProperty`.

**What this does not do.** `Stacks.Adequate.StandardAffineDescent` does not follow from
`Stacks.Adequate.cechExactOn_affineSectionFunctor_pi` alone; what is settled here is one of its
inputs, the Čech-exactness hypothesis `hexact`. The port of [Stacks, Tag 06VH] to the algebras
of the site is `AdequateFunctor.isAdequate_of_descent_on`, and
`Stacks.Adequate.standardAffineDescent_of_productAdequacy` in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/StandardAffineDescentReduction.lean`
assembles the two, reducing `StandardAffineDescent` to adequacy of `F_{F, A'}` for
`A' = A'₁ × ⋯ × A'ₘ`, which
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/StandardAffineProductAdequacy.lean`
then proves. See the implementation notes of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineLocal.lean`.

No `@[stacks]` attribute is attached: the statement is
`Stacks.Adequate.cechExactOn_affineSectionFunctor` with its hypothesis supplied, and that theorem
already carries what Tag 06VH asks of it.

## References

* [Stacks Project, Tag 06VH](https://stacks.math.columbia.edu/tag/06VH)
* [Stacks Project, Tag 06VI](https://stacks.math.columbia.edu/tag/06VI)
* [Stacks Project, Tag 06VB](https://stacks.math.columbia.edu/tag/06VB)
* [Stacks Project, Tag 03X9](https://stacks.math.columbia.edu/tag/03X9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u m

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-- Precomposing with an isomorphism does not change the set-theoretic image of a morphism of
schemes, an isomorphism being surjective on points. -/
public theorem range_comp_of_isIso {X Y Z : Scheme.{u}} (e : X ⟶ Y) (k : Y ⟶ Z) [IsIso e] :
    Set.range (e ≫ k) = Set.range k := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp]
  exact Function.Surjective.range_comp e.homeomorph.surjective _

/-- **The base change of `Spec(A') ⟶ Spec(A)` along an algebra of the site is covered, as soon
as `A'` maps to each member of a finite standard affine `τ`-covering of `Spec A`.**

This is the hypothesis of
`Stacks.Adequate.cechExactOn_affineSectionFunctor_of_hasFactoringCovering` discharged: `C₁` is
the pushout `C₀ ⊗_A A'`, and the factoring family of
`Stacks.Adequate.BigSite.HasFactoringCovering` is `{Spec(C₀ ⊗_A A'ⱼ) ⟶ Spec(C₁)}`, the map out
of the pushout being determined by `C₀ ⟶ C₀ ⊗_A A'ⱼ` and by `A' ⟶ A'ⱼ ⟶ C₀ ⊗_A A'ⱼ`. Its
composite with `Spec(C₁) ⟶ Spec(C₀)` is therefore `Spec(C₀ ⊗_A A'ⱼ) ⟶ Spec(C₀)`, the base
change of `Spec(A'ⱼ) ⟶ Spec(A)` along `Spec(C₀) ⟶ Spec(A)`, and that family is a standard
affine `τ`-covering of `Spec C₀` by
`AlgebraicGeometry.IsStandardCovering.pullback_fst`. No use is made of `A'` being the product of
the `A'ⱼ`; only the projections are needed. -/
public theorem hasFactoringCovering_of_proj (B : BigSite τ S) (A : CommRingCat.{u})
    (f : Spec A ⟶ S) {n : ℕ} (P : Fin n → CommAlgCat.{u} A)
    (hstd : IsStandardCovering τ (fun j => Spec (CommRingCat.of ↥(P j)))
      (fun j => Spec.map (CommRingCat.ofHom (algebraMap ↥A ↥(P j)))))
    {A' C₀ C₁ : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)}
    (π : ∀ j, A'.obj ⟶ P j) (iB : C₀ ⟶ C₁) (iA : A' ⟶ C₁)
    (hc : IsColimit (BinaryCofan.mk
      ((AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).map iB)
      ((AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).map iA))) :
    B.HasFactoringCovering ((affineSpecOver B A f).map iB.op) := by
  have hbc := hstd.pullback_fst (V := Spec (CommRingCat.of ↥C₀.obj))
    (Spec.map (CommRingCat.ofHom (algebraMap ↥A ↥C₀.obj)))
  have hD : ∀ j, schemeSizeBelow B.cutoff
      (Spec (CommRingCat.of (↥C₀.obj ⊗[↥A] ↥(P j)))) := fun j => by
    change (Spec (CommRingCat.of (↥C₀.obj ⊗[↥A] ↥(P j)))).size < B.cutoff
    rw [← Scheme.size_congr (pullbackSpecIso ↥A ↥C₀.obj ↥(P j))]
    exact B.size_lt_of_isStandardCovering hbc C₀.property j
  let D : Fin n → AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff) :=
    fun j => ⟨CommAlgCat.of ↥A (↥C₀.obj ⊗[↥A] ↥(P j)), hD j⟩
  let inc : ∀ j, C₀ ⟶ D j := fun j =>
    ObjectProperty.homMk (CommAlgCat.ofHom Algebra.TensorProduct.includeLeft)
  let dsc : ∀ j, C₁ ⟶ D j := fun j =>
    ObjectProperty.homMk (BinaryCofan.IsColimit.desc hc
      (CommAlgCat.ofHom Algebra.TensorProduct.includeLeft)
      (π j ≫ CommAlgCat.ofHom Algebra.TensorProduct.includeRight))
  have hkg : ∀ j, (affineSpecOver B A f).map (dsc j).op ≫ (affineSpecOver B A f).map iB.op =
      (affineSpecOver B A f).map (inc j).op := fun j => by
    rw [← Functor.map_comp, ← op_comp]
    exact congrArg (fun φ => (affineSpecOver B A f).map (Quiver.Hom.op φ))
      ((AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).map_injective
        (BinaryCofan.IsColimit.inl_desc hc _ _))
  have hfst : ∀ j, (B.toOver.map ((affineSpecOver B A f).map (inc j).op)).left =
      (pullbackSpecIso ↥A ↥C₀.obj ↥(P j)).inv ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap ↥A ↥C₀.obj)))
          (Spec.map (CommRingCat.ofHom (algebraMap ↥A ↥(P j)))) := fun j => by
    rw [pullbackSpecIso_inv_fst]
    rfl
  have hri := ExtendingFunctors.respectsIso_coveringMorphismProperty.{u} τ
  refine ⟨ULift.{u} (Fin n), fun i => (affineSpecOver B A f).obj (op (D i.down)),
    fun i => (affineSpecOver B A f).map (dsc i.down).op, fun i => ?_, fun x => ?_⟩
  · rw [hkg i.down, hfst i.down]
    exact MorphismProperty.RespectsIso.precomp _ _ _
      (ExtendingFunctors.coveringMorphismProperty_of_isStandardCovering τ hbc i.down)
  · have hx : x ∈ ⋃ j, Set.range (pullback.fst
        (Spec.map (CommRingCat.ofHom (algebraMap ↥A ↥C₀.obj)))
        (Spec.map (CommRingCat.ofHom (algebraMap ↥A ↥(P j))))) :=
      hbc.jointly_surjective ▸ Set.mem_univ _
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    rw [← range_comp_of_isIso (pullbackSpecIso ↥A ↥C₀.obj ↥(P j)).inv, ← hfst j,
      ← hkg j] at hj
    exact ⟨ULift.up j, hj⟩

/-- **The Čech condition of [Stacks, Tag 06VH] for the affine-section functor at the product
algebra of a finite standard affine `τ`-covering, with no hypothesis.**

`Stacks.Adequate.cechExactOn_affineSectionFunctor_of_hasFactoringCovering` reduces the Čech
condition to the base changes of `Spec(A') ⟶ Spec(A)` being covered, and
`Stacks.Adequate.hasFactoringCovering_of_proj` supplies that for
`A' = A'₁ × ⋯ × A'ₘ` through the projections of the product. The product is an algebra of the
site by `Stacks.Adequate.schemeSizeBelow_Spec_pi`, and the members of the covering are by
`Stacks.Adequate.BigSite.size_lt_of_isStandardCovering`.

This is the Čech-exactness input `hexact` of `AdequateFunctor.isAdequate_of_descent` for the
passage through the product algebra of [Stacks, Tag 06VB], and nothing about `F` beyond
`CategoryTheory.SheafOfModules.isSheaf` is used. -/
public theorem cechExactOn_affineSectionFunctor_pi (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf) (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (hA : schemeSizeBelow B.cutoff (Spec A)) {n : ℕ} (P : Fin n → CommAlgCat.{u} A)
    (hstd : IsStandardCovering τ (fun j => Spec (CommRingCat.of ↥(P j)))
      (fun j => Spec.map (CommRingCat.ofHom (algebraMap ↥A ↥(P j))))) :
    AdequateFunctor.CechExactOn
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))
      (affineSectionFunctor B F A f)
      ⟨CommAlgCat.of ↥A (∀ j, ↥(P j)),
        schemeSizeBelow_Spec_pi B (fun j => CommRingCat.of ↥(P j))
          fun j => B.size_lt_of_isStandardCovering hstd hA j⟩ :=
  cechExactOn_affineSectionFunctor_of_hasFactoringCovering B F A f _ fun iB iA hc =>
    hasFactoringCovering_of_proj B A f P hstd
      (fun j => CommAlgCat.ofHom (Pi.evalAlgHom ↥A (fun j => ↥(P j)) j)) iB iA hc

end Stacks.Adequate

end
