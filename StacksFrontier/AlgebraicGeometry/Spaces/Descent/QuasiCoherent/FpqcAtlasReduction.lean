module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedBaseEffectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FpqcCoverings

/-!
# The effectivity clause of Stacks 04W8 at a representable base, and the reduction to it

Step 1 of the effectivity clause of Stacks 04W8 —
`AlgebraicGeometry.Space.QuasiCoherentDescent.isEffective_of_isCovering_represented` —
proves that every descent datum relative to an fpqc covering of a **representable** algebraic
space **by representable** algebraic spaces is effective.  This file removes the second
restriction and then reduces an arbitrary fpqc covering to the first.

* **The members need not be representable.**  Each member of the family has a surjective étale
  scheme atlas, which refines the family by one whose members are representable, and pullback of
  descent data along such a refinement is fully faithful, so effectivity descends back through
  it — `AlgebraicGeometry.Space.QuasiCoherentDescent`
  `.isEffective_of_forall_isEffective_refineFamilyHom`.  That the refinement is again an fpqc
  covering is Stacks 03MR's composition clause followed by its reindexing, exactly as in
  Stacks 0419.
* **The base can be made representable.**  For a scheme atlas `ρ : R ⟶ X` of the target, the
  family of fibre products `X i ×_X R` refines `{X i ⟶ X}` by one-member surjective étale
  coverings — `AlgebraicGeometry.Space.isEtaleCovering_pullback`, Stacks 041F — and so
  effectivity descends back through it too; and that refinement is at the same time an fpqc
  covering **of `R`**, by Stacks 03MR's base-change clause.

What those two leave is the **transitivity** of effective descent: the refined family maps to
`R` and `R` maps to `X`, each step effective, and the conclusion wanted is effectivity over `X`.
That statement is the hypothesis `htrans` of
`…isEffective_of_isFpqcCovering_of_isEffective_comp`, and it is **proved** in
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/FpqcDescentTransitivity.lean`, where
`…isEffective_of_isFpqcCovering_comp` discharges it and
`…forall_isEffective_of_isFpqcCovering` is the effectivity clause of Stacks 04W8 with no
hypothesis beyond the covering.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.forall_isEffective_congr`: effectivity of every
  descent datum relative to a family is unchanged by an equality of the structure morphisms.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isEffective_of_isFpqcCovering_representedBase`:
  **every descent datum relative to an fpqc covering of a representable algebraic space is
  effective**, with no hypothesis on the members.
* `AlgebraicGeometry.Space.QuasiCoherentDescent`
  `.isEffective_of_forall_isEffective_fiberProductAtlas`: effectivity for a family follows from
  effectivity for its refinement by the fibre products with a scheme atlas of the target.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isFpqcCovering_fiberProductAtlas`: that
  refinement is an fpqc covering of the atlas.
* `AlgebraicGeometry.Space.QuasiCoherentDescent`
  `.isEffective_of_isFpqcCovering_of_isEffective_comp`: **the effectivity clause of Stacks 04W8
  for an arbitrary fpqc covering, over the transitivity statement alone.**

## Implementation notes

The index type of the refinement is the index type of the given family in both reductions, so
nothing has to be said about the size of a new index type, and the transitivity hypothesis is
quantified over families indexed by the same type.

`…forall_isEffective_congr` exists because the two reductions produce the structure morphisms of
the refined family as the composites `u i ≫ f i` while the statements they are fed to are
written at the morphisms those composites are equal to — `yoneda.map` of a morphism of the site
in the first, the other projection of the fibre product followed by the atlas in the second.
The equality is of *functions*, and the descent data depend on it, so it cannot be rewritten:
`subst` on a variable family of structure morphisms is what carries it, and that is all this
declaration is.

No `stacks` attribute is registered: Stacks 0419, 041F and 03MR are tagged where they are
proved, and the effectivity clause of Stacks 04W8 is reduced here to its step 3 rather than
proved; the tag is registered where both of its clauses are available, on
`AlgebraicGeometry.Space.QuasiCoherentDescent`
`.isEquivalence_canonicalDescentFunctor'_of_isFpqcCovering`.

## References

* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03MR](https://stacks.math.columbia.edu/tag/03MR)
* [Stacks Project, Tag 041F](https://stacks.math.columbia.edu/tag/041F)
* [Stacks Project, Tag 0419](https://stacks.math.columbia.edu/tag/0419)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Congr

variable {I : Type v} {X : AlgebraicSpaces B S hS}

/-- **Effectivity of every descent datum relative to a family is unchanged by an equality of
the structure morphisms of the family.**

The descent data depend on the structure morphisms, so the equality cannot be rewritten in the
statement; what carries it is `subst`, the family of structure morphisms being a variable
here. -/
theorem forall_isEffective_congr {Y : I → AlgebraicSpaces B S hS} {g g' : ∀ i, Y i ⟶ X}
    (hgg : g = g') (h : ∀ D : DescentDatum B S hS Y g, IsEffective B S hS Y g D)
    (D : DescentDatum B S hS Y g') : IsEffective B S hS Y g' D := by
  subst hgg
  exact h D

end Congr

section RepresentedBase

variable {I : Type v} {U : BigFppfOver B S hS}

/-- **Every descent datum for quasi-coherent modules relative to an fpqc covering of a
representable algebraic space is effective**, with no hypothesis on the members of the family.

Each member has a surjective étale scheme atlas, which makes the family of those atlases a
refinement of the given family by one-member surjective étale coverings; pullback of descent
data along such a refinement is fully faithful, so effectivity descends back through it by
`…isEffective_of_forall_isEffective_refineFamilyHom`.  The refined family is a family of
*representable* algebraic spaces over a representable algebraic space, and it is again an fpqc
covering by the composition clause of Stacks 03MR reindexed along `i ↦ ⟨i, ()⟩`, so
`…isEffective_of_isCovering_represented` — step 1 of the effectivity clause — applies to
it.

Its structure morphisms are the composites of the atlases with the given morphisms, and the
morphisms of the site they represent are their preimages under the fully faithful `yoneda`;
`…forall_isEffective_congr` identifies the two. -/
theorem isEffective_of_isFpqcCovering_representedBase
    (Wi : I → AlgebraicSpaces B S hS)
    (w : ∀ i, Wi i ⟶ representedAlgebraicSpace B S hS U)
    (hcov : IsFpqcCovering B S hS fun i => (w i).hom)
    (D : DescentDatum B S hS Wi w) : IsEffective B S hS Wi w D := by
  classical
  choose T e hsurj hetale using fun i => (Wi i).property.exists_atlas
  have hEtale (i : I) :
      IsEtaleCovering B S hS (fun _ : Unit => yoneda.obj (T i)) (fun _ => e i) := by
    refine ⟨(Wi i).property, fun _ => isAlgebraicSpace_yoneda B S hS (T i),
      fun _ => (isEtale_iff_presheaf_of_yoneda B S hS (e i)).2 (hetale i), ?_⟩
    rw [Set.iUnion_const, Set.range_eq_univ]
    exact (surjective_iff_surjective_pointsMap B S hS (Wi i).1 (Wi i).property (T i) (e i)).1
      (hsurj i)
  have hfpqc : IsFpqcCovering B S hS (fun i => e i ≫ (w i).hom) :=
    isFpqcCovering_reindex B S hS
      (isFpqcCovering_comp B S hS (X := (representedAlgebraicSpace B S hS U).1)
        (Xi := fun i => (Wi i).1)
        (Xij := fun ij : Σ _ : I, Unit => yoneda.obj (T ij.1))
        (isAlgebraicSpace_yoneda B S hS U) (fun i => (Wi i).property)
        (fun i _ => isAlgebraicSpace_yoneda B S hS (T i)) (fun i => (w i).hom)
        (fun i _ => e i) hcov
        (fun i => isFpqcCovering_of_isEtaleCovering B S hS
          (fun _ : Unit => yoneda.obj (T i)) (fun _ => e i) (hEtale i)))
      (σ := fun i : I => (⟨i, ()⟩ : Σ _ : I, Unit))
      (fun p => ⟨p.1, by cases p.2; rfl⟩)
  refine isEffective_of_forall_isEffective_refineFamilyHom B S hS
    (PreZeroHypercover.mk I Wi w) (fun i => representedAlgebraicSpace B S hS (T i))
    (fun i => ObjectProperty.homMk (e i))
    (fun i => relativelyRepresentable_of_isAlgebraicSpace B S hS (Wi i).property (e i))
    hEtale ?_ D
  refine forall_isEffective_congr B S hS
    (g := representedFamilyMap B S hS T
      (fun i => Yoneda.fullyFaithful.preimage (e i ≫ (w i).hom)))
    (funext fun i => ObjectProperty.hom_ext _ (Yoneda.fullyFaithful.map_preimage _)) ?_
  intro E
  refine isEffective_of_isCovering_represented B S hS T _ E
    ⟨isAlgebraicSpace_yoneda B S hS U, fun i => isAlgebraicSpace_yoneda B S hS (T i), ?_⟩
  have hfun : (fun i => e i ≫ (w i).hom) =
      fun i => yoneda.map (Yoneda.fullyFaithful.preimage (e i ≫ (w i).hom)) :=
    funext fun i => (Yoneda.fullyFaithful.map_preimage _).symm
  exact hfun ▸ hfpqc

end RepresentedBase

section Atlas

variable {I : Type v} {X : AlgebraicSpaces B S hS} {Xi : I → AlgebraicSpaces B S hS}
  (g : ∀ i, Xi i ⟶ X) {U : BigFppfOver B S hS}
  (ρ : representedAlgebraicSpace B S hS U ⟶ X)

/-- **Effectivity for a family of algebraic spaces over `X` follows from effectivity for its
refinement by the fibre products with a scheme atlas `ρ` of `X`.**

The projection `X i ×_X R ⟶ X i` is the base change of `ρ` along `X i ⟶ X`, so it is a
one-member surjective étale covering by Stacks 041F,
`AlgebraicGeometry.Space.isEtaleCovering_pullback`, and relatively representable because
relative representability is stable under base change and `ρ` has a representable source.  Those
are exactly the two hypotheses of
`…isEffective_of_forall_isEffective_refineFamilyHom`. -/
theorem isEffective_of_forall_isEffective_fiberProductAtlas
    (hρ : IsEtaleCovering B S hS (fun _ : Unit => yoneda.obj U) (fun _ => ρ.hom))
    (heff : ∀ E : DescentDatum B S hS
        (fun i => AlgebraicSpaces.fiberProduct B S hS (g i) ρ)
        (fun i => (ObjectProperty.homMk (pullback.fst (g i).hom ρ.hom) :
          AlgebraicSpaces.fiberProduct B S hS (g i) ρ ⟶ Xi i) ≫ g i),
      IsEffective B S hS _ _ E)
    (D : DescentDatum B S hS Xi g) : IsEffective B S hS Xi g D :=
  isEffective_of_forall_isEffective_refineFamilyHom B S hS
    (PreZeroHypercover.mk I Xi g)
    (fun i => AlgebraicSpaces.fiberProduct B S hS (g i) ρ)
    (fun i => ObjectProperty.homMk (pullback.fst (g i).hom ρ.hom))
    (fun i => (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
      (IsPullback.of_hasPullback (g i).hom ρ.hom).flip
      (relativelyRepresentable_of_isAlgebraicSpace B S hS X.property ρ.hom))
    (fun i => isEtaleCovering_pullback B S hS (g i).hom (Xi i).property
      (fun _ : Unit => yoneda.obj U) (fun _ => ρ.hom) hρ)
    heff D

/-- **The refinement of an fpqc covering of `X` by the fibre products with a morphism
`ρ : R ⟶ X` is an fpqc covering of `R`.**  This is the base-change clause of Stacks 03MR and
nothing else; it is stated here at the second projections read as morphisms of algebraic
spaces, which is the shape the reduction below consumes. -/
theorem isFpqcCovering_fiberProductAtlas
    (hg : IsFpqcCovering B S hS fun i => (g i).hom) :
    IsFpqcCovering B S hS fun i =>
      (ObjectProperty.homMk (pullback.snd (g i).hom ρ.hom) :
        AlgebraicSpaces.fiberProduct B S hS (g i) ρ ⟶
          representedAlgebraicSpace B S hS U).hom :=
  isFpqcCovering_pullback B S hS g ρ hg

/-- **The effectivity clause of Stacks 04W8 for an arbitrary fpqc covering of an arbitrary
algebraic space, over the transitivity statement alone.**

The hypothesis `htrans` is the transitivity of effective descent along the scheme atlas `ρ`:
every descent datum relative to a family that is an fpqc covering of `R` is effective *over
`X`*.  Everything else is supplied: the given family is refined by the fibre products with `ρ`,
which carries effectivity back by
`…isEffective_of_forall_isEffective_fiberProductAtlas`; that refinement is an fpqc covering of
`R` by `…isFpqcCovering_fiberProductAtlas`; and its structure morphism over `X` is the second
projection followed by `ρ`, by the cartesian square, which `…forall_isEffective_congr`
substitutes.

Combined with `…isEffective_of_isFpqcCovering_representedBase`, which makes every such family
effective *over `R`*, this is the whole of the effectivity clause except the passage from `R`
to `X`. -/
theorem isEffective_of_isFpqcCovering_of_isEffective_comp
    (hρ : IsEtaleCovering B S hS (fun _ : Unit => yoneda.obj U) (fun _ => ρ.hom))
    (hg : IsFpqcCovering B S hS fun i => (g i).hom)
    (htrans : ∀ (Wj : I → AlgebraicSpaces B S hS)
        (wj : ∀ i, Wj i ⟶ representedAlgebraicSpace B S hS U),
        IsFpqcCovering B S hS (fun i => (wj i).hom) →
        ∀ E : DescentDatum B S hS Wj (fun i => wj i ≫ ρ),
          IsEffective B S hS Wj (fun i => wj i ≫ ρ) E)
    (D : DescentDatum B S hS Xi g) : IsEffective B S hS Xi g D := by
  refine isEffective_of_forall_isEffective_fiberProductAtlas B S hS g ρ hρ ?_ D
  intro E
  refine forall_isEffective_congr B S hS
    (g := fun i => (ObjectProperty.homMk (pullback.snd (g i).hom ρ.hom) :
      AlgebraicSpaces.fiberProduct B S hS (g i) ρ ⟶
        representedAlgebraicSpace B S hS U) ≫ ρ)
    (funext fun i => (ObjectProperty.hom_ext _ pullback.condition).symm) ?_ E
  exact htrans (fun i => AlgebraicSpaces.fiberProduct B S hS (g i) ρ)
    (fun i => ObjectProperty.homMk (pullback.snd (g i).hom ρ.hom))
    (isFpqcCovering_fiberProductAtlas B S hS g ρ hg)

end Atlas

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
