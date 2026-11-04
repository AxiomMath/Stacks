module

public import StacksFrontier.CategoryTheory.Sites.AbelianPullbackExact.LanCriterion
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Continuity
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Sheaves
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumNaturality.ComponentCohomology

/-!
# Cohomology over an object of one summand of a simplicial semi-representable site

Stacks 0DC0 is the case of Stacks 0DBZ in which the simplicial degree concerned is the site of
objects over a semi-representable object `K`. An object of that site lies over one summand
`K.obj i`, the degree-`n` restriction of a sheaf on the total site is a family of sheaves on the
summand slices, and the claim is that cohomology over the object agrees with cohomology, over the
same object read in `C / K.obj i`, of the `i`-th member of that family.

The degree-`n` site is identified with the disjoint union of the slice sites by an equality of
sites `hsite`, exactly as the source's situation provides it, and the family of sheaves is read
off by `CategoryTheory.SemiRepresentable.formalCoproductSliceSheavesEquivalence` (Stacks 0D89).
What has to be supplied beyond Stacks 0DBZ is the same comparison again for the inclusion of one
summand slice into the disjoint union: that inclusion is continuous and cocontinuous, and the
pullback of abelian sheaves along it is exact because each of its comma categories has an initial
object.

## Main results

* `Stacks.Cohomology.SimplicialSummand.weaklyInitial_structuredArrow_incl`: every comma category
  of the inclusion of a summand slice has an initial object.
* `Stacks.Cohomology.SimplicialSummand.preservesMonomorphisms_sheafPullback_incl`: hence the
  pullback of abelian sheaves along that inclusion is exact.
* `Stacks.Cohomology.SimplicialSummand.summandSheafIso`: the `i`-th member of the family of
  sheaves attached to a sheaf on the disjoint union is its pullback along the `i`-th inclusion.
* `Stacks.Cohomology.SimplicialSummand.cohomologyObj_iso_summand`: **Stacks 0DC0.**

## Implementation notes

The comma category `StructuredArrow V (incl i)` is empty unless `V` lies in the `i`-th summand,
and when it does it has an initial object, namely the identity of `V`; the proof destructures the
given object of the comma category, which forces `V` into that form, and then quotes
`CategoryTheory.StructuredArrow.mkIdInitial`, which applies because the inclusion of a summand of
a `CategoryTheory.Sigma` category is full and faithful. Writing the initial object's structure
morphism as `𝟙` directly runs into the double-`CategoryStruct` pitfall of a sigma category — `𝟙`
resolves through `CategoryTheory.Sigma.SigmaHom.instCategoryStructSigma` while the comma category
is formed through `CategoryTheory.Sigma.sigma` — so it is written at the type
`CategoryTheory.StructuredArrow.mkIdInitial` dictates.

Cocontinuity is definitional: a sieve is covering for the componentwise topology exactly when its
restriction to the summand is covering, which is
`CategoryTheory.SemiRepresentable.mem_componentwiseTopology_iff`.

`cohomologyIsoOfSiteEq` is stated for two arbitrary bundled sites so that the equality can be
eliminated by `cases`; at the equality `hsite` of the statement below neither side is a variable,
so the elimination has to happen in a lemma. `eqMp_eqMp_symm` is the companion fact that the two
transports of `hsite` cancel.

## References

* [Stacks Project, Tag 0D89](https://stacks.math.columbia.edu/tag/0D89)
* [Stacks Project, Tag 0DBZ](https://stacks.math.columbia.edu/tag/0DBZ)
* [Stacks Project, Tag 0DC0](https://stacks.math.columbia.edu/tag/0DC0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.SemiRepresentable
open CategoryTheory.Sigma (incl)

universe w u

namespace Stacks.Cohomology.SimplicialSummand

variable {C : Type u} [SmallCategory C] {K : FormalCoproduct.{u} C}

/-- **Every comma category of the inclusion of a summand slice has an initial object.** A
morphism of a `CategoryTheory.Sigma` category cannot change the index, so the comma category of
the `i`-th inclusion over `V` is empty unless `V` lies in the `i`-th summand, and when it does
the identity of `V` is an initial object of it. The statement is in the weak-initiality form
`Stacks.Sites.AbelianPullback.preservesMonomorphisms_sheafPullback_of_weaklyInitial` consumes. -/
theorem weaklyInitial_structuredArrow_incl (i : K.I) (V : ComponentOver K)
    (x : StructuredArrow V (incl (C := fun i : K.I => Over (K.obj i)) i)) :
    ∃ W : StructuredArrow V (incl (C := fun i : K.I => Over (K.obj i)) i),
      (∀ {y : StructuredArrow V (incl (C := fun i : K.I => Over (K.obj i)) i)},
          (y ⟶ x) → Nonempty (W ⟶ y)) ∧
        ∀ {y : StructuredArrow V (incl (C := fun i : K.I => Over (K.obj i)) i)}
          (q q' : W ⟶ y), q = q' := by
  obtain ⟨⟨⟩, Z, h⟩ := x
  cases h with
  | @mk _ X _ _ =>
    have hinit := StructuredArrow.mkIdInitial
      (T := incl (C := fun i : K.I => Over (K.obj i)) i) (Y := X)
    refine ⟨StructuredArrow.mk (T := incl (C := fun i : K.I => Over (K.obj i)) i)
      (𝟙 ((incl (C := fun i : K.I => Over (K.obj i)) i).obj X)), ?_, ?_⟩
    · intro y _
      exact ⟨hinit.to y⟩
    · intro y q q'
      exact hinit.hom_ext q q'

/-- The inclusion of the `i`-th summand slice is cocontinuous, by the definition of the
componentwise topology. -/
theorem incl_isCocontinuous (J : GrothendieckTopology C) (K : FormalCoproduct.{u} C) (i : K.I) :
    (incl (C := fun i : K.I => Over (K.obj i)) i).IsCocontinuous
      (J.over (K.obj i)) (componentwiseTopology J K) :=
  ⟨fun hS => hS⟩

/-- **The pullback of abelian sheaves along the inclusion of a summand slice is exact.** Its
comma categories have initial objects, so the criterion of Stacks 002X applies. -/
theorem preservesMonomorphisms_sheafPullback_incl
    (J : GrothendieckTopology C) (K : FormalCoproduct.{u} C) (i : K.I) :
    haveI := incl_isContinuous J K i
    ((incl (C := fun i : K.I => Over (K.obj i)) i).sheafPullback Ab.{u}
      (J.over (K.obj i)) (componentwiseTopology J K)).PreservesMonomorphisms :=
  have := incl_isContinuous J K i
  Stacks.Sites.AbelianPullback.preservesMonomorphisms_sheafPullback_of_weaklyInitial _ Ab.{u}
    _ _ (weaklyInitial_structuredArrow_incl i)

/-- **Transporting cohomology along an equality of sites.** Stated for two arbitrary bundled
sites, so that the equality is between variables and can be eliminated by `cases`. -/
def cohomologyIsoOfSiteEq {T₁ T₂ : Σ D : Cat.{u, u}, GrothendieckTopology D} (h : T₁ = T₂)
    [HasSheafify T₁.2 Ab.{u}] [HasSheafify T₂.2 Ab.{u}]
    [HasExt.{w} (Sheaf T₁.2 Ab.{u})] [HasExt.{w} (Sheaf T₂.2 Ab.{u})]
    (F : Sheaf T₁.2 Ab.{u}) (p : ℕ) (X : T₁.1) :
    Sheaf.H'.{w, u, u} F p X ≅
      Sheaf.H'.{w, u, u}
        (Eq.mp (congrArg (fun T : Σ D : Cat.{u, u}, GrothendieckTopology D =>
          Sheaf T.2 Ab.{u}) h) F) p
        (Eq.mp (congrArg (fun T : Σ D : Cat.{u, u}, GrothendieckTopology D =>
          (T.1 : Type u)) h) X) := by
  cases h
  exact Iso.refl _

/-- The `i`-th component of a sheaf on the componentwise site, read as the pullback along the
`i`-th component inclusion. -/
def summandSheafIso (J : GrothendieckTopology C) (K : FormalCoproduct.{u} C) (i : K.I)
    [HasSheafify (J.over (K.obj i)) Ab.{u}] [HasSheafify (componentwiseTopology J K) Ab.{u}]
    (Fn : Sheaf (componentwiseTopology J K) Ab.{u}) :
    haveI := incl_isContinuous J K i
    haveI := incl_isCocontinuous J K i
    ((formalCoproductSliceSheavesEquivalence J K Ab.{u}).val.functor.obj Fn) i ≅
      ((incl (C := fun i : K.I => Over (K.obj i)) i).sheafPullbackCocontinuous Ab.{u}
        (J.over (K.obj i)) (componentwiseTopology J K)).obj Fn :=
  haveI := incl_isContinuous J K i
  haveI := incl_isCocontinuous J K i
  (fullyFaithfulSheafToPresheaf (J.over (K.obj i)) Ab.{u}).preimageIso
      ((Classical.choice
          ((formalCoproductSliceSheavesEquivalence J K Ab.{u}).property i)).app Fn ≪≫
        ((Functor.sheafPushforwardContinuousCompSheafToPresheafIso
          (incl (C := fun i : K.I => Over (K.obj i)) i) Ab.{u}
          (J.over (K.obj i)) (componentwiseTopology J K)).app Fn).symm) ≪≫
    ((Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
      (incl (C := fun i : K.I => Over (K.obj i)) i) Ab.{u}
      (J.over (K.obj i)) (componentwiseTopology J K)).app Fn).symm

/-- The two transports attached to an equality and its symmetric cancel. -/
theorem eqMp_eqMp_symm {α : Sort*} {T₁ T₂ : α} (f : α → Type u)
    (h : T₁ = T₂) (x : f T₂) : Eq.mp (congrArg f h) (Eq.mp (congrArg f h.symm) x) = x := by
  cases h
  rfl

/-- **Stacks 0DC0.** Cohomology over an object of one summand of a simplicial semi-representable
site agrees with the cohomology, with coefficients in the corresponding member of the family of
sheaves attached to the restriction of the sheaf to that simplicial degree.

This is Stacks 0DBZ (`Stacks.Cohomology.SimplicialComponent.cohomologyObj_iso_component`) for the
component inclusion, transported along the identification `hsite` of the degree-`n` site with the
disjoint union of the summand slices, followed by the same bigger-site comparison again for the
inclusion of the `i`-th summand slice. -/
@[stacks 0DC0]
def cohomologyObj_iso_summand
    (J : GrothendieckTopology C) (K : FormalCoproduct.{u} C)
    (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)
    (hsite : (⟨S.component n, S.componentTopology n⟩ :
        Σ D : Cat.{u, u}, GrothendieckTopology D) =
      ⟨Cat.of (ComponentOver K), componentwiseTopology J K⟩)
    [HasSheafify S.totalTopology Ab.{u}]
    [HasSheafify (S.componentTopology n) Ab.{u}]
    [HasSheafify (componentwiseTopology J K) Ab.{u}]
    [HasExt.{w} (Sheaf S.totalTopology Ab.{u})]
    [HasExt.{w} (Sheaf (S.componentTopology n) Ab.{u})]
    [HasExt.{w} (Sheaf (componentwiseTopology J K) Ab.{u})]
    (i : K.I) (U : Over (K.obj i))
    [HasSheafify (J.over (K.obj i)) Ab.{u}]
    [HasExt.{w} (Sheaf (J.over (K.obj i)) Ab.{u})]
    (F : Sheaf S.totalTopology Ab.{u}) (p : ℕ) :
    let V : S.component n :=
      Eq.mp (congrArg (fun T : Σ D : Cat.{u, u}, GrothendieckTopology D =>
        (T.1 : Type u)) hsite.symm) (⟨i, U⟩ : ComponentOver K)
    let Fn : Sheaf (componentwiseTopology J K) Ab.{u} :=
      Eq.mp (congrArg (fun T : Σ D : Cat.{u, u}, GrothendieckTopology D =>
        Sheaf T.2 Ab.{u}) hsite)
        (((SimplicialSiteSituation.componentFunctor S n).sheafPullbackCocontinuous
          Ab.{u} (S.componentTopology n) S.totalTopology).obj F)
    Sheaf.H'.{w, u, u} F p ((SimplicialSiteSituation.componentFunctor S n).obj V) ≅
      Sheaf.H'.{w, u, u}
        (((formalCoproductSliceSheavesEquivalence J K Ab.{u}).val.functor.obj Fn) i) p U := by
  intro V Fn
  haveI := incl_isContinuous J K i
  haveI := incl_isCocontinuous J K i
  haveI := preservesMonomorphisms_sheafPullback_incl J K i
  have hmp : Eq.mp (congrArg (fun T : Σ D : Cat.{u, u}, GrothendieckTopology D =>
      (T.1 : Type u)) hsite) V = (⟨i, U⟩ : ComponentOver K) :=
    eqMp_eqMp_symm
      (fun T : Σ D : Cat.{u, u}, GrothendieckTopology D => (T.1 : Type u)) hsite
      (⟨i, U⟩ : ComponentOver K)
  refine Stacks.Cohomology.SimplicialComponent.cohomologyObj_iso_component S n V F p ≪≫
    cohomologyIsoOfSiteEq hsite
      (((SimplicialSiteSituation.componentFunctor S n).sheafPullbackCocontinuous
        Ab.{u} (S.componentTopology n) S.totalTopology).obj F) p V ≪≫
    eqToIso (congrArg (fun X : ComponentOver K => Sheaf.H'.{w, u, u} Fn p X) hmp) ≪≫ ?_
  refine Stacks.Cohomology.SimplicialComponent.cohomologyObjIsoExtUniv
    (J.over (K.obj i)) (componentwiseTopology J K)
    (incl (C := fun i : K.I => Over (K.obj i)) i) Fn p U ≪≫ ?_
  exact ((Sheaf.cohomologyPresheafFunctor (J.over (K.obj i)) p).mapIso
    (summandSheafIso J K i Fn).symm).app (op U)

end Stacks.Cohomology.SimplicialSummand

end
