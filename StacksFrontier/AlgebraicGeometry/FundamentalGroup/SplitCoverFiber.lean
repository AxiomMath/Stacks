module

public import StacksFrontier.AlgebraicGeometry.FiniteEtaleColimits.FpqcLocalCoequalizer
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleGaloisCategory
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.ImageStabilizer

/-!
# The geometric fibre of a split cover

Let `X` be a scheme, `x` a geometric point of it and `ι` a finite index type. The split cover
`∐_{i : ι} X` of `Stacks.FundamentalGroup.splitCover` is the coproduct of `ι` copies of the
terminal finite étale cover, and this file computes its geometric fibre at `x`: it is `ι`, and
the étale fundamental group acts on it trivially.

Both statements come from the same observation. A lift of `x` to `∐_{i : ι} X` factors through
exactly one copy of `X`, because the source of a geometric point is the spectrum of a field and
so has a single point, while the copies of `X` are disjoint open subschemes of their coproduct;
and the factorization is unique because a morphism to an open subscheme is determined by the
morphism to the ambient scheme. Each point of the fibre is therefore the image of the unique
point of the fibre of the terminal cover under one of the `ι` inclusions, and a natural
automorphism of the fibre functor commutes with those inclusions and acts trivially on the fibre
of the terminal cover.

## Main definitions

* `Stacks.FundamentalGroup.topFiberPoint`: the point of the geometric fibre of the terminal
  finite étale cover.
* `Stacks.FundamentalGroup.splitCoverFiberPoint`: the point of the geometric fibre of the split
  cover lying in a prescribed copy of the base.
* `Stacks.FundamentalGroup.splitCoverFiberEquiv`: the geometric fibre of the split cover is the
  index type.

## Main results

* `Stacks.FundamentalGroup.exists_splitCoverFiberPoint_eq`: every point of the geometric fibre of
  the split cover lies in one of the copies of the base.
* `Stacks.FundamentalGroup.smul_eq_self_splitCover`: **the étale fundamental group acts trivially
  on the geometric fibre of a split cover.**

## References

* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.FundamentalGroup

variable {X : Scheme.{u}} (x : GeometricPoint X) (ι : Type u) [Finite ι]

/-- The point of the geometric fibre of the terminal finite étale cover. -/
def topFiberPoint : (finiteEtaleFiberFunctor x).obj (fEtTop X) :=
  ⟨x.hom, Category.comp_id _⟩

/-- The point of the geometric fibre of the split cover lying in the `i`-th copy of the base. -/
def splitCoverFiberPoint (i : ι) : (finiteEtaleFiberFunctor x).obj (splitCover X ι) :=
  (finiteEtaleFiberFunctor x).map (splitCoverInj X ι i) (topFiberPoint x)

/-- The lift of `x` attached to a copy of the base is `x` followed by the inclusion of that
copy. -/
theorem splitCoverFiberPoint_val (i : ι) :
    (splitCoverFiberPoint x ι i).1 = x.hom ≫ Sigma.ι (fun _ : ι ↦ X) i :=
  rfl

/-- **Every point of the geometric fibre of the split cover lies in one of the copies of the
base.** The source of a geometric point has a single point, which lies in exactly one copy, and
the copies are open subschemes of the coproduct, so the lift factors through that copy. -/
theorem exists_splitCoverFiberPoint_eq
    (y : (finiteEtaleFiberFunctor x).obj (splitCover X ι)) :
    ∃ i, splitCoverFiberPoint x ι i = y := by
  have hsub : Subsingleton (x.source) :=
    inferInstance
  have hgen : ∀ q : (∐ fun _ : ι ↦ X : Scheme.{u}),
      ∃ (i : ι) (p : X), (Sigma.ι (fun _ : ι ↦ X) i).base p = q := by
    intro q
    obtain ⟨⟨i, p⟩, rfl⟩ := (AlgebraicGeometry.sigmaMk (fun _ : ι ↦ X)).surjective q
    exact ⟨i, p, (AlgebraicGeometry.sigmaMk_mk (fun _ : ι ↦ X) i p).symm⟩
  obtain ⟨i, p, hp⟩ := hgen (y.1.base default)
  have hrange : Set.range y.1.base ⊆ Set.range (Sigma.ι (fun _ : ι ↦ X) i).base := by
    rintro _ ⟨a, rfl⟩
    rw [hsub.allEq a default]
    exact ⟨p, hp⟩
  refine ⟨i, Subtype.ext ?_⟩
  have hlift := IsOpenImmersion.lift_fac (Sigma.ι (fun _ : ι ↦ X) i) y.1 hrange
  have h1 : IsOpenImmersion.lift (Sigma.ι (fun _ : ι ↦ X) i) y.1 hrange ≫ 𝟙 X = x.hom := by
    have e := (congrArg (fun k ↦ k ≫ Sigma.desc (fun _ : ι ↦ (𝟙 X : X ⟶ X))) hlift).trans y.2
    rwa [Category.assoc, Sigma.ι_comp_desc] at e
  have hx : IsOpenImmersion.lift (Sigma.ι (fun _ : ι ↦ X) i) y.1 hrange = x.hom :=
    (Category.comp_id _).symm.trans h1
  exact (congrArg (fun k ↦ k ≫ Sigma.ι (fun _ : ι ↦ X) i) hx).symm.trans hlift

/-- **The étale fundamental group acts trivially on the geometric fibre of a split cover.** Each
point of the fibre comes from the fibre of the terminal cover, on which the action is trivial
because that fibre has a single point. -/
theorem smul_eq_self_splitCover [ConnectedSpace X]
    (σ : EtaleFundamentalGroup X x) (y : (finiteEtaleFiberFunctor x).obj (splitCover X ι)) :
    σ • y = y := by
  obtain ⟨i, rfl⟩ := exists_splitCoverFiberPoint_eq x ι y
  have hnat := ConcreteCategory.congr_hom
    (σ.asIso.hom.naturality (splitCoverInj X ι i)) (topFiberPoint x)
  simp only [ConcreteCategory.comp_apply] at hnat
  have h1 : σ • splitCoverFiberPoint x ι i =
      (σ.asIso.hom.app (splitCover X ι)) (splitCoverFiberPoint x ι i) := rfl
  have h2 : (σ.asIso.hom.app (fEtTop X)) (topFiberPoint x) = topFiberPoint x :=
    (subsingleton_finiteEtaleFiber_finiteEtaleOverTerminal x).allEq _ _
  rw [h1, splitCoverFiberPoint, hnat, h2]

/-- **The geometric fibre of the split cover is the index type.** -/
def splitCoverFiberEquiv :
    (finiteEtaleFiberFunctor x).obj (splitCover X ι) ≃ ι := by
  classical
  refine Equiv.symm (Equiv.ofBijective (splitCoverFiberPoint x ι) ⟨fun i j hij ↦ ?_, ?_⟩)
  · by_contra hne
    have hcomm : CommSq x.hom x.hom (Sigma.ι (fun _ : ι ↦ X) i) (Sigma.ι (fun _ : ι ↦ X) j) :=
      ⟨congrArg Subtype.val hij⟩
    have hempty :=
      AlgebraicGeometry.isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : ι ↦ X) hcomm hne
    exact hempty.false (default : x.source)
  · exact fun y ↦ exists_splitCoverFiberPoint_eq x ι y

end Stacks.FundamentalGroup

end
