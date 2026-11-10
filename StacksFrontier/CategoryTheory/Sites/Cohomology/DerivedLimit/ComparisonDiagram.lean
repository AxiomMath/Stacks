module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.SheafificationOfTheCohomologyPresheaf
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison diagram of a derived inverse limit of cohomology on a ringed site

Let `(C, O)` be a ringed site, let `(Kₙ)` be an inverse system in the unbounded derived category
`D(O)` and let `L` be a derived limit of it, so that the structural map `p : L ⟶ ∏ Kₙ` sits in a
distinguished triangle whose second map is the difference map `(xₙ) ↦ (xₙ - fₙ₊₁(xₙ₊₁))`. Fix a
degree `m` and write `P` for the cohomology presheaf functor `K ↦ (U ↦ H^m(U, K))`, `H` for the
cohomology sheaf functor and `S` for sheafification.

The maps `p` followed by the product projections assemble into three comparison morphisms: one
into the limit of the cohomology presheaves, one into the limit of the cohomology sheaves, and
one out of the sheafification of the first limit into the second. The three fit into a
commuting square with the Tag 0BKV identification `S ∘ P ≅ H`.

The content is that the family `p ≫ πₙ` is a cone at all: that holds precisely because `p` is
the first map of the derived-limit triangle, so its composite with the difference map vanishes,
which says exactly that `p ≫ πₙ` is `p ≫ πₙ₊₁` followed by the transition map.

## Main results

* `Stacks.Cohomology.DerivedLimitDiagram.comp_π_eq_comp_π_succ`: the structural map of a derived
  limit followed by a product projection is compatible with the transition maps of the system.
* `Stacks.Cohomology.DerivedLimitDiagram.cohomologyDerivedLimitDiagram`: the three comparison
  maps and the square they form, which is the first of the two assertions of Tag 0BKW.

## Implementation notes

The three maps are existentially quantified but pinned down: each is required to have prescribed
composites with every limit projection, and a morphism into a limit is determined by those, so
the statement names a unique triple. The first two are the lifts of the cone `p ≫ πₙ`; the third
factors the sheafified limit of presheaves through the limit of the sheafified system, which is
where the Tag 0BKV identification enters, and is *not* asserted to be invertible — sheafification
does not in general commute with this inverse limit.

`IsGrothendieckAbelian` for the sheaves of modules appears as a hypothesis, with its own
universe, because Tag 0BKV's associated-sheaf isomorphism needs it to supply K-injective
resolutions. It is none of the source's business, and neither are the other four class
hypotheses: all five are theorems as soon as the module universe contains the site, which is
discharged in `ComparisonDiagramUnconditional.lean`, where the tag lives. The coefficient
universe of the abelian-group-valued sheafification is the structure-ring universe `w` of the
ringed site, since that is what `homotopySectionsPresheaf` is stated at.

The difference map is written out as the explicit `Pi.lift` of the tagged statement rather than
through `Stacks.DerivedLimit.inverseSystemDifference`; the two are the same term, and spelling
it out keeps the triangle appearing here the one the derived-limit hypothesis of Tag 0A09 names.

## References

* [Stacks Project, Tag 0BKW](https://stacks.math.columbia.edu/tag/0BKW)
* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry Stacks.Cohomology.SiteCohomologyPresheaf

namespace Stacks.Cohomology.DerivedLimitDiagram

universe u v w g

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The structural map of a derived limit is compatible with the transition maps of the system:
composing it with the `n`-th projection is the same as composing it with the `(n+1)`-st and
then restricting along `n ≤ n + 1`.

This is the cone condition, and it holds because the composite of the first two maps of a
distinguished triangle vanishes: the second map here is the difference map of the system. -/
theorem comp_π_eq_comp_π_succ
    {D : Type*} [Category* D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
    (K : ℕᵒᵖ ⥤ D) (L : D) [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈ distTriang D)
    (n : ℕ) :
    p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n =
      p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
        K.map (homOfLE (Nat.le_succ n)).op := by
  obtain ⟨δ, hδ⟩ := hp
  have hzero : p ≫ (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
          K.map (homOfLE (Nat.le_succ n)).op) = 0 :=
    comp_distTriang_mor_zero₁₂ _ hδ
  have h := congrArg (fun φ ↦ φ ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n) hzero
  simp only [Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub, zero_comp, sub_eq_zero] at h
  exact h

variable
  [IsGrothendieckAbelian.{g} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [(homotopySectionsPresheaf X).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (.up ℤ))]

/-- The canonical commuting square comparing cohomology before and after a derived inverse
limit, with the module universe of the ringed site left free. The comparison into the limit of
cohomology presheaves, the one into the limit of cohomology sheaves and the one out of the
sheafification of the former are each determined by their composites with the limit projections,
and the square they form with the Tag 0BKV associated-sheaf isomorphism commutes.

This is the square of [Stacks, Tag 0BKW], which is the first of the two assertions of that
remark; the second is the short exact sequence of [Stacks, Tag 0BKX] over each object of the
site. The tag is *not* registered here: it asserts both, and the five class hypotheses below are
not hypotheses of the source -- they are all theorems once the module universe contains the
site. The registration is on
`Stacks.Cohomology.DerivedLimitDiagram.cohomologyDerivedLimitDiagram_unconditional` in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedLimit/ComparisonDiagramUnconditional.lean`,
which carries both assertions at the module universe `max u v r w`, where all five are
discharged. -/
theorem cohomologyDerivedLimitDiagram (X : RingedSite.{u, v, w})
    [HasSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [IsGrothendieckAbelian.{g} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    [(homotopySectionsPresheaf X).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (.up ℤ))]
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang
          (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (m : ℤ) :
    let P := derivedSectionsPresheaf X ⋙
      DerivedCategory.homologyFunctor
        (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) m
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m
    let S := PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    let e := sheafificationCohomologyPresheafIso X m
    ∃ (a : P.obj L ⟶ limit (K ⋙ P))
      (b : H.obj L ⟶ limit (K ⋙ H))
      (c : S.obj (limit (K ⋙ P)) ⟶ limit (K ⋙ H)),
      (∀ n : ℕ,
        a ≫ limit.π (K ⋙ P) ⟨n⟩ =
          P.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) ∧
      (∀ n : ℕ,
        b ≫ limit.π (K ⋙ H) ⟨n⟩ =
          H.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) ∧
      (∀ n : ℕ,
        c ≫ limit.π (K ⋙ H) ⟨n⟩ =
          S.map (limit.π (K ⋙ P) ⟨n⟩) ≫ e.hom.app (K.obj ⟨n⟩)) ∧
      (S.map a ≫ c = e.hom.app L ≫ b) := by
  intro P H S e
  have hstep := comp_π_eq_comp_π_succ K L p hp
  -- The cone on `K` with vertex `L`, whose legs are `p ≫ πₙ`.
  let cK : Cone K := Cone.mk L
    (NatTrans.ofOpSequence (F := (Functor.const ℕᵒᵖ).obj L) (G := K)
      (fun n ↦ p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)
      (fun n ↦ by simpa using hstep n))
  -- Its images under the cohomology presheaf and cohomology sheaf functors.
  let cP : Cone (K ⋙ P) := P.mapCone cK
  let cH : Cone (K ⋙ H) := H.mapCone cK
  -- The third map factors the sheafified limit of presheaves through the limit of the
  -- sheafified system, then transports along the Tag 0BKV identification.
  let eK : (K ⋙ P) ⋙ S ≅ K ⋙ H := Functor.isoWhiskerLeft K e
  let a : P.obj L ⟶ limit (K ⋙ P) := limit.lift (K ⋙ P) cP
  let b : H.obj L ⟶ limit (K ⋙ H) := limit.lift (K ⋙ H) cH
  let c : S.obj (limit (K ⋙ P)) ⟶ limit (K ⋙ H) :=
    limit.lift ((K ⋙ P) ⋙ S) (S.mapCone (limit.cone (K ⋙ P))) ≫ (HasLimit.isoOfNatIso eK).hom
  have ha : ∀ n : ℕ, a ≫ limit.π (K ⋙ P) ⟨n⟩ =
      P.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n) := fun n ↦ limit.lift_π cP ⟨n⟩
  have hb : ∀ n : ℕ, b ≫ limit.π (K ⋙ H) ⟨n⟩ =
      H.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n) := fun n ↦ limit.lift_π cH ⟨n⟩
  have hc : ∀ n : ℕ, c ≫ limit.π (K ⋙ H) ⟨n⟩ =
      S.map (limit.π (K ⋙ P) ⟨n⟩) ≫ e.hom.app (K.obj ⟨n⟩) := by
    intro n
    change (limit.lift ((K ⋙ P) ⋙ S) (S.mapCone (limit.cone (K ⋙ P))) ≫
      (HasLimit.isoOfNatIso eK).hom) ≫ limit.π (K ⋙ H) ⟨n⟩ = _
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc, limit.lift_π]
    rfl
  refine ⟨a, b, c, ha, hb, hc, ?_⟩
  refine limit.hom_ext fun j ↦ ?_
  obtain ⟨n⟩ := j
  rw [Category.assoc, hc n, Category.assoc, hb n, ← Category.assoc, ← Functor.map_comp, ha n]
  exact e.hom.naturality (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)

end Stacks.Cohomology.DerivedLimitDiagram

end
