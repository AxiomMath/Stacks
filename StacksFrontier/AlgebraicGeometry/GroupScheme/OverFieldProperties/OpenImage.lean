module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Multiplication

/-!
# An open image of a homomorphism of group schemes over a field is closed

Let `ψ : G' ⟶ G` be a homomorphism of group schemes over a field.  If the image of `ψ` on
underlying topological spaces is open, then it is closed.

The argument is the one of the source.  Write `U` for the image and `Z` for its complement, and
let `T` be the reduced closed subscheme supported on `Z`.  Multiplying the `T`-family of
translations against `U` produces an open subset of `G`, by the openness of multiplication on a
group scheme over a field.  On the other hand that subset is exactly `Z`: a point of it lying in
`U` would make the fibre product of `T ⊗ G` against `ψ` nonempty over a point of `Z`, which the
group law forbids, and `Z` is contained in it because the identity section of `G` gives a section
of the multiplication map over `T`.  So `Z` is open and `U` is closed.

## Main results

* `AlgebraicGeometry.isClosed_range_of_isOpen`: an open image of a homomorphism of group schemes
  over a field is closed.

## Implementation notes

A group scheme over `k` is a group object in schemes over `Spec k`, and the image is the range of
the underlying continuous map.  The auxiliary fibre products used in the proof are formed in
`CategoryTheory.Over (Spec k)` from the fibre products of the underlying schemes, so that their
underlying schemes are literally those fibre products.

## References

* [Stacks Project, Tag 047S](https://stacks.math.columbia.edu/tag/047S)
-/

@[expose] public section

open CategoryTheory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

universe u

/-- The fibre product of two morphisms of schemes over `S`, as a scheme over `S`, formed from
the fibre product of the underlying schemes. -/
private noncomputable def overPullback {S : Scheme} {A B C : Over S}
    (f : A ⟶ C) (g : B ⟶ C) : Over S :=
  Over.mk (Limits.pullback.fst f.left g.left ≫ A.hom)

/-- The first projection of `overPullback`. -/
private noncomputable def overPullbackFst {S : Scheme} {A B C : Over S}
    (f : A ⟶ C) (g : B ⟶ C) : overPullback f g ⟶ A :=
  Over.homMk (Limits.pullback.fst f.left g.left)

/-- The second projection of `overPullback`. -/
private noncomputable def overPullbackSnd {S : Scheme} {A B C : Over S}
    (f : A ⟶ C) (g : B ⟶ C) : overPullback f g ⟶ B := by
  refine Over.homMk (Limits.pullback.snd f.left g.left) ?_
  change Limits.pullback.snd f.left g.left ≫ B.hom =
    Limits.pullback.fst f.left g.left ≫ A.hom
  rw [← Over.w g, ← Over.w f, ← Category.assoc, ← Category.assoc,
    Limits.pullback.condition]

private lemma overPullback_condition {S : Scheme} {A B C : Over S} (f : A ⟶ C) (g : B ⟶ C) :
    overPullbackFst f g ≫ f = overPullbackSnd f g ≫ g := by
  apply Over.OverMorphism.ext
  show Limits.pullback.fst f.left g.left ≫ f.left = Limits.pullback.snd f.left g.left ≫ g.left
  exact Limits.pullback.condition

private lemma range_overPullbackFst {S : Scheme} {A B C : Over S} (f : A ⟶ C) (g : B ⟶ C) :
    Set.range (overPullbackFst f g).left.base = f.left.base ⁻¹' Set.range g.left.base := by
  show Set.range (Limits.pullback.fst f.left g.left).base = _
  exact Scheme.Pullback.range_fst f.left g.left

/-- If `z` avoids the image of a homomorphism `ψ` of group schemes, so does the product of `z`
with any morphism factoring through `ψ`. -/
private theorem notMem_range_mul_comp {S : Scheme} {G' G : Grp (Over S)} (ψ : G' ⟶ G) {Q : Over S}
    (z : Q ⟶ G.X) (h : Q ⟶ G'.X) (hz : ∀ q, z.left.base q ∉ Set.range ψ.hom.hom.left.base)
    (q : Q.left) :
    (z * (h ≫ ψ.hom.hom)).left.base q ∉ Set.range ψ.hom.hom.left.base := by
  intro hq
  let rQ := overPullbackFst (z * (h ≫ ψ.hom.hom)) ψ.hom.hom
  let rH := overPullbackSnd (z * (h ≫ ψ.hom.hom)) ψ.hom.hom
  have hrRange : Set.range rQ.left.base =
      (z * (h ≫ ψ.hom.hom)).left.base ⁻¹' Set.range ψ.hom.hom.left.base :=
    range_overPullbackFst _ _
  have hpull : rQ ≫ (z * (h ≫ ψ.hom.hom)) = rH ≫ ψ.hom.hom := overPullback_condition _ _
  obtain ⟨r, -⟩ : q ∈ Set.range rQ.left.base := hrRange ▸ hq
  have hmul : (rQ ≫ z) * (rQ ≫ h ≫ ψ.hom.hom) = rH ≫ ψ.hom.hom := by
    simpa [MonObj.comp_mul] using hpull
  have hsolve : rQ ≫ z = (rH ≫ ψ.hom.hom) / (rQ ≫ h ≫ ψ.hom.hom) := by
    rw [← hmul]
    simp
  have hfactor : rQ ≫ z = (rH / (rQ ≫ h)) ≫ ψ.hom.hom := by
    rw [hsolve]
    show (rH ≫ ψ.hom.hom) / ((rQ ≫ h) ≫ ψ.hom.hom) = _
    rw [← GrpObj.div_comp]
  have hin : (rQ ≫ z).left.base r ∈ Set.range ψ.hom.hom.left.base := by
    rw [hfactor]
    exact ⟨(rH / (rQ ≫ h)).left.base r, rfl⟩
  exact hz (rQ.left.base r) hin

private lemma range_subset_range_overPullbackFst_comp_mul {S : Scheme} {G' G : Grp (Over S)}
    (ψ : G' ⟶ G) {T : Over S} (inc : T ⟶ G.X) :
    Set.range inc.left.base ⊆ Set.range (overPullbackFst (snd T G.X) ψ.hom.hom ≫
      lift (fst T G.X ≫ inc) (snd T G.X) ≫ μ[G.X]).left.base := by
  let sectionP : T ⟶ T ⊗ G.X := lift (𝟙 T) (toUnit T ≫ η[G.X])
  let sectionH : T ⟶ G'.X := toUnit T ≫ η[G'.X]
  have hsection : sectionP ≫ snd T G.X = sectionH ≫ ψ.hom.hom := by
    apply Over.OverMorphism.ext
    simp [sectionP, sectionH, IsMonHom.one_hom, Category.assoc]
  let sectionQ : T ⟶ overPullback (snd T G.X) ψ.hom.hom := Over.homMk
    (Limits.pullback.lift sectionP.left sectionH.left (congrArg Over.Hom.left hsection)) (by
      show (Limits.pullback.lift sectionP.left sectionH.left
            (congrArg Over.Hom.left hsection) ≫
          Limits.pullback.fst (snd T G.X).left ψ.hom.hom.left) ≫ (T ⊗ G.X).hom = T.hom
      rw [Limits.pullback.lift_fst]
      exact Over.w sectionP)
  have hsectionQ : sectionQ ≫ overPullbackFst (snd T G.X) ψ.hom.hom = sectionP := by
    apply Over.OverMorphism.ext
    show Limits.pullback.lift sectionP.left sectionH.left _ ≫
        Limits.pullback.fst (snd T G.X).left ψ.hom.hom.left = sectionP.left
    exact Limits.pullback.lift_fst _ _ _
  have hsectionM : sectionP ≫ lift (fst T G.X ≫ inc) (snd T G.X) ≫ μ[G.X] = inc := by
    rw [← Category.assoc, CartesianMonoidalCategory.comp_lift, ← CategoryTheory.Hom.mul_def]
    simp [sectionP, CategoryTheory.Hom.one_def]
  have hsectionB : sectionQ ≫ overPullbackFst (snd T G.X) ψ.hom.hom ≫
      lift (fst T G.X ≫ inc) (snd T G.X) ≫ μ[G.X] = inc := by
    rw [← Category.assoc, hsectionQ, hsectionM]
  rintro _ ⟨t, rfl⟩
  exact ⟨sectionQ.left.base t, congrArg (fun f => f.left.base t) hsectionB⟩

/-- **Stacks Project, Tag 047S.** An open image of a homomorphism of group schemes over a
field is closed. -/
@[stacks 047S]
theorem isClosed_range_of_isOpen {k : Type u} [Field k]
    {G' G : Grp (Over (Spec (.of k)))} (ψ : G' ⟶ G)
    (hopen : IsOpen (Set.range ψ.hom.hom.left.base)) :
    IsClosed (Set.range ψ.hom.hom.left.base) := by
  let U : G.X.left.Opens := ⟨Set.range ψ.hom.hom.left.base, hopen⟩
  let Z : TopologicalSpace.Closeds G.X.left :=
    ⟨(Set.range ψ.hom.hom.left.base)ᶜ, hopen.isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let T : Over (Spec (.of k)) := Over.mk (I.subschemeι ≫ G.X.hom)
  let inc : T ⟶ G.X := Over.homMk I.subschemeι
  let m : T ⊗ G.X ⟶ G.X := lift (fst T G.X ≫ inc) (snd T G.X) ≫ μ[G.X]
  let qP := overPullbackFst (snd T G.X) ψ.hom.hom
  let qH := overPullbackSnd (snd T G.X) ψ.hom.hom
  let b := qP ≫ m
  have hqRange : Set.range qP.left.base =
      (snd T G.X).left.base ⁻¹' Set.range ψ.hom.hom.left.base :=
    range_overPullbackFst (snd T G.X) ψ.hom.hom
  have hproj : qP ≫ snd T G.X = qH ≫ ψ.hom.hom := overPullback_condition _ _
  have hb : b = (qP ≫ fst T G.X ≫ inc) * (qH ≫ ψ.hom.hom) := by
    dsimp [b, m]
    rw [← Category.assoc, CartesianMonoidalCategory.comp_lift, hproj]
    rfl
  have hrangeInc : Set.range inc.left.base = (Z : Set G.X.left) := by
    show Set.range I.subschemeι.base = (Z : Set G.X.left)
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  have hz : ∀ q, (qP ≫ fst T G.X ≫ inc).left.base q ∉ Set.range ψ.hom.hom.left.base := by
    intro q
    have hZ : (qP ≫ fst T G.X ≫ inc).left.base q ∈ (Z : Set G.X.left) := by
      rw [← hrangeInc]
      exact ⟨(qP ≫ fst T G.X).left.base q, rfl⟩
    simpa [Z] using hZ
  have hbRangeSub : Set.range b.left.base ⊆ (Z : Set G.X.left) := by
    rintro _ ⟨q, rfl⟩
    rw [hb]
    simpa [Z] using notMem_range_mul_comp ψ _ qH hz q
  have hbRangeEq : Set.range b.left.base = (Z : Set G.X.left) :=
    hbRangeSub.antisymm (hrangeInc.symm.subset.trans
      (range_subset_range_overPullbackFst_comp_mul ψ inc))
  have hcomp : b.left.base = m.left.base ∘ qP.left.base := by
    simp [b, Over.comp_left, Scheme.Hom.comp_base]
  have hopenZ : IsOpen (Z : Set G.X.left) := by
    rw [← hbRangeEq, hcomp, Set.range_comp, hqRange]
    exact isOpen_image_mul_of_open G.X T inc U
  simpa [Z] using hopenZ.isClosed_compl

end AlgebraicGeometry

end
