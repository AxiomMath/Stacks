module

public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationsOverSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPartRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence

/-!
# The relation glued from a diagonal and an open part of a fibre square

Let `S` be a scheme contained in a big fppf site `B`, let `fA : A ⟶ X` be a morphism of
presheaves on the big fppf site of `S` and let `W` be a subfunctor of `X`. Inside the fibre square
`A ×_X A` consider the two pieces

* the diagonal `Δ_A`, the pairs `(a, b)` with `a = b`, and
* the part over `W`, the pairs `(a, b)` whose common image in `X` lies in `W`.

Their union is not a sheaf, but its fppf sheafification inside `A ×_X A` is. This is the relation
of the proof of Stacks 0AR9: for `W` the open subspace `X ∖ T` and `A ⟶ X` étale over `W`, it is
the pushout `R = A ⨿_{A_W} (A_W ×_W A_W)` of the source, glued along the open immersion
`A_W ⟶ A_W ×_W A_W`, realized as a subsheaf of `A ×_X A`.

## Main definitions

* `AlgebraicGeometry.Space.gluedDiagonalRelation₀`: the union of the two pieces, a subfunctor of
  `A ×_X A`.
* `AlgebraicGeometry.Space.gluedDiagonalRelation`: its fppf sheafification.
* `AlgebraicGeometry.Space.gluedRelation`: the resulting pre-relation on `A` over `X` in the
  sense of Stacks 043C.

## Main results

* `AlgebraicGeometry.Space.isSheaf_gluedDiagonalRelation`: the relation is an fppf sheaf when
  `A` and `X` are.
* `AlgebraicGeometry.Space.isEquivalenceRelation_gluedRelation`: the pre-relation is an
  equivalence relation.

## References

* [Stacks Project, Tag 0AR9](https://stacks.math.columbia.edu/tag/0AR9)
* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (fA : A ⟶ X) (W : Subfunctor X)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site is heavy
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_GluedDiagonalRelation :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site, found directly. -/
local instance (priority := high) hasPullback_presheaf_GluedDiagonalRelation
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for discrete limits of presheaves on the big fppf site is heavy
/-- Discrete limits of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasLimitsOfShape_discrete_presheaf_GluedDiagonalRelation (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-! ### The relation -/

/-- The union of the diagonal of `A ×_X A` and of its part lying over `W`: the sections of the
fibre square whose two components agree or whose common image in `X` lies in `W`. -/
def gluedDiagonalRelation₀ : Subfunctor (pullback fA fA) where
  obj V := {x | (pullback.fst fA fA).app V x = (pullback.snd fA fA).app V x ∨
      fA.app V ((pullback.fst fA fA).app V x) ∈ W.obj V}
  map {V V'} i x hx := by
    change (pullback.fst fA fA).app V' ((pullback fA fA).map i x) =
        (pullback.snd fA fA).app V' ((pullback fA fA).map i x) ∨
      fA.app V' ((pullback.fst fA fA).app V' ((pullback fA fA).map i x)) ∈ W.obj V'
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, NatTrans.naturality_apply]
    rcases hx with h | h
    · exact Or.inl (congrArg (A.map i) h)
    · exact Or.inr (W.map i h)

/-- The relation of the proof of Stacks 0AR9: the fppf sheafification, inside `A ×_X A`, of the
union of the diagonal and of the part of `A ×_X A` lying over `W`. -/
def gluedDiagonalRelation : Subfunctor (pullback fA fA) :=
  (gluedDiagonalRelation₀ fA W).sheafify (BigFppfOver.topology B S hS)

/-- The union of the diagonal and of the part over `W` is contained in the relation. -/
theorem gluedDiagonalRelation₀_le :
    gluedDiagonalRelation₀ fA W ≤ gluedDiagonalRelation fA W :=
  Subfunctor.le_sheafify _ _

/-- A section of the fibre square with equal components lies in the relation. -/
theorem mem_gluedDiagonalRelation_of_fst_eq_snd {V : (BigFppfOver B S hS)ᵒᵖ}
    {x : (pullback fA fA).obj V}
    (h : (pullback.fst fA fA).app V x = (pullback.snd fA fA).app V x) :
    x ∈ (gluedDiagonalRelation fA W).obj V :=
  gluedDiagonalRelation₀_le fA W V (Or.inl h)

/-- A section of the fibre square lying over `W` lies in the relation. -/
theorem mem_gluedDiagonalRelation_of_mem {V : (BigFppfOver B S hS)ᵒᵖ}
    {x : (pullback fA fA).obj V}
    (h : fA.app V ((pullback.fst fA fA).app V x) ∈ W.obj V) :
    x ∈ (gluedDiagonalRelation fA W).obj V :=
  gluedDiagonalRelation₀_le fA W V (Or.inr h)

/-- The relation is an fppf sheaf when `A` and `X` are. -/
theorem isSheaf_gluedDiagonalRelation
    (hA : Presheaf.IsSheaf (BigFppfOver.topology B S hS) A)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (gluedDiagonalRelation fA W).toFunctor := by
  have hP := Presheaf.isSheaf_pullback _ fA fA hA hA hX
  rw [isSheaf_iff_isSheaf_of_type] at hP ⊢
  exact Subfunctor.sheafify_isSheaf _ hP

/-! ### Closure properties of the relation on sections -/

/-- The generating subfunctor is closed under transitivity, on sections. -/
private theorem gluedDiagonalRelation₀_trans {V : (BigFppfOver B S hS)ᵒᵖ}
    {x y z : (pullback fA fA).obj V}
    (hxy : (pullback.snd fA fA).app V x = (pullback.fst fA fA).app V y)
    (hzx : (pullback.fst fA fA).app V z = (pullback.fst fA fA).app V x)
    (hzy : (pullback.snd fA fA).app V z = (pullback.snd fA fA).app V y)
    (hx : x ∈ (gluedDiagonalRelation₀ fA W).obj V)
    (hy : y ∈ (gluedDiagonalRelation₀ fA W).obj V) :
    z ∈ (gluedDiagonalRelation₀ fA W).obj V := by
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · exact Or.inl (by rw [hzx, hzy, hx, hxy, hy])
    · exact Or.inr (by rw [hzx, hx, hxy]; exact hy)
  · exact Or.inr (by rw [hzx]; exact hx)

/-- The generating subfunctor is closed under symmetry, on sections. -/
private theorem gluedDiagonalRelation₀_symm {V : (BigFppfOver B S hS)ᵒᵖ}
    {x y : (pullback fA fA).obj V}
    (h₁ : (pullback.fst fA fA).app V y = (pullback.snd fA fA).app V x)
    (h₂ : (pullback.snd fA fA).app V y = (pullback.fst fA fA).app V x)
    (hx : x ∈ (gluedDiagonalRelation₀ fA W).obj V) :
    y ∈ (gluedDiagonalRelation₀ fA W).obj V := by
  rcases hx with hx | hx
  · exact Or.inl (by rw [h₁, h₂, hx])
  · refine Or.inr ?_
    have hc : fA.app V ((pullback.fst fA fA).app V x) =
        fA.app V ((pullback.snd fA fA).app V x) := by
      simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using
        congrArg (fun k => k.app V x) (pullback.condition (f := fA) (g := fA))
    rw [h₁, ← hc]
    exact hx

/-- The relation is closed under transitivity, on sections. -/
theorem gluedDiagonalRelation_trans {V : (BigFppfOver B S hS)ᵒᵖ}
    {x y z : (pullback fA fA).obj V}
    (hxy : (pullback.snd fA fA).app V x = (pullback.fst fA fA).app V y)
    (hzx : (pullback.fst fA fA).app V z = (pullback.fst fA fA).app V x)
    (hzy : (pullback.snd fA fA).app V z = (pullback.snd fA fA).app V y)
    (hx : x ∈ (gluedDiagonalRelation fA W).obj V)
    (hy : y ∈ (gluedDiagonalRelation fA W).obj V) :
    z ∈ (gluedDiagonalRelation fA W).obj V := by
  change _ ∈ BigFppfOver.topology B S hS V.unop
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    ((BigFppfOver.topology B S hS).intersection_covering hx hy)
  rintro V' q ⟨hqx, hqy⟩
  change (pullback fA fA).map q.op z ∈ (gluedDiagonalRelation₀ fA W).obj (op V')
  refine gluedDiagonalRelation₀_trans fA W ?_ ?_ ?_ hqx hqy
  · rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
  · rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hzx]
  · rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hzy]

/-- The relation is closed under symmetry, on sections. -/
theorem gluedDiagonalRelation_symm {V : (BigFppfOver B S hS)ᵒᵖ}
    {x y : (pullback fA fA).obj V}
    (h₁ : (pullback.fst fA fA).app V y = (pullback.snd fA fA).app V x)
    (h₂ : (pullback.snd fA fA).app V y = (pullback.fst fA fA).app V x)
    (hx : x ∈ (gluedDiagonalRelation fA W).obj V) :
    y ∈ (gluedDiagonalRelation fA W).obj V := by
  change _ ∈ BigFppfOver.topology B S hS V.unop
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hx
  intro V' q hq
  change (pullback fA fA).map q.op y ∈ (gluedDiagonalRelation₀ fA W).obj (op V')
  refine gluedDiagonalRelation₀_symm fA W ?_ ?_ hq
  · rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h₁]
  · rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h₂]

/-! ### The pre-relation -/

/-- The object `A` of the relation, in the slice over `X`. -/
abbrev gluedObject : Over X := Over.mk fA

/-- The arrows of the relation, in the slice over `X`. -/
abbrev gluedArrows : Over X :=
  Over.mk ((gluedDiagonalRelation fA W).ι ≫ pullback.fst fA fA ≫ fA)

/-- The target map of the relation: the first projection. -/
def gluedTarget : gluedArrows fA W ⟶ gluedObject fA :=
  Over.homMk ((gluedDiagonalRelation fA W).ι ≫ pullback.fst fA fA) (by simp)

/-- The source map of the relation: the second projection. -/
def gluedSource : gluedArrows fA W ⟶ gluedObject fA :=
  Over.homMk ((gluedDiagonalRelation fA W).ι ≫ pullback.snd fA fA) (by
    simp [pullback.condition])

/-- **The relation of the proof of Stacks 0AR9**, as a pre-relation on `A` over `X` in the sense
of Stacks 043C. -/
def gluedRelation : PreRelation (gluedArrows fA W) (gluedObject fA) :=
  prod.lift (gluedTarget fA W) (gluedSource fA W)

/-- The target map of `gluedRelation` is `gluedTarget`. -/
theorem gluedRelation_target : (gluedRelation fA W).target = gluedTarget fA W :=
  prod.lift_fst _ _

/-- The source map of `gluedRelation` is `gluedSource`. -/
theorem gluedRelation_source : (gluedRelation fA W).source = gluedSource fA W :=
  prod.lift_snd _ _

/-- The target map of `gluedRelation` is the first projection on the relation. -/
theorem gluedRelation_target_left :
    (gluedRelation fA W).target.left = (gluedDiagonalRelation fA W).ι ≫ pullback.fst fA fA :=
  congrArg CommaMorphism.left (gluedRelation_target fA W)

/-- The source map of `gluedRelation` is the second projection on the relation. -/
theorem gluedRelation_source_left :
    (gluedRelation fA W).source.left = (gluedDiagonalRelation fA W).ι ≫ pullback.snd fA fA :=
  congrArg CommaMorphism.left (gluedRelation_source fA W)

/-- The pre-relation is a monomorphism: a section of the relation is determined by its two
components. -/
instance mono_gluedRelation : Mono (gluedRelation fA W) where
  right_cancellation {Z} g₁ g₂ h := by
    have ht := congrArg (fun k => k ≫ prod.fst) h
    have hs := congrArg (fun k => k ≫ prod.snd) h
    simp only [Category.assoc] at ht hs
    change g₁ ≫ (gluedRelation fA W).target = g₂ ≫ (gluedRelation fA W).target at ht
    change g₁ ≫ (gluedRelation fA W).source = g₂ ≫ (gluedRelation fA W).source at hs
    rw [gluedRelation_target] at ht
    rw [gluedRelation_source] at hs
    have ht' := congrArg CommaMorphism.left ht
    have hs' := congrArg CommaMorphism.left hs
    simp only [Over.comp_left, gluedTarget, gluedSource, Over.homMk_left] at ht' hs'
    apply Over.OverMorphism.ext
    rw [← cancel_mono (gluedDiagonalRelation fA W).ι]
    apply pullback.hom_ext
    · simpa only [Category.assoc] using ht'
    · simpa only [Category.assoc] using hs'

/-- The section of the fibre square defined by two test points of `A` over the same test point
of `X`. -/
def gluedPair {T : BigFppfOver B S hS} {b : yoneda.obj T ⟶ X}
    (x y : TestPoint T b (gluedObject fA)) : yoneda.obj T ⟶ pullback fA fA :=
  pullback.lift (f := fA) (g := fA) x.1 y.1 (x.2.trans y.2.symm)

/-- The first component of `gluedPair fA x y` is `x`. -/
@[simp]
theorem gluedPair_fst {T : BigFppfOver B S hS} {b : yoneda.obj T ⟶ X}
    (x y : TestPoint T b (gluedObject fA)) : gluedPair fA x y ≫ pullback.fst fA fA = x.1 :=
  pullback.lift_fst _ _ _

/-- The second component of `gluedPair fA x y` is `y`. -/
@[simp]
theorem gluedPair_snd {T : BigFppfOver B S hS} {b : yoneda.obj T ⟶ X}
    (x y : TestPoint T b (gluedObject fA)) : gluedPair fA x y ≫ pullback.snd fA fA = y.1 :=
  pullback.lift_snd _ _ _

/-- The relation induced on test points: two test points are related exactly when the section of
the fibre square they define lies in the relation. -/
theorem gluedRelation_rel_iff {T : BigFppfOver B S hS} {b : yoneda.obj T ⟶ X}
    (x y : TestPoint T b (gluedObject fA)) :
    (gluedRelation fA W).Rel b x y ↔
      yonedaEquiv (gluedPair fA x y) ∈ (gluedDiagonalRelation fA W).obj (op T) := by
  constructor
  · rintro ⟨r, hrt, hrs⟩
    rw [gluedRelation_target_left] at hrt
    rw [gluedRelation_source_left] at hrs
    have hl : r.1 ≫ (gluedDiagonalRelation fA W).ι = gluedPair fA x y := by
      apply pullback.hom_ext
      · simpa only [Category.assoc, gluedPair_fst] using hrt
      · simpa only [Category.assoc, gluedPair_snd] using hrs
    rw [← hl, yonedaEquiv_comp]
    exact (yonedaEquiv r.1).2
  · intro h
    let r : yoneda.obj T ⟶ (gluedDiagonalRelation fA W).toFunctor := yonedaEquiv.symm ⟨_, h⟩
    have hr : r ≫ (gluedDiagonalRelation fA W).ι = gluedPair fA x y := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, show yonedaEquiv r = ⟨_, h⟩ from yonedaEquiv.apply_symm_apply _]
      rfl
    refine ⟨⟨r, ?_⟩, ?_, ?_⟩
    · change r ≫ (gluedDiagonalRelation fA W).ι ≫ pullback.fst fA fA ≫ fA = b
      rw [← Category.assoc, hr, ← Category.assoc, gluedPair_fst]
      exact x.2
    · rw [gluedRelation_target_left, ← Category.assoc, hr, gluedPair_fst]
    · rw [gluedRelation_source_left, ← Category.assoc, hr, gluedPair_snd]

/-- **The relation of the proof of Stacks 0AR9 is an equivalence relation.** -/
theorem isEquivalenceRelation_gluedRelation :
    IsEquivalenceRelation (gluedRelation fA W).target (gluedRelation fA W).source := by
  rw [isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation]
  refine ⟨inferInstance, fun T b => ⟨fun x => ?_, fun {x y} h => ?_, fun {x y z} h₁ h₂ => ?_⟩⟩
  · rw [gluedRelation_rel_iff]
    apply mem_gluedDiagonalRelation_of_fst_eq_snd
    rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, gluedPair_fst, gluedPair_snd]
  · rw [gluedRelation_rel_iff] at h ⊢
    refine gluedDiagonalRelation_symm fA W ?_ ?_ h <;>
      rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, gluedPair_fst, gluedPair_snd]
  · rw [gluedRelation_rel_iff] at h₁ h₂ ⊢
    refine gluedDiagonalRelation_trans fA W ?_ ?_ ?_ h₁ h₂
    · rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, gluedPair_snd, gluedPair_fst]
    · rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, gluedPair_fst, gluedPair_fst]
    · rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, gluedPair_snd, gluedPair_snd]


/-- The first projection of the fibre square undoes the diagonal, on sections. -/
private theorem diagonal_app_fst {V : (BigFppfOver B S hS)ᵒᵖ} (a : A.obj V) :
    (pullback.fst fA fA).app V ((pullback.diagonal fA).app V a) = a := by
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply, NatTrans.id_app,
    ConcreteCategory.id_apply] using
    congrArg (fun k => k.app V a) (pullback.diagonal_fst fA)

/-- The second projection of the fibre square undoes the diagonal, on sections. -/
private theorem diagonal_app_snd {V : (BigFppfOver B S hS)ᵒᵖ} (a : A.obj V) :
    (pullback.snd fA fA).app V ((pullback.diagonal fA).app V a) = a := by
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply, NatTrans.id_app,
    ConcreteCategory.id_apply] using
    congrArg (fun k => k.app V a) (pullback.diagonal_snd fA)

/-- A section of the fibre square with equal components is the diagonal of its component. -/
private theorem diagonal_app_fst_of_fst_eq_snd {V : (BigFppfOver B S hS)ᵒᵖ}
    {x : (pullback fA fA).obj V}
    (h : (pullback.fst fA fA).app V x = (pullback.snd fA fA).app V x) :
    (pullback.diagonal fA).app V ((pullback.fst fA fA).app V x) = x :=
  Types.ext_of_isPullback ((IsPullback.of_hasPullback fA fA).map ((evaluation _ _).obj V))
    (diagonal_app_fst fA _) ((diagonal_app_snd fA _).trans h)

/-! ### The two pieces and the maps between them -/

/-- The part of the fibre square `A ×_X A` lying over `W`. -/
abbrev gluedOverPart : Subfunctor (pullback fA fA) := W.preimage (pullback.fst fA fA ≫ fA)

/-- The part of the fibre square over `W` is contained in the relation. -/
theorem gluedOverPart_le : gluedOverPart fA W ≤ gluedDiagonalRelation fA W :=
  fun _ _ hx => mem_gluedDiagonalRelation_of_mem fA W hx

/-- The part of `A` lying over `W`. -/
abbrev gluedSourcePart : Subfunctor A := W.preimage fA

/-- The two components of a section of `A ×_X A` have the same image in `X`. -/
theorem gluedPair_app_condition {V : (BigFppfOver B S hS)ᵒᵖ} (x : (pullback fA fA).obj V) :
    fA.app V ((pullback.fst fA fA).app V x) = fA.app V ((pullback.snd fA fA).app V x) := by
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using
    congrArg (fun k => k.app V x) (pullback.condition (f := fA) (g := fA))

/-- The diagonal, as a morphism into the relation. -/
def gluedDiag : A ⟶ (gluedDiagonalRelation fA W).toFunctor :=
  Subfunctor.lift (pullback.diagonal fA) (by
    rintro V _ ⟨a, rfl⟩
    apply mem_gluedDiagonalRelation_of_fst_eq_snd
    have h₁ := congrArg (fun k => k.app V a) (pullback.diagonal_fst fA)
    have h₂ := congrArg (fun k => k.app V a) (pullback.diagonal_snd fA)
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h₁ h₂
    exact h₁.trans h₂.symm)

/-- The composite of `gluedDiag` with the inclusion of the relation is the diagonal of `A`. -/
@[reassoc (attr := simp)]
theorem gluedDiag_ι : gluedDiag fA W ≫ (gluedDiagonalRelation fA W).ι = pullback.diagonal fA :=
  rfl

/-- The inclusion of the part over `W` into the relation. -/
def gluedOverIncl : (gluedOverPart fA W).toFunctor ⟶ (gluedDiagonalRelation fA W).toFunctor :=
  Subfunctor.homOfLe (gluedOverPart_le fA W)

/-- The composite of `gluedOverIncl` with the inclusion of the relation is the inclusion of the
part over `W`. -/
@[reassoc (attr := simp)]
theorem gluedOverIncl_ι :
    gluedOverIncl fA W ≫ (gluedDiagonalRelation fA W).ι = (gluedOverPart fA W).ι :=
  rfl

/-- The first projection from the part over `W` to the part of `A` over `W`. -/
def gluedOverFst : (gluedOverPart fA W).toFunctor ⟶ (gluedSourcePart fA W).toFunctor :=
  Subfunctor.lift ((gluedOverPart fA W).ι ≫ pullback.fst fA fA) (by
    rintro V _ ⟨x, rfl⟩
    exact x.2)

/-- The second projection from the part over `W` to the part of `A` over `W`. -/
def gluedOverSnd : (gluedOverPart fA W).toFunctor ⟶ (gluedSourcePart fA W).toFunctor :=
  Subfunctor.lift ((gluedOverPart fA W).ι ≫ pullback.snd fA fA) (by
    rintro V _ ⟨x, rfl⟩
    change fA.app V ((pullback.snd fA fA).app V x.1) ∈ W.obj V
    rw [← gluedPair_app_condition]
    exact x.2)

/-- The composite of `gluedOverFst` with the inclusion of the part of `A` over `W` is the first
projection. -/
@[reassoc (attr := simp)]
theorem gluedOverFst_ι : gluedOverFst fA W ≫ (gluedSourcePart fA W).ι =
    (gluedOverPart fA W).ι ≫ pullback.fst fA fA :=
  rfl

/-- The composite of `gluedOverSnd` with the inclusion of the part of `A` over `W` is the second
projection. -/
@[reassoc (attr := simp)]
theorem gluedOverSnd_ι : gluedOverSnd fA W ≫ (gluedSourcePart fA W).ι =
    (gluedOverPart fA W).ι ≫ pullback.snd fA fA :=
  rfl

/-- The diagonal of the part of `A` over `W`, landing in the part of `A ×_X A` over `W`. -/
def gluedOverDiag : (gluedSourcePart fA W).toFunctor ⟶ (gluedOverPart fA W).toFunctor :=
  Subfunctor.lift ((gluedSourcePart fA W).ι ≫ pullback.diagonal fA) (by
    rintro V _ ⟨a, rfl⟩
    change fA.app V ((pullback.fst fA fA).app V
      ((pullback.diagonal fA).app V a.1)) ∈ W.obj V
    have h₁ := congrArg (fun k => k.app V a.1) (pullback.diagonal_fst fA)
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h₁
    rw [h₁]
    exact a.2)

/-- The composite of `gluedOverDiag` with the inclusion of the part over `W` is the diagonal of
`A` restricted to the part of `A` over `W`. -/
@[reassoc (attr := simp)]
theorem gluedOverDiag_ι : gluedOverDiag fA W ≫ (gluedOverPart fA W).ι =
    (gluedSourcePart fA W).ι ≫ pullback.diagonal fA :=
  rfl

/-- `gluedOverDiag` is a section of `gluedOverFst`. -/
@[reassoc (attr := simp)]
theorem gluedOverDiag_fst : gluedOverDiag fA W ≫ gluedOverFst fA W = 𝟙 _ := by
  rw [← cancel_mono (gluedSourcePart fA W).ι]
  simp

/-- `gluedOverDiag` is a section of `gluedOverSnd`. -/
@[reassoc (attr := simp)]
theorem gluedOverDiag_snd : gluedOverDiag fA W ≫ gluedOverSnd fA W = 𝟙 _ := by
  rw [← cancel_mono (gluedSourcePart fA W).ι]
  simp

/-- The part of `A ×_X A` over `W` is the fibre square of the part of `A` over `W` over `W`. -/
theorem isPullback_gluedOverFst_gluedOverSnd :
    IsPullback (gluedOverFst fA W) (gluedOverSnd fA W) (W.fromPreimage fA)
      (W.fromPreimage fA) := by
  have hw : gluedOverFst fA W ≫ W.fromPreimage fA = gluedOverSnd fA W ≫ W.fromPreimage fA := by
    rw [← cancel_mono W.ι]
    simp only [Category.assoc, Subfunctor.fromPreimage_ι, gluedOverFst_ι_assoc,
      gluedOverSnd_ι_assoc, pullback.condition]
  refine IsPullback.of_forall_isPullback_app fun V => ?_
  rw [Types.isPullback_iff]
  refine ⟨congrArg (fun k => k.app V) hw, fun x y ⟨h₁, h₂⟩ => ?_, fun a b hab => ?_⟩
  · apply Subtype.ext
    exact Types.ext_of_isPullback ((IsPullback.of_hasPullback fA fA).map
      ((evaluation _ _).obj V)) (congrArg Subtype.val h₁) (congrArg Subtype.val h₂)
  · obtain ⟨x, hx₁, hx₂⟩ := Types.exists_of_isPullback ((IsPullback.of_hasPullback fA fA).map
      ((evaluation _ _).obj V)) a.1 b.1 (congrArg Subtype.val hab)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx₁, Subtype.ext hx₂⟩
    change fA.app V ((pullback.fst fA fA).app V x) ∈ W.obj V
    rw [show (pullback.fst fA fA).app V x = a.1 from hx₁]
    exact a.2

/-- The diagonal of `A` meets the part of `A ×_X A` over `W` exactly in the part of `A` over
`W`, on which it is the diagonal of that part. -/
theorem isPullback_gluedDiag_gluedOverIncl :
    IsPullback (gluedSourcePart fA W).ι (gluedOverDiag fA W) (gluedDiag fA W)
      (gluedOverIncl fA W) := by
  have hw : (gluedSourcePart fA W).ι ≫ gluedDiag fA W =
      gluedOverDiag fA W ≫ gluedOverIncl fA W := by
    rw [← cancel_mono (gluedDiagonalRelation fA W).ι]
    simp
  refine IsPullback.of_forall_isPullback_app fun V => ?_
  rw [Types.isPullback_iff]
  refine ⟨congrArg (fun k => k.app V) hw, fun x y h => Subtype.ext h.1, fun a v hav => ?_⟩
  have hav' : (pullback.diagonal fA).app V a = v.1 := congrArg Subtype.val hav
  have h₁ := diagonal_app_fst fA a
  have ha : a ∈ (gluedSourcePart fA W).obj V := by
    have hv := v.2
    change fA.app V ((pullback.fst fA fA).app V v.1) ∈ W.obj V at hv
    rwa [← hav', h₁] at hv
  exact ⟨⟨a, ha⟩, rfl, Subtype.ext hav'⟩

/-! ### Local surjectivity onto the relation -/

/-- A morphism to the relation is locally surjective as soon as every section of the diagonal
and every section of the part over `W` lifts along it: every section of the relation lies,
locally, in one of the two pieces. -/
theorem isLocallySurjective_to_gluedDiagonalRelation {K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (ψ : K ⟶ (gluedDiagonalRelation fA W).toFunctor)
    (hΔ : ∀ V (a : A.obj V), ∃ x, ψ.app V x = (gluedDiag fA W).app V a)
    (hW : ∀ V (v : (gluedOverPart fA W).toFunctor.obj V), ∃ x,
      ψ.app V x = (gluedOverIncl fA W).app V v) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) ψ where
  imageSieve_mem {V} r := by
    refine (BigFppfOver.topology B S hS).superset_covering ?_ r.2
    intro V' q hq
    have hq' : (pullback fA fA).map q.op r.1 ∈ (gluedDiagonalRelation₀ fA W).obj (op V') := hq
    rcases hq' with h | h
    · obtain ⟨x, hx⟩ := hΔ (op V')
        ((pullback.fst fA fA).app (op V') ((pullback fA fA).map q.op r.1))
      exact ⟨x, hx.trans (Subtype.ext (diagonal_app_fst_of_fst_eq_snd fA h))⟩
    · obtain ⟨x, hx⟩ := hW (op V') ⟨(pullback fA fA).map q.op r.1, h⟩
      exact ⟨x, hx.trans (Subtype.ext rfl)⟩


/-! ### Étaleness out of a space covered by two open pieces -/

section TwoOpens

variable (B S hS) in
/-- **Étaleness is local on the source for a covering by two open pieces.** Let `κ₁ : F₁ ⟶ R` and
`κ₂ : F₂ ⟶ R` be open immersions of algebraic spaces such that every section of `R` lies, fppf
locally, in the image of one of them. Then a morphism `φ : R ⟶ Y` to an algebraic space is étale
as soon as `κ₁ ≫ φ` and `κ₂ ≫ φ` are. This is Stacks 06F4 for the étale covering `{κ₁, κ₂}`. -/
theorem isEtale_of_isEtale_comp_of_two_opens {R Y F₁ F₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hR : IsAlgebraicSpace B S hS R) (hY : IsAlgebraicSpace B S hS Y)
    (hF₁ : IsAlgebraicSpace B S hS F₁) (hF₂ : IsAlgebraicSpace B S hS F₂)
    (κ₁ : F₁ ⟶ R) (κ₂ : F₂ ⟶ R) (ho₁ : IsOpenImmersion B S hS κ₁)
    (ho₂ : IsOpenImmersion B S hS κ₂)
    (hcov : (Subfunctor.range κ₁ ⊔ Subfunctor.range κ₂).sheafify
      (BigFppfOver.topology B S hS) = ⊤)
    (φ : R ⟶ Y) (h₁ : IsEtale B S hS (κ₁ ≫ φ)) (h₂ : IsEtale B S hS (κ₂ ≫ φ)) :
    IsEtale B S hS φ := by
  let I := ULift.{u} WalkingPair
  let RS : AlgebraicSpaces B S hS := ⟨R, hR⟩
  let Fs : I → AlgebraicSpaces B S hS := fun i => WalkingPair.casesOn i.down ⟨F₁, hF₁⟩ ⟨F₂, hF₂⟩
  let ιs : ∀ i, Fs i ⟶ RS := fun i =>
    match i with
    | ⟨.left⟩ => ObjectProperty.homMk κ₁
    | ⟨.right⟩ => ObjectProperty.homMk κ₂
  let U : I → Subfunctor R := fun i => Subfunctor.range (ιs i).hom
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Sigma.desc fun i => (U i).ι) := by
    have hcov' : ∀ (V : (BigFppfOver B S hS)ᵒᵖ) (r : R.obj V),
        (Subfunctor.range κ₁ ⊔ Subfunctor.range κ₂).sieveOfSection r ∈
          BigFppfOver.topology B S hS V.unop := fun V r => by
      have hr : r ∈ ((Subfunctor.range κ₁ ⊔ Subfunctor.range κ₂).sheafify
          (BigFppfOver.topology B S hS)).obj V := by rw [hcov]; trivial
      exact hr
    refine ⟨fun {V} r => (BigFppfOver.topology B S hS).superset_covering ?_ (hcov' (op V) r)⟩
    rintro V' q (⟨x, hx⟩ | ⟨x, hx⟩)
    · refine ⟨(Sigma.ι (fun i => (U i).toFunctor) ⟨.left⟩).app (op V') ⟨_, x, rfl⟩, ?_⟩
      exact (congrArg (fun k => k.app (op V') ⟨_, x, rfl⟩)
        (Sigma.ι_comp_desc (fun i => (U i).ι) (⟨.left⟩ : I))).trans hx
    · refine ⟨(Sigma.ι (fun i => (U i).toFunctor) ⟨.right⟩).app (op V') ⟨_, x, rfl⟩, ?_⟩
      exact (congrArg (fun k => k.app (op V') ⟨_, x, rfl⟩)
        (Sigma.ι_comp_desc (fun i => (U i).ι) (⟨.right⟩ : I))).trans hx
  have hcover := points_cover_of_isLocallySurjective_sigma_desc B S hS _ I U hls
  have hcovE : IsEtaleCovering B S hS (fun i => (Fs i).obj) (fun i => (ιs i).hom) := by
    refine ⟨hR, fun i => (Fs i).property, ?_, ?_⟩
    · rintro ⟨_ | _⟩
      exacts [isEtale_of_isOpenImmersion B S hS ho₁, isEtale_of_isOpenImmersion B S hS ho₂]
    · refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨i, z, hz⟩ := Set.mem_iUnion.1 (hcover ▸ Set.mem_univ x)
      have hrange : Function.Surjective
          (pointsMap B S hS (Fs i).obj (Subfunctor.toRange (ιs i).hom)) := by
        refine surjective_pointsMap_of_surjective_app B S hS _ fun T => ?_
        rintro ⟨_, y, rfl⟩
        exact ⟨y, rfl⟩
      obtain ⟨w, hw⟩ := hrange z
      refine Set.mem_iUnion.2 ⟨i, w, ?_⟩
      rwa [← Subfunctor.toRange_ι (ιs i).hom, pointsMap_comp, Function.comp_apply, hw]
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃_ _ : AlgebraicSpaces B S hS⦄ k => IsEtale B S hS k.hom
  let _ : Q.IsLocalAtSource (Topology.precoverage.{u, u} .etale B S hS) :=
    isEtale_isLocalAtSource_etale.{u, u} B S hS
  have hPre : Presieve.ofArrows Fs ιs ∈ Topology.precoverage.{u, u} .etale B S hS RS :=
    ⟨I, Fs, ιs, rfl, hR, fun i => (Fs i).property, hcovE⟩
  have hfin : Q (ObjectProperty.homMk φ : RS ⟶ ⟨Y, hY⟩) := by
    refine MorphismProperty.IsLocalAtSource.of_forall_comp (P := Q) hPre ?_
    rintro T g ⟨⟨_ | _⟩⟩
    exacts [h₁, h₂]
  exact hfin

end TwoOpens

/-! ### The relation is an algebraic space -/

section Algebraic

variable (B S hS) in
/-- The hypotheses under which the relation is an algebraic space: `A` and `X` are algebraic
spaces, `W` is an open subspace of `X`, and `A ⟶ X` is étale over `W`. -/
structure GluedRelationData : Prop where
  isAlgebraicSpace_source : IsAlgebraicSpace B S hS A
  isAlgebraicSpace_target : IsAlgebraicSpace B S hS X
  isOpenSubspace : IsOpenSubspace B S hS W
  isEtale : IsEtale B S hS (W.fromPreimage fA)

variable {fA W} (H : GluedRelationData B S hS fA W)
include H

/-- The fibre square `A ×_X A` is an algebraic space. -/
theorem GluedRelationData.isAlgebraicSpace_fibreSquare :
    IsAlgebraicSpace B S hS (pullback fA fA) :=
  AlgebraicGeometry.isAlgebraicSpace_pullback B S hS fA fA H.1 H.1 H.2

/-- The part of `A ×_X A` over `W` is an open subspace. -/
theorem GluedRelationData.isOpenSubspace_gluedOverPart :
    IsOpenSubspace B S hS (gluedOverPart fA W) :=
  isOpenSubspace_preimage B S hS _ W H.2 H.isAlgebraicSpace_fibreSquare H.3

/-- The part of `A` over `W` is an open subspace. -/
theorem GluedRelationData.isOpenSubspace_gluedSourcePart :
    IsOpenSubspace B S hS (gluedSourcePart fA W) :=
  isOpenSubspace_preimage B S hS fA W H.2 H.1 H.3

/-- The second projection from the part of `A ×_X A` over `W` to the part of `A` over `W` is
étale. -/
theorem GluedRelationData.isEtale_gluedOverSnd : IsEtale B S hS (gluedOverSnd fA W) := by
  rw [← (isPullback_gluedOverFst_gluedOverSnd fA W).isoPullback_hom_snd]
  exact isEtale_comp B S hS (isEtale_of_isIso B S hS _)
    (isEtale_pullback_snd B S hS H.isOpenSubspace_gluedSourcePart.1 H.3.1
      H.isOpenSubspace_gluedSourcePart.1 _ _ H.4)

/-- The first projection from the part of `A ×_X A` over `W` to the part of `A` over `W` is
étale. -/
theorem GluedRelationData.isEtale_gluedOverFst : IsEtale B S hS (gluedOverFst fA W) := by
  rw [← (isPullback_gluedOverFst_gluedOverSnd fA W).flip.isoPullback_hom_snd]
  exact isEtale_comp B S hS (isEtale_of_isIso B S hS _)
    (isEtale_pullback_snd B S hS H.isOpenSubspace_gluedSourcePart.1 H.3.1
      H.isOpenSubspace_gluedSourcePart.1 _ _ H.4)

/-- The diagonal of the part of `A` over `W` is an open immersion, `A ⟶ X` being étale, hence
unramified, over `W` (Stacks 05W1). -/
theorem GluedRelationData.isOpenImmersion_gluedOverDiag :
    IsOpenImmersion B S hS (gluedOverDiag fA W) := by
  have h := isPullback_gluedOverFst_gluedOverSnd fA W
  have hd : gluedOverDiag fA W ≫ h.isoPullback.hom = pullback.diagonal (W.fromPreimage fA) := by
    apply pullback.hom_ext <;> simp
  rw [(Iso.eq_comp_inv _).2 hd]
  exact MorphismProperty.RespectsIso.postcomp _ _ _
    (isOpenImmersion_diagonal_of_isUnramified B S hS H.isOpenSubspace_gluedSourcePart.1 H.3.1 _
      (isUnramified_of_isEtale B S hS H.4))

/-- The inclusion of the part over `W` into the relation is an open immersion. -/
theorem GluedRelationData.isOpenImmersion_gluedOverIncl :
    IsOpenImmersion B S hS (gluedOverIncl fA W) :=
  isOpenImmersion_of_comp_mono B S hS _ (gluedDiagonalRelation fA W).ι
    H.isOpenSubspace_gluedOverPart.2

/-- The diagonal is an open immersion into the relation: locally on the source of a test
morphism into the relation, the test morphism factors through the diagonal, where the base
change is an isomorphism, or through the part over `W`, where it is a base change of the diagonal
of the part of `A` over `W`. -/
theorem GluedRelationData.isOpenImmersion_gluedDiag :
    IsOpenImmersion B S hS (gluedDiag fA W) := by
  have hQi : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hrep : yoneda.relativelyRepresentable (gluedDiag fA W) :=
    (MorphismProperty.relative_of_comp_mono yoneda _ (gluedDiag fA W)
      (gluedDiagonalRelation fA W).ι (monomorphisms_diagonal B S hS H.1 fA)).rep
  refine (MorphismProperty.presheaf_iff_forall_presheaf_pullback_snd _ _).2 fun a g => ?_
  have hrep' : yoneda.relativelyRepresentable (pullback.snd (gluedDiag fA W) g) :=
    (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
      (IsPullback.of_hasPullback (gluedDiag fA W) g) hrep
  refine presheaf_of_coveringSieve_of_descendsAlong g hrep'
    (T := (gluedDiagonalRelation₀ fA W).sieveOfSection (yonedaEquiv g).1) (yonedaEquiv g).2 ?_
  intro b q hq
  have hq' : (pullback fA fA).map q.op (yonedaEquiv g).1 ∈
      (gluedDiagonalRelation₀ fA W).obj (op b) := hq
  set s := (pullback fA fA).map q.op (yonedaEquiv g).1 with hs
  have hsg : yonedaEquiv (yoneda.map q ≫ g ≫ (gluedDiagonalRelation fA W).ι) = s := by
    rw [← yonedaEquiv_naturality, yonedaEquiv_comp]
    rfl
  have hsg₁ : yonedaEquiv (yoneda.map q ≫ g ≫ (gluedDiagonalRelation fA W).ι ≫
      pullback.fst fA fA) = (pullback.fst fA fA).app (op b) s := by
    rw [← hsg, ← yonedaEquiv_comp]
    simp only [Category.assoc]
  have hsg₂ : yonedaEquiv (yoneda.map q ≫ g ≫ (gluedDiagonalRelation fA W).ι ≫
      pullback.snd fA fA) = (pullback.snd fA fA).app (op b) s := by
    rw [← hsg, ← yonedaEquiv_comp]
    simp only [Category.assoc]
  rcases hq' with h | h
  · let c : yoneda.obj b ⟶ A := yonedaEquiv.symm ((pullback.fst fA fA).app (op b) s)
    have hc : yonedaEquiv c = (pullback.fst fA fA).app (op b) s := yonedaEquiv.apply_symm_apply _
    have hk : yoneda.map q ≫ g = c ≫ gluedDiag fA W := by
      rw [← cancel_mono (gluedDiagonalRelation fA W).ι]
      apply pullback.hom_ext <;> apply yonedaEquiv.injective <;>
        simp only [Category.assoc, gluedDiag_ι_assoc, pullback.diagonal_fst,
          pullback.diagonal_snd, Category.comp_id]
      · rw [hsg₁, hc]
      · rw [hsg₂, hc, h]
    have key : ∀ k, k = c ≫ gluedDiag fA W → (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd (gluedDiag fA W) k) := by
      rintro k rfl
      have : Mono (gluedDiag fA W) := by
        have : Mono (gluedDiag fA W ≫ (gluedDiagonalRelation fA W).ι) := by
          rw [gluedDiag_ι]; infer_instance
        exact mono_of_mono _ (gluedDiagonalRelation fA W).ι
      exact presheaf_of_isIso B S hS hQi (fun U => by
        change AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (𝟙 U))
        rw [CategoryTheory.Functor.map_id]; infer_instance) _
    exact key _ hk
  · let k' : yoneda.obj b ⟶ (gluedOverPart fA W).toFunctor := yonedaEquiv.symm ⟨s, h⟩
    have hk : yoneda.map q ≫ g = k' ≫ gluedOverIncl fA W := by
      rw [← cancel_mono (gluedDiagonalRelation fA W).ι]
      apply yonedaEquiv.injective
      rw [Category.assoc, hsg, Category.assoc, gluedOverIncl_ι, yonedaEquiv_comp,
        show yonedaEquiv k' = ⟨s, h⟩ from yonedaEquiv.apply_symm_apply _]
      rfl
    have key : ∀ k, k = k' ≫ gluedOverIncl fA W → (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd (gluedDiag fA W) k) := by
      rintro k rfl
      have hsq := (IsPullback.of_hasPullback (gluedOverDiag fA W) k').paste_horiz
        (isPullback_gluedDiag_gluedOverIncl fA W)
      rw [← hsq.isoPullback_inv_snd]
      exact MorphismProperty.RespectsIso.precomp _ _ _
        (presheaf_of_isPullback B S hS (IsPullback.of_hasPullback (gluedOverDiag fA W) k')
          H.isOpenImmersion_gluedOverDiag)
    exact key _ hk


/-- **The relation of the proof of Stacks 0AR9 is an algebraic space.** It is covered by the two
open subspaces `A` (through the diagonal) and the part of `A ×_X A` over `W`, both algebraic
spaces; this is the open-covering criterion Stacks 02WR. -/
theorem GluedRelationData.isAlgebraicSpace_gluedDiagonalRelation :
    IsAlgebraicSpace B S hS (gluedDiagonalRelation fA W).toFunctor := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let FA : Sheaf J (Type u) := ⟨A, H.1.isSheaf⟩
  let FV : Sheaf J (Type u) :=
    ⟨(gluedOverPart fA W).toFunctor, H.isOpenSubspace_gluedOverPart.1.isSheaf⟩
  let FR : Sheaf J (Type u) :=
    ⟨_, isSheaf_gluedDiagonalRelation fA W H.1.isSheaf H.2.isSheaf⟩
  let Fs : WalkingPair → Sheaf J (Type u) := pairFunction FA FV
  have hFs : ∀ k, IsAlgebraicSpace B S hS (Fs k).obj :=
    fun k => WalkingPair.casesOn k H.1 H.isOpenSubspace_gluedOverPart.1
  let E := colimit.cocone (Discrete.functor Fs ⋙ sheafToPresheaf J (Type u))
  let G := Sheaf.sheafifyCocone E
  have hG : IsColimit G := Sheaf.isColimitSheafifyCocone E (colimit.isColimit _)
  let m : ∀ k, Fs k ⟶ FR := fun k => WalkingPair.casesOn k
    (ObjectProperty.homMk (gluedDiag fA W)) (ObjectProperty.homMk (gluedOverIncl fA W))
  let gS : G.pt ⟶ FR := hG.desc (Cofan.mk FR m)
  have hgS : ∀ k, (G.ι.app ⟨k⟩).hom ≫ gS.hom = (m k).hom := fun k =>
    congrArg (fun f => f.hom) (hG.fac (Cofan.mk FR m) ⟨k⟩)
  refine AlgebraicGeometry.isAlgebraicSpace_of_open_cover B S hS _ FR.property WalkingPair
    Fs hFs G.pt (fun k => G.ι.app ⟨k⟩) hG gS.hom ?_ ?_
    (isAlgebraicSpace_finiteCoproduct B S hS (fun k => (Fs k).obj) hFs G.pt
      (fun k => G.ι.app ⟨k⟩) hG)
  · rintro (_ | _)
    · rw [hgS]
      exact H.isOpenImmersion_gluedDiag
    · rw [hgS]
      exact H.isOpenImmersion_gluedOverIncl
  · refine isLocallySurjective_to_gluedDiagonalRelation fA W gS.hom (fun V a => ?_)
      (fun V v => ?_)
    · exact ⟨(G.ι.app ⟨.left⟩).hom.app V a, congrArg (fun k => k.app V a) (hgS .left)⟩
    · exact ⟨(G.ι.app ⟨.right⟩).hom.app V v, congrArg (fun k => k.app V v) (hgS .right)⟩

/-- A morphism out of the relation to an algebraic space is étale as soon as its restrictions to
the diagonal and to the part over `W` are: the two pieces form an étale covering of the
relation, and étaleness is étale local on the source (Stacks 06F4). -/
theorem GluedRelationData.isEtale_of_isEtale_comp {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (φ : (gluedDiagonalRelation fA W).toFunctor ⟶ Y)
    (h₁ : IsEtale B S hS (gluedDiag fA W ≫ φ)) (h₂ : IsEtale B S hS (gluedOverIncl fA W ≫ φ)) :
    IsEtale B S hS φ := by
  refine isEtale_of_isEtale_comp_of_two_opens B S hS H.isAlgebraicSpace_gluedDiagonalRelation hY H.1
    H.isOpenSubspace_gluedOverPart.1 _ _ H.isOpenImmersion_gluedDiag
    H.isOpenImmersion_gluedOverIncl ?_ φ h₁ h₂
  refine eq_top_iff.2 fun V r _ => ?_
  refine (BigFppfOver.topology B S hS).superset_covering ?_ r.2
  intro V' q hq
  have hq' : (pullback fA fA).map q.op r.1 ∈ (gluedDiagonalRelation₀ fA W).obj (op V') := hq
  rcases hq' with h | h
  · refine Or.inl ⟨(pullback.fst fA fA).app (op V') ((pullback fA fA).map q.op r.1),
      Subtype.ext ?_⟩
    exact diagonal_app_fst_of_fst_eq_snd fA h
  · exact Or.inr ⟨⟨(pullback fA fA).map q.op r.1, h⟩, Subtype.ext rfl⟩

/-- The target map of the relation, its first projection to `A`, is étale. -/
theorem GluedRelationData.isEtale_target :
    IsEtale B S hS ((gluedDiagonalRelation fA W).ι ≫ pullback.fst fA fA) := by
  refine H.isEtale_of_isEtale_comp H.1 _ ?_ ?_
  · rw [gluedDiag_ι_assoc, pullback.diagonal_fst]
    exact isEtale_of_isIso B S hS _
  · rw [gluedOverIncl_ι_assoc, ← gluedOverFst_ι]
    exact isEtale_comp B S hS H.isEtale_gluedOverFst
      (isEtale_ι_of_isOpenSubspace H.isOpenSubspace_gluedSourcePart)

/-- The source map of the relation, its second projection to `A`, is étale. -/
theorem GluedRelationData.isEtale_source :
    IsEtale B S hS ((gluedDiagonalRelation fA W).ι ≫ pullback.snd fA fA) := by
  refine H.isEtale_of_isEtale_comp H.1 _ ?_ ?_
  · rw [gluedDiag_ι_assoc, pullback.diagonal_snd]
    exact isEtale_of_isIso B S hS _
  · rw [gluedOverIncl_ι_assoc, ← gluedOverSnd_ι]
    exact isEtale_comp B S hS H.isEtale_gluedOverSnd
      (isEtale_ι_of_isOpenSubspace H.isOpenSubspace_gluedSourcePart)

end Algebraic

end AlgebraicGeometry.Space

end
