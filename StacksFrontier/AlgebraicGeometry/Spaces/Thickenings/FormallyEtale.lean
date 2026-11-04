module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.UnramifiedThickenings
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmoothSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Universal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Formally étale morphisms and first-order thickenings of algebraic spaces

Formal étaleness of a morphism of algebraic spaces over `S` is defined by existence and
uniqueness of lifts across square-zero closed immersions of *affine* objects of the big fppf
site of `S` (Stacks 049S, part (2)). As for formal unramifiedness (Stacks 05ZY) the affineness
is no restriction: a formally étale morphism `f : X ⟶ Y` has exactly one lift across an
arbitrary first-order thickening `T ⊂ T'` of algebraic spaces over `S`. This is **Stacks
0611**, and it is what makes a universal first-order thickening over `Y` remain universal over
any algebraic space `X` receiving a formally étale morphism from `Y`, which is **Stacks 0604**.

The proof proceeds in two independent steps. The first is purely about the site: a first-order
thickening of *site objects* is Zariski-locally a first-order thickening of affine site
objects, and square-zero closed immersions of site objects are stable under base change, so
the lifting problem over an arbitrary square-zero closed immersion `P ⟶ Q` is solved over an
affine open cover of `Q` and the solutions are glued by the sheaf condition of the source. The
second step descends the result to algebraic spaces: the thickening pulls back along a
surjective étale atlas `U ⟶ T'` to a square-zero closed immersion of site objects, step one
produces a lift over `U`, that lift is invariant under the kernel pair of the atlas because the
two restrictions solve the same lifting problem over a chart of `T'`, and an atlas exhibits an
algebraic space as the coequalizer of its kernel pair in fppf sheaves (Stacks 0262, part (3)).

## Main results

* `AlgebraicGeometry.Space.FormallyUnramified.lift_unique_of_isSquareZeroClosedImmersion`:
  the affineness of the test objects in Stacks 049S, part (3), may be dropped.
* `AlgebraicGeometry.Space.FormallySmooth.exists_lift_of_isSquareZeroClosedImmersion`: the
  same for the existence clause of Stacks 049S, part (1), granted uniqueness.
* `AlgebraicGeometry.Space.FormallyEtale.existsUnique_lift_of_firstOrderThickening`:
  **Stacks 0611**.
* `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.comp_formallyEtale`:
  **Stacks 0604**.

## Implementation notes

The thickening of algebraic spaces is presented as a subfunctor `T` of the functor of points of
`T'` which is a first-order thickening in the sense of Stacks 05ZK, part (2), matching
`AlgebraicGeometry.Space.IsFirstOrderThickening`; a dotted arrow is a transformation of
functors of points, which is the same datum as a morphism of algebraic spaces because the
category of algebraic spaces over `S` is full in presheaves.

The site-level statements are phrased for transformations out of representable presheaves
rather than for sections of a presheaf, because that is the form in which the gluing arguments
use them; `CategoryTheory.yonedaEquiv` translates them into the sections of Stacks 049S. The
source presheaf is required to be a sheaf — both to glue the local lifts and to recognise two
lifts that agree Zariski-locally — and so is the target presheaf, which is needed only to
recognise that the glued arrow lies over the given one.

Uniqueness at the level of algebraic spaces is not reproved here: it is exactly
`AlgebraicGeometry.Space.FormallyUnramified.lifts_unique_of_firstOrderThickening`, Stacks 05ZY,
applied to the formally unramified morphism underlying a formally étale one.

## References

* [Stacks Project, Tag 0611](https://stacks.math.columbia.edu/tag/0611)
* [Stacks Project, Tag 0604](https://stacks.math.columbia.edu/tag/0604)
* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 05ZY](https://stacks.math.columbia.edu/tag/05ZY)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Gluing transformations out of a representable presheaf -/

/-- Two transformations from a representable presheaf to a sheaf which agree after restriction
along every member of a covering sieve of the representing object are equal. -/
theorem hom_ext_of_mem_topology {C : Type*} [Category.{u} C]
    (J : GrothendieckTopology C) {F : Cᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf J F)
    {W : C} (R : Sieve W) (hR : R ∈ J W) {c d : yoneda.obj W ⟶ F}
    (h : ∀ ⦃Z : C⦄ (e : Z ⟶ W), R.arrows e → yoneda.map e ≫ c = yoneda.map e ≫ d) :
    c = d := by
  refine yonedaEquiv.injective
    ((((isSheaf_iff_isSheaf_of_type J F).1 hF) R hR).isSeparatedFor.ext ?_)
  intro Z e he
  simpa only [yonedaEquiv_naturality] using congrArg yonedaEquiv (h e he)

/-- A family of transformations out of the members of a covering family, agreeing on every
common refinement, glues to a transformation out of the covered object. -/
theorem exists_glue_of_mem_topology {C : Type*} [Category.{u} C]
    (J : GrothendieckTopology C) {F : Cᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf J F)
    {W : C} {I : Type*} (V : I → C) (r : ∀ k, V k ⟶ W)
    (hr : Sieve.ofArrows V r ∈ J W) (c : ∀ k, yoneda.obj (V k) ⟶ F)
    (hc : ∀ (k l : I) (Z : C) (s : Z ⟶ V k) (t : Z ⟶ V l),
      s ≫ r k = t ≫ r l → yoneda.map s ≫ c k = yoneda.map t ≫ c l) :
    ∃ d : yoneda.obj W ⟶ F, ∀ k, yoneda.map (r k) ≫ d = c k := by
  obtain ⟨z, hz, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
    (((isSheaf_iff_isSheaf_of_type J F).1 hF).isSheafFor (Presieve.ofArrows V r) hr)
    (fun k ↦ yonedaEquiv (c k)) (fun k l Z s t hst ↦ by
      simpa only [yonedaEquiv_naturality] using congrArg yonedaEquiv (hc k l Z s t hst))
  refine ⟨yonedaEquiv.symm z, fun k ↦ yonedaEquiv.injective ?_⟩
  rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply, hz]

/-! ### Affine open covers and base changes in the big fppf site -/

/-- Every object of the big fppf category over `S` is covered by a jointly surjective family of
open immersions from affine objects, indexed by its affine opens. -/
theorem exists_affineOpenFamily (T : BigFppfOver B S hS) :
    ∃ (V : ((BigFppfOver.toScheme B S hS).obj T).affineOpens → BigFppfOver B S hS)
      (r : ∀ k, V k ⟶ T),
      (∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (V k))) ∧
      (∀ k, _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (r k))) ∧
      ∀ x : (BigFppfOver.toScheme B S hS).obj T,
        ∃ k, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (r k)) := by
  classical
  choose V r hoi hrange haff using fun k ↦ BigFppfOver.exists_affineOpen_restrict B S hS T k
  refine ⟨V, r, haff, hoi, fun x ↦ ?_⟩
  have hx : x ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj T).Opens) := trivial
  rw [← iSup_affineOpens_eq_top] at hx
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨k, by rwa [hrange k]⟩

/-- The base change of a square-zero closed immersion of objects of the big fppf category over
`S` along an arbitrary morphism of that category is again one, together with the universal
property of the base change. -/
private theorem exists_baseChange_isSquareZeroClosedImmersion {P Q V : BigFppfOver B S hS}
    {i : P ⟶ Q} (hi : IsSquareZeroClosedImmersion B S hS i) (r : V ⟶ Q) :
    ∃ (P₀ : BigFppfOver B S hS) (i₀ : P₀ ⟶ V) (w : P₀ ⟶ P),
      w ≫ i = i₀ ≫ r ∧ IsSquareZeroClosedImmersion B S hS i₀ ∧
      ∀ {Z : BigFppfOver B S hS} (g : Z ⟶ P) (h : Z ⟶ V), g ≫ i = h ≫ r →
        ∃ l : Z ⟶ P₀, l ≫ w = g ∧ l ≫ i₀ = h := by
  have hpres := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hsq := (IsPullback.of_hasPullback i r).map (BigFppfOver.toScheme B S hS)
  exact ⟨Limits.pullback i r, pullback.snd i r, pullback.fst i r, pullback.condition,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Stacks.Thickenings.IsFirstOrderThickening.{u}) hsq
      (isFirstOrderThickening_of_isSquareZeroClosedImmersion hi),
    fun g h hgh ↦ ⟨pullback.lift g h hgh, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩⟩

/-- The source of a closed immersion into an affine object of the big fppf category over `S` is
again affine. -/
private theorem isAffine_of_isSquareZeroClosedImmersion {P V : BigFppfOver B S hS}
    {i₀ : P ⟶ V} (hi₀ : IsSquareZeroClosedImmersion B S hS i₀)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj P) := by
  have hclosed : _root_.AlgebraicGeometry.IsClosedImmersion
    ((BigFppfOver.toScheme B S hS).map i₀) := hi₀.1
  exact isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map i₀)

/-! ### Lifting across a square-zero closed immersion of affine test objects -/

/-- A commutative square of transformations out of representable presheaves gives a commutative
square of sections, as in the definition of formal smoothness. -/
private theorem app_yonedaEquiv_eq_map {C : Type*} [Category.{u} C] {F G : Cᵒᵖ ⥤ Type u}
    (a : F ⟶ G) {P Q : C} (i : P ⟶ Q) (x : yoneda.obj P ⟶ F) (y : yoneda.obj Q ⟶ G)
    (hsq : x ≫ a = yoneda.map i ≫ y) :
    a.app (op P) (yonedaEquiv x) = G.map i.op (yonedaEquiv y) :=
  calc a.app (op P) (yonedaEquiv x) = yonedaEquiv (x ≫ a) := (yonedaEquiv_comp _ _).symm
    _ = yonedaEquiv (yoneda.map i ≫ y) := congrArg _ hsq
    _ = G.map i.op (yonedaEquiv y) := (yonedaEquiv_naturality _ _).symm

/-- Formal smoothness, read on transformations out of representable presheaves: a commutative
square over a square-zero closed immersion of affine objects of the site admits a dotted
arrow. -/
private theorem exists_lift_arrow_of_isAffine {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} (ha : FormallySmooth a) {P Q : BigFppfOver B S hS} {i : P ⟶ Q}
    (hi : IsSquareZeroClosedImmersion B S hS i)
    (hP : IsAffine ((BigFppfOver.toScheme B S hS).obj P))
    (hQ : IsAffine ((BigFppfOver.toScheme B S hS).obj Q))
    (x : yoneda.obj P ⟶ F) (y : yoneda.obj Q ⟶ G) (hsq : x ≫ a = yoneda.map i ≫ y) :
    ∃ z : yoneda.obj Q ⟶ F, yoneda.map i ≫ z = x ∧ z ≫ a = y := by
  obtain ⟨z, hz₁, hz₂⟩ := ha P Q hP hQ i hi (yonedaEquiv x) (yonedaEquiv y)
    (app_yonedaEquiv_eq_map a i x y hsq)
  refine ⟨yonedaEquiv.symm z, ?_, ?_⟩
  · rw [yonedaEquiv_symm_naturality_left, hz₁, Equiv.symm_apply_apply]
  · rw [yonedaEquiv_symm_naturality_right, hz₂, Equiv.symm_apply_apply]

/-- Formal unramifiedness, read on transformations out of representable presheaves: a
commutative square over a square-zero closed immersion of affine objects of the site admits at
most one dotted arrow. -/
private theorem lift_arrow_unique_of_isAffine {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} (ha : FormallyUnramified a) {P Q : BigFppfOver B S hS} {i : P ⟶ Q}
    (hi : IsSquareZeroClosedImmersion B S hS i)
    (hP : IsAffine ((BigFppfOver.toScheme B S hS).obj P))
    (hQ : IsAffine ((BigFppfOver.toScheme B S hS).obj Q))
    (x : yoneda.obj P ⟶ F) (y : yoneda.obj Q ⟶ G) (z₁ z₂ : yoneda.obj Q ⟶ F)
    (hz₁ : yoneda.map i ≫ z₁ = x) (hz₁' : z₁ ≫ a = y)
    (hz₂ : yoneda.map i ≫ z₂ = x) (hz₂' : z₂ ≫ a = y) :
    z₁ = z₂ := by
  have hlift (z : yoneda.obj Q ⟶ F) (hz : yoneda.map i ≫ z = x) (hz' : z ≫ a = y) :
      IsLift a i (yonedaEquiv x) (yonedaEquiv y) (yonedaEquiv z) :=
    ⟨by rw [yonedaEquiv_naturality, hz], by rw [← yonedaEquiv_comp, hz']⟩
  refine yonedaEquiv.injective (ha P Q hP hQ i hi (yonedaEquiv x) (yonedaEquiv y)
    (app_yonedaEquiv_eq_map a i x y (by rw [← hz₁, Category.assoc, hz₁']))
    (yonedaEquiv z₁) (yonedaEquiv z₂) (hlift z₁ hz₁ hz₁') (hlift z₂ hz₂ hz₂'))

/-! ### Dropping the affineness of the test objects -/

/-- **The affineness of the test objects of Stacks 049S, part (3), may be dropped.** A formally
unramified transformation to a sheaf admits at most one dotted arrow in a commutative square
over an arbitrary square-zero closed immersion of objects of the big fppf site over `S`.

Both lifts restrict, over the base change of the immersion to an affine open of the larger
object, to a lift against a square-zero closed immersion of affine objects, where formal
unramifiedness applies; the affine opens cover, and a sheaf is separated for the covering sieve
they generate. -/
theorem FormallyUnramified.lift_unique_of_isSquareZeroClosedImmersion
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) (ha : FormallyUnramified a)
    {P Q : BigFppfOver B S hS} {i : P ⟶ Q} (hi : IsSquareZeroClosedImmersion B S hS i)
    (x : yoneda.obj P ⟶ F) (y : yoneda.obj Q ⟶ G) (z₁ z₂ : yoneda.obj Q ⟶ F)
    (hz₁ : yoneda.map i ≫ z₁ = x) (hz₁' : z₁ ≫ a = y)
    (hz₂ : yoneda.map i ≫ z₂ = x) (hz₂' : z₂ ≫ a = y) :
    z₁ = z₂ := by
  obtain ⟨V, r, hVaff, hVoi, hVcov⟩ := exists_affineOpenFamily B S hS Q
  refine hom_ext_of_openCover_of_isSheaf B S hS hF r hVoi hVcov fun k ↦ ?_
  obtain ⟨P₀, i₀, w, hcomm, hi₀, -⟩ :=
    exists_baseChange_isSquareZeroClosedImmersion B S hS hi (r k)
  have hrest (z : yoneda.obj Q ⟶ F) (hz : yoneda.map i ≫ z = x) :
      yoneda.map i₀ ≫ yoneda.map (r k) ≫ z = yoneda.map w ≫ x := by
    rw [← Functor.map_comp_assoc, ← hcomm, Functor.map_comp_assoc, hz]
  exact lift_arrow_unique_of_isAffine B S hS ha hi₀
    (isAffine_of_isSquareZeroClosedImmersion B S hS hi₀ (hVaff k)) (hVaff k) _ _ _ _
    (hrest z₁ hz₁) (by rw [Category.assoc, hz₁']) (hrest z₂ hz₂) (by rw [Category.assoc, hz₂'])

/-- **The affineness of the test objects of Stacks 049S, part (1), may be dropped.** A formally
smooth and formally unramified transformation of sheaves admits a dotted arrow in every
commutative square over an arbitrary square-zero closed immersion of objects of the big fppf
site over `S`.

Over each affine open of the larger object the base-changed immersion is a square-zero closed
immersion of affine objects, so formal smoothness produces a lift there. Two such lifts agree
on every common refinement, because both solve the lifting problem base-changed to it and
`AlgebraicGeometry.Space.FormallyUnramified.lift_unique_of_isSquareZeroClosedImmersion`
applies; the sheaf condition then glues them. Formal unramifiedness is therefore used for the
compatibility of the local solutions, not for uniqueness of the global one. -/
@[ega "IV 17.1.2" "(iv)"]
theorem FormallySmooth.exists_lift_of_isSquareZeroClosedImmersion
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (ha : FormallySmooth a) (hau : FormallyUnramified a)
    {P Q : BigFppfOver B S hS} {i : P ⟶ Q} (hi : IsSquareZeroClosedImmersion B S hS i)
    (x : yoneda.obj P ⟶ F) (y : yoneda.obj Q ⟶ G) (hsq : x ≫ a = yoneda.map i ≫ y) :
    ∃ z : yoneda.obj Q ⟶ F, yoneda.map i ≫ z = x ∧ z ≫ a = y := by
  classical
  obtain ⟨V, r, hVaff, hVoi, hVcov⟩ := exists_affineOpenFamily B S hS Q
  choose P₀ i₀ w hcomm hi₀ hlift using
    fun k ↦ exists_baseChange_isSquareZeroClosedImmersion B S hS hi (r k)
  -- The base-changed lifting problem over a morphism into `Q`.
  have hsqbc {Z : BigFppfOver B S hS} {P₁ : BigFppfOver B S hS} {i₁ : P₁ ⟶ Z} {w₁ : P₁ ⟶ P}
      (m : Z ⟶ Q) (hcomm₁ : w₁ ≫ i = i₁ ≫ m) :
      (yoneda.map w₁ ≫ x) ≫ a = yoneda.map i₁ ≫ yoneda.map m ≫ y := by
    rw [Category.assoc, hsq, ← Functor.map_comp_assoc, hcomm₁, Functor.map_comp_assoc]
  -- The local solutions, over the affine opens of `Q`.
  choose z hz₁ hz₂ using fun k ↦ exists_lift_arrow_of_isAffine B S hS ha (hi₀ k)
    (isAffine_of_isSquareZeroClosedImmersion B S hS (hi₀ k) (hVaff k)) (hVaff k)
    (yoneda.map (w k) ≫ x) (yoneda.map (r k) ≫ y) (hsqbc (r k) (hcomm k))
  -- Restricting a local solution along a morphism of the site again solves the problem.
  have hres {Z : BigFppfOver B S hS} (k : _) (s : Z ⟶ V k) {P₁ : BigFppfOver B S hS}
      {i₁ : P₁ ⟶ Z} {w₁ : P₁ ⟶ P} (hcomm₁ : w₁ ≫ i = i₁ ≫ s ≫ r k) :
      yoneda.map i₁ ≫ yoneda.map s ≫ z k = yoneda.map w₁ ≫ x ∧
        (yoneda.map s ≫ z k) ≫ a = yoneda.map (s ≫ r k) ≫ y := by
    obtain ⟨l, hl₁, hl₂⟩ := hlift k w₁ (i₁ ≫ s) (by rw [hcomm₁, Category.assoc])
    refine ⟨?_, by rw [Category.assoc, hz₂, Functor.map_comp_assoc]⟩
    rw [← Functor.map_comp_assoc, ← hl₂, Functor.map_comp_assoc, hz₁, ← Functor.map_comp_assoc,
      hl₁]
  -- The local solutions agree on every common refinement.
  have hcompat (k l : _) (Z : BigFppfOver B S hS) (s : Z ⟶ V k) (t : Z ⟶ V l)
      (hst : s ≫ r k = t ≫ r l) : yoneda.map s ≫ z k = yoneda.map t ≫ z l := by
    obtain ⟨P₁, i₁, w₁, hcomm₁, hi₁, -⟩ :=
      exists_baseChange_isSquareZeroClosedImmersion B S hS hi (s ≫ r k)
    obtain ⟨hk₁, hk₂⟩ := hres k s hcomm₁
    obtain ⟨hl₁, hl₂⟩ := hres l t (by rw [hcomm₁, hst])
    exact FormallyUnramified.lift_unique_of_isSquareZeroClosedImmersion B S hS hF hau hi₁
      (yoneda.map w₁ ≫ x) (yoneda.map (s ≫ r k) ≫ y) _ _ hk₁ hk₂ hl₁ (by rw [hl₂, hst])
  obtain ⟨d, hd⟩ := exists_glue_of_mem_topology (BigFppfOver.topology B S hS) hF V r
    (BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS r hVoi hVcov) z hcompat
  refine ⟨d, ?_, ?_⟩
  · -- The glued arrow restricts to `x`, tested on the sieve the cover pulls back to.
    refine hom_ext_of_mem_topology (BigFppfOver.topology B S hS) hF
      ((Sieve.ofArrows V r).pullback i)
      ((BigFppfOver.topology B S hS).pullback_stable i
        (BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS r hVoi hVcov)) ?_
    intro Z e he
    obtain ⟨k, g, hg⟩ := (Sieve.mem_ofArrows_iff V r (e ≫ i)).1 he
    obtain ⟨l, hl₁, hl₂⟩ := hlift k e g hg
    rw [← Functor.map_comp_assoc, hg, Functor.map_comp_assoc, hd, ← hl₂, Functor.map_comp_assoc,
      hz₁, ← Functor.map_comp_assoc, hl₁]
  · -- The glued arrow lies over `y`.
    refine hom_ext_of_openCover_of_isSheaf B S hS hG r hVoi hVcov fun k ↦ ?_
    rw [← Category.assoc, hd k, hz₂ k]

/-! ### Lifting across a first-order thickening of algebraic spaces -/

/-- **Stacks 0611.** A formally étale morphism `f : X ⟶ Y` of algebraic spaces over `S` admits
exactly one dotted arrow in a solid square over a first-order thickening `T ⊂ T'` of algebraic
spaces over `S`. No affineness is assumed of either space of the thickening: the affineness of
the test objects in the definition of formal étaleness, Stacks 049S part (2), may be dropped. -/
@[stacks 0611]
theorem FormallyEtale.existsUnique_lift_of_firstOrderThickening
    {X Y T' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : FormallyEtale f.hom)
    (T : Subfunctor T'.obj) (hT : IsFirstOrderThickening B S hS T' T)
    (a : T.toFunctor ⟶ X.obj) (b : T'.obj ⟶ Y.obj) (hsq : a ≫ f.hom = T.ι ≫ b) :
    ∃! c : T'.obj ⟶ X.obj, T.ι ≫ c = a ∧ c ≫ f.hom = b := by
  classical
  have hsm : FormallySmooth f.hom := fun P Q hP hQ i hi v y hvy ↦
    (hf P Q hP hQ i hi v y hvy).exists
  have hur : FormallyUnramified f.hom := fun P Q hP hQ i hi v y hvy z₁ z₂ h₁ h₂ ↦
    (hf P Q hP hQ i hi v y hvy).unique h₁ h₂
  -- A surjective étale atlas of the ambient space, and the thickening of site objects that the
  -- given thickening pulls back to over it.
  obtain ⟨U, q, hqS, hqE⟩ := T'.property.exists_atlas
  obtain ⟨U₀, i, p, hpb, hci, hker⟩ :=
    exists_nthOrderThickening_chart_pullback B S hS hT U q hqE
  have hi : IsSquareZeroClosedImmersion B S hS i := ⟨hci, hker⟩
  obtain ⟨c, hc₁, hc₂⟩ := FormallySmooth.exists_lift_of_isSquareZeroClosedImmersion B S hS
    X.property.isSheaf Y.property.isSheaf hsm hur hi (p ≫ a) (q ≫ b)
    (by rw [Category.assoc, hsq, ← Category.assoc, hpb.w, Category.assoc])
  -- The kernel pair of the atlas, and the invariance of the lift under it.
  let rep := T'.property.diagonal_representable.of_diag q
  let R := rep.pullback q
  let s : R ⟶ U := rep.fst' q
  let t : R ⟶ U := rep.snd q
  have hR : IsPullback (yoneda.map s) (yoneda.map t) q q := rep.isPullback' q
  have hEs : Etale ((BigFppfOver.toScheme B S hS).map s) :=
    hqE.property q (yoneda.map t) s hR.flip
  have hinv : yoneda.map s ≫ c = yoneda.map t ≫ c := by
    have hmul := (isMultiplicative_presheaf_etale B S hS).toIsStableUnderComposition
    have hρE : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map s ≫ q) :=
      MorphismProperty.comp_mem _ _ _
        ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ s).2 hEs) hqE
    obtain ⟨R₀, j, pR, hpbR, hciR, hkerR⟩ :=
      exists_nthOrderThickening_chart_pullback B S hS hT R (yoneda.map s ≫ q) hρE
    have key (v : R ⟶ U) (hv : yoneda.map v ≫ q = yoneda.map s ≫ q) :
        yoneda.map j ≫ yoneda.map v ≫ c = pR ≫ a ∧
          (yoneda.map v ≫ c) ≫ f.hom = (yoneda.map s ≫ q) ≫ b := by
      have hw : pR ≫ T.ι = yoneda.map (j ≫ v) ≫ q := by
        rw [hpbR.w, Functor.map_comp, Category.assoc, hv]
      refine ⟨?_, ?_⟩
      · calc yoneda.map j ≫ yoneda.map v ≫ c = yoneda.map (j ≫ v) ≫ c := by
              rw [Functor.map_comp, Category.assoc]
          _ = (hpb.lift pR (yoneda.map (j ≫ v)) hw ≫ yoneda.map i) ≫ c := by
              rw [hpb.lift_snd]
          _ = hpb.lift pR (yoneda.map (j ≫ v)) hw ≫ p ≫ a := by rw [Category.assoc, hc₁]
          _ = pR ≫ a := by rw [← Category.assoc, hpb.lift_fst]
      · calc (yoneda.map v ≫ c) ≫ f.hom = yoneda.map v ≫ q ≫ b := by
              rw [Category.assoc, hc₂]
          _ = (yoneda.map v ≫ q) ≫ b := by rw [Category.assoc]
          _ = (yoneda.map s ≫ q) ≫ b := by rw [hv]
    exact FormallyUnramified.lift_unique_of_isSquareZeroClosedImmersion B S hS
      X.property.isSheaf hur ⟨hciR, hkerR⟩ (pR ≫ a) ((yoneda.map s ≫ q) ≫ b) _ _
      (key s rfl).1 (key s rfl).2 (key t hR.w.symm).1 (key t hR.w.symm).2
  -- The atlas presents `T'` as the coequalizer of its kernel pair, so the lift descends.
  let J := BigFppfOver.topology B S hS
  let hcolimit := isCoequalizer_of_surjectiveEtale B S hS q s t hR T'.property hqS hqE
  let hRsh := Classical.choose hcolimit
  have hcolimitU := Classical.choose_spec hcolimit
  let hUsh := Classical.choose hcolimitU
  have hcolimitC := Classical.choose_spec hcolimitU
  let hc := Classical.choice hcolimitC
  let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
  let UF : Sheaf J (Type u) := ⟨yoneda.obj U, hUsh⟩
  let T'F : Sheaf J (Type u) := ⟨T'.obj, T'.property.isSheaf⟩
  let XF : Sheaf J (Type u) := ⟨X.obj, X.property.isSheaf⟩
  let YF : Sheaf J (Type u) := ⟨Y.obj, Y.property.isSheaf⟩
  let sf : RF ⟶ UF := ⟨yoneda.map s⟩
  let tf : RF ⟶ UF := ⟨yoneda.map t⟩
  let qf : UF ⟶ T'F := ⟨q⟩
  have hwc : sf ≫ (⟨c⟩ : UF ⟶ XF) = tf ≫ (⟨c⟩ : UF ⟶ XF) := Sheaf.hom_ext hinv
  let cofork : Cofork sf tf := Cofork.ofπ (⟨c⟩ : UF ⟶ XF) hwc
  let dsh := hc.desc cofork
  have hfac : qf ≫ dsh = (⟨c⟩ : UF ⟶ XF) := by
    simpa [dsh, cofork] using hc.fac cofork WalkingParallelPair.one
  have hqd : q ≫ dsh.hom = c := congrArg (fun φ ↦ φ.hom) hfac
  -- The descended arrow solves the original lifting problem.
  have hd₂ : dsh.hom ≫ f.hom = b := by
    have _ : Epi qf := Cofork.IsColimit.epi hc
    refine Sheaf.hom_ext_iff.1 ((cancel_epi qf).1 (Sheaf.hom_ext
      (show q ≫ dsh.hom ≫ f.hom = q ≫ b from ?_) :
      qf ≫ (⟨dsh.hom ≫ f.hom⟩ : T'F ⟶ YF) = qf ≫ (⟨b⟩ : T'F ⟶ YF)))
    rw [← Category.assoc, hqd, hc₂]
  have hd₁ : T.ι ≫ dsh.hom = a := by
    have hstabS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    have hstabE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    have hpS := MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hqS
    have hpE := MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hqE
    let U₀F : Sheaf J (Type u) := ⟨yoneda.obj U₀, BigFppfOver.isSheaf_yoneda_obj B S hS U₀⟩
    let TF : Sheaf J (Type u) := ⟨T.toFunctor, hT.choose.1.1.isSheaf⟩
    let pf : U₀F ⟶ TF := ⟨p⟩
    have _ : Sheaf.IsLocallySurjective pf :=
      isLocallySurjective_of_surjective_etale B S hS p hpS hpE
    have _ : Epi pf := inferInstance
    refine Sheaf.hom_ext_iff.1 ((cancel_epi pf).1 (Sheaf.hom_ext
      (show p ≫ T.ι ≫ dsh.hom = p ≫ a from ?_) :
      pf ≫ (⟨T.ι ≫ dsh.hom⟩ : TF ⟶ XF) = pf ≫ (⟨a⟩ : TF ⟶ XF)))
    calc p ≫ T.ι ≫ dsh.hom = (p ≫ T.ι) ≫ dsh.hom := by rw [Category.assoc]
      _ = (yoneda.map i ≫ q) ≫ dsh.hom := by rw [hpb.w]
      _ = yoneda.map i ≫ c := by rw [Category.assoc, hqd]
      _ = p ≫ a := hc₁
  exact ⟨dsh.hom, ⟨hd₁, hd₂⟩, fun c' hc' ↦
    FormallyUnramified.lifts_unique_of_firstOrderThickening B S hS f hur T hT a b hsq
      c' dsh.hom hc'.1 hc'.2 hd₁ hd₂⟩

/-- **Stacks 0604.** A universal first-order thickening of `Z` over an algebraic space `Y` is
also a universal first-order thickening of `Z` over an algebraic space `X` whenever `Y ⟶ X` is
formally étale: the structure morphism of the thickening is composed with the formally étale
morphism, and nothing else changes.

A solid diagram over `X` is first pushed through the formally étale morphism, which by
Stacks 0611 has a unique lift against the thickening `T ⊂ T'`; that lift turns the diagram into
a solid diagram over `Y`, where universality over `Y` applies. Uniqueness over `X` follows
because any competing extension produces, after composition with the structure morphism, a lift
of the pushed diagram, which the uniqueness clause of Stacks 0611 identifies with the chosen
one. -/
@[stacks 0604]
theorem IsUniversalFirstOrderThickening.comp_formallyEtale {Z' Y X : AlgebraicSpaces B S hS}
    (Z : Subfunctor Z'.obj) (p : Z' ⟶ Y) (q : Y ⟶ X)
    (hp : IsUniversalFirstOrderThickening B S hS Z p) (hq : FormallyEtale q.hom) :
    IsUniversalFirstOrderThickening B S hS Z (p ≫ q) := by
  have hpq : (p ≫ q).hom = p.hom ≫ q.hom := rfl
  refine ⟨hp.firstOrder, ?_⟩
  intro T' T hT a b hcomm
  rw [hpq] at hcomm ⊢
  have hsolid : (a ≫ Z.ι ≫ p.hom) ≫ q.hom = T.ι ≫ b := by
    simp only [Category.assoc]
    exact hcomm.symm
  obtain ⟨c, hc, hcu⟩ := FormallyEtale.existsUnique_lift_of_firstOrderThickening B S hS q hq
    T hT (a ≫ Z.ι ≫ p.hom) b hsolid
  obtain ⟨d, hd, hdu⟩ := hp.existsUnique_lift T hT a c hc.1
  refine ⟨d, ⟨hd.1, ?_⟩, fun e he ↦ ?_⟩
  · rw [← Category.assoc, hd.2, hc.2]
  · refine hdu e ⟨he.1, hcu (e ≫ p.hom) ⟨?_, ?_⟩⟩
    · rw [← Category.assoc, he.1, Category.assoc]
    · rw [Category.assoc]
      exact he.2

end AlgebraicGeometry.Space

end
