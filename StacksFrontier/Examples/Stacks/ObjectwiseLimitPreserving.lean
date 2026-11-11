module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure
public import Mathlib.CategoryTheory.Preadditive.CommGrp_
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ClassifyingTorsors
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalOverTerminal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Smallness
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import StacksFrontier.CategoryTheory.Sites.SmallSiteSheafification
import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import StacksFrontier.Deformation.Artin.LimitPreserving
import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfStructureSheaf

/-!
# Limit preserving on objects does not imply limit preserving

Over a nonempty scheme `S` there is a stack in groupoids over the big fppf site of `S` whose
structure morphism is limit preserving on objects while the stack itself is not limit
preserving. The witness is the stack of torsors under an injective abelian sheaf `H` on the
site: every `H`-torsor is trivial, so each fibre is a connected nonempty groupoid and objects
descend to a finite stage for free, whereas the automorphism group of the trivial torsor over
`T` is `H(T)`, and for `H` a countable product of copies of a nonzero injective sheaf the
sections of `H` over an affine inverse limit are not the colimit of the sections at the
stages.

## Main results

* `exists_stack_isLimitPreservingOnObjects_not_isLimitPreserving` produces such a stack over
  the big fppf site of a nonempty scheme, from the stackiness of categories of torsors; the
  unconditional statement, Stacks 07Z1, is in
  `StacksFrontier/Examples/Stacks/ObjectwiseLimitPreservingTorsors.lean`.

## Implementation notes

The objectwise condition is the one of Stacks 06CU for the structure morphism to the final
object of the 2-category of categories fibred in groupoids over the site, and the failure of
limit preservation is the failure of the canonical comparison functor of Stacks 07XL from the
colimit of the stage fibres to the fibre over the cone point to be an equivalence. Taking
Boolean powers `R → R^{2^n}` of a nonzero ring gives a cofiltered system of affines whose
limit has a section of the product sheaf that does not come from any stage.

`IsStackOfTorsors` carries the stackiness of the category of torsors, which is Stacks 04UM;
the result here takes it as an explicit hypothesis in that shape, which
`StacksFrontier/Examples/Stacks/ObjectwiseLimitPreservingTorsors.lean` discharges.

## References

* [Stacks Project, Tag 07Z1](https://stacks.math.columbia.edu/tag/07Z1)
* [Stacks Project, Tag 04UK](https://stacks.math.columbia.edu/tag/04UK)
* [Stacks Project, Tag 04UM](https://stacks.math.columbia.edu/tag/04UM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.ObjectwiseLimitPreserving

universe u v w t

/-- Stackiness of the category of torsors under a group object over a sheaf, which is the
content of Stacks 04UM: for a sheaf `ℬ` on the big fppf site of `S` and a group object `𝒢`
over `ℬ` whose underlying presheaf is a sheaf, the projection from `𝒢/ℬ-Torsors` to the site
is a stack in groupoids for the fppf topology. -/
public class IsStackOfTorsors (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : Prop where
  /-- The projection from the category of `𝒢/ℬ`-torsors to the big fppf site of `S` is a
  stack in groupoids. -/
  isStackInGroupoids :
    ∀ {ℬ : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (𝒢 : Grp (Over ℬ)),
      Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) ℬ →
      Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) 𝒢.X.left →
      Functor.IsStackInGroupoids.{u + 1}
        (ClassifyingTorsors.torsorsProjection 𝒢)
        (AlgebraicGeometry.BigFppfOver.topology B S hS)

open Cardinal in
/-- The category of schemes of cardinal size strictly below `κ` is essentially small. -/
private lemma essentiallySmall_schemeBelow (κ : Cardinal.{u}) :
    EssentiallySmall.{u} (AlgebraicGeometry.SchemeBelow κ) := by
  let P : ObjectProperty Scheme.{u} := fun X =>
    ∃ R : CommRingCat.{u}, #R ≤ κ ∧ Nonempty (X ≅ Spec R)
  let : ObjectProperty.EssentiallySmall.{u} P := essentiallySmall_affineBelow κ
  let μ := Order.succ (max κ ℵ₀)
  let Q := P.colimitsCardinalClosure μ
  have hPQ : AlgebraicGeometry.schemeSizeBelow κ ≤ Q := by
    intro X hX
    have hμ : ℵ₀ ≤ μ := (le_max_right _ _).trans (Order.le_succ _)
    have hcard : HasCardinalLT X.AffineZariskiSite μ := by
      rw [hasCardinalLT_iff_cardinal_mk_lt]
      exact (X.mk_affineOpens_le_size.trans hX.le).trans_lt
        ((le_max_left _ _).trans_lt (Order.lt_succ _))
    let : Q.IsClosedUnderColimitsOfShape X.AffineZariskiSite :=
      P.isClosedUnderColimitsOfShape_colimitsCardinalClosure μ _
        ((hasCardinalLT_arrow_iff_of_isThin _ _ hμ).mpr hcard)
    apply Q.prop_of_isColimit (Scheme.AffineZariskiSite.isColimitCocone X)
    intro U
    apply P.le_colimitsCardinalClosure μ
    exact ⟨_, (X.mk_sections_le_size ⟨U.1, U.2⟩).trans hX.le, ⟨Iso.refl _⟩⟩
  let : ObjectProperty.EssentiallySmall.{u} (AlgebraicGeometry.schemeSizeBelow κ) :=
    ObjectProperty.EssentiallySmall.of_le hPQ
  exact (inferInstance : EssentiallySmall.{u} (AlgebraicGeometry.SchemeBelow κ))

/-- For `X` an object of an essentially small category, the over category `Over X` is
essentially small. -/
private lemma essentiallySmall_over {C : Type*} [Category.{u} C]
    [EssentiallySmall.{u} C] (X : C) : EssentiallySmall.{u} (Over X) :=
  essentiallySmall_of_fully_faithful (Over.post (equivSmallModel.{u} C).functor)

/-- The big fppf site of a scheme `S` is essentially small. -/
private lemma essentiallySmall_bigFppfOver
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    EssentiallySmall.{u} (AlgebraicGeometry.BigFppfOver B S hS) := by
  let : EssentiallySmall.{u} B.Schemes := essentiallySmall_schemeBelow B.cutoff
  exact essentiallySmall_over _

/-- Presheaves of abelian groups on an essentially small site admit sheafification. -/
private lemma hasSheafify_of_essentiallySmall {C : Type*} [Category.{u} C]
    [EssentiallySmall.{u} C] (J : GrothendieckTopology C) : HasSheafify J AddCommGrpCat.{u} := by
  let : HasSheafify ((equivSmallModel C).inverse.inducedTopology J) AddCommGrpCat.{u} :=
    inferInstance
  exact hasSheafifyEssentiallySmallSite J _

/-- Abelian group valued sheaves on an essentially small site with sheafification form a
Grothendieck abelian category. -/
private lemma isGrothendieckAbelian_sheaf_of_essentiallySmall {C : Type*} [Category.{u} C]
    [EssentiallySmall.{u} C] (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{u}] :
    IsGrothendieckAbelian.{u} (Sheaf J AddCommGrpCat.{u}) := by
  let : HasSheafify ((equivSmallModel C).inverse.inducedTopology J) AddCommGrpCat.{u} :=
    inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} J AddCommGrpCat.{u}

/-- Presheaves of abelian groups on the big fppf site of a scheme `S` admit sheafification. -/
private theorem bigFppfHasSheafify
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u} := by
  have := essentiallySmall_bigFppfOver B S hS
  exact hasSheafify_of_essentiallySmall _

attribute [local instance] bigFppfHasSheafify

/-- The category of abelian group valued sheaves on the big fppf site of a scheme `S` has
enough injectives. -/
private theorem bigFppfSheavesHaveEnoughInjectives
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    EnoughInjectives
      (Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u}) := by
  have := essentiallySmall_bigFppfOver B S hS
  have := isGrothendieckAbelian_sheaf_of_essentiallySmall
    (AlgebraicGeometry.BigFppfOver.topology B S hS)
  exact IsGrothendieckAbelian.enoughInjectives

attribute [local instance] bigFppfSheavesHaveEnoughInjectives

/-- A product of injective objects is injective. -/
private lemma productOfInjectives_injective
    {C : Type u} [Category.{v} C] {α : Type w} (F : α → C)
    [HasProduct F] (hF : ∀ a, Injective (F a)) : Injective (∏ᶜ F) := by
  let (a : α) : Injective (F a) := hF a
  exact (inferInstance : Injective (∏ᶜ F))

/-- Every torsor under an injective abelian sheaf `H` lies in the same isomorphism class as
the trivial `H`-torsor, the first cohomology of `H` being zero. -/
private lemma abelianTorsor_class_eq_trivial
    {C : Type*} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
    (H : Sheaf J AddCommGrpCat.{u}) [Injective H]
    (F : Stacks.Cohomology.Torsors.AbelianTorsor H) :
    Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid H) F =
      Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid H)
        ⟨trivialTorsor (Stacks.Cohomology.Torsors.abelianSheafAsGroupSheaf H),
          trivialTorsor_isTorsor (Stacks.Cohomology.Torsors.abelianSheafAsGroupSheaf H)⟩ := by
  apply (Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1 H).injective
  rw [Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_trivial]
  exact Subsingleton.elim _ _

open Opposite in
/-- A family `s` of sections of a presheaf `F` over the vertex of a cone `c` on `D` is the
restriction of no family of sections over a single stage `D.obj i`, provided that for each
`i` some member of `s` is separated by two maps into `c.pt` that agree over `D.obj i`. -/
private lemma not_exists_pi_section_of_separating_sections
    {C : Type u} [Category.{v} C] {I : Type w} [Category I]
    (F : Cᵒᵖ ⥤ Type t) (D : I ⥤ C) (c : Cone D)
    {A : Type*} (s : A → F.obj (op c.pt))
    (h : ∀ i, ∃ (a : A) (V : C) (f g : V ⟶ c.pt),
      f ≫ c.π.app i = g ≫ c.π.app i ∧ F.map f.op (s a) ≠ F.map g.op (s a)) :
    ¬ ∃ (i : I) (t : A → F.obj (op (D.obj i))),
      ∀ a, F.map (c.π.app i).op (t a) = s a := by
  rintro ⟨i, t, ht⟩
  obtain ⟨a, V, f, g, hfg, hne⟩ := h i
  apply hne
  rw [← ht a]
  change (F.map (c.π.app i).op ≫ F.map f.op) (t a) =
    (F.map (c.π.app i).op ≫ F.map g.op) (t a)
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, hfg]

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

section
noncomputable section
universe uF vF wF uC hC uX hX uY hY

open Opposite

/-- For a full functor `K` out of `colimit F` over a filtered index category, a morphism
between the `K`-images of `a : F.obj i` and `b : F.obj j` is `K` applied to a morphism
between the pullbacks of `a` and `b` to a common later stage `k`. -/
private lemma exists_stage_map_of_full
    {I : Type vF} [Category.{wF} I] [IsFiltered I]
    (F : I ⥤ Cat.{max uF vF wF, max uF vF wF}) [HasColimit F]
    [HasColimit (F ⋙ CategoryTheory.nerveFunctor.{max uF vF wF, max uF vF wF})]
    {C : Type*} [Category C] (K : (colimit F : Cat) ⥤ C) [K.Full]
    (i j : I) (a : F.obj i) (b : F.obj j)
    (f : K.obj ((colimit.ι F i).toFunctor.obj a) ⟶
      K.obj ((colimit.ι F j).toFunctor.obj b)) :
    ∃ (k : I) (s : i ⟶ k) (t : j ⟶ k)
      (g : (F.map s).toFunctor.obj a ⟶ (F.map t).toFunctor.obj b),
      HEq (((colimit.ι F k).toFunctor ⋙ K).map g) f := by
  obtain ⟨k, s, t, g, hg⟩ := Cat.exists_stage_map_of_colimit.{uF, vF, wF} F i j a b (K.preimage f)
  refine ⟨k, s, t, g, ?_⟩
  exact (Cat.map_heq_of_eq K
    (Functor.congr_obj (congrArg Cat.Hom.toFunctor (colimit.w F s)) a)
    (Functor.congr_obj (congrArg Cat.Hom.toFunctor (colimit.w F t)) b) hg).trans
      (heq_of_eq (K.map_preimage f))

/-- For a fibered `p` whose comparison functor at the cone `c` is full, a morphism between the
restrictions to `c.pt` of split fibre objects over `D.obj i` and `D.obj j` is the
restriction of a morphism between their pullbacks to a common stage of the cofiltered `D`. -/
private lemma exists_split_stage_map
    {C : Type uC} [Category.{hC} C] {Y : Type uY} [Category.{hY} Y]
    (p : Y ⥤ C) [p.IsFibered]
    {I : Type vF} [Category.{wF} I] [IsCofiltered I]
    (D : I ⥤ C) (c : Cone D) [(Deformation.Artin.colimitComparison p D c).Full]
    (i j : I) (a : p.SplitFiber (D.obj i)) (b : p.SplitFiber (D.obj j))
    (f : (Functor.SplitFiber.restrict p (c.π.app i)).obj a ⟶
      (Functor.SplitFiber.restrict p (c.π.app j)).obj b) :
    ∃ (k : I) (s : k ⟶ i) (t : k ⟶ j)
      (g : (Functor.SplitFiber.restrict p (D.map s)).obj a ⟶
        (Functor.SplitFiber.restrict p (D.map t)).obj b),
      HEq ((Functor.SplitFiber.restrict p (c.π.app k)).map g) f := by
  let F := Deformation.Artin.fiberDiagram p D
  let K := Deformation.Artin.colimitComparison p D c
  let ei := Deformation.Artin.colimitComparison_ι p D c i
  let ej := Deformation.Artin.colimitComparison_ι p D c j
  let f' := eqToHom (Functor.congr_obj ei
      (AsSmall.up.{hY, max uC hC uY, max vF wF}.obj a)) ≫
    f ≫ eqToHom (Functor.congr_obj ej
      (AsSmall.up.{hY, max uC hC uY, max vF wF}.obj b)).symm
  obtain ⟨k, s, t, g, hg⟩ :=
    exists_stage_map_of_full.{max uC hC uY hY, vF, wF} F K
      (op i) (op j)
      (AsSmall.up.{hY, max uC hC uY, max vF wF}.obj a)
      (AsSmall.up.{hY, max uC hC uY, max vF wF}.obj b) f'
  refine ⟨k.unop, s.unop, t.unop,
    AsSmall.down.{hY, max uC hC uY, max vF wF}.map g, ?_⟩
  have he := Functor.hcongr_hom (Deformation.Artin.colimitComparison_ι p D c k.unop) g
  exact (he.symm.trans hg).trans (by
    dsimp only [f']
    exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq (C := p.Fiber c.pt) _ _))

/-- The morphism into the pullback fibre induced by a lift `δ` of `f : U ⟶ V` is unchanged, up
to heterogeneous equality, when `f` is replaced by an equal morphism `g`. -/
private lemma toPullbackFiber_heq {C X : Type*} [Category C] [Category X]
    (p : X ⥤ C) [p.IsFibered] {U V : C} (x : p.Fiber U) (y : p.Fiber V)
    (f g : U ⟶ V) (e : f = g) (δ : x.1 ⟶ y.1)
    [p.IsHomLift f δ] [p.IsHomLift g δ] :
    HEq (Functor.toPullbackFiber p x y f δ) (Functor.toPullbackFiber p x y g δ) := by
  subst g
  rfl

attribute [local implicit_reducible] Functor.SplitFiber.restrict Bicategory.InducedBicategory

/-- Along a cofiltered diagram, a morphism from `x` in the fibre over the cone point to an object
at stage `i` and a morphism from `G.obj x` to an object at stage `j` both factor through a
single object in the fibre at a common stage `k` mapping to `i` and to `j`. -/
private lemma factor_through_stage_with_projection
    {C : Type uC} [Category.{hC} C]
    {X : Type uX} [Category.{hX} X] {Y : Type uY} [Category.{hY} Y]
    (pX : X ⥤ C) (pY : Y ⥤ C) [pX.IsFibered] [pY.IsFibered]
    (hY : pY.IsFiberedInGroupoids) (G : X ⥤ Y) (hG : G ⋙ pY = pX)
    {I : Type vF} [Category.{wF} I] [IsCofiltered I]
    (D : I ⥤ C) (c : Cone D) [(Deformation.Artin.colimitComparison pY D c).Full]
    (i j : I) (x : pX.Fiber c.pt) (xi : pX.Fiber (D.obj i))
    (yj : pY.Fiber (D.obj j)) (δ : x.1 ⟶ xi.1) (γ : G.obj x.1 ⟶ yj.1)
    [pX.IsHomLift (c.π.app i) δ] [pY.IsHomLift (c.π.app j) γ] :
    ∃ (k : I) (s : k ⟶ i) (t : k ⟶ j) (xk : pX.Fiber (D.obj k))
      (d : xk.1 ⟶ xi.1) (δk : x.1 ⟶ xk.1) (γk : G.obj xk.1 ⟶ yj.1),
      pX.IsHomLift (D.map s) d ∧ δk ≫ d = δ ∧
      pX.IsHomLift (c.π.app k) δk ∧ pY.IsHomLift (D.map t) γk ∧
      G.map δk ≫ γk = γ := by
  let z : pY.Fiber c.pt := ⟨G.obj x.1, (Functor.congr_obj hG x.1).trans x.2⟩
  let yi : pY.Fiber (D.obj i) := ⟨G.obj xi.1, (Functor.congr_obj hG xi.1).trans xi.2⟩
  let a : pY.SplitFiber (D.obj i) := ⟨D.obj i, yi, 𝟙 _⟩
  let b : pY.SplitFiber (D.obj j) := ⟨D.obj j, yj, 𝟙 _⟩
  have hδY : pY.IsHomLift (c.π.app i) (G.map δ) :=
    Functor.isHomLift_map_of_comp_eq hG _ δ
  let : pY.IsHomLift (c.π.app i ≫ 𝟙 _) (G.map δ) := by simpa using hδY
  let : pY.IsHomLift (c.π.app j ≫ 𝟙 _) γ := by simpa using
    (inferInstance : pY.IsHomLift (c.π.app j) γ)
  let η := Functor.toPullbackFiber pY z yi (c.π.app i ≫ 𝟙 _) (G.map δ)
  let θ := Functor.toPullbackFiber pY z yj (c.π.app j ≫ 𝟙 _) γ
  let := hY.fiber_isGroupoid c.pt
  let f := inv η ≫ θ
  obtain ⟨k, s, t, g, hg⟩ := exists_split_stage_map pY D c i j a b f
  let si := D.map s ≫ 𝟙 (D.obj i)
  let tj := D.map t ≫ 𝟙 (D.obj j)
  change (Functor.pullbackFiber pY yi si ⟶ Functor.pullbackFiber pY yj tj) at g
  have hi : c.π.app k ≫ si = c.π.app i ≫ 𝟙 _ := by simp [si, c.w s]
  have hj : c.π.app k ≫ tj = c.π.app j ≫ 𝟙 _ := by simp [tj, c.w t]
  let : pY.IsHomLift (c.π.app k ≫ si) (G.map δ) := hi.symm ▸ inferInstance
  let : pY.IsHomLift (c.π.app k ≫ tj) γ := hj.symm ▸ inferInstance
  let ηk := Functor.toPullbackFiber pY z yi (c.π.app k ≫ si) (G.map δ)
  let θk := Functor.toPullbackFiber pY z yj (c.π.app k ≫ tj) γ
  have hη := toPullbackFiber_heq pY z yi _ _ hi (G.map δ)
  have hθ := toPullbackFiber_heq pY z yj _ _ hj γ
  have hηg : ηk ≫ (Functor.SplitFiber.restrict pY (c.π.app k)).map
      (X := (Functor.SplitFiber.restrict pY (D.map s)).obj a)
      (Y := (Functor.SplitFiber.restrict pY (D.map t)).obj b) g = θk := by
    apply eq_of_heq
    have h := Cat.comp_heq_of_eq (rfl : z = z)
      (congrArg (Functor.pullbackFiber pY yi) hi)
      (congrArg (Functor.pullbackFiber pY yj) hj) hη hg
    exact h.trans ((heq_of_eq (by simp [f] : η ≫ f = θ)).trans hθ.symm)
  let xk := Functor.pullbackFiber pX xi si
  let d := Functor.IsPreFibered.pullbackMap xi.2 si
  let δk := Functor.IsStronglyCartesian.map pX si d
    (g := c.π.app k) (by simpa using hi.symm) δ
  let zk : pY.Fiber (D.obj k) :=
    ⟨G.obj xk.1, (Functor.congr_obj hG xk.1).trans xk.2⟩
  let : pY.IsHomLift si (G.map d) := Functor.isHomLift_map_of_comp_eq hG si d
  let ηs := Functor.toPullbackFiber pY zk yi si (G.map d)
  let γk := Functor.Fiber.fiberInclusion.map ηs ≫
    Functor.Fiber.fiberInclusion.map g ≫ Functor.IsPreFibered.pullbackMap yj.2 tj
  have hδk : pX.IsHomLift (c.π.app k) δk := inferInstance
  let : pY.IsHomLift (c.π.app k) (G.map δk) :=
    Functor.isHomLift_map_of_comp_eq hG _ δk
  have he : G.map δk ≫ Functor.Fiber.fiberInclusion.map ηs =
      Functor.Fiber.fiberInclusion.map ηk ≫ Functor.pullbackFiberProj yi si (c.π.app k) := by
    apply Functor.IsStronglyCartesian.ext pY si
      (Functor.IsPreFibered.pullbackMap yi.2 si) (c.π.app k)
    dsimp only [ηs, ηk]
    simp only [Category.assoc, Functor.toPullbackFiber_fac, Functor.pullbackFiberProj_fac]
    change G.map δk ≫ G.map d = G.map δ
    rw [← G.map_comp, Functor.IsStronglyCartesian.fac]
  refine ⟨k, s, t, xk, d, δk, γk, ?_, ?_, hδk, ?_, ?_⟩
  · simpa [si] using (inferInstance : pX.IsHomLift si d)
  · exact Functor.IsStronglyCartesian.fac pX si d _ δ
  · have h : pY.IsHomLift (𝟙 (D.obj k) ≫ 𝟙 (D.obj k) ≫ tj) γk := by
      dsimp only [γk]
      infer_instance
    simpa [tj] using h
  · dsimp only [γk]
    rw [← Category.assoc, he]
    have hfac := Functor.SplitFiber.restrictHom_fac (p := pY) (c.π.app k)
      (o := (Functor.SplitFiber.restrict pY (D.map s)).obj a)
      (o' := (Functor.SplitFiber.restrict pY (D.map t)).obj b) g
    change Functor.Fiber.fiberInclusion.map
      ((Functor.SplitFiber.restrict pY (c.π.app k)).map
        (X := (Functor.SplitFiber.restrict pY (D.map s)).obj a)
        (Y := (Functor.SplitFiber.restrict pY (D.map t)).obj b) g) ≫
        Functor.IsPreFibered.pullbackMap yj.2 (c.π.app k ≫ tj) =
      Functor.pullbackFiberProj yi si (c.π.app k) ≫
        Functor.Fiber.fiberInclusion.map g ≫ Functor.IsPreFibered.pullbackMap yj.2 tj at hfac
    rw [Category.assoc, ← hfac, ← Functor.map_comp_assoc, hηg]
    exact Functor.toPullbackFiber_fac pY z yj _ γ

end
end

attribute [local implicit_reducible] AlgebraicGeometry.Stack.terminalCFG
    AlgebraicGeometry.Stack.toTerminalCFG CategoryTheory.ShrinkHoms.functor
    CategoryTheory.Bicategory.InducedBicategory in
/-- A category fibred in groupoids over the big fppf site of `S` all of whose fibres are nonempty
and connected has its structure morphism to the final object limit preserving on objects. -/
private theorem isLimitPreservingOnObjects_of_connected_fibers
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (hne : ∀ U, Nonempty (𝒳.val.p.Fiber U))
    (hconn : ∀ U (x y : 𝒳.val.p.Fiber U), Nonempty (x ≅ y)) :
    AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects.{u, v, w, u, u + 1} B S hS 𝒳
      (AlgebraicGeometry.Stack.terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom
        (AlgebraicGeometry.Stack.toTerminalCFG B S hS 𝒳)) := by
  classical
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  intro I _ _ D c hc i y x γ hγ
  let F := AlgebraicGeometry.BigAffineFppf.inclusion B S hS
  let f := F.map (c.π.app i)
  obtain ⟨x'⟩ := hne (F.obj (D.obj i))
  let xU := (Functor.chosenPullbacks 𝒳.val.p).obj f x'
  obtain ⟨e⟩ := hconn (F.obj c.pt) xU x
  let β := Functor.Fiber.fiberInclusion.map e.hom
  let δ := (Functor.chosenPullbacks 𝒳.val.p).map f x'
  have hy : (F.obj (D.obj i)) = y.1 := y.2.symm
  let γ' : 𝒳.val.p.obj x'.1 ⟶ y.1 := eqToHom (x'.2.trans hy)
  refine ⟨i, 𝟙 i, x', xU, δ, β, γ', ?_, ?_, ?_, ?_, ?_⟩
  · exact (Functor.chosenPullbacks 𝒳.val.p).isStronglyCartesian f x'
  · exact e.hom.2
  · exact Functor.map_isIso _ e.hom
  · change (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)).IsStronglyCartesian
      (F.map (D.map (𝟙 i))) γ'
    have : (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)).IsHomLift
        (F.map (D.map (𝟙 i))) γ' := by
      simpa [γ', hy, Functor.map_id] using
        IsHomLift.of_fac' (𝟭 (AlgebraicGeometry.BigFppfOver B S hS))
          (𝟙 (F.obj (D.obj i))) γ' x'.2 y.2 (by change γ' = _; simp [γ'])
    exact Functor.isFiberedInGroupoids_id.isStronglyCartesian_homLift _ _
  · have key {A A' M X Y Z Bo : AlgebraicGeometry.BigFppfOver B S hS} (g : X ⟶ Y)
        (p₁ : A = X) (p₂ : Y = Z) (p₃ : Z = Bo) (p₄ : A = M) (p₅ : M = A')
        (p₆ : A' = X) (p₇ : Y = Bo) :
        (eqToHom p₁ ≫ g ≫ eqToHom p₂) ≫ eqToHom p₃ =
          (eqToHom p₄ ≫ 𝟙 M ≫ eqToHom p₅) ≫ eqToHom p₆ ≫ g ≫ eqToHom p₇ := by
      simp
    change 𝒳.val.p.map δ ≫ γ' = 𝒳.val.p.map β ≫ γ
    have hδ := IsHomLift.fac' 𝒳.val.p f δ
    have hβ := IsHomLift.fac' 𝒳.val.p (𝟙 (F.obj c.pt)) β
    have hγ' := IsHomLift.fac'
      (AlgebraicGeometry.Stack.terminalCFG B S hS).val.p f γ
    change γ = _ at hγ'
    rw [hδ, hβ, hγ']
    simp only [γ']
    exact key f _ _ _ _ _ _ _

section

open Opposite

noncomputable section

/-- The Boolean powers of `R`: the functor sending `n : ℕ` to the ring `(Fin n → Bool) → R` of
`2 ^ n` copies of `R`, where `m ⟶ n` acts by evaluating at the restriction of a Boolean
string of length `n` to its first `m` entries. -/
private def booleanPowerDiagram (R : CommRingCat.{u}) : ℕ ⥤ CommRingCat.{u} where
  obj n := CommRingCat.of ((Fin n → Bool) → R)
  map {m n} f := CommRingCat.ofHom
    (RingHom.pi fun b => Pi.evalRingHom _ (b ∘ Fin.castLE (leOfHom f)))
  map_id n := by ext a b; rfl
  map_comp f g := by ext a b; rfl

/-- Evaluation at a Boolean string `b : ℕ → Bool`, as a cocone on the Boolean powers of `R` with
point `R`: at stage `n` it evaluates a function at the truncation of `b` to `Fin n`. -/
private def booleanPowerEvaluation (R : CommRingCat.{u}) (b : ℕ → Bool) :
    Cocone (booleanPowerDiagram R) where
  pt := R
  ι := {
    app n := CommRingCat.ofHom (Pi.evalRingHom _ (fun i : Fin n => b i))
    naturality := by intro m n f; ext a; rfl }

/-- The `n`-th Boolean coordinate of the colimit of the Boolean powers of `R`: the map from
`Bool → R` sending `a` to the stage `n + 1` function whose value at `b` is `a (b n)`. -/
private def booleanPowerCoordinate (R : CommRingCat.{u}) (n : ℕ) :
    CommRingCat.of (Bool → R) ⟶ colimit (booleanPowerDiagram R) :=
  CommRingCat.ofHom (RingHom.pi fun b : Fin (n + 1) → Bool =>
    Pi.evalRingHom _ (b (Fin.last n))) ≫ colimit.ι (booleanPowerDiagram R) (n + 1)

attribute [local implicit_reducible] booleanPowerCoordinate booleanPowerDiagram
    booleanPowerEvaluation in
/-- Evaluation at `b : ℕ → Bool` carries the `n`-th Boolean coordinate of the colimit to
evaluation of `Bool → R` at the bit `b n`. -/
private lemma booleanPowerCoordinate_evaluation (R : CommRingCat.{u}) (b : ℕ → Bool)
    (n : ℕ) :
    booleanPowerCoordinate R n ≫
      colimit.desc (booleanPowerDiagram R) (booleanPowerEvaluation R b) =
      CommRingCat.ofHom (Pi.evalRingHom _ (b n)) := by
  rw [booleanPowerCoordinate, Category.assoc, colimit.ι_desc]
  rfl

/-- Boolean strings agreeing in all coordinates below `n` induce maps out of the colimit of the
Boolean powers of `R` that agree on the image of the stage `n`. -/
private lemma booleanPowerEvaluation_eq_at (R : CommRingCat.{u}) (b b' : ℕ → Bool)
    (n : ℕ) (h : ∀ k < n, b k = b' k) :
    colimit.ι (booleanPowerDiagram R) n ≫
        colimit.desc (booleanPowerDiagram R) (booleanPowerEvaluation R b) =
      colimit.ι (booleanPowerDiagram R) n ≫
        colimit.desc (booleanPowerDiagram R) (booleanPowerEvaluation R b') := by
  simp only [colimit.ι_desc]
  ext a
  change a (fun i : Fin n => b i) = a (fun i : Fin n => b' i)
  congr 1
  funext i
  exact h i i.isLt
/-- The cone of the spectra of the Boolean powers of `R`, with point the spectrum of their
colimit. -/
private def booleanPowerLimitCone (R : CommRingCat.{u}) :
    Cone ((booleanPowerDiagram R).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (colimit.cocone (booleanPowerDiagram R)).op

/-- The spectrum of the colimit of the Boolean powers of `R` is the limit of their spectra. -/
private def booleanPowerLimitConeIsLimit (R : CommRingCat.{u}) :
    IsLimit (booleanPowerLimitCone R) :=
  isLimitOfPreserves Scheme.Spec (colimit.isColimit (booleanPowerDiagram R)).op
open Cardinal in
/-- The Boolean power `(Fin n → Bool) → R` has cardinality at most `max ℵ₀ #R`. -/
private lemma cardinal_booleanPowerDiagram_le (R : CommRingCat.{u}) (n : ℕ) :
    #((booleanPowerDiagram R).obj n) ≤ max ℵ₀ #R := by
  change #((Fin n → Bool) → R) ≤ _
  rw [mk_arrow, mk_fintype (Fin n → Bool)]
  simpa only [lift_uzero, lift_natCast] using (power_nat_le_max (c := #R)
    (n := Fintype.card (Fin n → Bool))).trans_eq (max_comm _ _)

open Cardinal in
/-- The colimit of the Boolean powers of `R` has cardinality at most `max ℵ₀ #R`. -/
private lemma cardinal_booleanPowerColimit_le (R : CommRingCat.{u}) :
    #(colimit (booleanPowerDiagram R) : CommRingCat.{u}) ≤ max ℵ₀ #R := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget CommRingCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let q : (Σ n, (booleanPowerDiagram R).obj n) →
      (colimit (booleanPowerDiagram R) : CommRingCat.{u}) :=
    fun x => colimit.ι (booleanPowerDiagram R) x.1 x.2
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨n, a, h⟩ := Concrete.colimit_exists_rep (booleanPowerDiagram R) x
    exact ⟨⟨n, a⟩, h⟩
  apply (mk_le_of_surjective hq).trans
  rw [mk_sigma]
  apply (sum_le_sum _ (fun _ : ℕ => max ℵ₀ #R)
    (cardinal_booleanPowerDiagram_le R)).trans
  simp [sum_const, aleph0_mul_eq (le_max_left _ _)]
/-- If `Spec R` lies in the big fppf site `B` and `R'` has cardinality at most `max ℵ₀ #R`, then
`Spec R'` lies in `B` too. -/
private lemma contains_spec_of_card_le (B : AlgebraicGeometry.BigFppfSite.{u})
    {R R' : CommRingCat.{u}} (hR : B.Contains (Spec R))
    (h : Cardinal.mk R' ≤ max Cardinal.aleph0 (Cardinal.mk R)) :
    B.Contains (Spec R') := by
  change (Spec R').size < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff (h.trans_lt ((Scheme.size_Spec R) ▸ hR))

/-- If `Spec R` lies in the big fppf site `B`, so does the spectrum of the colimit of the Boolean
powers of `R`. -/
private lemma booleanPowerLimitCone_mem
    (B : AlgebraicGeometry.BigFppfSite.{u}) (R : CommRingCat.{u}) (hR : B.Contains (Spec R)) :
    B.Contains (Spec (colimit (booleanPowerDiagram R))) :=
  contains_spec_of_card_le B hR (cardinal_booleanPowerColimit_le R)
attribute [local implicit_reducible] booleanPowerCoordinate booleanPowerDiagram
    booleanPowerEvaluation booleanPowerLimitCone in
/-- The diagonal ring map from `R` into its Boolean power `(Fin n → Bool) → R`, sending `a` to
the function constant at `a`. -/
private def booleanPowerUnit (R : CommRingCat.{u}) (n : ℕ) :
    R ⟶ (booleanPowerDiagram R).obj n :=
  CommRingCat.ofHom (RingHom.pi fun _ => RingHom.id R)

/-- The diagonals from `R` into its Boolean powers are compatible with the transition maps. -/
private lemma booleanPowerUnit_map (R : CommRingCat.{u}) {m n : ℕ} (f : m ⟶ n) :
    booleanPowerUnit R m ≫ (booleanPowerDiagram R).map f = booleanPowerUnit R n := by
  ext a
  rfl

/-- The ring map from `R` to the colimit of its Boolean powers induced by the diagonals. -/
private def booleanPowerColimitUnit (R : CommRingCat.{u}) :
    R ⟶ colimit (booleanPowerDiagram R) :=
  booleanPowerUnit R 0 ≫ colimit.ι (booleanPowerDiagram R) 0

/-- The diagonal into the Boolean power at stage `n`, followed by the inclusion of that stage into
the colimit, is the map from `R` to the colimit. -/
private lemma booleanPowerUnit_ι (R : CommRingCat.{u}) (n : ℕ) :
    booleanPowerUnit R n ≫ colimit.ι (booleanPowerDiagram R) n =
      booleanPowerColimitUnit R := by
  rw [booleanPowerColimitUnit, ← booleanPowerUnit_map R (homOfLE (Nat.zero_le n)),
    Category.assoc, colimit.w]

/-- If `Spec R` lies in the big fppf site `B`, so does the spectrum of each Boolean power of `R`.
If `Spec R` lies in the big fppf site `B`, so does the spectrum of each Boolean power of `R`. -/
private lemma booleanPowerDiagram_mem (B : AlgebraicGeometry.BigFppfSite.{u})
    (R : CommRingCat.{u}) (hR : B.Contains (Spec R)) (n : ℕ) :
    B.Contains (Spec ((booleanPowerDiagram R).obj n)) :=
  contains_spec_of_card_le B hR (cardinal_booleanPowerDiagram_le R n)

/-- A spectrum, with its structure morphism to `S`, regarded as an object of the big affine fppf
site of `S`. -/
private def affineSpecOver (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (R : CommRingCat.{u}) (hR : B.Contains (Spec R))
    (f : Spec R ⟶ S) : AlgebraicGeometry.BigAffineFppf B S hS :=
  ⟨siteObject B S hS hR f, by change IsAffine (Spec R); infer_instance⟩

/-- A ring map `φ : R ⟶ R'` compatible with the structure morphisms to `S` induces the morphism
`Spec φ` from `Spec R'` to `Spec R` in the big affine fppf site of `S`. -/
private def affineSpecOverMap (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {R R' : CommRingCat.{u}}
    {hR : B.Contains (Spec R)} {hR' : B.Contains (Spec R')}
    {f : Spec R ⟶ S} {f' : Spec R' ⟶ S}
    (φ : R ⟶ R') (hφ : Scheme.Spec.map φ.op ≫ f = f') :
    affineSpecOver B S hS R' hR' f' ⟶ affineSpecOver B S hS R hR f :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk (Scheme.Spec.map φ.op))
    (by apply ObjectProperty.hom_ext; exact hφ))

/-- The cofiltered diagram of the spectra of the Boolean powers of `R` in the big affine fppf site
of `S`, each lying over `S` through the diagonal from `R` and a fixed `f : Spec R ⟶ S`. -/
private def booleanPowerAffineDiagram
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (R : CommRingCat.{u}) (hR : B.Contains (Spec R)) (f : Spec R ⟶ S) :
    ℕᵒᵖ ⥤ AlgebraicGeometry.BigAffineFppf B S hS where
  obj n := affineSpecOver B S hS ((booleanPowerDiagram R).obj n.unop)
    (booleanPowerDiagram_mem B R hR n.unop)
    (Scheme.Spec.map (booleanPowerUnit R n.unop).op ≫ f)
  map g := affineSpecOverMap B S hS ((booleanPowerDiagram R).map g.unop) (by
    rw [← Category.assoc, ← Scheme.Spec.map_comp, ← op_comp, booleanPowerUnit_map])
  map_id n := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    simp [affineSpecOverMap, affineSpecOver, AlgebraicGeometry.siteObject,
      AlgebraicGeometry.BigFppfSite.obj]
  map_comp g h := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    simp [affineSpecOverMap, affineSpecOver, AlgebraicGeometry.siteObject,
      AlgebraicGeometry.BigFppfSite.obj]

/-- The cone over the spectra of the Boolean powers of `R` in the big affine fppf site of `S`,
with point the spectrum of their colimit, over `S` through the diagonal and `f`. -/
private def booleanPowerAffineCone
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (R : CommRingCat.{u}) (hR : B.Contains (Spec R)) (f : Spec R ⟶ S) :
    Cone (booleanPowerAffineDiagram B S hS R hR f) where
  pt := affineSpecOver B S hS (colimit (booleanPowerDiagram R))
    (booleanPowerLimitCone_mem B R hR)
    (Scheme.Spec.map (booleanPowerColimitUnit R).op ≫ f)
  π := {
    app n := affineSpecOverMap B S hS (colimit.ι (booleanPowerDiagram R) n.unop) (by
      rw [← Category.assoc, ← Scheme.Spec.map_comp, ← op_comp, booleanPowerUnit_ι])
    naturality := by
      intro i j g
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      change 𝟙 _ ≫ Scheme.Spec.map (colimit.ι (booleanPowerDiagram R) j.unop).op =
        Scheme.Spec.map (colimit.ι (booleanPowerDiagram R) i.unop).op ≫
          Scheme.Spec.map ((booleanPowerDiagram R).map g.unop).op
      simp only [Category.id_comp, ← Scheme.Spec.map_comp, ← op_comp, colimit.w] }

/-- The spectrum of the colimit of the Boolean powers of `R` is, as a scheme over `S`, the limit
of the spectra of the stages. -/
private def booleanPowerAffineConeIsLimit
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (R : CommRingCat.{u}) (hR : B.Contains (Spec R)) (f : Spec R ⟶ S) :
    IsLimit ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).mapCone
      (booleanPowerAffineCone B S hS R hR f)) :=
  booleanPowerLimitConeIsLimit R

/-- Evaluation at a Boolean string `b : ℕ → Bool` is a retraction of the map from `R` to the
colimit of its Boolean powers. -/
private lemma booleanPowerColimitUnit_evaluation (R : CommRingCat.{u}) (b : ℕ → Bool) :
    booleanPowerColimitUnit R ≫
        colimit.desc (booleanPowerDiagram R) (booleanPowerEvaluation R b) = 𝟙 R := by
  rw [booleanPowerColimitUnit, Category.assoc, colimit.ι_desc]
  ext a
  rfl

attribute [local implicit_reducible] affineSpecOver affineSpecOverMap booleanPowerAffineCone
    booleanPowerDiagram booleanPowerEvaluation in
/-- Evaluation at a Boolean string `b : ℕ → Bool`, as a morphism over `S` from `Spec R` to the
point of the cone over the spectra of the Boolean powers of `R`. -/
private def booleanPowerAffineEvaluation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (R : CommRingCat.{u}) (hR : B.Contains (Spec R)) (f : Spec R ⟶ S)
    (b : ℕ → Bool) :
    affineSpecOver B S hS R hR f ⟶ (booleanPowerAffineCone B S hS R hR f).pt :=
  affineSpecOverMap B S hS
    (colimit.desc (booleanPowerDiagram R) (booleanPowerEvaluation R b)) (by
      rw [← Category.assoc, ← Scheme.Spec.map_comp, ← op_comp,
        booleanPowerColimitUnit_evaluation]
      simp)

attribute [local implicit_reducible] booleanPowerAffineCone booleanPowerAffineEvaluation
    booleanPowerDiagram booleanPowerEvaluation in
/-- Evaluation at Boolean strings agreeing in all coordinates below `n` gives morphisms with the
same composite to the stage `n` of the cone over the spectra of the Boolean powers of `R`. -/
private lemma booleanPowerAffineEvaluation_eq_at
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (R : CommRingCat.{u}) (hR : B.Contains (Spec R)) (f : Spec R ⟶ S)
    (b b' : ℕ → Bool) (n : ℕ) (h : ∀ k < n, b k = b' k) :
    booleanPowerAffineEvaluation B S hS R hR f b ≫
        (booleanPowerAffineCone B S hS R hR f).π.app (op n) =
      booleanPowerAffineEvaluation B S hS R hR f b' ≫
        (booleanPowerAffineCone B S hS R hR f).π.app (op n) := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Scheme.Spec.map _ ≫ Scheme.Spec.map _ =
    Scheme.Spec.map _ ≫ Scheme.Spec.map _
  rw [← Scheme.Spec.map_comp, ← Scheme.Spec.map_comp, ← op_comp, ← op_comp,
    booleanPowerEvaluation_eq_at R b b' n h]

/-- A nonempty scheme `S` receives a morphism `Spec R ⟶ S` whose source lies in the big fppf
site `B` and whose ring `R` is nontrivial. -/
private lemma exists_nontrivial_affine_over
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [Nonempty S] :
    ∃ (R : CommRingCat.{u}) (_ : Spec R ⟶ S), B.Contains (Spec R) ∧ Nontrivial R := by
  classical
  obtain ⟨x⟩ := (inferInstance : Nonempty S)
  obtain ⟨y, hy⟩ := S.affineCover.covers x
  let U := S.affineCover.X (S.affineCover.idx x)
  let f : Spec Γ(U, ⊤) ⟶ S := U.isoSpec.inv ≫ S.affineCover.f (S.affineCover.idx x)
  refine ⟨Γ(U, ⊤), f, Scheme.size_lt_of_isOpenImmersion f hS, ?_⟩
  apply PrimeSpectrum.nonempty_iff_nontrivial.mp
  exact ⟨U.isoSpec.hom y⟩
end

end

section

open Opposite

noncomputable section

/-- The structure sheaf of the big fppf site over `S` with its multiplication forgotten, as a
sheaf of abelian groups. -/
private abbrev additiveStructureSheaf
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u} :=
  (sheafCompose _ (forget₂ RingCat AddCommGrpCat)).obj
    (AlgebraicGeometry.BigFppfOver.structureSheaf B S hS)

/-- The global function on `Spec (colimit (booleanPowerDiagram R))` cut out by the `n`-th
Boolean coordinate: the image of `fun b : Bool => if b then 1 else 0` under the `n`-th
coordinate map `booleanPowerCoordinate R n`. -/
private def booleanPowerSection
    (R : CommRingCat.{u}) (n : ℕ) : Γ(Spec (colimit (booleanPowerDiagram R)), ⊤) :=
  (Scheme.ΓSpecIso (colimit (booleanPowerDiagram R))).inv
    (booleanPowerCoordinate R n (fun b : Bool => if b then 1 else 0))

/-- Restricting `booleanPowerSection R n` along evaluation of the Boolean coordinates at
`b : ℕ → Bool` gives the global function `if b n then 1 else 0` on `Spec R`. -/
private lemma booleanPowerSection_evaluation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (R : CommRingCat.{u}) (hR : B.Contains (Spec R)) (f : Spec R ⟶ S)
    (b : ℕ → Bool) (n : ℕ) :
    (additiveStructureSheaf B S hS).obj.map
        ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map
          (booleanPowerAffineEvaluation B S hS R hR f b)).op
        (booleanPowerSection R n) =
      (Scheme.ΓSpecIso R).inv (if b n then 1 else 0) := by
  let e := colimit.desc (booleanPowerDiagram R) (booleanPowerEvaluation R b)
  change (Spec.map e).appTop
    ((Scheme.ΓSpecIso (colimit (booleanPowerDiagram R))).inv
      (booleanPowerCoordinate R n (fun b : Bool => if b then 1 else 0))) = _
  have he := congrArg (fun g : colimit (booleanPowerDiagram R) ⟶ Γ(Spec R, ⊤) =>
    g (booleanPowerCoordinate R n (fun b : Bool => if b then 1 else 0)))
    (Scheme.ΓSpecIso_inv_naturality e)
  refine he.symm.trans ?_
  apply congrArg ((Scheme.ΓSpecIso R).inv)
  exact congrArg (fun g : CommRingCat.of (Bool → R) ⟶ R =>
    g (fun b : Bool => if b then 1 else 0)) (booleanPowerCoordinate_evaluation R b n)

attribute [local implicit_reducible] affineSpecOver booleanPowerAffineCone
    booleanPowerAffineDiagram booleanPowerAffineEvaluation booleanPowerSection in
/-- For nontrivial `R` and a morphism `η` out of the additive structure sheaf that is injective
on sections over `Spec R`, no single stage of the Boolean power tower over `Spec R` carries
sections of `H` restricting to `η (booleanPowerSection R n)` for every `n`. -/
private lemma not_exists_booleanPowerAffine_pi_section
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (R : CommRingCat.{u}) [Nontrivial R] (hR : B.Contains (Spec R)) (f : Spec R ⟶ S)
    (H : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (η : (additiveStructureSheaf B S hS).obj ⟶ H)
    (hη : Function.Injective (η.app (op (siteObject B S hS hR f)))) :
    ¬ ∃ (i : ℕᵒᵖ)
      (a : ℕ → H.obj (op ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
        ((booleanPowerAffineDiagram B S hS R hR f).obj i)))),
      ∀ n, H.map ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map
          ((booleanPowerAffineCone B S hS R hR f).π.app i)).op (a n) =
        η.app (op ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
          (booleanPowerAffineCone B S hS R hR f).pt)) (booleanPowerSection R n) := by
  let inc := AlgebraicGeometry.BigAffineFppf.inclusion B S hS
  apply not_exists_pi_section_of_separating_sections (H ⋙ forget AddCommGrpCat)
    (booleanPowerAffineDiagram B S hS R hR f ⋙ inc)
    (inc.mapCone (booleanPowerAffineCone B S hS R hR f))
  intro i
  let b : ℕ → Bool := fun k => decide (k = i.unop)
  let e₀ := inc.map (booleanPowerAffineEvaluation B S hS R hR f (fun _ => false))
  let e₁ := inc.map (booleanPowerAffineEvaluation B S hS R hR f b)
  refine ⟨i.unop, inc.obj (affineSpecOver B S hS R hR f), e₀, e₁, ?_, ?_⟩
  · change inc.map _ ≫ inc.map _ = inc.map _ ≫ inc.map _
    rw [← inc.map_comp, ← inc.map_comp]
    congr 1
    apply booleanPowerAffineEvaluation_eq_at
    intro k hk
    simp [b, Nat.ne_of_lt hk]
  · intro h
    have hnat₀ := congrArg (fun g => g (booleanPowerSection R i.unop)) (η.naturality e₀.op)
    have hnat₁ := congrArg (fun g => g (booleanPowerSection R i.unop)) (η.naturality e₁.op)
    dsimp at hnat₀ hnat₁
    change H.map e₀.op (η.app _ (booleanPowerSection R i.unop)) =
      H.map e₁.op (η.app _ (booleanPowerSection R i.unop)) at h
    have he := hη (hnat₀.trans (h.trans hnat₁.symm))
    have he₀ := booleanPowerSection_evaluation B S hS R hR f (fun _ => false) i.unop
    have he₁ := booleanPowerSection_evaluation B S hS R hR f b i.unop
    have h0 : (if (false : Bool) then (1 : R) else 0) = 0 := by simp
    have h1 : (if b i.unop then (1 : R) else 0) = 1 := by simp [b]
    have he' : (Scheme.ΓSpecIso R).inv 0 = (Scheme.ΓSpecIso R).inv 1 :=
      ((congrArg ((Scheme.ΓSpecIso R).inv) h0).symm.trans
        (he₀.symm.trans (he.trans he₁))).trans (congrArg ((Scheme.ΓSpecIso R).inv) h1)
    apply (zero_ne_one : (0 : R) ≠ 1)
    simpa using congrArg ((Scheme.ΓSpecIso R).hom) he'

/-- A monomorphism of sheaves of abelian groups is injective on sections over every object of
the site. -/
private lemma sheaf_mono_app_injective
    {C : Type*} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] {F G : Sheaf J AddCommGrpCat.{u}}
    (η : F ⟶ G) [Mono η] (U : Cᵒᵖ) : Function.Injective (η.hom.app U) := by
  let : Mono η.hom := (sheafToPresheaf J AddCommGrpCat).map_mono η
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the countable product of sheaves and its limits is heavy
/-- Every sequence of sections of `H` over `U` is the family of components of a single section
of the countable product `∏ᶜ fun _ : ℕ => H` over `U`. -/
private lemma exists_product_sheaf_section
    {C : Type*} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] (H : Sheaf J AddCommGrpCat.{u})
    (U : Cᵒᵖ) (s : ℕ → H.obj.obj U) :
    ∃ t : (∏ᶜ fun _ : ℕ => H).obj.obj U,
      ∀ n, (Pi.π (fun _ : ℕ => H) n).hom.app U t = s n := by
  have hP : HasProduct (fun _ : ℕ => H) := inferInstance
  have : HasLimitsOfShape (Discrete ℕ) (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    functorCategoryHasLimitsOfShape
  let F := sheafToPresheaf J AddCommGrpCat ⋙
    (evaluation Cᵒᵖ AddCommGrpCat).obj U ⋙ forget AddCommGrpCat
  have : PreservesLimit (Discrete.functor fun _ : ℕ => H) (sheafToPresheaf J AddCommGrpCat) :=
    inferInstance
  have : PreservesLimit (Discrete.functor fun _ : ℕ => H) F := inferInstance
  have : HasProduct (fun _ : ℕ => F.obj H) := inferInstance
  let e₁ : F.obj (∏ᶜ fun _ : ℕ => H) ≅ ∏ᶜ fun _ : ℕ => F.obj H :=
    PreservesProduct.iso F (fun _ : ℕ => H)
  let e₂ := Types.productIso.{0, u} (fun _ : ℕ => F.obj H)
  refine ⟨e₁.inv (e₂.inv s), fun n => ?_⟩
  have he : e₁.inv ≫ F.map (Pi.π (fun _ : ℕ => H) n) = Pi.π (fun _ : ℕ => F.obj H) n := by
    apply (cancel_epi e₁.hom).1
    rw [Iso.hom_inv_id_assoc,
      show e₁.hom = piComparison F _ from PreservesProduct.iso_hom F (fun _ : ℕ => H),
      piComparison_comp_π]
  have h₂ : Pi.π (fun _ : ℕ => F.obj H) n (e₂.inv s) = s n :=
    Types.productIso_inv_comp_π_apply.{0, u} (fun _ : ℕ => F.obj H) n s
  exact (ConcreteCategory.congr_hom he (e₂.inv s)).trans h₂

/-- Over a nonempty `S` there is an injective sheaf of abelian groups on the big fppf site over
`S`, an `ℕᵒᵖ`-diagram of affine objects whose cone is a limit of schemes, and a section
over that limit which is restricted from no stage of the diagram. -/
private lemma exists_injective_sheaf_not_surjective_limit_sections
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [Nonempty S] :
    ∃ (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
      (_ : Injective H) (D : ℕᵒᵖ ⥤ AlgebraicGeometry.BigAffineFppf B S hS) (c : Cone D)
      (_ : IsLimit ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).mapCone c)),
      ∃ s : H.obj.obj (op ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj c.pt)),
        ¬ ∃ (i : ℕᵒᵖ)
          (a : H.obj.obj (op ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj (D.obj i)))),
          H.obj.map
            ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i)).op a = s := by
  classical
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  obtain ⟨P⟩ := EnoughInjectives.presentation (additiveStructureSheaf B S hS)
  let : Injective P.J := P.injective
  let : Mono P.f := P.mono
  let H := ∏ᶜ fun _ : ℕ => P.J
  let : Injective H := productOfInjectives_injective _ (fun _ => P.injective)
  obtain ⟨R, f, hR, hnt⟩ := exists_nontrivial_affine_over B S hS
  let : Nontrivial R := hnt
  let inc := AlgebraicGeometry.BigAffineFppf.inclusion B S hS
  let D := booleanPowerAffineDiagram B S hS R hR f
  let c := booleanPowerAffineCone B S hS R hR f
  let U := op (inc.obj c.pt)
  obtain ⟨s, hs⟩ := exists_product_sheaf_section J P.J U
    (fun n => P.f.hom.app U (booleanPowerSection R n))
  refine ⟨H, inferInstance, D, c, booleanPowerAffineConeIsLimit B S hS R hR f, s, ?_⟩
  rintro ⟨i, a, ha⟩
  apply not_exists_booleanPowerAffine_pi_section B S hS R hR f P.J.obj P.f.hom
    (sheaf_mono_app_injective J P.f _)
  refine ⟨i, fun n => (Pi.π (fun _ : ℕ => P.J) n).hom.app _ a, fun n => ?_⟩
  have hn := congrArg (fun k => k a)
    ((Pi.π (fun _ : ℕ => P.J) n).hom.naturality (inc.map (c.π.app i)).op)
  exact hn.symm.trans ((congrArg ((Pi.π (fun _ : ℕ => P.J) n).hom.app U) ha).trans (hs n))

section RestrictionInjective

variable {C : Type*} [Category.{u} C]

/-- The morphisms `X.unop ⟶ U` as a discrete diagram in `CostructuredArrow (Over.forget U).op X`,
with `f` sent to `op (Over.mk f)` equipped with the identity of `X`. -/
private def overForgetFiber (U : C) (X : Cᵒᵖ) :
    Discrete (X.unop ⟶ U) ⥤ CostructuredArrow (Over.forget U).op X :=
  Discrete.functor fun f => CostructuredArrow.mk
    (Y := op (Over.mk f)) (𝟙 X)

attribute [local implicit_reducible] overForgetFiber in
/-- The discrete diagram of morphisms `X.unop ⟶ U` is final in
`CostructuredArrow (Over.forget U).op X`. -/
private lemma overForgetFiber_final (U : C) (X : Cᵒᵖ) :
    (overForgetFiber U X).Final := by
  apply Functor.Final.mk
  intro d
  let o : StructuredArrow d (overForgetFiber U X) :=
    StructuredArrow.mk (Y := Discrete.mk (d.hom.unop ≫ d.left.unop.hom))
      (CostructuredArrow.homMk
        (Over.homMk d.hom.unop (by simp)).op (by simp [overForgetFiber]))
  have he (Z : StructuredArrow d (overForgetFiber U X)) :
      Z.hom.left.unop.left = d.hom.unop := by
    have h := congrArg Quiver.Hom.unop Z.hom.w
    simpa [overForgetFiber] using h
  have hf (Z : StructuredArrow d (overForgetFiber U X)) :
      Z.right.as = d.hom.unop ≫ d.left.unop.hom := by
    rw [← he Z]
    exact (Over.w Z.hom.left.unop).symm
  let m (Z : StructuredArrow d (overForgetFiber U X)) : o ⟶ Z :=
    StructuredArrow.homMk (eqToHom (Discrete.ext (hf Z).symm)) (by
      apply CostructuredArrow.hom_ext
      apply Quiver.Hom.unop_inj
      apply Over.OverMorphism.ext
      rw [he]
      simp [o, overForgetFiber, eqToHom_map])
  exact isConnected_of_isInitial _
    (IsInitial.ofUniqueHom m (fun Z f => StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _)))

attribute [local instance] overForgetFiber_final

/-- Abelian groups have colimits of shape `CostructuredArrow (Over.forget U).op X`. -/
private lemma overForget_hasColimits (U : C) (X : Cᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow (Over.forget U).op X) AddCommGrpCat.{u} :=
  Functor.Final.hasColimitsOfShape_of_final (overForgetFiber U X)

attribute [local instance] overForget_hasColimits

attribute [local implicit_reducible] CategoryTheory.Functor.lan in
/-- Evaluating at `X` the left Kan extension along `(Over.forget U).op` is the colimit over
`CostructuredArrow (Over.forget U).op X` of the restriction along the projection to
`(Over U)ᵒᵖ`. -/
private def overForgetLanEvaluationIso (U : C) (X : Cᵒᵖ) :
    (Over.forget U).op.lan ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj X ≅
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
        (CostructuredArrow.proj (Over.forget U).op X) ⋙ colim :=
  NatIso.ofComponents
    (fun F => (Over.forget U).op.leftKanExtensionObjIsoColimit F X)
    (by
      intro F G f
      dsimp only [Functor.comp_map, evaluation_obj_map, Functor.whiskeringLeft_obj_obj,
        Functor.comp_obj]
      rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
      apply colimit.hom_ext
      intro j
      rw [Functor.ι_leftKanExtensionObjIsoColimit_inv_assoc]
      simp only [colim_map, ι_colimMap_assoc,
        Functor.ι_leftKanExtensionObjIsoColimit_inv]
      have hunit : ((Over.forget U).op.leftKanExtensionUnit F).app j.left ≫
            ((Over.forget U).op.lan.map f).app ((Over.forget U).op.obj j.left)
          = f.app j.left ≫ ((Over.forget U).op.leftKanExtensionUnit G).app j.left := by
        exact Functor.descOfIsLeftKanExtension_fac_app ((Over.forget U).op.leftKanExtension F)
          ((Over.forget U).op.leftKanExtensionUnit F) ((Over.forget U).op.leftKanExtension G)
          (f ≫ (Over.forget U).op.leftKanExtensionUnit G) j.left
      have hnat : ((Over.forget U).op.leftKanExtension F).map j.hom ≫
            ((Over.forget U).op.lan.map f).app X
          = ((Over.forget U).op.lan.map f).app ((Over.forget U).op.obj j.left) ≫
            ((Over.forget U).op.leftKanExtension G).map j.hom :=
        ((Over.forget U).op.lan.map f).naturality j.hom
      rw [hnat, ← Category.assoc, hunit]
      exact Category.assoc _ _ _)

/-- Left Kan extension along `(Over.forget U).op` preserves finite limits of presheaves of
abelian groups. -/
private lemma overForgetLan_preservesFiniteLimits (U : C) :
    PreservesFiniteLimits ((Over.forget U).op.lan :
      ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u})) := by
  apply preservesFiniteLimits_of_evaluation
  intro X
  let : HasExactColimitsOfShape (CostructuredArrow (Over.forget U).op X)
      AddCommGrpCat.{u} := hasExactColimitsOfShape_of_final _ (overForgetFiber U X)
  let : PreservesFiniteLimits
      (colim : (CostructuredArrow (Over.forget U).op X ⥤ AddCommGrpCat.{u}) ⥤ _) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  exact preservesFiniteLimits_of_natIso (overForgetLanEvaluationIso U X).symm

/-- The restriction `H.over U` of an injective sheaf of abelian groups to the localization of
`J` at `U` is again injective. -/
private lemma injective_over (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] (U : C)
    (H : Sheaf J AddCommGrpCat.{u}) [Injective H] : Injective (H.over U) := by
  let := overForgetLan_preservesFiniteLimits U
  let L := Functor.sheafPullbackConstruction.sheafPullback
    (Over.forget U) AddCommGrpCat.{u} (J.over U) J
  let : PreservesFiniteLimits L := by
    dsimp [L, Functor.sheafPullbackConstruction.sheafPullback]
    infer_instance
  let : L.PreservesMonomorphisms := preservesMonomorphisms_of_preservesLimitsOfShape L
  exact (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Over.forget U) AddCommGrpCat.{u} (J.over U) J).map_injective H inferInstance

end RestrictionInjective

/-- Presheaves of abelian groups on the localization at `U` of the big fppf site over `S` admit
sheafification. -/
private lemma bigFppfOverOver_hasSheafify
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS) :
    HasSheafify ((AlgebraicGeometry.BigFppfOver.topology B S hS).over U)
      AddCommGrpCat.{u} := by
  have := essentiallySmall_bigFppfOver B S hS
  have : EssentiallySmall.{u} (Over U) := essentiallySmall_over _
  exact hasSheafify_of_essentiallySmall _

/-- A torsor under the restriction `H.over U` of an injective abelian sheaf on the big fppf site
over `S` has a global section, hence is trivial. -/
private lemma abelianTorsor_over_hasGlobalSections
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    [Injective H] (U : AlgebraicGeometry.BigFppfOver B S hS)
    (T : Stacks.Cohomology.Torsors.AbelianTorsor (H.over U)) :
    Nonempty (GlobalSections T.1.presheaf) := by
  let := bigFppfOverOver_hasSheafify B S hS U
  let := essentiallySmall_bigFppfOver B S hS
  let : EssentiallySmall.{u} (Over U) := essentiallySmall_over _
  let := isGrothendieckAbelian_sheaf_of_essentiallySmall
    ((AlgebraicGeometry.BigFppfOver.topology B S hS).over U)
  let : EnoughInjectives
      (Sheaf ((AlgebraicGeometry.BigFppfOver.topology B S hS).over U) AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.enoughInjectives
  let := injective_over _ U H
  let : HasExt.{u}
      (Sheaf ((AlgebraicGeometry.BigFppfOver.topology B S hS).over U) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  exact (Stacks.Cohomology.Torsors.torsor_class_eq_trivial_iff (H.over U) T).mp
    (abelianTorsor_class_eq_trivial (H.over U) T).symm

section Torsors

attribute [local instance] Over.cartesianMonoidalCategory
  Functor.Monoidal.ofChosenFiniteProducts

open scoped MonoidalCategory MonObj

/-- The constant presheaf of sets at `PUnit`. -/
private abbrev unitPresheaf {C : Type*} [Category C] : Cᵒᵖ ⥤ Type u :=
  (Functor.const Cᵒᵖ).obj PUnit.{u + 1}

/-- The constant presheaf at `PUnit` is terminal among presheaves of sets. -/
private def unitPresheafIsTerminal {C : Type*} [Category C] :
    IsTerminal (unitPresheaf.{u} (C := C)) :=
  IsTerminal.ofUniqueHom (fun F => { app := fun U => ↾fun _ => PUnit.unit })
    (by intro F α; ext U x; change (PUnit.unit : PUnit) = _; exact Subsingleton.elim _ _)

/-- For `T` over `yoneda.obj U` and `W : Over U`, the sections of `T.left` over `W.left` lying
above `W.hom` correspond to the morphisms `Over.mk (yoneda.map W.hom) ⟶ T`. -/
private def overYonedaSectionEquiv {C : Type*} [Category.{u} C]
    {U : C} (T : Over (yoneda.obj U)) (W : Over U) :
    {s : T.left.obj (op W.left) // T.hom.app (op W.left) s = W.hom} ≃
      (Over.mk (yoneda.map W.hom) ⟶ T) where
  toFun s := Over.homMk (yonedaEquiv.symm s.1) (by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, s.2]
    exact (yonedaEquiv_yoneda_map W.hom).symm)
  invFun f := ⟨yonedaEquiv f.left, by
    rw [← yonedaEquiv_comp, Over.w f]
    exact yonedaEquiv_yoneda_map W.hom⟩
  left_inv s := Subtype.ext (yonedaEquiv.apply_symm_apply s.1)
  right_inv f := Over.OverMorphism.ext (yonedaEquiv.symm_apply_apply f.left)

/-- Naturality of `overYonedaSectionEquiv` in `W`: composing with `(Over.post yoneda).map f`
corresponds to restricting the section along `f.left`. -/
private lemma overYonedaSectionEquiv_naturality {C : Type*} [Category.{u} C]
    {U : C} (T : Over (yoneda.obj U)) {W W' : Over U} (f : W ⟶ W')
    (s : {s : T.left.obj (op W'.left) // T.hom.app (op W'.left) s = W'.hom}) :
    (Over.post yoneda).map f ≫ overYonedaSectionEquiv T W' s =
      overYonedaSectionEquiv T W
        ⟨T.left.map f.left.op s.1, by
          rw [T.hom.naturality_apply, s.2]
          exact Over.w f⟩ := by
  apply Over.OverMorphism.ext
  exact yonedaEquiv_symm_naturality_left f.left T.left s.1

/-- A sheaf of abelian groups `H`, viewed as a group object over the terminal presheaf
`unitPresheaf` via its underlying presheaf of sets. -/
private def sheafGroupOver {C : Type*} [Category.{u} C]
    {J : GrothendieckTopology C} (H : Sheaf J AddCommGrpCat.{u}) :
    Grp (Over (unitPresheaf.{u} (C := C))) := by
  letI : CartesianMonoidalCategory (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    CartesianMonoidalCategory.ofHasFiniteProducts
  let F := (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{u} (Type u)).obj
    (forget AddCommGrpCat)
  exact (Over.equivalenceOfIsTerminal unitPresheafIsTerminal.{u}).inverse.mapGrp.obj
    (F.mapGrp.obj (Grp.mk H.obj))

/-- The group object `sheafGroupOver H` has underlying presheaf of sets
`H.obj ⋙ forget AddCommGrpCat`. -/
private lemma sheafGroupOver_presheaf {C : Type*} [Category.{u} C]
    {J : GrothendieckTopology C} (H : Sheaf J AddCommGrpCat.{u}) :
    (sheafGroupOver H).X.left = H.obj ⋙ forget AddCommGrpCat := rfl

/-- The presheaf of sets underlying the group object `sheafGroupOver H` is a `J`-sheaf. -/
private lemma sheafGroupOver_isSheaf {C : Type*} [Category.{u} C]
    {J : GrothendieckTopology C} (H : Sheaf J AddCommGrpCat.{u}) :
    Presheaf.IsSheaf J (sheafGroupOver H).X.left := by
  rw [sheafGroupOver_presheaf]
  exact Presheaf.isSheaf_comp_of_isSheaf J H.obj (forget AddCommGrpCat.{u}) H.property

open scoped CategoryTheory.Obj in
/-- For an adjunction `L ⊣ R` with `R` monoidal and `G` a group object of `D`, the adjunction
bijection `(L.obj T ⟶ G.X) ≃ (T ⟶ (R.mapGrp.obj G).X)` is multiplicative. -/
private def adjunctionHomMulEquiv {C D : Type*} [Category C] [Category D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [R.Monoidal]
    (G : Grp D) (T : C) :
    (L.obj T ⟶ G.X) ≃* (T ⟶ (R.mapGrp.obj G).X) where
  __ := adj.homEquiv T G.X
  map_mul' f g := by
    exact (congrArg (fun a => adj.unit.app T ≫ a) (R.map_mul f g)).trans
      (MonObj.comp_mul _ _ _)

/-- Points of the pullback group `(Over.pullback b).mapGrp.obj G` over `T` are, as a group, the
points of `G` over `(Over.map b).obj T`. -/
private def pullbackHomMulEquiv {C : Type*} [Category C] [HasPullbacks C]
    {U V : C} (b : U ⟶ V) (G : Grp (Over V)) (T : Over U) :
    (T ⟶ ((Over.pullback b).mapGrp.obj G).X) ≃* ((Over.map b).obj T ⟶ G.X) :=
  (adjunctionHomMulEquiv (Over.mapPullbackAdj b) G T).symm

/-- For a terminal object `T` and a group object `G` of `C`, the points over `A : Over T` of the
group object transported along `C ≌ Over T` are, as a group, the morphisms `A.left ⟶ G.X`. -/
private def overTerminalHomMulEquiv {C : Type*} [Category C]
    [CartesianMonoidalCategory C] [HasPullbacks C] {T : C} (hT : IsTerminal T)
    (G : Grp C) (A : Over T) :
    (A ⟶ ((Over.equivalenceOfIsTerminal hT).inverse.mapGrp.obj G).X) ≃*
      (A.left ⟶ G.X) where
  toFun f := f.left
  invFun f := Over.homMk f (hT.hom_ext _ _)
  left_inv f := Over.OverMorphism.ext rfl
  right_inv f := rfl
  map_mul' f g := by
    have h := (Over.equivalenceOfIsTerminal hT).inverse.map_mul (M := G.X)
      (f.left : A.left ⟶ G.X) (g.left : A.left ⟶ G.X)
    exact (congrArg Over.Hom.left h).symm

section
variable {C : Type*} [Category.{u} C]

/-- The cartesian monoidal structure on presheaves of abelian groups coming from finite
products. -/
private abbrev additivePresheafCartesian (C : Type*) [Category.{u} C] :
    CartesianMonoidalCategory (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  CartesianMonoidalCategory.ofHasFiniteProducts

attribute [local instance] additivePresheafCartesian

/-- The presheaf of types underlying a presheaf of abelian groups on `C`, obtained by
forgetting the group structure on sections. -/
private abbrev underlyingAdditivePresheaf :
    (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ Type u) :=
  (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{u} (Type u)).obj
    (forget AddCommGrpCat)

/-- The presheaf of types underlying a presheaf of abelian groups `A`, as a group object in
`Cᵒᵖ ⥤ Type u` whose multiplication is the addition of `A`. -/
private def additivePresheafGroup (A : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    Grp (Cᵒᵖ ⥤ Type u) := by
  let F : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ Type u) :=
    underlyingAdditivePresheaf
  exact F.mapGrp.obj (Grp.mk A)

/-- The sections of `additivePresheafGroup A` over `V` carry the abelian group structure of
`A.obj V`. -/
private abbrev additivePresheafGroup_sectionAddCommGroup
    (A : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (V : Cᵒᵖ) :
    AddCommGroup ((additivePresheafGroup A).X.obj V) :=
  inferInstanceAs (AddCommGroup (A.obj V))

attribute [local instance] additivePresheafGroup_sectionAddCommGroup

attribute [local implicit_reducible] additivePresheafGroup in
open scoped CategoryTheory.Obj in
/-- Multiplication in the group `P ⟶ (additivePresheafGroup A).X` is addition in `A` on
sections: `(f * g).app V x = f.app V x + g.app V x`. -/
private lemma additivePresheafGroup_mul_apply
    (A : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (P : Cᵒᵖ ⥤ Type u)
    (f g : P ⟶ (additivePresheafGroup A).X) (V : Cᵒᵖ) (x : P.obj V) :
    (f * g).app V x = (f.app V x : A.obj V) + (g.app V x : A.obj V) := by
  let a := Stacks.Cohomology.Torsors.freeAbelianPresheafLift P A f
  let b := Stacks.Cohomology.Torsors.freeAbelianPresheafLift P A g
  let z := Stacks.Cohomology.Torsors.freeAbelianGenerators P
  have ha : z ≫ underlyingAdditivePresheaf.map a = f := by
    ext W y
    exact FreeAbelianGroup.lift_apply_of (fun s => (f.app W s : A.obj W)) y
  have hb : z ≫ underlyingAdditivePresheaf.map b = g := by
    ext W y
    exact FreeAbelianGroup.lift_apply_of (fun s => (g.app W s : A.obj W)) y
  have hab : a * b = a + b := by
    simp [Hom.mul_def, Preadditive.mul_def]
  have hfg : f * g = z ≫ underlyingAdditivePresheaf.map (a + b) := by
    rw [← hab]
    rw [Functor.map_mul, MonObj.comp_mul, ha, hb]
    rfl
  rw [hfg]
  change (a.app V + b.app V) (FreeAbelianGroup.of x) = _
  change a.app V (FreeAbelianGroup.of x) + b.app V (FreeAbelianGroup.of x) = _
  exact congrArg₂ (· + ·)
    (FreeAbelianGroup.lift_apply_of (fun s => (f.app V s : A.obj V)) x)
    (FreeAbelianGroup.lift_apply_of (fun s => (g.app V s : A.obj V)) x)

/-- Yoneda identifies the group `yoneda.obj W ⟶ (additivePresheafGroup A).X` with the group
`A.obj (op W)` of sections of `A` over `W`. -/
private def additivePresheafGroupYonedaEquiv
    (A : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (W : C) :
    (yoneda.obj W ⟶ (additivePresheafGroup A).X) ≃*
      Multiplicative (A.obj (op W)) where
  __ := yonedaEquiv
  map_mul' f g := additivePresheafGroup_mul_apply A _ f g (op W) (𝟙 W)

end

open scoped CategoryTheory.Obj in
/-- Sections over an object `W` of `Over U` of the group object obtained by pulling `H` back to
`U` along `b` form the group `H(W)` of sections of `H` over `W`. -/
private def sheafGroupSectionMulEquiv
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (b : yoneda.obj U ⟶ unitPresheaf) (W : Over U) :
    (Over.mk (yoneda.map W.hom) ⟶ (ClassifyingTorsors.pullbackGroup (sheafGroupOver H) U b).X) ≃*
      Multiplicative ((H.over U).obj.obj (op W)) :=
  (pullbackHomMulEquiv b (sheafGroupOver H) (Over.mk (yoneda.map W.hom))).trans
    ((overTerminalHomMulEquiv unitPresheafIsTerminal (additivePresheafGroup H.obj)
      ((Over.map b).obj (Over.mk (yoneda.map W.hom)))).trans
      (additivePresheafGroupYonedaEquiv H.obj W.left))

/-- The identification of these sections with `H(W)` sends `f` to the section of `H` over `W`
cut out by `f.left` followed by the projection of the fibre product to `H`. -/
private lemma sheafGroupSectionMulEquiv_apply
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (b : yoneda.obj U ⟶ unitPresheaf) (W : Over U)
    (f : Over.mk (yoneda.map W.hom) ⟶
      (ClassifyingTorsors.pullbackGroup (sheafGroupOver H) U b).X) :
    sheafGroupSectionMulEquiv H U b W f =
      Multiplicative.ofAdd (yonedaEquiv (f.left ≫ pullback.fst (sheafGroupOver H).X.hom b)) := by
  simp only [sheafGroupSectionMulEquiv,
    pullbackHomMulEquiv, adjunctionHomMulEquiv, overTerminalHomMulEquiv,
    additivePresheafGroupYonedaEquiv,
    Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

attribute [local implicit_reducible] ClassifyingTorsors.pullbackGroup sheafGroupOver
    sheafGroupSectionMulEquiv in
/-- The identification of these sections with `H(W)` is natural in `W`: precomposition with
`f : W ⟶ W'` corresponds to the restriction map `H.obj.map f.left.op` of sections of `H`. -/
private lemma sheafGroupSectionMulEquiv_naturality
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (b : yoneda.obj U ⟶ unitPresheaf) {W W' : Over U} (f : W ⟶ W')
    (a : Over.mk (yoneda.map W'.hom) ⟶
      (ClassifyingTorsors.pullbackGroup (sheafGroupOver H) U b).X) :
    sheafGroupSectionMulEquiv H U b W ((Over.post yoneda).map f ≫ a) =
      Multiplicative.ofAdd (H.obj.map f.left.op
        (sheafGroupSectionMulEquiv H U b W' a).toAdd) := by
  rw [sheafGroupSectionMulEquiv_apply, sheafGroupSectionMulEquiv_apply]
  change yonedaEquiv (F := H.obj ⋙ forget AddCommGrpCat)
    ((yoneda.map f.left ≫ a.left) ≫ pullback.fst (sheafGroupOver H).X.hom b) =
    H.obj.map f.left.op (yonedaEquiv (a.left ≫ pullback.fst (sheafGroupOver H).X.hom b))
  exact (congrArg (fun t => yonedaEquiv (F := H.obj ⋙ forget AddCommGrpCat) t)
      (Category.assoc (yoneda.map f.left) a.left
        (pullback.fst (sheafGroupOver H).X.hom b))).trans
    (yonedaEquiv_naturality (F := H.obj ⋙ forget AddCommGrpCat)
      (a.left ≫ pullback.fst (sheafGroupOver H).X.hom b) f.left).symm

/-- The category of torsors under an abelian sheaf `H` on the big fppf site of `S`, taken as a
group object over the terminal presheaf, fibred in groupoids over that site. -/
private def abelianSheafTorsors
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsStackOfTorsors B S hS]
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u}) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1}
      (AlgebraicGeometry.BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor
    (ClassifyingTorsors.torsorsProjection (sheafGroupOver H)))
    (IsStackOfTorsors.isStackInGroupoids (sheafGroupOver H)
      (Presheaf.isSheaf_of_isTerminal _ Types.isTerminalPUnit)
      (sheafGroupOver_isSheaf H)).isFiberedInGroupoids

/-- The topology of a big fppf site is subcanonical, so every representable presheaf on it is a
sheaf. -/
private lemma bigFppf_subcanonical (B : AlgebraicGeometry.BigFppfSite.{u}) :
    B.topology.Subcanonical := by
  let : ObjectProperty.IsClosedUnderIsomorphisms
      (fun X : Scheme.{u} => X.size < B.cutoff) :=
    ⟨fun e h => by rwa [← Scheme.size_congr e]⟩
  let : ObjectProperty.IsClosedUnderLimitsOfShape
      (fun X : Scheme.{u} => X.size < B.cutoff) WalkingCospan :=
    .mk' (by
      rintro _ ⟨F, hF⟩
      rw [Scheme.size_congr (HasLimit.isoOfNatIso (diagramIsoCospan F))]
      exact Scheme.size_pullback_lt _ _ (hF .left) (hF .right))
  let Q := Scheme.fppfPrecoverage.comap B.inclusion
  have htop : B.topology ≤ Q.toGrothendieck := by
    apply Precoverage.toGrothendieck_mono
    rintro X R ⟨E, rfl, hE⟩
    exact B.isFppfCovering_of_isCovering hE
  let : B.inclusion.IsContinuous Q.toGrothendieck Scheme.fppfTopology :=
    Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
      (F := B.inclusion) (J := Q) (K := Scheme.fppfPrecoverage) (by
        intro X R hR
        exact hR)
  let : Q.toGrothendieck.Subcanonical :=
    GrothendieckTopology.subcanonical_of_full_of_faithful B.inclusion
      Q.toGrothendieck Scheme.fppfTopology
  exact GrothendieckTopology.Subcanonical.of_le htop

/-- The presheaf represented by an object `U` of the big fppf site of `S` is a sheaf for the
fppf topology. -/
private lemma bigFppfOver_isSheaf_yoneda
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS) :
    Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (yoneda.obj U) := by
  let := bigFppf_subcanonical B
  exact (isSheaf_iff_isSheaf_of_type _ _).mpr
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := AlgebraicGeometry.BigFppfOver.topology B S hS) (yoneda.obj U))

/-- A fibre product of sheaves of types is a sheaf: if `F`, `G` and `K` are sheaves for `J`, so
is `pullback f g` for `f : F ⟶ K` and `g : G ⟶ K`. -/
private lemma isSheaf_pullback {C : Type*} [Category.{u} C]
    (J : GrothendieckTopology C) {F G K : Cᵒᵖ ⥤ Type u}
    (f : F ⟶ K) (g : G ⟶ K)
    (hF : Presheaf.IsSheaf J F) (hG : Presheaf.IsSheaf J G)
    (hK : Presheaf.IsSheaf J K) : Presheaf.IsSheaf J (pullback f g) := by
  apply (show ObjectProperty (Cᵒᵖ ⥤ Type u) from Presheaf.IsSheaf J).prop_of_isLimit
    (pullback.isLimit f g)
  rintro (_ | _ | _)
  · exact hK
  · exact hF
  · exact hG

attribute [local implicit_reducible] overYonedaSectionEquiv sheafGroupOver
    sheafGroupSectionMulEquiv CategoryTheory.OverShriek.fiber
    Stacks.Cohomology.Torsors.abelianSheafAsGroupSheaf AddCommGrpCat.toCommGrp in
/-- The sections of `T.F` over `W ⟶ T.U`, with the translation action of `H(W)` transported
along the identification of `H.over T.U` with the group acting on `T.F`. -/
private def localizedPseudoTorsor
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    (T : ClassifyingTorsors.Torsor (sheafGroupOver H)) :
    PseudoTorsor (Stacks.Cohomology.Torsors.abelianSheafAsGroupSheaf (H.over T.U)) := by
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  let P := OverShriek.fiber (𝟙 (yoneda.obj T.U)) T.F.hom
  let se (W : Over T.U) := overYonedaSectionEquiv T.F W
  let ce (W : Over T.U) := sheafGroupSectionMulEquiv H T.U T.b W
  exact
    { presheaf := P
      isSheaf := by
        apply (isSheaf_iff_isSheaf_of_type _ _).mpr
        let Fsh : Sheaf J (Type u) := ⟨T.F.left, T.isTorsor.1⟩
        let Ush : Sheaf J (Type u) :=
          ⟨yoneda.obj T.U, bigFppfOver_isSheaf_yoneda B S hS T.U⟩
        exact OverShriek.isSheaf_fiber _ _
          ((isSheaf_iff_isSheaf_of_type _ _).mp (Fsh.over T.U).property)
          ((isSheaf_iff_isSheaf_of_type _ _).mp (Ush.over T.U).property).isSeparated
      act W g s := (se W.unop).symm ((ce W.unop).symm g • se W.unop s)
      one_act := by
        intro W s
        refine (congrArg (se W.unop).symm ?_).trans ((se W.unop).symm_apply_apply s)
        exact (congrArg (· • se W.unop s) (map_one (ce W.unop).symm)).trans
          (one_smul _ (se W.unop s))
      mul_act := by
        intro W g h s
        have h2 : (ce W.unop).symm (g * h) • se W.unop s =
            (ce W.unop).symm g • (ce W.unop).symm h • se W.unop s :=
          (congrArg (· • se W.unop s) (map_mul (ce W.unop).symm g h)).trans
            (mul_smul _ _ (se W.unop s))
        refine (congrArg (se W.unop).symm h2).trans (congrArg (se W.unop).symm ?_)
        exact congrArg (fun t : Over.mk (yoneda.map W.unop.hom) ⟶ T.F =>
          (ce W.unop).symm g • t)
          ((se W.unop).apply_symm_apply ((ce W.unop).symm h • se W.unop s)).symm
      naturality := by
        intro W W' f g s
        apply (se W'.unop).injective
        rw [Equiv.apply_symm_apply]
        have hn (s : P.obj W) :
            (Over.post yoneda).map f.unop ≫ se W.unop s =
              se W'.unop (P.map f s) := overYonedaSectionEquiv_naturality T.F f.unop s
        rw [← hn, Equiv.apply_symm_apply, ModObj.comp_smul, hn]
        congr 1
        apply (ce W'.unop).injective
        rw [MulEquiv.apply_symm_apply]
        change sheafGroupSectionMulEquiv H T.U T.b W'.unop
          ((Over.post yoneda).map f.unop ≫ (ce W.unop).symm g) = _
        rw [sheafGroupSectionMulEquiv_naturality, MulEquiv.apply_symm_apply]
        rfl
      simplyTransitive := by
        intro W _ s t
        obtain ⟨a, ha, hu⟩ := ModObj.isIso_leftSMul_iff.mp T.isTorsor.2.1
          (Over.mk (yoneda.map W.unop.hom)) (se W.unop s) (se W.unop t)
        refine ⟨ce W.unop a, ?_, ?_⟩
        · simp only [MulEquiv.symm_apply_apply, ha, Equiv.symm_apply_apply]
        · intro g hg
          apply (ce W.unop).symm.injective
          rw [MulEquiv.symm_apply_apply]
          apply hu
          simpa only [Equiv.apply_symm_apply] using congrArg (se W.unop) hg }

/-- The underlying presheaf of the localized pseudo-torsor is the fibre of `T.F` over the
identity of `T.U`. -/
private lemma localizedPseudoTorsor_presheaf
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    (T : ClassifyingTorsors.Torsor (sheafGroupOver H)) :
    (localizedPseudoTorsor H T).presheaf =
      OverShriek.fiber (𝟙 (yoneda.obj T.U)) T.F.hom := rfl

/-- The sections of `T.F` over the members of a covering of `W` that lift `W.hom` along
`T.F ⟶ yoneda.obj T.U` form a covering sieve of `W` in the localized topology. -/
private lemma localizedSectionSieve_mem
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    (T : ClassifyingTorsors.Torsor (sheafGroupOver H)) (W : Over T.U) :
    (Sieve.overEquiv W).symm (Presheaf.imageSieve T.F.hom W.hom) ∈
      ((AlgebraicGeometry.BigFppfOver.topology B S hS).over T.U) W := by
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  have hloc : Presheaf.IsLocallySurjective J T.F.hom := T.isTorsor.2.2
  exact J.overEquiv_symm_mem_over W _ (hloc.imageSieve_mem (U := W.left) W.hom)

/-- The sections of `T.F` exist locally on `T.U`, so they form a torsor and not merely a
pseudo-torsor under `H.over T.U`. -/
private lemma localizedPseudoTorsor_isTorsor
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    (T : ClassifyingTorsors.Torsor (sheafGroupOver H)) :
    (localizedPseudoTorsor H T).IsTorsor := by
  intro W
  refine ⟨_, localizedSectionSieve_mem H T W, ?_⟩
  intro V f hf
  rw [localizedPseudoTorsor_presheaf]
  obtain ⟨s, hs⟩ := hf
  exact ⟨⟨s, hs.trans (Over.w f)⟩⟩

/-- A torsor `T` under `H`, read as a torsor under the restriction `H.over T.U` of `H` to the
site localized at `T.U`, its sections over `W ⟶ T.U` being the sections of `T.F` over `W`. -/
private def localizedAbelianTorsor
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    (T : ClassifyingTorsors.Torsor (sheafGroupOver H)) :
    Stacks.Cohomology.Torsors.AbelianTorsor (H.over T.U) :=
  ⟨localizedPseudoTorsor H T, localizedPseudoTorsor_isTorsor H T⟩

/-- A torsor under an injective abelian sheaf `H` has a global section, a morphism from the
terminal object of `Over (yoneda.obj T.U)` to `T.F`. -/
private lemma abelianSheafTorsor_hasSection
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    [IsStackOfTorsors B S hS]
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    [Injective H]
    (T : ClassifyingTorsors.Torsor (sheafGroupOver H)) :
    Nonempty (𝟙_ (Over (yoneda.obj T.U)) ⟶ T.F) := by
  obtain ⟨s, _⟩ := (Stacks.Cohomology.Torsors.nonempty_globalSections_iff_sectionFamily _).mp
    (abelianTorsor_over_hasGlobalSections B S hS H T.U (localizedAbelianTorsor H T))
  refine ⟨Over.homMk (𝟙_ (Over (yoneda.obj T.U))).hom (by simp) ≫
    overYonedaSectionEquiv T.F (Over.mk (𝟙 T.U)) (s (op (Over.mk (𝟙 T.U))))⟩

/-- Every torsor under an injective abelian sheaf `H` is trivial: it is equivariantly isomorphic
to its group acting on itself by translation. -/
private lemma abelianSheafTorsor_isTrivial
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    [IsStackOfTorsors B S hS]
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    [Injective H]
    (T : ClassifyingTorsors.Torsor (sheafGroupOver H)) :
    AlgebraicGeometry.IsTrivialPseudoTorsor T.group T.F :=
  (AlgebraicGeometry.isTrivial_iff_exists_globalSection
    T.group T.F T.isTorsor.2.1).mpr (abelianSheafTorsor_hasSection H T)

/-- The trivial torsor over `U` under an abelian sheaf `H`: the group object obtained by pulling
`H` back to `U` acting on itself by translation. -/
private def trivialAbelianSheafTorsor
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsStackOfTorsors B S hS]
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    (U : AlgebraicGeometry.BigFppfOver B S hS) :
    ClassifyingTorsors.Torsor (sheafGroupOver H) := by
  let b : yoneda.obj U ⟶ unitPresheaf := unitPresheafIsTerminal.from _
  let G := ClassifyingTorsors.pullbackGroup (sheafGroupOver H) U b
  letI : ModObj G.X G.X := ModObj.regular G.X
  refine ⟨U, b, G.X, inferInstance, ?_, ?_, ?_⟩
  · exact isSheaf_pullback _ _ _ (sheafGroupOver_isSheaf H)
      (bigFppfOver_isSheaf_yoneda B S hS U)
      (Presheaf.isSheaf_of_isTerminal _ Types.isTerminalPUnit)
  · apply ModObj.isIso_leftSMul_iff.mpr
    intro Z x y
    change ∃! m : Z ⟶ G.X, m * x = y
    exact ⟨y * x⁻¹, by simp, fun m hm => by rw [← hm]; simp⟩
  · apply Presheaf.isLocallySurjective_of_surjective
    intro W s
    refine ⟨(η[G.X]).left.app W s, ?_⟩
    have h := congrArg (fun α => α.app W s) (Over.w (η[G.X]))
    exact h

/-- The category of torsors under an abelian sheaf `H` is a stack in groupoids over the big
fppf site of `S`. -/
private lemma abelianSheafTorsors_isStackInGroupoids
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsStackOfTorsors B S hS]
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u}) :
    (abelianSheafTorsors B S hS H).val.p.IsStackInGroupoids.{u + 1}
      (AlgebraicGeometry.BigFppfOver.topology B S hS) :=
  IsStackOfTorsors.isStackInGroupoids (sheafGroupOver H)
    (Presheaf.isSheaf_of_isTerminal _ Types.isTerminalPUnit)
    (sheafGroupOver_isSheaf H)

/-- The category of functors `C ⥤ Type u` on an essentially small category `C` is locally
small. -/
private lemma locallySmall_functor_of_essentiallySmall
    {C : Type*} [Category.{u} C] [EssentiallySmall.{u} C] :
    LocallySmall.{u} (C ⥤ Type u) := by
  exact locallySmall_of_faithful
    ((Functor.whiskeringLeft (SmallModel C) C (Type u)).obj (equivSmallModel C).inverse)

/-- The category of torsors under `H` on the big fppf site of `S` is locally small, a morphism
of torsors being determined by its pair of component morphisms. -/
private lemma abelianSheafTorsors_locallySmall
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsStackOfTorsors B S hS]
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u}) :
    LocallySmall.{u} (abelianSheafTorsors B S hS H).val.obj := by
  let C := AlgebraicGeometry.BigFppfOver B S hS
  let := essentiallySmall_bigFppfOver B S hS
  let : LocallySmall.{u} (Cᵒᵖ ⥤ Type u) := locallySmall_functor_of_essentiallySmall.{u} (C := Cᵒᵖ)
  change LocallySmall.{u}
    (ClassifyingTorsors.Torsor.{u} (sheafGroupOver H))
  refine ⟨fun T T' => ?_⟩
  apply small_of_injective.{u} (f := fun φ : T ⟶ T' => (φ.f, φ.g))
  intro φ ψ h
  exact ClassifyingTorsors.TorsorHom.ext.{u} (G := sheafGroupOver H)
    (congrArg Prod.fst h) (congrArg Prod.snd h)

attribute [local implicit_reducible] CategoryTheory.ShrinkHoms.functor
    CategoryTheory.ShrinkHoms.inverse in
/-- Precomposing a functor fibred in groupoids with the equivalence `ShrinkHoms X ≌ X` of a
locally small category `X` gives a functor fibred in groupoids. -/
private lemma isFiberedInGroupoids_shrinkHoms
    {C X : Type*} [Category C] [Category X] [LocallySmall.{u} X]
    (p : X ⥤ C) (hp : p.IsFiberedInGroupoids) :
    (ShrinkHoms.inverse.{u} X ⋙ p).IsFiberedInGroupoids := by
  let F := ShrinkHoms.inverse.{u} X
  constructor
  · intro V U f x hx
    obtain ⟨y, φ, hφ⟩ := hp.exists_lift f (F.obj x) hx
    let y' : ShrinkHoms X := ShrinkHoms.toShrinkHoms y
    let φ' : y' ⟶ x := F.preimage φ
    refine ⟨y', φ', ?_⟩
    have : p.IsHomLift f φ := hφ
    have hy : p.obj y = V := IsHomLift.domain_eq p f φ
    apply IsHomLift.of_fac' (F ⋙ p) f φ' hy hx
    change p.map (F.map φ') = _
    rw [show F.map φ' = φ from F.map_preimage φ]
    exact IsHomLift.fac' p f φ
  · intro x y z φ ψ f hf
    obtain ⟨χ, hχ, huniq⟩ := hp.unique_lift (F.map φ) (F.map ψ) f hf
    refine ⟨F.preimage χ, ⟨?_, ?_⟩, ?_⟩
    · change p.map (F.map (F.preimage χ)) = f
      simpa only [F.map_preimage] using hχ.1
    · apply F.map_injective
      simpa only [F.map_comp, F.map_preimage] using hχ.2
    · intro χ' hχ'
      apply F.map_injective
      rw [F.map_preimage]
      apply huniq
      exact ⟨hχ'.1, by simpa only [F.map_comp] using congrArg F.map hχ'.2⟩

attribute [local implicit_reducible] CategoryTheory.ShrinkHoms.functor
    CategoryTheory.ShrinkHoms.inverse in
/-- For a locally small category `X`, the composite `ShrinkHoms.functor X ⋙ ShrinkHoms.inverse X`
is the identity functor of `X`. -/
private lemma shrinkHoms_functor_comp_inverse
    {X : Type*} [Category X] [LocallySmall.{u} X] :
    ShrinkHoms.functor.{u} X ⋙ ShrinkHoms.inverse.{u} X = 𝟭 X := by
  refine CategoryTheory.Functor.ext
    (F := ShrinkHoms.functor.{u} X ⋙ ShrinkHoms.inverse.{u} X)
    (G := 𝟭 X) (fun _ => rfl) ?_
  intro x y f
  have h : (ShrinkHoms.functor.{u} X ⋙ ShrinkHoms.inverse.{u} X).map f = f :=
    (equivShrink (x ⟶ y)).symm_apply_apply f
  rw [h]
  change f = eqToHom (rfl : x = x) ≫ f ≫ eqToHom (rfl : y = y)
  simp

/-- The category of `H`-torsors with its hom types replaced by small models, fibred in
groupoids over the big fppf site of `S` with morphisms in `Type u`. -/
private def smallAbelianSheafTorsors
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsStackOfTorsors B S hS]
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u}) :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (AlgebraicGeometry.BigFppfOver B S hS) := by
  let 𝒯 := abelianSheafTorsors B S hS H
  letI : LocallySmall.{u} 𝒯.val.obj := abelianSheafTorsors_locallySmall B S hS H
  exact CatFiberedInGroupoids.mk
    (BasedCategory.ofFunctor (ShrinkHoms.inverse.{u} 𝒯.val.obj ⋙ 𝒯.val.p))
    (isFiberedInGroupoids_shrinkHoms 𝒯.val.p 𝒯.2)

/-- The category of torsors under `H` is equivalent to its model with small hom types. -/
private def smallAbelianSheafTorsorsEquivalence
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsStackOfTorsors B S hS]
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u}) :
    (abelianSheafTorsors B S hS H).val.obj ≌
      (smallAbelianSheafTorsors B S hS H).val.obj := by
  letI := abelianSheafTorsors_locallySmall B S hS H
  exact ShrinkHoms.equivalence.{u} (abelianSheafTorsors B S hS H).val.obj

/-- This equivalence lies over the site: its functor followed by the structure functor of the
small model is the structure functor of the category of `H`-torsors. -/
private lemma smallAbelianSheafTorsorsEquivalence_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsStackOfTorsors B S hS]
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u}) :
    (smallAbelianSheafTorsorsEquivalence B S hS H).functor ⋙
        (smallAbelianSheafTorsors B S hS H).val.p =
      (abelianSheafTorsors B S hS H).val.p := by
  let := abelianSheafTorsors_locallySmall B S hS H
  change ShrinkHoms.functor.{u} _ ⋙ (ShrinkHoms.inverse.{u} _ ⋙ _) = _
  rw [← Functor.assoc, shrinkHoms_functor_comp_inverse, Functor.id_comp]

/-- Its inverse lies over the site too: followed by the structure functor of the category of
`H`-torsors it is the structure functor of the small model. -/
private lemma smallAbelianSheafTorsorsEquivalence_inverse_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsStackOfTorsors B S hS]
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u}) :
    (smallAbelianSheafTorsorsEquivalence B S hS H).inverse ⋙
        (abelianSheafTorsors B S hS H).val.p =
      (smallAbelianSheafTorsors B S hS H).val.p := rfl

section StackTransport

universe uc vc ux vx uy vy
variable {C : Type uc} [Category.{vc} C]
  {X : Type ux} [Category.{vx} X] {Y : Type uy} [Category.{vy} Y]

/-- The image under an equivalence `F : X ⥤ Y` over `C` of a restriction of `point` along
`base`: a strongly cartesian lift of `base` at `F.obj point`, with source `F.obj res.pt`. -/
private noncomputable def restrictionMap
    (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) [F.IsEquivalence]
    (hF : F ⋙ q = p) {U V : C} (base : V ⟶ U) (point : X)
    (hpoint : p.obj point = U) (res : Functor.Restriction p base point hpoint) :
    Functor.Restriction q base (F.obj point) (by rw [← Functor.comp_obj, hF]; exact hpoint) where
  pt := F.obj res.pt
  hpt := by rw [← Functor.comp_obj, hF]; exact res.hpt
  hom := F.map res.hom
  isHomLift := by
    subst p
    have := res.isHomLift
    exact Functor.isHomLift_map_of_comp_eq rfl _ res.hom
  isCart := by
    subst p
    exact F.asEquivalence.isStronglyCartesian_map_functor q rfl _ res.hom res.isCart

attribute [local implicit_reducible] restrictionMap in
/-- The canonical comparison of two restrictions of one object along composable base morphisms
commutes with an equivalence over `C`: the comparison of the images is the image of the
comparison. -/
private lemma restrictionMap_compTo
    (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) [F.IsEquivalence]
    (hF : F ⋙ q = p) {U V W : C} (first : W ⟶ V) (second : V ⟶ U)
    {composite : W ⟶ U} (hcomp : composite = first ≫ second)
    (point : X) (hpoint : p.obj point = U)
    (res : Functor.Restriction p second point hpoint)
    (resW : Functor.Restriction p composite point hpoint) :
    Functor.Restriction.compTo q first second hcomp
        (restrictionMap p q F hF second point hpoint res)
        (restrictionMap p q F hF composite point hpoint resW) =
      F.map (Functor.Restriction.compTo p first second hcomp res resW) := by
  subst p
  let p := F ⋙ q
  let mapped := restrictionMap p q F rfl second point hpoint res
  let mappedW := restrictionMap p q F rfl composite point hpoint resW
  have := mapped.isCart
  have hmap : p.IsHomLift (eqToHom resW.hpt ≫ first ≫ eqToHom res.hpt.symm)
      (Functor.Restriction.compTo p first second hcomp res resW) := by
    dsimp [Functor.Restriction.compTo]
    infer_instance
  have hmapped : q.IsHomLift (eqToHom mappedW.hpt ≫ first ≫ eqToHom mapped.hpt.symm)
      (F.map (Functor.Restriction.compTo p first second hcomp res resW)) := by
    let := hmap
    exact Functor.isHomLift_map_of_comp_eq rfl _ _
  have hcanonical : q.IsHomLift (eqToHom mappedW.hpt ≫ first ≫ eqToHom mapped.hpt.symm)
      (Functor.Restriction.compTo q first second hcomp mapped mappedW) := by
    dsimp [Functor.Restriction.compTo]
    infer_instance
  apply Functor.IsStronglyCartesian.ext q
    (eqToHom mapped.hpt ≫ second ≫ eqToHom hpoint.symm) mapped.hom
    (eqToHom mappedW.hpt ≫ first ≫ eqToHom mapped.hpt.symm)
  rw [Functor.Restriction.compTo_hom]
  simpa [mapped, restrictionMap, ← Functor.map_comp] using
    congrArg F.map (Functor.Restriction.compTo_hom p first second hcomp res resW).symm

attribute [local implicit_reducible] restrictionMap in
/-- Being the canonical restriction of a fibre morphism along `base` is preserved by an
equivalence `F` with `F ⋙ q = p`: the images `F.map arrow` and `F.map arrowW` are again
canonical restrictions of one another, for the transported restrictions. -/
private lemma isRestrictionOf_map
    (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) [F.IsEquivalence]
    (hF : F ⋙ q = p) {Ux Uy V W : C} (base : W ⟶ V)
    {first : V ⟶ Ux} {second : V ⟶ Uy}
    {firstW : W ⟶ Ux} {secondW : W ⟶ Uy}
    (hfirst : firstW = base ≫ first) (hsecond : secondW = base ≫ second)
    (point other : X) (hpoint : p.obj point = Ux) (hother : p.obj other = Uy)
    (res : Functor.Restriction p first point hpoint)
    (otherRes : Functor.Restriction p second other hother)
    (resW : Functor.Restriction p firstW point hpoint)
    (otherResW : Functor.Restriction p secondW other hother)
    (arrow : res.pt ⟶ otherRes.pt) (arrowW : resW.pt ⟶ otherResW.pt)
    (h : Functor.IsRestrictionOf p base hfirst hsecond res otherRes resW otherResW arrow arrowW) :
    Functor.IsRestrictionOf q base hfirst hsecond
      (restrictionMap p q F hF first point hpoint res)
      (restrictionMap p q F hF second other hother otherRes)
      (restrictionMap p q F hF firstW point hpoint resW)
      (restrictionMap p q F hF secondW other hother otherResW)
      (F.map arrow) (F.map arrowW) := by
  dsimp only [Functor.IsRestrictionOf]
  rw [restrictionMap_compTo, restrictionMap_compTo, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg F.map h

universe wi
attribute [local implicit_reducible] CategoryTheory.ShrinkHoms.inverse restrictionMap in
/-- The image of a descent datum for `p` under an equivalence `F` with `F ⋙ q = p`: a descent
datum for `q` on the same covering family, with objects `F.obj (D.x i)` and gluing
isomorphisms `F.map (D.φ i j)`. -/
private noncomputable def descentDatumMap
    (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) [F.IsEquivalence]
    (hF : F ⋙ q = p) {U : C} {I : Type wi} (V : I → C) (f : ∀ i, V i ⟶ U)
    (Vij : I → I → C) (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, CategoryTheory.IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (Vijk : I → I → I → C) (s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j)
    (s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k)
    (hVijk : ∀ i j k, CategoryTheory.IsPullback
      (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k))
    (q₁ : ∀ i j k, Vijk i j k ⟶ V i) (q₂ : ∀ i j k, Vijk i j k ⟶ V j)
    (q₃ : ∀ i j k, Vijk i j k ⟶ V k)
    (hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j)
    (hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j)
    (hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k)
    (D : Functor.DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk
      q₁ q₂ q₃ hq₁ hq₂ hq₃) :
    Functor.DescentDatum q V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk
      q₁ q₂ q₃ hq₁ hq₂ hq₃ where
  x index := F.obj (D.x index)
  hx index := by rw [← Functor.comp_obj, hF]; exact D.hx index
  xrij first second := restrictionMap p q F hF _ _ _ (D.xrij first second)
  xrji first second := restrictionMap p q F hF _ _ _ (D.xrji first second)
  φ first second := F.map (D.φ first second)
  φ_fibreHom first second := by
    subst p
    let := D.φ_fibreHom first second
    exact Functor.isHomLift_map_of_comp_eq rfl _ _
  φ_iso first second := by let := D.φ_iso first second; infer_instance
  wi first second third := restrictionMap p q F hF _ _ _ (D.wi first second third)
  wj first second third := restrictionMap p q F hF _ _ _ (D.wj first second third)
  wk first second third := restrictionMap p q F hF _ _ _ (D.wk first second third)
  αij first second third := F.map (D.αij first second third)
  αjk first second third := F.map (D.αjk first second third)
  αik first second third := F.map (D.αik first second third)
  αij_restr first second third := isRestrictionOf_map p q F hF _ _ _ _ _ _ _ _ _ _ _ _ _
    (D.αij_restr first second third)
  αjk_restr first second third := isRestrictionOf_map p q F hF _ _ _ _ _ _ _ _ _ _ _ _ _
    (D.αjk_restr first second third)
  s₁₃ := D.s₁₃
  hs₁₃₁ := D.hs₁₃₁
  hs₁₃₂ := D.hs₁₃₂
  αik_restr first second third := isRestrictionOf_map p q F hF _ _ _ _ _ _ _ _ _ _ _ _ _
    (D.αik_restr first second third)
  cocycle first second third := by
    simpa only [Functor.map_comp] using congrArg F.map (D.cocycle first second third)

attribute [local implicit_reducible] CategoryTheory.ShrinkHoms.functor
    CategoryTheory.ShrinkHoms.inverse descentDatumMap restrictionMap in
/-- Being a stack in groupoids for `J` is unchanged by passing to the equivalent category
`ShrinkHoms X` with small hom types: `ShrinkHoms.inverse X ⋙ p` is again a stack in
groupoids. -/
private lemma shrinkHoms_stack
    {C : Type uc} [Category.{vc} C] {X : Type ux} [Category.{vx} X]
    [LocallySmall.{vc} X] (p : X ⥤ C) (J : GrothendieckTopology C)
    (hp : p.IsStackInGroupoids.{wi} J) :
    (ShrinkHoms.inverse.{vc} X ⋙ p).IsStackInGroupoids.{wi} J := by
  let up := ShrinkHoms.inverse.{vc} X
  let down := ShrinkHoms.functor.{vc} X
  let q := up ⋙ p
  have hdown : down ⋙ q = p := by
    rw [← Functor.assoc, shrinkHoms_functor_comp_inverse, Functor.id_comp]
  let : up.IsEquivalence := ShrinkHoms.instIsEquivalenceInverse X
  let : down.IsEquivalence := ShrinkHoms.instIsEquivalenceFunctor X
  let : LocallySmall.{vc} (BasedCategory.ofFunctor p).obj := inferInstanceAs (LocallySmall.{vc} X)
  have hup : ∀ (a b : X) (g : a ⟶ b), up.map (down.map g) = g :=
    fun a b g => (equivShrink (a ⟶ b)).symm_apply_apply g
  have hdn : ∀ (a b : ShrinkHoms X) (g : a ⟶ b), down.map (up.map g) = g :=
    fun a b g => (equivShrink (up.obj a ⟶ up.obj b)).apply_symm_apply g
  have hq : q.IsFiberedInGroupoids := isFiberedInGroupoids_shrinkHoms p hp.isFiberedInGroupoids
  refine ⟨hq, ?_, ?_⟩
  · intro U first second hfirst hsecond I V f hf Vij pr₁ pr₂ hVij xr yr xrij yrij arrows harrows
      hisos hcompat
    have mapped := hp.isom_isSheaf (up.obj first) (up.obj second) hfirst hsecond
      V f hf Vij pr₁ pr₂ hVij
      (fun index => restrictionMap q p up rfl _ _ _ (xr index))
      (fun index => restrictionMap q p up rfl _ _ _ (yr index))
      (fun first second => restrictionMap q p up rfl _ _ _ (xrij first second))
      (fun first second => restrictionMap q p up rfl _ _ _ (yrij first second))
    obtain ⟨arrow, ⟨hbase, hiso, hagree⟩, huniq⟩ := mapped (fun index => up.map (arrows index))
      (fun index => by
        let := harrows index
        exact Functor.isHomLift_map_of_comp_eq rfl
          (eqToHom (xr index).hpt ≫ eqToHom (yr index).hpt.symm) (arrows index))
      (fun index => by
        let := hisos index
        exact inferInstanceAs (IsIso (up.map (arrows index))))
      (by
        intro first second
        obtain ⟨arrow, hbase, hleft, hright⟩ := hcompat first second
        refine ⟨up.map arrow, ?_, ?_, ?_⟩
        · let := hbase
          exact Functor.isHomLift_map_of_comp_eq rfl
            (eqToHom (xrij first second).hpt ≫ eqToHom (yrij first second).hpt.symm) arrow
        · exact isRestrictionOf_map q p up rfl _ _ _ _ _ _ _ _ _ _ _ _ _ hleft
        · exact isRestrictionOf_map q p up rfl _ _ _ _ _ _ _ _ _ _ _ _ _ hright)
    refine ⟨down.map arrow, ⟨?_, ?_, ?_⟩, ?_⟩
    · have hb : p.IsHomLift (eqToHom hfirst ≫ eqToHom hsecond.symm) arrow := hbase
      exact Functor.isHomLift_map_of_comp_eq hdown
        (eqToHom hfirst ≫ eqToHom hsecond.symm) arrow
    · let := hiso
      exact inferInstanceAs (IsIso (down.map arrow))
    · intro index
      apply up.map_injective
      have e1 : up.map ((xr index).hom ≫ down.map arrow)
          = up.map (xr index).hom ≫ arrow := by
        refine Eq.trans (up.map_comp _ _) ?_
        exact congrArg (fun k => up.map (xr index).hom ≫ k) (hup _ _ arrow)
      exact e1.trans ((hagree index).trans (up.map_comp _ _).symm)
    · intro candidate hcand
      apply up.map_injective
      have h : up.map candidate = arrow := huniq (up.map candidate) ⟨?_, ?_, ?_⟩
      · exact h.trans (hup _ _ arrow).symm
      · let := hcand.1
        exact Functor.isHomLift_map_of_comp_eq rfl _ _
      · let := hcand.2.1
        infer_instance
      · intro index
        have hc := congrArg up.map (hcand.2.2 index)
        simp only [up.map_comp] at hc
        exact hc
  · intro U I V f hf Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ D
    let mapped := descentDatumMap q p up rfl V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk
      q₁ q₂ q₃ hq₁ hq₂ hq₃ D
    obtain ⟨point, hpoint, res, arrows, hbases, hisos, hcompat⟩ :=
      hp.effective_descent V f hf Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk
        q₁ q₂ q₃ hq₁ hq₂ hq₃ mapped
    -- transport of the restriction relation, used for both sides of the gluing isomorphism
    have side : ∀ {i : I} {Z : C} (e : Z ⟶ V i) (r : q.Restriction e (D.x i) (D.hx i))
        {b : Z ⟶ U} (hb : b = e ≫ f i) (rW : p.Restriction b point hpoint)
        (l : rW.pt ⟶ (restrictionMap q p up rfl e (D.x i) (D.hx i) r).pt),
        p.IsRestrictionOf e hb (by simp) (res i)
          (Functor.Restriction.id p (mapped.x i) (mapped.hx i)) rW
          (restrictionMap q p up rfl e (D.x i) (D.hx i) r) (arrows i) l →
        q.IsRestrictionOf e hb (by simp)
          (restrictionMap p q down hdown (f i) point hpoint (res i))
          (Functor.Restriction.id q (D.x i) (D.hx i))
          (restrictionMap p q down hdown b point hpoint rW)
          r (down.map (arrows i)) (down.map l) := by
      intro i Z e r b hb rW l hl
      have transported := isRestrictionOf_map p q down hdown _ _ _ _ _ _ _ _ _ _ _ _ _ hl
      -- restricting `r` along `up` and then along `down` gives back `r`
      have hres : restrictionMap p q down hdown _ _ _
          (restrictionMap q p up rfl _ _ _ r) = r := by
        cases r
        simp only [restrictionMap]
        congr 1
        exact hdn _ _ _
      dsimp only [mapped, descentDatumMap] at transported
      dsimp only [Functor.IsRestrictionOf] at transported ⊢
      have hcomp : Functor.Restriction.compTo q e (𝟙 (V i))
          (by simp) (restrictionMap p q down hdown _ _ _
            (Functor.Restriction.id p (up.obj (D.x i)) (mapped.hx i)))
          (restrictionMap p q down hdown _ _ _
            (restrictionMap q p up rfl _ _ _ r)) =
          Functor.Restriction.compTo q e (𝟙 (V i))
            (by simp) (Functor.Restriction.id q (D.x i) (D.hx i)) r := by
        congr 1
      -- the comparison for the identity restriction is the canonical one
      rw [hcomp] at transported
      simpa [mapped, descentDatumMap, restrictionMap, Functor.Restriction.id,
        q, up, down, ShrinkHoms.functor, ShrinkHoms.inverse,
        ShrinkHoms.fromShrinkHoms, ShrinkHoms.toShrinkHoms] using transported
    refine ⟨down.obj point, ?_,
      (fun index => restrictionMap p q down hdown _ _ _ (res index)),
      (fun index => down.map (arrows index)), ?_, ?_, ?_⟩
    · change p.obj (up.obj (down.obj point)) = U
      exact hpoint
    · intro index
      let := hbases index
      exact Functor.isHomLift_map_of_comp_eq hdown
        (eqToHom (res index).hpt ≫ eqToHom (mapped.hx index).symm) (arrows index)
    · intro index
      let := hisos index
      exact inferInstanceAs (IsIso (down.map (arrows index)))
    · intro first second
      obtain ⟨resW, left, right, hleftbase, hrightbase, hleftIso, hrightIso,
        hleft, hright, hagree⟩ := hcompat first second
      refine ⟨restrictionMap p q down hdown _ _ _ resW,
        down.map left, down.map right, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · let := hleftbase
        exact Functor.isHomLift_map_of_comp_eq hdown
          (eqToHom resW.hpt ≫ eqToHom (mapped.xrij first second).hpt.symm) left
      · let := hrightbase
        exact Functor.isHomLift_map_of_comp_eq hdown
          (eqToHom resW.hpt ≫ eqToHom (mapped.xrji first second).hpt.symm) right
      · let := hleftIso
        exact inferInstanceAs (IsIso (down.map left))
      · let := hrightIso
        exact inferInstanceAs (IsIso (down.map right))
      -- the restriction relations on the two sides of the gluing isomorphism
      · exact side (pr₁ first second) (D.xrij first second) _ resW left hleft
      · exact side (pr₂ first second) (D.xrji first second) _ resW right hright
      · refine Eq.trans ?_ (congrArg down.map hagree)
        refine Eq.trans ?_ (down.map_comp left (mapped.φ first second)).symm
        exact congrArg (fun k => down.map left ≫ k) (hdn _ _ (D.φ first second)).symm

end StackTransport

/-- The small model of the category of `H`-torsors is a stack in groupoids over the big fppf
site of `S`. -/
private lemma smallAbelianSheafTorsors_isStackInGroupoids
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsStackOfTorsors B S hS]
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u}) :
    (smallAbelianSheafTorsors B S hS H).val.p.IsStackInGroupoids.{u + 1}
      (AlgebraicGeometry.BigFppfOver.topology B S hS) := by
  let := abelianSheafTorsors_locallySmall B S hS H
  exact shrinkHoms_stack _ _ (abelianSheafTorsors_isStackInGroupoids B S hS H)

/-- Every fibre of the small model of the stack of `H`-torsors is nonempty: the trivial
`H`-torsor over `U` lies over `U`. -/
private lemma smallAbelianSheafTorsors_fiber_nonempty
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsStackOfTorsors B S hS]
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    (U : AlgebraicGeometry.BigFppfOver B S hS) :
    Nonempty ((smallAbelianSheafTorsors B S hS H).val.p.Fiber U) :=
  ⟨⟨(smallAbelianSheafTorsorsEquivalence B S hS H).functor.obj
    (trivialAbelianSheafTorsor B S hS H U), rfl⟩⟩

attribute [local implicit_reducible] abelianSheafTorsors sheafGroupOver
    unitPresheafIsTerminal in
/-- For injective `H` every `H`-torsor is trivial, so any two objects of the fibre over `U`
are isomorphic and that fibre is a connected groupoid. -/
private lemma abelianSheafTorsors_fiber_connected
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsStackOfTorsors B S hS]
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    [Injective H] (U : AlgebraicGeometry.BigFppfOver B S hS)
    (x y : (abelianSheafTorsors B S hS H).val.p.Fiber U) :
    Nonempty (x ≅ y) := by
  let := (abelianSheafTorsors B S hS H).2.fiber_isGroupoid U
  rcases x with ⟨⟨V, b, F, act, hF⟩, hx⟩
  change V = U at hx
  subst V
  rcases y with ⟨⟨V, b', F', act', hF'⟩, hy⟩
  change V = U at hy
  subst V
  have hb : b' = b := unitPresheafIsTerminal.hom_ext _ _
  subst b'
  let T : ClassifyingTorsors.Torsor (sheafGroupOver H) := ⟨U, b, F, act, hF⟩
  let T' : ClassifyingTorsors.Torsor (sheafGroupOver H) := ⟨U, b, F', act', hF'⟩
  obtain ⟨e⟩ := abelianSheafTorsor_isTrivial H T
  obtain ⟨e'⟩ := abelianSheafTorsor_isTrivial H T'
  let := act
  let := act'
  let φ := e.symm ≪≫ e'
  let g : F ⟶ F' := φ.hom.hom
  have : IsIso g := (Mod.forget _).map_isIso φ.hom
  have : IsIso g.left := (Over.forget _).map_isIso g
  let f : T ⟶ T' :=
    { f := 𝟙 U
      comp_b := by change yoneda.map (𝟙 U) ≫ b = b; simp
      g := g.left
      isPullback := IsPullback.of_horiz_isIso ⟨by
        change g.left ≫ F'.hom = F.hom ≫ yoneda.map (𝟙 U)
        rw [CategoryTheory.Functor.map_id, Category.comp_id]
        exact Over.w g⟩
      smul_comp := by
        have he : ClassifyingTorsors.actionBaseChange (T := T) (T' := T') (𝟙 U)
            (by change yoneda.map (𝟙 U) ≫ b = b; simp) g.left (by
              change F.hom ≫ yoneda.map (𝟙 U) = g.left ≫ F'.hom
              rw [CategoryTheory.Functor.map_id, Category.comp_id]
              exact (Over.w g).symm) =
            (T.group ◁ g).left := by
          apply pullback.hom_ext
          · refine (ClassifyingTorsors.actionBaseChange_fst _ _ _ _).trans ?_
            have hg : ClassifyingTorsors.groupBaseChange (T := T) (T' := T')
                (𝟙 U) (by change yoneda.map (𝟙 U) ≫ b = b; simp) = 𝟙 T.group.left := by
              apply pullback.hom_ext <;>
                simp only [ClassifyingTorsors.groupBaseChange, pullback.map, Category.comp_id,
                  CategoryTheory.Functor.map_id, pullback.lift_fst_snd, Category.id_comp, T, T']
              all_goals exact (Category.id_comp _).symm
            refine (_ ≫= hg).trans ?_
            exact (Category.comp_id _).trans (Over.whiskerLeft_left_fst (R := T.group) g).symm
          · change ClassifyingTorsors.actionBaseChange _ _ _ _ ≫ _ =
              (T.group ◁ g).left ≫ pullback.snd T.group.hom F'.hom
            rw [ClassifyingTorsors.actionBaseChange_snd, Over.whiskerLeft_left_snd]
            rfl
        rw [he]
        exact congrArg Over.Hom.left (IsModHom.smul_hom (A := T.group) (f := g)) }
  let x₀ : (abelianSheafTorsors B S hS H).val.p.Fiber U := ⟨T, rfl⟩
  let y₀ : (abelianSheafTorsors B S hS H).val.p.Fiber U := ⟨T', rfl⟩
  let f' : x₀ ⟶ y₀ := ⟨f, IsHomLift.of_fac' _ _ _ rfl rfl rfl⟩
  exact ⟨asIso f'⟩

/-- For injective `H` any two objects of the fibre of the small model of the stack of
`H`-torsors over `U` are isomorphic. -/
private lemma smallAbelianSheafTorsors_fiber_connected
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsStackOfTorsors B S hS]
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    [Injective H] (U : AlgebraicGeometry.BigFppfOver B S hS)
    (x y : (smallAbelianSheafTorsors B S hS H).val.p.Fiber U) :
    Nonempty (x ≅ y) := by
  let := abelianSheafTorsors_locallySmall B S hS H
  let := (smallAbelianSheafTorsors B S hS H).2.fiber_isGroupoid U
  let E := smallAbelianSheafTorsorsEquivalence B S hS H
  let x' : (abelianSheafTorsors B S hS H).val.p.Fiber U := ⟨E.inverse.obj x.1, x.2⟩
  let y' : (abelianSheafTorsors B S hS H).val.p.Fiber U := ⟨E.inverse.obj y.1, y.2⟩
  obtain ⟨e⟩ := abelianSheafTorsors_fiber_connected B S hS H U x' y'
  let f : x ⟶ y := ⟨E.functor.map e.hom.1, by
    let := e.hom.2
    exact Functor.isHomLift_map_of_comp_eq
      (smallAbelianSheafTorsorsEquivalence_comp B S hS H) (𝟙 U) e.hom.1⟩
  exact ⟨asIso f⟩

section

open CartesianMonoidalCategory
/-- Right translation of a group object `G` in a cartesian monoidal category by a point
`s : 𝟙_ C ⟶ G`, acting as `g ↦ g * s` on generalized elements. -/
private def regularTranslation {C : Type u} [Category.{v} C]
    [CartesianMonoidalCategory C] (G : C) [GrpObj G] (s : 𝟙_ C ⟶ G) : G ⟶ G :=
  (𝟙 G) * (toUnit G ≫ s)
/-- Right translation of a group object by a point is an isomorphism. -/
private lemma regularTranslation_isIso {C : Type u} [Category.{v} C]
    [CartesianMonoidalCategory C] (G : C) [GrpObj G] (s : 𝟙_ C ⟶ G) :
    IsIso (regularTranslation G s) := by
  rw [isIso_iff_yoneda_map_bijective]
  intro Z
  have h (f : Z ⟶ G) : f ≫ regularTranslation G s = f * (toUnit Z ≫ s) := by
    simp [regularTranslation, MonObj.comp_mul]
  change Function.Bijective (fun f : Z ⟶ G => f ≫ regularTranslation G s)
  simp_rw [h]
  exact (Group.mulRight_bijective _)
/-- Right translation of `G` by a point is a morphism for the regular left action of `G` on
itself, since left and right multiplication commute. -/
private lemma regularTranslation_isModHom {C : Type u} [Category.{v} C]
    [CartesianMonoidalCategory C] (G : C) [GrpObj G] (s : 𝟙_ C ⟶ G) :
    letI : ModObj G G := .regular G
    IsModHom G (regularTranslation G s) := by
  let : ModObj G G := .regular G
  constructor
  change μ[G] ≫ regularTranslation G s = G ◁ regularTranslation G s ≫ μ[G]
  rw [MonObj.mul_eq_mul, MonObj.comp_mul]
  simp [regularTranslation, MonObj.comp_mul, mul_assoc]
/-- The endomorphism of a torsor `T` over the identity of `T.U` given by an equivariant
automorphism `g` of its total object `T.F`. -/
private def torsorEndHom
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {G : Grp (Over (unitPresheaf.{u} (C := AlgebraicGeometry.BigFppfOver B S hS)))}
    (T : ClassifyingTorsors.Torsor G) (g : T.F ⟶ T.F) [IsIso g] [IsModHom T.group g] : T ⟶ T where
  f := 𝟙 T.U
  comp_b := by simp
  g := g.left
  isPullback := by
    have : IsIso g.left := (Over.forget _).map_isIso g
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  smul_comp := by
    have he : ClassifyingTorsors.actionBaseChange (T := T) (T' := T) (𝟙 T.U)
        (by simp) g.left (by simp) = (T.group ◁ g).left := by
      apply pullback.hom_ext
      · change _ = (T.group ◁ g).left ≫ pullback.fst T.group.hom T.F.hom
        rw [ClassifyingTorsors.actionBaseChange_fst, Over.whiskerLeft_left_fst,
          ClassifyingTorsors.groupBaseChange_id]
        exact Category.comp_id _
      · change _ = (T.group ◁ g).left ≫ pullback.snd T.group.hom T.F.hom
        rw [ClassifyingTorsors.actionBaseChange_snd, Over.whiskerLeft_left_snd]
        rfl
    rw [he]
    exact congrArg Over.Hom.left (IsModHom.smul_hom (A := T.group) (f := g))

/-- The image under `f : T ⟶ T'` of a global section of the total object `T.F`, as a point
of `T'.F` lying over `T.U` through `f.f`. -/
private def torsorSectionMap
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {G : Grp (Over (unitPresheaf.{u} (C := AlgebraicGeometry.BigFppfOver B S hS)))}
    {T T' : ClassifyingTorsors.Torsor G} (f : T ⟶ T')
    (z : 𝟙_ (Over (yoneda.obj T.U)) ⟶ T.F) :
    Over.mk (yoneda.map f.f) ⟶ T'.F :=
  Over.homMk (z.left ≫ f.g) (by
    rw [Category.assoc, f.isPullback.w, ← Category.assoc, Over.w z]
    exact Category.id_comp _)

/-- The image under base change along `f.f` of a global section of the group `T.group`, as a
point of `T'.group` lying over `T.U`. -/
private def groupSectionMap
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {G : Grp (Over (unitPresheaf.{u} (C := AlgebraicGeometry.BigFppfOver B S hS)))}
    {T T' : ClassifyingTorsors.Torsor G} (f : T ⟶ T')
    (a : 𝟙_ (Over (yoneda.obj T.U)) ⟶ T.group) :
    Over.mk (yoneda.map f.f) ⟶ T'.group :=
  Over.homMk (a.left ≫ ClassifyingTorsors.groupBaseChange f.f f.comp_b)
    ((Category.assoc _ _ _).trans
      ((a.left ≫= ClassifyingTorsors.groupBaseChange_snd f.f f.comp_b).trans
        ((Category.assoc _ _ _).symm.trans
          ((Over.w a =≫ yoneda.map f.f).trans (Category.id_comp _)))))

attribute [local implicit_reducible] ClassifyingTorsors.pullbackGroup groupSectionMap
    torsorSectionMap in
/-- Pushing a section forward along `f : T ⟶ T'` is equivariant: the image of `a • z` is the
image of `a` acting on the image of `z`. -/
private lemma torsorSectionMap_smul
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {G : Grp (Over (unitPresheaf.{u} (C := AlgebraicGeometry.BigFppfOver B S hS)))}
    {T T' : ClassifyingTorsors.Torsor G} (f : T ⟶ T')
    (a : 𝟙_ (Over (yoneda.obj T.U)) ⟶ T.group)
    (z : 𝟙_ (Over (yoneda.obj T.U)) ⟶ T.F) :
    torsorSectionMap f (a • z) = groupSectionMap f a • torsorSectionMap f z := by
  apply Over.OverMorphism.ext
  change (lift a z).left ≫ (γ[T.group,T.F]).left ≫ f.g =
    (lift (groupSectionMap f a) (torsorSectionMap f z)).left ≫ (γ[T'.group,T'.F]).left
  rw [f.smul_comp]
  refine (Category.assoc _ _ _).symm.trans ?_
  congr 1
  apply pullback.hom_ext <;>
    simp only [Over.tensorUnit_left, ClassifyingTorsors.Torsor.group,
      ClassifyingTorsors.pullbackGroup, Over.tensorObj_left, Over.lift_left, groupSectionMap,
      Over.mk_left, torsorSectionMap, Over.homMk_left]
  all_goals first
    | exact (Category.assoc _ _ _).trans
        ((_ ≫= ClassifyingTorsors.actionBaseChange_fst ..).trans
          ((pullback.lift_fst_assoc ..).trans (pullback.lift_fst ..).symm))
    | exact (Category.assoc _ _ _).trans
        ((_ ≫= ClassifyingTorsors.actionBaseChange_snd ..).trans
          ((pullback.lift_snd_assoc ..).trans (pullback.lift_snd ..).symm))

attribute [local implicit_reducible] ClassifyingTorsors.pullbackGroup sheafGroupOver
    sheafGroupSectionMulEquiv in
/-- Global sections over `U` of the group object attached to `H`, pulled back along `b`, form
the group `H(U)` written multiplicatively. -/
private def unitGroupSectionMulEquiv
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    (U : AlgebraicGeometry.BigFppfOver B S hS) (b : yoneda.obj U ⟶ unitPresheaf) :
    (𝟙_ (Over (yoneda.obj U)) ⟶ (ClassifyingTorsors.pullbackGroup (sheafGroupOver H) U b).X) ≃*
      Multiplicative (H.obj.obj (op U)) := by
  let e : 𝟙_ (Over (yoneda.obj U)) ≅ Over.mk (yoneda.map (𝟙 U)) :=
    Over.isoMk (Iso.refl _) (by simp)
  let ce := sheafGroupSectionMulEquiv H U b (Over.mk (𝟙 U))
  exact
    { toFun := fun a => ce (e.inv ≫ a)
      invFun := fun a => e.hom ≫ ce.symm a
      left_inv := by intro a; simp
      right_inv := by
        intro a
        simp only [Over.mk_left, Over.mk_hom, Iso.inv_hom_id_assoc]
        exact ce.apply_symm_apply a
      map_mul' := by intro a b; rw [MonObj.comp_mul, map_mul]; rfl }

attribute [local implicit_reducible] ClassifyingTorsors.pullbackGroup sheafGroupOver
    sheafGroupSectionMulEquiv unitGroupSectionMulEquiv in
/-- The identification of global sections with `H(U)` sends `a` to the section of `H` read off
from `a` through the first projection of the pullback. -/
private lemma unitGroupSectionMulEquiv_apply
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    (U : AlgebraicGeometry.BigFppfOver B S hS) (b : yoneda.obj U ⟶ unitPresheaf)
    (a : 𝟙_ (Over (yoneda.obj U)) ⟶ (ClassifyingTorsors.pullbackGroup (sheafGroupOver H) U b).X) :
    unitGroupSectionMulEquiv H U b a =
      Multiplicative.ofAdd (yonedaEquiv (a.left ≫ pullback.fst (sheafGroupOver H).X.hom b)) := by
  exact sheafGroupSectionMulEquiv_apply H U b (Over.mk (𝟙 U)) a

attribute [local implicit_reducible] groupSectionMap sheafGroupOver sheafGroupSectionMulEquiv
    unitGroupSectionMulEquiv in
/-- Base change along `f : T ⟶ T'` leaves unchanged the section of `H` named by a global
section `a` of `T.group`. -/
private lemma groupSectionMap_equiv
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    {T T' : ClassifyingTorsors.Torsor (sheafGroupOver H)} (f : T ⟶ T')
    (a : 𝟙_ (Over (yoneda.obj T.U)) ⟶ T.group) :
    sheafGroupSectionMulEquiv H T'.U T'.b (Over.mk f.f) (groupSectionMap f a) =
      unitGroupSectionMulEquiv H T.U T.b a := by
  have h : (groupSectionMap f a).left ≫ pullback.fst (sheafGroupOver H).X.hom T'.b =
      a.left ≫ pullback.fst (sheafGroupOver H).X.hom T.b :=
    (Category.assoc a.left (ClassifyingTorsors.groupBaseChange f.f f.comp_b)
      (pullback.fst (sheafGroupOver H).X.hom T'.b)).trans
      (a.left ≫= ClassifyingTorsors.groupBaseChange_fst f.f f.comp_b)
  rw [sheafGroupSectionMulEquiv_apply, unitGroupSectionMulEquiv_apply]
  exact congrArg _ (congrArg _ h)

attribute [local implicit_reducible] regularTranslation torsorEndHom trivialAbelianSheafTorsor
    unitGroupSectionMulEquiv in
/-- The automorphism of the trivial `H`-torsor over `U` given by translation by a section `s`
of `H` over `U`. -/
private def regularTorsorTranslation
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    [IsStackOfTorsors B S hS]
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    (U : AlgebraicGeometry.BigFppfOver B S hS) (s : H.obj.obj (op U)) :
    trivialAbelianSheafTorsor B S hS H U ⟶ trivialAbelianSheafTorsor B S hS H U := by
  let T := trivialAbelianSheafTorsor B S hS H U
  let a := (unitGroupSectionMulEquiv H U T.b).symm (Multiplicative.ofAdd s)
  letI := regularTranslation_isIso T.group a
  letI := regularTranslation_isModHom T.group a
  exact torsorEndHom T (regularTranslation T.group a)

/-- The section of `H` over `W` underlying a `W`-point of the group object attached to `H`
pulled back to `U`, read off through the first projection. -/
private def groupCoordinate
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    {U W : AlgebraicGeometry.BigFppfOver B S hS} (b : yoneda.obj U ⟶ unitPresheaf)
    (f : yoneda.obj W ⟶ (ClassifyingTorsors.pullbackGroup (sheafGroupOver H) U b).X.left) :
    H.obj.obj (op W) := yonedaEquiv (f ≫ pullback.fst (sheafGroupOver H).X.hom b)

attribute [local implicit_reducible] groupCoordinate groupSectionMap regularTorsorTranslation
    regularTranslation sheafGroupSectionMulEquiv torsorEndHom torsorSectionMap
    trivialAbelianSheafTorsor unitGroupSectionMulEquiv in
/-- Composing with the translation by `s` adds `s` to the coordinate: the coordinate of
`z ≫ (regularTorsorTranslation H U s).g ≫ δ.g` is `s` plus that of `z ≫ δ.g`. -/
private lemma regularTorsorTranslation_coordinate
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    [IsStackOfTorsors B S hS]
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    (U V : AlgebraicGeometry.BigFppfOver B S hS) (s : H.obj.obj (op U))
    (δ : trivialAbelianSheafTorsor B S hS H U ⟶ trivialAbelianSheafTorsor B S hS H V)
    (z : 𝟙_ (Over (yoneda.obj U)) ⟶ (trivialAbelianSheafTorsor B S hS H U).F) :
    groupCoordinate H (trivialAbelianSheafTorsor B S hS H V).b
      (z.left ≫ (regularTorsorTranslation H U s).g ≫ δ.g) =
      s + groupCoordinate H (trivialAbelianSheafTorsor B S hS H V).b (z.left ≫ δ.g) := by
  let T := trivialAbelianSheafTorsor B S hS H U
  let T' := trivialAbelianSheafTorsor B S hS H V
  let z' : 𝟙_ (Over (yoneda.obj U)) ⟶ T.group := z
  let a : 𝟙_ (Over (yoneda.obj U)) ⟶ T.group :=
    (unitGroupSectionMulEquiv H T.U T.b).symm (Multiplicative.ofAdd s)
  have hcomm : z' * a = a * z' := by
    apply (unitGroupSectionMulEquiv H T.U T.b).injective
    simp only [map_mul]
    exact mul_comm _ _
  have hz : z' ≫ regularTranslation T.group a = a • z' := by
    change z' ≫ regularTranslation T.group a = a * z'
    rw [regularTranslation, MonObj.comp_mul, Category.comp_id]
    have hunit : z' ≫ toUnit T.group = 𝟙 _ := toUnit_unique _ _
    rw [← Category.assoc, hunit, Category.id_comp]
    exact hcomm
  have he := torsorSectionMap_smul δ a z'
  have he' := congrArg (sheafGroupSectionMulEquiv H T'.U T'.b (Over.mk δ.f)) he
  let q : Over.mk (yoneda.map δ.f) ⟶ T'.group := torsorSectionMap δ z'
  let r : Over.mk (yoneda.map δ.f) ⟶ T'.group := groupSectionMap δ a
  change sheafGroupSectionMulEquiv H T'.U T'.b (Over.mk δ.f)
      (torsorSectionMap δ (a • z')) =
    sheafGroupSectionMulEquiv H T'.U T'.b (Over.mk δ.f)
      (r * q) at he'
  rw [map_mul] at he'
  dsimp only [r, q] at he'
  rw [groupSectionMap_equiv H δ a] at he'
  have ha : unitGroupSectionMulEquiv H T.U T.b a = Multiplicative.ofAdd s :=
    (unitGroupSectionMulEquiv H T.U T.b).apply_symm_apply _
  rw [ha] at he'
  rw [← hz] at he'
  simp only [sheafGroupSectionMulEquiv_apply] at he'
  have he'' := congrArg Multiplicative.toAdd he'
  dsimp only [torsorSectionMap, Over.homMk_left, Over.comp_left,
    Multiplicative.toAdd, Multiplicative.ofAdd] at he''
  dsimp only [regularTorsorTranslation, torsorEndHom, groupCoordinate]
  convert he'' using 1
  rfl

attribute [local implicit_reducible] CategoryTheory.ShrinkHoms.functor
    CategoryTheory.ShrinkHoms.inverse groupCoordinate regularTorsorTranslation sheafGroupOver
    trivialAbelianSheafTorsor in
/-- If `δ` and its composite with the translation by `s` both factor through a torsor `T`
through one and the same `a`, then `s` is the pullback along `a.f` of a section of `H`
over `T.U`. -/
private lemma section_descends_of_translation_factors
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    [IsStackOfTorsors B S hS]
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u}) [Injective H]
    (U V : AlgebraicGeometry.BigFppfOver B S hS) (s : H.obj.obj (op U))
    (δ : trivialAbelianSheafTorsor B S hS H U ⟶ trivialAbelianSheafTorsor B S hS H V)
    (T : ClassifyingTorsors.Torsor (sheafGroupOver H))
    (a : trivialAbelianSheafTorsor B S hS H U ⟶ T)
    (b d : T ⟶ trivialAbelianSheafTorsor B S hS H V)
    (hd : a ≫ d = δ) (hb : a ≫ b = regularTorsorTranslation H U s ≫ δ) :
    ∃ t : H.obj.obj (op T.U), H.obj.map a.f.op t = s := by
  let R := trivialAbelianSheafTorsor B S hS H V
  let P := trivialAbelianSheafTorsor B S hS H U
  let pr := pullback.fst (sheafGroupOver H).X.hom R.b
  obtain ⟨z⟩ := abelianSheafTorsor_hasSection H T
  let z₀ : 𝟙_ (Over (yoneda.obj U)) ⟶ P.F := Over.homMk
    (a.isPullback.lift (yoneda.map a.f ≫ z.left) (𝟙 _) (by simp [Over.w z]))
    (a.isPullback.lift_snd _ _ _)
  have hz₀ : z₀.left ≫ a.g = yoneda.map a.f ≫ z.left := a.isPullback.lift_fst _ _ _
  let tb : H.obj.obj (op T.U) := groupCoordinate H R.b (z.left ≫ b.g)
  let td : H.obj.obj (op T.U) := groupCoordinate H R.b (z.left ≫ d.g)
  have hmap (f : T ⟶ R) : H.obj.map a.f.op (groupCoordinate H R.b (z.left ≫ f.g)) =
      groupCoordinate H R.b (z₀.left ≫ a.g ≫ f.g) := by
    let pr' : R.F.left ⟶ H.obj ⋙ forget AddCommGrpCat := pr
    have hn := yonedaEquiv_naturality (F := H.obj ⋙ forget AddCommGrpCat)
      (z.left ≫ f.g ≫ pr') a.f
    apply hn.trans
    have he := congrArg
      (fun q : yoneda.obj U ⟶ T.F.left => yonedaEquiv (q ≫ f.g ≫ pr')) hz₀.symm
    dsimp only [groupCoordinate]
    convert he using 1
    rfl
  refine ⟨tb - td, ?_⟩
  dsimp only [tb, td]
  rw [map_sub, hmap b, hmap d]
  have hbg := congrArg (fun f => ClassifyingTorsors.TorsorHom.g f) hb
  have hdg := congrArg (fun f => ClassifyingTorsors.TorsorHom.g f) hd
  change a.g ≫ b.g = (regularTorsorTranslation H U s).g ≫ δ.g at hbg
  change a.g ≫ d.g = δ.g at hdg
  rw [hbg, hdg, regularTorsorTranslation_coordinate H U V s δ z₀]
  exact add_sub_cancel_right _ _

/-- The equivalence between the category of `H`-torsors and its small model composes with its
inverse to the identity functor on the nose. -/
private lemma smallAbelianSheafTorsorsEquivalence_functor_inverse
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsStackOfTorsors B S hS]
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u}) :
    (smallAbelianSheafTorsorsEquivalence B S hS H).functor ⋙
      (smallAbelianSheafTorsorsEquivalence B S hS H).inverse = 𝟭 _ := by
  let := abelianSheafTorsors_locallySmall B S hS H
  exact shrinkHoms_functor_comp_inverse

attribute [local implicit_reducible] CategoryTheory.ShrinkHoms.functor
    CategoryTheory.ShrinkHoms.inverse abelianSheafTorsors regularTorsorTranslation
    smallAbelianSheafTorsors smallAbelianSheafTorsorsEquivalence trivialAbelianSheafTorsor in
/-- When the canonical comparison from the colimit of the stage fibres is full, every
section of `H` over the cone point is the pullback of a section over some stage
`D.obj k`. -/
private lemma sheaf_sections_descend_of_full_comparison
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsStackOfTorsors B S hS]
    (H : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u}) [Injective H]
    {I : Type v} [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ AlgebraicGeometry.BigFppfOver B S hS) (c : Cone D)
    (hfull : letI := (smallAbelianSheafTorsors B S hS H).2.isFibered
      (Deformation.Artin.colimitComparison (smallAbelianSheafTorsors B S hS H).val.p D c).Full)
    (s : H.obj.obj (op c.pt)) :
    ∃ (k : I) (t : H.obj.obj (op (D.obj k))), H.obj.map (c.π.app k).op t = s := by
  let X := smallAbelianSheafTorsors B S hS H
  let p := X.val.p
  let : p.IsFibered := X.2.isFibered
  let : (Deformation.Artin.colimitComparison p D c).Full := hfull
  let E := smallAbelianSheafTorsorsEquivalence B S hS H
  obtain ⟨i⟩ := (IsCofiltered.nonempty : Nonempty I)
  let P := trivialAbelianSheafTorsor B S hS H c.pt
  let R := trivialAbelianSheafTorsor B S hS H (D.obj i)
  let x : p.Fiber c.pt := ⟨E.functor.obj P, rfl⟩
  let xi : p.Fiber (D.obj i) := ⟨E.functor.obj R, rfl⟩
  let xu := Functor.pullbackFiber p xi (c.π.app i)
  obtain ⟨e⟩ := smallAbelianSheafTorsors_fiber_connected B S hS H c.pt x xu
  let δ := Functor.Fiber.fiberInclusion.map e.hom ≫
    Functor.IsPreFibered.pullbackMap xi.2 (c.π.app i)
  let : p.IsHomLift (c.π.app i) δ := by
    have := e.hom.2
    simpa only [Category.id_comp] using
      (inferInstance : p.IsHomLift (𝟙 c.pt ≫ c.π.app i) δ)
  let τ := regularTorsorTranslation H c.pt s
  let : (abelianSheafTorsors B S hS H).val.p.IsHomLift (𝟙 c.pt) τ :=
    IsHomLift.of_fac' _ _ _ rfl rfl rfl
  let : p.IsHomLift (𝟙 c.pt) (E.functor.map τ) :=
    Functor.isHomLift_map_of_comp_eq (smallAbelianSheafTorsorsEquivalence_comp B S hS H) _ τ
  let g := E.functor.map τ ≫ δ
  let : p.IsHomLift (c.π.app i) g := by
    simpa only [Category.id_comp] using
      (inferInstance : p.IsHomLift (𝟙 c.pt ≫ c.π.app i) g)
  obtain ⟨k, ik, jk, xk, d, δk, gk, hd, hδd, hδk, hgk, hfac⟩ :=
    factor_through_stage_with_projection p p X.2 (𝟭 _) rfl D c i i x xi xi δ g
  let T := E.inverse.obj xk.1
  let a := E.inverse.map δk
  let b := E.inverse.map gk
  let d' := E.inverse.map d
  let δ' := E.inverse.map δ
  have had : a ≫ d' = δ' := by
    exact (E.inverse.map_comp δk d).symm.trans (congrArg E.inverse.map hδd)
  have hab : a ≫ b = τ ≫ δ' := by
    have hτ : E.inverse.map (E.functor.map τ) = τ := by
      exact Functor.congr_hom (smallAbelianSheafTorsorsEquivalence_functor_inverse B S hS H) τ
    change δk ≫ gk = g at hfac
    rw [← E.inverse.map_comp, hfac]
    change E.inverse.map (E.functor.map τ ≫ δ) = _
    rw [E.inverse.map_comp, hτ]
    rfl
  obtain ⟨r, hr⟩ := section_descends_of_translation_factors H c.pt (D.obj i) s δ' T a b d' had hab
  have hT : T.U = D.obj k := xk.2
  have ha : a.f = c.π.app k ≫ eqToHom hT.symm := by
    let := hδk
    have := Functor.isHomLift_map_of_comp_eq
      (smallAbelianSheafTorsorsEquivalence_inverse_comp B S hS H) (c.π.app k) δk
    have h := IsHomLift.fac' (abelianSheafTorsors B S hS H).val.p (c.π.app k) a
    change a.f = eqToHom _ ≫ c.π.app k ≫ eqToHom _ at h
    exact h.trans ((eqToHom_refl _ _ =≫ _).trans (Category.id_comp _))
  refine ⟨k, H.obj.map (eqToHom hT.symm).op r, ?_⟩
  change (H.obj.map (eqToHom hT.symm).op ≫ H.obj.map (c.π.app k).op) r = s
  rw [← H.obj.map_comp, ← op_comp, ← ha]
  exact hr

end

end Torsors

end

end

attribute [local instance] uliftCategory

/-- Over a nonempty base, given that the categories of torsors under group objects over sheaves
are stacks in groupoids over the big fppf site, there is a stack in groupoids whose structure
morphism to the big fppf site is limit preserving on objects while the stack itself is not
limit preserving. The hypothesis `h04UM` is Stacks 04UM, and it is discharged in
`StacksFrontier/Examples/Stacks/ObjectwiseLimitPreservingTorsors.lean`, which states 07Z1. -/
public theorem exists_stack_isLimitPreservingOnObjects_not_isLimitPreserving
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [Nonempty S]
    (h04UM : ∀ {ℬ : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (𝒢 : Grp (Over ℬ)),
      Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) ℬ →
      Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) 𝒢.X.left →
      Functor.IsStackInGroupoids.{u + 1}
        (ClassifyingTorsors.torsorsProjection 𝒢)
        (AlgebraicGeometry.BigFppfOver.topology B S hS)) :
    ∃ 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
        (AlgebraicGeometry.BigFppfOver B S hS),
      𝒳.val.p.IsStackInGroupoids.{u + 1}
          (AlgebraicGeometry.BigFppfOver.topology B S hS) ∧
        AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects.{u, v, w, u, u + 1} B S hS 𝒳
          (AlgebraicGeometry.Stack.terminalCFG B S hS)
          (Bicategory.InducedBicategory.mkHom
            (AlgebraicGeometry.Stack.toTerminalCFG B S hS 𝒳)) ∧
        ¬ Deformation.Artin.IsLimitPreserving.{u, v, w, u + 1, u} B S hS 𝒳 := by
  classical
  let : IsStackOfTorsors B S hS := ⟨h04UM⟩
  obtain ⟨H, hH, D, c, hc, s, hs⟩ :=
    exists_injective_sheaf_not_surjective_limit_sections B S hS
  let 𝒳 := smallAbelianSheafTorsors B S hS H
  refine ⟨𝒳, smallAbelianSheafTorsors_isStackInGroupoids B S hS H, ?_, ?_⟩
  · apply isLimitPreservingOnObjects_of_connected_fibers
    · exact smallAbelianSheafTorsors_fiber_nonempty B S hS H
    · let : Injective H := hH
      exact smallAbelianSheafTorsors_fiber_connected B S hS H
  · intro hlim
    let : Injective H := hH
    let e := (ULiftHomULiftCategory.equiv.{w, v} ℕᵒᵖ).symm
    let D' := e.functor ⋙ D
    let c' := c.whisker e.functor
    have hc' : IsLimit ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).mapCone c') :=
      hc.whiskerEquivalence e
    let := 𝒳.2.isFibered
    have := hlim _ D' c' hc'
    obtain ⟨k, a, ha⟩ := sheaf_sections_descend_of_full_comparison B S hS H
      (D' ⋙ AlgebraicGeometry.BigAffineFppf.inclusion B S hS)
      ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).mapCone c') inferInstance s
    exact hs ⟨e.functor.obj k, a, ha⟩

end AlgebraicGeometry.Stack.ObjectwiseLimitPreserving

end
