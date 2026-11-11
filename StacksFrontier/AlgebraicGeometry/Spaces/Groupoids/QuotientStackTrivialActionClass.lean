module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.MemberLocalStep
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientStackConstantData
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackTorsorEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfALocalizedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.DenseSubsiteTorsorClass
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology

/-!
# The first cohomology class of an object of a classifying stack

Let `S` be a scheme of a big fppf site and let `G` be a commutative group algebraic space over
`S`. An object `x` of the quotient stack `[S/G]` of the trivial action of `G` on `S` lying over
an object `U` of the site is, by Stacks 04WM, an fppf `G`-torsor over `U`, and its sections form
a torsor on the localized site `(Sch/U)_fppf` under the restriction of the abelian sheaf of
points of `G` (the relative form of Stacks 04TZ). Stacks 03AJ attaches to it a class in
`H¹(U, G) = H¹((Sch/U)_fppf, G|_U)`. This file constructs that class and proves that it is
compatible with pullback along morphisms of `[S/G]`, that it vanishes exactly when the torsor
has a section, and that it is read off on the big fppf site of the scheme of `U` as the class of
the torsor carried there along the equivalence of sites of Stacks 06WI.

## Main definitions

* `Stacks.Cohomology.Torsors.overMapH1Restrict`: the restriction map `Hⁿ(H) → Hⁿ(f^* H)` along a
  morphism `f : X ⟶ Y` of a site, between the `Ext`-groups out of the constant sheaf on the two
  localized sites.
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.pointsSheaf`: the abelian sheaf of points of a
  commutative group algebraic space over `S`, on the big fppf site of `S`.
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.actingGroupSectionEquiv`: the sheaf of groups
  acting on an fppf `G`-torsor over `U` is the restriction of that sheaf to `(Sch/U)_fppf`.
* `AlgebraicGeometry.Space.TorsorObj.abelianTorsor` and
  `AlgebraicGeometry.Space.TorsorObj.h1Class`: the torsor on `(Sch/U)_fppf` attached to an fppf
  `G`-torsor over `U`, and its class in `H¹(U, G)`.
* `AlgebraicGeometry.Space.quotientStackTrivialActionClass`: **the class in `H¹(U, G)` of an
  object of `[S/G]` over `U`**.
* `AlgebraicGeometry.Space.TorsorObj.objSchemeTorsor`: the torsor carried to the big fppf site of
  the scheme of `U`.

## Main results

* `Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_eq_overMapH1Restrict`: a torsor on the
  site localized at `X` which is identified, equivariantly, with the restriction of a torsor on
  the site localized at `Y` has the restricted class.
* `AlgebraicGeometry.Space.TorsorObj.h1Class_eq_overMapH1Restrict` and
  `AlgebraicGeometry.Space.quotientStackTrivialActionClass_map`: the class is compatible with
  pullback.
* `AlgebraicGeometry.Space.TorsorObj.h1Class_eq_zero_iff` and
  `AlgebraicGeometry.Space.quotientStackTrivialActionClass_eq_zero_iff`: the class vanishes
  exactly when the torsor has a section.
* `AlgebraicGeometry.Space.TorsorObj.hAddEquiv_h1Class`: the comparison of cohomology along the
  equivalence of sites `(Sch/W)_fppf ≌ (Sch/S)_fppf / U` (Stacks 00XU) carries the class to the
  class of the carried torsor.

## Implementation notes

The sections of `G` over an object `V` of the site are
`AlgebraicGeometry.Space.GroupAlgebraicSpace.Sections`, the sections of the underlying presheaf,
with the group law of the points `V ⟶ G` over `S`
transported to them: the points themselves form a type one universe too large for an abelian
sheaf of the site. Commutativity of `G` is the condition
`AlgebraicGeometry.Space.GroupAlgebraicSpace.IsCommutative` on its groups of points.

The restriction map along `f : X ⟶ Y` is built from the exact restriction functor
`J.overMapPullback f` and the comparison of constant sheaves, not from the cohomology presheaf
of the site: the comparison of `CategoryTheory.Sheaf.H'` over an object with the cohomology of
the localized site needs an extension by zero, which is not available for a site whose objects
lie one universe above its morphisms and its coefficients. Right exactness of the restriction
is `Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overMapPullback`, from local
bijectivity of the localized topologies; sheafification, `Ext`-groups and that local
bijectivity on the localized sites are instance arguments, as everywhere in the library for the
big fppf site.

## References

* [Stacks Project, Tag 04WM](https://stacks.math.columbia.edu/tag/04WM)
* [Stacks Project, Tag 04TZ](https://stacks.math.columbia.edu/tag/04TZ)
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w t v u

namespace Stacks.Cohomology.Torsors

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y)
  [HasSheafify (J.over X) AddCommGrpCat.{t}] [HasSheafify (J.over Y) AddCommGrpCat.{t}]
  [HasExt.{w} (Sheaf (J.over X) AddCommGrpCat.{t})]
  [HasExt.{w} (Sheaf (J.over Y) AddCommGrpCat.{t})]
  [PreservesFiniteColimits (J.overMapPullback AddCommGrpCat.{t} f)]

/-- The morphism from the constant sheaf `ℤ` on the site localized at `X` to the restriction
along `f : X ⟶ Y` of the constant sheaf `ℤ` on the site localized at `Y`: the sheafification
map of the constant presheaf on `Over Y`, restricted along `Over.map f`, and then transposed
along the sheafification adjunction on `Over X`. -/
def overMapConstantSheafHom :
    (presheafToSheaf (J.over X) AddCommGrpCat.{t}).obj
        ((Functor.const (Over X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ))) ⟶
      (J.overMapPullback AddCommGrpCat.{t} f).obj
        ((presheafToSheaf (J.over Y) AddCommGrpCat.{t}).obj
          ((Functor.const (Over Y)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)))) :=
  ((sheafificationAdjunction (J.over X) AddCommGrpCat.{t}).homEquiv _ _).symm
    (Functor.whiskerLeft (Over.map f).op (constantUnit (J := J.over Y)))

/-- **The restriction map on first cohomology along a morphism of localized sites.** For a
morphism `f : X ⟶ Y` of a site and an abelian sheaf `H` on the site localized at `Y`, the map
`Hⁿ(H) → Hⁿ(f^* H)` of `Ext`-groups out of the constant sheaf `ℤ`: apply the exact restriction
functor along `Over.map f`, then precompose with the comparison
`Stacks.Cohomology.Torsors.overMapConstantSheafHom` of the constant sheaves. For `H = F|_Y`
the target is `Hⁿ(F|_X)`, since `f^* (F|_Y)` is `F|_X` on the nose. -/
def overMapH1Restrict (H : Sheaf (J.over Y) AddCommGrpCat.{t}) (n : ℕ) :
    Sheaf.H.{w} H n →+ Sheaf.H.{w} ((J.overMapPullback AddCommGrpCat.{t} f).obj H) n :=
  ((Ext.mk₀ (overMapConstantSheafHom J f)).precomp _ (zero_add n)).comp
    ((J.overMapPullback AddCommGrpCat.{t} f).mapExtAddHom _ H n)

theorem overMapH1Restrict_apply (H : Sheaf (J.over Y) AddCommGrpCat.{t}) (n : ℕ)
    (e : Sheaf.H.{w} H n) :
    overMapH1Restrict J f H n e =
      (Ext.mk₀ (overMapConstantSheafHom J f)).comp
        (e.mapExactFunctor (J.overMapPullback AddCommGrpCat.{t} f)) (zero_add n) :=
  rfl

/-- **The class of a torsor identified with a restricted torsor is the restricted class.** Let
`P` be a torsor under an abelian sheaf `H` on the site localized at `Y`, let `F` be a torsor
under its restriction `f^* H` to the site localized at `X`, and let `α` identify the sections of
`F` over `W` bijectively and naturally with the sections of `P` over `f_* W`, equivariantly.
Then the class of `F` in `H¹(f^* H)` is the restriction of the class of `P` in `H¹(H)`. -/
theorem torsorIsoClassesEquivH1_eq_overMapH1Restrict (H : Sheaf (J.over Y) AddCommGrpCat.{t})
    (P : AbelianTorsor H) (F : AbelianTorsor ((J.overMapPullback AddCommGrpCat.{t} f).obj H))
    (α : F.1.presheaf ⟶ (Over.map f).op ⋙ P.1.presheaf)
    (hα : ∀ W, Function.Bijective (α.app W))
    (hact : ∀ (W : (Over X)ᵒᵖ) (h : H.obj.obj ((Over.map f).op.obj W))
      (s : F.1.presheaf.obj W),
      α.app W (F.1.act W (Multiplicative.ofAdd h) s) =
        P.1.act ((Over.map f).op.obj W) (Multiplicative.ofAdd h) (α.app W s)) :
    torsorIsoClassesEquivH1 _ (Quotient.mk (torsorSetoid _) F) =
      overMapH1Restrict J f H 1 (torsorIsoClassesEquivH1 H (Quotient.mk (torsorSetoid H) P)) := by
  let L := J.overMapPullback AddCommGrpCat.{t} f
  let S := torsorPushoutComplex H P
  have hS : S.ShortExact := torsorPushoutComplex_shortExact H P
  obtain ⟨i0, e0, inj0, fib0⟩ :=
    (torsorIsoClassesEquivH1_eq_boundary_iff S hS (constantUnit (J := J.over Y)) P).mp (by
      rw [constantUnit_adj_inverse, Abelian.Ext.mk₀_id_comp]
      rfl)
  let q' : (Functor.const (Over X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ (S.map L).X₃.obj :=
    Functor.whiskerLeft (Over.map f).op (constantUnit (J := J.over Y))
  have hR := (torsorIsoClassesEquivH1_eq_boundary_iff (S.map L) (hS.map_of_exact L) q' F).mpr
    ⟨α ≫ Functor.whiskerLeft (Over.map f).op i0,
      fun W h s => (congrArg (i0.app _) (hact W h s)).trans (e0 _ h (α.app W s)),
      fun W => (inj0 _).comp (hα W).1,
      fun W x => (fib0 _ x).trans
        ⟨fun ⟨p, hp⟩ => by
          obtain ⟨s, rfl⟩ := (hα W).2 p
          exact ⟨s, hp⟩,
        fun ⟨s, hs⟩ => ⟨α.app W s, hs⟩⟩⟩
  refine hR.trans ?_
  rw [overMapH1Restrict_apply]
  change _ = (Ext.mk₀ (overMapConstantSheafHom J f)).comp
    (hS.extClass.mapExactFunctor L) (zero_add 1)
  rw [Abelian.Ext.mapExactFunctor_extClass L hS]
  rfl

section Vanishing

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})]

/-- **The class of a torsor vanishes exactly when the torsor has a global section**: the
bijection of Stacks 03AJ sends the trivial torsor to `0`. -/
theorem torsorIsoClassesEquivH1_eq_zero_iff (H : Sheaf J AddCommGrpCat.{t})
    (F : AbelianTorsor H) :
    torsorIsoClassesEquivH1 H (Quotient.mk (torsorSetoid H) F) = 0 ↔
      Nonempty (GlobalSections F.1.presheaf) := by
  constructor
  · intro h
    exact (torsor_class_eq_trivial_iff H F).1
      ((torsorIsoClassesEquivH1 H).injective ((torsorIsoClassesEquivH1_trivial H).trans h.symm))
  · intro h
    rw [← (torsor_class_eq_trivial_iff H F).2 h]
    exact torsorIsoClassesEquivH1_trivial H

end Vanishing

end Stacks.Cohomology.Torsors

namespace AlgebraicGeometry.Space

open Stacks.Cohomology.Torsors
open scoped MonoidalCategory CategoryTheory.MonObj

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}

/-- The morphism of presheaves over `S` induced by a morphism of the big fppf site of `S`
between the representable presheaves. -/
def overBaseSYonedaMap {V W : BigFppfOver 𝒞 S hS} (g : W ⟶ V) :
    overBaseS (yoneda.obj W) ⟶ overBaseS (yoneda.obj V) :=
  Over.homMk (yoneda.map g) (baseS_ext _ _)

@[simp]
theorem overBaseSYonedaMap_left {V W : BigFppfOver 𝒞 S hS} (g : W ⟶ V) :
    (overBaseSYonedaMap g).left = yoneda.map g :=
  rfl

/-! ### The abelian sheaf of points of a commutative group algebraic space over `S` -/

namespace GroupAlgebraicSpace

variable (G : GroupAlgebraicSpace 𝒞 S hS (baseS 𝒞 S hS) (isAlgebraicSpace_baseS 𝒞 S hS))

/-- A group algebraic space over `S` is *commutative* when its group of points over every
object over `S` is commutative. -/
class IsCommutative : Prop where
  mul_comm : ∀ (Z : Over (baseS 𝒞 S hS)) (x y : Z ⟶ G.obj.X), x * y = y * x

/-- The sections of `G` over an object `V` of the big fppf site of `S`, with the group law of
the points `V ⟶ G` over `S`. -/
def Sections (V : BigFppfOver 𝒞 S hS) : Type u :=
  G.obj.X.left.obj (op V)

/-- A morphism `V ⟶ G` over `S` is a section of `G` over `V`. -/
def overBaseSHomEquiv (V : BigFppfOver 𝒞 S hS) :
    (overBaseS (yoneda.obj V) ⟶ G.obj.X) ≃ G.Sections V where
  toFun x := yonedaEquiv x.left
  invFun s := Over.homMk (yonedaEquiv.symm s) (baseS_ext _ _)
  left_inv x := Over.OverMorphism.ext (yonedaEquiv.symm_apply_apply x.left)
  right_inv s := yonedaEquiv.apply_symm_apply s

/-- Restricting a section of `G` along a morphism of the site is precomposing the morphism to
`G` it is. -/
theorem overBaseSHomEquiv_naturality {V W : BigFppfOver 𝒞 S hS} (g : W ⟶ V)
    (x : overBaseS (yoneda.obj V) ⟶ G.obj.X) :
    G.obj.X.left.map g.op (overBaseSHomEquiv G V x) =
      overBaseSHomEquiv G W (overBaseSYonedaMap g ≫ x) :=
  yonedaEquiv_naturality _ _

/-- The commutative group of points of a commutative group algebraic space over an object over
`S`. -/
abbrev homCommGroup [G.IsCommutative] (Z : Over (baseS 𝒞 S hS)) : CommGroup (Z ⟶ G.obj.X) :=
  { (inferInstance : Group (Z ⟶ G.obj.X)) with mul_comm := IsCommutative.mul_comm Z }

instance [G.IsCommutative] (V : BigFppfOver 𝒞 S hS) : CommGroup (G.Sections V) :=
  letI := homCommGroup G (overBaseS (yoneda.obj V))
  (overBaseSHomEquiv G V).symm.commGroup

/-- The group law on the sections of `G` is the group law of the points `V ⟶ G`. -/
theorem overBaseSHomEquiv_mul [G.IsCommutative] (V : BigFppfOver 𝒞 S hS)
    (a c : overBaseS (yoneda.obj V) ⟶ G.obj.X) :
    overBaseSHomEquiv G V (a * c) = overBaseSHomEquiv G V a * overBaseSHomEquiv G V c := by
  let := homCommGroup G (overBaseS (yoneda.obj V))
  refine Eq.trans ?_ (Equiv.mul_def (overBaseSHomEquiv G V).symm _ _).symm
  simp only [Equiv.symm_symm, Equiv.symm_apply_apply]

/-- The group of sections of `G` over `V` is the group of points `V ⟶ G` over `S`. -/
def sectionsMulEquiv [G.IsCommutative] (V : BigFppfOver 𝒞 S hS) :
    G.Sections V ≃* (overBaseS (yoneda.obj V) ⟶ G.obj.X) :=
  MulEquiv.symm
    { toEquiv := overBaseSHomEquiv G V
      map_mul' := overBaseSHomEquiv_mul G V }

theorem sectionsMulEquiv_symm_apply [G.IsCommutative] (V : BigFppfOver 𝒞 S hS)
    (x : overBaseS (yoneda.obj V) ⟶ G.obj.X) :
    (sectionsMulEquiv G V).symm x = overBaseSHomEquiv G V x :=
  rfl

@[simp]
theorem sectionsMulEquiv_overBaseSHomEquiv [G.IsCommutative] (V : BigFppfOver 𝒞 S hS)
    (x : overBaseS (yoneda.obj V) ⟶ G.obj.X) :
    sectionsMulEquiv G V (overBaseSHomEquiv G V x) = x :=
  (overBaseSHomEquiv G V).symm_apply_apply x

/-! ### The acting group of a torsor is the restricted sheaf of points -/

/-- The presentation over `S` of a test object of the localized site `(Sch/U)_fppf` is the
object over `S` given by the composite with a section `b` of `S` over `U`. -/
def overBaseSIso {U : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ baseS 𝒞 S hS) (W : Over U) :
    (Over.mk (yoneda.map W.hom ≫ b) : Over (baseS 𝒞 S hS)) ≅ overBaseS (yoneda.obj W.left) :=
  Over.isoMk (Iso.refl _) (baseS_ext _ _)

/-- **The points of `G_U = U ×_{b, S} G` over a test object `W` of `(Sch/U)_fppf` are the points
of `G` over `W`**, as groups. -/
def pointsSliceMulEquiv (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ baseS 𝒞 S hS)
    (W : Over U) :
    (overBaseS (yoneda.obj W.left) ⟶ G.obj.X) ≃*
      (sliceOver W ⟶ (pullbackGroup (isAlgebraicSpace_baseS 𝒞 S hS) G U b).obj.X) :=
  ((yonedaGrpObj G.obj.X).mapIso (overBaseSIso b W).op).groupIsoToMulEquiv.trans
    (baseChangePts G U b W).symm

theorem pointsSliceMulEquiv_left (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ baseS 𝒞 S hS)
    (W : Over U) (x : overBaseS (yoneda.obj W.left) ⟶ G.obj.X) :
    (pointsSliceMulEquiv G U b W x).left =
      pullback.lift x.left (yoneda.map W.hom) (baseS_ext _ _) :=
  rfl

theorem pbLeft_pointsSliceMulEquiv_fst (U : BigFppfOver 𝒞 S hS)
    (b : yoneda.obj U ⟶ baseS 𝒞 S hS) (W : Over U) (x : overBaseS (yoneda.obj W.left) ⟶ G.obj.X) :
    pbLeft G (pointsSliceMulEquiv G U b W x) ≫ pullback.fst G.obj.X.hom b = x.left :=
  pullback.lift_fst _ _ _

theorem pbLeft_pointsSliceMulEquiv_snd (U : BigFppfOver 𝒞 S hS)
    (b : yoneda.obj U ⟶ baseS 𝒞 S hS) (W : Over U) (x : overBaseS (yoneda.obj W.left) ⟶ G.obj.X) :
    pbLeft G (pointsSliceMulEquiv G U b W x) ≫ pullback.snd G.obj.X.hom b = yoneda.map W.hom :=
  pullback.lift_snd _ _ _

/-- A point of `G_U` over a test object of `(Sch/U)_fppf` is determined by its component in
`G`. -/
theorem pointsSlice_ext {U : BigFppfOver 𝒞 S hS} {b : yoneda.obj U ⟶ baseS 𝒞 S hS} {W : Over U}
    {k k' : sliceOver W ⟶ (pullbackGroup (isAlgebraicSpace_baseS 𝒞 S hS) G U b).obj.X}
    (h : pbLeft G k ≫ pullback.fst G.obj.X.hom b = pbLeft G k' ≫ pullback.fst G.obj.X.hom b) :
    k = k' :=
  (baseChangePts G U b W).injective (Over.OverMorphism.ext h)

/-- The product of two sections of the sheaf of groups of sections of a group object over the
representable presheaf of `U` is the section of the product of the morphisms they are. -/
theorem _root_.AlgebraicGeometry.Space.sliceSheafOfGroups_mul_sliceSectionEquiv
    {U : BigFppfOver 𝒞 S hS} (Gr : Over (yoneda.obj U)) [GrpObj Gr]
    (hGr : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) Gr.left) (W : (Over U)ᵒᵖ)
    (x y : sliceOver W.unop ⟶ Gr) :
    @HMul.hMul ((sliceSheafOfGroups Gr hGr).presheaf.obj W)
        ((sliceSheafOfGroups Gr hGr).presheaf.obj W) ((sliceSheafOfGroups Gr hGr).presheaf.obj W)
        _ (Space.sliceSectionEquiv Gr W.unop x) (Space.sliceSectionEquiv Gr W.unop y) =
      Space.sliceSectionEquiv Gr W.unop (x * y) :=
  (sliceSheafOfGroups_mul Gr hGr W _ _).trans (by
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply])

/-- The identification of the acting groups is compatible with base change along a morphism
`f : U ⟶ U'` over `S`: the point of `G_{U'}` attached to a point of `G` over `W` is the base
change of the point of `G_U` attached to it. -/
theorem pointsSliceMulEquiv_baseChange {U U' : BigFppfOver 𝒞 S hS}
    {b : yoneda.obj U ⟶ baseS 𝒞 S hS} {b' : yoneda.obj U' ⟶ baseS 𝒞 S hS} (f : U ⟶ U')
    (hf : yoneda.map f ≫ b' = b) (W : Over U) (x : overBaseS (yoneda.obj W.left) ⟶ G.obj.X) :
    pbLeft G (pointsSliceMulEquiv G U' b' ((Over.map f).obj W) x) =
      pbLeft G (pointsSliceMulEquiv G U b W x) ≫
        baseChangeGroupHom (isAlgebraicSpace_baseS 𝒞 S hS) G f hf := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, baseChangeGroupHom_fst, pbLeft_pointsSliceMulEquiv_fst,
      pbLeft_pointsSliceMulEquiv_fst]
  · rw [Category.assoc, baseChangeGroupHom_snd, ← Category.assoc,
      pbLeft_pointsSliceMulEquiv_snd, pbLeft_pointsSliceMulEquiv_snd]
    exact Functor.map_comp _ _ _

variable [G.IsCommutative]

/-- The restriction of sections of `G` along a morphism of the site, as a group homomorphism. -/
def sectionsMap {V W : BigFppfOver 𝒞 S hS} (g : W ⟶ V) : G.Sections V →* G.Sections W :=
  MonoidHom.mk' (G.obj.X.left.map g.op) (by
    intro x y
    obtain ⟨a, rfl⟩ := (overBaseSHomEquiv G V).surjective x
    obtain ⟨c, rfl⟩ := (overBaseSHomEquiv G V).surjective y
    rw [← overBaseSHomEquiv_mul, overBaseSHomEquiv_naturality, overBaseSHomEquiv_naturality,
      overBaseSHomEquiv_naturality, MonObj.comp_mul, overBaseSHomEquiv_mul])

theorem sectionsMap_apply {V W : BigFppfOver 𝒞 S hS} (g : W ⟶ V) (x : G.Sections V) :
    sectionsMap G g x = G.obj.X.left.map g.op x :=
  rfl

/-- The presheaf of sections of a commutative group algebraic space `G` over `S` on the big
fppf site of `S`, as abelian groups written additively. -/
def pointsPresheaf : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (Additive (G.Sections V.unop))
  map g := AddCommGrpCat.ofHom (sectionsMap G g.unop).toAdditive
  map_id V := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
    exact ConcreteCategory.congr_hom (G.obj.X.left.map_id _) (Additive.toMul x)
  map_comp f g := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
    exact ConcreteCategory.congr_hom (G.obj.X.left.map_comp f g) (Additive.toMul x)

/-- The underlying presheaf of sets of the sections of `G` is `G` itself. -/
def pointsPresheafForgetIso : pointsPresheaf G ⋙ forget AddCommGrpCat ≅ G.obj.X.left :=
  NatIso.ofComponents (fun V => Equiv.toIso (Additive.toMul (α := G.Sections V.unop)))
    (fun _ => rfl)

/-- The sections of `G` form an abelian sheaf on the big fppf site of `S`: the underlying
presheaf of sets is `G`, which is a sheaf since it is an algebraic space. -/
theorem pointsPresheaf_isSheaf :
    Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) (pointsPresheaf G) :=
  Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{u})
    ((Presheaf.isSheaf_of_iso_iff (pointsPresheafForgetIso G)).mpr G.property.isSheaf)

/-- **The abelian sheaf of points of a commutative group algebraic space over `S`** on the big
fppf site of `S`. -/
def pointsSheaf : Sheaf (BigFppfOver.topology 𝒞 S hS) AddCommGrpCat.{u} :=
  ⟨pointsPresheaf G, pointsPresheaf_isSheaf G⟩

/-- The sections of the restriction of the abelian sheaf of points of `G` to `(Sch/U)_fppf`,
read multiplicatively, are the sections of `G`, with their group law. -/
def pointsOverMulEquiv (U : BigFppfOver 𝒞 S hS) (W : (Over U)ᵒᵖ) :
    (abelianSheafAsGroupSheaf ((pointsSheaf G).over U)).presheaf.obj W ≃* G.Sections W.unop.left
    where
  toEquiv := Equiv.refl _
  map_mul' _ _ := rfl

/-- **The sheaf of groups acting on a torsor over `U` is the restriction of the abelian sheaf of
points of `G` to `(Sch/U)_fppf`**, read multiplicatively. -/
def actingGroupSectionEquiv (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ baseS 𝒞 S hS) :
    SheafOfGroups.SectionEquiv (abelianSheafAsGroupSheaf ((pointsSheaf G).over U))
      (baseGroupSheaf (isAlgebraicSpace_baseS 𝒞 S hS) G U b) where
  equiv W := ((pointsOverMulEquiv G U W).trans ((sectionsMulEquiv G W.unop.left).trans
    (pointsSliceMulEquiv G U b W.unop))).toEquiv.trans (Space.sliceSectionEquiv _ W.unop)
  map_mul W g h := by
    let m := (pointsOverMulEquiv G U W).trans ((sectionsMulEquiv G W.unop.left).trans
      (pointsSliceMulEquiv G U b W.unop))
    change Space.sliceSectionEquiv _ W.unop (m (g * h)) =
      @HMul.hMul ((baseGroupSheaf (isAlgebraicSpace_baseS 𝒞 S hS) G U b).presheaf.obj W)
        ((baseGroupSheaf (isAlgebraicSpace_baseS 𝒞 S hS) G U b).presheaf.obj W)
        ((baseGroupSheaf (isAlgebraicSpace_baseS 𝒞 S hS) G U b).presheaf.obj W) _
        (Space.sliceSectionEquiv _ W.unop (m g)) (Space.sliceSectionEquiv _ W.unop (m h))
    rw [sliceSheafOfGroups_mul_sliceSectionEquiv, map_mul]
  naturality {V W} f g := by
    obtain ⟨a, rfl⟩ := (overBaseSHomEquiv G V.unop.left).surjective g
    change Space.sliceSectionEquiv _ W.unop (pointsSliceMulEquiv G U b W.unop
      (sectionsMulEquiv G W.unop.left (G.obj.X.left.map f.unop.left.op
        (overBaseSHomEquiv G V.unop.left a)))) =
      (sliceSection _).map f (Space.sliceSectionEquiv _ V.unop (pointsSliceMulEquiv G U b V.unop
        (sectionsMulEquiv G V.unop.left (overBaseSHomEquiv G V.unop.left a))))
    rw [overBaseSHomEquiv_naturality, sliceSectionEquiv_map, sectionsMulEquiv_overBaseSHomEquiv,
      sectionsMulEquiv_overBaseSHomEquiv]
    congr 1
    refine pointsSlice_ext G ?_
    change pbLeft G (pointsSliceMulEquiv G U b W.unop (overBaseSYonedaMap f.unop.left ≫ a)) ≫
        pullback.fst G.obj.X.hom b =
      yoneda.map f.unop.left ≫ pbLeft G (pointsSliceMulEquiv G U b V.unop a) ≫
        pullback.fst G.obj.X.hom b
    rw [pbLeft_pointsSliceMulEquiv_fst, pbLeft_pointsSliceMulEquiv_fst]
    rfl

end GroupAlgebraicSpace

/-! ### The first cohomology class of an fppf `G`-torsor -/

namespace TorsorObj

variable {G : GroupAlgebraicSpace 𝒞 S hS (baseS 𝒞 S hS) (isAlgebraicSpace_baseS 𝒞 S hS)}
  [G.IsCommutative]

/-- **The torsor on `(Sch/U)_fppf` attached to an fppf `G`-torsor over `U`**: the sections of
its total space, a torsor under the sections of `G_U`
(`AlgebraicGeometry.Space.slicePseudoTorsor`, the relative form of Stacks 04TZ), read as a
torsor under the restriction to `(Sch/U)_fppf` of the abelian sheaf of points of `G`. -/
def abelianTorsor (T : TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G) :
    AbelianTorsor ((GroupAlgebraicSpace.pointsSheaf G).over T.U) :=
  ⟨(slicePseudoTorsor T.group T.total
      (pullbackGroup (isAlgebraicSpace_baseS 𝒞 S hS) G T.U T.b).property.isSheaf
      T.isAlgebraicSpace.isSheaf T.isFppfTorsor.1).transport
      (GroupAlgebraicSpace.actingGroupSectionEquiv G T.U T.b),
    by
      refine PseudoTorsor.transport_isTorsor _ _ ?_
      obtain ⟨I, Bi, f, -, hcov, hsec⟩ := T.isFppfTorsor.2
      exact isTorsor_slicePseudoTorsor 𝒞 S hS T.group T.total _ _ T.isFppfTorsor.1 Bi f hcov
        hsec⟩

/-- The sections of the torsor attached to an fppf `G`-torsor are the sections of its total
space lying over the tautological section. -/
theorem abelianTorsor_presheaf (T : TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G) :
    T.abelianTorsor.1.presheaf = sliceSection T.total :=
  rfl

/-- A morphism of fppf `G`-torsors identifies the sections of the source over a test object `W`
of `(Sch/U)_fppf` with the sections of the target over `f_* W`. -/
def Hom.sliceSectionsMap {T T' : TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G} (m : T ⟶ T') :
    T.abelianTorsor.1.presheaf ⟶ (Over.map m.f).op ⋙ T'.abelianTorsor.1.presheaf where
  app W := ↾fun s => ⟨m.g.app (op W.unop.left) s.1,
    (ConcreteCategory.congr_hom (NatTrans.congr_app m.isPullback.w _) s.1).trans
      (congrArg (· ≫ m.f) s.2)⟩
  naturality {W W'} k := by
    ext s
    refine Subtype.ext ?_
    change m.g.app (op W'.unop.left) (T.total.left.map k.unop.left.op s.1) =
      T'.total.left.map k.unop.left.op (m.g.app (op W.unop.left) s.1)
    exact NatTrans.naturality_apply m.g k.unop.left.op s.1

theorem Hom.sliceSectionsMap_app_val {T T' : TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G}
    (m : T ⟶ T') (W : (Over T.U)ᵒᵖ) (s : T.abelianTorsor.1.presheaf.obj W) :
    ((Hom.sliceSectionsMap m).app W s).1 = m.g.app (op W.unop.left) s.1 :=
  rfl

/-- The identification of sections along a morphism of fppf `G`-torsors is bijective: the total
space of the source is the pullback of that of the target. -/
theorem Hom.sliceSectionsMap_bijective {T T' : TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G}
    (m : T ⟶ T') (W : (Over T.U)ᵒᵖ) : Function.Bijective ((Hom.sliceSectionsMap m).app W) := by
  have hpb := m.isPullback.map
    ((evaluation (BigFppfOver 𝒞 S hS)ᵒᵖ (Type u)).obj (op W.unop.left))
  refine ⟨fun s s' h => Subtype.ext (Types.ext_of_isPullback hpb (congrArg Subtype.val h)
    (s.2.trans s'.2.symm)), fun y => ?_⟩
  obtain ⟨s, hs1, hs2⟩ := Types.exists_of_isPullback hpb y.1 W.unop.hom y.2
  exact ⟨⟨s, hs2⟩, Subtype.ext hs1⟩

/-- The identification of the acting groups commutes with base change along a morphism of fppf
`G`-torsors. -/
theorem Hom.actingGroupSectionEquiv_baseChange
    {T T' : TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G} (m : T ⟶ T') (W : (Over T.U)ᵒᵖ)
    (h : ((GroupAlgebraicSpace.pointsSheaf G).over T'.U).obj.obj ((Over.map m.f).op.obj W)) :
    ((GroupAlgebraicSpace.actingGroupSectionEquiv G T'.U T'.b).equiv ((Over.map m.f).op.obj W)
        (Multiplicative.ofAdd h)).1 =
      (groupBaseChange m.f m.comp_b).app (op W.unop.left)
        ((GroupAlgebraicSpace.actingGroupSectionEquiv G T.U T.b).equiv W
          (Multiplicative.ofAdd h)).1 := by
  let x := GroupAlgebraicSpace.sectionsMulEquiv G W.unop.left
    (GroupAlgebraicSpace.pointsOverMulEquiv G T.U W (Multiplicative.ofAdd h))
  change yonedaEquiv (pbLeft G (GroupAlgebraicSpace.pointsSliceMulEquiv G T'.U T'.b
      ((Over.map m.f).obj W.unop) x)) =
    (baseChangeGroupHom (isAlgebraicSpace_baseS 𝒞 S hS) G m.f m.comp_b).app (op W.unop.left)
      (yonedaEquiv (pbLeft G (GroupAlgebraicSpace.pointsSliceMulEquiv G T.U T.b W.unop x)))
  rw [GroupAlgebraicSpace.pointsSliceMulEquiv_baseChange G m.f m.comp_b, yonedaEquiv_comp]
  rfl

/-- The identification of sections along a morphism of fppf `G`-torsors is equivariant. -/
theorem Hom.sliceSectionsMap_act {T T' : TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G}
    (m : T ⟶ T') (W : (Over T.U)ᵒᵖ)
    (h : ((GroupAlgebraicSpace.pointsSheaf G).over T'.U).obj.obj ((Over.map m.f).op.obj W))
    (s : T.abelianTorsor.1.presheaf.obj W) :
    (Hom.sliceSectionsMap m).app W (T.abelianTorsor.1.act W (Multiplicative.ofAdd h) s) =
      T'.abelianTorsor.1.act ((Over.map m.f).op.obj W) (Multiplicative.ofAdd h)
        ((Hom.sliceSectionsMap m).app W s) := by
  refine Subtype.ext ?_
  refine (Hom.map_smulSection m _ _
    ((((GroupAlgebraicSpace.actingGroupSectionEquiv G T.U T.b).equiv W
      (Multiplicative.ofAdd h)).2).trans s.2.symm)).trans ?_
  exact smulSection_congr (h' := (((GroupAlgebraicSpace.actingGroupSectionEquiv G T'.U T'.b).equiv
      ((Over.map m.f).op.obj W) (Multiplicative.ofAdd h)).2).trans
        ((Hom.sliceSectionsMap m).app W s).2.symm) _ _
    (Hom.actingGroupSectionEquiv_baseChange m W h).symm rfl

variable [∀ U : BigFppfOver 𝒞 S hS,
    HasSheafify ((BigFppfOver.topology 𝒞 S hS).over U) AddCommGrpCat.{u}]
  [∀ U : BigFppfOver 𝒞 S hS,
    HasExt.{w} (Sheaf ((BigFppfOver.topology 𝒞 S hS).over U) AddCommGrpCat.{u})]

/-- **The first cohomology class of an fppf `G`-torsor over `U`**: the class in
`H¹(U, G) = H¹((Sch/U)_fppf, G|_U)` of its torsor of sections (Stacks 03AJ). -/
def h1Class (T : TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G) :
    Sheaf.H.{w} ((GroupAlgebraicSpace.pointsSheaf G).over T.U) 1 :=
  torsorIsoClassesEquivH1 _ (Quotient.mk (torsorSetoid _) T.abelianTorsor)

/-- **The class of an fppf `G`-torsor over `U` vanishes exactly when the torsor is trivial**,
that is, when its total space has a section over `U`. -/
theorem h1Class_eq_zero_iff (T : TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G) :
    T.h1Class = 0 ↔ ∃ s : T.total.left.obj (op T.U), T.total.hom.app (op T.U) s = 𝟙 T.U := by
  rw [h1Class, torsorIsoClassesEquivH1_eq_zero_iff, nonempty_globalSections_iff_sectionFamily]
  constructor
  · rintro ⟨s, -⟩
    exact ⟨(s (op (Over.mk (𝟙 T.U)))).1, (s (op (Over.mk (𝟙 T.U)))).2⟩
  · rintro ⟨x, hx⟩
    let x' : T.abelianTorsor.1.presheaf.obj (op (Over.mk (𝟙 T.U))) := ⟨x, hx⟩
    refine ⟨fun W => T.abelianTorsor.1.presheaf.map (Over.mkIdTerminal.from W.unop).op x', ?_⟩
    intro W W' k
    change T.abelianTorsor.1.presheaf.map k
        (T.abelianTorsor.1.presheaf.map (Over.mkIdTerminal.from W.unop).op x') =
      T.abelianTorsor.1.presheaf.map (Over.mkIdTerminal.from W'.unop).op x'
    rw [← Functor.map_comp_apply]
    exact congrArg (fun g => T.abelianTorsor.1.presheaf.map g x')
      (Quiver.Hom.unop_inj (Over.mkIdTerminal.hom_ext _ _))

attribute [local instance] Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overMapPullback

variable [∀ U : BigFppfOver 𝒞 S hS,
  ((BigFppfOver.topology 𝒞 S hS).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The first cohomology class of an fppf `G`-torsor is compatible with pullback**: for a
morphism `m : T ⟶ T'` of fppf `G`-torsors over `f : U ⟶ U'`, the class of `T` is the
restriction along `f` of the class of `T'`. -/
theorem h1Class_eq_overMapH1Restrict {T T' : TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G}
    (m : T ⟶ T') :
    T.h1Class = overMapH1Restrict (BigFppfOver.topology 𝒞 S hS) m.f
      ((GroupAlgebraicSpace.pointsSheaf G).over T'.U) 1 T'.h1Class :=
  torsorIsoClassesEquivH1_eq_overMapH1Restrict _ m.f _ T'.abelianTorsor T.abelianTorsor
    (Hom.sliceSectionsMap m) (Hom.sliceSectionsMap_bijective m) (Hom.sliceSectionsMap_act m)

end TorsorObj

/-! ### The first cohomology class of an object of a category of torsors, and of `[S/G]` -/

section Stack

variable {G : GroupAlgebraicSpace 𝒞 S hS (baseS 𝒞 S hS) (isAlgebraicSpace_baseS 𝒞 S hS)}
  [G.IsCommutative]
  [∀ U : BigFppfOver 𝒞 S hS,
    HasSheafify ((BigFppfOver.topology 𝒞 S hS).over U) AddCommGrpCat.{u}]
  [∀ U : BigFppfOver 𝒞 S hS,
    HasExt.{w} (Sheaf ((BigFppfOver.topology 𝒞 S hS).over U) AddCommGrpCat.{u})]

variable {𝒳 : Type*} [Category* 𝒳] (p : 𝒳 ⥤ BigFppfOver 𝒞 S hS)
  (Φ : 𝒳 ⥤ TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G)
  (hΦ : Φ ⋙ torsorProjection (isAlgebraicSpace_baseS 𝒞 S hS) G = p)

/-- The first cohomology class of an object `x` of a category over the big fppf site of `S`
which a functor `Φ` over the site sends to fppf `G`-torsors: the class of the torsor `Φ x`, in
`H¹(p x, G)`. -/
def torsorH1Class (x : 𝒳) :
    Sheaf.H.{w} ((GroupAlgebraicSpace.pointsSheaf G).over (p.obj x)) 1 :=
  cast (congrArg (fun U => Sheaf.H.{w} ((GroupAlgebraicSpace.pointsSheaf G).over U) 1)
    (Functor.congr_obj hΦ x)) (Φ.obj x).h1Class

/-- The class of an object vanishes exactly when the class of its torsor does. -/
theorem torsorH1Class_eq_zero_iff (x : 𝒳) :
    torsorH1Class p Φ hΦ x = 0 ↔ (Φ.obj x).h1Class = 0 := by
  subst hΦ
  rfl

attribute [local instance] Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overMapPullback

variable [∀ U : BigFppfOver 𝒞 S hS,
  ((BigFppfOver.topology 𝒞 S hS).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The first cohomology class is compatible with pullback**: for a morphism `φ : x ⟶ y` of
the category over the site, the class of `x` is the restriction along `p φ` of the class of
`y`. -/
theorem torsorH1Class_map {x y : 𝒳} (φ : x ⟶ y) :
    torsorH1Class p Φ hΦ x = overMapH1Restrict (BigFppfOver.topology 𝒞 S hS) (p.map φ)
      ((GroupAlgebraicSpace.pointsSheaf G).over (p.obj y)) 1 (torsorH1Class p Φ hΦ y) := by
  subst hΦ
  exact TorsorObj.h1Class_eq_overMapH1Restrict (Φ.map φ)

end Stack

section QuotientStack

variable (G : GroupAlgebraicSpace 𝒞 S hS (baseS 𝒞 S hS) (isAlgebraicSpace_baseS 𝒞 S hS))

/-- The functor from `[S/G]`, the quotient stack of the trivial action of `G` on `S`, to the
category of fppf `G`-torsors: Stacks 04WM (`AlgebraicGeometry.Space.quotientStackTorsorEquivalence`)
at `X = S`, followed by forgetting the equivariant map to `S`. -/
def quotientStackToTorsors :
    (Stack.quotientStackOfAction ⟨baseS 𝒞 S hS, isAlgebraicSpace_baseS 𝒞 S hS⟩ G.obj.X
        (𝟙_ (Over (baseS 𝒞 S hS))) G.property (isAlgebraicSpace_baseS 𝒞 S hS)).obj ⥤
      TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G :=
  (quotientStackTorsorEquivalence (isAlgebraicSpace_baseS 𝒞 S hS) G
      (𝟙_ (Over (baseS 𝒞 S hS))) (isAlgebraicSpace_baseS 𝒞 S hS)).1.hom.functor ⋙
    TorsorWithMap.forget (isAlgebraicSpace_baseS 𝒞 S hS) G (𝟙_ (Over (baseS 𝒞 S hS)))

/-- The functor from `[S/G]` to fppf `G`-torsors lies over the big fppf site. -/
theorem quotientStackToTorsors_comp_torsorProjection :
    quotientStackToTorsors G ⋙ torsorProjection (isAlgebraicSpace_baseS 𝒞 S hS) G =
      (Stack.quotientStackOfAction ⟨baseS 𝒞 S hS, isAlgebraicSpace_baseS 𝒞 S hS⟩ G.obj.X
        (𝟙_ (Over (baseS 𝒞 S hS))) G.property (isAlgebraicSpace_baseS 𝒞 S hS)).p :=
  (quotientStackTorsorEquivalence (isAlgebraicSpace_baseS 𝒞 S hS) G
    (𝟙_ (Over (baseS 𝒞 S hS))) (isAlgebraicSpace_baseS 𝒞 S hS)).1.hom.w

variable [G.IsCommutative]
  [∀ U : BigFppfOver 𝒞 S hS,
    HasSheafify ((BigFppfOver.topology 𝒞 S hS).over U) AddCommGrpCat.{u}]
  [∀ U : BigFppfOver 𝒞 S hS,
    HasExt.{w} (Sheaf ((BigFppfOver.topology 𝒞 S hS).over U) AddCommGrpCat.{u})]

/-- **The first cohomology class of an object of `[S/G]`.** For a commutative group algebraic
space `G` over `S` and an object `x` of the quotient stack `[S/G]` of the trivial action of `G`
on `S` (Stacks 044Q) lying over `U`, the class in `H¹(U, G) = H¹((Sch/U)_fppf, G|_U)` of the
fppf `G`-torsor that `x` corresponds to under Stacks 04WM. -/
def quotientStackTrivialActionClass
    (x : (Stack.quotientStackOfAction ⟨baseS 𝒞 S hS, isAlgebraicSpace_baseS 𝒞 S hS⟩ G.obj.X
      (𝟙_ (Over (baseS 𝒞 S hS))) G.property (isAlgebraicSpace_baseS 𝒞 S hS)).obj) :
    Sheaf.H.{w} ((GroupAlgebraicSpace.pointsSheaf G).over
      ((Stack.quotientStackOfAction ⟨baseS 𝒞 S hS, isAlgebraicSpace_baseS 𝒞 S hS⟩ G.obj.X
        (𝟙_ (Over (baseS 𝒞 S hS))) G.property (isAlgebraicSpace_baseS 𝒞 S hS)).p.obj x)) 1 :=
  torsorH1Class _ (quotientStackToTorsors G) (quotientStackToTorsors_comp_torsorProjection G) x

/-- **The class of an object of `[S/G]` vanishes exactly when its torsor is trivial**, that is,
when the total space of the fppf `G`-torsor it corresponds to has a section over its base. -/
theorem quotientStackTrivialActionClass_eq_zero_iff
    (x : (Stack.quotientStackOfAction ⟨baseS 𝒞 S hS, isAlgebraicSpace_baseS 𝒞 S hS⟩ G.obj.X
      (𝟙_ (Over (baseS 𝒞 S hS))) G.property (isAlgebraicSpace_baseS 𝒞 S hS)).obj) :
    quotientStackTrivialActionClass G x = 0 ↔
      ∃ s : ((quotientStackToTorsors G).obj x).total.left.obj
          (op ((quotientStackToTorsors G).obj x).U),
        ((quotientStackToTorsors G).obj x).total.hom.app _ s = 𝟙 _ :=
  (torsorH1Class_eq_zero_iff _ _ _ x).trans (TorsorObj.h1Class_eq_zero_iff _)

attribute [local instance] Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overMapPullback

variable [∀ U : BigFppfOver 𝒞 S hS,
  ((BigFppfOver.topology 𝒞 S hS).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The first cohomology class of an object of `[S/G]` is compatible with pullback**: for a
morphism `φ : x ⟶ y` of `[S/G]`, the class of `x` is the restriction of the class of `y` along
the morphism `p φ` of the big fppf site under it. -/
theorem quotientStackTrivialActionClass_map
    {x y : (Stack.quotientStackOfAction ⟨baseS 𝒞 S hS, isAlgebraicSpace_baseS 𝒞 S hS⟩ G.obj.X
      (𝟙_ (Over (baseS 𝒞 S hS))) G.property (isAlgebraicSpace_baseS 𝒞 S hS)).obj}
    (φ : x ⟶ y) :
    quotientStackTrivialActionClass G x =
      overMapH1Restrict (BigFppfOver.topology 𝒞 S hS)
        ((Stack.quotientStackOfAction ⟨baseS 𝒞 S hS, isAlgebraicSpace_baseS 𝒞 S hS⟩ G.obj.X
          (𝟙_ (Over (baseS 𝒞 S hS))) G.property (isAlgebraicSpace_baseS 𝒞 S hS)).p.map φ)
        ((GroupAlgebraicSpace.pointsSheaf G).over
          ((Stack.quotientStackOfAction ⟨baseS 𝒞 S hS, isAlgebraicSpace_baseS 𝒞 S hS⟩ G.obj.X
            (𝟙_ (Over (baseS 𝒞 S hS))) G.property (isAlgebraicSpace_baseS 𝒞 S hS)).p.obj y))
        1 (quotientStackTrivialActionClass G y) :=
  torsorH1Class_map _ _ _ φ

end QuotientStack

/-! ### Carrying the torsor to the big fppf site of the scheme of `U` -/

section ObjScheme


variable {G : GroupAlgebraicSpace 𝒞 S hS (baseS 𝒞 S hS) (isAlgebraicSpace_baseS 𝒞 S hS)}
  [G.IsCommutative]

/-- The restriction of the abelian sheaf of points of `G` from `(Sch/S)_fppf` to the big fppf
site of the scheme `W` of an object `U` of the site, through the localization at `U` and the
equivalence `AlgebraicGeometry.BigFppfOver.objEquiv` of Stacks 06WI. -/
abbrev pointsSheafOnObjScheme (G : GroupAlgebraicSpace 𝒞 S hS (baseS 𝒞 S hS)
    (isAlgebraicSpace_baseS 𝒞 S hS)) [G.IsCommutative] (U : BigFppfOver 𝒞 S hS) :
    Sheaf (BigFppfOver.topology 𝒞 (BigFppfOver.objScheme 𝒞 S hS U)
      (BigFppfOver.contains_objScheme 𝒞 S hS U)) AddCommGrpCat.{u} :=
  ((BigFppfOver.objEquiv 𝒞 S hS U).functor.sheafPushforwardContinuous AddCommGrpCat.{u}
    (BigFppfOver.topology 𝒞 (BigFppfOver.objScheme 𝒞 S hS U)
      (BigFppfOver.contains_objScheme 𝒞 S hS U))
    ((BigFppfOver.topology 𝒞 S hS).over U)).obj ((GroupAlgebraicSpace.pointsSheaf G).over U)

/-- Restriction of sheaves along the equivalence of sites of Stacks 06WI between the big fppf
site of the scheme of `U` and the localization at `U` is an equivalence of categories: it is the
inverse of `CategoryTheory.Equivalence.sheafCongr`. -/
instance isEquivalence_objEquiv_sheafPushforwardContinuous (U : BigFppfOver 𝒞 S hS) :
    ((BigFppfOver.objEquiv 𝒞 S hS U).functor.sheafPushforwardContinuous AddCommGrpCat.{u}
      (BigFppfOver.topology 𝒞 (BigFppfOver.objScheme 𝒞 S hS U)
        (BigFppfOver.contains_objScheme 𝒞 S hS U))
      ((BigFppfOver.topology 𝒞 S hS).over U)).IsEquivalence :=
  inferInstanceAs ((BigFppfOver.objEquiv 𝒞 S hS U).sheafCongr
    (BigFppfOver.topology 𝒞 (BigFppfOver.objScheme 𝒞 S hS U)
      (BigFppfOver.contains_objScheme 𝒞 S hS U))
    ((BigFppfOver.topology 𝒞 S hS).over U) AddCommGrpCat.{u}).inverse.IsEquivalence

/-- **The torsor of an fppf `G`-torsor over `U`, on the big fppf site of the scheme `W` of
`U`**: the torsor of sections `AlgebraicGeometry.Space.TorsorObj.abelianTorsor` on
`(Sch/U)_fppf`, restricted along the equivalence of sites
`AlgebraicGeometry.BigFppfOver.objEquiv` between `(Sch/W)_fppf` and `(Sch/S)_fppf / U`. -/
def TorsorObj.objSchemeTorsor (T : TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G) :
    AbelianTorsor (pointsSheafOnObjScheme G T.U) :=
  T.abelianTorsor.restrict _ _ (BigFppfOver.objEquiv 𝒞 S hS T.U).functor

variable [∀ U : BigFppfOver 𝒞 S hS,
    HasSheafify ((BigFppfOver.topology 𝒞 S hS).over U) AddCommGrpCat.{u}]
  [∀ U : BigFppfOver 𝒞 S hS,
    HasExt.{w} (Sheaf ((BigFppfOver.topology 𝒞 S hS).over U) AddCommGrpCat.{u})]

/-- **The class of an fppf `G`-torsor over `U`, read on the big fppf site of the scheme of
`U`.** The comparison `H¹((Sch/S)_fppf / U, G|_U) ≅ H¹((Sch/W)_fppf, G|_W)` of cohomology along
the equivalence of sites (`Stacks.Cohomology.DenseSubsite.hAddEquiv`, Stacks 00XU) carries the
class of the torsor to the class of the torsor carried to `(Sch/W)_fppf`. -/
theorem TorsorObj.hAddEquiv_h1Class (T : TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G)
    [HasSheafify (BigFppfOver.topology 𝒞 (BigFppfOver.objScheme 𝒞 S hS T.U)
      (BigFppfOver.contains_objScheme 𝒞 S hS T.U)) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (BigFppfOver.topology 𝒞 (BigFppfOver.objScheme 𝒞 S hS T.U)
      (BigFppfOver.contains_objScheme 𝒞 S hS T.U)) AddCommGrpCat.{u})]
    [EnoughInjectives (Sheaf (BigFppfOver.topology 𝒞 (BigFppfOver.objScheme 𝒞 S hS T.U)
      (BigFppfOver.contains_objScheme 𝒞 S hS T.U)) AddCommGrpCat.{u})] :
    Stacks.Cohomology.DenseSubsite.hAddEquiv _ _ (BigFppfOver.objEquiv 𝒞 S hS T.U).functor
        ((GroupAlgebraicSpace.pointsSheaf G).over T.U) 1 T.h1Class =
      torsorIsoClassesEquivH1 _ (Quotient.mk (torsorSetoid _) T.objSchemeTorsor) :=
  Stacks.Cohomology.DenseSubsite.hAddEquiv_torsorIsoClassesEquivH1 _ _ _ _ _

end ObjScheme

end AlgebraicGeometry.Space

end
