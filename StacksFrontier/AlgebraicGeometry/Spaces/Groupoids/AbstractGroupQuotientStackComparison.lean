module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientStackIsStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.RelativeSiteTorsor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.UniverseBridge

/-!
# The comparison functor from the quotient of Situation 04WL to the quotient by an abstract group

Let `S` be a scheme of a big fppf site, let `ℬ` be an algebraic space over `S`, let `𝒢` be a
group algebraic space over `ℬ` and let `X` be an algebraic space over `ℬ` on which `𝒢` acts.
Situation 04WL has the category `[[X/𝒢]]` of `AlgebraicGeometry.Space.TorsorWithMap`, whose
objects are quadruples `(U, b, P, φ)`. For an abstract group `Gabs`, Stacks 0371 has the
category `[[X/Gabs]]` of `AlgebraicGeometry.AbstractGroupQuotientStack`, whose objects are
triples `(U, P, φ)` with `P` a torsor under the *constant sheaf of groups* with value `Gabs`.
This file constructs the comparison functor `[[X/𝒢]] ⥤ [[X/Gabs]]` of the last clause of
Stacks 0371.

The functor exists in that direction only: the total space of the torsor of a quadruple is
required to be an algebraic space, while the torsor of a triple is an arbitrary sheaf.

## The two obstacles, and what this file does about them

**The acting groups.** A quadruple carries a torsor under `G_U = U ×_{b, ℬ} 𝒢`, an object of
the slice over the representable presheaf of `U` with an action of a group object; a triple
carries a torsor under the constant sheaf of groups on the localized site `(Sch/U)_fppf`. The
first is turned into the second by `AlgebraicGeometry.Space.slicePseudoTorsor`, whose acting
sheaf of groups is `AlgebraicGeometry.Space.sliceSheafOfGroups`, the sections of `G_U`. That
this sheaf of groups *is* the constant one is the content of the clause, and it is taken here
as the datum `AlgebraicGeometry.Space.ConstantGroupData`: an identification of the two,
compatible with base change along a morphism of the site over `ℬ`. Producing that datum for
the constant group algebraic space `G_S` is a construction this file does not carry out; see
the closing section.

**The universes.** The sections of the torsor of a quadruple lie in `Type u`, the universe of
the schemes, whereas a triple carries a torsor whose sections lie in an independent universe,
and the value universe of the sheaf `X` differs on the two sides in the same way. The bridge is
`PseudoTorsor.bridge` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.UniverseBridge`, which lifts the sections
along `CategoryTheory.uliftFunctor` and transports the acting sheaf of groups along an
identification of sections whose two sides may live in different universes. Accordingly the
comparison functor lands in the triples with sections in `Type (max u t)` for an arbitrary `t`
and with target presheaf `X.left ⋙ uliftFunctor.{t}`; taking `t := max t' (u + 1)` gives the
rendering in which `AlgebraicGeometry.AbstractGroupQuotientStack.projection_isStackInGroupoids`
is stated. No universe is specialized and nothing is identified by fiat.

## Main definitions

* `AlgebraicGeometry.Space.smulSection`: the action of a section of a group object over a
  presheaf on a section of an object it acts on, both lying over the same section of the base.
  This is the sectionwise reading of the action morphism, and the form in which the
  equivariance of a morphism of torsors and of the map `φ` are used.
* `AlgebraicGeometry.Space.baseGroupSheaf`: the sheaf of groups of sections of
  `G_U = U ×_{b, ℬ} 𝒢` on the localized site `(Sch/U)_fppf`.
* `AlgebraicGeometry.Space.ConstantGroupData`: the identification of `G_U` with the constant
  sheaf of groups with value `Gabs`, compatible with base change; the datum that makes `𝒢` the
  constant group algebraic space as far as the comparison is concerned.
* `AlgebraicGeometry.Space.TorsorObj.toConstantTorsor` and
  `AlgebraicGeometry.Space.torsorObjToConstantTorsors`: an fppf `G`-torsor read as a torsor
  under the constant sheaf of groups, and the functor it defines into the category
  `𝒢-Torsors` of Stacks 04UJ.
* `AlgebraicGeometry.Space.IsCompatibleAction`: the compatibility of an action
  `ρ : Gabs →* Aut X` of the abstract group with the action of `𝒢`, namely that the constant
  section `g` acts as `ρ g`.
* `AlgebraicGeometry.Space.TorsorWithMap.toAbstractQuotient` and
  `AlgebraicGeometry.Space.torsorWithMapToAbstractQuotient`: **the comparison functor**
  `[[X/𝒢]] ⥤ [[X/Gabs]]` of the last clause of Stacks 0371.

## Main results

* `AlgebraicGeometry.Space.sliceAction_fst`: the action on the sections of the localized site
  is the sectionwise action `AlgebraicGeometry.Space.smulSection`. This is what removes the
  test object of the localized site from every equivariance computation.
* `AlgebraicGeometry.Space.torsorObjToConstantTorsors_comp_projection` and
  `AlgebraicGeometry.Space.torsorWithMapToAbstractQuotient_comp_projection`: both comparison
  functors are 1-morphisms of categories over the big fppf site of `S`.
* `AlgebraicGeometry.Space.torsorWithMapToAbstractQuotient_faithful`: the comparison functor is
  faithful.
* `AlgebraicGeometry.Space.torsorWithMapToAbstractQuotient_full`: the comparison functor is
  full, as soon as a section of `ℬ` over an object of the site is unique — which is the case in
  the situation the clause is about, where `ℬ` is `S` itself.
* `AlgebraicGeometry.Space.TorsorObj.isPullback_of_bijOn` and
  `AlgebraicGeometry.Space.TorsorObj.smul_comp_of_sections`: cartesianness and equivariance of
  a morphism of fppf `G`-torsors are conditions on sections, which is what makes fullness
  work.

## Implementation notes

The total space `Total` of a torsor under a sheaf of groups is a dependent sum over the
morphism to the base, so a section of it is a pair whose second component's type depends on the
first. Every section produced here is therefore produced by
`AlgebraicGeometry.Space.TorsorObj.totalSectionOf`, which reads the morphism to the base *off*
the section rather than prescribing it; the morphism to the base is then recovered
propositionally. `AlgebraicGeometry.Space.TorsorObj.toConstantTorsor_total_ext` says that a
section of the total space is determined by its underlying section, which is what makes this
work: the type of the underlying section does not depend on the morphism to the base.

Cartesianness of the square of a morphism of torsors is used only sectionwise, through
`CategoryTheory.Limits.Types.exists_of_isPullback` and
`CategoryTheory.Limits.Types.ext_of_isPullback` applied to the image of the square under
evaluation at an object of the site; that is how the bijectivity condition `bijOn_map` of a
morphism of the triples is obtained, and in the other direction it is the only thing fullness
needs beyond the uniqueness of `b`.

## References

* [Stacks Project, Tag 0371](https://stacks.math.columbia.edu/tag/0371)
* [Stacks Project, Situation 04WL](https://stacks.math.columbia.edu/tag/04WL)
* [Stacks Project, Tag 04UJ](https://stacks.math.columbia.edu/tag/04UJ)
* [Stacks Project, Tag 04UT](https://stacks.math.columbia.edu/tag/04UT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory MonObj

universe t w u

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}

/-! ### The sectionwise action of a group object over a presheaf -/

section SmulSection

variable {Z : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (Gr Y : Over Z) [GrpObj Gr] [ModObj Gr Y]

/-- The section of `Gr ×_Z Y` determined by a section of `Gr` and a section of `Y` lying over
the same section of `Z`, read as a morphism out of the representable presheaf. -/
def smulSectionLift {V : BigFppfOver 𝒞 S hS} (gs : Gr.left.obj (op V)) (y : Y.left.obj (op V))
    (h : Gr.hom.app (op V) gs = Y.hom.app (op V) y) :
    yoneda.obj V ⟶ pullback Gr.hom Y.hom :=
  pullback.lift (yonedaEquiv.symm gs) (yonedaEquiv.symm y) (by
    rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, h])

omit [GrpObj Gr] [ModObj Gr Y] in
/-- The first projection of the lift of a pair of sections is the section of `Gr`. -/
@[reassoc (attr := simp)]
theorem smulSectionLift_fst {V : BigFppfOver 𝒞 S hS} (gs : Gr.left.obj (op V))
    (y : Y.left.obj (op V)) (h : Gr.hom.app (op V) gs = Y.hom.app (op V) y) :
    smulSectionLift Gr Y gs y h ≫ pullback.fst Gr.hom Y.hom = yonedaEquiv.symm gs :=
  pullback.lift_fst _ _ _

omit [GrpObj Gr] [ModObj Gr Y] in
/-- The second projection of the lift of a pair of sections is the section of `Y`. -/
@[reassoc (attr := simp)]
theorem smulSectionLift_snd {V : BigFppfOver 𝒞 S hS} (gs : Gr.left.obj (op V))
    (y : Y.left.obj (op V)) (h : Gr.hom.app (op V) gs = Y.hom.app (op V) y) :
    smulSectionLift Gr Y gs y h ≫ pullback.snd Gr.hom Y.hom = yonedaEquiv.symm y :=
  pullback.lift_snd _ _ _

/-- **The sectionwise action.** A section of a group object `Gr` over `Z` acts on a section of
an object `Y` it acts on lying over the same section of `Z`, by the action morphism of the
slice read on sections. -/
def smulSection {V : BigFppfOver 𝒞 S hS} (gs : Gr.left.obj (op V)) (y : Y.left.obj (op V))
    (h : Gr.hom.app (op V) gs = Y.hom.app (op V) y) : Y.left.obj (op V) :=
  yonedaEquiv (smulSectionLift Gr Y gs y h ≫ (γ[Gr, Y]).left)

/-- The sectionwise action depends on the two sections only; the hypothesis that they lie over
the same section of the base is a proposition. -/
theorem smulSection_congr {V : BigFppfOver 𝒞 S hS} {gs gs' : Gr.left.obj (op V)}
    {y y' : Y.left.obj (op V)} {h : Gr.hom.app (op V) gs = Y.hom.app (op V) y}
    {h' : Gr.hom.app (op V) gs' = Y.hom.app (op V) y'} (hg : gs = gs') (hy : y = y') :
    smulSection Gr Y gs y h = smulSection Gr Y gs' y' h' := by
  subst hg
  subst hy
  rfl

end SmulSection

/-- A morphism of fibre products which is `a` on the first and `e` on the second factor carries
the lift of a pair of sections to the lift of the pair of images. -/
private theorem smulSectionLift_comp_eq {Z Z' : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}
    {Gr Y : Over Z} {Gr' Y' : Over Z'} (u : pullback Gr.hom Y.hom ⟶ pullback Gr'.hom Y'.hom)
    (a : Gr.left ⟶ Gr'.left) (e : Y.left ⟶ Y'.left)
    (hfst : u ≫ pullback.fst Gr'.hom Y'.hom = pullback.fst Gr.hom Y.hom ≫ a)
    (hsnd : u ≫ pullback.snd Gr'.hom Y'.hom = pullback.snd Gr.hom Y.hom ≫ e)
    {V : BigFppfOver 𝒞 S hS} (gs : Gr.left.obj (op V)) (y : Y.left.obj (op V))
    (h : Gr.hom.app (op V) gs = Y.hom.app (op V) y)
    (h' : Gr'.hom.app (op V) (a.app (op V) gs) = Y'.hom.app (op V) (e.app (op V) y)) :
    smulSectionLift Gr Y gs y h ≫ u =
      smulSectionLift Gr' Y' (a.app (op V) gs) (e.app (op V) y) h' := by
  apply pullback.hom_ext
  · rw [Category.assoc, hfst, ← Category.assoc, smulSectionLift_fst,
      yonedaEquiv_symm_naturality_right, smulSectionLift_fst]
  · rw [Category.assoc, hsnd, ← Category.assoc, smulSectionLift_snd,
      yonedaEquiv_symm_naturality_right, smulSectionLift_snd]

/-- A morphism `e` of the objects acted on, which is equivariant for a morphism `u` of the
fibre products with the groups, is equivariant for the sectionwise actions. -/
private theorem map_smulSection_of_comp {Z Z' : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}
    {Gr Y : Over Z} {Gr' Y' : Over Z'} [GrpObj Gr] [ModObj Gr Y] [GrpObj Gr'] [ModObj Gr' Y']
    (u : pullback Gr.hom Y.hom ⟶ pullback Gr'.hom Y'.hom) (a : Gr.left ⟶ Gr'.left)
    (e : Y.left ⟶ Y'.left)
    (hfst : u ≫ pullback.fst Gr'.hom Y'.hom = pullback.fst Gr.hom Y.hom ≫ a)
    (hsnd : u ≫ pullback.snd Gr'.hom Y'.hom = pullback.snd Gr.hom Y.hom ≫ e)
    (hγ : (γ[Gr,Y]).left ≫ e = u ≫ (γ[Gr',Y']).left)
    {V : BigFppfOver 𝒞 S hS} (gs : Gr.left.obj (op V)) (y : Y.left.obj (op V))
    (h : Gr.hom.app (op V) gs = Y.hom.app (op V) y)
    (h' : Gr'.hom.app (op V) (a.app (op V) gs) = Y'.hom.app (op V) (e.app (op V) y)) :
    e.app (op V) (smulSection Gr Y gs y h) =
      smulSection Gr' Y' (a.app (op V) gs) (e.app (op V) y) h' := by
  have key := smulSectionLift_comp_eq u a e hfst hsnd gs y h h'
  refine (yonedaEquiv_comp _ e).symm.trans (congrArg yonedaEquiv ?_)
  rw [Category.assoc, hγ, ← Category.assoc, key]

/-! ### The action on the sections of the localized site is the sectionwise action -/

/-- The action of `AlgebraicGeometry.Space.sliceAction` on the sections of the localized site
`(Sch/U)_fppf` is the sectionwise action `AlgebraicGeometry.Space.smulSection` of the
underlying sections. The test object of the localized site enters only through the section of
the representable presheaf that both sections lie over, so no computation with the localized
site is needed once this is known. -/
theorem sliceAction_fst {U : BigFppfOver 𝒞 S hS} (Gr Y : Over (yoneda.obj U)) [GrpObj Gr]
    [ModObj Gr Y] (W : Over U) (g : (sliceSection Gr).obj (op W))
    (x : (sliceSection Y).obj (op W)) :
    (sliceAction Gr Y W g x).1 = smulSection Gr Y g.1 x.1 (g.2.trans x.2.symm) :=
  rfl

/-! ### Identifying the acting group with the constant sheaf of groups -/

variable {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}

/-- The sheaf of groups on the localized site `(Sch/U)_fppf` of sections of the acting group
`G_U = U ×_{b, ℬ} 𝒢` of an object of the big fppf site together with a section `b` of `ℬ`. -/
abbrev baseGroupSheaf (hB : IsAlgebraicSpace 𝒞 S hS B) (G : GroupAlgebraicSpace 𝒞 S hS B hB)
    (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ B) :
    SheafOfGroups.{u} (C := Over U) ((BigFppfOver.topology 𝒞 S hS).over U) :=
  sliceSheafOfGroups (pullbackGroup hB G U b).obj.X (pullbackGroup hB G U b).property.isSheaf

/-- The base change `G_U ⟶ G_{U'}` of the acting group along a morphism `f : U ⟶ U'` of the big
fppf site lying over `ℬ`. For a morphism of fppf `G`-torsors this is
`AlgebraicGeometry.Space.groupBaseChange`, which is the same morphism read off the torsors. -/
def baseChangeGroupHom (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB) {U U' : BigFppfOver 𝒞 S hS}
    {b : yoneda.obj U ⟶ B} {b' : yoneda.obj U' ⟶ B} (f : U ⟶ U')
    (hf : yoneda.map f ≫ b' = b) :
    pullback G.obj.X.hom b ⟶ pullback G.obj.X.hom b' :=
  pullback.map _ _ _ _ (𝟙 G.obj.X.left) (yoneda.map f) (𝟙 B) (by simp) (by simp [hf])

/-- The base change of the acting group commutes with the projections to `𝒢`. -/
@[reassoc (attr := simp)]
theorem baseChangeGroupHom_fst (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB) {U U' : BigFppfOver 𝒞 S hS}
    {b : yoneda.obj U ⟶ B} {b' : yoneda.obj U' ⟶ B} (f : U ⟶ U')
    (hf : yoneda.map f ≫ b' = b) :
    baseChangeGroupHom hB G f hf ≫ pullback.fst G.obj.X.hom b' =
      pullback.fst G.obj.X.hom b :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The base change of the acting group lies over the morphism `f` of the site. -/
@[reassoc (attr := simp)]
theorem baseChangeGroupHom_snd (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB) {U U' : BigFppfOver 𝒞 S hS}
    {b : yoneda.obj U ⟶ B} {b' : yoneda.obj U' ⟶ B} (f : U ⟶ U')
    (hf : yoneda.map f ≫ b' = b) :
    baseChangeGroupHom hB G f hf ≫ pullback.snd G.obj.X.hom b' =
      pullback.snd G.obj.X.hom b ≫ yoneda.map f :=
  pullback.lift_snd _ _ _

variable {hB : IsAlgebraicSpace 𝒞 S hS B} {G : GroupAlgebraicSpace 𝒞 S hS B hB}

/-- The base change of the acting group along the morphism of a morphism of fppf `G`-torsors is
the base change along that morphism of the site. -/
theorem baseChangeGroupHom_eq_groupBaseChange {T T' : TorsorObj hB G} (m : T ⟶ T') :
    baseChangeGroupHom hB G m.f m.comp_b = groupBaseChange m.f m.comp_b :=
  rfl

variable (hB G) in
/-- **The identification of the acting group with the constant sheaf of groups.** For every
object `U` of the big fppf site and every section `b` of `ℬ` over `U`, an identification of the
sections of `G_U = U ×_{b, ℬ} 𝒢` on the localized site `(Sch/U)_fppf` with the sections of the
constant sheaf of groups with value `Gabs`, compatible with base change along a morphism of the
site lying over `ℬ`.

This is the datum that makes `𝒢` the constant group algebraic space with value `Gabs` as far as
the comparison of Situation 04WL with Stacks 0371 is concerned. Compatibility with base change
is what makes a morphism of quadruples into a morphism of triples: equivariance of a morphism
of torsors is stated against `AlgebraicGeometry.Space.groupBaseChange`, while equivariance of a
morphism of triples is stated against one and the same constant sheaf of groups. -/
structure ConstantGroupData (Gabs : Type w) [Group Gabs]
    [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat.{w}] where
  /-- The identification of the sections of `G_U` with those of the constant sheaf. -/
  equiv : ∀ (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ B),
    SheafOfGroups.SectionEquiv (constantGroupSheaf 𝒞 S hS Gabs U) (baseGroupSheaf hB G U b)
  /-- The identification is compatible with base change along a morphism over `ℬ`. The test
  object of the localized site at `U'` is given as `Over.mk a` for a morphism `a` *equal* to
  the composite, rather than as the composite itself, so that the condition applies at the
  test object a computation produces without rewriting inside it. -/
  equiv_baseChange : ∀ {U U' : BigFppfOver 𝒞 S hS} {b : yoneda.obj U ⟶ B}
    {b' : yoneda.obj U' ⟶ B} (f : U ⟶ U') (hf : yoneda.map f ≫ b' = b) (W : Over U)
    (a : W.left ⟶ U') (_ : a = W.hom ≫ f)
    (gs : (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) Gabs).presheaf.obj (op W.left)),
    (((equiv U' b').equiv (op (Over.mk a))) gs).1 =
      (baseChangeGroupHom hB G f hf).app (op W.left) (((equiv U b).equiv (op W)) gs).1

variable {Gabs : Type w} [Group Gabs]
  [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat.{w}]

namespace ConstantGroupData

/-- The section of `𝒢` over an object `V` of the big fppf site lying over a given section `β` of
`ℬ` which the identification attaches to an element `g` of the abstract group: the *constant
section* `g`. -/
def constSection (D : ConstantGroupData hB G Gabs) (V : BigFppfOver 𝒞 S hS)
    (β : yoneda.obj V ⟶ B) (g : Gabs) : G.obj.X.left.obj (op V) :=
  (pullback.fst G.obj.X.hom β).app (op V)
    (((D.equiv V β).equiv (op (Over.mk (𝟙 V)))
      (constantSheafOfGroupsUnit (BigFppfOver.topology 𝒞 S hS) Gabs (op V) g)).1)

/-- The constant section `g` of `𝒢` over `V` attached to a section `β` of `ℬ` lies over `β`. -/
theorem constSection_over (D : ConstantGroupData hB G Gabs) (V : BigFppfOver 𝒞 S hS)
    (β : yoneda.obj V ⟶ B) (g : Gabs) :
    G.obj.X.hom.app (op V) (D.constSection V β g) = yonedaEquiv β := by
  have hz := ((D.equiv V β).equiv (op (Over.mk (𝟙 V)))
    (constantSheafOfGroupsUnit (BigFppfOver.topology 𝒞 S hS) Gabs (op V) g)).2
  have hc := ConcreteCategory.congr_hom
    (NatTrans.congr_app (pullback.condition (f := G.obj.X.hom) (g := β)) (op V))
    (((D.equiv V β).equiv (op (Over.mk (𝟙 V)))
      (constantSheafOfGroupsUnit (BigFppfOver.topology 𝒞 S hS) Gabs (op V) g)).1)
  refine hc.trans ?_
  change β.app (op V) ((pullback.snd G.obj.X.hom β).app (op V) _) = _
  rw [show (pullback.snd G.obj.X.hom β).app (op V) _ = 𝟙 V from hz]
  rfl

end ConstantGroupData

/-! ### The torsor under the constant sheaf of groups attached to an fppf `G`-torsor -/

namespace TorsorObj

/-- **The universe bridge applied to an fppf `G`-torsor.** The torsor of sheaves on the
localized site attached to an fppf `G_U`-torsor by
`AlgebraicGeometry.Space.slicePseudoTorsor`, with its sections lifted to `Type (max u t)` and
its acting sheaf of groups replaced by the constant sheaf of groups with value `Gabs`. -/
def toConstantTorsor (D : ConstantGroupData hB G Gabs) (T : TorsorObj hB G) :
    SheafOfGroups.Torsors.{max u t} (bigConstantGroupSheaf 𝒞 S hS Gabs) where
  base := T.U
  torsor := (slicePseudoTorsor T.group T.total
    (pullbackGroup hB G T.U T.b).property.isSheaf T.isAlgebraicSpace.isSheaf
    T.isFppfTorsor.1).bridge.{t} (D.equiv T.U T.b)
  isTorsor := by
    refine PseudoTorsor.bridge_isTorsor _ _ ?_
    obtain ⟨I, Bi, f, -, hcov, hsec⟩ := T.isFppfTorsor.2
    exact isTorsor_slicePseudoTorsor 𝒞 S hS T.group T.total _ _ T.isFppfTorsor.1 Bi f hcov hsec

/-- The section of the total space of the attached torsor determined by a section of the total
space of the fppf `G`-torsor: the morphism to the base is read off the section. -/
def totalSectionOf (D : ConstantGroupData hB G Gabs) (T : TorsorObj hB G)
    {V : (BigFppfOver 𝒞 S hS)ᵒᵖ} (s : T.total.left.obj V) :
    (T.toConstantTorsor.{t} D).Total V :=
  ⟨T.total.hom.app V s, ULift.up ⟨s, rfl⟩⟩

/-- The morphism to the base of `totalSectionOf` is the image of the section. -/
@[simp]
theorem totalSectionOf_fst (D : ConstantGroupData hB G Gabs) (T : TorsorObj hB G)
    {V : (BigFppfOver 𝒞 S hS)ᵒᵖ} (s : T.total.left.obj V) :
    (totalSectionOf.{t} D T s).1 = T.total.hom.app V s :=
  rfl

/-- The underlying section of a section of the total space of the attached torsor. Its type
does not depend on the morphism to the base, which is what makes the dependent sum of the
total space harmless. -/
def totalSectionVal (D : ConstantGroupData hB G Gabs) (T : TorsorObj hB G)
    {V : (BigFppfOver 𝒞 S hS)ᵒᵖ} (p : (T.toConstantTorsor.{t} D).Total V) :
    T.total.left.obj V :=
  p.2.down.1

/-- The underlying section of `totalSectionOf s` is `s`. -/
@[simp]
theorem totalSectionVal_totalSectionOf (D : ConstantGroupData hB G Gabs) (T : TorsorObj hB G)
    {V : (BigFppfOver 𝒞 S hS)ᵒᵖ} (s : T.total.left.obj V) :
    totalSectionVal.{t} D T (totalSectionOf.{t} D T s) = s :=
  rfl

/-- The morphism to the base of a section of the total space of the attached torsor is the
image of its underlying section. -/
theorem totalSectionVal_over (D : ConstantGroupData hB G Gabs) (T : TorsorObj hB G)
    {V : (BigFppfOver 𝒞 S hS)ᵒᵖ} (p : (T.toConstantTorsor.{t} D).Total V) :
    T.total.hom.app V (totalSectionVal.{t} D T p) = p.1 :=
  p.2.down.2

/-- **A section of the total space of the attached torsor is determined by its underlying
section.** -/
theorem toConstantTorsor_total_ext (D : ConstantGroupData hB G Gabs) (T : TorsorObj hB G)
    {V : (BigFppfOver 𝒞 S hS)ᵒᵖ} (p q : (T.toConstantTorsor.{t} D).Total V)
    (h : totalSectionVal.{t} D T p = totalSectionVal.{t} D T q) : p = q := by
  obtain ⟨a, ⟨⟨s, hs⟩⟩⟩ := p
  obtain ⟨a', ⟨⟨s', hs'⟩⟩⟩ := q
  change s = s' at h
  subst h
  change T.total.hom.app V s = a at hs
  change T.total.hom.app V s = a' at hs'
  obtain rfl : a = a' := hs.symm.trans hs'
  rfl

/-- A section of the total space of the attached torsor is `totalSectionOf` of its underlying
section. -/
theorem totalSectionOf_totalSectionVal (D : ConstantGroupData hB G Gabs) (T : TorsorObj hB G)
    {V : (BigFppfOver 𝒞 S hS)ᵒᵖ} (p : (T.toConstantTorsor.{t} D).Total V) :
    totalSectionOf.{t} D T (totalSectionVal.{t} D T p) = p :=
  toConstantTorsor_total_ext D T _ _ rfl

/-- Restricting a section of the total space of the attached torsor restricts its underlying
section. -/
@[simp]
theorem totalSectionVal_totalMap (D : ConstantGroupData hB G Gabs) (T : TorsorObj hB G)
    {V W : (BigFppfOver 𝒞 S hS)ᵒᵖ} (h : V ⟶ W)
    (p : (T.toConstantTorsor.{t} D).Total V) :
    totalSectionVal.{t} D T ((T.toConstantTorsor.{t} D).totalMap h p) =
      T.total.left.map h (totalSectionVal.{t} D T p) :=
  rfl

/-- The constant sheaf of groups acts on the underlying section by the sectionwise action of
the section of `G_U` that the identification attaches to it. -/
theorem totalSectionVal_totalSmul (D : ConstantGroupData hB G Gabs) (T : TorsorObj hB G)
    {V : BigFppfOver 𝒞 S hS}
    (gs : (bigConstantGroupSheaf 𝒞 S hS Gabs).presheaf.obj (op V))
    (p : (T.toConstantTorsor.{t} D).Total (op V)) :
    totalSectionVal.{t} D T ((T.toConstantTorsor.{t} D).totalSmul gs p) =
      smulSection T.group T.total
        (((D.equiv T.U T.b).equiv (op (Over.mk p.1)) gs).1)
        (totalSectionVal.{t} D T p)
        ((((D.equiv T.U T.b).equiv (op (Over.mk p.1)) gs).2).trans
          (totalSectionVal_over.{t} D T p).symm) :=
  rfl

/-! ### Morphisms, and the comparison functor on torsors -/

omit [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat] in
/-- The projections of the fibre product `G_U ×_U P` read on the lift of a pair of sections,
in the spelling in which `AlgebraicGeometry.Space.actionBaseChange` and
`AlgebraicGeometry.Space.actionComparison` present that fibre product. -/
@[reassoc (attr := simp)]
theorem smulSectionLift_fst_torsor (T : TorsorObj hB G) {V : BigFppfOver 𝒞 S hS}
    (gs : T.group.left.obj (op V)) (s : T.total.left.obj (op V))
    (h : T.group.hom.app (op V) gs = T.total.hom.app (op V) s) :
    smulSectionLift T.group T.total gs s h ≫
      pullback.fst (pullback.snd G.obj.X.hom T.b) T.total.hom = yonedaEquiv.symm gs :=
  pullback.lift_fst _ _ _

omit [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat] in
/-- The second projection of the lift of a pair of sections of `G_U` and `P`, in the spelling in
which `AlgebraicGeometry.Space.actionBaseChange` presents that fibre product, is the section of
`P`. -/
@[reassoc (attr := simp)]
theorem smulSectionLift_snd_torsor (T : TorsorObj hB G) {V : BigFppfOver 𝒞 S hS}
    (gs : T.group.left.obj (op V)) (s : T.total.left.obj (op V))
    (h : T.group.hom.app (op V) gs = T.total.hom.app (op V) s) :
    smulSectionLift T.group T.total gs s h ≫
      pullback.snd (pullback.snd G.obj.X.hom T.b) T.total.hom = yonedaEquiv.symm s :=
  pullback.lift_snd _ _ _

omit [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat] in
/-- The base change of the acting group along a morphism of fppf `G`-torsors carries a section
lying over a section of the total space to one lying over its image. -/
theorem baseChangeGroupHom_over {T T' : TorsorObj hB G} (m : T ⟶ T')
    {V : BigFppfOver 𝒞 S hS} (gs : T.group.left.obj (op V))
    (s : T.total.left.obj (op V))
    (h : T.group.hom.app (op V) gs = T.total.hom.app (op V) s) :
    T'.group.hom.app (op V) ((groupBaseChange m.f m.comp_b).app (op V) gs) =
      T'.total.hom.app (op V) (m.g.app (op V) s) := by
  have h1 : T'.group.hom.app (op V) ((groupBaseChange m.f m.comp_b).app (op V) gs) =
      T.group.hom.app (op V) gs ≫ m.f :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (groupBaseChange_snd m.f m.comp_b) (op V)) gs
  have h2 : T'.total.hom.app (op V) (m.g.app (op V) s) =
      T.total.hom.app (op V) s ≫ m.f :=
    ConcreteCategory.congr_hom (NatTrans.congr_app m.isPullback.w (op V)) s
  rw [h1, h2, h]

omit [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat] in
/-- **The equivariance of a morphism of fppf `G`-torsors, read on sections.** The morphism of
total spaces carries the sectionwise action of `G_U` to the sectionwise action of `G_{U'}` on
the base-changed section. -/
theorem Hom.map_smulSection {T T' : TorsorObj hB G} (m : T ⟶ T') {V : BigFppfOver 𝒞 S hS}
    (gs : T.group.left.obj (op V)) (s : T.total.left.obj (op V))
    (h : T.group.hom.app (op V) gs = T.total.hom.app (op V) s) :
    m.g.app (op V) (smulSection T.group T.total gs s h) =
      smulSection T'.group T'.total ((groupBaseChange m.f m.comp_b).app (op V) gs)
        (m.g.app (op V) s) (baseChangeGroupHom_over m gs s h) := by
  exact map_smulSection_of_comp _ _ _
    (actionBaseChange_fst m.f m.comp_b m.g m.isPullback.w.symm)
    (actionBaseChange_snd m.f m.comp_b m.g m.isPullback.w.symm) m.smul_comp gs s h _

/-- A morphism of fppf `G`-torsors, read as a morphism of torsors under the constant sheaf of
groups: the same morphism of total spaces, read on sections. -/
def toConstantTorsorHom (D : ConstantGroupData hB G Gabs) {T T' : TorsorObj hB G} (m : T ⟶ T') :
    T.toConstantTorsor.{t} D ⟶ T'.toConstantTorsor.{t} D where
  base := m.f
  map V p := totalSectionOf.{t} D T' (m.g.app V (totalSectionVal.{t} D T p))
  map_naturality {V W} h p := by
    refine toConstantTorsor_total_ext D T' _ _ ?_
    exact NatTrans.naturality_apply m.g h (totalSectionVal.{t} D T p)
  map_equivariant V gs p := by
    obtain ⟨V, rfl⟩ : ∃ V₀, op V₀ = V := ⟨V.unop, rfl⟩
    refine toConstantTorsor_total_ext D T' _ _ ?_
    have hw : T'.total.hom.app (op V) (m.g.app (op V) (totalSectionVal.{t} D T p)) =
        p.1 ≫ m.f :=
      (ConcreteCategory.congr_hom (NatTrans.congr_app m.isPullback.w (op V)) _).trans
        (congrArg (· ≫ m.f) (totalSectionVal_over.{t} D T p))
    have hgs := D.equiv_baseChange m.f m.comp_b (Over.mk p.1)
      (T'.total.hom.app (op V) (m.g.app (op V) (totalSectionVal.{t} D T p))) hw gs
    refine Eq.trans ?_ (totalSectionVal_totalSmul.{t} D T' gs
      (totalSectionOf.{t} D T' (m.g.app (op V) (totalSectionVal.{t} D T p)))).symm
    refine Eq.trans (congrArg (m.g.app (op V))
      (totalSectionVal_totalSmul.{t} D T gs p)) ?_
    refine Eq.trans (Hom.map_smulSection m _ _ _) ?_
    exact smulSection_congr T'.group T'.total hgs.symm rfl
  bijOn_map V a := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      change T'.total.hom.app V (m.g.app V (totalSectionVal.{t} D T p)) = a ≫ m.f
      refine Eq.trans (ConcreteCategory.congr_hom
        (NatTrans.congr_app m.isPullback.w V) (totalSectionVal.{t} D T p)) ?_
      exact congrArg (· ≫ m.f) ((totalSectionVal_over.{t} D T p).trans hp)
    · intro p hp q hq hpq
      refine toConstantTorsor_total_ext D T _ _ ?_
      have hpb := m.isPullback.map ((evaluation (BigFppfOver 𝒞 S hS)ᵒᵖ (Type u)).obj V)
      refine Types.ext_of_isPullback hpb ?_ ?_
      · exact congrArg (totalSectionVal.{t} D T') hpq
      · exact ((totalSectionVal_over.{t} D T p).trans hp).trans
          ((totalSectionVal_over.{t} D T q).trans hq).symm
    · intro q hq
      have hpb := m.isPullback.map ((evaluation (BigFppfOver 𝒞 S hS)ᵒᵖ (Type u)).obj V)
      obtain ⟨s, hs1, hs2⟩ := Types.exists_of_isPullback hpb
        (totalSectionVal.{t} D T' q) a ((totalSectionVal_over.{t} D T' q).trans hq)
      refine ⟨totalSectionOf.{t} D T s, ?_, ?_⟩
      · change T.total.hom.app V s = a
        exact hs2
      · exact toConstantTorsor_total_ext D T' _ _ hs1

end TorsorObj

/-- **The comparison functor on torsors.** The functor from the category of fppf `G`-torsors of
Stacks 04US to the category `𝒢-Torsors` of Stacks 04UJ for the constant sheaf of groups with
value `Gabs`, given an identification of the acting groups. -/
def torsorObjToConstantTorsors (D : ConstantGroupData hB G Gabs) :
    TorsorObj hB G ⥤ SheafOfGroups.Torsors.{max u t} (bigConstantGroupSheaf 𝒞 S hS Gabs) where
  obj T := T.toConstantTorsor.{t} D
  map m := TorsorObj.toConstantTorsorHom.{t} D m
  map_id T := SheafOfGroups.Torsors.Hom.ext rfl (by
    funext V p
    exact TorsorObj.toConstantTorsor_total_ext D T _ _ rfl)
  map_comp m n := SheafOfGroups.Torsors.Hom.ext rfl rfl

/-- The comparison functor on torsors is a 1-morphism of categories over the big fppf site of
`S`: it does not move the base object. -/
theorem torsorObjToConstantTorsors_comp_projection (D : ConstantGroupData hB G Gabs) :
    torsorObjToConstantTorsors.{t} D ⋙ SheafOfGroups.Torsors.projection =
      torsorProjection hB G :=
  rfl

/-! ### The comparison functor on the quotient categories -/

variable {X : Over B} [ModObj G.obj.X X]

/-- **The compatibility of the two actions.** The action `ρ` of the abstract group on the
sections of `X` is the action of `𝒢` through the constant sections: for every section `β` of
`ℬ` over an object of the site, the constant section `g` of `𝒢` lying over `β` acts on the
sections of `X` lying over `β` as `ρ g` does. -/
def IsCompatibleAction (D : ConstantGroupData hB G Gabs)
    (ρ : Gabs →* Aut (X.left ⋙ uliftFunctor.{t})) : Prop :=
  ∀ (V : BigFppfOver 𝒞 S hS) (β : yoneda.obj V ⟶ B) (g : Gabs) (x : X.left.obj (op V))
    (hx : X.hom.app (op V) x = yonedaEquiv β),
    smulSection G.obj.X X (D.constSection V β g) x
        ((D.constSection_over V β g).trans hx.symm) =
      ((ρ g).hom.app (op V) (ULift.up x)).down

namespace TorsorWithMap

omit [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat] in
/-- The image under the equivariant map `φ` of a section of the total space lies over the same
section of `ℬ` as the `𝒢`-component of a section of `G_U` over the same section of `P`. -/
theorem map_over_section (A : TorsorWithMap hB G X) {V : BigFppfOver 𝒞 S hS}
    (gs : A.toTorsorObj.group.left.obj (op V)) (s : A.toTorsorObj.total.left.obj (op V))
    (h : A.toTorsorObj.group.hom.app (op V) gs =
      A.toTorsorObj.total.hom.app (op V) s) :
    G.obj.X.hom.app (op V) ((pullback.fst G.obj.X.hom A.toTorsorObj.b).app (op V) gs) =
      X.hom.app (op V) (A.map.app (op V) s) := by
  have h1 : G.obj.X.hom.app (op V)
        ((pullback.fst G.obj.X.hom A.toTorsorObj.b).app (op V) gs) =
      A.toTorsorObj.b.app (op V)
        ((pullback.snd G.obj.X.hom A.toTorsorObj.b).app (op V) gs) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (pullback.condition (f := G.obj.X.hom) (g := A.toTorsorObj.b)) (op V)) gs
  have h2 : X.hom.app (op V) (A.map.app (op V) s) =
      A.toTorsorObj.b.app (op V) (A.toTorsorObj.total.hom.app (op V) s) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app A.map_over (op V)) s
  rw [h1, h2]
  exact congrArg (A.toTorsorObj.b.app (op V)) h

omit [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat] in
/-- The equivariant map `φ` of a quadruple carries the sectionwise action of `G_U` on the total
space to the sectionwise action of `𝒢` on `X`. -/
theorem map_smulSection (A : TorsorWithMap hB G X) {V : BigFppfOver 𝒞 S hS}
    (gs : A.toTorsorObj.group.left.obj (op V)) (s : A.toTorsorObj.total.left.obj (op V))
    (h : A.toTorsorObj.group.hom.app (op V) gs =
      A.toTorsorObj.total.hom.app (op V) s) :
    A.map.app (op V) (smulSection A.toTorsorObj.group A.toTorsorObj.total gs s h) =
      smulSection G.obj.X X ((pullback.fst G.obj.X.hom A.toTorsorObj.b).app (op V) gs)
        (A.map.app (op V) s) (map_over_section A gs s h) := by
  exact map_smulSection_of_comp _ _ _
    (actionComparison_fst X A.toTorsorObj A.map A.map_over)
    (actionComparison_snd X A.toTorsorObj A.map A.map_over) A.smul_map gs s h _

/-- **The comparison functor on objects.** A quadruple `(U, b, P, φ)` of Situation 04WL, read
as a triple `(U, P, φ)` of Stacks 0371: the torsor is carried across by the universe bridge and
the identification of the acting groups, and the equivariant map is the same map read on
sections. -/
def toAbstractQuotient (D : ConstantGroupData hB G Gabs)
    {ρ : Gabs →* Aut (X.left ⋙ uliftFunctor.{t})} (hρ : IsCompatibleAction D ρ)
    (A : TorsorWithMap hB G X) :
    AbstractGroupQuotientStack.{max u t} 𝒞 S hS Gabs (X.left ⋙ uliftFunctor.{t}) ρ :=
  AbstractGroupQuotientStack.ofTotal (ρ := ρ) (A.toTorsorObj.toConstantTorsor.{t} D)
    (fun V p => ULift.up (A.map.app V (TorsorObj.totalSectionVal.{t} D A.toTorsorObj p)))
    (fun {V V'} h p => ULift.ext _ _
      (NatTrans.naturality_apply A.map h (TorsorObj.totalSectionVal.{t} D A.toTorsorObj p)))
    (fun V g p => by
      obtain ⟨V, rfl⟩ : ∃ V₀, op V₀ = V := ⟨V.unop, rfl⟩
      refine ULift.ext _ _ ?_
      have hfst : (pullback.fst G.obj.X.hom A.toTorsorObj.b).app (op V)
            (((D.equiv A.toTorsorObj.U A.toTorsorObj.b).equiv (op (Over.mk p.1))
              (constantSheafOfGroupsUnit (BigFppfOver.topology 𝒞 S hS) Gabs (op V) g)).1) =
          D.constSection V (yoneda.map p.1 ≫ A.toTorsorObj.b) g := by
        have hb := D.equiv_baseChange (U' := A.toTorsorObj.U) (b' := A.toTorsorObj.b)
          (b := yoneda.map p.1 ≫ A.toTorsorObj.b) p.1 rfl (Over.mk (𝟙 V)) p.1
          (Category.id_comp p.1).symm
          (constantSheafOfGroupsUnit (BigFppfOver.topology 𝒞 S hS) Gabs (op V) g)
        refine Eq.trans
          (congrArg ((pullback.fst G.obj.X.hom A.toTorsorObj.b).app (op V)) hb) ?_
        exact ConcreteCategory.congr_hom (NatTrans.congr_app
          (baseChangeGroupHom_fst hB G p.1
            (rfl : yoneda.map p.1 ≫ A.toTorsorObj.b = _)) (op V))
          (((D.equiv V (yoneda.map p.1 ≫ A.toTorsorObj.b)).equiv (op (Over.mk (𝟙 V)))
            (constantSheafOfGroupsUnit (BigFppfOver.topology 𝒞 S hS) Gabs (op V) g)).1)
      have hx : X.hom.app (op V) (A.map.app (op V)
          (TorsorObj.totalSectionVal.{t} D A.toTorsorObj p)) =
          yonedaEquiv (yoneda.map p.1 ≫ A.toTorsorObj.b) := by
        have hy : yonedaEquiv (yoneda.map p.1 ≫ A.toTorsorObj.b) =
            A.toTorsorObj.b.app (op V) p.1 :=
          (yonedaEquiv_comp (yoneda.map p.1) A.toTorsorObj.b).trans
            (congrArg (A.toTorsorObj.b.app (op V)) (yonedaEquiv_yoneda_map p.1))
        refine Eq.trans (ConcreteCategory.congr_hom
          (NatTrans.congr_app A.map_over (op V))
          (TorsorObj.totalSectionVal.{t} D A.toTorsorObj p)) ?_
        refine Eq.trans ?_ hy.symm
        exact congrArg (A.toTorsorObj.b.app (op V))
          (TorsorObj.totalSectionVal_over.{t} D A.toTorsorObj p)
      refine Eq.trans ?_ (hρ V (yoneda.map p.1 ≫ A.toTorsorObj.b) g _ hx)
      refine Eq.trans (congrArg (A.map.app (op V))
        (TorsorObj.totalSectionVal_totalSmul.{t} D A.toTorsorObj _ p)) ?_
      refine Eq.trans (map_smulSection A _ _ _) ?_
      exact smulSection_congr G.obj.X X hfst rfl)

/-- **The comparison functor on morphisms.** A morphism of quadruples, read as a morphism of
triples: the same morphism of total spaces, which is compatible with the two equivariant maps
because it is so on the quadruples. -/
def toAbstractQuotientHom (D : ConstantGroupData hB G Gabs)
    {ρ : Gabs →* Aut (X.left ⋙ uliftFunctor.{t})} (hρ : IsCompatibleAction D ρ)
    {A C : TorsorWithMap hB G X} (m : A ⟶ C) :
    A.toAbstractQuotient D hρ ⟶ C.toAbstractQuotient D hρ :=
  AbstractGroupQuotientStack.homOfTorsorHom
    (TorsorObj.toConstantTorsorHom.{t} D m.toHom)
    (fun V _ => ULift.ext _ _
      (ConcreteCategory.congr_hom (NatTrans.congr_app m.comp_map V) _))

end TorsorWithMap

/-- **The comparison functor of the last clause of Stacks 0371.** The functor
`[[X/𝒢]] ⥤ [[X/Gabs]]` from the quotient category of Situation 04WL to the quotient of
Stacks 0371 by the abstract group `Gabs`, given an identification of the acting group with the
constant sheaf of groups and the compatibility of the two actions on `X`. -/
def torsorWithMapToAbstractQuotient (D : ConstantGroupData hB G Gabs)
    {ρ : Gabs →* Aut (X.left ⋙ uliftFunctor.{t})} (hρ : IsCompatibleAction D ρ) :
    TorsorWithMap hB G X ⥤
      AbstractGroupQuotientStack.{max u t} 𝒞 S hS Gabs (X.left ⋙ uliftFunctor.{t}) ρ where
  obj A := A.toAbstractQuotient D hρ
  map m := TorsorWithMap.toAbstractQuotientHom D hρ m
  map_id A := AbstractGroupQuotientStack.Hom.ext rfl (by
    funext V p
    exact TorsorObj.toConstantTorsor_total_ext D A.toTorsorObj _ _ rfl)
  map_comp m n := AbstractGroupQuotientStack.Hom.ext rfl rfl

/-- The comparison functor is a 1-morphism of categories over the big fppf site of `S`: a
quadruple and the triple it becomes have the same base object, and a morphism and its image the
same morphism of the site. -/
theorem torsorWithMapToAbstractQuotient_comp_projection (D : ConstantGroupData hB G Gabs)
    {ρ : Gabs →* Aut (X.left ⋙ uliftFunctor.{t})} (hρ : IsCompatibleAction D ρ) :
    torsorWithMapToAbstractQuotient D hρ ⋙ AbstractGroupQuotientStack.projection =
      TorsorWithMap.projection hB G X :=
  rfl

/-- **The comparison functor is faithful.** A morphism of quadruples is a morphism of the
underlying torsors subject to a condition, and the morphism of total spaces is recovered from
the morphism of triples by reading it on sections. -/
theorem torsorWithMapToAbstractQuotient_faithful (D : ConstantGroupData hB G Gabs)
    {ρ : Gabs →* Aut (X.left ⋙ uliftFunctor.{t})} (hρ : IsCompatibleAction D ρ) :
    (torsorWithMapToAbstractQuotient D hρ).Faithful where
  map_injective {A C} m n h := by
    refine TorsorWithMap.Hom.ext X (TorsorObj.Hom.ext ?_ ?_)
    · exact congrArg AbstractGroupQuotientStack.Hom.base h
    · have hm := congrArg AbstractGroupQuotientStack.Hom.map h
      ext V s
      exact congrArg (TorsorObj.totalSectionVal.{t} D C.toTorsorObj)
        (congrFun (congrFun hm V) (TorsorObj.totalSectionOf.{t} D A.toTorsorObj s))

/-! ### Fullness -/

namespace TorsorObj

omit [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat] in
/-- The lift of a pair of sections is carried by the base-change morphism of `G_U ×_U P` to the
lift of the base-changed pair. This uses nothing about the morphism of total spaces beyond its
lying over `f`. -/
theorem smulSectionLift_comp_actionBaseChange {T T' : TorsorObj hB G} (f : T.U ⟶ T'.U)
    (hf : yoneda.map f ≫ T'.b = T.b) (gg : T.total.left ⟶ T'.total.left)
    (hg : T.total.hom ≫ yoneda.map f = gg ≫ T'.total.hom)
    {V : BigFppfOver 𝒞 S hS} (gs : T.group.left.obj (op V))
    (s : T.total.left.obj (op V))
    (h : T.group.hom.app (op V) gs = T.total.hom.app (op V) s)
    (h' : T'.group.hom.app (op V) ((groupBaseChange f hf).app (op V) gs) =
      T'.total.hom.app (op V) (gg.app (op V) s)) :
    smulSectionLift T.group T.total gs s h ≫ actionBaseChange f hf gg hg =
      smulSectionLift T'.group T'.total ((groupBaseChange f hf).app (op V) gs)
        (gg.app (op V) s) h' := by
  exact smulSectionLift_comp_eq _ _ _ (actionBaseChange_fst f hf gg hg)
    (actionBaseChange_snd f hf gg hg) gs s h h'

omit [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat] in
/-- The base change of the acting group along a morphism of the site carries a section lying
over a section of the total space to one lying over its image, for any morphism of total
spaces over that morphism of the site. -/
theorem groupBaseChange_over_of_comp {T T' : TorsorObj hB G} (f : T.U ⟶ T'.U)
    (hf : yoneda.map f ≫ T'.b = T.b) (gg : T.total.left ⟶ T'.total.left)
    (hg : T.total.hom ≫ yoneda.map f = gg ≫ T'.total.hom)
    {V : BigFppfOver 𝒞 S hS} (gs : T.group.left.obj (op V))
    (s : T.total.left.obj (op V))
    (h : T.group.hom.app (op V) gs = T.total.hom.app (op V) s) :
    T'.group.hom.app (op V) ((groupBaseChange f hf).app (op V) gs) =
      T'.total.hom.app (op V) (gg.app (op V) s) := by
  have h1 : T'.group.hom.app (op V) ((groupBaseChange f hf).app (op V) gs) =
      T.group.hom.app (op V) gs ≫ f :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (groupBaseChange_snd f hf) (op V)) gs
  have h2 : T.total.hom.app (op V) s ≫ f =
      T'.total.hom.app (op V) (gg.app (op V) s) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hg (op V)) s
  rw [h1, h, h2]

omit [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat] in
/-- **Equivariance is a condition on sections.** A morphism of total spaces over a morphism of
the site which carries the sectionwise action of `G_U` to that of `G_{U'}` is equivariant in
the sense the morphisms of fppf `G`-torsors ask for. -/
theorem smul_comp_of_sections {T T' : TorsorObj hB G} (f : T.U ⟶ T'.U)
    (hf : yoneda.map f ≫ T'.b = T.b) (gg : T.total.left ⟶ T'.total.left)
    (hg : T.total.hom ≫ yoneda.map f = gg ≫ T'.total.hom)
    (hs : ∀ (V : BigFppfOver 𝒞 S hS) (gs : T.group.left.obj (op V))
      (s : T.total.left.obj (op V))
      (h : T.group.hom.app (op V) gs = T.total.hom.app (op V) s),
      gg.app (op V) (smulSection T.group T.total gs s h) =
        smulSection T'.group T'.total ((groupBaseChange f hf).app (op V) gs)
          (gg.app (op V) s) (groupBaseChange_over_of_comp f hf gg hg gs s h)) :
    (γ[T.group, T.total]).left ≫ gg =
      actionBaseChange f hf gg hg ≫ (γ[T'.group, T'.total]).left := by
  refine hom_ext_yoneda fun V p => ?_
  have h₀ : T.group.hom.app (op V)
        (yonedaEquiv (p ≫ pullback.fst T.group.hom T.total.hom)) =
      T.total.hom.app (op V)
        (yonedaEquiv (p ≫ pullback.snd T.group.hom T.total.hom)) := by
    rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, Category.assoc, Category.assoc,
      pullback.condition]
  have hp : p = smulSectionLift T.group T.total
      (yonedaEquiv (p ≫ pullback.fst T.group.hom T.total.hom))
      (yonedaEquiv (p ≫ pullback.snd T.group.hom T.total.hom)) h₀ := by
    apply pullback.hom_ext
    · exact (Equiv.symm_apply_apply yonedaEquiv _).symm.trans
        (smulSectionLift_fst T.group T.total _ _ h₀).symm
    · exact (Equiv.symm_apply_apply yonedaEquiv _).symm.trans
        (smulSectionLift_snd T.group T.total _ _ h₀).symm
  apply yonedaEquiv.injective
  rw [hp]
  refine Eq.trans (congrArg yonedaEquiv (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (yonedaEquiv_comp _ gg) ?_
  refine Eq.trans (hs V _ _ h₀) ?_
  refine Eq.trans ?_ (congrArg yonedaEquiv (Category.assoc _ _ _))
  exact congrArg yonedaEquiv (congrArg (· ≫ (γ[T'.group, T'.total]).left)
    (smulSectionLift_comp_actionBaseChange f hf gg hg _ _ h₀ _).symm)

omit [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat] in
/-- **Cartesianness is a condition on sections.** A morphism of total spaces over a morphism
`f` of the site which is, over every section of the base, a bijection onto the sections lying
over its image makes the square cartesian: the induced morphism to the fibre product is an
isomorphism, which for presheaves of sets is a sectionwise bijection. -/
theorem isPullback_of_bijOn {T T' : TorsorObj hB G} (f : T.U ⟶ T'.U)
    (gg : T.total.left ⟶ T'.total.left)
    (hg : T.total.hom ≫ yoneda.map f = gg ≫ T'.total.hom)
    (hbij : ∀ (V : (BigFppfOver 𝒞 S hS)ᵒᵖ) (a : V.unop ⟶ T.U),
      Set.BijOn (gg.app V) {s : T.total.left.obj V | T.total.hom.app V s = a}
        {s' : T'.total.left.obj V | T'.total.hom.app V s' = a ≫ f}) :
    IsPullback gg T.total.hom T'.total.hom (yoneda.map f) := by
  have hw : gg ≫ T'.total.hom = T.total.hom ≫ yoneda.map f := hg.symm
  have hiso : IsIso (pullback.lift gg T.total.hom hw) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    rw [isIso_iff_bijective]
    have hpb := (IsPullback.of_hasPullback T'.total.hom (yoneda.map f)).map
      ((evaluation (BigFppfOver 𝒞 S hS)ᵒᵖ (Type u)).obj V)
    have hfst : ∀ x : T.total.left.obj V,
        (pullback.fst T'.total.hom (yoneda.map f)).app V
          ((pullback.lift gg T.total.hom hw).app V x) = gg.app V x := fun x =>
      ConcreteCategory.congr_hom
        (NatTrans.congr_app (pullback.lift_fst gg T.total.hom hw) V) x
    have hsnd : ∀ x : T.total.left.obj V,
        (pullback.snd T'.total.hom (yoneda.map f)).app V
          ((pullback.lift gg T.total.hom hw).app V x) = T.total.hom.app V x := fun x =>
      ConcreteCategory.congr_hom
        (NatTrans.congr_app (pullback.lift_snd gg T.total.hom hw) V) x
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have h1 : T.total.hom.app V x = T.total.hom.app V y :=
        ((hsnd x).symm.trans (congrArg _ hxy)).trans (hsnd y)
      have h2 : gg.app V x = gg.app V y :=
        ((hfst x).symm.trans (congrArg _ hxy)).trans (hfst y)
      exact (hbij V (T.total.hom.app V x)).injOn rfl h1.symm h2
    · have hcz : T'.total.hom.app V ((pullback.fst T'.total.hom (yoneda.map f)).app V z) =
          (pullback.snd T'.total.hom (yoneda.map f)).app V z ≫ f :=
        ConcreteCategory.congr_hom (NatTrans.congr_app
          (pullback.condition (f := T'.total.hom) (g := yoneda.map f)) V) z
      obtain ⟨x, hx1, hx2⟩ := (hbij V
        ((pullback.snd T'.total.hom (yoneda.map f)).app V z)).surjOn hcz
      exact ⟨x, Types.ext_of_isPullback hpb ((hfst x).trans hx2) ((hsnd x).trans hx1)⟩
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso (pullback.lift gg T.total.hom hw))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end TorsorObj

/-- **The comparison functor is full when a section of `ℬ` is unique.** A morphism of triples
carries no information about the morphism `b` to `ℬ` of a quadruple, so fullness needs the
section of `ℬ` over an object of the site to be unique — which it is in the situation the last
clause of Stacks 0371 is about, where `ℬ` is `S` itself. Everything else a morphism of
quadruples asks for is read off the morphism of triples: cartesianness from its bijectivity on
fibres, equivariance from its equivariance for the constant sheaf, and compatibility with the
equivariant maps from its own. -/
theorem torsorWithMapToAbstractQuotient_full (D : ConstantGroupData hB G Gabs)
    {ρ : Gabs →* Aut (X.left ⋙ uliftFunctor.{t})} (hρ : IsCompatibleAction D ρ)
    (hbsub : ∀ (U : BigFppfOver 𝒞 S hS) (b b' : yoneda.obj U ⟶ B), b = b') :
    (torsorWithMapToAbstractQuotient D hρ).Full where
  map_surjective {A C} w := by
    have hwb : yoneda.map (AbstractGroupQuotientStack.Hom.base w) ≫ C.toTorsorObj.b =
        A.toTorsorObj.b := hbsub _ _ _
    obtain ⟨gg, hggapp⟩ :
        ∃ gg : A.toTorsorObj.total.left ⟶ C.toTorsorObj.total.left,
          ∀ (V : (BigFppfOver 𝒞 S hS)ᵒᵖ) (s : A.toTorsorObj.total.left.obj V),
            gg.app V s = TorsorObj.totalSectionVal.{t} D C.toTorsorObj
              (AbstractGroupQuotientStack.Hom.map w V
                (TorsorObj.totalSectionOf.{t} D A.toTorsorObj s)) :=
      ⟨{ app V := ↾fun s => TorsorObj.totalSectionVal.{t} D C.toTorsorObj
            (AbstractGroupQuotientStack.Hom.map w V
              (TorsorObj.totalSectionOf.{t} D A.toTorsorObj s))
         naturality := by
           intro V W h
           ext s
           have hq : TorsorObj.totalSectionOf.{t} D A.toTorsorObj
                 (A.toTorsorObj.total.left.map h s) =
               (A.toTorsorObj.toConstantTorsor.{t} D).totalMap h
                 (TorsorObj.totalSectionOf.{t} D A.toTorsorObj s) :=
             TorsorObj.toConstantTorsor_total_ext D A.toTorsorObj _ _ rfl
           change TorsorObj.totalSectionVal.{t} D C.toTorsorObj
             (AbstractGroupQuotientStack.Hom.map w W
               (TorsorObj.totalSectionOf.{t} D A.toTorsorObj
                 (A.toTorsorObj.total.left.map h s))) = _
           rw [hq]
           exact congrArg (TorsorObj.totalSectionVal.{t} D C.toTorsorObj)
             (AbstractGroupQuotientStack.Hom.map_naturality w h _) }, fun _ _ => rfl⟩
    have hgof : ∀ (V : (BigFppfOver 𝒞 S hS)ᵒᵖ)
        (p : (A.toTorsorObj.toConstantTorsor.{t} D).Total V),
        gg.app V (TorsorObj.totalSectionVal.{t} D A.toTorsorObj p) =
          TorsorObj.totalSectionVal.{t} D C.toTorsorObj
            (AbstractGroupQuotientStack.Hom.map w V p) := by
      intro V p
      refine (hggapp V _).trans ?_
      exact congrArg (fun q => TorsorObj.totalSectionVal.{t} D C.toTorsorObj
        (AbstractGroupQuotientStack.Hom.map w V q))
        (TorsorObj.totalSectionOf_totalSectionVal.{t} D A.toTorsorObj p)
    have hbase : ∀ (V : (BigFppfOver 𝒞 S hS)ᵒᵖ) (s : A.toTorsorObj.total.left.obj V),
        C.toTorsorObj.total.hom.app V (gg.app V s) =
          A.toTorsorObj.total.hom.app V s ≫ AbstractGroupQuotientStack.Hom.base w := by
      intro V s
      refine Eq.trans (congrArg (C.toTorsorObj.total.hom.app V) (hggapp V s)) ?_
      refine Eq.trans (TorsorObj.totalSectionVal_over.{t} D C.toTorsorObj _) ?_
      exact AbstractGroupQuotientStack.Hom.fst_map w
        (TorsorObj.totalSectionOf.{t} D A.toTorsorObj s)
    have hg : A.toTorsorObj.total.hom ≫ yoneda.map (AbstractGroupQuotientStack.Hom.base w) =
        gg ≫ C.toTorsorObj.total.hom := by
      ext V s
      exact (hbase V s).symm
    have hbij : ∀ (V : (BigFppfOver 𝒞 S hS)ᵒᵖ) (a : V.unop ⟶ A.toTorsorObj.U),
        Set.BijOn (gg.app V)
          {s : A.toTorsorObj.total.left.obj V |
            A.toTorsorObj.total.hom.app V s = a}
          {s' : C.toTorsorObj.total.left.obj V |
            C.toTorsorObj.total.hom.app V s' =
              a ≫ AbstractGroupQuotientStack.Hom.base w} := by
      intro V a
      refine ⟨?_, ?_, ?_⟩
      · intro s hs
        exact (hbase V s).trans (congrArg (· ≫ AbstractGroupQuotientStack.Hom.base w) hs)
      · intro s hs s' hs' hss
        have h1 : AbstractGroupQuotientStack.Hom.map w V
              (TorsorObj.totalSectionOf.{t} D A.toTorsorObj s) =
            AbstractGroupQuotientStack.Hom.map w V
              (TorsorObj.totalSectionOf.{t} D A.toTorsorObj s') :=
          TorsorObj.toConstantTorsor_total_ext D C.toTorsorObj _ _
            (((hggapp V s).symm.trans hss).trans (hggapp V s'))
        exact congrArg (TorsorObj.totalSectionVal.{t} D A.toTorsorObj)
          ((AbstractGroupQuotientStack.Hom.bijOn_map w V a).injOn hs hs' h1)
      · intro s' hs'
        obtain ⟨p, hp1, hp2⟩ := (AbstractGroupQuotientStack.Hom.bijOn_map w V a).surjOn
          (show TorsorObj.totalSectionOf.{t} D C.toTorsorObj s' ∈
            {q : (C.toTorsorObj.toConstantTorsor.{t} D).Total V |
              q.1 = a ≫ AbstractGroupQuotientStack.Hom.base w} from hs')
        refine ⟨TorsorObj.totalSectionVal.{t} D A.toTorsorObj p, ?_, ?_⟩
        · exact (TorsorObj.totalSectionVal_over.{t} D A.toTorsorObj p).trans hp1
        · exact (hgof V p).trans
            (congrArg (TorsorObj.totalSectionVal.{t} D C.toTorsorObj) hp2)
    have hsmul : ∀ (V : BigFppfOver 𝒞 S hS)
        (gs : A.toTorsorObj.group.left.obj (op V))
        (s : A.toTorsorObj.total.left.obj (op V))
        (h : A.toTorsorObj.group.hom.app (op V) gs =
          A.toTorsorObj.total.hom.app (op V) s),
        gg.app (op V) (smulSection A.toTorsorObj.group A.toTorsorObj.total gs s h) =
          smulSection C.toTorsorObj.group C.toTorsorObj.total
            ((groupBaseChange (T := A.toTorsorObj) (T' := C.toTorsorObj)
              (AbstractGroupQuotientStack.Hom.base w) hwb).app (op V) gs)
            (gg.app (op V) s)
            (TorsorObj.groupBaseChange_over_of_comp (T := A.toTorsorObj)
              (T' := C.toTorsorObj) _ hwb gg hg gs s h) := by
      intro V gs s h
      obtain ⟨gsec, hgsec⟩ :
          ∃ c : (bigConstantGroupSheaf 𝒞 S hS Gabs).presheaf.obj (op V),
            ((D.equiv A.toTorsorObj.U A.toTorsorObj.b).equiv
              (op (Over.mk (A.toTorsorObj.total.hom.app (op V) s)))) c =
              ⟨gs, h⟩ :=
        ⟨_, Equiv.apply_symm_apply _ _⟩
      have hgs1 := congrArg Subtype.val hgsec
      have hL : (A.toTorsorObj.toConstantTorsor.{t} D).totalSmul gsec
            (TorsorObj.totalSectionOf.{t} D A.toTorsorObj s) =
          TorsorObj.totalSectionOf.{t} D A.toTorsorObj
            (smulSection A.toTorsorObj.group A.toTorsorObj.total gs s h) := by
        refine TorsorObj.toConstantTorsor_total_ext D A.toTorsorObj _ _ ?_
        refine Eq.trans (TorsorObj.totalSectionVal_totalSmul.{t} D A.toTorsorObj gsec
          (TorsorObj.totalSectionOf.{t} D A.toTorsorObj s)) ?_
        exact smulSection_congr A.toTorsorObj.group A.toTorsorObj.total hgs1 rfl
      have hR : (((D.equiv C.toTorsorObj.U C.toTorsorObj.b).equiv
            (op (Over.mk (AbstractGroupQuotientStack.Hom.map w (op V)
              (TorsorObj.totalSectionOf.{t} D A.toTorsorObj s)).1))) gsec).1 =
          (groupBaseChange (T := A.toTorsorObj) (T' := C.toTorsorObj)
            (AbstractGroupQuotientStack.Hom.base w) hwb).app (op V) gs := by
        refine Eq.trans (D.equiv_baseChange (b := A.toTorsorObj.b) (b' := C.toTorsorObj.b)
          (AbstractGroupQuotientStack.Hom.base w) hwb
          (Over.mk (A.toTorsorObj.total.hom.app (op V) s)) _
          (AbstractGroupQuotientStack.Hom.fst_map w
            (TorsorObj.totalSectionOf.{t} D A.toTorsorObj s)) gsec) ?_
        exact congrArg
          ((baseChangeGroupHom hB G (AbstractGroupQuotientStack.Hom.base w) hwb).app (op V))
          hgs1
      refine Eq.trans (hggapp (op V) _) ?_
      refine Eq.trans (congrArg (fun q => TorsorObj.totalSectionVal.{t} D C.toTorsorObj
        (AbstractGroupQuotientStack.Hom.map w (op V) q)) hL.symm) ?_
      refine Eq.trans (congrArg (TorsorObj.totalSectionVal.{t} D C.toTorsorObj)
        (AbstractGroupQuotientStack.Hom.map_equivariant w (op V) gsec
          (TorsorObj.totalSectionOf.{t} D A.toTorsorObj s))) ?_
      refine Eq.trans (TorsorObj.totalSectionVal_totalSmul.{t} D C.toTorsorObj gsec
        (AbstractGroupQuotientStack.Hom.map w (op V)
          (TorsorObj.totalSectionOf.{t} D A.toTorsorObj s))) ?_
      exact smulSection_congr C.toTorsorObj.group C.toTorsorObj.total hR
        (hgof (op V) (TorsorObj.totalSectionOf.{t} D A.toTorsorObj s)).symm
    have hpb := TorsorObj.isPullback_of_bijOn (T := A.toTorsorObj) (T' := C.toTorsorObj)
      (AbstractGroupQuotientStack.Hom.base w) gg hg hbij
    have hsc := TorsorObj.smul_comp_of_sections (T := A.toTorsorObj) (T' := C.toTorsorObj)
      (AbstractGroupQuotientStack.Hom.base w) hwb gg hg hsmul
    have hcm : gg ≫ C.map = A.map := by
      ext V s
      refine Eq.trans (congrArg (C.map.app V) (hggapp V s)) ?_
      exact congrArg ULift.down (AbstractGroupQuotientStack.Hom.totalToTarget_comp w V
        (TorsorObj.totalSectionOf.{t} D A.toTorsorObj s))
    refine ⟨(⟨(⟨AbstractGroupQuotientStack.Hom.base w, hwb, gg, hpb, hsc⟩ :
        TorsorObj.Hom A.toTorsorObj C.toTorsorObj), hcm⟩ :
      TorsorWithMap.Hom X A C), ?_⟩
    refine AbstractGroupQuotientStack.Hom.ext rfl ?_
    funext V p
    refine TorsorObj.toConstantTorsor_total_ext D C.toTorsorObj _ _ ?_
    exact hgof V p

/-! ### The data the comparison functor consumes

The comparison functor consumes the identification `AlgebraicGeometry.Space.ConstantGroupData`
of `U ×_{b, ℬ} 𝒢` with the constant sheaf of groups and the compatibility
`AlgebraicGeometry.Space.IsCompatibleAction` of the two actions on `X`. For `𝒢 = G_S` both are
constructed in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientStackConstantData`
(`AlgebraicGeometry.Space.constGSData`, `AlgebraicGeometry.Space.constGS_isCompatibleAction`), and
the comparison functor is shown to be an equivalence over the site in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientStackEquivalence`.

Fullness, `AlgebraicGeometry.Space.torsorWithMapToAbstractQuotient_full`, uses the one hypothesis
a morphism of triples cannot supply: that the section `b` of `ℬ` over an object of the site is
unique, which holds when `ℬ` is `S` itself. -/

variable (hB G) in
/-- **What the comparison functor of the last clause of Stacks 0371 needs of the group.** That
the group algebraic space `𝒢` acting on `X` is, as far as the comparison is concerned, the
constant group algebraic space with value `Gabs` acting through `ρ`: an identification of
`U ×_{b, ℬ} 𝒢` with the constant sheaf of groups compatible with base change, under which the
constant sections act on `X` as `ρ` does.

For `𝒢 = ` `AlgebraicGeometry.Space.constantGroupSpace` it is supplied by
`AlgebraicGeometry.Space.constGSData` and `AlgebraicGeometry.Space.constGS_isCompatibleAction`. -/
abbrev HasAbstractGroupComparison (Gabs : Type w) [Group Gabs]
    [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat.{w}] (X : Over B)
    [ModObj G.obj.X X] (ρ : Gabs →* Aut (X.left ⋙ uliftFunctor.{t})) : Prop :=
  ∃ D : ConstantGroupData hB G Gabs, IsCompatibleAction D ρ

end AlgebraicGeometry.Space

end
