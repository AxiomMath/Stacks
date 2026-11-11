module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackTrivialActionClass
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackTrivialActionRigidification
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackTorsorComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TrivialTorsorUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.PresentingDescentData
public import StacksFrontier.CategoryTheory.Sites.Descent.OfRefinement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.CechClassTorsion

/-!
# The class of an object of `[S/G]` presented by a Čech cocycle

Let `G` be a commutative group algebraic space over a scheme `S` of a big fppf site and let `x`
be an object of the classifying stack `[S/G]` over `T`. Suppose that the canonical descent datum
of `x` relative to an fppf covering `𝒰 = {U_i ⟶ T}` is identified with the image of a descent
datum of the presentation (Stacks 044X) built from a Čech cocycle `c` with values in the points
of `G` (`CategoryTheory.Functor.Rigidification.descentDatumOfCocycle`). This file proves that if
the class of `x` in `H¹(T, G)` (`AlgebraicGeometry.Space.quotientStackTrivialActionClass`,
through Stacks 04WM and 03AJ) has finite order, then `c` is torsion.

The proof follows the source. The torsor of `x` under Stacks 04WM receives, over each `U_i`, a
morphism from the trivial torsor, through the comparison `F_p` of the pointwise presentation;
the image of the unit section is a section `s_i` of the torsor over `U_i`
(`AlgebraicGeometry.Space.memberPt`). On an overlap the two sections differ by the inverse of
`c` (`AlgebraicGeometry.Space.memberPt_relation`): this is the description of `F_p` on arrows as
right translation by the inverse of their `G`-component
(`AlgebraicGeometry.Space.actionPointwiseComparison_map_g_trivialUnitPt`), read through the
compatibility of the gluing arrows with the identification of descent data
(`AlgebraicGeometry.Space.toQuotientStack_map_descentDatum_hom`). Stacks 0A6G then turns finite
order of the class into torsion of the transition cocycle of the `s_i`
(`Stacks.Cohomology.Torsors.exists_nsmul_torsorDifference_eq_of_isOfFinAddOrder`).

## Main definitions

* `AlgebraicGeometry.Space.TorsorObj.actOn` and `AlgebraicGeometry.Space.TorsorObj.act`: the
  action of a section of `G` on a point of the total space of an fppf `G`-torsor.
* `AlgebraicGeometry.Space.TorsorObj.trivialCoord`: the `G`-coordinate of a point of the
  trivial torsor.
* `AlgebraicGeometry.Space.memberTorsorHom` and `AlgebraicGeometry.Space.memberPt`: the morphism
  from the trivial torsor over `U_i` to the torsor of `x`, and the section of the torsor of `x`
  over `U_i` it gives.

## Main results

* `AlgebraicGeometry.Space.memberPt_relation`: the sections over two members differ by the
  inverse of the cocycle on their overlap.
* `AlgebraicGeometry.Space.isTorsionClass_of_isOfFinAddOrder_quotientStackTrivialActionClass`:
  the class of `x` has finite order only if `c` is torsion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory CategoryTheory.MonObj

universe w' w u

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {G : GroupAlgebraicSpace 𝒞 S hS (baseS 𝒞 S hS) (isAlgebraicSpace_baseS 𝒞 S hS)}
  [G.IsCommutative]

namespace TorsorObj

/-! ### The action on the points of the total space of a torsor -/

/-- The action of a section `h` of `G` over `V` on a point `y` of the total space of an fppf
`G`-torsor over `V`, lying over `w : V ⟶ U`: the action of the torsor of sections over the test
object `(V, w)` of `(Sch/U)_fppf`. -/
def actOn (T : TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G) {V : BigFppfOver 𝒞 S hS}
    (w : V ⟶ T.U) (h : G.Sections V) (y : T.total.left.obj (op V))
    (hy : T.total.hom.app (op V) y = w) : T.total.left.obj (op V) :=
  (T.abelianTorsor.1.act (op (Over.mk w)) (Multiplicative.ofAdd (Additive.ofMul h)) ⟨y, hy⟩).1

variable (T : TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G) {V : BigFppfOver 𝒞 S hS}

lemma actOn_over (w : V ⟶ T.U) (h : G.Sections V) (y : T.total.left.obj (op V))
    (hy : T.total.hom.app (op V) y = w) : T.total.hom.app (op V) (T.actOn w h y hy) = w :=
  (T.abelianTorsor.1.act (op (Over.mk w)) (Multiplicative.ofAdd (Additive.ofMul h)) ⟨y, hy⟩).2

lemma actOn_congr {w w' : V ⟶ T.U} (hw : w = w') (h : G.Sections V) (y : T.total.left.obj (op V))
    (hy : T.total.hom.app (op V) y = w) (hy' : T.total.hom.app (op V) y = w') :
    T.actOn w h y hy = T.actOn w' h y hy' := by
  subst hw
  rfl

lemma actOn_one (w : V ⟶ T.U) (y : T.total.left.obj (op V))
    (hy : T.total.hom.app (op V) y = w) : T.actOn w 1 y hy = y :=
  congrArg Subtype.val (T.abelianTorsor.1.one_act (op (Over.mk w)) ⟨y, hy⟩)

lemma actOn_actOn (w : V ⟶ T.U) (h h' : G.Sections V) (y : T.total.left.obj (op V))
    (hy : T.total.hom.app (op V) y = w) :
    T.actOn w h (T.actOn w h' y hy) (T.actOn_over w h' y hy) = T.actOn w (h * h') y hy :=
  (congrArg Subtype.val (T.abelianTorsor.1.mul_act (op (Over.mk w))
    (Multiplicative.ofAdd (Additive.ofMul h)) (Multiplicative.ofAdd (Additive.ofMul h'))
    ⟨y, hy⟩)).symm

/-- The action on points commutes with restriction along a morphism of the site. -/
lemma map_actOn {V' : BigFppfOver 𝒞 S hS} (g : V' ⟶ V) (w : V ⟶ T.U) (h : G.Sections V)
    (y : T.total.left.obj (op V)) (hy : T.total.hom.app (op V) y = w) :
    T.total.left.map g.op (T.actOn w h y hy) =
      T.actOn (g ≫ w) (G.obj.X.left.map g.op h) (T.total.left.map g.op y) (by
        rw [NatTrans.naturality_apply T.total.hom g.op y, hy]
        rfl) :=
  congrArg Subtype.val (T.abelianTorsor.1.naturality
    (Over.homMk g rfl : (Over.mk (g ≫ w) : Over T.U) ⟶ Over.mk w).op
    (Multiplicative.ofAdd (Additive.ofMul h)) ⟨y, hy⟩)

/-- A morphism of fppf `G`-torsors carries the action on points to the action on points. -/
lemma Hom.g_actOn {T T' : TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G} (m : T ⟶ T')
    (w : V ⟶ T.U) (h : G.Sections V) (y : T.total.left.obj (op V))
    (hy : T.total.hom.app (op V) y = w) :
    m.g.app (op V) (T.actOn w h y hy) =
      T'.actOn (w ≫ m.f) h (m.g.app (op V) y)
        ((Hom.sliceSectionsMap m).app (op (Over.mk w)) ⟨y, hy⟩).2 :=
  congrArg Subtype.val (Hom.sliceSectionsMap_act m (op (Over.mk w))
    (Additive.ofMul h) ⟨y, hy⟩)

/-- The action of a section `h` of `G` over `V` on a point `y` of the total space over `V`, as a
point lying over `w : V ⟶ U`; it is `TorsorObj.actOn` when `y` lies over `w`, and `y` otherwise.
Stating it without the proof that `y` lies over `w` lets it be rewritten freely. -/
def act (T : TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G) {V : BigFppfOver 𝒞 S hS}
    (w : V ⟶ T.U) (h : G.Sections V) (y : T.total.left.obj (op V)) : T.total.left.obj (op V) :=
  open Classical in
  if hy : T.total.hom.app (op V) y = w then T.actOn w h y hy else y

lemma act_congr {w w' : V ⟶ T.U} {h h' : G.Sections V} {y y' : T.total.left.obj (op V)}
    (hw : w = w') (hh : h = h') (hy : y = y') : T.act w h y = T.act w' h' y' := by
  subst hw hh hy
  rfl

lemma act_eq {w : V ⟶ T.U} (h : G.Sections V) {y : T.total.left.obj (op V)}
    (hy : T.total.hom.app (op V) y = w) : T.act w h y = T.actOn w h y hy := by
  simp only [act, hy, ↓reduceDIte]

lemma act_over {w : V ⟶ T.U} (h : G.Sections V) {y : T.total.left.obj (op V)}
    (hy : T.total.hom.app (op V) y = w) : T.total.hom.app (op V) (T.act w h y) = w := by
  rw [T.act_eq h hy]
  exact T.actOn_over w h y hy

lemma act_one {w : V ⟶ T.U} {y : T.total.left.obj (op V)}
    (hy : T.total.hom.app (op V) y = w) : T.act w 1 y = y := by
  rw [T.act_eq 1 hy]
  exact T.actOn_one w y hy

lemma act_act {w : V ⟶ T.U} (h h' : G.Sections V) {y : T.total.left.obj (op V)}
    (hy : T.total.hom.app (op V) y = w) : T.act w h (T.act w h' y) = T.act w (h * h') y := by
  rw [T.act_eq h' hy, T.act_eq h (T.actOn_over w h' y hy), T.act_eq (h * h') hy]
  exact T.actOn_actOn w h h' y hy

lemma map_act {V' : BigFppfOver 𝒞 S hS} (g : V' ⟶ V) {w : V ⟶ T.U} (h : G.Sections V)
    {y : T.total.left.obj (op V)} (hy : T.total.hom.app (op V) y = w) :
    T.total.left.map g.op (T.act w h y) =
      T.act (g ≫ w) (G.obj.X.left.map g.op h) (T.total.left.map g.op y) := by
  rw [T.act_eq h hy, T.map_actOn g w h y hy]
  exact (T.act_eq _ _).symm

lemma Hom.g_act {T T' : TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G} (m : T ⟶ T')
    {w : V ⟶ T.U} (h : G.Sections V) {y : T.total.left.obj (op V)}
    (hy : T.total.hom.app (op V) y = w) :
    m.g.app (op V) (T.act w h y) = T'.act (w ≫ m.f) h (m.g.app (op V) y) := by
  rw [T.act_eq h hy, Hom.g_actOn m w h y hy]
  exact (T'.act_eq _ _).symm

/-! ### Points of the trivial torsor -/

section Trivial

variable (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ baseS 𝒞 S hS)

/-- The `G`-coordinate of a point of the total space `G_U = U ×_{b, S} G` of the trivial
torsor. -/
def trivialCoord {V : BigFppfOver 𝒞 S hS}
    (y : (trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G U b).total.left.obj (op V)) :
    G.Sections V :=
  (pullback.fst G.obj.X.hom b).app (op V) y

omit [G.IsCommutative] in
lemma trivialCoord_map {V V' : BigFppfOver 𝒞 S hS} (g : V' ⟶ V)
    (y : (trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G U b).total.left.obj (op V)) :
    trivialCoord U b ((trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G U b).total.left.map
      g.op y) = G.obj.X.left.map g.op (trivialCoord U b y) :=
  NatTrans.naturality_apply (pullback.fst G.obj.X.hom b) g.op y

omit [G.IsCommutative] in
/-- A point of the trivial torsor is determined by its coordinate and the point of `U` it lies
over. -/
lemma trivialCoord_injective {V : BigFppfOver 𝒞 S hS}
    {y y' : (trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G U b).total.left.obj (op V)}
    (hb : (trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G U b).total.hom.app (op V) y =
      (trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G U b).total.hom.app (op V) y')
    (hc : trivialCoord U b y = trivialCoord U b y') : y = y' := by
  have key : ∀ z z' : (pullback G.obj.X.hom b).obj (op V),
      (pullback.fst G.obj.X.hom b).app (op V) z = (pullback.fst G.obj.X.hom b).app (op V) z' →
      (pullback.snd G.obj.X.hom b).app (op V) z = (pullback.snd G.obj.X.hom b).app (op V) z' →
        z = z' := by
    intro z z' h1 h2
    apply yonedaEquiv.symm.injective
    apply pullback.hom_ext
    · rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, h1]
    · rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, h2]
  exact key y y' hc hb

/-- The action on the trivial torsor multiplies coordinates. -/
lemma trivialCoord_actOn {V : BigFppfOver 𝒞 S hS} (w : V ⟶ U) (h : G.Sections V)
    (y : (trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G U b).total.left.obj (op V))
    (hy : (trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G U b).total.hom.app (op V) y = w) :
    trivialCoord U b ((trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G U b).actOn w h y hy) =
      h * trivialCoord U b y := by
  let P := (pullbackGroup (isAlgebraicSpace_baseS 𝒞 S hS) G U b).obj.X
  let W : Over U := Over.mk w
  let k : sliceOver W ⟶ P := (sliceSectionEquiv P W).symm ⟨y, hy⟩
  let a : overBaseS (yoneda.obj V) ⟶ G.obj.X := GroupAlgebraicSpace.sectionsMulEquiv G V h
  let : ModObj P P := ModObj.regular P
  have hact : (trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G U b).actOn w h y hy =
      yonedaEquiv (GroupAlgebraicSpace.pointsSliceMulEquiv G U b W a * k).left := by
    change (sliceAction P P W (sliceSectionEquiv P W
      (GroupAlgebraicSpace.pointsSliceMulEquiv G U b W a)) ⟨y, hy⟩).1 = _
    rw [← (sliceSectionEquiv P W).apply_symm_apply ⟨y, hy⟩, sliceAction_apply]
    rfl
  have hk : (GroupAlgebraicSpace.pointsSliceMulEquiv G U b W).symm k =
      GroupAlgebraicSpace.sectionsMulEquiv G V (trivialCoord U b y) := by
    refine Over.OverMorphism.ext ?_
    rw [← GroupAlgebraicSpace.pbLeft_pointsSliceMulEquiv_fst G U b W, MulEquiv.apply_symm_apply]
    change yonedaEquiv.symm y ≫ pullback.fst G.obj.X.hom b =
      yonedaEquiv.symm ((pullback.fst G.obj.X.hom b).app (op V) y)
    exact yonedaEquiv_symm_naturality_right _ _ y
  have hprod : GroupAlgebraicSpace.pointsSliceMulEquiv G U b W a * k =
      GroupAlgebraicSpace.pointsSliceMulEquiv G U b W
        (a * GroupAlgebraicSpace.sectionsMulEquiv G V (trivialCoord U b y)) := by
    rw [map_mul, ← hk, MulEquiv.apply_symm_apply]
  rw [hact, hprod]
  change yonedaEquiv (pbLeft G (GroupAlgebraicSpace.pointsSliceMulEquiv G U b W _) ≫
    pullback.fst G.obj.X.hom b) = _
  rw [GroupAlgebraicSpace.pbLeft_pointsSliceMulEquiv_fst, ← map_mul]
  exact yonedaEquiv.apply_symm_apply _

/-- The unit section of the trivial torsor, as a point of its total space over `U`. -/
def trivialUnitPt :
    (trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G U b).total.left.obj (op U) :=
  yonedaEquiv (η[(pullbackGroup (isAlgebraicSpace_baseS 𝒞 S hS) G U b).obj.X]).left

omit [G.IsCommutative] in
lemma trivialUnitPt_over :
    (trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G U b).total.hom.app (op U)
      (trivialUnitPt U b) = 𝟙 U := by
  change yonedaEquiv ((η[(pullbackGroup (isAlgebraicSpace_baseS 𝒞 S hS) G U b).obj.X]).left ≫
    (pullbackGroup (isAlgebraicSpace_baseS 𝒞 S hS) G U b).obj.X.hom) = 𝟙 U
  rw [Over.w]
  rfl

lemma trivialCoord_trivialUnitPt : trivialCoord U b (trivialUnitPt (G := G) U b) = 1 := by
  change yonedaEquiv ((η[(pullbackGroup (isAlgebraicSpace_baseS 𝒞 S hS) G U b).obj.X]).left ≫
    pullback.fst G.obj.X.hom b) = (1 : G.Sections U)
  rw [pullbackGroup_unit_left_comp_fst]
  apply (GroupAlgebraicSpace.sectionsMulEquiv G U).injective
  rw [map_one]
  refine Over.OverMorphism.ext ?_
  change yonedaEquiv.symm (yonedaEquiv (b ≫ (η[G.obj.X]).left)) =
    (CartesianMonoidalCategory.toUnit (overBaseS (yoneda.obj U)) ≫ η[G.obj.X]).left
  rw [Equiv.symm_apply_apply, Over.comp_left]
  exact congrArg (· ≫ (η[G.obj.X]).left) (baseS_ext _ _)

omit [G.IsCommutative] in
lemma trivialUnitPt_map_over' {V : BigFppfOver 𝒞 S hS} (β : V ⟶ U) :
    (trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G U b).total.hom.app (op V)
      ((trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G U b).total.left.map β.op
        (trivialUnitPt (G := G) U b)) = β :=
  (NatTrans.naturality_apply _ β.op _).trans
    ((congrArg ((yoneda.obj U).map β.op) (trivialUnitPt_over (G := G) U b)).trans
      (Category.comp_id β))

/-- Right translation by a section `g` carries the unit to a point of coordinate `g⁻¹`. -/
lemma trivialCoord_trivialTorsorRightTranslation_trivialUnitPt {U' : BigFppfOver 𝒞 S hS}
    (b' : yoneda.obj U' ⟶ baseS 𝒞 S hS) (f : U ⟶ U') (hb : b = yoneda.map f ≫ b')
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b) :
    trivialCoord U' b' ((trivialTorsorRightTranslation (isAlgebraicSpace_baseS 𝒞 S hS) G b b' f
      hb g hg).app (op U) (trivialUnitPt U b)) = (show G.Sections U from yonedaEquiv g)⁻¹ := by
  change yonedaEquiv ((η[(pullbackGroup (isAlgebraicSpace_baseS 𝒞 S hS) G U b).obj.X]).left ≫
    trivialTorsorRightTranslation (isAlgebraicSpace_baseS 𝒞 S hS) G b b' f hb g hg ≫
      pullback.fst G.obj.X.hom b') = _
  rw [unit_comp_trivialTorsorRightTranslation]
  apply (GroupAlgebraicSpace.sectionsMulEquiv G U).injective
  rw [map_inv]
  refine Over.OverMorphism.ext ?_
  change yonedaEquiv.symm (yonedaEquiv (g ≫ (ι[G.obj.X]).left)) =
    (GroupAlgebraicSpace.sectionsMulEquiv G U (yonedaEquiv g) ≫ ι[G.obj.X]).left
  rw [Equiv.symm_apply_apply, Over.comp_left]
  change _ = yonedaEquiv.symm (yonedaEquiv g) ≫ _
  rw [Equiv.symm_apply_apply]

end Trivial

end TorsorObj

/-! ### The pointwise comparison of Stacks 04WM on the unit section -/

section Pointwise

variable (G)

/-- **The comparison `F_p` of Stacks 04WM on an arrow, read on the unit section.** For an arrow
`φ : A ⟶ A'` of the pointwise presentation of `[S/G]` over `f : T ⟶ T'`, the right translation
`F_p φ` carries the unit section of the trivial torsor over `T` to the inverse of the
`G`-component of `φ` acting on the restriction along `f` of the unit section over `T'`. -/
lemma actionPointwiseComparison_map_g_trivialUnitPt
    {A A' : (actionPointwiseCategory (isAlgebraicSpace_baseS 𝒞 S hS) G
      (𝟙_ (Over (baseS 𝒞 S hS))) (isAlgebraicSpace_baseS 𝒞 S hS)).obj} (φ : A ⟶ A') :
    ((actionPointwiseComparison (isAlgebraicSpace_baseS 𝒞 S hS) G (𝟙_ (Over (baseS 𝒞 S hS)))
        (isAlgebraicSpace_baseS 𝒞 S hS)).map φ).toHom.g.app (op A.base)
        (TorsorObj.trivialUnitPt A.base _) =
      (trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G A'.base
        (actionPointwiseValue (isAlgebraicSpace_baseS 𝒞 S hS) G (𝟙_ (Over (baseS 𝒞 S hS)))
          (isAlgebraicSpace_baseS 𝒞 S hS) A' ≫ (𝟙_ (Over (baseS 𝒞 S hS))).hom)).actOn φ.base
        (show G.Sections A.base from yonedaEquiv (actionPointwiseGroupElement
          (isAlgebraicSpace_baseS 𝒞 S hS) G (𝟙_ (Over (baseS 𝒞 S hS)))
          (isAlgebraicSpace_baseS 𝒞 S hS) φ))⁻¹
        ((trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G A'.base
          (actionPointwiseValue (isAlgebraicSpace_baseS 𝒞 S hS) G (𝟙_ (Over (baseS 𝒞 S hS)))
            (isAlgebraicSpace_baseS 𝒞 S hS) A' ≫ (𝟙_ (Over (baseS 𝒞 S hS))).hom)).total.left.map
          φ.base.op (TorsorObj.trivialUnitPt A'.base _))
        ((NatTrans.naturality_apply _ φ.base.op _).trans
          ((congrArg ((yoneda.obj A'.base).map φ.base.op)
            (TorsorObj.trivialUnitPt_over (G := G) A'.base _)).trans
              (Category.comp_id φ.base))) := by
  let Fp := actionPointwiseComparison (isAlgebraicSpace_baseS 𝒞 S hS) G
    (𝟙_ (Over (baseS 𝒞 S hS))) (isAlgebraicSpace_baseS 𝒞 S hS)
  apply TorsorObj.trivialCoord_injective A'.base _
  · have hw := ConcreteCategory.congr_hom (NatTrans.congr_app (Fp.map φ).toHom.isPullback.w
      (op A.base)) (TorsorObj.trivialUnitPt (G := G) A.base _)
    refine hw.trans ((congrArg ((yoneda.map φ.base).app (op A.base))
      (TorsorObj.trivialUnitPt_over (G := G) A.base _)).trans ?_)
    refine (Category.id_comp φ.base).trans ?_
    exact (TorsorObj.actOn_over (trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G A'.base _)
      _ _ _ _).symm
  · refine (TorsorObj.trivialCoord_trivialTorsorRightTranslation_trivialUnitPt (G := G) A.base _ _ _
      (baseS_ext _ _) _ _).trans ?_
    rw [TorsorObj.trivialCoord_actOn, TorsorObj.trivialCoord_map,
      TorsorObj.trivialCoord_trivialUnitPt, ← GroupAlgebraicSpace.sectionsMap_apply, map_one,
      mul_one]

/-- `actionPointwiseComparison_map_g_trivialUnitPt` followed by a morphism of torsors out of the
trivial torsor over the target. -/
lemma actionPointwiseComparison_map_g_trivialUnitPt_comp
    {A A' : (actionPointwiseCategory (isAlgebraicSpace_baseS 𝒞 S hS) G
      (𝟙_ (Over (baseS 𝒞 S hS))) (isAlgebraicSpace_baseS 𝒞 S hS)).obj} (φ : A ⟶ A')
    {T' : TorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G}
    (m : ((actionPointwiseComparison (isAlgebraicSpace_baseS 𝒞 S hS) G (𝟙_ (Over (baseS 𝒞 S hS)))
        (isAlgebraicSpace_baseS 𝒞 S hS)).obj A').toTorsorObj ⟶ T') :
    m.g.app (op A.base) (((actionPointwiseComparison (isAlgebraicSpace_baseS 𝒞 S hS) G
        (𝟙_ (Over (baseS 𝒞 S hS))) (isAlgebraicSpace_baseS 𝒞 S hS)).map φ).toHom.g.app (op A.base)
        (TorsorObj.trivialUnitPt A.base _)) =
      T'.act (φ.base ≫ m.f)
        (show G.Sections A.base from yonedaEquiv (actionPointwiseGroupElement
          (isAlgebraicSpace_baseS 𝒞 S hS) G (𝟙_ (Over (baseS 𝒞 S hS)))
          (isAlgebraicSpace_baseS 𝒞 S hS) φ))⁻¹
        (T'.total.left.map φ.base.op (m.g.app (op A'.base) (TorsorObj.trivialUnitPt A'.base _))) :=
  (congrArg (m.g.app (op A.base)) ((actionPointwiseComparison_map_g_trivialUnitPt G φ).trans
    (TorsorObj.act_eq _ _ _).symm)).trans
    ((TorsorObj.Hom.g_act m _ (TorsorObj.trivialUnitPt_map_over' _ _ _)).trans
      (congrArg _ (NatTrans.naturality_apply m.g φ.base.op _)))

end Pointwise

/-! ### An object presented by a descent datum -/

section Presented

open CategoryTheory.Functor

variable (G)

omit [G.IsCommutative] in
/-- **The gluing arrows of a presenting descent datum, read in the quotient stack.** Let `x` be an
object of `[S/G]` over `T` whose canonical descent datum relative to `𝒰` is identified by `e` with
the image of a descent datum `D` of the presentation (Stacks 044X). Let `ζ_i` be the morphism to
`x` from the image of `D_i`, through `e` and the chosen pullback of `x` to `U_i`. Then for every
pair `a : Y ⟶ U_i`, `b : Y ⟶ U_j` agreeing over `T`, the image of the gluing arrow
`a^* D_i ⟶ b^* D_j`
followed by the chosen lift of `b` and `ζ_j` is the chosen lift of `a` followed by `ζ_i`. -/
lemma toQuotientStack_map_descentDatum_hom {T : BigFppfOver 𝒞 S hS}
    {𝒰 : PreZeroHypercover.{w} T}
    (x : (Stack.quotientStack (baseTrivialActionGroupoid G)).p.Fiber T)
    (D : FamilyDescentDatum (Stack.quotientPrestack (baseTrivialActionGroupoid G)).p 𝒰)
    (e : (toFamilyDescentDatum (Stack.quotientStack (baseTrivialActionGroupoid G)).p 𝒰).obj x ≅
      (Stack.presentingDescentFunctor (baseTrivialActionGroupoid G) 𝒰).obj D)
    {Y : BigFppfOver 𝒞 S hS} {i j : 𝒰.I₀} (a : Y ⟶ 𝒰.X i) (b : Y ⟶ 𝒰.X j)
    (h : a ≫ 𝒰.f i = b ≫ 𝒰.f j) :
    (Stack.toQuotientStack (baseTrivialActionGroupoid G)).map
        (Fiber.fiberInclusion.map
          (show pullbackFiber _ (D.obj i) a ⟶ pullbackFiber _ (D.obj j) b from
            D.hom (a ≫ 𝒰.f i) a b rfl h.symm)) ≫
      (Stack.toQuotientStack (baseTrivialActionGroupoid G)).map
        (IsPreFibered.pullbackMap (D.obj j).2 b) ≫
      Fiber.fiberInclusion.map
        (show _ ⟶ pullbackFiber _ x (𝒰.f j) from e.inv.hom j) ≫
      IsPreFibered.pullbackMap x.2 (𝒰.f j) =
    (Stack.toQuotientStack (baseTrivialActionGroupoid G)).map
        (IsPreFibered.pullbackMap (D.obj i).2 a) ≫
      Fiber.fiberInclusion.map
        (show _ ⟶ pullbackFiber _ x (𝒰.f i) from e.inv.hom i) ≫
      IsPreFibered.pullbackMap x.2 (𝒰.f i) := by
  let r := (Stack.quotientStack (baseTrivialActionGroupoid G)).p
  let hF := Stack.isFibredOneMorphism_toQuotientStack (baseTrivialActionGroupoid G)
  let F := Stack.toQuotientStack (baseTrivialActionGroupoid G)
  let q := a ≫ 𝒰.f i
  have hq : b ≫ 𝒰.f j = q := h.symm
  let zi := (fiberFunctorOfCompEq hF.comp_eq (𝒰.X i)).obj (D.obj i)
  let zj := (fiberFunctorOfCompEq hF.comp_eq (𝒰.X j)).obj (D.obj j)
  let εi : zi ⟶ pullbackFiber r x (𝒰.f i) := e.inv.hom i
  let εj : zj ⟶ pullbackFiber r x (𝒰.f j) := e.inv.hom j
  let Dh : pullbackFiber _ (D.obj i) a ⟶ pullbackFiber _ (D.obj j) b := D.hom q a b rfl hq
  let Ph : pullbackFiber r zi a ⟶ pullbackFiber r zj b :=
    ((Stack.presentingDescentFunctor (baseTrivialActionGroupoid G) 𝒰).obj D).hom q a b rfl hq
  have hPh : Ph = (hF.mapPullbackFiberIso (D.obj i) a).hom ≫
      (fiberFunctorOfCompEq hF.comp_eq Y).map Dh ≫ (hF.mapPullbackFiberIso (D.obj j) b).inv := rfl
  have hcomm : pullbackFiberHom εi a ≫ (pullbackFiberCompIso' x (𝒰.f i) a q rfl).hom ≫
      (pullbackFiberCompIso' x (𝒰.f j) b q hq).inv = Ph ≫ pullbackFiberHom εj b := by
    have h0 := e.inv.comm q a b rfl hq
    rw [pullbackPseudofunctor_map_map r a (e.inv.hom i),
      pullbackPseudofunctor_map_map r b (e.inv.hom j)] at h0
    have hdd : ((toFamilyDescentDatum r 𝒰).obj x).hom q a b rfl hq =
        (pullbackFiberCompIso' x (𝒰.f i) a q rfl).hom ≫
          (pullbackFiberCompIso' x (𝒰.f j) b q hq).inv := by
      change ((IsFibered.pullbackPseudofunctor r).mapComp' (𝒰.f i).op.toLoc a.op.toLoc
          q.op.toLoc _).inv.toNatTrans.app x ≫
        ((IsFibered.pullbackPseudofunctor r).mapComp' (𝒰.f j).op.toLoc b.op.toLoc
          q.op.toLoc _).hom.toNatTrans.app x = _
      rw [pullbackPseudofunctor_mapComp'_inv_app r (𝒰.f i) a q rfl x,
        pullbackPseudofunctor_mapComp'_hom_app r (𝒰.f j) b q hq x]
      rfl
    rw [hdd] at h0
    exact h0
  have H : pullbackFiberHom εi a ≫ (pullbackFiberCompIso' x (𝒰.f i) a q rfl).hom =
      Ph ≫ pullbackFiberHom εj b ≫ (pullbackFiberCompIso' x (𝒰.f j) b q hq).hom := by
    rw [← reassoc_of% hcomm, Iso.inv_hom_id, Category.comp_id]
  have f1 := IsFibredOneMorphism.mapPullbackFiberIso_hom_fac hF (D.obj i) a
  have f2 := IsFibredOneMorphism.mapPullbackFiberIso_inv_fac hF (D.obj j) b
  have f3 := pullbackFiberHom_fac εi a
  have f3' := pullbackFiberHom_fac εj b
  have f4 := pullbackFiberCompIso'_hom_fac x (𝒰.f i) a q rfl
  have f4' := pullbackFiberCompIso'_hom_fac x (𝒰.f j) b q hq
  have H' := congrArg (fun φ => Fiber.fiberInclusion.map φ) H
  simp only [Functor.map_comp, hPh] at H'
  refine (cancel_epi (Fiber.fiberInclusion.map (hF.mapPullbackFiberIso (D.obj i) a).hom)).1 ?_
  dsimp only [Fiber.fiberInclusion, Functor.pullbackFiber, fiberFunctorOfCompEq] at f1 f2 f3 f3'
  dsimp only [Fiber.fiberInclusion, Functor.pullbackFiber, fiberFunctorOfCompEq] at f4 f4' H' ⊢
  rw [reassoc_of% f1, ← reassoc_of% f2, ← reassoc_of% f3', ← f4', ← reassoc_of% f3, ← f4]
  simp only [← Category.assoc] at H' ⊢
  rw [H']

end Presented

/-! ### The local sections of the torsor of a presented object -/

section Points

open CategoryTheory.Functor

variable (G) in
/-- The equivalence of Stacks 04WM between `[S/G]` and the category of fppf `G`-torsors with a
map to `S`. -/
abbrev trivialActionTorsorEquivalence :=
  (quotientStackTorsorEquivalence (isAlgebraicSpace_baseS 𝒞 S hS) G (𝟙_ (Over (baseS 𝒞 S hS)))
    (isAlgebraicSpace_baseS 𝒞 S hS)).1

variable (α : Stack.pointwiseToQuotientStack (baseTrivialActionGroupoid G) ⋙
      (trivialActionTorsorEquivalence G).hom.functor ≅
    actionPointwiseComparison (isAlgebraicSpace_baseS 𝒞 S hS) G (𝟙_ (Over (baseS 𝒞 S hS)))
      (isAlgebraicSpace_baseS 𝒞 S hS))
  {T : BigFppfOver 𝒞 S hS} {𝒰 : PreZeroHypercover.{w} T}
  (x : (Stack.quotientStack (baseTrivialActionGroupoid G)).p.Fiber T)
  (c : FamilyCocycle (GroupAlgebraicSpace.pointsGrpPresheaf G) 𝒰.f)
  (e : (toFamilyDescentDatum (Stack.quotientStack (baseTrivialActionGroupoid G)).p 𝒰).obj x ≅
    (Stack.presentingDescentFunctor (baseTrivialActionGroupoid G) 𝒰).obj
      ((trivialActionRigidification G).descentDatumOfCocycle
        (fun i ↦ trivialActionPoint G (𝒰.X i)) c))

/-- The point of the pointwise presentation of `[S/G]` over a member `U_i` of the covering. -/
abbrev memberPoint (i : 𝒰.I₀) :
    (actionPointwiseCategory (isAlgebraicSpace_baseS 𝒞 S hS) G (𝟙_ (Over (baseS 𝒞 S hS)))
      (isAlgebraicSpace_baseS 𝒞 S hS)).obj :=
  (trivialActionPoint G (𝒰.X i)).1

/-- The structure morphism to `S` of the trivial torsor over `U_i`. -/
abbrev memberBase (i : 𝒰.I₀) : yoneda.obj (𝒰.X i) ⟶ baseS 𝒞 S hS :=
  actionPointwiseValue (isAlgebraicSpace_baseS 𝒞 S hS) G (𝟙_ (Over (baseS 𝒞 S hS)))
    (isAlgebraicSpace_baseS 𝒞 S hS) (memberPoint (G := G) (𝒰 := 𝒰) i) ≫
      (𝟙_ (Over (baseS 𝒞 S hS))).hom

/-- The component over `U_i` of the identification of descent data, as a morphism of the fibre
over `U_i`. -/
def memberFiberHom (i : 𝒰.I₀) :
    (fiberFunctorOfCompEq
        (Stack.isFibredOneMorphism_toQuotientStack (baseTrivialActionGroupoid G)).comp_eq
        (𝒰.X i)).obj (trivialActionPoint G (𝒰.X i)) ⟶
      pullbackFiber (Stack.quotientStack (baseTrivialActionGroupoid G)).p x (𝒰.f i) :=
  e.inv.hom i

/-- The morphism of `[S/G]` from the image of the point over `U_i` to `x`: the component of the
identification of descent data, followed by the chosen pullback of `x` to `U_i`. -/
def memberHom (i : 𝒰.I₀) :
    (Stack.toQuotientStack (baseTrivialActionGroupoid G)).obj (trivialActionPoint G (𝒰.X i)).1 ⟶
      x.1 :=
  (memberFiberHom x c e i).1 ≫ IsPreFibered.pullbackMap x.2 (𝒰.f i)

instance (i : 𝒰.I₀) :
    (Stack.quotientStack (baseTrivialActionGroupoid G)).p.IsHomLift (𝒰.f i) (memberHom x c e i) :=
  @IsHomLift.comp_lift_id_left _ _ _ _ _ _ _ _ _ _ (𝒰.f i) (IsPreFibered.pullbackMap x.2 (𝒰.f i))
    inferInstance (memberFiberHom x c e i).1 (memberFiberHom x c e i).2

/-- The morphism of fppf `G`-torsors from the trivial torsor over `U_i` to the torsor of `x`
(Stacks 04WM), through the comparison `α` of the pointwise presentation. -/
def memberTorsorHom (i : 𝒰.I₀) :
    ((actionPointwiseComparison (isAlgebraicSpace_baseS 𝒞 S hS) G (𝟙_ (Over (baseS 𝒞 S hS)))
        (isAlgebraicSpace_baseS 𝒞 S hS)).obj (memberPoint (G := G) (𝒰 := 𝒰) i)).toTorsorObj ⟶
      (quotientStackToTorsors G).obj x.1 :=
  (TorsorWithMap.forget _ G _).map (α.inv.app (memberPoint (G := G) (𝒰 := 𝒰) i) ≫
    (trivialActionTorsorEquivalence G).hom.functor.map (memberHom x c e i))

omit [G.IsCommutative] in
/-- The torsor of `x` lies over `T`. -/
lemma quotientStackToTorsors_obj_U :
    ((quotientStackToTorsors G).obj x.1).U = T :=
  (Functor.congr_obj (quotientStackToTorsors_comp_torsorProjection G) x.1).trans x.2

omit [G.IsCommutative] in
/-- The morphism of torsors out of the trivial torsor over `U_i` lies over `U_i ⟶ T`. -/
lemma memberTorsorHom_f
    (hα : ∀ A, (TorsorWithMap.projection (isAlgebraicSpace_baseS 𝒞 S hS) G
      (𝟙_ (Over (baseS 𝒞 S hS)))).IsHomLift (𝟙 A.base) (α.hom.app A)) (i : 𝒰.I₀) :
    (memberTorsorHom α x c e i).f = 𝒰.f i ≫ eqToHom (quotientStackToTorsors_obj_U x).symm := by
  have h1 : (TorsorWithMap.projection (isAlgebraicSpace_baseS 𝒞 S hS) G
      (𝟙_ (Over (baseS 𝒞 S hS)))).IsHomLift (𝟙 (𝒰.X i))
        (α.inv.app (memberPoint (G := G) (𝒰 := 𝒰) i)) := by
    have : (TorsorWithMap.projection (isAlgebraicSpace_baseS 𝒞 S hS) G
        (𝟙_ (Over (baseS 𝒞 S hS)))).IsHomLift (𝟙 (𝒰.X i))
          (α.app (memberPoint (G := G) (𝒰 := 𝒰) i)).hom := hα (memberPoint (G := G) (𝒰 := 𝒰) i)
    exact IsHomLift.lift_id_inv _ (𝒰.X i) (α.app (memberPoint (G := G) (𝒰 := 𝒰) i))
  have h2 : (TorsorWithMap.projection (isAlgebraicSpace_baseS 𝒞 S hS) G
      (𝟙_ (Over (baseS 𝒞 S hS)))).IsHomLift (𝒰.f i)
        ((trivialActionTorsorEquivalence G).hom.functor.map (memberHom x c e i)) :=
    isHomLift_map_of_comp_eq (trivialActionTorsorEquivalence G).hom.w (𝒰.f i) _
  have h12 : (TorsorWithMap.projection (isAlgebraicSpace_baseS 𝒞 S hS) G
      (𝟙_ (Over (baseS 𝒞 S hS)))).IsHomLift (𝒰.f i)
        (α.inv.app (memberPoint (G := G) (𝒰 := 𝒰) i) ≫
          (trivialActionTorsorEquivalence G).hom.functor.map (memberHom x c e i)) :=
    @IsHomLift.comp_lift_id_left _ _ _ _ _ _ _ _ _ _ (𝒰.f i)
      ((trivialActionTorsorEquivalence G).hom.functor.map (memberHom x c e i)) h2
      (α.inv.app (memberPoint (G := G) (𝒰 := 𝒰) i)) h1
  have h3 : (torsorProjection (isAlgebraicSpace_baseS 𝒞 S hS) G).IsHomLift (𝒰.f i)
      (memberTorsorHom α x c e i) :=
    isHomLift_map_of_comp_eq (p := TorsorWithMap.projection (isAlgebraicSpace_baseS 𝒞 S hS) G
      (𝟙_ (Over (baseS 𝒞 S hS)))) (G := TorsorWithMap.forget _ G _) rfl (𝒰.f i) _
  have := IsHomLift.fac' (torsorProjection (isAlgebraicSpace_baseS 𝒞 S hS) G) (𝒰.f i)
    (memberTorsorHom α x c e i)
  exact this.trans (Category.id_comp (𝒰.f i ≫ eqToHom (quotientStackToTorsors_obj_U x).symm))

/-- The point over `U_i` of the torsor of `x`: the image of the unit section of the trivial
torsor. -/
def memberPt (i : 𝒰.I₀) :
    ((quotientStackToTorsors G).obj x.1).total.left.obj (op (𝒰.X i)) :=
  (memberTorsorHom α x c e i).g.app (op (𝒰.X i))
    (TorsorObj.trivialUnitPt (G := G) (𝒰.X i) (memberBase (G := G) (𝒰 := 𝒰) i))

omit [G.IsCommutative] in
lemma memberPt_over (i : 𝒰.I₀) :
    ((quotientStackToTorsors G).obj x.1).total.hom.app (op (𝒰.X i)) (memberPt α x c e i) =
      (memberTorsorHom α x c e i).f := by
  have hw := ConcreteCategory.congr_hom (NatTrans.congr_app (memberTorsorHom α x c e i).isPullback.w
    (op (𝒰.X i))) (TorsorObj.trivialUnitPt (G := G) (𝒰.X i) (memberBase (G := G) (𝒰 := 𝒰) i))
  refine hw.trans ?_
  have hu := TorsorObj.trivialUnitPt_over (G := G) (𝒰.X i) (memberBase (G := G) (𝒰 := 𝒰) i)
  change (yoneda.map (memberTorsorHom α x c e i).f).app (op (𝒰.X i))
    ((trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G (𝒰.X i)
      (memberBase (G := G) (𝒰 := 𝒰) i)).total.hom.app (op (𝒰.X i))
        (TorsorObj.trivialUnitPt (G := G) (𝒰.X i) (memberBase (G := G) (𝒰 := 𝒰) i))) = _
  rw [hu]
  exact Category.id_comp (memberTorsorHom α x c e i).f

omit [G.IsCommutative] in
/-- The section of `G` attached to an arrow of the pointwise presentation by the comparison of
04WM is the element of the arrow in the rigidification by the points of `G`. -/
lemma yonedaEquiv_actionPointwiseGroupElement_inv [G.IsCommutative]
    {A A' : (actionPointwiseCategory (isAlgebraicSpace_baseS 𝒞 S hS) G
      (𝟙_ (Over (baseS 𝒞 S hS))) (isAlgebraicSpace_baseS 𝒞 S hS)).obj} (φ : A ⟶ A') :
    (show G.Sections A.base from yonedaEquiv (actionPointwiseGroupElement
        (isAlgebraicSpace_baseS 𝒞 S hS) G (𝟙_ (Over (baseS 𝒞 S hS)))
        (isAlgebraicSpace_baseS 𝒞 S hS) φ))⁻¹ =
      GroupAlgebraicSpace.overBaseSHomEquiv G A.base
        ((trivialActionRigidification G).elt
          ((Stack.quotientPrestackEquivalence (baseTrivialActionGroupoid G)).functor.map φ)) := by
  apply (GroupAlgebraicSpace.sectionsMulEquiv G A.base).injective
  rw [_root_.map_inv]
  refine Eq.trans ?_ (GroupAlgebraicSpace.sectionsMulEquiv_overBaseSHomEquiv G A.base _).symm
  change _ = (trivialActionComponent G
    ((Stack.quotientPrestackEquivalence (baseTrivialActionGroupoid G)).functor.map φ))⁻¹
  congr 1
  exact Over.OverMorphism.ext (yonedaEquiv.symm_apply_apply _)


omit [G.IsCommutative] in
lemma memberPt_map_over {V : BigFppfOver 𝒞 S hS} (i : 𝒰.I₀) (β : V ⟶ 𝒰.X i) :
    ((quotientStackToTorsors G).obj x.1).total.hom.app (op V)
      (((quotientStackToTorsors G).obj x.1).total.left.map β.op (memberPt α x c e i)) =
      β ≫ (memberTorsorHom α x c e i).f :=
  (NatTrans.naturality_apply _ β.op _).trans
    (congrArg ((yoneda.obj _).map β.op) (memberPt_over α x c e i))

omit [G.IsCommutative] in
lemma trivialUnitPt_map_over [G.IsCommutative] {U V : BigFppfOver 𝒞 S hS}
    (b : yoneda.obj U ⟶ baseS 𝒞 S hS) (β : V ⟶ U) :
    (trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G U b).total.hom.app (op V)
      ((trivialTorsorObj (isAlgebraicSpace_baseS 𝒞 S hS) G U b).total.left.map β.op
        (TorsorObj.trivialUnitPt (G := G) U b)) = β :=
  (NatTrans.naturality_apply _ β.op _).trans
    ((congrArg ((yoneda.obj U).map β.op) (TorsorObj.trivialUnitPt_over (G := G) U b)).trans
      (Category.comp_id β))


omit [G.IsCommutative] in
lemma overBaseSHomEquiv_inv_mul_eq [G.IsCommutative] (Y : BigFppfOver 𝒞 S hS)
    (f k l : overBaseS (yoneda.obj Y) ⟶ G.obj.X) :
    (GroupAlgebraicSpace.overBaseSHomEquiv G Y (f * k))⁻¹ *
        GroupAlgebraicSpace.overBaseSHomEquiv G Y l =
      (GroupAlgebraicSpace.overBaseSHomEquiv G Y (l⁻¹ * f * k))⁻¹ := by
  apply (GroupAlgebraicSpace.sectionsMulEquiv G Y).injective
  simp only [_root_.map_mul, _root_.map_inv, GroupAlgebraicSpace.sectionsMulEquiv_overBaseSHomEquiv]
  group

/-- **The points of the torsor of `x` over two members differ by the cocycle.** For
`a : Y ⟶ U_i` and `b : Y ⟶ U_j` agreeing over `T`, the restriction along `b` of the point over
`U_j` is the restriction along `a` of the point over `U_i`, acted on by the inverse of
`c (a, b)`. -/
lemma memberPt_relation
    (hα : ∀ A, (TorsorWithMap.projection (isAlgebraicSpace_baseS 𝒞 S hS) G
      (𝟙_ (Over (baseS 𝒞 S hS)))).IsHomLift (𝟙 A.base) (α.hom.app A))
    {Y : BigFppfOver 𝒞 S hS} {i j : 𝒰.I₀} (a : Y ⟶ 𝒰.X i) (b : Y ⟶ 𝒰.X j)
    (h : a ≫ 𝒰.f i = b ≫ 𝒰.f j) :
    ((quotientStackToTorsors G).obj x.1).total.left.map b.op (memberPt α x c e j) =
      ((quotientStackToTorsors G).obj x.1).act (a ≫ (memberTorsorHom α x c e i).f)
        (GroupAlgebraicSpace.overBaseSHomEquiv G Y (c.val a b))⁻¹
        (((quotientStackToTorsors G).obj x.1).total.left.map a.op (memberPt α x c e i)) := by
  let ρ := trivialActionRigidification G
  let D := ρ.descentDatumOfCocycle (fun i ↦ trivialActionPoint G (𝒰.X i)) c
  let qp := (Stack.quotientPrestack (baseTrivialActionGroupoid G)).p
  let Fp := actionPointwiseComparison (isAlgebraicSpace_baseS 𝒞 S hS) G
    (𝟙_ (Over (baseS 𝒞 S hS))) (isAlgebraicSpace_baseS 𝒞 S hS)
  let q := a ≫ 𝒰.f i
  have hq : b ≫ 𝒰.f j = q := h.symm
  let zA := pullbackFiber qp (D.obj i) a
  let Dh : pullbackFiber qp (D.obj i) a ⟶ pullbackFiber qp (D.obj j) b := D.hom q a b rfl hq
  let B : (actionPointwiseCategory (isAlgebraicSpace_baseS 𝒞 S hS) G
      (𝟙_ (Over (baseS 𝒞 S hS))) (isAlgebraicSpace_baseS 𝒞 S hS)).obj := zA.1
  let ca : B ⟶ memberPoint (G := G) (𝒰 := 𝒰) i := (IsPreFibered.pullbackMap (D.obj i).2 a).down
  let cb : B ⟶ memberPoint (G := G) (𝒰 := 𝒰) j :=
    (Dh.1 ≫ IsPreFibered.pullbackMap (D.obj j).2 b).down
  have key : (Stack.pointwiseToQuotientStack (baseTrivialActionGroupoid G)).map cb ≫
      memberHom x c e j =
      (Stack.pointwiseToQuotientStack (baseTrivialActionGroupoid G)).map ca ≫ memberHom x c e i :=
    ((congrArg (· ≫ memberHom x c e j)
      ((Stack.toQuotientStack (baseTrivialActionGroupoid G)).map_comp Dh.1
        (IsPreFibered.pullbackMap (D.obj j).2 b))).trans (Category.assoc _ _ _)).trans
      (toQuotientStack_map_descentDatum_hom G x D e a b h)
  have key2 : Fp.map cb ≫ α.inv.app (memberPoint (G := G) (𝒰 := 𝒰) j) ≫
      (trivialActionTorsorEquivalence G).hom.functor.map (memberHom x c e j) =
      Fp.map ca ≫ α.inv.app (memberPoint (G := G) (𝒰 := 𝒰) i) ≫
        (trivialActionTorsorEquivalence G).hom.functor.map (memberHom x c e i) := by
    have hk : (trivialActionTorsorEquivalence G).hom.functor.map
          ((Stack.pointwiseToQuotientStack (baseTrivialActionGroupoid G)).map cb) ≫
        (trivialActionTorsorEquivalence G).hom.functor.map (memberHom x c e j) =
        (trivialActionTorsorEquivalence G).hom.functor.map
          ((Stack.pointwiseToQuotientStack (baseTrivialActionGroupoid G)).map ca) ≫
        (trivialActionTorsorEquivalence G).hom.functor.map (memberHom x c e i) :=
      (Functor.map_comp _ _ _).symm.trans
        ((congrArg (trivialActionTorsorEquivalence G).hom.functor.map key).trans
          (Functor.map_comp _ _ _))
    rw [← Category.assoc, α.inv.naturality, ← Category.assoc (Fp.map ca), α.inv.naturality,
      Category.assoc, Category.assoc]
    exact congrArg (α.inv.app B ≫ ·) hk
  -- Evaluate on the unit section of the trivial torsor over the base of `a^* D_i`.
  have key3 := congrArg (fun (m : (actionPointwiseComparison (isAlgebraicSpace_baseS 𝒞 S hS) G
      (𝟙_ (Over (baseS 𝒞 S hS))) (isAlgebraicSpace_baseS 𝒞 S hS)).obj B ⟶
        (trivialActionTorsorEquivalence G).hom.functor.obj x.1) =>
      ((TorsorWithMap.forget _ G _).map m).g.app (op B.base)
    (TorsorObj.trivialUnitPt (G := G) B.base (actionPointwiseValue (isAlgebraicSpace_baseS 𝒞 S hS) G
      (𝟙_ (Over (baseS 𝒞 S hS))) (isAlgebraicSpace_baseS 𝒞 S hS) B ≫
        (𝟙_ (Over (baseS 𝒞 S hS))).hom))) key2
  change (memberTorsorHom α x c e j).g.app (op B.base)
      (((actionPointwiseComparison (isAlgebraicSpace_baseS 𝒞 S hS) G (𝟙_ (Over (baseS 𝒞 S hS)))
        (isAlgebraicSpace_baseS 𝒞 S hS)).map cb).toHom.g.app (op B.base)
          (TorsorObj.trivialUnitPt (G := G) B.base _)) =
    (memberTorsorHom α x c e i).g.app (op B.base)
      (((actionPointwiseComparison (isAlgebraicSpace_baseS 𝒞 S hS) G (𝟙_ (Over (baseS 𝒞 S hS)))
        (isAlgebraicSpace_baseS 𝒞 S hS)).map ca).toHom.g.app (op B.base)
          (TorsorObj.trivialUnitPt (G := G) B.base _)) at key3
  rw [actionPointwiseComparison_map_g_trivialUnitPt_comp G cb,
    actionPointwiseComparison_map_g_trivialUnitPt_comp G ca] at key3
  change ((quotientStackToTorsors G).obj x.1).act _ _
      (((quotientStackToTorsors G).obj x.1).total.left.map cb.base.op (memberPt α x c e j)) =
    ((quotientStackToTorsors G).obj x.1).act _ _
      (((quotientStackToTorsors G).obj x.1).total.left.map ca.base.op (memberPt α x c e i)) at key3
  -- Transport to `Y` along the identification of the base of `a^* D_i` with `Y`.
  have hB := zA.2.symm
  have hca : eqToHom hB ≫ ca.base = a :=
    ((IsHomLift.fac qp a (IsPreFibered.pullbackMap (D.obj i).2 a)).trans
      (congrArg (eqToHom hB ≫ ·) (Category.comp_id ca.base))).symm
  have hcb : eqToHom hB ≫ cb.base = b := by
    have := Dh.2
    exact ((IsHomLift.fac qp (𝟙 Y ≫ b) (Dh.1 ≫ IsPreFibered.pullbackMap (D.obj j).2 b)).trans
      (congrArg (eqToHom hB ≫ ·) (Category.comp_id cb.base))).symm.trans (Category.id_comp b)
  have key4 := (TorsorObj.map_act _ (eqToHom hB) _ (memberPt_map_over α x c e j cb.base)).symm.trans
    ((congrArg (((quotientStackToTorsors G).obj x.1).total.left.map (eqToHom hB).op) key3).trans
      (TorsorObj.map_act _ (eqToHom hB) _ (memberPt_map_over α x c e i ca.base)))
  have hpj : ((quotientStackToTorsors G).obj x.1).total.left.map (eqToHom hB).op
      (((quotientStackToTorsors G).obj x.1).total.left.map cb.base.op (memberPt α x c e j)) =
      ((quotientStackToTorsors G).obj x.1).total.left.map b.op (memberPt α x c e j) :=
    (Functor.map_comp_apply _ cb.base.op (eqToHom hB).op _).symm.trans
      (congrArg (fun g => ((quotientStackToTorsors G).obj x.1).total.left.map g.op
        (memberPt α x c e j)) hcb)
  have hpi : ((quotientStackToTorsors G).obj x.1).total.left.map (eqToHom hB).op
      (((quotientStackToTorsors G).obj x.1).total.left.map ca.base.op (memberPt α x c e i)) =
      ((quotientStackToTorsors G).obj x.1).total.left.map a.op (memberPt α x c e i) :=
    (Functor.map_comp_apply _ ca.base.op (eqToHom hB).op _).symm.trans
      (congrArg (fun g => ((quotientStackToTorsors G).obj x.1).total.left.map g.op
        (memberPt α x c e i)) hca)
  have hwj : eqToHom hB ≫ cb.base ≫ (memberTorsorHom α x c e j).f =
      b ≫ (memberTorsorHom α x c e j).f :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (memberTorsorHom α x c e j).f) hcb)
  have hwi : eqToHom hB ≫ ca.base ≫ (memberTorsorHom α x c e i).f =
      a ≫ (memberTorsorHom α x c e i).f :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (memberTorsorHom α x c e i).f) hca)
  have key5 := (TorsorObj.act_congr _ hwj rfl hpj).symm.trans
    (key4.trans (TorsorObj.act_congr _ hwi rfl hpi))
  -- The two sections, read in the rigidification by the points of `G`.
  have := Dh.2
  have hcomp : qp.IsHomLift b (Dh.1 ≫ IsPreFibered.pullbackMap (D.obj j).2 b) :=
    @IsHomLift.comp_lift_id_left _ _ _ _ _ _ _ _ _ _ b (IsPreFibered.pullbackMap (D.obj j).2 b)
      inferInstance Dh.1 Dh.2
  have hκi : G.obj.X.left.map (eqToHom hB).op
      (show G.Sections B.base from (show G.Sections B.base from yonedaEquiv
        (actionPointwiseGroupElement (isAlgebraicSpace_baseS 𝒞 S hS) G (𝟙_ (Over (baseS 𝒞 S hS)))
        (isAlgebraicSpace_baseS 𝒞 S hS) ca))⁻¹) =
      GroupAlgebraicSpace.overBaseSHomEquiv G Y (ρ.cartElt (D.obj i) a) :=
    (congrArg (G.obj.X.left.map (eqToHom hB).op)
      (yonedaEquiv_actionPointwiseGroupElement_inv ca)).trans
      ((GroupAlgebraicSpace.overBaseSHomEquiv_naturality G (eqToHom hB) _).trans rfl)
  have hκj : G.obj.X.left.map (eqToHom hB).op
      (show G.Sections B.base from (show G.Sections B.base from yonedaEquiv
        (actionPointwiseGroupElement (isAlgebraicSpace_baseS 𝒞 S hS) G (𝟙_ (Over (baseS 𝒞 S hS)))
        (isAlgebraicSpace_baseS 𝒞 S hS) cb))⁻¹) =
      GroupAlgebraicSpace.overBaseSHomEquiv G Y
        (ρ.eltOver b (Dh.1 ≫ IsPreFibered.pullbackMap (D.obj j).2 b)) :=
    (congrArg (G.obj.X.left.map (eqToHom hB).op)
      (yonedaEquiv_actionPointwiseGroupElement_inv cb)).trans
      ((GroupAlgebraicSpace.overBaseSHomEquiv_naturality G (eqToHom hB) _).trans rfl)
  have hel : ρ.eltOver b (Dh.1 ≫ IsPreFibered.pullbackMap (D.obj j).2 b) =
      ρ.fiberElt Dh * ρ.cartElt (D.obj j) b := by
    rw [ρ.eltOver_congr (Category.id_comp b).symm rfl, ρ.eltOver_comp,
      Rigidification.map_op_id_apply (𝒜 := GroupAlgebraicSpace.pointsGrpPresheaf G)]
    rfl
  have key6 := (TorsorObj.act_congr _ rfl (hκj.trans (congrArg _ hel)) rfl).symm.trans
    (key5.trans (TorsorObj.act_congr _ rfl hκi rfl))
  let Tx := (quotientStackToTorsors G).obj x.1
  have hw : b ≫ (memberTorsorHom α x c e j).f = a ≫ (memberTorsorHom α x c e i).f := by
    rw [memberTorsorHom_f α x c e hα, memberTorsorHom_f α x c e hα, ← Category.assoc,
      ← Category.assoc, h]
  have hyj : Tx.total.hom.app (op Y) (Tx.total.left.map b.op (memberPt α x c e j)) =
      a ≫ (memberTorsorHom α x c e i).f :=
    (memberPt_map_over α x c e j b).trans hw
  have hyi := memberPt_map_over α x c e i a
  have key7 := (TorsorObj.act_congr _ hw rfl rfl).symm.trans key6
  have hrep := ρ.isRepresentedBy_descentDatumOfCocycle (fun i ↦ trivialActionPoint G (𝒰.X i)) c
    q a b rfl hq
  have halg :
      (GroupAlgebraicSpace.overBaseSHomEquiv G Y (ρ.fiberElt Dh * ρ.cartElt (D.obj j) b))⁻¹ *
      GroupAlgebraicSpace.overBaseSHomEquiv G Y (ρ.cartElt (D.obj i) a) =
      (GroupAlgebraicSpace.overBaseSHomEquiv G Y (c.val a b))⁻¹ := by
    rw [← hrep]
    exact overBaseSHomEquiv_inv_mul_eq Y _ _ _
  exact (Tx.act_one hyj).symm.trans ((Tx.act_congr rfl (inv_mul_cancel _).symm rfl).trans
    ((Tx.act_act _ _ hyj).symm.trans ((congrArg (Tx.act _ _) key7).trans
      ((Tx.act_act _ _ hyi).trans (Tx.act_congr rfl halg rfl)))))

end Points

/-! ### The class of a presented object is torsion only if its cocycle is -/

section Torsion

open CategoryTheory.Functor Stacks.Cohomology.Torsors

omit [G.IsCommutative] in
/-- A covering family transported along an equality of its target is a covering family. -/
lemma sieve₀_mem_of_eq {T T' : BigFppfOver 𝒞 S hS} (𝒰 : PreZeroHypercover.{w} T) (h : T' = T)
    (h𝒰 : 𝒰.sieve₀ ∈ BigFppfOver.topology 𝒞 S hS T) :
    ({ I₀ := 𝒰.I₀, X := 𝒰.X, f := fun i ↦ 𝒰.f i ≫ eqToHom h.symm } :
      PreZeroHypercover.{w} T').sieve₀ ∈ BigFppfOver.topology 𝒞 S hS T' := by
  subst h
  obtain ⟨I, X, f⟩ := 𝒰
  simpa using h𝒰

omit [G.IsCommutative] in
lemma isOfFinAddOrder_cast_iff [G.IsCommutative]
    [∀ U : BigFppfOver 𝒞 S hS,
      HasSheafify ((BigFppfOver.topology 𝒞 S hS).over U) AddCommGrpCat.{u}]
    [∀ U : BigFppfOver 𝒞 S hS,
      HasExt.{w'} (Sheaf ((BigFppfOver.topology 𝒞 S hS).over U) AddCommGrpCat.{u})]
    {U U' : BigFppfOver 𝒞 S hS} (h : U = U')
    (y : Sheaf.H.{w'} ((GroupAlgebraicSpace.pointsSheaf G).over U) 1) :
    IsOfFinAddOrder (cast (congrArg (fun V ↦ Sheaf.H.{w'}
      ((GroupAlgebraicSpace.pointsSheaf G).over V) 1) h) y) ↔ IsOfFinAddOrder y := by
  subst h
  rfl

omit [G.IsCommutative] in
/-- Restricting a point of `G` and reading it as a section commute. -/
lemma overBaseSHomEquiv_pointsGrpPresheaf_map [G.IsCommutative] {Y V : BigFppfOver 𝒞 S hS}
    (g : Y ⟶ V) (k : overBaseS (yoneda.obj V) ⟶ G.obj.X) :
    GroupAlgebraicSpace.overBaseSHomEquiv G Y
        ((GroupAlgebraicSpace.pointsGrpPresheaf G).map g.op k) =
      G.obj.X.left.map g.op (GroupAlgebraicSpace.overBaseSHomEquiv G V k) :=
  (GroupAlgebraicSpace.overBaseSHomEquiv_naturality G g k).symm


omit [G.IsCommutative] in
/-- Restricting the point of `G` attached to a section is attaching a point to the restricted
section. -/
lemma pointsGrpPresheaf_map_sectionsMulEquiv [G.IsCommutative] {Y V : BigFppfOver 𝒞 S hS}
    (g : Y ⟶ V) (t : G.Sections V) :
    (GroupAlgebraicSpace.pointsGrpPresheaf G).map g.op
        (GroupAlgebraicSpace.sectionsMulEquiv G V t) =
      GroupAlgebraicSpace.sectionsMulEquiv G Y (G.obj.X.left.map g.op t) := by
  refine (GroupAlgebraicSpace.sectionsMulEquiv G Y).symm.injective ?_
  exact (overBaseSHomEquiv_pointsGrpPresheaf_map g _).trans
    ((congrArg (G.obj.X.left.map g.op) ((GroupAlgebraicSpace.sectionsMulEquiv G V).symm_apply_apply
      t)).trans ((GroupAlgebraicSpace.sectionsMulEquiv G Y).symm_apply_apply _).symm)

omit [G.IsCommutative] in
/-- The multiplicative form of a torsion relation in the additive sections of `G`. -/
lemma pow_eq_of_nsmul_ofMul [G.IsCommutative] (Y : BigFppfOver 𝒞 S hS) (n : ℕ)
    (k : overBaseS (yoneda.obj Y) ⟶ G.obj.X) (u v : G.Sections Y)
    (h : n • Additive.ofMul (GroupAlgebraicSpace.overBaseSHomEquiv G Y k)⁻¹ =
      Additive.ofMul v - Additive.ofMul u) :
    k ^ n = GroupAlgebraicSpace.sectionsMulEquiv G Y u *
      (GroupAlgebraicSpace.sectionsMulEquiv G Y v)⁻¹ := by
  have h' := congrArg Additive.toMul h
  rw [toMul_nsmul, toMul_sub, toMul_ofMul, toMul_ofMul, toMul_ofMul] at h'
  apply (GroupAlgebraicSpace.sectionsMulEquiv G Y).symm.injective
  rw [map_pow, _root_.map_mul, _root_.map_inv, MulEquiv.symm_apply_apply,
    MulEquiv.symm_apply_apply, GroupAlgebraicSpace.sectionsMulEquiv_symm_apply]
  rw [inv_pow, inv_eq_iff_eq_inv, div_eq_mul_inv] at h'
  rw [h', mul_inv, inv_inv, mul_comm]

variable [∀ U : BigFppfOver 𝒞 S hS,
    HasSheafify ((BigFppfOver.topology 𝒞 S hS).over U) AddCommGrpCat.{u}]
  [∀ U : BigFppfOver 𝒞 S hS,
    HasExt.{w'} (Sheaf ((BigFppfOver.topology 𝒞 S hS).over U) AddCommGrpCat.{u})]
  [∀ U : BigFppfOver 𝒞 S hS,
    ((BigFppfOver.topology 𝒞 S hS).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The class of an object of `[S/G]` presented by a Čech cocycle has finite order only if the
cocycle is torsion.** Let `x` be an object of `[S/G]` over `T` whose canonical descent datum
relative to a covering `𝒰` of `T` is identified with the image of the descent datum of a Čech
cocycle `c` with values in the points of `G` (Stacks 044X). If the class of `x` in `H¹(T, G)`
(through Stacks 04WM and 03AJ) has finite order, then some nonzero power of `c` is a Čech
coboundary. The torsor of `x` has the images of the unit sections over the `U_i` as local
sections, which differ on overlaps by the inverse of `c`, and Stacks 0A6G identifies the class
with the image of the Čech class under an injective group homomorphism. -/
theorem isTorsionClass_of_isOfFinAddOrder_quotientStackTrivialActionClass {T : BigFppfOver 𝒞 S hS}
    (𝒰 : PreZeroHypercover.{w} T) (h𝒰 : 𝒰.sieve₀ ∈ BigFppfOver.topology 𝒞 S hS T)
    (x : (Stack.quotientStack (baseTrivialActionGroupoid G)).p.Fiber T)
    (c : FamilyCocycle (GroupAlgebraicSpace.pointsGrpPresheaf G) 𝒰.f)
    (e : (toFamilyDescentDatum (Stack.quotientStack (baseTrivialActionGroupoid G)).p 𝒰).obj x ≅
      (Stack.presentingDescentFunctor (baseTrivialActionGroupoid G) 𝒰).obj
        ((trivialActionRigidification G).descentDatumOfCocycle
          (fun i ↦ trivialActionPoint G (𝒰.X i)) c))
    (hx : IsOfFinAddOrder (quotientStackTrivialActionClass.{w'} G x.1)) : c.IsTorsionClass := by
  obtain ⟨α, hα⟩ := (quotientStackTorsorEquivalence (isAlgebraicSpace_baseS 𝒞 S hS) G
    (𝟙_ (Over (baseS 𝒞 S hS))) (isAlgebraicSpace_baseS 𝒞 S hS)).2
  let Tx := (quotientStackToTorsors G).obj x.1
  have hU := quotientStackToTorsors_obj_U x
  let E : PreZeroHypercover.{w} Tx.U :=
    { I₀ := 𝒰.I₀, X := 𝒰.X, f := fun i ↦ 𝒰.f i ≫ eqToHom hU.symm }
  have hE : E.sieve₀ ∈ BigFppfOver.topology 𝒞 S hS Tx.U := sieve₀_mem_of_eq 𝒰 hU h𝒰
  let : HasFiniteProducts (Over Tx.U) :=
    let : HasBinaryProducts (Over Tx.U) := Over.ConstructProducts.over_binaryProduct_of_pullback
    hasFiniteProducts_of_has_binary_and_terminal
  have hf : ∀ i, (memberTorsorHom α x c e i).f = E.f i := memberTorsorHom_f α x c e hα
  let σ : ∀ i, Tx.abelianTorsor.1.presheaf.obj (op (Over.mk (E.f i))) :=
    fun i ↦ ⟨memberPt α x c e i, (memberPt_over α x c e i).trans (hf i)⟩
  have hF : IsOfFinAddOrder (torsorIsoClassesEquivH1.{w'} _
      (Quotient.mk (torsorSetoid _) Tx.abelianTorsor)) :=
    (isOfFinAddOrder_cast_iff
      (Functor.congr_obj (quotientStackToTorsors_comp_torsorProjection G) x.1) _).1 hx
  obtain ⟨n, hn, τ, hτ⟩ := exists_nsmul_torsorDifference_eq_of_isOfFinAddOrder E
    (GroupAlgebraicSpace.pointsSheaf G) hE Tx.abelianTorsor σ hF
  refine ⟨n, hn, fun i ↦ (GroupAlgebraicSpace.sectionsMulEquiv G (𝒰.X i)
    (Additive.toMul (τ i)))⁻¹, ?_⟩
  intro Y i₁ i₂ a b hab
  let W : Over Tx.U := Over.mk (a ≫ E.f i₁)
  let a' : W ⟶ Over.mk (E.f i₁) := Over.homMk a rfl
  let b' : W ⟶ Over.mk (E.f i₂) := Over.homMk b (by
    change b ≫ 𝒰.f i₂ ≫ eqToHom hU.symm = a ≫ 𝒰.f i₁ ≫ eqToHom hU.symm
    rw [← Category.assoc, ← Category.assoc, hab])
  have hrel := memberPt_relation α x c e hα a b hab
  have hdiff : torsorDifference _ Tx.abelianTorsor (op W) (Tx.abelianTorsor.1.presheaf.map b'.op
      (σ i₂)) (Tx.abelianTorsor.1.presheaf.map a'.op (σ i₁)) =
      Additive.ofMul (GroupAlgebraicSpace.overBaseSHomEquiv G Y (c.val a b))⁻¹ := by
    refine torsorDifference_eq_of_act _ _ _ _ _ _ (Subtype.ext ?_)
    refine Eq.trans ?_ hrel.symm
    exact (Tx.act_eq _ ((memberPt_map_over α x c e i₁ a).trans
      (congrArg (a ≫ ·) (hf i₁)))).symm.trans
      (Tx.act_congr (congrArg (a ≫ ·) (hf i₁)).symm rfl rfl)
  have hd := hτ a' b'
  rw [hdiff] at hd
  have h1 : (GroupAlgebraicSpace.pointsGrpPresheaf G).map a.op
      (GroupAlgebraicSpace.sectionsMulEquiv G (𝒰.X i₁) (Additive.toMul (τ i₁)))⁻¹ =
      (GroupAlgebraicSpace.sectionsMulEquiv G Y
        (G.obj.X.left.map a.op (Additive.toMul (τ i₁))))⁻¹ :=
    (_root_.map_inv _ _).trans (congrArg _ (pointsGrpPresheaf_map_sectionsMulEquiv a _))
  have h2 : (GroupAlgebraicSpace.pointsGrpPresheaf G).map b.op
      (GroupAlgebraicSpace.sectionsMulEquiv G (𝒰.X i₂) (Additive.toMul (τ i₂)))⁻¹ =
      (GroupAlgebraicSpace.sectionsMulEquiv G Y
        (G.obj.X.left.map b.op (Additive.toMul (τ i₂))))⁻¹ :=
    (_root_.map_inv _ _).trans (congrArg _ (pointsGrpPresheaf_map_sectionsMulEquiv b _))
  refine (pow_eq_of_nsmul_ofMul Y n (c.val a b) _ _ hd).trans (congrArg₂ (· * ·) ?_ h2.symm)
  rw [h1]
  exact (inv_inv _).symm

end Torsion

end AlgebraicGeometry.Space

end
