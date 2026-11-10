module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentablePushforward
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineDiagonalPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverSchemeRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheaf
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Adjunction.Comma
import all StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Representable

/-!
# The right adjoint of an affine 1-morphism of algebraic stacks

Let `g : 𝒰 ⟶ 𝒳` be an affine 1-morphism of algebraic stacks over `S` (Stacks 0CHQ). For every
object `x` of `𝒳` lying over a scheme `T`, the base change `𝒰 ×_𝒳 (Sch/T)` is represented by a
scheme `W_x` affine over `T`; so the comma category of `x` under the functor underlying `g` has a
terminal object, and `g` has a right adjoint `r : 𝒳 ⥤ 𝒰`, `x ↦ W_x`, whose counit lies over the
affine morphism `W_x ⟶ T`.  This is Stacks 06W8 for the representable-by-schemes 1-morphism `g`,
at the universes of the 2-category of algebraic stacks (morphisms in `Type u`), where the base's
`AlgebraicGeometry.BigFppfOver.isLeftAdjoint_of_isRepresentableMorphism` (stated for morphisms in
`Type (u + 1)`) does not apply.

The right adjoint is continuous for the fppf topologies (it is the right adjoint of a cocontinuous
functor), so restriction along it is the direct image of sheaves of modules
`g_* : Mod(𝒪_𝒰) ⥤ Mod(𝒪_𝒳)`, `(g_*ℱ)(x) = ℱ(W_x)`, which is right adjoint to the inverse image
`g^*` (objectwise restriction along `g`, Stacks 06WE).

## Main results

* `AlgebraicGeometry.Stack.exists_iso_yoneda_of_isAffineHom_algebraicSpaceMap`: an algebraic space
  over `T` affine over `T` is representable on the big fppf site of `T`.
* `AlgebraicGeometry.Stack.exists_isTerminal_twoFibreProductOver_of_isAffineHom`: the 2-fibre
  product of an affine 1-morphism with a scheme-valued point has a terminal object.
* `AlgebraicGeometry.BigFppfOver.exists_isTerminal_costructuredArrow_of_isAffineHom`: the comma
  categories of an affine 1-morphism have terminal objects lying over affine morphisms.
* `AlgebraicGeometry.Stack.affineRightAdjoint`, `AlgebraicGeometry.Stack.affineAdjunction`: the
  right adjoint `r` and the adjunction `g ⊣ r`.
* `AlgebraicGeometry.Stack.affinePushforward`: the direct image `g_*` of sheaves of modules, and
  `AlgebraicGeometry.Stack.affinePullbackPushforwardAdjunction`: `g^* ⊣ g_*`.

## References

* [Stacks Project, Tag 06W8](https://stacks.math.columbia.edu/tag/06W8)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 0CHQ](https://stacks.math.columbia.edu/tag/0CHQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The fibre of `yoneda.map P` over the tautological section, read on the big fppf site of `T`,
is the presheaf represented by `P` there. -/
noncomputable def fiberYonedaMapIso (T : BigFppfOver B S hS) {Y : BigFppfOver B S hS}
    (P : Y ⟶ Over.mk T.hom) :
    (smallerBasePresheafEquivalence B T.left.1 S T.left.2 hS T.hom).inverse.obj
        (Over.mk (yoneda.map P)) ≅
      yoneda.obj ((Over.iteratedSliceForward (Over.mk T.hom)).obj (Over.mk P)) := by
  refine NatIso.ofComponents (fun V => Equiv.toIso ?_) ?_
  · exact
      { toFun := fun s => Over.homMk s.1.left (congrArg CommaMorphism.left s.2)
        invFun := fun φ => ⟨Over.homMk φ.left (by
            have h := Over.w φ
            have hP := Over.w P
            change φ.left ≫ P.left = V.unop.hom at h
            change P.left ≫ T.hom = Y.hom at hP
            change φ.left ≫ Y.hom = V.unop.hom ≫ T.hom
            rw [← hP]; exact (reassoc_of% h) T.hom), Over.OverMorphism.ext (Over.w φ)⟩
        left_inv := fun s => Subtype.ext (Over.OverMorphism.ext rfl)
        right_inv := fun φ => Over.OverMorphism.ext rfl }
  · intro V V' f
    ext s
    rfl

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An algebraic space over `T` which is affine over `T` when read over `S` is representable on
the big fppf site of `T`**, by an object whose structure morphism is an affine morphism of
schemes. -/
theorem exists_iso_yoneda_of_isAffineHom_algebraicSpaceMap (T : BigFppfOver B S hS)
    (A : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u) (hA : IsAlgebraicSpace B T.left.1 T.left.2 A)
    (haff : Space.IsAffineHom B S hS (algebraicSpaceMap B S hS T
      ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj ⟨A, hA⟩)).hom) :
    ∃ (Y : BigFppfOver B S hS) (P : Y ⟶ Over.mk T.hom),
      Nonempty (A ≅ yoneda.obj ((Over.iteratedSliceForward (Over.mk T.hom)).obj (Over.mk P))) ∧
        _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map P) := by
  obtain ⟨Y, eY, P, hP, hPaff⟩ := Space.exists_representing_over_of_isAffineHom B S hS
    ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj ⟨A, hA⟩).property _ haff
  let E := smallerBasePresheafEquivalence B T.left.1 S T.left.2 hS T.hom
  let i2 : E.functor.obj A ≅ Over.mk (yoneda.map P) := Over.isoMk eY (by
    rw [← hP]; exact eY.hom_inv_id_assoc _)
  exact ⟨Y, P, ⟨E.unitIso.app A ≪≫ E.inverse.mapIso i2 ≪≫ fiberYonedaMapIso B S hS T P⟩, hPaff⟩

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The 2-fibre product of an affine 1-morphism of algebraic stacks with a scheme-valued point
has a terminal object, lying over an affine morphism to the point's scheme.** -/
theorem exists_isTerminal_twoFibreProductOver_of_isAffineHom {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (g : 𝒰 ⟶ 𝒳) (hg : AlgebraicStacks.IsAffineHom B S hS g)
    (T : BigFppfOver B S hS) (G : Over T ⥤ 𝒳.val.val.obj) (hG : G ⋙ 𝒳.val.val.p = Over.forget T) :
    ∃ Q : TwoFibreProductOver (Over.forget T) 𝒰.val.val.p 𝒳.val.val.p G g.hom.hom.toFunctor,
      Nonempty (IsTerminal Q) ∧
        _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map Q.x.hom) := by
  have hy : (Over.iteratedSliceBackward T ⋙ G) ⋙ 𝒳.val.val.p = Over.map T.hom := by
    rw [Functor.assoc, hG]; exact Over.iteratedSliceBackward_forget T
  obtain ⟨A, hA, ⟨e⟩⟩ := hg.1 T _ hy
  obtain ⟨Y, P, ⟨iA⟩, hPaff⟩ :=
    exists_iso_yoneda_of_isAffineHom_algebraicSpaceMap B S hS T A hA (hg.2 T _ hy A hA ⟨e⟩)
  let V0 := (Over.iteratedSliceForward (Over.mk T.hom)).obj (Over.mk P)
  let e' := (e.trans (PresheafOfCategories.equivalenceOverOfIso iA)).trans
    (PresheafOfCategories.sliceElementsEquivalenceOver V0).symm
  let Q0 := e'.toEquivalence.inverse.obj (Over.mk (𝟙 V0))
  have hQ0 : IsTerminal Q0 := IsTerminal.isTerminalObj _ _ Over.mkIdTerminal
  have hx0 : Q0.x = V0 := Functor.congr_obj e'.inv.w (Over.mk (𝟙 V0))
  have hΦ := TwoFibreProductOver.isEquivalence_precomposeFst (Over.map T.hom) (Over.forget T)
    𝒰.val.val.p 𝒳.val.val.p G g.hom.hom.toFunctor (Over.iteratedSliceBackward T) rfl
    𝒰.val.isFiberedInGroupoids (Functor.IsFiberedInGroupoids.over_map T.hom)
    (Functor.IsFiberedInGroupoids.over_forget T)
    (Over.iteratedSliceEquiv T).isEquivalence_inverse hG
  refine ⟨(TwoFibreProductOver.precomposeFst (Over.map T.hom) (Over.forget T)
    𝒰.val.val.p 𝒳.val.val.p G g.hom.hom.toFunctor (Over.iteratedSliceBackward T) rfl).obj Q0,
    ⟨IsTerminal.isTerminalObj _ _ hQ0⟩, ?_⟩
  have key : ∀ (Z : Over T.left) (_ : Z = V0), _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map ((Over.iteratedSliceBackward T).obj Z).hom) := by
    rintro _ rfl; exact hPaff
  exact key _ hx0

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.BigFppfOver
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

open Functor.ChoiceOfPullbacks in
/-- **An affine 1-morphism of algebraic stacks has, at every object of its target, a terminal
costructured arrow, and that arrow lies over an affine morphism of schemes.** -/
theorem exists_isTerminal_costructuredArrow_of_isAffineHom
    {𝒰 𝒳 : Stack.AlgebraicStacks.{u, w} B S hS} (g : 𝒰 ⟶ 𝒳)
    (hg : Stack.AlgebraicStacks.IsAffineHom B S hS g) (x : 𝒳.val.val.obj) :
    ∃ c : CostructuredArrow g.hom.hom.toFunctor x, Nonempty (IsTerminal c) ∧
      _root_.AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map c.hom)) := by
  have h𝒳 := 𝒳.val.isFiberedInGroupoids
  have hF : g.hom.hom.toFunctor ⋙ 𝒳.val.val.p = 𝒰.val.val.p := g.hom.hom.w
  obtain ⟨G, hG, ξ, -⟩ := Stacks.RepresentableMorphism.ClassifyingFunctor.exists_classifying_functor
    𝒳.val.val.p h𝒳 (𝒳.val.val.p.obj x) x rfl
  obtain ⟨Q, ⟨hQ⟩, hQaff⟩ :=
    Stack.exists_isTerminal_twoFibreProductOver_of_isAffineHom B S hS g hg _ G hG
  refine ⟨CostructuredArrow.mk (pairMorphism Q ≫ ξ.hom), ⟨?_⟩, ?_⟩
  · refine IsTerminal.ofUniqueHom (fun c => CostructuredArrow.homMk
      (hQ.from (pairOfMorphism hF hG h𝒳 c.left (c.hom ≫ ξ.inv))).b ?_) ?_
    · change g.hom.hom.toFunctor.map _ ≫ pairMorphism Q ≫ ξ.hom = c.hom
      rw [← Category.assoc, pairMorphism_naturality, pairMorphism_pairOfMorphism, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
    · intro c m
      have hw : g.hom.hom.toFunctor.map m.left ≫ pairMorphism Q ≫ ξ.hom = c.hom :=
        CostructuredArrow.w m
      have hm : g.hom.hom.toFunctor.map m.left ≫ pairMorphism Q =
          pairMorphism (pairOfMorphism hF hG h𝒳 c.left (c.hom ≫ ξ.inv)) := by
        rw [pairMorphism_pairOfMorphism, ← hw]; simp
      ext
      exact congrArg TwoFibreProductOver.Hom.b
        (hQ.hom_ext (homOfPairMorphism hF hG h𝒳
          (P := pairOfMorphism hF hG h𝒳 c.left (c.hom ≫ ξ.inv)) (Q := Q) m.left hm) _)
  · have hmap := map_over hG (toTerminal Q.x)
    change _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map
      (𝒳.val.val.p.map ((Q.iso.inv ≫ G.map (toTerminal Q.x)) ≫ ξ.hom)))
    have : _root_.AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B S hS).map (toTerminal Q.x).left) := hQaff
    simp only [hmap, Functor.map_comp]
    infer_instance

end AlgebraicGeometry.BigFppfOver

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Lying over an affine morphism of schemes is invariant under isomorphism of costructured
arrows. -/
theorem isAffineHom_toScheme_map_hom_of_iso {C D : Type*} [Category C] [Category D]
    (P : D ⥤ BigFppfOver B S hS) {G : C ⥤ D} {x : D} {c c' : CostructuredArrow G x}
    (e : c ≅ c')
    (h : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (P.map c'.hom))) :
    _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (P.map c.hom)) := by
  have : IsIso e.hom.left := (CostructuredArrow.proj _ _).map_isIso e.hom
  rw [← CostructuredArrow.w e.hom]
  simp only [Functor.map_comp]
  infer_instance

variable {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒰 ⟶ 𝒳)
  (hg : AlgebraicStacks.IsAffineHom B S hS g)

include hg in
/-- The comma categories of an affine 1-morphism of algebraic stacks have terminal objects. -/
theorem hasTerminal_costructuredArrow_of_isAffineHom (x : 𝒳.val.val.obj) :
    HasTerminal (CostructuredArrow g.hom.hom.toFunctor x) := by
  obtain ⟨c, ⟨hc⟩, -⟩ :=
    BigFppfOver.exists_isTerminal_costructuredArrow_of_isAffineHom B S hS g hg x
  exact hc.hasTerminal

/-- **The right adjoint `r : 𝒳 ⥤ 𝒰` of an affine 1-morphism `g : 𝒰 ⟶ 𝒳`**, `x ↦ 𝒰 ×_𝒳 x`. -/
noncomputable def affineRightAdjoint : 𝒳.val.val.obj ⥤ 𝒰.val.val.obj :=
  letI := fun x => hasTerminal_costructuredArrow_of_isAffineHom g hg x
  rightAdjointOfCostructuredArrowTerminals g.hom.hom.toFunctor

/-- **The adjunction `g ⊣ r`** of an affine 1-morphism with its right adjoint. -/
noncomputable def affineAdjunction : g.hom.hom.toFunctor ⊣ affineRightAdjoint g hg :=
  letI := fun x => hasTerminal_costructuredArrow_of_isAffineHom g hg x
  adjunctionOfCostructuredArrowTerminals g.hom.hom.toFunctor

/-- **The counit of `g ⊣ r` lies over an affine morphism of schemes**: at `x` over `T` it lies over
the projection `𝒰 ×_𝒳 x ⟶ T`. -/
theorem isAffineHom_map_affineAdjunction_counit (x : 𝒳.val.val.obj) :
    _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map
      (𝒳.val.val.p.map ((affineAdjunction g hg).counit.app x))) := by
  obtain ⟨c, ⟨hc⟩, hcaff⟩ :=
    BigFppfOver.exists_isTerminal_costructuredArrow_of_isAffineHom B S hS g hg x
  let := fun x => hasTerminal_costructuredArrow_of_isAffineHom g hg x
  have hcounit : (affineAdjunction g hg).counit.app x =
      (⊤_ (CostructuredArrow g.hom.hom.toFunctor x)).hom := by
    simp [affineAdjunction, adjunctionOfCostructuredArrowTerminals]
    rfl
  rw [hcounit]
  exact isAffineHom_toScheme_map_hom_of_iso 𝒳.val.val.p (terminalIsoIsTerminal hc) hcaff

variable (B S hS) in
/-- The fppf topology of the site associated with an algebraic stack over `S` (Stacks 06TP). -/
abbrev AlgebraicStacks.fppfSiteTopology (𝒴 : AlgebraicStacks.{u, w} B S hS) :
    GrothendieckTopology 𝒴.val.val.obj :=
  BigFppfOver.associatedTopology B S hS 𝒴.val.val.p SiteKind.fppf

variable (B S hS) in
/-- The structure sheaf of rings `𝒪_𝒴` of the fppf site associated with an algebraic stack over
`S` (Stacks 06TV), the coefficient sheaf of `Mod(𝒪_𝒴)` and `QCoh(𝒪_𝒴)`. -/
noncomputable abbrev AlgebraicStacks.fppfStructureRingSheaf (𝒴 : AlgebraicStacks.{u, w} B S hS) :
    Sheaf (AlgebraicStacks.fppfSiteTopology B S hS 𝒴) RingCat.{u} :=
  FibredSite.ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids SiteKind.fppf

local notation "J[" Y "]" => AlgebraicStacks.fppfSiteTopology _ _ _ Y
local notation "𝒪[" Y "]" => AlgebraicStacks.fppfStructureRingSheaf _ _ _ Y

omit hg in
/-- **The functor underlying a 1-morphism of algebraic stacks is continuous and cocontinuous**
for the associated fppf topologies (Stacks 06NW). -/
theorem isContinuous_and_isCocontinuous_homFunctor :
    g.hom.hom.toFunctor.IsContinuous J[𝒰] J[𝒳] ∧ g.hom.hom.toFunctor.IsCocontinuous J[𝒰] J[𝒳] := by
  have : 𝒰.val.val.p.IsFibered := 𝒰.val.isFiberedInGroupoids.isFibered
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have h := 𝒳.val.isFiberedInGroupoids.isFibredOneMorphism g.hom.hom.w
  exact h.isContinuous_and_isCocontinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS .fppf)

omit hg in
/-- The functor underlying a 1-morphism of algebraic stacks is continuous for the associated fppf
topologies. -/
instance isContinuous_homFunctor : g.hom.hom.toFunctor.IsContinuous J[𝒰] J[𝒳] :=
  (isContinuous_and_isCocontinuous_homFunctor g).1

omit hg in
/-- The functor underlying a 1-morphism of algebraic stacks is cocontinuous for the associated
fppf topologies. -/
instance isCocontinuous_hom_fppfSiteTopology : g.hom.hom.toFunctor.IsCocontinuous J[𝒰] J[𝒳] :=
  (isContinuous_and_isCocontinuous_homFunctor g).2

/-- **The right adjoint of an affine 1-morphism is continuous** for the associated fppf topologies,
being the right adjoint of a cocontinuous functor. -/
theorem isContinuous_affineRightAdjoint : (affineRightAdjoint g hg).IsContinuous J[𝒳] J[𝒰] :=
  (affineAdjunction g hg).isContinuous_of_isCocontinuous _ _

variable (B S hS) in
/-- The structure sheaf of commutative rings `𝒪_𝒴` of the fppf site associated with an algebraic
stack over `S` (Stacks 06TV); `AlgebraicStacks.fppfStructureRingSheaf` is its underlying sheaf of
rings. -/
noncomputable abbrev AlgebraicStacks.fppfStructureSheaf (𝒴 : AlgebraicStacks.{u, w} B S hS) :
    Sheaf (AlgebraicStacks.fppfSiteTopology B S hS 𝒴) CommRingCat.{u} :=
  FibredSite.structureSheaf B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids SiteKind.fppf

local notation "𝒪c[" Y "]" => AlgebraicStacks.fppfStructureSheaf _ _ _ Y

omit hg in
/-- The structure presheaf of commutative rings of the source is the restriction of that of the
target. -/
theorem structureSheaf_obj_eq_homFunctor :
    (𝒪c[𝒰]).obj = g.hom.hom.toFunctor.op ⋙ (𝒪c[𝒳]).obj := by
  rw [FibredSite.structureSheaf_obj, FibredSite.structureSheaf_obj, ← g.hom.hom.w]
  rfl

omit hg in
/-- The structure presheaf of rings of the source is the restriction of that of the target. -/
theorem ringStructureSheafCore_obj_eq_homFunctor :
    (𝒪[𝒰]).obj = g.hom.hom.toFunctor.op ⋙ (𝒪[𝒳]).obj :=
  congrArg (fun K => K ⋙ forget₂ CommRingCat RingCat) (structureSheaf_obj_eq_homFunctor g)

omit hg in
/-- The identification of the structure sheaf of the source with the restriction of that of the
target, as a morphism of sheaves of rings: the comorphism of `g`. -/
noncomputable def pullbackRingHom :
    𝒪[𝒰] ⟶ (g.hom.hom.toFunctor.sheafPushforwardContinuous RingCat.{u} J[𝒰] J[𝒳]).obj 𝒪[𝒳] :=
  ⟨eqToHom (ringStructureSheafCore_obj_eq_homFunctor g)⟩

/-- The comorphism of the right adjoint `r`, as a morphism of presheaves of commutative rings:
the map `𝒪_𝒳(x) ⟶ 𝒪_𝒰(r x) = 𝒪_𝒳(g (r x))` given by restriction along the counit. -/
noncomputable def pushforwardCommRingHom :
    (𝒪c[𝒳]).obj ⟶ (affineRightAdjoint g hg).op ⋙ (𝒪c[𝒰]).obj :=
  Functor.whiskerRight (NatTrans.op (affineAdjunction g hg).counit) (𝒪c[𝒳]).obj ≫
    eqToHom (congrArg (fun F => (affineRightAdjoint g hg).op ⋙ F)
      (structureSheaf_obj_eq_homFunctor g)).symm

/-- The comorphism of the right adjoint `r`: the map `𝒪_𝒳(x) ⟶ 𝒪_𝒰(r x) = 𝒪_𝒳(g (r x))` given by
restriction along the counit. -/
noncomputable def pushforwardRingHom :
    letI := isContinuous_affineRightAdjoint g hg
    𝒪[𝒳] ⟶ ((affineRightAdjoint g hg).sheafPushforwardContinuous RingCat.{u} J[𝒳] J[𝒰]).obj 𝒪[𝒰] :=
  ⟨Functor.whiskerRight (pushforwardCommRingHom g hg) (forget₂ CommRingCat RingCat)⟩

universe v

omit hg in
/-- The two compatibilities between an adjunction `F ⊣ G` and the scalar identifications it
induces, when the presheaf of commutative rings on the source is the restriction of the one on
the target. -/
theorem whiskerRight_counit_eq_of_eq {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {RC : Cᵒᵖ ⥤ CommRingCat.{u}} {RD : Dᵒᵖ ⥤ CommRingCat.{u}}
    (h : RC = F.op ⋙ RD) :
    Functor.whiskerRight (NatTrans.op adj.counit) (RD ⋙ forget₂ CommRingCat RingCat) =
      Functor.whiskerRight (Functor.whiskerRight (NatTrans.op adj.counit) RD ≫
        eqToHom (congrArg (fun K => G.op ⋙ K) h).symm) (forget₂ CommRingCat RingCat) ≫
        G.op.whiskerLeft (eqToHom (congrArg (fun K => K ⋙ forget₂ CommRingCat RingCat) h)) ∧
    eqToHom (congrArg (fun K => K ⋙ forget₂ CommRingCat RingCat) h) ≫
      F.op.whiskerLeft (Functor.whiskerRight (Functor.whiskerRight (NatTrans.op adj.counit) RD ≫
        eqToHom (congrArg (fun K => G.op ⋙ K) h).symm) (forget₂ CommRingCat RingCat)) ≫
      Functor.whiskerRight (NatTrans.op adj.unit) (RC ⋙ forget₂ CommRingCat RingCat) =
        𝟙 (RC ⋙ forget₂ CommRingCat RingCat) := by
  subst h
  refine ⟨by ext; simp, ?_⟩
  ext X : 2
  simp only [NatTrans.comp_app, eqToHom_refl, NatTrans.id_app, Category.id_comp,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.op_app, Category.comp_id,
    Functor.comp_map, Functor.op_map]
  rw [← Functor.map_comp, ← RD.map_comp, ← op_comp]
  refine (congrArg (fun k => (forget₂ CommRingCat RingCat).map (RD.map k.op))
    (adj.left_triangle_components X.unop)).trans ?_
  rw [op_id, RD.map_id]
  exact CategoryTheory.Functor.map_id _ _

omit hg in
/-- **The inverse image `g^*` of sheaves of modules along a 1-morphism of algebraic stacks**
(Stacks 06WE): objectwise restriction along the functor underlying `g`, the scalars being
identified by `AlgebraicGeometry.Stack.pullbackRingHom`. -/
noncomputable def stackModulePullback : SheafOfModules.{v} 𝒪[𝒳] ⥤ SheafOfModules.{v} 𝒪[𝒰] :=
  SheafOfModules.pushforward (pullbackRingHom g)

/-- **The direct image `g_*` of sheaves of modules along an affine 1-morphism of algebraic
stacks** (Stacks 06WE): `(g_*ℱ)(x) = ℱ(r x)`, restriction along the right adjoint `r` of `g`,
with the scalars of `x` acting through the counit `g (r x) ⟶ x`. -/
noncomputable def affinePushforward : SheafOfModules.{v} 𝒪[𝒰] ⥤ SheafOfModules.{v} 𝒪[𝒳] :=
  letI := isContinuous_affineRightAdjoint g hg
  SheafOfModules.pushforward (pushforwardRingHom g hg)

/-- **The adjunction `g^* ⊣ g_*` for an affine 1-morphism** (Stacks 06WE).  The adjunction
`g ⊣ r` on the sites induces the adjunction between the two restrictions of sheaves of modules. -/
noncomputable def affinePullbackPushforwardAdjunction :
    stackModulePullback.{u, w, v} g ⊣ affinePushforward.{u, w, v} g hg := by
  letI := isContinuous_affineRightAdjoint g hg
  refine SheafOfModules.pushforwardPushforwardAdj (affineAdjunction g hg) (pullbackRingHom g)
    (pushforwardRingHom g hg) ?_ ?_
  · exact (whiskerRight_counit_eq_of_eq (affineAdjunction g hg)
      (structureSheaf_obj_eq_homFunctor g)).1
  · exact (whiskerRight_counit_eq_of_eq (affineAdjunction g hg)
      (structureSheaf_obj_eq_homFunctor g)).2

end AlgebraicGeometry.Stack
