module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomPrecomposition
public import StacksFrontier.Topology.Sheaves.Modules.Recovery17.PullbackInternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical comparison map for pullback of internal Hom

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `F`, `G` be `𝒪_Y`-modules, with internal
Homs `SheafHom(F, G)` on `Y` and `SheafHom(f^*F, f^*G)` on `X`. This file constructs the canonical
map `f^* SheafHom(F, G) ⟶ SheafHom(f^*F, f^*G)` and proves Stacks Tag 0C6I: it is an isomorphism
when `f` is flat and `F` is finitely presented.

A section `s` of `SheafHom(F, G)` over an open `V` is a homomorphism `φ : F|_V ⟶ G|_V`. Its pullback
`f^*φ : (f^*F)|_{f⁻¹V} ⟶ (f^*G)|_{f⁻¹V}` is the morphism corresponding to
`φ` followed by the unit `G ⟶ f_* f^* G` under the bijection `overHomEquiv` of morphisms out of
`(f^*F)|_{f⁻¹V}` with morphisms out of `F|_V`. The sections `f^*φ` form a morphism
`SheafHom(F, G) ⟶ f_* SheafHom(f^*F, f^*G)` of `𝒪_Y`-modules, whose adjoint transpose is the
canonical map. On every pulled-back section `η_F(t)` the morphism `f^*φ` takes the value
`η_G(φ(t))`, and these values determine it.

## Main definitions

* `Stacks.SheafHomPullback.overHomEquiv`: morphisms out of `(f^*F)|_{f⁻¹V}` correspond to morphisms
  out of `F|_V`.
* `Stacks.SheafHomPullback.overPullbackHom`: the pullback `f^*φ` of a local homomorphism `φ`.
* `Stacks.SheafHomPullback.pullbackSheafHomMap`: the canonical map
  `f^* SheafHom(F, G) ⟶ SheafHom(f^*F, f^*G)`.
* `Stacks.SheafHomPullback.canonicalPullbackSheafHomComparison`: the canonical map with its
  sectionwise characterization `PullbackSheafHomComparison`.

## Main results

* `Stacks.SheafHomPullback.overPullbackHom_val_app_unit` and
  `Stacks.SheafHomPullback.eq_overPullbackHom`: `f^*φ` sends `η_F(t)` to `η_G(φ(t))`, and it is
  the unique such morphism.
* `Stacks.SheafHomPullback.isIso_pullbackSheafHomMap`: **Stacks Tag 0C6I**, the canonical map is
  an isomorphism when `f` is flat and `F` is finitely presented.

## Implementation notes

The base change step of `overHomEquiv` uses `Stacks.SheafOfModules.pushforwardBaseChangeIso`.
Several definitions here (`unitMk`, `counitX`, `baseChangeW`, `secEqX`, `secEqY`, ...) exist to
fix the spelling of their type. With these spellings the rewriting steps match syntactically;
without them the kernel has to compare differently spelled section modules, which is very slow.

## References

* [Stacks Project, Tag 0C6I](https://stacks.math.columbia.edu/tag/0C6I)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafHomPullback

open RingedSpaceModuleAdjunction

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The pushforward of modules along the morphism of slice sites `(Opens Y)/V ⥤ (Opens X)/f⁻¹V`
induced by `f`. -/
noncomputable abbrev overPushforward (V : Opens Y.carrier) :
    _root_.SheafOfModules.{u} ((structureSheafRing X).over ((opensMap f).obj V)) ⥤
      _root_.SheafOfModules.{u} ((structureSheafRing Y).over V) :=
  _root_.SheafOfModules.pushforward (Stacks.SheafOfModules.overStructureSheafHom f V)

/-- A composite of morphisms of sheaves of modules acts on sections as the composite. -/
theorem comp_val_app_apply {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M₁ M₂ M₃ : _root_.SheafOfModules.{u} R} (a : M₁ ⟶ M₂)
    (b : M₂ ⟶ M₃) (U : Cᵒᵖ) (x : M₁.val.obj U) :
    (a ≫ b).val.app U x = b.val.app U (a.val.app U x) :=
  rfl

variable (V : Opens Y.carrier)

/-- The unit of `Over.forget V ⊣ Over.star V` at `W ⟶ V`, with its target written as
`(Over.star V).obj W`. -/
noncomputable def unitMk {W : Opens Y.carrier} (i : W ⟶ V) : Over.mk i ⟶ (Over.star V).obj W :=
  (Over.forgetAdjStar V).unit.app (Over.mk i)

/-- The image of `unitMk V i` under the functor of slice sites induced by `f`. -/
noncomputable def postUnitMk {W : Opens Y.carrier} (i : W ⟶ V) :
    (Over.post (opensMap f)).obj (Over.mk i) ⟶ (Over.post (opensMap f)).obj ((Over.star V).obj W) :=
  (Over.post (opensMap f)).map (unitMk V i)

/-- The counit of `Over.forget ⊣ Over.star` over `f⁻¹V` at an open `A`. -/
noncomputable def counitX (A : Opens X.carrier) :
    ((Over.star ((opensMap f).obj V)).obj A).left ⟶ A :=
  (Over.forgetAdjStar ((opensMap f).obj V)).counit.app A

/-- The component at `W` of the base change isomorphism of slice sites. -/
noncomputable def baseChangeW (W : Opens Y.carrier) :
    (Over.post (opensMap f)).obj ((Over.star V).obj W) ⟶
      (Over.star ((opensMap f).obj V)).obj ((opensMap f).obj W) :=
  (Stacks.SheafOfModules.siteBaseChangeIso f V).hom.app W

/-- The first half of `overHomEquiv`: the composite of the adjunctions `(-)|_{f⁻¹V} ⊣ j_*` and
`f^* ⊣ f_*`. -/
noncomputable def overHomEquivX (F : _root_.SheafOfModules.{u} (structureSheafRing Y))
    (N : _root_.SheafOfModules.{u} ((structureSheafRing X).over ((opensMap f).obj V))) :
    (((modulePullback f).obj F).over ((opensMap f).obj V) ⟶ N) ≃
      (F ⟶ (modulePushforward f).obj
        ((_root_.SheafOfModules.pushforward
          (_root_.SheafOfModules.pushforwardOver (R := structureSheafRing X)
            ((opensMap f).obj V))).obj N)) :=
  ((_root_.SheafOfModules.overPushforwardOverAdj (R := structureSheafRing X)
      ((opensMap f).obj V)).homEquiv _ N).trans
    ((modulePullbackPushforwardAdjunction f).homEquiv F _)

/-- `overHomEquivX` on sections over an open `W` of `Y`. -/
theorem overHomEquivX_apply_val_app (F : _root_.SheafOfModules.{u} (structureSheafRing Y))
    (N : _root_.SheafOfModules.{u} ((structureSheafRing X).over ((opensMap f).obj V)))
    (ψ : ((modulePullback f).obj F).over ((opensMap f).obj V) ⟶ N)
    (W : Opens Y.carrier) (t : F.val.obj (op W)) :
    (overHomEquivX f V F N ψ).val.app (op W) t =
      ψ.val.app (op ((Over.star ((opensMap f).obj V)).obj ((opensMap f).obj W)))
        (((modulePullback f).obj F).val.map (counitX f V ((opensMap f).obj W)).op
          (((modulePullbackPushforwardAdjunction f).unit.app F).val.app (op W) t)) :=
  rfl

/-- The inverse of the base change isomorphism `pushforwardBaseChangeIso` acts on sections by
restriction along the base change isomorphism of slice sites. -/
theorem pushforwardBaseChangeIso_inv_app_val_app
    (N : _root_.SheafOfModules.{u} ((structureSheafRing X).over ((opensMap f).obj V)))
    (W : Opens Y.carrier) (m) :
    ((Stacks.SheafOfModules.pushforwardBaseChangeIso f V).inv.app N).val.app (op W) m =
      N.val.map ((Stacks.SheafOfModules.siteBaseChangeIso f V).hom.app W).op m := by
  simp only [Stacks.SheafOfModules.pushforwardBaseChangeIso, Iso.trans_inv,
    NatTrans.comp_app, _root_.SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply, _root_.SheafOfModules.pushforwardCongr₂,
    _root_.SheafOfModules.pushforwardComp_inv_app_val_app]
  rfl

/-- The base change identification `f_* j_* N ≅ j_* (f|_V)_* N`. -/
noncomputable def baseChangeIsoApp
    (N : _root_.SheafOfModules.{u} ((structureSheafRing X).over ((opensMap f).obj V))) :
    (modulePushforward f).obj
        ((_root_.SheafOfModules.pushforward
          (_root_.SheafOfModules.pushforwardOver (R := structureSheafRing X)
            ((opensMap f).obj V))).obj N) ≅
      (_root_.SheafOfModules.pushforward
          (_root_.SheafOfModules.pushforwardOver (R := structureSheafRing Y) V)).obj
            ((overPushforward f V).obj N) :=
  ((Stacks.SheafOfModules.pushforwardBaseChangeIso f V).app N).symm

/-- `baseChangeIsoApp` on sections over an open `W` of `Y`. -/
theorem baseChangeIsoApp_hom_val_app
    (N : _root_.SheafOfModules.{u} ((structureSheafRing X).over ((opensMap f).obj V)))
    (W : Opens Y.carrier) (m) :
    (baseChangeIsoApp f V N).hom.val.app (op W) m = N.val.map (baseChangeW f V W).op m :=
  pushforwardBaseChangeIso_inv_app_val_app f V N W m

/-- The base change identification `f_* j_* ≅ j_* (f|_V)_*`, on morphisms out of `F`. -/
noncomputable def overHomEquivBaseChange (F : _root_.SheafOfModules.{u} (structureSheafRing Y))
    (N : _root_.SheafOfModules.{u} ((structureSheafRing X).over ((opensMap f).obj V))) :
    (F ⟶ (modulePushforward f).obj
        ((_root_.SheafOfModules.pushforward
          (_root_.SheafOfModules.pushforwardOver (R := structureSheafRing X)
            ((opensMap f).obj V))).obj N)) ≃
      (F ⟶ (_root_.SheafOfModules.pushforward
          (_root_.SheafOfModules.pushforwardOver (R := structureSheafRing Y) V)).obj
            ((overPushforward f V).obj N)) :=
  (baseChangeIsoApp f V N).homToEquiv

/-- `overHomEquivBaseChange` on sections over an open `W` of `Y`. -/
theorem overHomEquivBaseChange_apply_val_app
    (F : _root_.SheafOfModules.{u} (structureSheafRing Y))
    (N : _root_.SheafOfModules.{u} ((structureSheafRing X).over ((opensMap f).obj V)))
    (g : F ⟶ (modulePushforward f).obj
        ((_root_.SheafOfModules.pushforward
          (_root_.SheafOfModules.pushforwardOver (R := structureSheafRing X)
            ((opensMap f).obj V))).obj N))
    (W : Opens Y.carrier) (t : F.val.obj (op W)) :
    (overHomEquivBaseChange f V F N g).val.app (op W) t =
      N.val.map (baseChangeW f V W).op (g.val.app (op W) t) := by
  rw [overHomEquivBaseChange, Iso.homToEquiv_apply, comp_val_app_apply]
  exact baseChangeIsoApp_hom_val_app f V N W _

/-- The adjunction `(-)|_V ⊣ j_*` on `Y`, on morphisms out of `F`. -/
noncomputable def overHomEquivY (F : _root_.SheafOfModules.{u} (structureSheafRing Y))
    (M : _root_.SheafOfModules.{u} ((structureSheafRing Y).over V)) :
    (F.over V ⟶ M) ≃
      (F ⟶ (_root_.SheafOfModules.pushforward
          (_root_.SheafOfModules.pushforwardOver (R := structureSheafRing Y) V)).obj M) :=
  (_root_.SheafOfModules.overPushforwardOverAdj (R := structureSheafRing Y) V).homEquiv F M

/-- The inverse of `overHomEquivY` on sections over `W ⊆ V`. -/
theorem overHomEquivY_symm_apply_val_app
    (F : _root_.SheafOfModules.{u} (structureSheafRing Y))
    (N : _root_.SheafOfModules.{u} ((structureSheafRing X).over ((opensMap f).obj V)))
    (g : F ⟶ (_root_.SheafOfModules.pushforward
          (_root_.SheafOfModules.pushforwardOver (R := structureSheafRing Y) V)).obj
            ((overPushforward f V).obj N))
    {W : Opens Y.carrier} (i : W ⟶ V) (t : F.val.obj (op W)) :
    ((overHomEquivY V F ((overPushforward f V).obj N)).symm g).val.app (op (Over.mk i)) t =
      N.val.map (postUnitMk f V i).op (g.val.app (op W) t) :=
  rfl

/-- Morphisms out of the restriction of `f^*F` to `f⁻¹V` correspond to morphisms out of the
restriction of `F` to `V`: the composite of the adjunctions `(-)|_{f⁻¹V} ⊣ j_*` and `f^* ⊣ f_*`,
followed by the base change identification `f_* j_* ≅ j_* (f|_V)_*` and the adjunction
`(-)|_V ⊣ j_*` on `Y`. -/
noncomputable def overHomEquiv (F : _root_.SheafOfModules.{u} (structureSheafRing Y))
    (N : _root_.SheafOfModules.{u} ((structureSheafRing X).over ((opensMap f).obj V))) :
    (((modulePullback f).obj F).over ((opensMap f).obj V) ⟶ N) ≃
      (F.over V ⟶ (overPushforward f V).obj N) :=
  (overHomEquivX f V F N).trans
    ((overHomEquivBaseChange f V F N).trans (overHomEquivY V F ((overPushforward f V).obj N)).symm)

/-- The restriction maps of `Q|_U` are those of `Q`. -/
theorem over_val_map_apply {Z : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} Z}
    (Q : _root_.SheafOfModules.{u} R) (U : Opens Z) {A B : (Over U)ᵒᵖ} (g : A ⟶ B)
    (x : Q.val.obj (op A.unop.left)) :
    (Q.over U).val.map g x = Q.val.map g.unop.left.op x :=
  rfl

/-- In a sheaf on a topological space, restricting along `A ⊆ B` and back to `A` is the
identity. -/
theorem val_map_val_map_eq_self {Z : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} Z}
    (Q : _root_.SheafOfModules.{u} R) {A B : Opens Z} (b : op A ⟶ op B) (a : op B ⟶ op A)
    (x : Q.val.obj (op A)) :
    Q.val.map a (Q.val.map b x) = x := by
  rw [← PresheafOfModules.map_comp_apply, Subsingleton.elim (b ≫ a) (𝟙 _),
    PresheafOfModules.map_id]
  rfl

/-- `overHomEquiv` on sections: on a pulled-back section `η_F(t)`, with `t ∈ F(W)` and
`W ⊆ V`, the morphism `ψ` and its image under `overHomEquiv` take the same value. -/
theorem overHomEquiv_apply_val_app (F : _root_.SheafOfModules.{u} (structureSheafRing Y))
    (N : _root_.SheafOfModules.{u} ((structureSheafRing X).over ((opensMap f).obj V)))
    (ψ : ((modulePullback f).obj F).over ((opensMap f).obj V) ⟶ N)
    {W : Opens Y.carrier} (i : W ⟶ V) (t : F.val.obj (op W)) :
    (overHomEquiv f V F N ψ).val.app (op (Over.mk i)) t =
      ψ.val.app (op ((Over.post (opensMap f)).obj (Over.mk i)))
        (((modulePullbackPushforwardAdjunction f).unit.app F).val.app (op W) t) := by
  rw [overHomEquiv, Equiv.trans_apply, Equiv.trans_apply]
  refine (overHomEquivY_symm_apply_val_app f V F N _ i t).trans ?_
  refine (congrArg (N.val.map (postUnitMk f V i).op)
    ((overHomEquivBaseChange_apply_val_app f V F N _ W t).trans
      (congrArg (N.val.map (baseChangeW f V W).op)
        (overHomEquivX_apply_val_app f V F N ψ W t)))).trans ?_
  refine (PresheafOfModules.map_comp_apply N.val (baseChangeW f V W).op (postUnitMk f V i).op
    _).symm.trans ?_
  refine (PresheafOfModules.naturality_apply ψ.val
    ((baseChangeW f V W).op ≫ (postUnitMk f V i).op) _).symm.trans ?_
  refine congrArg _ ?_
  refine (over_val_map_apply ((modulePullback f).obj F) ((opensMap f).obj V) _ _).trans ?_
  exact val_map_val_map_eq_self _ _ _ _

/-- The pullback to `f⁻¹V` of a morphism `φ : F|_V ⟶ G|_V`: the morphism
`(f^*F)|_{f⁻¹V} ⟶ (f^*G)|_{f⁻¹V}` corresponding under `overHomEquiv` to `φ` followed by the
restriction to `V` of the unit `G ⟶ f_* f^* G`. -/
noncomputable def overPullbackHom {F G : _root_.SheafOfModules.{u} (structureSheafRing Y)}
    (φ : F.over V ⟶ G.over V) :
    ((modulePullback f).obj F).over ((opensMap f).obj V) ⟶
      ((modulePullback f).obj G).over ((opensMap f).obj V) :=
  (overHomEquiv f V F _).symm (φ ≫ overHomEquiv f V G _ (𝟙 _))

/-- `overPullbackHom f V φ` corresponds under `overHomEquiv` to `φ` followed by the unit. -/
theorem overHomEquiv_overPullbackHom {F G : _root_.SheafOfModules.{u} (structureSheafRing Y)}
    (φ : F.over V ⟶ G.over V) :
    overHomEquiv f V F _ (overPullbackHom f V φ) = φ ≫ overHomEquiv f V G _ (𝟙 _) :=
  Equiv.apply_symm_apply _ _

/-- The pullback of `φ` sends the pullback `η_F(t)` of a section `t` of `F` to the pullback
`η_G(φ(t))` of its image. -/
theorem overPullbackHom_val_app_unit {F G : _root_.SheafOfModules.{u} (structureSheafRing Y)}
    (φ : F.over V ⟶ G.over V) {W : Opens Y.carrier} (i : W ⟶ V) (t : F.val.obj (op W)) :
    (overPullbackHom f V φ).val.app (op ((Over.post (opensMap f)).obj (Over.mk i)))
        (((modulePullbackPushforwardAdjunction f).unit.app F).val.app (op W) t) =
      ((modulePullbackPushforwardAdjunction f).unit.app G).val.app (op W)
        (φ.val.app (op (Over.mk i)) t) := by
  refine (overHomEquiv_apply_val_app f V F _ (overPullbackHom f V φ) i t).symm.trans ?_
  rw [overHomEquiv_overPullbackHom]
  refine (comp_val_app_apply φ (overHomEquiv f V G _ (𝟙 _)) (op (Over.mk i)) t).trans ?_
  exact (overHomEquiv_apply_val_app f V G _ (𝟙 _) i _).trans rfl

/-- A morphism `(f^*F)|_{f⁻¹V} ⟶ (f^*G)|_{f⁻¹V}` sending each pulled-back section `η_F(t)` to
`η_G(φ(t))` is the pullback of `φ`. -/
theorem eq_overPullbackHom {F G : _root_.SheafOfModules.{u} (structureSheafRing Y)}
    (φ : F.over V ⟶ G.over V)
    (ψ : ((modulePullback f).obj F).over ((opensMap f).obj V) ⟶
      ((modulePullback f).obj G).over ((opensMap f).obj V))
    (h : ∀ (W : Opens Y.carrier) (i : W ⟶ V) (t : F.val.obj (op W)),
      ψ.val.app (op ((Over.post (opensMap f)).obj (Over.mk i)))
          (((modulePullbackPushforwardAdjunction f).unit.app F).val.app (op W) t) =
        ((modulePullbackPushforwardAdjunction f).unit.app G).val.app (op W)
          (φ.val.app (op (Over.mk i)) t)) :
    ψ = overPullbackHom f V φ := by
  apply (overHomEquiv f V F _).injective
  rw [overHomEquiv_overPullbackHom]
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  ext t
  exact (overHomEquiv_apply_val_app f V F _ ψ Z.unop.hom t).trans
    ((h _ Z.unop.hom t).trans ((comp_val_app_apply φ _ (op (Over.mk Z.unop.hom)) t).trans
      ((overHomEquiv_apply_val_app f V G _ (𝟙 _) Z.unop.hom _).trans rfl)).symm)

/-- A sum of morphisms of sheaves of modules acts on sections as the sum. -/
theorem add_val_app_apply {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M₁ M₂ : _root_.SheafOfModules.{u} R} (a b : M₁ ⟶ M₂)
    (U : Cᵒᵖ) (x : M₁.val.obj U) :
    (a + b).val.app U x = a.val.app U x + b.val.app U x :=
  rfl

/-- The pullback of local homomorphisms is additive. -/
theorem overPullbackHom_add {F G : _root_.SheafOfModules.{u} (structureSheafRing Y)}
    (φ₁ φ₂ : F.over V ⟶ G.over V) :
    overPullbackHom f V (φ₁ + φ₂) = overPullbackHom f V φ₁ + overPullbackHom f V φ₂ := by
  refine (eq_overPullbackHom f V _ _ fun W i t => ?_).symm
  refine (add_val_app_apply _ _ _ _).trans ?_
  rw [overPullbackHom_val_app_unit, overPullbackHom_val_app_unit]
  exact (map_add (ConcreteCategory.hom
    (((modulePullbackPushforwardAdjunction f).unit.app G).val.app (op W))) _ _).symm

section Comparison

variable (F G : _root_.SheafOfModules.{u} (structureSheafRing Y))
  (H : SheafHom Y.sheaf F G)
  (H' : SheafHom X.sheaf ((modulePullback f).obj F) ((modulePullback f).obj G))

/-- `H.sectionsEquiv`, with the local homomorphisms read in the category of modules over
`structureSheafRing Y`. -/
noncomputable def secEqY : H.obj.val.obj (op V) ≃+ (F.over V ⟶ G.over V) :=
  H.sectionsEquiv V

/-- `H'.sectionsEquiv`, with the local homomorphisms read in the category of modules over
`structureSheafRing X`. -/
noncomputable def secEqX (U : Opens X.carrier) :
    H'.obj.val.obj (op U) ≃+
      (((modulePullback f).obj F).over U ⟶ ((modulePullback f).obj G).over U) :=
  H'.sectionsEquiv U

/-- The section of `SheafHom(f^*F, f^*G)` over `f⁻¹V` obtained by pulling back the local
homomorphism represented by a section of `SheafHom(F, G)` over `V`. -/
noncomputable def pullbackHomSection (s : H.obj.val.obj (op V)) :
    H'.obj.val.obj (op ((opensMap f).obj V)) :=
  (secEqX f F G H' _).symm (overPullbackHom f V (secEqY V F G H s))

/-- The local homomorphism represented by `pullbackHomSection f V F G H H' s` is the pullback
of the local homomorphism represented by `s`. -/
theorem secEqX_pullbackHomSection (s : H.obj.val.obj (op V)) :
    secEqX f F G H' _ (pullbackHomSection f V F G H H' s) =
      overPullbackHom f V (secEqY V F G H s) :=
  AddEquiv.apply_symm_apply _ _

/-- A section of `SheafHom(f^*F, f^*G)` over `f⁻¹V` whose local homomorphism sends each
`η_F(t)` to `η_G(φ_s(t))` is the pullback of `s`. -/
theorem eq_pullbackHomSection (s : H.obj.val.obj (op V))
    (z : H'.obj.val.obj (op ((opensMap f).obj V)))
    (h : ∀ (W : Opens Y.carrier) (i : W ⟶ V) (t : F.val.obj (op W)),
      (secEqX f F G H' _ z).val.app (op ((Over.post (opensMap f)).obj (Over.mk i)))
          (((modulePullbackPushforwardAdjunction f).unit.app F).val.app (op W) t) =
        ((modulePullbackPushforwardAdjunction f).unit.app G).val.app (op W)
          ((secEqY V F G H s).val.app (op (Over.mk i)) t)) :
    z = pullbackHomSection f V F G H H' s :=
  (secEqX f F G H' _).injective
    ((eq_overPullbackHom f V _ _ h).trans (secEqX_pullbackHomSection f V F G H H' s).symm)

/-- `pullbackHomSection` is additive. -/
theorem pullbackHomSection_add (s₁ s₂ : H.obj.val.obj (op V)) :
    pullbackHomSection f V F G H H' (s₁ + s₂) =
      pullbackHomSection f V F G H H' s₁ + pullbackHomSection f V F G H H' s₂ := by
  rw [pullbackHomSection, pullbackHomSection, pullbackHomSection, (secEqY V F G H).map_add,
    overPullbackHom_add]
  exact (secEqX f F G H' _).symm.map_add _ _

/-- Restriction of sections of `SheafHom(f^*F, f^*G)`, read on local homomorphisms. -/
theorem secEqX_map_val_app {V' : Opens Y.carrier} (g : V' ⟶ V) {W : Opens Y.carrier}
    (i : W ⟶ V') (z : H'.obj.val.obj (op ((opensMap f).obj V)))
    (x : ((modulePullback f).obj F).val.obj (op ((opensMap f).obj W))) :
    (secEqX f F G H' ((opensMap f).obj V') (H'.obj.val.map ((opensMap f).map g).op z)).val.app
        (op ((Over.post (opensMap f)).obj (Over.mk i))) x =
      (secEqX f F G H' _ z).val.app (op ((Over.post (opensMap f)).obj (Over.mk (i ≫ g)))) x :=
  (H'.restrict_natural (leOfHom ((opensMap f).map g)) z (leOfHom ((opensMap f).map i)) x).symm

/-- Restriction of sections of `SheafHom(F, G)`, read on local homomorphisms. -/
theorem secEqY_map_val_app {V' : Opens Y.carrier} (g : V' ⟶ V) {W : Opens Y.carrier}
    (i : W ⟶ V') (s : H.obj.val.obj (op V)) (t : F.val.obj (op W)) :
    (secEqY V' F G H (H.obj.val.map g.op s)).val.app (op (Over.mk i)) t =
      (secEqY V F G H s).val.app (op (Over.mk (i ≫ g))) t :=
  (H.restrict_natural (leOfHom g) s (leOfHom i) t).symm

/-- `pullbackHomSection` commutes with restriction to smaller opens. -/
theorem pullbackHomSection_map {V' : Opens Y.carrier} (g : V' ⟶ V) (s : H.obj.val.obj (op V)) :
    pullbackHomSection f V' F G H H' (H.obj.val.map g.op s) =
      H'.obj.val.map ((opensMap f).map g).op (pullbackHomSection f V F G H H' s) := by
  refine (eq_pullbackHomSection f V' F G H H' _ _ fun W i t => ?_).symm
  refine (secEqX_map_val_app f V F G H' g i _ _).trans ?_
  rw [secEqX_pullbackHomSection, overPullbackHom_val_app_unit]
  exact congrArg _ (secEqY_map_val_app V F G H g i s t).symm

/-- Multiplication by a section `r` of `𝒪_Y` over `V`, on `G|_V`, read in the category of
modules over `structureSheafRing Y`. -/
noncomputable def overSmulY (r : (structureSheaf Y.sheaf).obj.obj (op V)) : G.over V ⟶ G.over V :=
  Stacks.SheafOfModules.overSmul (Rc := Y.sheaf) G V r

/-- Multiplying a section of `SheafHom(F, G)` by `r` postcomposes its local homomorphism with
multiplication by `r`. -/
theorem secEqY_smul (r : (structureSheaf Y.sheaf).obj.obj (op V)) (s : H.obj.val.obj (op V)) :
    secEqY V F G H (r • s) = secEqY V F G H s ≫ overSmulY V G r :=
  SheafHom.sectionsEquiv_smul H V r s

/-- Multiplication by a section `c` of `𝒪_X` over `U`, on `(f^*G)|_U`, read in the category of
modules over `structureSheafRing X`. -/
noncomputable def overSmulX (U : Opens X.carrier) (c : (structureSheaf X.sheaf).obj.obj (op U)) :
    ((modulePullback f).obj G).over U ⟶ ((modulePullback f).obj G).over U :=
  Stacks.SheafOfModules.overSmul (Rc := X.sheaf) _ U c

/-- Multiplying a section of `SheafHom(f^*F, f^*G)` by `c` postcomposes its local homomorphism
with multiplication by `c`. -/
theorem secEqX_smul (U : Opens X.carrier) (c : (structureSheaf X.sheaf).obj.obj (op U))
    (z : H'.obj.val.obj (op U)) :
    secEqX f F G H' U (c • z) = secEqX f F G H' U z ≫ overSmulX f G U c :=
  SheafHom.sectionsEquiv_smul H' U c z

/-- The pullback `f^♯ r` of a section `r` of `𝒪_Y` over `V`, a section of `𝒪_X` over `f⁻¹V`. -/
noncomputable def pullbackScalar (r : (structureSheaf Y.sheaf).obj.obj (op V)) :
    (structureSheaf X.sheaf).obj.obj (op ((opensMap f).obj V)) :=
  ((structureSheafHom f).hom.app (op V)).hom r

/-- `overSmulX` on sections over `f⁻¹W`, for `W ⊆ V`. -/
theorem overSmulX_val_app (c : (structureSheaf X.sheaf).obj.obj (op ((opensMap f).obj V)))
    {W : Opens Y.carrier} (i : W ⟶ V)
    (x : ((modulePullback f).obj G).val.obj (op ((opensMap f).obj W))) :
    (overSmulX f G ((opensMap f).obj V) c).val.app
        (op ((Over.post (opensMap f)).obj (Over.mk i))) x =
      (structureSheafRing X).obj.map ((opensMap f).map i).op c • x :=
  Stacks.SheafOfModules.overSmul_app (Rc := X.sheaf) ((modulePullback f).obj G) _ c
    (op ((Over.post (opensMap f)).obj (Over.mk i))) x

/-- `overSmulY` on sections over `W ⊆ V`. -/
theorem overSmulY_val_app (r : (structureSheaf Y.sheaf).obj.obj (op V)) {W : Opens Y.carrier}
    (i : W ⟶ V) (y : G.val.obj (op W)) :
    (overSmulY V G r).val.app (op (Over.mk i)) y = (structureSheafRing Y).obj.map i.op r • y :=
  Stacks.SheafOfModules.overSmul_app (Rc := Y.sheaf) G V r (op (Over.mk i)) y

/-- Restriction commutes with the pullback `f^♯` of sections of the structure sheaf. -/
theorem map_pullbackScalar (r : (structureSheaf Y.sheaf).obj.obj (op V)) {W : Opens Y.carrier}
    (i : W ⟶ V) :
    (structureSheafRing X).obj.map ((opensMap f).map i).op (pullbackScalar f V r) =
      ((structureSheafHom f).hom.app (op W)).hom ((structureSheafRing Y).obj.map i.op r) :=
  (ConcreteCategory.congr_hom ((structureSheafHom f).hom.naturality i.op) r).symm

/-- Multiplication by `r` commutes with the unit `G ⟶ f_* f^* G`, read on `f⁻¹V`. -/
theorem overSmulX_unit (r : (structureSheaf Y.sheaf).obj.obj (op V)) {W : Opens Y.carrier}
    (i : W ⟶ V) (y : G.val.obj (op W)) :
    (overSmulX f G _ (pullbackScalar f V r)).val.app
        (op ((Over.post (opensMap f)).obj (Over.mk i)))
        (((modulePullbackPushforwardAdjunction f).unit.app G).val.app (op W) y) =
      ((modulePullbackPushforwardAdjunction f).unit.app G).val.app (op W)
        ((overSmulY V G r).val.app (op (Over.mk i)) y) := by
  refine (overSmulX_val_app f V G _ i _).trans ?_
  refine Eq.trans ?_ (congrArg _ (overSmulY_val_app V G r i _)).symm
  refine Eq.trans ?_ ((((modulePullbackPushforwardAdjunction f).unit.app G).val.app
    (op W)).hom.map_smul _ _).symm
  refine Eq.trans ?_ (ModuleCat.restrictScalars.smul_def _ _ _).symm
  rw [map_pullbackScalar]
  rfl

/-- `pullbackHomSection` is semilinear along `f^♯`. -/
theorem pullbackHomSection_smul (r : (structureSheaf Y.sheaf).obj.obj (op V))
    (s : H.obj.val.obj (op V)) :
    pullbackHomSection f V F G H H' (r • s) =
      pullbackScalar f V r • pullbackHomSection f V F G H H' s := by
  refine (eq_pullbackHomSection f V F G H H' _ _ fun W i t => ?_).symm
  rw [secEqX_smul, secEqY_smul]
  refine (comp_val_app_apply _ _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg (ConcreteCategory.hom
    (((modulePullbackPushforwardAdjunction f).unit.app G).val.app (op W)))
    (comp_val_app_apply (secEqY V F G H s) (overSmulY V G r) (op (Over.mk i)) t)).symm
  rw [secEqX_pullbackHomSection, overPullbackHom_val_app_unit]
  exact overSmulX_unit f V G r i _

/-- The adjoint transpose `SheafHom(F, G) ⟶ f_* SheafHom(f^*F, f^*G)` of the canonical
comparison: a section over `V` goes to the pullback to `f⁻¹V` of its local homomorphism. -/
noncomputable def pullbackHomTranspose :
    @Quiver.Hom (_root_.SheafOfModules.{u} (structureSheafRing Y)) _ H.obj
      ((modulePushforward f).obj H'.obj) :=
  ⟨PresheafOfModules.homMk
    { app := fun V => AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (pullbackHomSection f V.unop F G H H')
          (pullbackHomSection_add f V.unop F G H H'))
      naturality := fun V V' g => by
        ext s
        exact pullbackHomSection_map f V.unop F G H H' g.unop s }
    (fun V r s => pullbackHomSection_smul f V.unop F G H H' r s)⟩

/-- The canonical map `f^* SheafHom(F, G) ⟶ SheafHom(f^*F, f^*G)`: the adjoint transpose of
pulling back local homomorphisms. -/
noncomputable def pullbackSheafHomMap : (modulePullback f).obj H.obj ⟶ H'.obj :=
  ((modulePullbackPushforwardAdjunction f).homEquiv H.obj H'.obj).symm
    (pullbackHomTranspose f F G H H')

/-- The canonical map `pullbackSheafHomMap`, together with its action on pulled-back local
homomorphisms and pulled-back sections. -/
noncomputable def canonicalPullbackSheafHomComparison : PullbackSheafHomComparison f F G H H' where
  hom := pullbackSheafHomMap f F G H H'
  map_sections V U i s t := by
    rw [pullbackSheafHomMap, Equiv.apply_symm_apply]
    exact (congrArg (fun ψ => ψ.val.app (op ((Over.post (opensMap f)).obj (Over.mk i)))
      (((modulePullbackPushforwardAdjunction f).unit.app F).val.app (op U) t))
      (secEqX_pullbackHomSection f V F G H H' s)).trans (overPullbackHom_val_app_unit f V _ i t)

/-- **Stacks Project, Tag 0C6I.** Let `f : X ⟶ Y` be a flat morphism of ringed spaces and let
`F`, `G` be `𝒪_Y`-modules with `F` finitely presented. Then the canonical map
`f^* SheafHom(F, G) ⟶ SheafHom(f^*F, f^*G)` is an isomorphism.

The canonical map is `pullbackSheafHomMap`, the adjoint transpose of pulling back local
homomorphisms along `f`; the two internal Homs are any `SheafHom` models. -/
@[stacks 0C6I]
theorem isIso_pullbackSheafHomMap (hf : AlgebraicGeometry.IsFlat f) [F.IsFinitePresentation] :
    IsIso (pullbackSheafHomMap f F G H H') :=
  pullbackSheafHomComparison_isIso f hf F G H H' (canonicalPullbackSheafHomComparison f F G H H')

end Comparison

end Stacks.SheafHomPullback
