module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceAdjunctions
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# Variance of the internal Hom of presheaves of modules

Let `O` be a presheaf of commutative rings on a category `C`. The internal Hom presheaf
`internalHom O F G` of Stacks 03EM, whose sections over `U` are the morphisms
`F|_{C/U} ⟶ G|_{C/U}` of presheaves of modules on the slice, is contravariant in `F` and
covariant in `G`. Stacks 03EN asserts that it is continuous in each variable separately: it
turns colimits in the first variable into limits, and preserves limits in the second.

## Main definitions

* `Stacks.PresheafOfModules.InternalHom.internalHomMapLeft` and `internalHomFunctor`:
  precomposition in the first variable, assembled as a functor into the opposite category so
  that "colimits go to limits" is literally preservation of colimits rather than an unnamed
  comparison map.
* `Stacks.PresheafOfModules.InternalHom.internalHomMapRight` and `internalHomSecondFunctor`:
  postcomposition in the second variable, as an endofunctor of presheaves of modules.
* `Stacks.PresheafOfModules.InternalHom.pairing` and
  `Stacks.PresheafOfModules.InternalHom.transposeHom`: the two-variable pairing attached to a
  morphism into an internal Hom, and the morphism obtained by exchanging its two arguments.

## Main results

* `Stacks.PresheafOfModules.InternalHom.internalHomFunctor_preservesColimitsOfShape`: for a
  fixed target, internal Hom carries arbitrary colimits in the first variable to limits.
* `Stacks.PresheafOfModules.InternalHom.internalHomSecondFunctor_preservesLimits`: for a
  fixed source, internal Hom preserves arbitrary limits in the second variable.
* `Stacks.PresheafOfModules.InternalHom.transposeHom_involutive`: transposing twice returns the
  original morphism, so a morphism `A ⟶ internalHom O B G` and a morphism
  `B ⟶ internalHom O A G` are the same datum.

## Implementation notes

The first variable is handled by directing the functor into the opposite category, so that
the assertion of Stacks 03EN is preservation of colimits.

The two halves are stated at the universes each needs: the first variable at module universe
`max u v`, the second at an independent `m` and at `max u v w m` for the endofunctor. Both
are available because Tag 03EM leaves the module universe of `internalHom` free.

The symmetry of the internal Hom pairing is a computation with the slice sites and needs no
sheaf condition, so it is stated here, for presheaves of modules, at module universe
`max u v`: a morphism `A ⟶ internalHom O B G` is the same thing as an `O`-bilinear pairing of
`A` and `B` into `G`, natural over every object of the site, and that description is symmetric
in `A` and `B`.

The three places where the restriction maps of the slice sites have to be moved across a
composition are written as `Eq.trans` of a `congrArg` rather than as rewrites: the carrier of
`((restrFun O U).obj G).obj V` is `G.obj (op V.left)` only up to unfolding `restrFun`, so a
`rw` reports a pattern mismatch while `exact` and `congrArg` go through.

The two presheaf halves of Stacks 03EN are proved here; the two sheaf halves are
`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor_preservesLimits` and
`Stacks.SheafOfModules.InternalHom.sheafInternalHomFunctor_preservesColimitsOfShape`.

## References

* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.PresheafOfModules.InternalHom

section FirstVariable

universe w v u m

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat)

/-- The action of `O(U)` on the slice-level endomorphisms of `G|_{C/U}`, as a ring
homomorphism into the endomorphism ring. -/
private noncomputable def scalarToEnd
    (G : _root_.PresheafOfModules.{max u v} (Oforget O)) (U : C) :
    (Oforget O).obj (op U) →+* End ((restrFun O U).obj G) where
  toFun r := .of (multEndoHom O G U r)
  map_one' := by
    ext1
    change multEndoHom O G U 1 = 𝟙 _
    simpa only [smulHom, Category.id_comp] using homModule_one_smul O G G U (𝟙 _)
  map_mul' f g := by
    ext1
    change multEndoHom O G U (f * g) =
      multEndoHom O G U g ≫ multEndoHom O G U f
    simpa only [smulHom, Category.id_comp] using homModule_mul_smul O G G U f g (𝟙 _)
  map_zero' := by
    ext1
    change multEndoHom O G U 0 = 0
    simpa only [smulHom, Category.id_comp] using homModule_zero_smul O G G U (𝟙 _)
  map_add' f g := by
    ext1
    change multEndoHom O G U (f + g) = multEndoHom O G U f + multEndoHom O G U g
    simpa only [smulHom, Category.id_comp] using homModule_add_smul O G G U f g (𝟙 _)

/-- The internal Hom against `G`, evaluated at `U`, as a functor into the opposite category
of modules over `O(U)`. -/
private noncomputable def evaluatedInternalHomFunctor
    (G : _root_.PresheafOfModules.{max u v} (Oforget O)) (U : C) :
    _root_.PresheafOfModules.{max u v} (Oforget O) ⥤
      (ModuleCat.{max u v} ((Oforget O).obj (op U)))ᵒᵖ :=
  ((restrFun O U).op ⋙
    CategoryTheory.preadditiveYonedaObj.{max u v} ((restrFun O U).obj G) ⋙
    ModuleCat.restrictScalars (scalarToEnd O G U)).rightOp

/-- Restriction of scalars along an identity is the identity functor. -/
private noncomputable def presheafRestrictScalarsId
    (R : Cᵒᵖ ⥤ RingCat) :
    _root_.PresheafOfModules.restrictScalars (𝟙 R) ≅
      Functor.id (_root_.PresheafOfModules.{max u v} R) := Iso.refl _

/-- Tag 03EM's restriction to a slice is the pushforward along `Over.forget U`. -/
private noncomputable def restrFunIsoPushforward (U : C) :
    restrFun.{v, u, _, max u v} O U ≅
      _root_.PresheafOfModules.pushforward₀.{max u v} (Over.forget U) (Oforget O) := by
  unfold restrFun _root_.PresheafOfModules.pushforward
  exact Functor.isoWhiskerLeft _ (presheafRestrictScalarsId (ORestr O U)) ≪≫
    Functor.rightUnitor _

/-- Restriction to a slice preserves colimits. -/
private theorem restrFunPreservesColimitsOfShape
    (U : C) (J : Type w) [Category.{w} J] :
    PreservesColimitsOfShape J (restrFun.{v, u, _, max u v} O U) := by
  let A := Stacks.Sites.OverModules.presheafModuleAdjunctionsOver.{v, u, _, 0} (Oforget O) U
  refine ⟨?_⟩
  intro K
  refine ⟨?_⟩
  intro c hc
  let : PreservesColimitsOfSize.{w, w}
      (_root_.PresheafOfModules.pushforward₀.{max u v} (Over.forget U) (Oforget O)) :=
    A.restrictionDirectImage.leftAdjoint_preservesColimits.{w, w}
  exact ⟨IsColimit.mapCoconeEquiv (restrFunIsoPushforward O U).symm
    (isColimitOfPreserves
      (_root_.PresheafOfModules.pushforward₀.{max u v} (Over.forget U) (Oforget O)) hc)⟩

/-- Precomposition in the first variable of the internal Hom presheaf. -/
noncomputable def internalHomMapLeft
    {F F' G : _root_.PresheafOfModules.{m} (Oforget O)} (f : F ⟶ F') :
    internalHom O F' G ⟶ internalHom O F G :=
  _root_.PresheafOfModules.Hom.mk
    (fun X ↦
      letI := homModule O F' G X.unop
      letI := homModule O F G X.unop
      ModuleCat.ofHom
        { toFun := fun g ↦ (restrFun O X.unop).map f ≫ g
          map_add' := fun _ _ ↦ by simp
          map_smul' := fun r g ↦ by
            change _ ≫ smulHom O F' G X.unop r g =
              smulHom O F G X.unop r ((restrFun O X.unop).map f ≫ g)
            simp only [smulHom, Category.assoc] })
    (fun {X Y} a ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro g
      change (restrFun O Y.unop).map f ≫ homRestr O F' G a.unop g =
        homRestr O F G a.unop ((restrFun O X.unop).map f ≫ g)
      rfl)

/-- Internal Hom is contravariantly functorial in its first variable: precomposing with `g` and
then with `f` is precomposing with `f ≫ g`. -/
theorem internalHomMapLeft_comp
    {F F' F'' G : _root_.PresheafOfModules.{m} (Oforget O)} (f : F ⟶ F') (g : F' ⟶ F'') :
    internalHomMapLeft O g ≫ internalHomMapLeft O f (G := G) =
      internalHomMapLeft O (f ≫ g) := rfl

/-- Internal Hom against `G`, regarded as a covariant functor to the opposite category of
presheaves of modules. -/
noncomputable def internalHomFunctor
    (G : _root_.PresheafOfModules.{max u v} (Oforget O)) :
    _root_.PresheafOfModules.{max u v} (Oforget O) ⥤
      (_root_.PresheafOfModules.{max u v} (Oforget O))ᵒᵖ where
  obj F := op (internalHom O F G)
  map f := (internalHomMapLeft O f).op
  map_id _ := rfl
  map_comp f g := Quiver.Hom.unop_inj (internalHomMapLeft_comp O f g).symm

/-- The preadditive Yoneda functor at `X`, followed by a restriction of scalars along a ring
map into `End X`, preserves limits of every shape. -/
private theorem preadditiveYonedaObj_restrictScalars_preservesLimitsOfShape
    {A : Type u} [Category.{v} A] [Preadditive A] (X : A)
    {R : Type*} [Ring R] (f : R →+* End X)
    (J : Type w) [Category.{w} J] :
    PreservesLimitsOfShape J
      (preadditiveYonedaObj.{v, u} X ⋙ ModuleCat.restrictScalars.{v} f) := by
  let T := preadditiveYonedaObj.{v, u} X ⋙ ModuleCat.restrictScalars.{v} f
  let L := ModuleCat.uliftFunctor.{max w v, v} R
  let : PreservesLimitsOfSize.{w, w}
      ((T ⋙ L) ⋙ forget (ModuleCat.{max w v} R)) := by
    show PreservesLimitsOfSize.{w, w}
      (yoneda.obj X ⋙ CategoryTheory.uliftFunctor.{max w v})
    infer_instance
  let : PreservesLimitsOfSize.{w, w} (T ⋙ L) :=
    preservesLimits_of_reflects_of_preserves.{w, w}
      (T ⋙ L) (forget (ModuleCat.{max w v} R))
  exact (preservesLimits_of_reflects_of_preserves.{w, w} T L).preservesLimitsOfShape

private noncomputable instance evaluatedInternalHomFunctor_preservesColimitsOfShape
    (G : _root_.PresheafOfModules.{max u v} (Oforget O)) (U : C)
    (I : Type w) [Category.{w} I] :
    PreservesColimitsOfShape I (evaluatedInternalHomFunctor O G U) := by
  let : PreservesColimitsOfShape.{w, w} (Iᵒᵖ)ᵒᵖ
      (restrFun.{v, u, _, max u v} O U) :=
    restrFunPreservesColimitsOfShape O U (Iᵒᵖ)ᵒᵖ
  let : PreservesLimitsOfShape.{w, w} Iᵒᵖ
      ((restrFun.{v, u, _, max u v} O U).op) := by
    apply preservesLimitsOfShape_op
  let X := (restrFun.{v, u, _, max u v} O U).obj G
  let : PreservesLimitsOfShape.{w, w} Iᵒᵖ
      (preadditiveYonedaObj.{max u v} X ⋙
        ModuleCat.restrictScalars.{max u v} (scalarToEnd O G U)) :=
    preadditiveYonedaObj_restrictScalars_preservesLimitsOfShape
      X (scalarToEnd O G U) Iᵒᵖ
  apply preservesColimitsOfShape_rightOp.{w, w}

private noncomputable def evaluatedInternalHomLeftOpIso
    (G : _root_.PresheafOfModules.{max u v} (Oforget O)) (U : C) :
    ((internalHomFunctor O G).leftOp ⋙
      _root_.PresheafOfModules.evaluation (Oforget O) (op U)) ≅
      (evaluatedInternalHomFunctor O G U).leftOp := by
  refine NatIso.ofComponents ?_ ?_
  · intro X
    apply Iso.refl
  · intro X Y f
    rfl

/-- A compatible family of slice-level morphisms out of the terms of a colimit, read as a
cocone on the restricted diagram. -/
private noncomputable def internalHomSectionsCocone
    (G : _root_.PresheafOfModules.{max u v} (Oforget O)) (U : C)
    (I : Type w) [Category.{w} I]
    (K : Iᵒᵖ ⥤ (_root_.PresheafOfModules.{max u v} (Oforget O))ᵒᵖ)
    (s : Functor.sections
      (((K ⋙ (internalHomFunctor O G).leftOp) ⋙
        _root_.PresheafOfModules.evaluation (Oforget O) (op U)) ⋙
        forget (ModuleCat ((Oforget O).obj (op U))))) :
    Cocone (K.leftOp ⋙ restrFun O U) where
  pt := (restrFun O U).obj G
  ι :=
    { app := fun i ↦ s.1 (unop i)
      naturality := fun {i j} f ↦ by
        change (restrFun O U).map ((K.leftOp).map f) ≫ s.1 (unop j) = s.1 (unop i)
        exact s.2 (unop f) }

/-- Over a limit cone, the sections of the evaluated internal-Hom diagram are small: such a
family of compatible morphisms is determined by the single morphism it descends to. -/
private theorem internalHomSections_small
    (G : _root_.PresheafOfModules.{max u v} (Oforget O)) (U : C)
    (I : Type w) [Category.{w} I]
    (K : Iᵒᵖ ⥤ (_root_.PresheafOfModules.{max u v} (Oforget O))ᵒᵖ)
    (c : Cone K) (hc : IsLimit c) :
    Small.{max u v}
      ((((K ⋙ (internalHomFunctor O G).leftOp) ⋙
        _root_.PresheafOfModules.evaluation (Oforget O) (op U)) ⋙
        forget (ModuleCat ((Oforget O).obj (op U)))).sections) := by
  let : PreservesColimitsOfShape ((Iᵒᵖ)ᵒᵖ) (restrFun O U) :=
    restrFunPreservesColimitsOfShape O U ((Iᵒᵖ)ᵒᵖ)
  let hcolim := isColimitCoconeLeftOpOfCone K hc
  let d := (restrFun O U).mapCocone (coconeLeftOpOfCone c)
  have hd : IsColimit d := isColimitOfPreserves (restrFun O U) hcolim
  let : Small.{max u v}
      ((restrFun O U).obj c.pt.unop ⟶ (restrFun O U).obj G) := inferInstance
  let toHom :
      ((((K ⋙ (internalHomFunctor O G).leftOp) ⋙
        _root_.PresheafOfModules.evaluation (Oforget O) (op U)) ⋙
        forget (ModuleCat ((Oforget O).obj (op U)))).sections) →
        ((restrFun O U).obj c.pt.unop ⟶ (restrFun O U).obj G) :=
    fun s ↦ hd.desc (internalHomSectionsCocone O G U I K s)
  apply small_of_injective (f := toHom)
  intro s t h
  apply Subtype.ext
  funext i
  have key (s : Functor.sections
      (((K ⋙ (internalHomFunctor O G).leftOp) ⋙
        _root_.PresheafOfModules.evaluation (Oforget O) (op U)) ⋙
        forget (ModuleCat ((Oforget O).obj (op U))))) :
      d.ι.app (op i) ≫ hd.desc (internalHomSectionsCocone O G U I K s) = s.1 i :=
    hd.fac _ _
  exact (key s).symm.trans ((congrArg (d.ι.app (op i) ≫ ·) h).trans (key t))

private theorem internalHomLeftOp_preservesLimitsOfShape
    (G : _root_.PresheafOfModules.{max u v} (Oforget O)) (I : Type w) [Category.{w} I] :
    PreservesLimitsOfShape Iᵒᵖ (internalHomFunctor O G).leftOp := by
  refine ⟨fun {K} => ⟨fun {c} hc => ?_⟩⟩
  let H := internalHomFunctor O G
  let F := H.leftOp
  have hSmall : ∀ U : Cᵒᵖ,
      Small.{max u v, max w u v}
        (((K ⋙ F) ⋙ _root_.PresheafOfModules.evaluation (Oforget O) U ⋙
          forget (ModuleCat ((Oforget O).obj U))).sections) :=
    fun U => internalHomSections_small O G U.unop I K c hc
  refine ⟨@_root_.PresheafOfModules.evaluationJointlyReflectsLimits
    C inferInstance (Oforget O) (Iᵒᵖ) inferInstance (K ⋙ F) hSmall
    (F.mapCone c) ?_⟩
  intro U
  let Q := evaluatedInternalHomFunctor O G U.unop
  let : PreservesColimitsOfShape I Q :=
    evaluatedInternalHomFunctor_preservesColimitsOfShape O G U.unop I
  let : PreservesColimitsOfShape (Iᵒᵖ)ᵒᵖ Q :=
    preservesColimitsOfShape_of_equiv (opOpEquivalence I).symm Q
  let : PreservesLimitsOfShape Iᵒᵖ Q.leftOp :=
    preservesLimitsOfShape_leftOp (J := Iᵒᵖ) Q
  let : PreservesLimitsOfShape Iᵒᵖ
      (F ⋙ _root_.PresheafOfModules.evaluation (Oforget O) U) :=
    preservesLimitsOfShape_of_natIso
      (evaluatedInternalHomLeftOpIso O G U.unop).symm
  exact isLimitOfPreserves
    (F ⋙ _root_.PresheafOfModules.evaluation (Oforget O) U) hc

/-- For a fixed target `G`, internal Hom in the first variable sends arbitrary colimits of
presheaves of `O`-modules to limits. -/
@[stacks 03EN "presheaf_first_variable"]
noncomputable instance internalHomFunctor_preservesColimitsOfShape
    (G : _root_.PresheafOfModules.{max u v} (Oforget O)) (I : Type w) [Category.{w} I] :
    PreservesColimitsOfShape I (internalHomFunctor O G) := by
  let H := internalHomFunctor O G
  let F := H.leftOp
  let : PreservesLimitsOfShape Iᵒᵖ F :=
    internalHomLeftOp_preservesLimitsOfShape O G I
  let : PreservesColimitsOfShape I F.rightOp :=
    preservesColimitsOfShape_rightOp (J := I) F
  exact preservesColimitsOfShape_of_natIso (Functor.leftOpRightOpIso H)

end FirstVariable

/-! ### The pairing attached to a morphism into an internal Hom, and its transpose -/

section Transpose

universe v u w

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{w})
variable {A B G : _root_.PresheafOfModules.{max u v} (Oforget O)}

/-- The pairing attached to `f : A ⟶ internalHom O B G`: the section `a` of `A` over `U` is sent
by `f` to a morphism `B|_U ⟶ G|_U` on the slice site `C/U`, whose component at the terminal
object `Over.mk (𝟙 U)` is applied to the section `b` of `B` over `U`. -/
noncomputable def pairing (f : A ⟶ internalHom O B G) (U : C)
    (a : A.obj (op U)) (b : B.obj (op U)) : G.obj (op U) :=
  (((f.app (op U)).hom a).app (op (Over.mk (𝟙 U)))).hom b

/-- The pairing is additive in its first argument. -/
lemma pairing_add_left (f : A ⟶ internalHom O B G) (U : C)
    (a a' : A.obj (op U)) (b : B.obj (op U)) :
    pairing O f U (a + a') b = pairing O f U a b + pairing O f U a' b := by
  unfold pairing
  rw [map_add]; rfl

/-- The pairing is `O(U)`-linear in its first argument. -/
lemma pairing_smul_left (f : A ⟶ internalHom O B G) (U : C)
    (r : (Oforget O).obj (op U)) (a : A.obj (op U)) (b : B.obj (op U)) :
    pairing O f U (r • a) b = r • pairing O f U a b := by
  unfold pairing
  rw [map_smul]
  show (((Oforget O).map (𝟙 U).op).hom r) • pairing O f U a b = _
  simp [pairing]

/-- The pairing is natural: restricting both arguments along `g` restricts the value. The two
sides differ because relocalization along `g` sends the terminal object `Over.mk (𝟙 V)` of `C/V`
to `Over.mk (𝟙 V ≫ g)`, so this is the naturality of `f.app (op U) a` along the morphism
`Over.homMk g : Over.mk (𝟙 V ≫ g) ⟶ Over.mk (𝟙 U)` of `C/U`. -/
lemma pairing_naturality (f : A ⟶ internalHom O B G) {U V : C}
    (g : V ⟶ U) (a : A.obj (op U)) (b : B.obj (op U)) :
    pairing O f V (A.map g.op a) (B.map g.op b) = G.map g.op (pairing O f U a b) := by
  unfold pairing
  rw [_root_.PresheafOfModules.naturality_apply]
  show ((f.app (op U) a).app (op (Over.mk (𝟙 V ≫ g)))) (B.map g.op b) = _
  exact _root_.PresheafOfModules.naturality_apply (f.app (op U) a)
    (Over.homMk g (by simp) : Over.mk (𝟙 V ≫ g) ⟶ Over.mk (𝟙 U)).op b

/-- The pairing is additive in its second argument. -/
lemma pairing_add_right (f : A ⟶ internalHom O B G) (U : C)
    (a : A.obj (op U)) (b b' : B.obj (op U)) :
    pairing O f U a (b + b') = pairing O f U a b + pairing O f U a b' :=
  map_add _ b b'

/-- The pairing is `O(U)`-linear in its second argument. -/
lemma pairing_smul_right (f : A ⟶ internalHom O B G) (U : C)
    (r : (Oforget O).obj (op U)) (a : A.obj (op U)) (b : B.obj (op U)) :
    pairing O f U a (r • b) = r • pairing O f U a b :=
  ((f.app (op U) a).app (op (Over.mk (𝟙 U)))).hom.map_smul r b

/-- The morphism `A|_U ⟶ G|_U` obtained from the pairing of `f` by fixing a section `b` of `B`
over `U`, which is the transpose of `f` evaluated at `b`. -/
noncomputable def transposeSection (f : A ⟶ internalHom O B G)
    (U : C) (b : B.obj (op U)) : (restrFun O U).obj A ⟶ (restrFun O U).obj G where
  app V := ModuleCat.ofHom
    (X := ((restrFun O U).obj A).obj V)
    (Y := ((restrFun O U).obj G).obj V)
    { toFun := fun a => pairing O f V.unop.left a (B.map V.unop.hom.op b)
      map_add' := fun a a' => pairing_add_left O f V.unop.left a a' _
      map_smul' := fun r a => pairing_smul_left O f V.unop.left r a _ }
  naturality {V W} g := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro a
    change pairing O f W.unop.left (A.map g.unop.left.op a) (B.map W.unop.hom.op b) =
      G.map g.unop.left.op (pairing O f V.unop.left a (B.map V.unop.hom.op b))
    rw [← Over.w g.unop, op_comp, _root_.PresheafOfModules.map_comp_apply]
    exact pairing_naturality O f g.unop.left a _

/-- **The transpose of a morphism into an internal Hom.** A morphism `A ⟶ internalHom O B G` is
the same thing as a pairing of `A` and `B` into `G`, and that description is symmetric in `A` and
`B`; `transposeHom` is the resulting morphism `B ⟶ internalHom O A G`. -/
noncomputable def transposeHom (f : A ⟶ internalHom O B G) :
    B ⟶ internalHom O A G where
  app U := ModuleCat.ofHom
    (X := B.obj U) (Y := (internalHom O A G).obj U)
    { toFun := transposeSection O f U.unop
      map_add' := by
        intro b b'
        apply _root_.PresheafOfModules.hom_ext; intro V
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro a
        change pairing O f V.unop.left a (B.map V.unop.hom.op (b + b')) =
          pairing O f V.unop.left a (B.map V.unop.hom.op b) +
            pairing O f V.unop.left a (B.map V.unop.hom.op b')
        exact (congrArg (pairing O f V.unop.left a)
          (map_add (B.map V.unop.hom.op).hom b b')).trans
            (pairing_add_right O f V.unop.left a _ _)
      map_smul' := by
        intro r b
        apply _root_.PresheafOfModules.hom_ext; intro V
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro a
        change pairing O f V.unop.left a (B.map V.unop.hom.op (r • b)) =
          ((Oforget O).map V.unop.hom.op).hom r •
            pairing O f V.unop.left a (B.map V.unop.hom.op b)
        exact (congrArg (pairing O f V.unop.left a)
          (_root_.PresheafOfModules.map_smul B V.unop.hom.op r b)).trans
            (pairing_smul_right O f V.unop.left _ a _) }
  naturality {U V} g := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro b
    apply _root_.PresheafOfModules.hom_ext; intro W
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro a
    change pairing O f W.unop.left a (B.map W.unop.hom.op (B.map g b)) =
      pairing O f W.unop.left a (B.map (W.unop.hom ≫ g.unop).op b)
    rw [op_comp, _root_.PresheafOfModules.map_comp_apply]
    rfl

/-- Taking the transpose twice returns the original morphism: the pairing determines, and is
determined by, the morphism into the internal Hom. -/
lemma transposeHom_involutive (f : A ⟶ internalHom O B G) :
    transposeHom O (transposeHom O f) = f := by
  apply _root_.PresheafOfModules.hom_ext; intro U
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro a
  apply _root_.PresheafOfModules.hom_ext; intro V
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro b
  show pairing O f V.unop.left (A.map V.unop.hom.op a)
    (B.map (𝟙 V.unop.left).op b) = (f.app U a).app V b
  unfold pairing
  rw [_root_.PresheafOfModules.naturality_apply]
  show (f.app U a).app (op (Over.mk (𝟙 V.unop.left ≫ V.unop.hom)))
    (B.map (𝟙 V.unop.left).op b) = _
  have hi : B.map (𝟙 V.unop.left).op b = b := by
    show B.presheaf.map (𝟙 (op V.unop.left)) b = b
    rw [B.presheaf.map_id]
    rfl
  rw [hi]
  exact congrArg (fun k : V.unop.left ⟶ U.unop =>
    show G.obj (op V.unop.left) from
      (f.app U a).app (op (Over.mk k)) b) (Category.id_comp V.unop.hom)

end Transpose

section SecondVariable

universe v u w m t s n

/-- A functor into presheaves of modules preserves limits as soon as it does so after every
evaluation, provided the resulting sections are small. -/
private theorem preservesLimits_of_moduleEvaluations
    {C : Type u} [Category.{v} C] {D : Type t} [Category.{s} D]
    {R : Cᵒᵖ ⥤ RingCat.{w}}
    (K : D ⥤ _root_.PresheafOfModules.{n} R)
    (hK : ∀ X, PreservesLimitsOfSize.{max n u, max n u}
      (K ⋙ _root_.PresheafOfModules.evaluation R X))
    (hSmall : ∀ {J : Type (max n u)} [Category.{max n u} J]
      (E : J ⥤ D) (X : Cᵒᵖ),
      Small.{n, max n u} (((E ⋙ K) ⋙ _root_.PresheafOfModules.evaluation R X ⋙
        forget (ModuleCat.{n} (R.obj X))).sections)) :
    PreservesLimits K := by
  refine ⟨?_⟩; intro J; refine ⟨?_⟩; intro E; refine ⟨?_⟩; intro c hc
  refine ⟨@_root_.PresheafOfModules.evaluationJointlyReflectsLimits.{n, v, max n u, u,
    max n u, w} C inferInstance R J inferInstance (E ⋙ K) (hSmall (J := J) E)
    (K.mapCone c) ?_⟩
  intro X
  let := hK X
  exact isLimitOfPreserves (K ⋙ _root_.PresheafOfModules.evaluation R X) hc

variable {C : Type u} [Category.{v} C]
variable (O : Cᵒᵖ ⥤ CommRingCat.{w})
variable (F : _root_.PresheafOfModules.{m} (Oforget O))

/-- Postcomposition by a morphism of presheaves of modules commutes with the scalar action on
morphisms over a slice category. -/
theorem internalHom_postcomp_smul
    {G H : _root_.PresheafOfModules.{m} (Oforget O)} (f : G ⟶ H) (U : C)
    (r : (Oforget O).obj (op U))
    (a : (restrFun O U).obj F ⟶ (restrFun O U).obj G) :
    smulHom O F G U r a ≫ (restrFun O U).map f =
      smulHom O F H U r (a ≫ (restrFun O U).map f) := by
  apply _root_.PresheafOfModules.hom_ext; intro X
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
  show (((restrFun O U).map f).app X).hom
      (fRestr O U r X • a.app X x) =
    fRestr O U r X • (((restrFun O U).map f).app X).hom (a.app X x)
  exact map_smul _ _ _

/-- The component at `X` of the action of internal Hom on a morphism in its second
variable. -/
noncomputable def internalHomMapRightApp
    {G H : _root_.PresheafOfModules.{m} (Oforget O)} (f : G ⟶ H) (X : Cᵒᵖ) :
    (internalHom O F G).obj X ⟶ (internalHom O F H).obj X :=
  letI := homModule O F G X.unop
  letI := homModule O F H X.unop
  ModuleCat.ofHom
    { toFun := fun a ↦ a ≫ (restrFun O X.unop).map f
      map_add' := by intro a b; simp
      map_smul' := fun r a => internalHom_postcomp_smul O F f X.unop r a }

/-- Postcomposition commutes with restriction of internal-Hom sections. -/
theorem internalHom_postcomp_naturality
    {G H : _root_.PresheafOfModules.{m} (Oforget O)} (f : G ⟶ H)
    {X Y : Cᵒᵖ} (g : X ⟶ Y)
    (a : (restrFun O X.unop).obj F ⟶ (restrFun O X.unop).obj G) :
    homRestr O F G g.unop a ≫ (restrFun O Y.unop).map f =
      homRestr O F H g.unop (a ≫ (restrFun O X.unop).map f) :=
  rfl

/-- The map on internal Hom induced covariantly by a morphism in the second variable. -/
noncomputable def internalHomMapRight
    {G H : _root_.PresheafOfModules.{m} (Oforget O)} (f : G ⟶ H) :
    internalHom O F G ⟶ internalHom O F H where
  app X := internalHomMapRightApp O F f X
  naturality _ := rfl

variable (F : _root_.PresheafOfModules.{max u v w m} (Oforget O))

/-- Internal Hom with fixed first variable, covariant in its second variable. -/
noncomputable def internalHomSecondFunctor :
    _root_.PresheafOfModules.{max u v w m} (Oforget O) ⥤
      _root_.PresheafOfModules.{max u v w m} (Oforget O) where
  obj G := internalHom O F G
  map f := internalHomMapRight O F f
  map_id _ := rfl
  map_comp f g := by
    apply _root_.PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rfl

/-- Internal Hom with fixed first variable commutes with arbitrary limits. -/
@[stacks 03EN "presheaf_second_variable"]
noncomputable instance internalHomSecondFunctor_preservesLimits :
    PreservesLimits (internalHomSecondFunctor.{v, u, w, m} O F) :=
  preservesLimits_of_moduleEvaluations (R := Oforget O)
    (internalHomSecondFunctor.{v, u, w, m} O F) (fun (X : Cᵒᵖ) => by
      let U := X.unop
      let A := Stacks.Sites.OverModules.presheafModuleAdjunctionsOver.{v, u, w, max w m}
        (Oforget O) U
      let R_U := restrFun.{v, u, w, max u v w m} O U
      have : PreservesLimits R_U := by
        change PreservesLimits
          (_root_.PresheafOfModules.pushforward₀ (Over.forget U) (Oforget O))
        exact A.extensionRestriction.rightAdjoint_preservesLimits
      let e : R_U ⋙ coyoneda.obj (Opposite.op (R_U.obj F)) ≅
          internalHomSecondFunctor.{v, u, w, m} O F ⋙
            _root_.PresheafOfModules.evaluation.{max u v w m} (Oforget O) X ⋙
            forget (ModuleCat.{max u v w m} ((Oforget O).obj (op U))) := by
        refine NatIso.ofComponents (fun G => Iso.refl _) ?_
        intro G H f
        ext a
        rfl
      have hUnderlying : PreservesLimits
          (internalHomSecondFunctor.{v, u, w, m} O F ⋙
            _root_.PresheafOfModules.evaluation.{max u v w m} (Oforget O) X ⋙
            forget (ModuleCat.{max u v w m} ((Oforget O).obj (op U)))) :=
        preservesLimits_of_natIso e
      exact @preservesLimits_of_reflects_of_preserves.{_, _, _, _, _, _, _, _}
        _ inferInstance _ inferInstance _ inferInstance
        (internalHomSecondFunctor.{v, u, w, m} O F ⋙
          _root_.PresheafOfModules.evaluation.{max u v w m} (Oforget O) X)
        (forget (ModuleCat.{max u v w m} ((Oforget O).obj (op U))))
        hUnderlying
        (ModuleCat.forget_reflectsLimitsOfSize.{0, max u v w m, w}))
    (by
      intro J hJ E X
      infer_instance)

end SecondVariable

end Stacks.PresheafOfModules.InternalHom

end
