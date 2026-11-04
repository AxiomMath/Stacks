module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticExtension

/-!
# The extension from a subcategory of a chaotic site is left adjoint to restriction

Let `F : C' ⥤ C` be a functor of chaotic sites such that every category `U/F` of arrows
`U → F U'` is cofiltered, let `(A, d)` be a sheaf of differential graded algebras on `C` and
`(A', d)` its restriction to `C'`. The extension
`E(X)(U) = colim_{U → F U'} X(U') ⊗_{A(F U')} A(U)` of a presheaf of section modules `X` along `F`
is left adjoint to the restriction `Y ↦ (U' ↦ Y(F U'))`. The unit `X(U') → E(X)(F U')` is
`x ↦ x ⊗ 1` at the identity arrow of `F U'`, and the counit `E(Y|_{C'})(U) → Y(U)` is
`x ⊗ c ↦ x|_U · c`. When `F` is fully faithful the identity arrow of `F U'` is an initial object
of `F U'/F`, so the colimit over `F U'` is attained there and the unit is an isomorphism.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.unit`: the unit `X ⟶ E(X)|_{C'}`.
* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.counit`: the counit
  `E(Y|_{C'}) ⟶ Y`, assembled from the comparison maps `Y(F U') ⊗_{A(F U')} A(U) ⟶ Y(U)`.
* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.adjunction`: **the extension is left
  adjoint to the restriction.**

## Main results

* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.isIso_unit`: for a fully faithful
  `F` the unit is an isomorphism.

## References

* [Stacks Project, Lemma 24.34.1 (Tag 0GZE)](https://stacks.math.columbia.edu/tag/0GZE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf CategoryTheory.Limits
open DifferentialGradedModule (restrictScalarsFunctor restrictScalarsIdHom restrictScalarsIdInv)
open DifferentialGraded.Bimodule (tensorCompFunctor regular tensorPure plainTranspose
  tensorSquareMap unitHom restrictScalarsCongr)

universe u

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

namespace SheafOfModules

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

namespace DifferentialGradedModule.ChaoticExtension

variable {C : Type u} [Category.{u} C] {C' : Type u} [Category.{u} C'] {F : C' ⥤ C}
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  {A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
  [∀ U : C, IsCofiltered (StructuredArrow U F)]

/-- A homomorphism of differential graded modules is determined by its values on homogeneous
elements. -/
theorem hom_ext_homogeneous {B : _root_.DifferentialGradedAlgebra.{u, u} (ULift.{u} ℤ)}
    {M N : _root_.DifferentialGradedModule.{u, u, u} B} {f g : M ⟶ N}
    (h : ∀ (p : ℤ) (x : M.grading p), f.toFun x = g.toFun x) : f = g := by
  refine _root_.DifferentialGradedModule.Hom.ext (DFunLike.ext _ _ fun x => ?_)
  induction x using DirectSum.Decomposition.inductionOn M.grading with
  | zero => exact (map_zero f.toFun).trans (map_zero g.toFun).symm
  | add x x' hx hx' =>
    exact (map_add f.toFun x x').trans
      ((congrArg₂ (· + ·) hx hx').trans (map_add g.toFun x x').symm)
  | @homogeneous p x => exact h p x

/-! ### The unit -/

variable (F) in
/-- The identity arrow of `F U'`, an object of `F U'/F`. -/
abbrev idArrow (U' : C'ᵒᵖ) : StructuredArrow (F.op.obj U').unop F :=
  StructuredArrow.mk (𝟙 (F.obj U'.unop))

/-- The restriction map of `A` along the identity arrow of `F U'` is the identity. -/
theorem arrowHom_idArrow (U' : C'ᵒᵖ) (y : (A.sectionAlgebra (F.op.obj U')).A) :
    (arrowHom F A (idArrow F U')).toAlgebraHom y =
      (_root_.DifferentialGradedAlgebra.Hom.id _).toAlgebraHom y :=
  sectionRestriction_id_apply A _ _

variable (X : AlongSystem F A)

/-- **The unit over `U'`**: `x ↦ x ⊗ 1` at the identity arrow of `F U'`. -/
def unitApp (U' : C'ᵒᵖ) : X.obj U' ⟶ (restrictSystem F (extSystem X)).obj U' :=
  unitHom (arrowHom F A (idArrow F U')) (X.obj U') ≫
    (restrictScalarsFunctor (arrowHom F A (idArrow F U'))).map
      (_root_.DifferentialGradedModule.FilteredColimit.ι (diagram X (F.op.obj U'))
        (Opposite.op (idArrow F U'))) ≫
    restrictScalarsCongr (arrowHom_idArrow U') _ ≫ restrictScalarsIdHom _

/-- The unit over `U'` sends `x` to the germ of `x ⊗ 1` at the identity arrow of `F U'`. -/
theorem unitApp_apply (U' : C'ᵒᵖ) (x : (X.obj U').M) :
    (unitApp X U').toFun x =
      germ X (idArrow F U') (pure X (idArrow F U') x (1 : (A.sectionAlgebra (F.op.obj U')).A)) :=
  congrArg (germ X (idArrow F U')) (DifferentialGraded.Bimodule.unitHom_apply _ _ x)

/-- The morphism of `F U'/F` from the identity arrow to the composite `F U' → F V' = F V'`. -/
abbrev idArrowHom {U' V' : C'ᵒᵖ} (a : V' ⟶ U') :
    idArrow F U' ⟶ pre F (F.op.map a) (idArrow F V') :=
  StructuredArrow.homMk a.unop (by simp)

/-- For `a : V' ⟶ U'` and a homogeneous `x ∈ X(V')`, restricting the germ of `x ⊗ 1` at the
identity arrow of `F V'` along `F a` gives the germ of `x|_{U'} ⊗ 1` at the identity arrow of
`F U'`. -/
theorem unit_naturality_aux {U' V' : C'ᵒᵖ} (a : V' ⟶ U') (p : ℤ) (x : (X.obj V').grading p) :
    germ X (pre F (F.op.map a) (idArrow F V'))
        ((restrLeg X (F.op.map a) (idArrow F V')).toFun
          (pure X (idArrow F V') (x : (X.obj V').M) (1 : (A.sectionAlgebra (F.op.obj V')).A))) =
      germ X (idArrow F U')
        (pure X (idArrow F U') (X.restrFun a x) (1 : (A.sectionAlgebra (F.op.obj U')).A)) := by
  refine (congrArg (germ X (pre F (F.op.map a) (idArrow F V')))
    (restrLeg_pure X (F.op.map a) (idArrow F V') p x 1)).trans ?_
  refine (germ_transition X (idArrowHom a) _).symm.trans ?_
  refine congrArg (germ X (idArrow F U')) ((transition_pure X (idArrowHom a) p x _).trans ?_)
  exact congrArg (fun c : (A.sectionAlgebra (F.op.obj U')).A => pure X (idArrow F U')
    (X.restrFun a x) c) (map_one (A.sectionRestriction (F.op.map a)).toAlgebraHom)

/-- **The unit**, a morphism of presheaves of section modules `X ⟶ E(X)|_{C'}`. -/
def unit : X ⟶ restrictSystem F (extSystem X) where
  app U' := unitApp X U'
  naturality {U' V'} a x := by
    have key : unitApp X V' ≫ (restrictSystem F (extSystem X)).restr a =
        X.restr a ≫ (restrictScalarsFunctor (A.sectionRestriction (F.op.map a))).map
          (unitApp X U') := hom_ext_homogeneous fun p x => by
      change (extSystem X).restrFun (F.op.map a) ((unitApp X V').toFun x) =
        (unitApp X U').toFun (X.restrFun a x)
      refine (congrArg ((extSystem X).restrFun (F.op.map a)) (unitApp_apply X V' x)).trans ?_
      refine (extSystem_restrFun_germ X (F.op.map a) (idArrow F V') _).trans ?_
      refine Eq.trans ?_ (unitApp_apply X U' _).symm
      exact unit_naturality_aux X a p x
    exact congrArg (fun f => f.toFun x) key

/-! ### The counit -/

variable (F) (Y : SectionSystem A)

/-- The comparison `Y(F U') ⟶ Y(U)_{A'(U')}` along an arrow `U → F U'`, read over `A'(U')`. -/
abbrev counitInner {U : Cᵒᵖ} (b : StructuredArrow U.unop F) :
    (restrictSystem F Y).obj (Opposite.op b.right) ⟶
      (restrictScalarsFunctor (arrowHom F A b)).obj (Y.obj U) :=
  Y.restr b.hom.op

/-- **The leg of the counit at `b : U → F U'`**: `x ⊗ c ↦ x|_U · c`. -/
def counitLeg {U : Cᵒᵖ} (b : StructuredArrow U.unop F) :
    term (restrictSystem F Y) b ⟶ Y.obj U :=
  plainTranspose (arrowHom F A b) (counitInner F Y b)

/-- The leg of the counit at `b : U → F U'` sends `x ⊗ c` to `x|_U · c`. -/
theorem counitLeg_pure {U : Cᵒᵖ} (b : StructuredArrow U.unop F) (p : ℤ)
    (x : ((restrictSystem F Y).obj (Opposite.op b.right)).grading p)
    (c : (A.sectionAlgebra U).A) :
    (counitLeg F Y b).toFun
        (pure (restrictSystem F Y) b
          (x : ((restrictSystem F Y).obj (Opposite.op b.right)).M) c) =
      MulOpposite.op c • Y.restrFun b.hom.op
        (x : ((restrictSystem F Y).obj (Opposite.op b.right)).M) :=
  DifferentialGraded.Bimodule.plainTranspose_pure (arrowHom F A b) (counitInner F Y b) p x c

/-- The legs of the counit are compatible with the transition maps of the diagram over `U/F`. -/
theorem transition_counitLeg {U : Cᵒᵖ} {b b' : StructuredArrow U.unop F} (g : b' ⟶ b) :
    transition (restrictSystem F Y) g ≫ counitLeg F Y b' = counitLeg F Y b := by
  refine (Category.assoc _ _ _).trans ?_
  refine DifferentialGraded.Bimodule.tensorSquareMap_comp_plainTranspose _ _ _
    (arrowHom_map F A g) _ _ _ ?_
  intro y
  have hw : F.op.map g.right.op ≫ b'.hom.op = b.hom.op :=
    congrArg Quiver.Hom.op (StructuredArrow.w g)
  have h := Y.restr_comp b'.hom.op (F.op.map g.right.op) y
  rw [hw] at h
  exact h.symm

/-- The cocone over the diagram of `Y|_{C'}` at `U` with vertex `Y(U)`. -/
def counitCocone (U : Cᵒᵖ) : Cocone (diagram (restrictSystem F Y) U) where
  pt := Y.obj U
  ι :=
    { app j := counitLeg F Y j.unop
      naturality {i j} g := (transition_counitLeg F Y g.unop).trans (Category.comp_id _).symm }

/-- **The counit over `U`**: `colim_{U → F U'} Y(F U') ⊗_{A(F U')} A(U) ⟶ Y(U)`. -/
def counitApp (U : Cᵒᵖ) : (extSystem (restrictSystem F Y)).obj U ⟶ Y.obj U :=
  _root_.DifferentialGradedModule.FilteredColimit.desc _ (counitCocone F Y U)

/-- The counit over `U` agrees on the germ at `b : U → F U'` with the leg of the counit at `b`. -/
theorem counitApp_germ {U : Cᵒᵖ} (b : StructuredArrow U.unop F)
    (z : (term (restrictSystem F Y) b).M) :
    (counitApp F Y U).toFun (germ (restrictSystem F Y) b z) = (counitLeg F Y b).toFun z :=
  _root_.DifferentialGradedModule.FilteredColimit.desc_germ (diagram _ U) (counitCocone F Y U)
    (Opposite.op b) z

/-- For `a : V ⟶ U` and `b : V → F U'`, the leg of the counit at `b` followed by restriction
along `a` equals restriction of the term at `b` followed by the leg of the counit at the
composite arrow `U → V → F U'`. -/
theorem counitLeg_restrict {U V : Cᵒᵖ} (a : V ⟶ U) (b : StructuredArrow V.unop F) :
    counitLeg F Y b ≫ Y.restr a =
      restrLeg (restrictSystem F Y) a b ≫
        (restrictScalarsFunctor (A.sectionRestriction a)).map (counitLeg F Y (pre F a b)) :=
  DifferentialGraded.Bimodule.plainTranspose_comp_restrict _ _ _ (arrowHom_pre F A a b) _ _ _
    fun y => (Y.restr_comp a b.hom.op y).symm

/-- **The counit**, a morphism of presheaves of section modules `E(Y|_{C'}) ⟶ Y`. -/
def counit : extSystem (restrictSystem F Y) ⟶ Y where
  app U := counitApp F Y U
  naturality {U V} a z := by
    obtain ⟨j, w, rfl⟩ := _root_.DifferentialGradedModule.FilteredColimit.exists_germ _ z
    change Y.restrFun a ((counitApp F Y V).toFun (germ (restrictSystem F Y) j.unop w)) =
      (counitApp F Y U).toFun ((extSystem (restrictSystem F Y)).restrFun a
        (germ (restrictSystem F Y) j.unop w))
    refine (congrArg (Y.restrFun a) (counitApp_germ F Y j.unop w)).trans ?_
    refine Eq.trans ?_ (congrArg (counitApp F Y U).toFun
      (extSystem_restrFun_germ (restrictSystem F Y) a j.unop w)).symm
    refine Eq.trans ?_ (counitApp_germ F Y (pre F a j.unop) _).symm
    exact congrArg (fun f => f.toFun w) (counitLeg_restrict F Y a j.unop)

/-! ### The adjunction -/

variable {F}

/-- The unit over `U'` is natural in the presheaf of section modules `X`. -/
theorem unitApp_naturality {X X' : AlongSystem F A} (f : X ⟶ X') (U' : C'ᵒᵖ) :
    f.app U' ≫ unitApp X' U' = unitApp X U' ≫ ((restrictFunctor F A).map (extMap f)).app U' :=
  _root_.DifferentialGradedModule.Hom.ext (DFunLike.ext _ _ fun x => by
    change (unitApp X' U').toFun ((f.app U').toFun x) =
      ((extMap f).app (F.op.obj U')).toFun ((unitApp X U').toFun x)
    refine (unitApp_apply X' U' _).trans ?_
    refine Eq.trans ?_ (congrArg ((extMap f).app (F.op.obj U')).toFun (unitApp_apply X U' x)).symm
    refine Eq.trans ?_ (extMap_germ f (idArrow F U') _).symm
    exact congrArg (germ X' (idArrow F U')) (termMap_pure f (idArrow F U') x 1).symm)

variable (F A) in
/-- The unit, as a natural transformation. -/
def unitNat : 𝟭 (AlongSystem F A) ⟶ extFunctor F A ⋙ restrictFunctor F A where
  app X := unit X
  naturality _ _ f := AlongSystem.hom_ext fun U' => unitApp_naturality f U'

/-- The leg of the counit at `b : U → F U'` is natural in the presheaf of section modules `Y`. -/
theorem counitLeg_naturality {Y Y' : SectionSystem A} (g : Y ⟶ Y') {U : Cᵒᵖ}
    (b : StructuredArrow U.unop F) :
    termMap (restrictMap F g) b ≫ counitLeg F Y' b = counitLeg F Y b ≫ g.app U := by
  refine (DifferentialGraded.Bimodule.plainTranspose_naturality_left _ _ _).symm.trans ?_
  refine Eq.trans ?_ (DifferentialGraded.Bimodule.plainTranspose_naturality_right _ _ _)
  congr 1
  exact _root_.DifferentialGradedModule.Hom.ext (DFunLike.ext _ _ fun x =>
    g.naturality b.hom.op x)

variable (F A) in
/-- The counit, as a natural transformation. -/
def counitNat : restrictFunctor F A ⋙ extFunctor F A ⟶ 𝟭 (SectionSystem A) where
  app Y := counit F Y
  naturality {Y Y'} g := SectionSystem.hom_ext fun U =>
    _root_.DifferentialGradedModule.FilteredColimit.hom_ext _
      fun j (w : (term (restrictSystem F Y) j.unop).M) => by
      change (counitApp F Y' U).toFun (((extMap (restrictMap F g)).app U).toFun
          (germ (restrictSystem F Y) j.unop w)) =
        (g.app U).toFun ((counitApp F Y U).toFun (germ (restrictSystem F Y) j.unop w))
      refine (congrArg (counitApp F Y' U).toFun (extMap_germ (restrictMap F g) j.unop w)).trans ?_
      refine (counitApp_germ F Y' j.unop _).trans ?_
      refine Eq.trans ?_ (congrArg (g.app U).toFun (counitApp_germ F Y j.unop w)).symm
      exact congrArg (fun f => f.toFun w) (counitLeg_naturality g j.unop)

/-- The identification of the identity arrow of `F U'` precomposed with `U → F U'` with the
arrow itself. -/
abbrev preIdArrowHom {U : Cᵒᵖ} (b : StructuredArrow U.unop F) :
    pre F b.hom.op (idArrow F (Opposite.op b.right)) ⟶ b :=
  StructuredArrow.homMk (𝟙 b.right) (by simp)

/-- For `b : U → F U'`, the unit over `U'` followed by restriction of `E(X)` along `b` sends
`x` to the germ of `x ⊗ 1` at `b`. -/
theorem unitApp_counitInner (X : AlongSystem F A) {U : Cᵒᵖ} (b : StructuredArrow U.unop F) :
    unitApp X (Opposite.op b.right) ≫ counitInner F (extSystem X) b =
      unitHom (arrowHom F A b) (X.obj (Opposite.op b.right)) ≫
        (restrictScalarsFunctor (arrowHom F A b)).map
          (_root_.DifferentialGradedModule.FilteredColimit.ι (diagram X U) (Opposite.op b)) :=
  hom_ext_homogeneous fun p x => by
    change (extSystem X).restrFun b.hom.op ((unitApp X (Opposite.op b.right)).toFun x) =
      germ X b ((unitHom (arrowHom F A b) (X.obj (Opposite.op b.right))).toFun x)
    refine (congrArg ((extSystem X).restrFun b.hom.op)
      (unitApp_apply X (Opposite.op b.right) x)).trans ?_
    refine (extSystem_restrFun_germ X b.hom.op _ _).trans ?_
    refine (congrArg (germ X (pre F b.hom.op (idArrow F (Opposite.op b.right))))
      (restrLeg_pure X b.hom.op (idArrow F (Opposite.op b.right)) p x 1)).trans ?_
    refine Eq.trans ?_ (congrArg (germ X b)
      (DifferentialGraded.Bimodule.unitHom_apply _ _ (x : (X.obj (Opposite.op b.right)).M))).symm
    refine Eq.trans ?_ (germ_transition X (preIdArrowHom b) _)
    refine congrArg (germ X (pre F b.hom.op (idArrow F (Opposite.op b.right))))
      (Eq.trans ?_ (transition_pure X (preIdArrowHom b) p x 1).symm)
    refine congrArg₂ (fun w c => pure X (pre F b.hom.op (idArrow F (Opposite.op b.right))) w c)
      (X.restr_id _ (x : (X.obj (Opposite.op b.right)).M)).symm ?_
    exact map_one (A.sectionRestriction b.hom.op).toAlgebraHom

/-- For `b : U → F U'`, the unit applied to the term at `b`, followed by the leg of the counit
of `E(X)` at `b`, is the colimit inclusion at `b`. -/
theorem left_triangle_app (X : AlongSystem F A) {U : Cᵒᵖ} (b : StructuredArrow U.unop F) :
    termMap (unit X) b ≫ counitLeg F (extSystem X) b =
      _root_.DifferentialGradedModule.FilteredColimit.ι (diagram X U) (Opposite.op b) := by
  refine (DifferentialGraded.Bimodule.plainTranspose_naturality_left _ _ _).symm.trans ?_
  refine (congrArg (plainTranspose (arrowHom F A b)) (unitApp_counitInner X b)).trans ?_
  exact DifferentialGraded.Bimodule.plainTranspose_unitHom_comp _ _

/-- **The extension is left adjoint to the restriction**, on presheaves of section modules. -/
def adjunction : extFunctor F A ⊣ restrictFunctor F A where
  unit := unitNat F A
  counit := counitNat F A
  left_triangle_components X := SectionSystem.hom_ext fun U =>
    _root_.DifferentialGradedModule.FilteredColimit.hom_ext _
      fun j (w : (term X j.unop).M) => by
      change (counitApp F (extSystem X) U).toFun (((extMap (unit X)).app U).toFun
          (germ X j.unop w)) = germ X j.unop w
      refine (congrArg (counitApp F (extSystem X) U).toFun (extMap_germ (unit X) j.unop w)).trans ?_
      refine (counitApp_germ F (extSystem X) j.unop _).trans ?_
      exact congrArg (fun f => f.toFun w) (left_triangle_app X j.unop)
  right_triangle_components Y := AlongSystem.hom_ext fun U' => hom_ext_homogeneous
    fun p (x : ((restrictSystem F Y).obj U').grading p) => by
    change (counitApp F Y (F.op.obj U')).toFun
      ((unitApp (restrictSystem F Y) U').toFun (x : ((restrictSystem F Y).obj U').M)) =
        (x : ((restrictSystem F Y).obj U').M)
    refine (congrArg (counitApp F Y (F.op.obj U')).toFun
      (unitApp_apply (restrictSystem F Y) U' _)).trans ?_
    refine (counitApp_germ F Y (idArrow F U') _).trans ?_
    refine (counitLeg_pure F Y (idArrow F U') p x 1).trans ?_
    rw [MulOpposite.op_one, one_smul]
    exact Y.restr_id (F.op.obj U') x.1

/-- The unit of `adjunction` at `X` is `unit X`. -/
theorem adjunction_unit_app (X : AlongSystem F A) : (adjunction (A := A)).unit.app X = unit X :=
  rfl

/-- The counit of `adjunction` at `Y` is `counit F Y`. -/
theorem adjunction_counit_app (Y : SectionSystem A) :
    (adjunction (F := F)).counit.app Y = counit F Y :=
  rfl

/-! ### The unit is an isomorphism for a fully faithful functor -/

/-- A morphism of presheaves of section modules along `F` all of whose components are bijective
is an isomorphism. -/
theorem AlongSystem.isIso_of_bijective {X Y : AlongSystem F A} (f : X ⟶ Y)
    (hf : ∀ U', Function.Bijective (f.app U').toFun) : IsIso f := by
  let e : ∀ U', X.obj U' ≅ Y.obj U' := fun U' =>
    _root_.DifferentialGradedModule.Hom.isoOfBijective (f.app U') (hf U')
  refine ⟨⟨⟨fun U' => (e U').inv, fun {U' V'} a y => ?_⟩, ?_, ?_⟩⟩
  · apply (hf U').injective
    have h : ∀ (W : C'ᵒᵖ) z, (f.app W).toFun ((e W).inv.toFun z) = z := fun W z =>
      congrArg (fun g => g.toFun z) (e W).inv_hom_id
    change (f.app U').toFun (X.restrFun a ((e V').inv.toFun y)) =
      (f.app U').toFun ((e U').inv.toFun (Y.restrFun a y))
    rw [← f.naturality, h V', h U']
  · exact AlongSystem.hom_ext fun U' => (e U').hom_inv_id
  · exact AlongSystem.hom_ext fun U' => (e U').inv_hom_id

/-- For a fully faithful `F`, the unit over each `U'` is bijective. -/
theorem bijective_unitApp [F.Full] [F.Faithful] (X : AlongSystem F A) (U' : C'ᵒᵖ) :
    Function.Bijective (unitApp X U').toFun := by
  have h1 := DifferentialGraded.Bimodule.bijective_unitHom (arrowHom F A (idArrow F U'))
    (_root_.DifferentialGradedAlgebra.Hom.id _) (fun y => sectionRestriction_id_apply A _ y)
    (fun y => sectionRestriction_id_apply A _ y) (X.obj U')
  have h2 := _root_.DifferentialGradedModule.FilteredColimit.bijective_ι_of_isTerminal
    (T := diagram X (F.op.obj U')) (StructuredArrow.mkIdInitial (T := F) (Y := U'.unop)).op
  have e : ⇑(unitApp X U').toFun =
      ⇑(_root_.DifferentialGradedModule.FilteredColimit.ι (diagram X (F.op.obj U'))
        (Opposite.op (idArrow F U'))).toFun ∘
        ⇑(unitHom (arrowHom F A (idArrow F U')) (X.obj U')).toFun := rfl
  rw [e]
  exact h2.comp h1

/-- For a fully faithful `F`, the unit `X ⟶ E(X)|_{C'}` is an isomorphism. -/
instance isIso_unit [F.Full] [F.Faithful] (X : AlongSystem F A) : IsIso (unit X) :=
  AlongSystem.isIso_of_bijective _ fun U' => bijective_unitApp X U'

/-- For a fully faithful `F`, the unit of `adjunction` is an isomorphism. -/
instance isIso_adjunction_unit [F.Full] [F.Faithful] : IsIso (adjunction (F := F) (A := A)).unit :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun X => isIso_unit X

end DifferentialGradedModule.ChaoticExtension

end SheafOfModules

end
