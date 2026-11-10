module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.CechModuleSections
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing
public import StacksFrontier.CategoryTheory.Sites.CechComplexMap

/-!
# Base change of the sections of the Zariski Čech complex of `𝐆_a`

Let `f : X ⟶ S` be a morphism to an affine scheme and `V'` an affine scheme étale over `S`. For an
affine open `V ⊆ X`, the scheme `(V' ×_S X) ×_X V` is the fibre product of `V'` and
`(S ×_S X) ×_X V ≅ V` over `S`, so its ring of functions is the tensor product
`Γ(V') ⊗_{Γ(S)} Γ((S ×_S X) ×_X V)`.

Consequently the Čech complex of the `Γ(V')`-modules `V ↦ Γ((V' ×_S X) ×_X V)` is the extension
of scalars along `Γ(S) ⟶ Γ(V')` of that of the `Γ(S)`-modules `V ↦ Γ((S ×_S X) ×_X V)`, for a
finite family of opens with affine finite intersections.

## Main results

* `Stacks.ArtinSchreier.isPullback_openFibreMap`: the cartesian square.
* `Stacks.ArtinSchreier.extendScalarsIsoOfIsPushout`: a pushout of rings is a base change of
  modules.
* `Stacks.ArtinSchreier.isIso_fibreBaseChange_app`: the comparison
  `Γ(V') ⊗_{Γ(S)} Γ((S ×_S X) ×_X V) ⟶ Γ((V' ×_S X) ×_X V)` is an isomorphism.
* `Stacks.ArtinSchreier.cechFibreBaseChangeIso`: the base change of Čech complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology
open TopologicalSpace

universe u

namespace Stacks.ArtinSchreier

variable {X S : Scheme.{u}} (f : X ⟶ S) {T : Scheme.{u}} (t : T ⟶ S)

/-- The comparison `T ×_S X ⟶ S ×_S X`. -/
abbrev fibreMap : pullback t f ⟶ pullback (𝟙 S) f :=
  pullback.map t f (𝟙 S) f t (𝟙 X) (𝟙 S) (by simp) (by simp)

/-- Changing the left leg of a cospan along `m` with `m ≫ p' = p` gives a cartesian square. -/
private theorem isPullback_map_left {A B Y Z : Scheme.{u}} (p : A ⟶ Z) (g : Y ⟶ Z) (p' : B ⟶ Z)
    (m : A ⟶ B) (w : m ≫ p' = p) :
    IsPullback (pullback.map p g p' g m (𝟙 Y) (𝟙 Z) (by simp [w]) (by simp)) (pullback.fst p g)
      (pullback.fst p' g) m := by
  refine IsPullback.of_right (h₁₂ := pullback.snd p' g) (v₁₃ := g) (h₂₂ := p') ?_
    (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback p' g).flip
  rw [pullback.lift_snd, Category.comp_id, w]
  exact (IsPullback.of_hasPullback p g).flip

/-- The square `T ×_S X ⟶ S ×_S X` over `T ⟶ S` is cartesian. -/
theorem isPullback_fibreMap :
    IsPullback (fibreMap f t) (pullback.fst t f) (pullback.fst (𝟙 S) f) t :=
  isPullback_map_left t f (𝟙 S) t (Category.comp_id t)

variable (V : X.Opens)

/-- The comparison `(T ×_S X) ×_X V ⟶ (S ×_S X) ×_X V`. -/
abbrev openFibreMap : pullback (pullback.snd t f) V.ι ⟶ pullback (pullback.snd (𝟙 S) f) V.ι :=
  pullback.map (pullback.snd t f) V.ι (pullback.snd (𝟙 S) f) V.ι (fibreMap f t) (𝟙 _) (𝟙 X)
    (by rw [pullback.lift_snd, Category.comp_id]) (by simp)

/-- The square `(T ×_S X) ×_X V ⟶ (S ×_S X) ×_X V` over `T ×_S X ⟶ S ×_S X` is cartesian. -/
theorem isPullback_openFibreMap_fibreMap :
    IsPullback (openFibreMap f t V) (pullback.fst (pullback.snd t f) V.ι)
      (pullback.fst (pullback.snd (𝟙 S) f) V.ι) (fibreMap f t) :=
  isPullback_map_left _ V.ι _ _ (pullback.lift_snd _ _ _ |>.trans (Category.comp_id _))

/-- **`(T ×_S X) ×_X V` is the fibre product of `T` and `(S ×_S X) ×_X V` over `S`.** -/
theorem isPullback_openFibreMap :
    IsPullback (openFibreMap f t V) (pullback.fst (pullback.snd t f) V.ι ≫ pullback.fst t f)
      (pullback.fst (pullback.snd (𝟙 S) f) V.ι ≫ pullback.fst (𝟙 S) f) t :=
  (isPullback_openFibreMap_fibreMap f t V).paste_vert (isPullback_fibreMap f t)

/-- For an affine open `V ⊆ X`, the scheme `(S ×_S X) ×_X V` is affine. -/
instance isAffine_openFibre [IsAffine V] : IsAffine (pullback (pullback.snd (𝟙 S) f) V.ι) :=
  IsAffine.of_isPullback (IsPullback.of_hasPullback (pullback.snd (𝟙 S) f) V.ι).flip

section Pushout

open scoped ChangeOfRings TensorProduct

variable {R R' S' P : CommRingCat.{u}} {a : R ⟶ R'} {b : R ⟶ S'} {c : R' ⟶ P} {d : S' ⟶ P}

/-- **A pushout of commutative rings is a base change of modules**: for a pushout square
`R → R', R → S', R' → P, S' → P`, extending scalars of `R'` along `R → S'` gives `P`. -/
def extendScalarsIsoOfIsPushout (h : IsPushout a b c d) :
    (ModuleCat.extendScalars.{u, u, u} b.hom).obj (algebraModule a) ≅ algebraModule d := by
  letI := a.hom.toAlgebra
  letI := b.hom.toAlgebra
  letI := c.hom.toAlgebra
  letI := d.hom.toAlgebra
  letI : Algebra R P := (a ≫ c).hom.toAlgebra
  haveI : IsScalarTower R R' P := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R S' P :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  have hp : Algebra.IsPushout R R' S' P := CommRingCat.isPushout_iff_isPushout.mp h
  let hb := hp.symm.out
  let : IsScalarTower R S' ((ModuleCat.restrictScalars b.hom).obj (ModuleCat.of S' S') : Type u) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let eTensor : ((ModuleCat.extendScalars b.hom).obj (algebraModule a) : Type u) ≃ₗ[S']
      TensorProduct R S' R' :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S' S') (LinearEquiv.refl R R')
  exact eTensor.toModuleIso ≪≫ hb.equiv.toModuleIso

/-- The isomorphism `extendScalarsIsoOfIsPushout h` sends `1 ⊗ x` to `c x`. -/
theorem extendScalarsIsoOfIsPushout_hom_one_tmul (h : IsPushout a b c d) (x : algebraModule a) :
    (extendScalarsIsoOfIsPushout h).hom ((1 : S') ⊗ₜ[R, b.hom] x) = c.hom x := by
  let := a.hom.toAlgebra
  let := b.hom.toAlgebra
  let := c.hom.toAlgebra
  let := d.hom.toAlgebra
  let : Algebra R P := (a ≫ c).hom.toAlgebra
  have : IsScalarTower R R' P := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R S' P :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  have hp : Algebra.IsPushout R R' S' P := CommRingCat.isPushout_iff_isPushout.mp h
  change hp.symm.out.equiv ((1 : S') ⊗ₜ[R] (show R' from x)) = _
  rw [IsBaseChange.equiv_tmul, one_smul]
  rfl

end Pushout

section Comparison

open scoped ChangeOfRings TensorProduct

variable {X S : Scheme.{u}} (f : X ⟶ S) {T : Scheme.{u}} (t : T ⟶ S)

/-- The `Γ(S)`-modules `V ↦ Γ((S ×_S X) ×_X V)`. -/
abbrev baseSectionsPresheaf : X.Opensᵒᵖ ⥤ ModuleCat.{u} Γ(S, ⊤) :=
  sectionsModulePresheaf (pullback.snd (𝟙 S) f) (pullback.fst (𝟙 S) f)

/-- The `Γ(T)`-modules `V ↦ Γ((T ×_S X) ×_X V)`. -/
abbrev fibreSectionsPresheaf : X.Opensᵒᵖ ⥤ ModuleCat.{u} Γ(T, ⊤) :=
  sectionsModulePresheaf (pullback.snd t f) (pullback.fst t f)

/-- The comparisons `(T ×_S X) ×_X V ⟶ (S ×_S X) ×_X V` commute with restriction to an open
`V' ≤ V`. -/
theorem openFibreMap_naturality {V' V : X.Opens} (h : V' ≤ V) :
    pullbackOpenMap (pullback.snd t f) h ≫ openFibreMap f t V =
      openFibreMap f t V' ≫ pullbackOpenMap (pullback.snd (𝟙 S) f) h := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
  · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]

/-- Pulling a function on `S` back to `(S ×_S X) ×_X V` and then to `(T ×_S X) ×_X V` is
pulling it back to `T` and then to `(T ×_S X) ×_X V`. -/
theorem openFibreMap_appTop_comp (V : X.Opens) :
    (pullback.fst (pullback.snd (𝟙 S) f) V.ι ≫ pullback.fst (𝟙 S) f).appTop ≫
        (openFibreMap f t V).appTop =
      t.appTop ≫ (pullback.fst (pullback.snd t f) V.ι ≫ pullback.fst t f).appTop := by
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, (isPullback_openFibreMap f t V).w]

/-- Pullback of functions along `(T ×_S X) ×_X V ⟶ (S ×_S X) ×_X V`, a `Γ(S)`-linear map into
the restriction of scalars of the `Γ(T)`-module `Γ((T ×_S X) ×_X V)`. -/
def fibreRestriction (V : X.Opens) :
    (baseSectionsPresheaf f).obj (op V) ⟶
      (ModuleCat.restrictScalars t.appTop.hom).obj ((fibreSectionsPresheaf f t).obj (op V)) :=
  ConcreteCategory.ofHom (C := ModuleCat.{u} Γ(S, ⊤))
    { toFun := (openFibreMap f t V).appTop.hom
      map_add' := map_add _
      map_smul' := fun b x => by
        change (openFibreMap f t V).appTop.hom
            ((pullback.fst (pullback.snd (𝟙 S) f) V.ι ≫ pullback.fst (𝟙 S) f).appTop.hom b *
              (show Γ(pullback (pullback.snd (𝟙 S) f) V.ι, ⊤) from x)) =
          (pullback.fst (pullback.snd t f) V.ι ≫ pullback.fst t f).appTop.hom (t.appTop.hom b) *
            (openFibreMap f t V).appTop.hom x
        rw [map_mul]
        congr 1
        exact congrArg (fun φ : Γ(S, ⊤) ⟶ _ => φ.hom b) (openFibreMap_appTop_comp f t V) }

/-- Pullback of functions from `(S ×_S X) ×_X V` to `(T ×_S X) ×_X V`, natural in `V`. -/
def fibreRestrictionNatTrans :
    baseSectionsPresheaf f ⟶
      fibreSectionsPresheaf f t ⋙ ModuleCat.restrictScalars t.appTop.hom where
  app V := fibreRestriction f t V.unop
  naturality V V' h := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change (openFibreMap f t V'.unop).appTop.hom
        ((pullbackOpenMap (pullback.snd (𝟙 S) f) h.unop.le).appTop.hom x) =
      (pullbackOpenMap (pullback.snd t f) h.unop.le).appTop.hom
        ((openFibreMap f t V.unop).appTop.hom x)
    have e := congrArg (fun φ => Scheme.Hom.appTop φ)
      (openFibreMap_naturality f t h.unop.le)
    simp only [Scheme.Hom.comp_appTop] at e
    exact (congrArg (fun φ => CommRingCat.Hom.hom φ x) e).symm

/-- **The comparison `Γ(T) ⊗_{Γ(S)} Γ((S ×_S X) ×_X V) ⟶ Γ((T ×_S X) ×_X V)`**, natural in `V`. -/
def fibreBaseChange :
    baseSectionsPresheaf f ⋙ ModuleCat.extendScalars.{u, u, u} t.appTop.hom ⟶
      fibreSectionsPresheaf f t :=
  Functor.whiskerRight (fibreRestrictionNatTrans f t) (ModuleCat.extendScalars t.appTop.hom) ≫
    Functor.whiskerLeft (fibreSectionsPresheaf f t)
      (ModuleCat.extendRestrictScalarsAdj t.appTop.hom).counit

/-- The comparison `fibreBaseChange f t` sends `1 ⊗ x` to the pullback of `x` along
`(T ×_S X) ×_X V ⟶ (S ×_S X) ×_X V`. -/
theorem fibreBaseChange_app_one_tmul (V : X.Opens) (x : (baseSectionsPresheaf f).obj (op V)) :
    (fibreBaseChange f t).app (op V) ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤), t.appTop.hom] x) =
      (openFibreMap f t V).appTop.hom x :=
  ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul t.appTop.hom
    ((fibreSectionsPresheaf f t).obj (op V)) ((fibreRestriction f t V) x)

/-- **Over affine schemes the comparison is an isomorphism**: `Γ((T ×_S X) ×_X V)` is
`Γ(T) ⊗_{Γ(S)} Γ((S ×_S X) ×_X V)` for affine `S`, `T` and `V`. -/
theorem isIso_fibreBaseChange_app [IsAffine S] [IsAffine T] (V : X.Opens) [IsAffine V] :
    IsIso ((fibreBaseChange f t).app (op V)) := by
  have h := isPushout_appTop_of_isPullback (isPullback_openFibreMap f t V)
  have e : (fibreBaseChange f t).app (op V) = (extendScalarsIsoOfIsPushout h).hom := by
    refine ModuleCat.ExtendScalars.hom_ext_one_tmul _ fun x => ?_
    exact (fibreBaseChange_app_one_tmul f t V x).trans
      (extendScalarsIsoOfIsPushout_hom_one_tmul h x).symm
  rw [e]
  exact (extendScalarsIsoOfIsPushout h).isIso_hom

end Comparison

section Cech

open Stacks.CategoryTheory.CechComplex

variable {X S : Scheme.{u}} (f : X ⟶ S) {T : Scheme.{u}} (t : T ⟶ S) {ι : Type} [Finite ι]
  (U : ι → X.Opens)

/-- **The Čech complex of `V ↦ Γ((T ×_S X) ×_X V)` is the base change of that of
`V ↦ Γ((S ×_S X) ×_X V)`**, for affine `S`, `T` and a family of opens whose finite
intersections are affine. -/
def cechFibreBaseChangeIso [IsAffine S] [IsAffine T]
    (hU : ∀ (n : ℕ) (x : Fin (n + 1) → ι), IsAffineOpen (inter U x)) :
    ((ModuleCat.extendScalars.{u, u, u} t.appTop.hom).mapHomologicalComplex _).obj
        ((cechComplexFunctor U).obj (baseSectionsPresheaf f)) ≅
      (cechComplexFunctor U).obj (fibreSectionsPresheaf f t) :=
  haveI := isIso_cechComplexFunctor_map U (fibreBaseChange f t) fun n x =>
    haveI : IsAffine ((inter U x : X.Opens) : Scheme.{u}) := hU n x
    isIso_fibreBaseChange_app f t (inter U x)
  haveI : (ModuleCat.extendScalars.{u, u, u} t.appTop.hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} t.appTop.hom).left_adjoint_additive
  mapCechIso (ModuleCat.extendScalars.{u, u, u} t.appTop.hom) U (baseSectionsPresheaf f) ≪≫
    asIso ((cechComplexFunctor U).map (fibreBaseChange f t))

end Cech

end Stacks.ArtinSchreier

end
