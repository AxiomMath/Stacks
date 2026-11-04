module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorHomAdjunctionFreeUniverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UliftTensorPresheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom

/-!
# The tensor--internal-Hom adjunction at the module universe of an essentially small ringed site

On a ringed site `X` whose objects lie one universe above its morphisms and the sections of its
structure sheaf — the shape of the small Zariski and the small étale site of a scheme, which are
`AlgebraicGeometry.RingedSite.{u + 1, u, u}` — the internal Hom of Stacks 03EM of two
`𝒪`-modules with sections in `u` has its own sections in `u + 1`, its sections over an object
being the morphisms on a slice of a category of objects in `Type (u + 1)`.  The sheaf clause of
Stacks 03EO at a free ring universe,
`Stacks.SheafOfModules.InternalHom.FreeUniverse.sheafTensorRightHomAdjunction`, is therefore
available there only at module universe `u + 1`, whereas `𝓕 ↦ 𝓕^a` and the tensor product of
Stacks 03EL both stay at `u`.

When the site is essentially small at `u` the internal Hom descends to `u`
(`AlgebraicGeometry.RingedSite.internalHomSheafSmall`), and so does the adjunction: the
sectionwise universe lift is fully faithful and carries both the internal Hom and the tensor
product to the corresponding constructions one universe up, so Stacks 03EO holds for the
`𝒪`-modules with sections in `u`.

## Main definitions

* `Stacks.SheafOfModules.InternalHomUlift.liftForInternalHom`, `internalHomUliftDown` and
  `internalHomUliftUp`: the sectionwise universe lift of a presheaf of modules into the universe
  of the internal Hom, and the two directions of the resulting bijection on local morphisms.
* `AlgebraicGeometry.RingedSite.moduleUliftForInternalHom` and `moduleUliftSmallSite`: that lift
  for sheaves of modules on a ringed site, in general and at the universes of a small site of a
  scheme.
* `AlgebraicGeometry.RingedSite.tensorRightModules` and `tensorRightModulesLift`: tensoring on
  the right by a module, and by its lift one universe up.
* `AlgebraicGeometry.RingedSite.tensorLiftPresheafHom` and `tensorLiftModulesNatTrans`: the
  comparison `𝓜^lift ⊗ 𝓕^lift ⟶ (𝓜 ⊗ 𝓕)^lift`, at the level of presheaves and of sheaves.

## Main results

* `Stacks.SheafOfModules.InternalHomUlift.internalHomUliftIso` and
  `AlgebraicGeometry.RingedSite.internalHomSheafUliftIso`: the internal Hom does not see the
  universe lift, for presheaves and for sheaves of modules, with
  `AlgebraicGeometry.RingedSite.internalHomPost_internalHomSheafUliftIso` its naturality in the
  second variable.
* `Stacks.SheafOfModules.UliftTensor.tensorUliftIso` and `tensorUliftIso_naturality`: the lift
  of the objectwise tensor product, with its naturality in the first variable.
* `PresheafOfModules.uliftSheafifyUnit_naturality`: the lift of the sheafification unit is
  natural.
* `AlgebraicGeometry.RingedSite.tensorLiftModulesNatIso`: the universe lift commutes with the
  tensor product of sheaves of modules, as an isomorphism of functors.
* `AlgebraicGeometry.RingedSite.internalHomSheafSmallLiftNatIso`: the lift carries the descended
  internal Hom to the internal Hom.
* `AlgebraicGeometry.RingedSite.sheafTensorRightInternalHomSmallAdjunction`: Stacks 03EO for
  the `𝒪`-modules with sections in the universe of the schemes on an essentially small ringed
  site whose objects lie one universe up.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

open scoped TensorProduct

universe u v w m t

namespace Stacks.SheafOfModules.InternalHomUlift

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The sectionwise universe lift of a presheaf of modules, raising the module universe `m` to
`max u v m`, the universe in which the internal Hom of Stacks 03EM lives. -/
abbrev liftForInternalHom (M : PresheafOfModules.{m} (Oforget O)) :
    PresheafOfModules.{max u v m} (Oforget O) :=
  UliftTensor.presheafUlift.{u, v, w, m, max u v} M

/-- Pushing a morphism of the universe lifts of two presheaves of modules, on a slice, down
to a morphism of the presheaves themselves. -/
def internalHomUliftDown (F G : PresheafOfModules.{m} (Oforget O)) (U : C)
    (α : (restrFun O U).obj (liftForInternalHom F) ⟶ (restrFun O U).obj (liftForInternalHom G)) :
    (restrFun O U).obj F ⟶ (restrFun O U).obj G where
  app X := ModuleCat.ofHom
    (X := ((restrFun O U).obj F).obj X) (Y := ((restrFun O U).obj G).obj X)
    { toFun := fun x => (α.app X (ULift.up x)).down
      map_add' := fun x y => congrArg ULift.down
        (map_add (α.app X).hom (ULift.up x) (ULift.up y))
      map_smul' := fun r x => congrArg ULift.down
        (map_smul (α.app X).hom r (ULift.up x)) }
  naturality {X Y} g := by
    ext x
    exact congrArg ULift.down (PresheafOfModules.naturality_apply α g (ULift.up x))

/-- Lifting a morphism of two presheaves of modules, on a slice, to a morphism of their
universe lifts. -/
def internalHomUliftUp (F G : PresheafOfModules.{m} (Oforget O)) (U : C)
    (α : (restrFun O U).obj F ⟶ (restrFun O U).obj G) :
    (restrFun O U).obj (liftForInternalHom F) ⟶ (restrFun O U).obj (liftForInternalHom G) where
  app X := ModuleCat.ofHom
    (X := ((restrFun O U).obj (liftForInternalHom F)).obj X)
    (Y := ((restrFun O U).obj (liftForInternalHom G)).obj X)
    { toFun := fun x => ULift.up (α.app X x.down)
      map_add' := fun x y => congrArg ULift.up (map_add (α.app X).hom x.down y.down)
      map_smul' := fun r x => congrArg ULift.up ((α.app X).hom.map_smul r x.down) }
  naturality {X Y} g := by
    ext x
    exact congrArg ULift.up (PresheafOfModules.naturality_apply α g x.down)

/-- The internal Hom of the universe lifts of two presheaves of modules is the internal Hom of
the presheaves themselves. -/
def internalHomUliftIso (F G : PresheafOfModules.{m} (Oforget O)) :
    internalHom O (liftForInternalHom F) (liftForInternalHom G) ≅ internalHom O F G := by
  refine PresheafOfModules.isoMk (fun U => ?_) ?_
  · exact (LinearEquiv.mk
      { toFun := internalHomUliftDown F G U.unop
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
      (internalHomUliftUp F G U.unop)
      (fun _ => rfl) (fun _ => rfl) :
      internalHomObj O (liftForInternalHom F) (liftForInternalHom G) U.unop ≃ₗ[(Oforget O).obj U]
        internalHomObj O F G U.unop).toModuleIso
  · intro _ _ _
    rfl

end Stacks.SheafOfModules.InternalHomUlift

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules.InternalHomUlift

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})

/-- The sectionwise universe lift of sheaves of modules on a ringed site, raising the module
universe `m` to `max u v m`, the universe in which the internal Hom of Stacks 03EM lives. -/
abbrev moduleUliftForInternalHom :
    SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{max u v m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  Stacks.SheafOfModules.moduleULift.{max u v, m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- The internal Hom sheaf of the universe lifts of two sheaves of modules is the internal Hom
sheaf of the sheaves themselves. -/
def internalHomSheafUliftIso
    (A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    internalHomSheaf X ((moduleUliftForInternalHom X).obj A) ((moduleUliftForInternalHom X).obj B) ≅
      internalHomSheaf X A B :=
  (SheafOfModules.fullyFaithfulForget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).preimageIso
    (internalHomUliftIso (O := X.O.obj) A.val B.val)

/-- The comparison of `AlgebraicGeometry.RingedSite.internalHomSheafUliftIso` is natural in the
second variable: postcomposition with a morphism commutes with it. -/
theorem internalHomPost_internalHomSheafUliftIso
    (A : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {B B' : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : B ⟶ B') :
    internalHomPost X (A := (moduleUliftForInternalHom X).obj A)
          ((moduleUliftForInternalHom X).map f) ≫
        (internalHomSheafUliftIso X A B').hom =
      (internalHomSheafUliftIso X A B).hom ≫ internalHomPost X (A := A) f :=
  rfl

end AlgebraicGeometry.RingedSite

namespace Stacks.SheafOfModules.UliftTensor

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The universe lift commutes with the objectwise tensor product: the tensor product of the
lifts is the lift of the tensor product, the comparison being `ULift.up` and `ULift.down` on each
factor. -/
def tensorUliftIso (F G : PresheafOfModules.{m} (O ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.tensorObj (PresheafOfModules.uliftObj.{_, _, _, _, t} F)
        (PresheafOfModules.uliftObj.{_, _, _, _, t} G) ≅
      PresheafOfModules.uliftObj.{_, _, _, _, t} (PresheafOfModules.tensorObj F G) :=
  PresheafOfModules.isoMk
    (fun _ ↦ ((TensorProduct.congr ULift.moduleEquiv ULift.moduleEquiv).trans
      ULift.moduleEquiv.symm).toModuleIso)
    (fun _ _ _ ↦ ModuleCat.tensor_ext fun _ _ ↦ rfl)

/-- `Stacks.SheafOfModules.UliftTensor.tensorUliftIso` is natural in its first variable. -/
theorem tensorUliftIso_naturality
    {M N : PresheafOfModules.{m} (O ⋙ forget₂ CommRingCat RingCat)} (f : M ⟶ N)
    (G : PresheafOfModules.{m} (O ⋙ forget₂ CommRingCat RingCat)) :
    ((PresheafOfModules.tensorBifunctor O).flip.obj
        (PresheafOfModules.uliftObj.{_, _, _, _, t} G)).map
          (PresheafOfModules.uliftMap.{_, _, _, _, t} f) ≫
        (tensorUliftIso.{u, v, w, m, t} N G).hom =
      (tensorUliftIso.{u, v, w, m, t} M G).hom ≫
        PresheafOfModules.uliftMap.{_, _, _, _, t}
          (((PresheafOfModules.tensorBifunctor O).flip.obj G).map f) :=
  PresheafOfModules.hom_ext fun _ ↦ ModuleCat.tensor_ext fun _ _ ↦ rfl

end Stacks.SheafOfModules.UliftTensor

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{w}} {R : Sheaf J RingCat.{w}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max m t}]
  [HasWeakSheafify J AddCommGrpCat.{max m t}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max m t}]
  [HasWeakSheafify J AddCommGrpCat.{max m t}] in
/-- The universe lift of the sheafification unit is natural. -/
theorem uliftSheafifyUnit_naturality {P Q : PresheafOfModules.{m} R₀} (f : P ⟶ Q) :
    uliftMap.{_, _, _, _, t} f ≫ uliftSheafifyUnit.{_, _, _, _, t} α Q =
      uliftSheafifyUnit.{_, _, _, _, t} α P ≫
        uliftMap.{_, _, _, _, t} ((SheafOfModules.forget R ⋙ restrictScalars α).map
          ((sheafification.{m} α).map f)) :=
  (((uliftFunctor.{_, _, _, _, t}).map_comp _ _).symm.trans
    (congrArg (uliftFunctor.{_, _, _, _, t}).map
      ((sheafificationAdjunction.{m} α).unit.naturality f))).trans
    ((uliftFunctor.{_, _, _, _, t}).map_comp _ _)

end PresheafOfModules

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules.UliftTensor

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable (X : AlgebraicGeometry.RingedSite.{u + 1, u, u})
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u + 1}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

/-- The sectionwise universe lift of the `𝒪`-modules of a ringed site whose objects lie one
universe above its morphisms and its structure rings, into the universe in which the internal
Hom of Stacks 03EM of two of them lives. -/
abbrev moduleUliftSmallSite :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  moduleUliftForInternalHom X

variable (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- Tensoring on the right by `𝓕`, on the `𝒪`-modules of the site. -/
abbrev tensorRightModules :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} X.O).flip.obj F

/-- Tensoring on the right by the universe lift of `𝓕`, one universe up. -/
abbrev tensorRightModulesLift :
    SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u + 1, u + 1} X.O).flip.obj
    ((moduleUliftSmallSite X).obj F)

/-- The sheafification adjunction for presheaves of modules on the site, at the raised module
universe. -/
abbrev liftSheafifyAdjunction :=
  PresheafOfModules.sheafificationAdjunction.{u + 1}
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)

/-- The presheaf-level comparison from the objectwise tensor product of the lifts to the lift of
the tensor product sheaf: the lift of the objectwise tensor product followed by the lift of the
sheafification unit. -/
def tensorLiftPresheafHom (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    PresheafOfModules.tensorObj (PresheafOfModules.uliftObj.{_, _, _, _, u + 1} M.val)
        (PresheafOfModules.uliftObj.{_, _, _, _, u + 1} F.val) ⟶
      (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
          PresheafOfModules.restrictScalars
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj
        (SheafOfModules.uliftObj.{_, _, _, _, u + 1}
          ((PresheafOfModules.sheafification.{u}
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj
            (PresheafOfModules.tensorObj M.val F.val))) :=
  (tensorUliftIso.{u + 1, u, u, u, u + 1} M.val F.val).hom ≫
    PresheafOfModules.uliftSheafifyUnit.{_, _, _, _, u + 1}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
      (PresheafOfModules.tensorObj M.val F.val)

/-- The comparison `𝓜^lift ⊗ 𝓕^lift ⟶ (𝓜 ⊗ 𝓕)^lift`, the transpose of
`AlgebraicGeometry.RingedSite.tensorLiftPresheafHom` across the sheafification adjunction. -/
def tensorLiftModulesNatTrans :
    moduleUliftSmallSite X ⋙ tensorRightModulesLift X F ⟶
      tensorRightModules X F ⋙ moduleUliftSmallSite X where
  app M := ((liftSheafifyAdjunction X).homEquiv _ _).symm (tensorLiftPresheafHom X F M)
  naturality {M N} g := by
    have e₃ : ((PresheafOfModules.tensorBifunctor X.O.obj).flip.obj
            (PresheafOfModules.uliftObj.{_, _, _, _, u + 1} F.val)).map
            (PresheafOfModules.uliftMap.{_, _, _, _, u + 1} g.val) ≫
          ((tensorUliftIso.{u + 1, u, u, u, u + 1} N.val F.val).hom ≫
            PresheafOfModules.uliftSheafifyUnit.{_, _, _, _, u + 1}
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
              (PresheafOfModules.tensorObj N.val F.val)) =
        ((tensorUliftIso.{u + 1, u, u, u, u + 1} M.val F.val).hom ≫
            PresheafOfModules.uliftSheafifyUnit.{_, _, _, _, u + 1}
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
              (PresheafOfModules.tensorObj M.val F.val)) ≫
          PresheafOfModules.uliftMap.{_, _, _, _, u + 1}
            ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
                PresheafOfModules.restrictScalars
                  (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
              ((PresheafOfModules.sheafification.{u}
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
                (((PresheafOfModules.tensorBifunctor X.O.obj).flip.obj F.val).map g.val))) := by
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun z => z ≫ PresheafOfModules.uliftSheafifyUnit.{_, _, _, _, u + 1}
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
          (PresheafOfModules.tensorObj N.val F.val))
        (tensorUliftIso_naturality.{u + 1, u, u, u, u + 1} g.val F.val)).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      exact (congrArg (fun z => (tensorUliftIso.{u + 1, u, u, u, u + 1} M.val F.val).hom ≫ z)
          (PresheafOfModules.uliftSheafifyUnit_naturality
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
            (((PresheafOfModules.tensorBifunctor X.O.obj).flip.obj F.val).map g.val))).trans
          (Category.assoc _ _ _).symm
    have e₁ := Adjunction.homEquiv_naturality_left_symm (adj := liftSheafifyAdjunction X)
      (((PresheafOfModules.tensorBifunctor X.O.obj).flip.obj
          (PresheafOfModules.uliftObj.{_, _, _, _, u + 1} F.val)).map
        (PresheafOfModules.uliftMap.{_, _, _, _, u + 1} g.val))
      (tensorLiftPresheafHom X F N)
    have e₂ := Adjunction.homEquiv_naturality_right_symm (adj := liftSheafifyAdjunction X)
      (tensorLiftPresheafHom X F M) ((moduleUliftSmallSite X).map ((tensorRightModules X F).map g))
    exact e₁.symm.trans ((congrArg _ e₃).trans e₂)

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Each component of `AlgebraicGeometry.RingedSite.tensorLiftModulesNatTrans` factors as the
sheafification of the presheaf-level comparison followed by
`PresheafOfModules.sheafifyULiftHom`. -/
theorem tensorLiftModulesNatTrans_app
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (tensorLiftModulesNatTrans X F).app M =
      (PresheafOfModules.sheafification.{u + 1}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
          (tensorUliftIso.{u + 1, u, u, u, u + 1} M.val F.val).hom ≫
        PresheafOfModules.sheafifyULiftHom.{_, _, _, _, u + 1}
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
          (PresheafOfModules.tensorObj M.val F.val) :=
  (Adjunction.homEquiv_naturality_left_symm (adj := liftSheafifyAdjunction X)
    (tensorUliftIso.{u + 1, u, u, u, u + 1} M.val F.val).hom
    (PresheafOfModules.uliftSheafifyUnit.{_, _, _, _, u + 1}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
      (PresheafOfModules.tensorObj M.val F.val)))

/-- Each component of `AlgebraicGeometry.RingedSite.tensorLiftModulesNatTrans` is an
isomorphism. -/
instance isIso_tensorLiftModulesNatTrans_app
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    IsIso ((tensorLiftModulesNatTrans X F).app M) := by
  rw [tensorLiftModulesNatTrans_app]
  exact IsIso.comp_isIso'
    (((PresheafOfModules.sheafification.{u + 1}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).mapIso
      (tensorUliftIso.{u + 1, u, u, u, u + 1} M.val F.val)).isIso_hom)
    (PresheafOfModules.isIso_sheafifyULiftHom.{_, _, _, _, u + 1}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
      (PresheafOfModules.tensorObj M.val F.val))

/-- `AlgebraicGeometry.RingedSite.tensorLiftModulesNatTrans` is a natural isomorphism. -/
instance isIso_tensorLiftModulesNatTrans : IsIso (tensorLiftModulesNatTrans X F) :=
  NatIso.isIso_of_isIso_app _

/-- The universe lift commutes with the tensor product, as an isomorphism of functors: the
tensor product of the lifts is the lift of the tensor product. -/
def tensorLiftModulesNatIso :
    moduleUliftSmallSite X ⋙ tensorRightModulesLift X F ≅
      tensorRightModules X F ⋙ moduleUliftSmallSite X :=
  asIso (tensorLiftModulesNatTrans X F)

variable [EssentiallySmall.{u} X.C]

/-- The universe lift carries the descended internal Hom to the internal Hom, as an isomorphism
of functors of the second variable. -/
def internalHomSheafSmallLiftNatIso :
    moduleUliftSmallSite X ⋙
        Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor.{u, u + 1, u, u}
          X.J X.O ((moduleUliftSmallSite X).obj F) ≅
      internalHomSheafSmallFunctor.{u} X F ⋙ moduleUliftSmallSite X :=
  NatIso.ofComponents
    (fun B => internalHomSheafUliftIso X F B ≪≫ (internalHomSheafSmallIso.{u} X F B).symm)
    (fun {B B'} f => by
      have h := moduleULift_map_internalHomSheafSmallFunctor_map.{u} X F f
      have k := internalHomPost_internalHomSheafUliftIso X F f
      have h' := congrArg (fun z => ((internalHomSheafUliftIso X F B).hom ≫
        (internalHomSheafSmallIso.{u} X F B).inv) ≫ z) h
      change internalHomPost X ((moduleUliftSmallSite X).map f) ≫
            ((internalHomSheafUliftIso X F B').hom ≫
              (internalHomSheafSmallIso.{u} X F B').inv) =
          ((internalHomSheafUliftIso X F B).hom ≫
              (internalHomSheafSmallIso.{u} X F B).inv) ≫
            (moduleUliftSmallSite X).map ((internalHomSheafSmallFunctor.{u} X F).map f)
      rw [← Category.assoc, k]
      refine Eq.trans ?_ h'.symm
      exact (congrArg (fun z => (internalHomSheafUliftIso X F B).hom ≫ z)
          (Iso.inv_hom_id_assoc (internalHomSheafSmallIso.{u} X F B)
            (internalHomPost X f ≫ (internalHomSheafSmallIso.{u} X F B').inv)).symm).trans
        (Category.assoc _ _ _).symm)

/-- Stacks 03EO at the module universe of the schemes: on a ringed site which is essentially small
at `u` and whose objects lie in `Type (u + 1)` while its morphisms and the sections of its
structure sheaf lie in `Type u`, tensoring on the right by `𝓕` is left adjoint to the internal
Hom with source `𝓕`, on the `𝒪`-modules with sections in `u`. -/
def sheafTensorRightInternalHomSmallAdjunction :
    tensorRightModules X F ⊣ internalHomSheafSmallFunctor.{u} X F :=
  Adjunction.restrictFullyFaithful
    (Stacks.SheafOfModules.InternalHom.FreeUniverse.sheafTensorRightHomAdjunction X.O
      ((moduleUliftSmallSite X).obj F))
    (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (tensorLiftModulesNatIso X F) (internalHomSheafSmallLiftNatIso X F)

end AlgebraicGeometry.RingedSite

end
