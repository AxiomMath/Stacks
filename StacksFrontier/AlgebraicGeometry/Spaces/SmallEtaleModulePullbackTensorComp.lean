module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalInduced
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompUnitChart
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposCompBilinear
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesCompare
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateCompTransfer
public import StacksFrontier.CategoryTheory.Adjunction.TransportEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackTensorComp
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRingHomComposition

/-!
# Naturality of Stacks 03EL on algebraic spaces, and its composite comparison

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S`.  The inverse
image of `𝒪`-modules of Stacks 03LU is monoidal, `AlgebraicGeometry.Space.modulePullbackTensorIso`
(Stacks 03EL), and it has a comparison `g^* ⋙ f^* ≅ (f ≫ g)^*` along a composite,
`AlgebraicGeometry.Space.modulePullbackCompIso`.  Transporting a multiplication of modules along an
étale chart and checking that it is compatible with the two projections of a presentation (the
descent of the graded structure in Stacks 084D) needs both to be natural and to be compatible
with each other.  This file supplies:

* the naturality of the monoidality in both factors;
* the identification of `AlgebraicGeometry.Space.modulePullbackCompIso` with the comparison of
  pullbacks `Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` of the four-field morphisms
  of small étale ringed topoi, taken along the comparison of Stacks 03G2, part (3), of their
  direct images.  The composition law of Stacks 03EL,
  `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp`, is stated for the latter, so this is
  what makes the composition law available for morphisms of algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Space.smallEtalePullbackModulesCompIso`: the comparison of inverse images of
  modules induced by the comparison `AlgebraicGeometry.Space.pushforwardSetCompNatIso` of
  Stacks 03G2, part (3), of the direct images of sheaves of sets; the comparison of direct images
  of modules it induces is `AlgebraicGeometry.Space.pushforwardModulesCompNatIso`.
* `AlgebraicGeometry.Space.modulePushforwardCompSpellingIso`: the identification of the two
  spellings of the composite of two direct images of modules.

## Main results

* `AlgebraicGeometry.Space.modulesTensorObjIso_hom_naturality` and
  `AlgebraicGeometry.Space.modulePullbackTensorIso_hom_naturality`: **the monoidality of the
  inverse image on algebraic spaces is natural in both factors.**
* `AlgebraicGeometry.Space.pushforwardModulesCompNatIso_hom_comp_modulePushforwardIso_hom`:
  the two comparisons of direct images of a composite agree.
* `AlgebraicGeometry.Space.modulePullbackCompIso_hom_eq` and
  `AlgebraicGeometry.Space.modulePullbackCompIso_eq_symm`: **the comparison of Stacks 03LU of
  inverse images along a composite is the inverse of the four-field comparison of pullbacks.**
* `Stacks.SheafOfModules.pullbackModulesCompIso_inv_app_comp_pullbackTensorIso_hom_app`: the
  composition law of Stacks 03EL read with the inverse comparison of pullbacks, the direction in
  which a comparison `g^* ⋙ f^* ≅ (f ≫ g)^*` consumes it.

## Implementation notes

The comparisons of direct images are compared on local sections, as in
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardCompIsoSheafTransfer.lean`: each factor is
the identity or the comparison of Stacks 03G2, part (3), on sections, and comparing them as
morphisms of sheaves of sets instead exhausts the budget.  Two elaboration hazards shape the
statements.  A composite of morphisms of modules is evaluated on a section only through a lemma
stated on variables (`AlgebraicGeometry.Space.modules_comp_val_app_apply`,
`Stacks.Sheaves.RingedToposModules.comp_val_app_apply`), never by unfolding the composite.  And an
object `(F ⋙ G).obj A` is never asked to be identified with `G.obj (F.obj A)` when `G` is an
inverse image of modules of a morphism of algebraic spaces: the unifier then unfolds the inverse
image itself, by height, before `CategoryTheory.Functor.comp`.  The composition law is therefore
supplied at the generic spelling, and its instance at algebraic spaces is to be taken inside a
proof, by `have`, after rewriting with `AlgebraicGeometry.Space.modulePullbackCompIso_eq_symm`.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open Stacks.Sheaves.RingedToposModules (fSharpSet fSharpSetComp pushforwardModules
  pullbackAdjPushforwardModules)

universe u

namespace Stacks.SheafOfModules

open Stacks.Sheaves.RingedToposModules (pullbackModulesCompIso)

universe w w' w'' v u₁ v' u' v'' u''

variable {X : AlgebraicGeometry.RingedTopos.{v, u₁, w}}
    {Y : AlgebraicGeometry.RingedTopos.{v', u', w'}}
    {Z : AlgebraicGeometry.RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]

/-- **The composition law of Stacks 03EL, read with the inverse comparison of pullbacks.**  The
inverse comparison `ψ^*φ^* ⟶ χ^*` at `F ⊗ G`, followed by the comparison of Stacks 03EL for `χ`,
is the pullback along `φ` of the comparison for `ψ`, followed by the comparison for `φ` and the
inverse comparisons of pullbacks in both factors.

This is `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp` with the comparison of pullbacks
moved to the other side, which is the shape a composite of inverse images written as
`g^* ⋙ f^* ≅ (f ≫ g)^*` consumes. -/
theorem pullbackModulesCompIso_inv_app_comp_pullbackTensorIso_hom_app
    (φ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    (ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom Y Z)
    (χ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Z)
    (τ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
    (hτ : fSharpSetComp φ ψ ≫ τ.hom.app
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)
    (F G : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    (pullbackModulesCompIso φ ψ χ τ hτ).inv.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor Z.O).obj F).obj G) ≫
        (pullbackTensorIso χ).hom.app (F, G) =
      (φ.pullbackModules).map ((pullbackTensorIso ψ).hom.app (F, G)) ≫
        (pullbackTensorIso φ).hom.app ((ψ.pullbackModules).obj F, (ψ.pullbackModules).obj G) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
            ((pullbackModulesCompIso φ ψ χ τ hτ).inv.app F)).app
              ((φ.pullbackModules).obj ((ψ.pullbackModules).obj G)) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj ((χ.pullbackModules).obj F)).map
            ((pullbackModulesCompIso φ ψ χ τ hτ).inv.app G) :=
  ((AlgebraicGeometry.RingedToposHom.comp_eq_inv_comp_of_comp_eq _ _ _ _ _ _
    (pullbackTensorIso_hom_app_comp φ ψ χ τ hτ F G)
    ((pullbackModulesCompIso φ ψ χ τ hτ).inv_hom_id_app _)
    (AlgebraicGeometry.RingedToposHom.uncurry_map_hom_comp_inv _
      ((pullbackModulesCompIso φ ψ χ τ hτ).app F)
      ((pullbackModulesCompIso φ ψ χ τ hτ).app G))).symm.trans (Category.assoc _ _ _))

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- Two morphisms of `𝒪`-modules on an algebraic space which agree on all local sections are
equal; stated on variables, so that it applies without unfolding either morphism. -/
theorem modules_hom_ext_of_val_app {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} {M N : Modules.{u, u} B S hS F hF} {a b : M ⟶ N}
    (h : ∀ (W : (SmallEtale B S hS F)ᵒᵖ) (z : M.val.obj W), a.val.app W z = b.val.app W z) :
    a = b :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W ↦
    ModuleCat.hom_ext (LinearMap.ext (h W)))

/-- Pasting three commutative squares along a composite `e ≪≫ k ≪≫ l.symm` of isomorphisms.
All objects are variables, so that the squares are matched syntactically. -/
theorem comp_trans_trans_symm_hom {𝒞 : Type*} [Category 𝒞] {A₁ A₂ B₁ B₂ C₁ C₂ D₁ D₂ : 𝒞}
    {p : A₁ ⟶ A₂} {q : B₁ ⟶ B₂} {r : C₁ ⟶ C₂} {t : D₁ ⟶ D₂} {e₁ : A₁ ≅ B₁} {e₂ : A₂ ≅ B₂}
    {k₁ : B₁ ≅ C₁} {k₂ : B₂ ≅ C₂} {l₁ : D₁ ≅ C₁} {l₂ : D₂ ≅ C₂}
    (h₁ : p ≫ e₂.hom = e₁.hom ≫ q) (h₂ : q ≫ k₂.hom = k₁.hom ≫ r)
    (h₃ : t ≫ l₂.hom = l₁.hom ≫ r) :
    p ≫ (e₂ ≪≫ k₂ ≪≫ l₂.symm).hom = (e₁ ≪≫ k₁ ≪≫ l₁.symm).hom ≫ t := by
  have h₃' : l₁.inv ≫ t = r ≫ l₂.inv := by
    rw [Iso.eq_comp_inv, Category.assoc, h₃, Iso.inv_hom_id_assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, h₁]
  simp only [Category.assoc, h₂, h₃']

/-- The comparison isomorphism `modulesTensorObjIso` between the monoidal tensor product of
`𝒪`-modules on an algebraic space and the sheafified tensor product `sheafTensor` is natural in
both factors. -/
theorem modulesTensorObjIso_hom_naturality {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} {G G₁ G' G₁' : Modules.{u, u} B S hS F hF}
    (a : G ⟶ G₁) (b : G' ⟶ G₁') :
    (a ⊗ₘ b) ≫ (modulesTensorObjIso B S hS F hF G₁ G₁').hom =
      (modulesTensorObjIso B S hS F hF G G').hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS F hF)).map a).app G' ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS F hF)).obj G₁).map b := by
  have h := Stacks.SheafOfModules.tensorObjIso_naturality (structureSheaf B S hS F hF).obj
    (structureRingPresheaf_isSheaf B S hS F hF) a b
  exact h.trans (congrArg (fun k => _ ≫ k)
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map _ a b).symm)

/-- **The monoidality of the inverse image on algebraic spaces is natural in both factors.** -/
theorem modulePullbackTensorIso_hom_naturality (f : X ⟶ Y)
    {G G₁ G' G₁' : Modules.{u, u} B S hS Y.1 Y.2} (a : G ⟶ G₁) (b : G' ⟶ G₁') :
    (modulePullback B S hS f).map (a ⊗ₘ b) ≫ (modulePullbackTensorIso B S hS f G₁ G₁').hom =
      (modulePullbackTensorIso B S hS f G G').hom ≫
        ((modulePullback B S hS f).map a ⊗ₘ (modulePullback B S hS f).map b) := by
  have h1 : (modulePullback B S hS f).map (a ⊗ₘ b) ≫
      (modulePullback B S hS f).map (modulesTensorObjIso B S hS Y.1 Y.2 G₁ G₁').hom =
      (modulePullback B S hS f).map (modulesTensorObjIso B S hS Y.1 Y.2 G G').hom ≫
        (modulePullback B S hS f).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (structureSheaf B S hS Y.1 Y.2)).map a).app G' ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (structureSheaf B S hS Y.1 Y.2)).obj G₁).map b) :=
    ((modulePullback B S hS f).map_comp _ _).symm.trans
      ((congrArg (modulePullback B S hS f).map
        (modulesTensorObjIso_hom_naturality B S hS a b)).trans
        ((modulePullback B S hS f).map_comp _ _))
  have h2 : (modulePullback B S hS f).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS Y.1 Y.2)).map a).app G' ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS Y.1 Y.2)).obj G₁).map b) ≫
      ((Stacks.SheafOfModules.pullbackTensorIso
        (smallEtaleRingedToposModulesHom B S hS f)).app (G₁, G₁')).hom =
      ((Stacks.SheafOfModules.pullbackTensorIso
        (smallEtaleRingedToposModulesHom B S hS f)).app (G, G')).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS X.1 X.2)).map ((modulePullback B S hS f).map a)).app
            ((modulePullback B S hS f).obj G') ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS X.1 X.2)).obj ((modulePullback B S hS f).obj G₁)).map
            ((modulePullback B S hS f).map b) :=
    Stacks.SheafOfModules.pullbackTensorIso_hom_naturality_map
      (smallEtaleRingedToposModulesHom B S hS f) a b
  exact comp_trans_trans_symm_hom h1 h2
    (modulesTensorObjIso_hom_naturality B S hS ((modulePullback B S hS f).map a)
      ((modulePullback B S hS f).map b))

/-! ### The composite of two morphisms of small étale ringed topoi -/

/-- The comparison of the inverse images of modules of the composite of the two four-field
morphisms of small étale ringed topoi of `f` and `g` with that of `f ≫ g`: the comparison of
pullbacks that the composition law of Stacks 03EL,
`Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp`, is stated with. -/
noncomputable abbrev smallEtalePullbackModulesCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :=
  Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso
    (smallEtaleRingedToposModulesHom B S hS f) (smallEtaleRingedToposModulesHom B S hS g)
    (smallEtaleRingedToposModulesHom B S hS (f ≫ g)) (pushforwardSetCompNatIso B S hS f g)
    (fSharpSetComp_smallEtaleRingedToposModulesHom B S hS f g)

/-- The comparison of the two spellings of the composite of two direct images of modules. -/
noncomputable def modulePushforwardCompSpellingIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforwardModules (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposModulesHom B S hS f) ⋙
        pushforwardModules (X := smallEtaleRingedTopos B S hS Y)
          (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposModulesHom B S hS g) ≅
      modulePushforward B S hS f ⋙ modulePushforward B S hS g :=
  Functor.isoWhiskerRight (modulePushforwardIso B S hS f)
      (pushforwardModules (X := smallEtaleRingedTopos B S hS Y)
        (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposModulesHom B S hS g)) ≪≫
    Functor.isoWhiskerLeft (modulePushforward B S hS f) (modulePushforwardIso B S hS g)

/-- On sections, the comparison of direct images of modules along
`AlgebraicGeometry.Space.pushforwardSetCompNatIso` is the comparison of Stacks 03G2,
part (3). -/
theorem pushforwardModulesCompNatIso_hom_app_val_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Modules.{u, u} B S hS X.1 X.2) (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (z : ((pushforwardModules (X := smallEtaleRingedTopos B S hS Y)
      (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposModulesHom B S hS g)).obj
        ((pushforwardModules (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposModulesHom B S hS f)).obj
            N)).val.obj W) :
    ((pushforwardModulesCompNatIso B S hS f g).hom.app N).val.app W z =
      ((smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj N)).hom.app W z :=
  rfl

/-- The sheaf of sets underlying the composite of the direct images of the morphisms of small
étale ringed topoi of `f` and `g` of the sheaf of sets underlying a module. -/
noncomputable abbrev compPushforwardSetSheaf (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Modules.{u, u} B S hS X.1 X.2) :
    Sheaf (SmallEtale.topology B S hS Z.1) (Type u) :=
  (MorphismOfTopoi.comp (smallToposMorphismTypeU B S hS g)
    (smallToposMorphismTypeU B S hS f)).pushforward.obj
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj N)

/-- On sections, the two factors of the comparison of the two spellings of the composite of two
direct images of modules are the identity. -/
theorem modulePushforwardCompSpellingFactors_val_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Modules.{u, u} B S hS X.1 X.2) (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (z : (compPushforwardSetSheaf B S hS f g N).obj.obj W) :
    (show (compPushforwardSetSheaf B S hS f g N).obj.obj W from
      ((modulePushforwardIso B S hS g).hom.app ((modulePushforward B S hS f).obj N)).val.app W
        (((pushforwardModules (X := smallEtaleRingedTopos B S hS Y)
          (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposModulesHom B S hS g)).map
            ((modulePushforwardIso B S hS f).hom.app N)).val.app W z)) = z := by
  have hF := moduleSheafFunctor_map_modulePushforwardIso_hom_app B S hS f N
  have hb : ((smallEtaleRingedToposModulesHom B S hS g).toToposHom.pushforward.map
      ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS Y).O)).map
          ((modulePushforwardIso B S hS f).hom.app N))).hom.app W z = z := by
    rw [hF]
    exact Sheaf.hom_congr_app_apply
      (CategoryTheory.Functor.map_id
        (smallEtaleRingedToposModulesHom B S hS g).toToposHom.pushforward
        ((smallEtaleDirectImage B S hS f).obj (moduleSetSheaf B S hS X N))) W z
  exact (modulePushforwardIso_hom_app_val_app B S hS g ((modulePushforward B S hS f).obj N) W
    _).trans hb

/-- On sections, the comparison of the two spellings of the composite of two direct images of
modules is the identity. -/
theorem modulePushforwardCompSpellingIso_hom_app_val_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Modules.{u, u} B S hS X.1 X.2) (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (z : (compPushforwardSetSheaf B S hS f g N).obj.obj W) :
    (show (compPushforwardSetSheaf B S hS f g N).obj.obj W from
      ((modulePushforwardCompSpellingIso B S hS f g).hom.app N).val.app W z) = z :=
  modulePushforwardCompSpellingFactors_val_app B S hS f g N W z

/-- On sections, the comparison of direct images of modules along
`AlgebraicGeometry.Space.pushforwardModulesCompNatIso` followed by the identification of
the two spellings of the direct image of `f ≫ g` is the comparison of Stacks 03G2, part (3). -/
theorem pushforwardModulesCompNatIso_hom_app_comp_val_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Modules.{u, u} B S hS X.1 X.2) (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (z : ((pushforwardModules (X := smallEtaleRingedTopos B S hS Y)
      (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposModulesHom B S hS g)).obj
        ((pushforwardModules (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposModulesHom B S hS f)).obj
            N)).val.obj W) :
    ((modulePushforwardIso B S hS (f ≫ g)).hom.app N).val.app W
        (((pushforwardModulesCompNatIso B S hS f g).hom.app N).val.app W z) =
      ((smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj N)).hom.app W z :=
  (modulePushforwardIso_hom_app_val_app B S hS (f ≫ g) N W
    (((pushforwardModulesCompNatIso B S hS f g).hom.app N).val.app W z)).trans
    (pushforwardModulesCompNatIso_hom_app_val_app B S hS f g N W z)

/-- On sections, the identification of the two spellings of the composite of two direct images
followed by the comparison of Stacks 03LU is the comparison of Stacks 03G2, part (3). -/
theorem modulePushforwardCompSpellingIso_hom_app_comp_val_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Modules.{u, u} B S hS X.1 X.2) (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (z : ((pushforwardModules (X := smallEtaleRingedTopos B S hS Y)
      (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposModulesHom B S hS g)).obj
        ((pushforwardModules (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposModulesHom B S hS f)).obj
            N)).val.obj W) :
    ((modulePushforwardCompIso B S hS f g).hom.app N).val.app W
        (((modulePushforwardCompSpellingIso B S hS f g).hom.app N).val.app W z) =
      ((smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj N)).hom.app W z := by
  have hA := modulePushforwardCompIso_hom_app_val_app B S hS f g N W
    (((modulePushforwardCompSpellingIso B S hS f g).hom.app N).val.app W z)
  have hB := congrArg (fun y ↦ ((smallToposMorphismTypeU_comp B S hS f g).hom.app
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj N)).hom.app W y)
      (modulePushforwardCompSpellingIso_hom_app_val_app B S hS f g N W z)
  have hB' : @Eq (((modulePushforward B S hS (f ≫ g)).obj N).val.obj W)
      (((smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj N)).hom.app W
          (((modulePushforwardCompSpellingIso B S hS f g).hom.app N).val.app W z))
      (((smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj N)).hom.app W z) := hB
  exact hA.trans hB'

/-- `AlgebraicGeometry.Space.pushforwardModulesCompNatIso_hom_comp_modulePushforwardIso_hom`
at one module. -/
theorem pushforwardModulesCompNatIso_hom_app_comp_modulePushforwardIso_hom_app
    (f : X ⟶ Y) (g : Y ⟶ Z) (N : Modules.{u, u} B S hS X.1 X.2) :
    (pushforwardModulesCompNatIso B S hS f g).hom.app N ≫
        (modulePushforwardIso B S hS (f ≫ g)).hom.app N =
      (modulePushforwardCompSpellingIso B S hS f g).hom.app N ≫
        (modulePushforwardCompIso B S hS f g).hom.app N :=
  modules_hom_ext_of_val_app B S hS fun W z ↦ by
    have h1 := pushforwardModulesCompNatIso_hom_app_comp_val_app B S hS f g N W z
    have h2 := modulePushforwardCompSpellingIso_hom_app_comp_val_app B S hS f g N W z
    have h0 := modules_comp_val_app_apply B S hS (W := Z)
        ((pushforwardModulesCompNatIso B S hS f g).hom.app N)
        ((modulePushforwardIso B S hS (f ≫ g)).hom.app N) W z
    have h3 := Stacks.Sheaves.RingedToposModules.comp_val_app_apply
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Z).O)
        ((modulePushforwardCompSpellingIso B S hS f g).hom.app N)
        ((modulePushforwardCompIso B S hS f g).hom.app N) W z
    exact (h0.trans h1).trans (h2.symm.trans h3.symm)

/-- The two comparisons of direct images of a composite agree, as an equation of natural
transformations. -/
theorem pushforwardModulesCompNatIso_hom_comp_modulePushforwardIso_hom (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    (pushforwardModulesCompNatIso B S hS f g).hom ≫
        (modulePushforwardIso B S hS (f ≫ g)).hom =
      (modulePushforwardCompSpellingIso B S hS f g).hom ≫
        (modulePushforwardCompIso B S hS f g).hom :=
  NatTrans.ext (funext fun N ↦
    pushforwardModulesCompNatIso_hom_app_comp_modulePushforwardIso_hom_app B S hS f g N)

/-- The adjunction of Stacks 03D7 for the four-field morphism of small étale ringed topoi of `f`,
with the direct image of the modules development as right adjoint. -/
noncomputable abbrev smallEtaleModulesAdj {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :=
  pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposModulesHom B S hS f)

/-- The composite adjunction of Stacks 03LU, with its right adjoint read through the comparison
of the two spellings of the direct image and the comparison of direct images of a composite. -/
theorem moduleCompAdjunction_eq_comp_smallEtaleModulesAdj (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleCompAdjunction B S hS f g =
      ((smallEtaleModulesAdj B S hS g).comp (smallEtaleModulesAdj B S hS f)).ofNatIsoRight
        (modulePushforwardCompSpellingIso B S hS f g ≪≫ modulePushforwardCompIso B S hS f g) :=
  (congrArg (fun a ↦ a.ofNatIsoRight (modulePushforwardCompIso B S hS f g))
    (Adjunction.comp_ofNatIsoRight (smallEtaleModulesAdj B S hS g)
      (smallEtaleModulesAdj B S hS f) (modulePushforwardIso B S hS g)
      (modulePushforwardIso B S hS f))).trans (Adjunction.ofNatIsoRight_trans _ _ _)

/-- The conjugate of the inverse of the four-field comparison of pullbacks is the inverse of the
comparison of direct images. -/
theorem conjugateEquiv_smallEtalePullbackModulesCompIso_inv (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (smallEtaleModulesAdj B S hS (f ≫ g))
        ((smallEtaleModulesAdj B S hS g).comp (smallEtaleModulesAdj B S hS f))
        (smallEtalePullbackModulesCompIso B S hS f g).inv =
      (pushforwardModulesCompNatIso B S hS f g).inv := by
  have e2 := Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    (smallEtaleModulesAdj B S hS (f ≫ g)) (pushforwardModulesCompNatIso B S hS f g).symm
    ((smallEtaleModulesAdj B S hS g).comp (smallEtaleModulesAdj B S hS f))
  have e2c := conjugateEquiv_comp (smallEtaleModulesAdj B S hS (f ≫ g))
    ((smallEtaleModulesAdj B S hS g).comp (smallEtaleModulesAdj B S hS f))
    (smallEtaleModulesAdj B S hS (f ≫ g))
    (smallEtalePullbackModulesCompIso B S hS f g).inv
    (smallEtalePullbackModulesCompIso B S hS f g).hom
  refine (Iso.comp_hom_eq_id _).1 ?_
  exact (congrArg (fun t ↦ conjugateEquiv (smallEtaleModulesAdj B S hS (f ≫ g))
      ((smallEtaleModulesAdj B S hS g).comp (smallEtaleModulesAdj B S hS f))
      (smallEtalePullbackModulesCompIso B S hS f g).inv ≫ t) e2).symm.trans
    (e2c.trans ((congrArg (conjugateEquiv (smallEtaleModulesAdj B S hS (f ≫ g))
      (smallEtaleModulesAdj B S hS (f ≫ g)))
      (smallEtalePullbackModulesCompIso B S hS f g).hom_inv_id).trans
        (conjugateEquiv_id (smallEtaleModulesAdj B S hS (f ≫ g)))))

/-- The conjugate of the comparison of Stacks 03LU of inverse images along a composite. -/
theorem conjugateEquiv_smallEtaleModulesAdj_modulePullbackCompIso_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (smallEtaleModulesAdj B S hS (f ≫ g))
        ((smallEtaleModulesAdj B S hS g).comp (smallEtaleModulesAdj B S hS f))
        (modulePullbackCompIso B S hS f g).hom =
      (modulePushforwardIso B S hS (f ≫ g)).hom ≫
        (modulePushforwardCompSpellingIso B S hS f g ≪≫
          modulePushforwardCompIso B S hS f g).inv := by
  have h := Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_hom
    (moduleCompAdjunction B S hS f g) (modulePullbackAdjunction B S hS (f ≫ g))
  rw [moduleCompAdjunction_eq_comp_smallEtaleModulesAdj] at h
  have h' := (Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight _ _ _ _ _).symm.trans h
  have hM : (modulePullbackCompIso B S hS f g).hom =
      (Adjunction.leftAdjointUniq
        (((smallEtaleModulesAdj B S hS g).comp (smallEtaleModulesAdj B S hS f)).ofNatIsoRight
          (modulePushforwardCompSpellingIso B S hS f g ≪≫ modulePushforwardCompIso B S hS f g))
        (modulePullbackAdjunction B S hS (f ≫ g))).hom := by
    unfold modulePullbackCompIso
    rw [moduleCompAdjunction_eq_comp_smallEtaleModulesAdj]
    rfl
  rw [hM]
  exact (Iso.eq_comp_inv _).2 (((Iso.inv_comp_eq _).1 h').trans (Category.comp_id _))

/-- `AlgebraicGeometry.Space.pushforwardModulesCompNatIso_hom_comp_modulePushforwardIso_hom`
rearranged: the identification of the two spellings of the direct image of `f ≫ g` followed by
the inverse of the composite comparison of Stacks 03LU is the inverse of the four-field
comparison. -/
theorem modulePushforwardIso_hom_comp_modulePushforwardCompIso_inv (f : X ⟶ Y) (g : Y ⟶ Z) :
    (modulePushforwardIso B S hS (f ≫ g)).hom ≫
        (modulePushforwardCompSpellingIso B S hS f g ≪≫ modulePushforwardCompIso B S hS f g).inv =
      (pushforwardModulesCompNatIso B S hS f g).inv :=
  (Iso.comp_inv_eq _).2 ((Iso.eq_inv_comp _).2
    (pushforwardModulesCompNatIso_hom_comp_modulePushforwardIso_hom B S hS f g))

/-- **The comparison of Stacks 03LU of inverse images along a composite is the comparison of
pullbacks of the composite of the morphisms of small étale ringed topoi.**  The comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` `g^* ⋙ f^* ≅ (f ≫ g)^*` is the inverse of the
comparison `Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` of the four-field morphisms
of small étale ringed topoi of `f`, `g` and `f ≫ g`, taken along the comparison
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of Stacks 03G2, part (3).

Both are comparisons of left adjoints, so they agree once their conjugates do; the conjugates
are the two comparisons of direct images, which agree by
`AlgebraicGeometry.Space.pushforwardModulesCompNatIso_hom_comp_modulePushforwardIso_hom`. -/
theorem modulePullbackCompIso_hom_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    (modulePullbackCompIso B S hS f g).hom = (smallEtalePullbackModulesCompIso B S hS f g).inv :=
  (conjugateEquiv (smallEtaleModulesAdj B S hS (f ≫ g))
    ((smallEtaleModulesAdj B S hS g).comp (smallEtaleModulesAdj B S hS f))).injective
    ((conjugateEquiv_smallEtaleModulesAdj_modulePullbackCompIso_hom B S hS f g).trans
      ((modulePushforwardIso_hom_comp_modulePushforwardCompIso_inv B S hS f g).trans
        (conjugateEquiv_smallEtalePullbackModulesCompIso_inv B S hS f g).symm))

/-- `AlgebraicGeometry.Space.modulePullbackCompIso_hom_eq` as an equality of isomorphisms: the
comparison of Stacks 03LU of inverse images along a composite is the inverse of the four-field
comparison of pullbacks.  Rewriting with it turns a statement about
`AlgebraicGeometry.Space.modulePullbackCompIso` into one about
`Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso`, where the composition law of
Stacks 03EL, `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp`, applies. -/
theorem modulePullbackCompIso_eq_symm (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullbackCompIso B S hS f g = (smallEtalePullbackModulesCompIso B S hS f g).symm :=
  Iso.ext (modulePullbackCompIso_hom_eq B S hS f g)

end AlgebraicGeometry.Space

end
