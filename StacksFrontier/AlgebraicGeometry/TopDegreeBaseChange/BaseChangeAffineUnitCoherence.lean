module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeAffineTensorOrder
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaUnit
public import StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChangeComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonBraided
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree

/-!
# The projection formula of the affine base change is the unit of the adjunction

Let
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
be a cartesian square of schemes with `h` affine, and let `F'` be a quasi-coherent
`𝒪_{X'}`-module. Conclusion (c) of [Stacks, Tag 0EX3] compares `F'` with `h'_* (h')^* F'` twice:
once through the unit of the adjunction `(h')^* ⊣ h'_*`, and once through the projection formula
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.pushforwardPullbackTensorIsoRight`, by tensoring
`F'` with the canonical map `𝒪_{Y'} ⟶ h_* 𝒪_{Y''}` pulled back along `f'`. **This file proves
that the two agree.**

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `unit_eq_pushforwardPullbackTensorIsoRight`: **the coherence.** The composite

  `F' ≅ F' ⊗ 𝒪_{X'} ≅ F' ⊗ (f')^* 𝒪_{Y'} ⟶ F' ⊗ (f')^* h_* 𝒪_{Y''} ≅ h'_* (h')^* F'`,

  whose last step is `pushforwardPullbackTensorIsoRight`, is the unit of
  `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction h'` at `F'`.
* `projectionFormula_unitObj_unit`: **the projection-formula morphism at the structure sheaf of
  the source, precomposed with the canonical `𝒪_Y ⟶ f_* 𝒪_X`, is the unit of `f^* ⊣ f_*`** — for
  every morphism of ringed spaces, with no affineness and no quasi-coherence.
  `projectionFormula_unitToPushforwardUnit` is the same identity for a morphism of schemes, with
  the canonical map named `AlgebraicGeometry.Scheme.Modules.unitToPushforwardUnit`.
* `unit_comp_pullbackPushforwardUnitIso`: **the structure-sheaf base change of the square carries
  the pullback of the canonical `𝒪_{Y'} ⟶ h_* 𝒪_{Y''}` to the canonical
  `𝒪_{X'} ⟶ h'_* 𝒪_{X''}`.**
* `pullbackSquareIso_hom_app_unitModule`: the comparison of the two ways around the square
  carries the structure sheaf to the structure sheaf, compatibly with
  `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`.
* `adjunctionTensorMap_unitObj_left_comp`: the formal reduction, for an adjunction with two
  bifunctors, a comparison between them, left unitors and a unit comparison.
* `inv_comp_eq_of_naturality_of_unitor`: the formal shape of the assembly — four identities in
  an arbitrary category give the conclusion.
* `tensorSheafRingedSpaceCommIso_hom_comp_tensorSheafUnitLeftIso` and
  `tensorSheafSchemeCommIso_hom_comp_tensorSheafUnitLeftIso`: the symmetry of the tensor product
  of sheaves of modules carries the left unitor to the right unitor.

## Implementation notes

*Why the identity splits in two.* The composite to be identified runs through two canonical maps
that are built quite differently: the projection-formula morphism of [Stacks, Tag 0FZE], which is
an adjoint transpose, and the base-change morphism of [Stacks, Tag 02KG], which is a mate.
Accordingly the proof has two halves, and each is stated on its own.
`projectionFormula_unitObj_unit` is the first: the projection formula at `G = 𝒪_X` is, after
tensoring the canonical `𝒪_Y ⟶ f_* 𝒪_X` into the first factor, the unit of `f^* ⊣ f_*`. It is an
instance of `adjunctionTensorMap_unitObj_left_comp`, whose one hypothesis is the left-unitor
coherence of [Stacks, Tag 01CD], available as `Stacks.RingedSpace.comparison_leftUnitor`.
`unit_comp_pullbackPushforwardUnitIso` is the second, and it rests on the triangle identity
`Stacks.Modules.map_unit_comp_baseChangeNatTrans_app` of the mate together with the
compatibility of `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` with composition. The two
halves are joined by `inv_comp_eq_of_naturality_of_unitor`, which is pure category theory.

*The symmetry of the tensor product enters only through one coherence.*
`pushforwardPullbackTensorIsoRight` begins with the commutor `F' ⊗ P ≅ P ⊗ F'`, while the
composite starts from the *right* unitor `F' ≅ F' ⊗ 𝒪_{X'}`; what reconciles them is that the
commutor carries the left unitor to the right unitor, which is
`CategoryTheory.braiding_leftUnitor` for the symmetric structure of [Stacks, Tag 01CA] on the
modules of a ringed space. The three morphisms have to be recognised inside that structure
first: `Stacks.RingedSpace.strict_leftUnitor_eq` and `strict_rightUnitor_eq` do it for the
unitors, and `tensorSheafRingedSpaceCommIso_hom_eq_braiding` does it for the commutor, through
the section formula `Stacks.PullbackTensorCoherence.braiding_tmul`.

*One spelling per lemma, and one reconciliation per declaration.* The computation is carried out
in the ringed-space spelling `Stacks.RingedSpace.pullbackFunctor`, `pushforwardFunctor`,
`pullbackAdjunction` and the uncurried `Stacks.SheafOfModules.Tensor.sheafTensor`, in which every
intermediate goal is type-correct at `implicit` transparency so that `rw` goes through; the
scheme-level statements are then obtained from it. The two spellings of each factor are
definitionally equal, but a single step that reconciles several factors at once exhausts a
declaration's elaboration budget, while each factor on its own is immediate. So each
reconciliation is a one-line lemma of its own — `projectionFormulaMap_unitModule_eq`,
`projectionFormulaMap_eq_adjunctionTensorMap`,
`pushforward_map_tensorSheafUnitLeftIso_eq`, `pushforwardPullbackTensorIsoRight_hom` — and the
final theorem combines them with `congrArg`, which never asks for more than one factor at a
time. For the same reason the transport of a factor through an equation is always term-mode
`congrArg` rather than `rw`.

*Where the uncurried bifunctor is not the fixed-factor one on the nose.* Tensoring a morphism
into one variable of `Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor _)` is the
sheafification of a single morphism of presheaves of modules only after the identity in the
other variable has been cancelled, which is
`Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map`. That is the one step
`tensorSheafRingedSpaceCommIso_naturality` and `projectionFormulaMap_eq_adjunctionTensorMap`
cost beyond `rfl`.

*Affineness of `h'`.* It is not a hypothesis: it follows from that of `h` by stability of
`IsAffineHom` under base change, exactly as in
`StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeAffineProjectionFormula`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MonoidalCategory Stacks.RingedSpace
open scoped CategoryTheory.Prod TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

/-! ### The formal reduction -/

section Abstract

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)
  {eC : C} {eD : D} (lA : ∀ Z : C, A.obj (eC, Z) ≅ Z) (lB : ∀ W : D, B.obj (eD, W) ≅ W)
  (ν : L.obj eC ≅ eD)

/-- **The abstract projection-formula map at the unit object of the target, precomposed with the
adjoint transpose of the unit comparison, is the left unitor followed by the unit of the
adjunction.** The one hypothesis is the left-unitor coherence of the comparison `α`; the rest is
naturality of `α`, the description of the map in `CategoryTheory.adjunctionTensorMap`, and
naturality of the unit of `L ⊣ R`. -/
lemma adjunctionTensorMap_unitObj_left_comp (H : C)
    (hcoh : α.app (eC, H) ≫
        (B.map ((ν.hom ×ₘ 𝟙 (L.obj H) : ((L.obj eC, L.obj H) : D × D) ⟶ (eD, L.obj H))) ≫
          (lB (L.obj H)).hom) = L.map (lA H).hom) :
    A.map (((adj.unit.app eC ≫ R.map ν.hom) ×ₘ 𝟙 H :
          ((eC, H) : C × C) ⟶ (R.obj eD, H))) ≫
        adjunctionTensorMap adj A B α eD H ≫ R.map (lB (L.obj H)).hom =
      (lA H).hom ≫ adj.unit.app H := by
  have hsplit : (((adj.unit.app eC ≫ R.map ν.hom) ×ₘ 𝟙 H) :
        ((eC, H) : C × C) ⟶ (R.obj eD, H)) =
      (adj.unit.app eC ×ₘ 𝟙 H) ≫ (R.map ν.hom ×ₘ 𝟙 H) := by
    apply Prod.ext <;> simp
  have hnat : A.map ((R.map ν.hom ×ₘ 𝟙 H :
          ((R.obj (L.obj eC), H) : C × C) ⟶ (R.obj eD, H))) ≫
        adjunctionTensorMap adj A B α eD H =
      adjunctionTensorMap adj A B α (L.obj eC) H ≫
        R.map (B.map ((ν.hom ×ₘ 𝟙 (L.obj H) :
          ((L.obj eC, L.obj H) : D × D) ⟶ (eD, L.obj H)))) := by
    have h := adjunctionTensorMap_natural adj A B α ν.hom (𝟙 H)
    rw [L.map_id] at h
    exact h
  rw [hsplit, A.map_comp, Category.assoc, reassoc_of% hnat, ← R.map_comp,
    ProjectionFormula.adjunctionTensorMap_unit_comp adj A B α eC H, hcoh,
    Adjunction.homEquiv_unit, Adjunction.unit_naturality]

end Abstract

/-! ### The symmetry of the tensor product and the two unitors -/

/-- **The symmetry of the tensor product of sheaves of modules on a ringed space**,
`A ⊗ B ≅ B ⊗ A`, with its type ascribed through the uncurried
`Stacks.SheafOfModules.Tensor.sheafTensor`. This is
`Stacks.SheafOfModules.tensorSheafCommIso`; the ascription is the one
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorSheafSchemeCommIso` performs for a scheme,
and it is what lets a composite mentioning the symmetry be rewritten. -/
def tensorSheafRingedSpaceCommIso (Z : RingedSpace.{u, u})
    (A B : _root_.SheafOfModules.{u} (structureRingSheaf Z)) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Z.presheaf,
          Z.IsSheaf⟩)).obj (A, B) ≅ (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Z.presheaf, Z.IsSheaf⟩)).obj (B, A) :=
  Stacks.SheafOfModules.tensorSheafCommIso (Opens.grothendieckTopology Z.carrier)
    (Osharp := Z.sheaf) A B

variable (Z : RingedSpace.{u, u})

/-- **Naturality of the symmetry of the tensor product sheaf in the second variable**: it
exchanges tensoring a morphism into the second factor with tensoring it into the first. Both
sides are the sheafification of one morphism of presheaves of modules, and the identity between
those is `PresheafOfModules.tensorHom_tensorCommHom`. -/
lemma tensorSheafRingedSpaceCommIso_naturality
    (A : _root_.SheafOfModules.{u} (structureRingSheaf Z))
    {B B' : _root_.SheafOfModules.{u} (structureRingSheaf Z)} (g : B ⟶ B') :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Z.presheaf, Z.IsSheaf⟩)).map ((𝟙 A ×ₘ g : ((A, B) : _ × _) ⟶ (A, B'))) ≫
        (tensorSheafRingedSpaceCommIso Z A B').hom =
      (tensorSheafRingedSpaceCommIso Z A B).hom ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Z.presheaf, Z.IsSheaf⟩)).map ((g ×ₘ 𝟙 A : ((B, A) : _ × _) ⟶ (B', A))) :=
  Eq.trans
    (congrArg (fun z => z ≫ (tensorSheafRingedSpaceCommIso Z A B').hom)
      (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map ⟨Z.presheaf, Z.IsSheaf⟩ (𝟙 A) g))
    (Eq.trans
      (((PresheafOfModules.sheafification (𝟙 (structureRingSheaf Z).obj)).map_comp _ _).symm.trans
        ((congrArg (PresheafOfModules.sheafification (𝟙 (structureRingSheaf Z).obj)).map
            (PresheafOfModules.tensorHom_tensorCommHom (𝟙 A.val) g.val)).trans
          ((PresheafOfModules.sheafification (𝟙 (structureRingSheaf Z).obj)).map_comp _ _)))
      (congrArg (fun z => (tensorSheafRingedSpaceCommIso Z A B).hom ≫ z)
        (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
          ⟨Z.presheaf, Z.IsSheaf⟩ g (𝟙 A)).symm))

section Braiding

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] Stacks.PullbackTensorCoherence.braidedCategory

/-- **The symmetry of the tensor product sheaf exchanges the two factors of a local pure
tensor.** -/
lemma tensorSheafRingedSpaceCommIso_hom_tmul
    (A B : _root_.SheafOfModules.{u} (structureRingSheaf Z)) (U : (Opens Z.carrier)ᵒᵖ)
    (a : A.val.obj U) (b : B.val.obj U) :
    (tensorSheafRingedSpaceCommIso Z A B).hom.val.app U
        (Stacks.PullbackTensorCoherence.tmul Z A B U a b) =
      Stacks.PullbackTensorCoherence.tmul Z B A U b a :=
  Stacks.SheafOfModules.sheafify_map_toSheafify_apply Z.sheaf.obj
    (structureRingSheaf Z).property (Stacks.tensorCommHom (O := Z.sheaf.obj) A.val B.val) U
    (a ⊗ₜ b)

/-- **The symmetry of the tensor product of sheaves of modules on a ringed space is the braiding
of the symmetric structure of [Stacks, Tag 01CA].** Both exchange the two factors of a local pure
tensor, and a morphism out of a tensor product sheaf is determined by its values on those. -/
lemma tensorSheafRingedSpaceCommIso_hom_eq_braiding
    (A B : _root_.SheafOfModules.{u} (structureRingSheaf Z)) :
    ((tensorSheafRingedSpaceCommIso Z A B).hom : A ⊗ B ⟶ B ⊗ A) = (β_ A B).hom :=
  Stacks.PullbackTensorCoherence.tensor_hom_ext fun U a b ↦
    (tensorSheafRingedSpaceCommIso_hom_tmul Z A B U a b).trans
      (Stacks.PullbackTensorCoherence.braiding_tmul Z A B U a b).symm

/-- **The symmetry of the tensor product of sheaves of modules carries the left unitor to the
right unitor**: `(A ⊗ 𝒪_Z ≅ 𝒪_Z ⊗ A) ≫ (𝒪_Z ⊗ A ≅ A)` is `A ⊗ 𝒪_Z ≅ A`. This is
`CategoryTheory.braiding_leftUnitor` for the symmetric structure of [Stacks, Tag 01CA], with the
three morphisms recognised inside that structure. -/
lemma tensorSheafRingedSpaceCommIso_hom_comp_tensorSheafUnitLeftIso
    (A : _root_.SheafOfModules.{u} (structureRingSheaf Z)) :
    (tensorSheafRingedSpaceCommIso Z A
          (_root_.SheafOfModules.unit (structureRingSheaf Z))).hom ≫
        (tensorSheafUnitLeftIso Z A).hom =
      (tensorSheafUnitRightIso Z A).hom := by
  refine Eq.trans ?_ (strict_rightUnitor_eq Z A)
  refine Eq.trans (congrArg (fun φ ↦ φ ≫ (tensorSheafUnitLeftIso Z A).hom)
    (tensorSheafRingedSpaceCommIso_hom_eq_braiding Z A
      (_root_.SheafOfModules.unit (structureRingSheaf Z)))) ?_
  refine Eq.trans ?_ (braiding_leftUnitor A)
  exact congrArg
    (fun φ ↦ (β_ A (𝟙_ (_root_.SheafOfModules.{u} (structureRingSheaf Z)))).hom ≫ φ)
    (strict_leftUnitor_eq Z A).symm

end Braiding

/-! ### The structure-sheaf base change and the unit -/

/-- The canonical morphism `𝒪_W ⟶ q_* 𝒪_Z` of a morphism of schemes `q : Z ⟶ W`, written
through the unit of `q^* ⊣ q_*`: it is the adjoint transpose of
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`. -/
lemma unitToPushforwardUnit_eq {Z W : Scheme.{u}} (q : Z ⟶ W) :
    Scheme.Modules.unitToPushforwardUnit q =
      (Scheme.Modules.pullbackPushforwardAdjunction q).unit.app (Scheme.unitModule W) ≫
        (Scheme.Modules.pushforward q).map (Scheme.Modules.pullbackUnitIso q).hom :=
  (Scheme.Modules.pullbackUnitIso_homEquiv q).symm.trans (Adjunction.homEquiv_unit _ _ _ _)

/-- **Naturality of the symmetry of the tensor product of modules on a scheme in the second
variable.** This is `tensorSheafRingedSpaceCommIso_naturality` on the underlying ringed space. -/
lemma tensorSheafSchemeCommIso_naturality (X : Scheme.{u}) (A : X.Modules)
    {B B' : X.Modules} (g : B ⟶ B') :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf,
          X.toRingedSpace.IsSheaf⟩)).map ((𝟙 A ×ₘ g : ((A, B) : _ × _) ⟶ (A, B'))) ≫
        (tensorSheafSchemeCommIso X A B').hom =
      (tensorSheafSchemeCommIso X A B).hom ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.toRingedSpace.presheaf,
              X.toRingedSpace.IsSheaf⟩)).map ((g ×ₘ 𝟙 A : ((B, A) : _ × _) ⟶ (B', A))) :=
  tensorSheafRingedSpaceCommIso_naturality X.toRingedSpace A g

/-- **The symmetry of the tensor product of modules on a scheme carries the left unitor to the
right unitor.** This is `tensorSheafRingedSpaceCommIso_hom_comp_tensorSheafUnitLeftIso` on the
underlying ringed space. -/
lemma tensorSheafSchemeCommIso_hom_comp_tensorSheafUnitLeftIso (X : Scheme.{u})
    (A : X.Modules) :
    (tensorSheafSchemeCommIso X A (Scheme.unitModule X)).hom ≫
        (tensorSheafUnitLeftIso X.toRingedSpace A).hom =
      (tensorSheafUnitRightIso X.toRingedSpace A).hom :=
  tensorSheafRingedSpaceCommIso_hom_comp_tensorSheafUnitLeftIso X.toRingedSpace A

/-- **Tensoring a composite into the first factor splits**, for the tensor product of modules on
a scheme. -/
lemma tensorSheaf_map_comp_left (X : Scheme.{u}) {A A' A'' B : X.Modules} (a : A ⟶ A')
    (a' : A' ⟶ A'') :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf,
          X.toRingedSpace.IsSheaf⟩)).map ((a ×ₘ 𝟙 B : ((A, B) : _ × _) ⟶ (A', B))) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.toRingedSpace.presheaf,
              X.toRingedSpace.IsSheaf⟩)).map ((a' ×ₘ 𝟙 B : ((A', B) : _ × _) ⟶ (A'', B))) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
        (((a ≫ a') ×ₘ 𝟙 B : ((A, B) : _ × _) ⟶ (A'', B))) :=
  (bifunctor_map_comp_left (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)) a a' (𝟙 B)).symm

/-- **The projection-formula morphism at the structure sheaf of the source is the unit of
`f^* ⊣ f_*`**, for a morphism of ringed spaces. Tensoring the adjoint transpose of
`Stacks.RingedSpace.pullbackObjUnitIso` into the first factor and then applying the
projection-formula morphism of [Stacks, Tag 0FZE] and the direct image of the left unitor on `X`
gives the left unitor on `Y` followed by the unit of `f^* ⊣ f_*` at `H`. There is no affineness
and no quasi-coherence hypothesis: only the description of the morphism as an adjoint transpose
is used, through `adjunctionTensorMap_unitObj_left_comp`. -/
lemma projectionFormula_unitObj_unit {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (H : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf, Y.IsSheaf⟩)).map
          ((((pullbackAdjunction f).unit.app
                  (_root_.SheafOfModules.unit (structureRingSheaf Y)) ≫
                (pushforwardFunctor f).map (pullbackObjUnitIso f).hom) ×ₘ 𝟙 H :
            ((_root_.SheafOfModules.unit (structureRingSheaf Y), H) : _ × _) ⟶
              ((pushforwardFunctor f).obj
                (_root_.SheafOfModules.unit (structureRingSheaf X)), H))) ≫
        adjunctionTensorMap (pullbackAdjunction f)
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨Y.presheaf, Y.IsSheaf⟩)) (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.presheaf, X.IsSheaf⟩))
            (comparisonNatTrans f)
            (_root_.SheafOfModules.unit (structureRingSheaf X)) H ≫
          (pushforwardFunctor f).map
            (tensorSheafUnitLeftIso X ((pullbackFunctor f).obj H)).hom =
      (tensorSheafUnitLeftIso Y H).hom ≫ (pullbackAdjunction f).unit.app H :=
  adjunctionTensorMap_unitObj_left_comp (pullbackAdjunction f)
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Y.presheaf, Y.IsSheaf⟩)) (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, X.IsSheaf⟩))
    (comparisonNatTrans f) (tensorSheafUnitLeftIso Y) (tensorSheafUnitLeftIso X)
    (pullbackObjUnitIso f) H (comparison_leftUnitor f H)

/-- **The projection-formula morphism at the structure sheaf of the source is the unit of
`k^* ⊣ k_*`**, with the canonical `𝒪_S ⟶ k_* 𝒪_T` of a morphism of schemes `k : T ⟶ S` spelled
as `AlgebraicGeometry.Scheme.Modules.unitToPushforwardUnit`. This is
`projectionFormula_unitObj_unit` with that one factor rewritten, by
`unitToPushforwardUnit_eq`. -/
lemma projectionFormula_unitToPushforwardUnit {S T : Scheme.{u}} (k : T ⟶ S) (H : S.Modules) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩)).map
          ((Scheme.Modules.unitToPushforwardUnit k ×ₘ 𝟙 H :
            ((Scheme.unitModule S, H) : _ × _) ⟶
              ((Scheme.Modules.pushforward k).obj (Scheme.unitModule T), H))) ≫
        (adjunctionTensorMap (pullbackAdjunction k.toLRSHom.toShHom)
            (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨S.toRingedSpace.presheaf,
                  S.toRingedSpace.IsSheaf⟩))
                    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩))
            (comparisonNatTrans k.toLRSHom.toShHom)
            (_root_.SheafOfModules.unit (structureRingSheaf T.toRingedSpace)) H ≫
          (pushforwardFunctor k.toLRSHom.toShHom).map
            (tensorSheafUnitLeftIso T.toRingedSpace
              ((pullbackFunctor k.toLRSHom.toShHom).obj H)).hom) =
      (tensorSheafUnitLeftIso S.toRingedSpace H).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app H := by
  rw [unitToPushforwardUnit_eq k]
  exact (projectionFormula_unitObj_unit k.toLRSHom.toShHom H).trans rfl

/-! ### Assembling the composite -/

section Assemble

universe u₃ v₃

variable {𝒞 : Type u₃} [Category.{v₃} 𝒞] {A B B' C C' D E : 𝒞} (ρ : B ≅ A) (t : B ⟶ B')
  (c' : B' ⟶ C') (c : B ⟶ C) (x : C ⟶ C') (y : C' ⟶ D) (w : C ⟶ D) (m : D ⟶ E) (l : C ⟶ A)
  (η : A ⟶ E)

/-- **The shape of the computation that identifies the composite of [Stacks, Tag 0EX3] (c) with
the unit.** Four identities — the naturality square `t ≫ c' = c ≫ x`, the factorisation
`x ≫ y = w`, the projection identity `w ≫ m = l ≫ η` and the unitor identity `c ≫ l = ρ.hom` —
give `ρ.inv ≫ t ≫ c' ≫ y ≫ m = η`. Nothing but associativity and `ρ` being invertible is
used. -/
lemma inv_comp_eq_of_naturality_of_unitor (h1 : t ≫ c' = c ≫ x) (h2 : x ≫ y = w)
    (h3 : w ≫ m = l ≫ η) (h4 : c ≫ l = ρ.hom) :
    ρ.inv ≫ t ≫ c' ≫ y ≫ m = η := by
  rw [← Category.assoc t, h1, Category.assoc, ← Category.assoc x, h2, h3,
    ← Category.assoc c, h4, Iso.inv_hom_id_assoc]

end Assemble

variable {X' Y' X'' Y'' : Scheme.{u}} (f' : X' ⟶ Y') (h' : X'' ⟶ X') (f'' : X'' ⟶ Y'')
  (h : Y'' ⟶ Y')

/-- The comparison isomorphism of a commutative square of schemes, read at one module: the
composite of the two instances of `AlgebraicGeometry.Scheme.Modules.pullbackComp` with the
transport along the equality of the two composites. -/
lemma pullbackSquareIso_hom_app (hsq : IsPullback h' f'' f' h) (M : Y'.Modules) :
    (Stacks.Modules.pullbackSquareIso h h' f' f'' hsq.flip.w).hom.app M =
      (Scheme.Modules.pullbackComp h' f').hom.app M ≫
        (Scheme.Modules.pullbackCongr hsq.flip.w.symm).hom.app M ≫
          (Scheme.Modules.pullbackComp f'' h).inv.app M :=
  rfl

/-- **The comparison isomorphism of the square carries the structure sheaf to the structure
sheaf.** Going around the square either way identifies `(h')^* 𝒪_{X'}` with `𝒪_{X''}` through
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`, and the two identifications agree. -/
lemma pullbackSquareIso_hom_app_unitModule (hsq : IsPullback h' f'' f' h) :
    (Scheme.Modules.pullback h').map (Scheme.Modules.pullbackUnitIso f').inv ≫
        (Stacks.Modules.pullbackSquareIso h h' f' f'' hsq.flip.w).hom.app
            (Scheme.unitModule Y') ≫
          (Scheme.Modules.pullback f'').map (Scheme.Modules.pullbackUnitIso h).hom ≫
            (Scheme.Modules.pullbackUnitIso f'').hom =
      (Scheme.Modules.pullbackUnitIso h').hom := by
  have hcg : (Scheme.Modules.pullbackCongr hsq.flip.w.symm).hom.app (Scheme.unitModule Y') =
      (Scheme.Modules.pullbackCongr hsq.flip.w).inv.app (Scheme.unitModule Y') := rfl
  have E1 := Scheme.Modules.pullbackUnitIso_comp_eq f'' h (h' ≫ f') hsq.flip.w
  have E2 := Scheme.Modules.pullbackUnitIso_comp h' f'
  rw [pullbackSquareIso_hom_app f' h' f'' h hsq, hcg]
  simp only [Category.assoc] at E1 E2 ⊢
  rw [E1, ← E2, Iso.hom_inv_id_app_assoc,
    ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- `pullbackPushforwardUnitIso` written out: the base-change morphism of [Stacks, Tag 02KG] at
the structure sheaf, followed by the direct image of
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`. -/
lemma pullbackPushforwardUnitIso_hom (hsq : IsPullback h' f'' f' h) [IsAffineHom h] :
    (pullbackPushforwardUnitIso f' h' f'' h hsq).hom =
      (AffinePushforward.baseChangeNatTrans hsq.flip.w).app (Scheme.unitModule Y'') ≫
        (Scheme.Modules.pushforward h').map (Scheme.Modules.pullbackUnitIso f'').hom :=
  rfl

/-- **The structure-sheaf base change of the square carries the canonical `𝒪_{Y'} ⟶ h_* 𝒪_{Y''}`
to the canonical `𝒪_{X'} ⟶ h'_* 𝒪_{X''}`.** This is the compatibility of the base-change
morphism of [Stacks, Tag 02KG] with the units of the two horizontal adjunctions. -/
lemma unit_comp_pullbackPushforwardUnitIso (hsq : IsPullback h' f'' f' h) [IsAffineHom h] :
    ((Scheme.Modules.pullbackUnitIso f').inv ≫
          (Scheme.Modules.pullback f').map (Scheme.Modules.unitToPushforwardUnit h)) ≫
        (pullbackPushforwardUnitIso f' h' f'' h hsq).hom =
      Scheme.Modules.unitToPushforwardUnit h' := by
  have hnat : (Scheme.Modules.pullback f').map ((Scheme.Modules.pushforward h).map
          (Scheme.Modules.pullbackUnitIso h).hom) ≫
        (AffinePushforward.baseChangeNatTrans hsq.flip.w).app (Scheme.unitModule Y'') =
      (AffinePushforward.baseChangeNatTrans hsq.flip.w).app
          ((Scheme.Modules.pullback h).obj (Scheme.unitModule Y')) ≫
        (Scheme.Modules.pushforward h').map
          ((Scheme.Modules.pullback f'').map (Scheme.Modules.pullbackUnitIso h).hom) :=
    (AffinePushforward.baseChangeNatTrans hsq.flip.w).naturality _
  have hbc := Stacks.Modules.map_unit_comp_baseChangeNatTrans_app hsq.flip.w
    (Scheme.unitModule Y')
  have hunit : (Scheme.Modules.pullbackUnitIso f').inv ≫
        (Scheme.Modules.pullbackPushforwardAdjunction h').unit.app
          ((Scheme.Modules.pullback f').obj (Scheme.unitModule Y')) =
      (Scheme.Modules.pullbackPushforwardAdjunction h').unit.app (Scheme.unitModule X') ≫
        (Scheme.Modules.pushforward h').map
          ((Scheme.Modules.pullback h').map (Scheme.Modules.pullbackUnitIso f').inv) :=
    (Scheme.Modules.pullbackPushforwardAdjunction h').unit.naturality
      (Scheme.Modules.pullbackUnitIso f').inv
  rw [pullbackPushforwardUnitIso_hom, unitToPushforwardUnit_eq h,
    unitToPushforwardUnit_eq h', Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hnat, reassoc_of% hbc, reassoc_of% hunit]
  simp only [← CategoryTheory.Functor.map_comp]
  rw [pullbackSquareIso_hom_app_unitModule f' h' f'' h hsq]

/-! ### The coherence -/

/-- `ProjectionFormula.projectionFormulaMap` at the structure sheaf of the source, read at the
spelling `SheafOfModules.unit (Stacks.RingedSpace.structureRingSheaf _)` of that structure
sheaf. The two spellings of the structure sheaf are definitionally equal; the equation exists so
that the identification can be made one factor at a time. -/
lemma projectionFormulaMap_unitModule_eq {S T : Scheme.{u}} (k : T ⟶ S) (F : S.Modules) :
    ProjectionFormula.projectionFormulaMap k (Scheme.unitModule T) F =
      ProjectionFormula.projectionFormulaMap k
        (_root_.SheafOfModules.unit (structureRingSheaf T.toRingedSpace)) F :=
  rfl

/-- `ProjectionFormula.projectionFormulaMap` is the abstract comparison morphism
`CategoryTheory.adjunctionTensorMap` of the adjunction `k^* ⊣ k_*` and the comparison of
[Stacks, Tag 01CD]. This is
`Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_eq` read at the structure sheaf
of the source. -/
lemma projectionFormulaMap_eq_adjunctionTensorMap {S T : Scheme.{u}} (k : T ⟶ S)
    (F : S.Modules) :
    ProjectionFormula.projectionFormulaMap k
        (_root_.SheafOfModules.unit (structureRingSheaf T.toRingedSpace)) F =
      adjunctionTensorMap (pullbackAdjunction k.toLRSHom.toShHom)
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩))
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩))
        (comparisonNatTrans k.toLRSHom.toShHom)
        (_root_.SheafOfModules.unit (structureRingSheaf T.toRingedSpace)) F :=
  ProjectionFormula.projectionFormulaMap_eq k
    (_root_.SheafOfModules.unit (structureRingSheaf T.toRingedSpace)) F

/-- The direct image of the left unitor on the source, read with the pullback and the pushforward
of a morphism of schemes spelled through the underlying morphism of ringed spaces. -/
lemma pushforward_map_tensorSheafUnitLeftIso_eq {S T : Scheme.{u}} (k : T ⟶ S)
    (F : S.Modules) :
    (Scheme.Modules.pushforward k).map
        (tensorSheafUnitLeftIso T.toRingedSpace
          ((Scheme.Modules.pullback k).obj F)).hom =
      (pushforwardFunctor k.toLRSHom.toShHom).map
        (tensorSheafUnitLeftIso T.toRingedSpace
          ((pullbackFunctor k.toLRSHom.toShHom).obj F)).hom :=
  rfl

/-- `pushforwardPullbackTensorIsoRight` written out: the commutor, the structure-sheaf base
change in the first tensor factor, the projection-formula morphism of [Stacks, Tag 0FZE] at the
structure sheaf of `X''`, and the direct image of the left unitor. -/
lemma pushforwardPullbackTensorIsoRight_hom (hsq : IsPullback h' f'' f' h) [IsAffineHom h]
    [IsAffineHom h'] (F' : X'.Modules) (hF' : F'.IsQuasicoherent) :
    (pushforwardPullbackTensorIsoRight f' h' f'' h hsq F' hF').hom =
      (tensorSheafSchemeCommIso X' F'
          ((Scheme.Modules.pullback f').obj
            ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y'')))).hom ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩)).map
            (((pullbackPushforwardUnitIso f' h' f'' h hsq).hom ×ₘ 𝟙 F') :
              (((Scheme.Modules.pullback f').obj
                  ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y'')),
                F') : _ × _) ⟶
                ((Scheme.Modules.pushforward h').obj (Scheme.unitModule X''), F')) ≫
          ProjectionFormula.projectionFormulaMap h' (Scheme.unitModule X'') F' ≫
            (Scheme.Modules.pushforward h').map
              (tensorSheafUnitLeftIso X''.toRingedSpace
                ((Scheme.Modules.pullback h').obj F')).hom :=
  rfl

/-- **The projection formula of the affine base change is the unit of the adjunction.** For a
cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
with `h` affine and `F'` a quasi-coherent `𝒪_{X'}`-module, the composite

`F' ≅ F' ⊗ 𝒪_{X'} ≅ F' ⊗ (f')^* 𝒪_{Y'} ⟶ F' ⊗ (f')^* h_* 𝒪_{Y''} ≅ h'_* (h')^* F'`

— the right unitor, then the pullback along `f'` of the canonical `𝒪_{Y'} ⟶ h_* 𝒪_{Y''}`
tensored into the second factor, then the projection formula
`pushforwardPullbackTensorIsoRight` — is the unit of
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction h'` at `F'`. This is the
coherence conclusion (c) of [Stacks, Tag 0EX3] needs in order to read its comparison map as the
one the unit induces. -/
theorem unit_eq_pushforwardPullbackTensorIsoRight (hsq : IsPullback h' f'' f' h) [IsAffineHom h]
    (F' : X'.Modules) (hF' : F'.IsQuasicoherent) :
    (tensorSheafUnitRightIso X'.toRingedSpace F').inv ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩)).map
            ((𝟙 F' ×ₘ ((Scheme.Modules.pullbackUnitIso f').inv ≫
                (Scheme.Modules.pullback f').map
                  (Scheme.Modules.unitToPushforwardUnit h)) :
              ((F', Scheme.unitModule X') : _ × _) ⟶
                (F', (Scheme.Modules.pullback f').obj
                  ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y''))))) ≫
          (pushforwardPullbackTensorIsoRight f' h' f'' h hsq F' hF').hom =
      (Scheme.Modules.pullbackPushforwardAdjunction h').unit.app F' := by
  have : IsAffineHom h' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip inferInstance
  rw [pushforwardPullbackTensorIsoRight_hom, projectionFormulaMap_unitModule_eq,
    projectionFormulaMap_eq_adjunctionTensorMap]
  exact inv_comp_eq_of_naturality_of_unitor (tensorSheafUnitRightIso X'.toRingedSpace F') _ _ _ _
    _ _ _ _ _ (tensorSheafSchemeCommIso_naturality X' F' _)
    ((tensorSheaf_map_comp_left X' _ _).trans
      (by rw [unit_comp_pullbackPushforwardUnitIso f' h' f'' h hsq]))
    (projectionFormula_unitToPushforwardUnit h' F')
    (tensorSheafSchemeCommIso_hom_comp_tensorSheafUnitLeftIso X' F')

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
