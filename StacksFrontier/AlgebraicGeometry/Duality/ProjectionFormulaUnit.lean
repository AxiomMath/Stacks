module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections
public import StacksFrontier.AlgebraicGeometry.Duality.AffineProjectionFormula

/-!
# The projection formula at the structure sheaf

The projection-formula morphism `h_*G ⊗_{𝒪_S} H ⟶ h_*(G ⊗_{𝒪_T} h^*H)` of
`StacksFrontier.AlgebraicGeometry.Duality.AffineProjectionFormula` is asserted to be an isomorphism
for an affine morphism of schemes and quasi-coherent modules (Stacks Tag 0FZE).  Every proof of
that statement by dévissage in the second argument starts from the case `H = 𝒪_S`, and this file
proves that case — **unconditionally, for an arbitrary morphism of ringed spaces, with no
affineness, quasi-coherence or finiteness hypothesis**.

The base case is formal once two things are known: the right unitor of the tensor product sheaf,
with its action on local sections, and the compatibility of the comparison morphism of Tag 01CD
with that unitor.  The unitor and its section formula are
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections`; the compatibility is
`Stacks.RingedSpace.comparison_rightUnitor` below; and the passage from the compatibility to
invertibility is pure category theory, carried out for the abstract comparison morphism
`CategoryTheory.adjunctionTensorMap`.

## Main results

* `Stacks.RingedSpace.pullbackObjUnitIso_hom_pullbackUnit`: the isomorphism `f^*𝒪_Y ≅ 𝒪_X` of
  `RingedSpaceModuleAdjunction.modulePullbackObjUnitIso` carries the pullback-unit image of a
  local section `r` of `𝒪_Y` to `r^♯`.  This is the one geometric input of the whole file, and it
  is exactly the defining property of Mathlib's `SheafOfModules.pullbackObjUnitToUnit`.
* `Stacks.RingedSpace.tensorSheafUnitRightIso_naturality` and
  `Stacks.RingedSpace.tensorSheafUnitLeftIso_naturality`: the two unitors are natural.
* `Stacks.RingedSpace.comparison_rightUnitor`: **the right-unitor coherence of Tag 01CD**,
  `c ≫ (𝟙 ⊗ ν) ≫ ρ = f^*ρ`, where `c` is the comparison morphism
  `f^*(A ⊗_{𝒪_Y} 𝒪_Y) ⟶ f^*A ⊗_{𝒪_X} f^*𝒪_Y` and `ν : f^*𝒪_Y ≅ 𝒪_X`.
* `Stacks.RingedSpace.comparison_leftUnitor`: **the left-unitor coherence of Tag 01CD**,
  `c ≫ (ν ⊗ 𝟙) ≫ λ = f^*λ`, the same statement with the structure sheaf in the first tensor
  factor; it is what reduces a comparison map on the target of `f` to its value at `𝒪_Y` when
  the tensor factor to be replaced is the left one.
* `Stacks.AlgebraicGeometry.ProjectionFormula.adjunctionTensorMap_unitObj_comp` and
  `isIso_adjunctionTensorMap_unitObj`: the abstract reduction.  For an adjunction `L ⊣ R` with
  binary functors `A`, `B`, a morphism of bifunctors `α`, right unitors for `A` and `B` and a
  unit comparison `ν : L(1) ≅ 1`, the right-unitor coherence of `α` makes
  `adjunctionTensorMap adj A B α G 1` an isomorphism — its composite with the unitors is the
  identity, by the triangle identity of the adjunction.
* `Stacks.AlgebraicGeometry.ProjectionFormula.adjunctionTensorMap_leftUnitObj_comp`: the
  left-handed counterpart of `adjunctionTensorMap_unitObj_comp` — the same statement for a unit
  object in the *first* argument and the left unitors, with the unit object reached through an
  object `G` and maps `c`, `γ` rather than being the first argument on the nose.
* `Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_unit`: **the base case
  of Tag 0FZE**, `IsIso (projectionFormulaMap h G 𝒪_S)` for any morphism of schemes `h` and any
  sheaf of modules `G`.

## Implementation notes

**Why the reduction is formal.**  Writing `ε` for the counit of `h^* ⊣ h_*`, the
projection-formula map at `H = 𝟙` is the adjoint transpose of `α.app (h_*G, 𝟙) ≫ B(ε, 𝟙)`.
Composing with `B(𝟙, ν) ≫ ρ^B` and using naturality of `ρ^B` in the first variable moves `ε` past
the unitor; the coherence then replaces `α.app ≫ B(𝟙, ν) ≫ ρ^B` by `L(ρ^A)`, leaving the
transpose of `L(ρ^A) ≫ ε`, which is `ρ^A` by the right triangle identity.  No property of the
geometry enters.

**Where the section computation happens.**  `comparison_rightUnitor` is proved by taking adjoint
transposes, which turns it into an identity of morphisms *out of* `A ⊗_{𝒪_Y} 𝒪_Y`.  That object
is a sheafification, so `PresheafOfModules.sheafification_hom_ext` together with
`PresheafOfModules.tensorObj_hom_ext` reduce the identity to pure tensors `x ⊗ r` of local
sections, where both sides compute to `r^♯ • η(x)` — the left one through
`Stacks.RingedSpace.comparisonTranspose_unit_tmul`, `tensorSheaf_map_unit_tmul`,
`pullbackObjUnitIso_hom_pullbackUnit` and the unitor's section formula, the right one through the
unitor's section formula and `Stacks.RingedSpace.pullbackUnit_smul`.  This is the only place the
pullback of a *section* is touched, and it is touched only through the unit of the adjunction;
nothing here needs a description of the sections of `f^*`, which `modulePullback` does not have.

**`rw` and the spellings.**  Inside the section computation every step is supplied in term mode
or inside an auxiliary statement that does not mention the unitor.  A `rw` on a goal mentioning
both the unitor and `Stacks.RingedSpace.structureRingSheaf` fails with "the target expression is
not type-correct under the `implicit` transparency level": unfolding `structureRingSheaf` exposes
`CategoryTheory.Sheaf.toRingCat _ X.sheaf`, and `X.sheaf : TopCat.Sheaf CommRingCat _` is not
reducible to a `Sheaf (Opens.grothendieckTopology _) CommRingCat` at that transparency.  The same
reason makes `Stacks.RingedSpace.pullbackObjUnitIso` below an opaque `def` rather than an
`abbrev`.

**What the base case does not give.**  Tag 0FZE is the statement for an *affine* morphism and
*quasi-coherent* modules, in the second argument `H` arbitrary.  What is proved here is the one
case `H = 𝒪_S`; the dévissage from it needs `H` to be a quotient of a free module and needs
`h_*` to preserve the relevant colimits.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

attribute [local implicit_reducible] TopCat.Presheaf.IsSheaf TopCat.Sheaf
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

open scoped CategoryTheory.Prod TensorProduct

universe u

namespace Stacks.RingedSpace

open RingedSpaceModuleAdjunction PresheafOfModules CategoryTheory.Sheaf

section

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The pullback of the structure sheaf**, `f^*𝒪_Y ≅ 𝒪_X`, re-typed over
`Stacks.RingedSpace.structureRingSheaf` and `Stacks.RingedSpace.pullbackFunctor`.  This is
`RingedSpaceModuleAdjunction.modulePullbackObjUnitIso`; the retyping is the same one that
`pullbackFunctor` and `pushforwardFunctor` perform, and it is a plain `def` so that `rw`'s
motive type-check does not unfold it. -/
noncomputable def pullbackObjUnitIso :
    (pullbackFunctor f).obj (_root_.SheafOfModules.unit (structureRingSheaf Y)) ≅
      _root_.SheafOfModules.unit (structureRingSheaf X) :=
  modulePullbackObjUnitIso f

/-- **The pullback of the structure sheaf, on local sections**: `ν` carries the pullback-unit
image of a local section `r` of `𝒪_Y` to its image `r^♯` under the structure morphism of `f`.
This is the defining property of Mathlib's `SheafOfModules.pullbackObjUnitToUnit`, which is the
morphism adjoint to `f^♯ : 𝒪_Y ⟶ f_*𝒪_X`. -/
lemma pullbackObjUnitIso_hom_pullbackUnit (U : (Opens Y.carrier)ᵒᵖ)
    (r : (structureRingSheaf Y).obj.obj U) :
    (pullbackObjUnitIso f).hom.val.app ((opensMap f).op.obj U)
        (pullbackUnit f (_root_.SheafOfModules.unit (structureRingSheaf Y)) U r) =
      sharp f U r := by
  have h := _root_.SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit.{u}
    (structureSheafHom f)
  rw [Adjunction.homEquiv_unit] at h
  have h2 := congrArg
    (fun k ↦ PresheafOfModules.Hom.app (_root_.SheafOfModules.Hom.val k) U r) h
  exact h2.trans
    (_root_.SheafOfModules.unitToPushforwardObjUnit_val_app_apply (structureSheafHom f) r)

end

section

variable (X : RingedSpace.{u, u})

/-- **The right unitor of the tensor product sheaf is natural.** -/
lemma tensorSheafUnitRightIso_naturality
    {A A' : _root_.SheafOfModules.{u} (structureRingSheaf X)} (u : A ⟶ A') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
          ((u ×ₘ 𝟙 (_root_.SheafOfModules.unit (structureRingSheaf X))) :
            ((A, _root_.SheafOfModules.unit (structureRingSheaf X)) : _ × _) ⟶
              (A', _root_.SheafOfModules.unit (structureRingSheaf X))) ≫
        (tensorSheafUnitRightIso X A').hom =
      (tensorSheafUnitRightIso X A).hom ≫ u := by
  refine sheafification_hom_ext (tensorObj_hom_ext fun U x r ↦ ?_)
  have l1 := tensorSheaf_map_unit_tmul X u
    (𝟙 (_root_.SheafOfModules.unit (structureRingSheaf X))) U x r
  have l2 := tensorSheafUnitRightIso_hom_tensorSheafUnit_tmul X A' U (u.val.app U x) r
  have l3 := tensorSheafUnitRightIso_hom_tensorSheafUnit_tmul X A U x r
  have l4 : ∀ (c : (structureRingSheaf X).obj.obj U) (z : A.val.obj U),
      (u.val.app U) (c • z) = c • (u.val.app U) z := fun _ _ ↦ map_smul _ _ _
  exact (congrArg ((tensorSheafUnitRightIso X A').hom.val.app U) l1).trans
    (l2.trans ((congrArg (u.val.app U) l3).trans (l4 r x)).symm)

/-- **The left unitor of the tensor product sheaf is natural.**  The mirror of
`Stacks.RingedSpace.tensorSheafUnitRightIso_naturality`, proved the same way: both sides carry
the sheafification-unit image of `r ⊗ x` to `r • u x`. -/
lemma tensorSheafUnitLeftIso_naturality
    {A A' : _root_.SheafOfModules.{u} (structureRingSheaf X)} (u : A ⟶ A') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
          ((𝟙 (_root_.SheafOfModules.unit (structureRingSheaf X)) ×ₘ u) :
            ((_root_.SheafOfModules.unit (structureRingSheaf X), A) : _ × _) ⟶
              (_root_.SheafOfModules.unit (structureRingSheaf X), A')) ≫
        (tensorSheafUnitLeftIso X A').hom =
      (tensorSheafUnitLeftIso X A).hom ≫ u := by
  refine sheafification_hom_ext (tensorObj_hom_ext fun U r x ↦ ?_)
  have l1 := tensorSheaf_map_unit_tmul X
    (𝟙 (_root_.SheafOfModules.unit (structureRingSheaf X))) u U r x
  have l2 := tensorSheafUnitLeftIso_hom_tensorSheafUnit_tmul X A' U r (u.val.app U x)
  have l3 := tensorSheafUnitLeftIso_hom_tensorSheafUnit_tmul X A U r x
  have l4 : ∀ (c : (structureRingSheaf X).obj.obj U) (z : A.val.obj U),
      (u.val.app U) (c • z) = c • (u.val.app U) z := fun _ _ ↦ map_smul _ _ _
  exact (congrArg ((tensorSheafUnitLeftIso X A').hom.val.app U) l1).trans
    (l2.trans ((congrArg (u.val.app U) l3).trans (l4 r x)).symm)

end

section

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- A morphism out of `f^*P` equals `f^*ψ` once its adjoint transpose, followed by `f_*φ`, is
`ψ` followed by the unit. -/
private lemma comp_eq_pullbackMap_of_homEquiv
    {P A : _root_.SheafOfModules.{u} (structureRingSheaf Y)}
    {W : _root_.SheafOfModules.{u} (structureRingSheaf X)}
    (c : (pullbackFunctor f).obj P ⟶ W) (φ : W ⟶ (pullbackFunctor f).obj A) (ψ : P ⟶ A)
    (h : (pullbackAdjunction f).homEquiv _ _ c ≫ (pushforwardFunctor f).map φ =
      ψ ≫ (pullbackAdjunction f).unit.app A) : c ≫ φ = (pullbackFunctor f).map ψ := by
  refine ((pullbackAdjunction f).homEquiv _ _).injective ?_
  rw [Adjunction.homEquiv_naturality_right, h, ← Adjunction.unit_naturality,
    Adjunction.homEquiv_unit]

/-- The tensor of the identity with `ν`, applied to the sheafification-unit image of a tensor
of two pullback-unit images.  This is the step of `comparison_rightUnitor` that mentions no
unitor, isolated so that `rw` can be used for it. -/
private lemma tensorSheafMap_nu_pullbackUnit_tmul
    (A : _root_.SheafOfModules.{u} (structureRingSheaf Y)) (U : (Opens Y.carrier)ᵒᵖ)
    (x : A.val.obj U) (r : (structureRingSheaf Y).obj.obj U) :
    Hom.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        X.sheaf))).map
          ((𝟙 ((pullbackFunctor f).obj A) ×ₘ (pullbackObjUnitIso f).hom) :
            (((pullbackFunctor f).obj A, (pullbackFunctor f).obj
                (_root_.SheafOfModules.unit (structureRingSheaf Y))) : _ × _) ⟶
              ((pullbackFunctor f).obj A,
                _root_.SheafOfModules.unit (structureRingSheaf X)))).val
        ((opensMap f).op.obj U)
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf (X))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf (X)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := (X).presheaf) (((pullbackFunctor f).obj A)).val
            (((pullbackFunctor f).obj (_root_.SheafOfModules.unit (structureRingSheaf Y)))).val))
          ((opensMap f).op.obj U)
          (pullbackUnit f A U x ⊗ₜ
            pullbackUnit f (_root_.SheafOfModules.unit (structureRingSheaf Y)) U r)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf (X))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf (X)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (X).presheaf) (((pullbackFunctor f).obj A)).val
          ((_root_.SheafOfModules.unit (structureRingSheaf X))).val)) ((opensMap f).op.obj U)
        (pullbackUnit f A U x ⊗ₜ sharp f U r) := by
  have mappedTensor := tensorSheaf_map_unit_tmul X
    (𝟙 ((pullbackFunctor f).obj A)) (pullbackObjUnitIso f).hom
    ((opensMap f).op.obj U) (pullbackUnit f A U x)
    (pullbackUnit f (_root_.SheafOfModules.unit (structureRingSheaf Y)) U r)
  refine mappedTensor.trans ?_
  exact congrArg (fun scalar =>
    Hom.app ((PresheafOfModules.sheafificationAdjunction (R := structureRingSheaf X)
      (𝟙 (structureRingSheaf X).obj)).unit.app
      (PresheafOfModules.tensorObj (O := X.presheaf) ((pullbackFunctor f).obj A).val
        (_root_.SheafOfModules.unit (structureRingSheaf X)).val))
      ((opensMap f).op.obj U) (pullbackUnit f A U x ⊗ₜ scalar))
    (pullbackObjUnitIso_hom_pullbackUnit f U r)

/-- **The right-unitor coherence of Tag 01CD, transposed.**  An identity of morphisms out of
`A ⊗_{𝒪_Y} 𝒪_Y`, checked on local pure tensors: both sides send `x ⊗ r` to `r^♯ • η(x)`. -/
lemma comparisonTranspose_rightUnitor (A : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    comparisonTranspose f A (_root_.SheafOfModules.unit (structureRingSheaf Y)) ≫
        (pushforwardFunctor f).map
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              X.sheaf))).map
              ((𝟙 ((pullbackFunctor f).obj A) ×ₘ (pullbackObjUnitIso f).hom) :
                (((pullbackFunctor f).obj A, (pullbackFunctor f).obj
                    (_root_.SheafOfModules.unit (structureRingSheaf Y))) : _ × _) ⟶
                  ((pullbackFunctor f).obj A,
                    _root_.SheafOfModules.unit (structureRingSheaf X))) ≫
            (tensorSheafUnitRightIso X ((pullbackFunctor f).obj A)).hom) =
      (tensorSheafUnitRightIso Y A).hom ≫ (pullbackAdjunction f).unit.app A := by
  refine sheafification_hom_ext (tensorObj_hom_ext fun U x r ↦ ?_)
  show (tensorSheafUnitRightIso X ((pullbackFunctor f).obj A)).hom.val.app
        ((opensMap f).op.obj U)
      (Hom.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          X.sheaf))).map
          ((𝟙 ((pullbackFunctor f).obj A) ×ₘ (pullbackObjUnitIso f).hom) :
            (((pullbackFunctor f).obj A, (pullbackFunctor f).obj
                (_root_.SheafOfModules.unit (structureRingSheaf Y))) : _ × _) ⟶
              ((pullbackFunctor f).obj A,
                _root_.SheafOfModules.unit (structureRingSheaf X)))).val
        ((opensMap f).op.obj U)
        (Hom.app
          (comparisonTranspose f A
            (_root_.SheafOfModules.unit (structureRingSheaf Y))).val U
          (Hom.app
            ((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.RingedSpace.structureRingSheaf (Y))
                (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y)).obj)).unit.app
                (PresheafOfModules.tensorObj (O := (Y).presheaf) (A).val
                ((_root_.SheafOfModules.unit (structureRingSheaf Y))).val)) U
            (x ⊗ₜ r)))) =
    ((pullbackAdjunction f).unit.app A).val.app U
      ((tensorSheafUnitRightIso Y A).hom.val.app U
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf (Y))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := (Y).presheaf) (A).val ((_root_.SheafOfModules.unit
            (structureRingSheaf Y))).val)) U
          (x ⊗ₜ r)))
  refine Eq.trans (congrArg (fun z ↦
      (tensorSheafUnitRightIso X ((pullbackFunctor f).obj A)).hom.val.app
          ((opensMap f).op.obj U)
        (Hom.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            X.sheaf))).map
            ((𝟙 ((pullbackFunctor f).obj A) ×ₘ (pullbackObjUnitIso f).hom) :
              (((pullbackFunctor f).obj A, (pullbackFunctor f).obj
                  (_root_.SheafOfModules.unit (structureRingSheaf Y))) : _ × _) ⟶
                ((pullbackFunctor f).obj A,
                  _root_.SheafOfModules.unit (structureRingSheaf X)))).val
          ((opensMap f).op.obj U) z))
    (comparisonTranspose_unit_tmul f A
      (_root_.SheafOfModules.unit (structureRingSheaf Y)) U x r)) ?_
  refine Eq.trans (congrArg
    ((tensorSheafUnitRightIso X ((pullbackFunctor f).obj A)).hom.val.app
      ((opensMap f).op.obj U)) (tensorSheafMap_nu_pullbackUnit_tmul f A U x r)) ?_
  refine Eq.trans (tensorSheafUnitRightIso_hom_tensorSheafUnit_tmul X
    ((pullbackFunctor f).obj A) ((opensMap f).op.obj U) (pullbackUnit f A U x)
    (sharp f U r)) ?_
  exact ((congrArg (fun z ↦ ((pullbackAdjunction f).unit.app A).val.app U z)
    (tensorSheafUnitRightIso_hom_tensorSheafUnit_tmul Y A U x r)).trans
      (pullbackUnit_smul f A U r x)).symm

/-- **The right-unitor coherence of Tag 01CD**: the comparison morphism
`f^*(A ⊗_{𝒪_Y} 𝒪_Y) ⟶ f^*A ⊗_{𝒪_X} f^*𝒪_Y`, followed by `𝟙 ⊗ ν` and the right unitor on `X`,
is the pullback of the right unitor on `Y`. -/
lemma comparison_rightUnitor (A : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    comparison f A (_root_.SheafOfModules.unit (structureRingSheaf Y)) ≫
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            X.sheaf))).map
            ((𝟙 ((pullbackFunctor f).obj A) ×ₘ (pullbackObjUnitIso f).hom) :
              (((pullbackFunctor f).obj A, (pullbackFunctor f).obj
                  (_root_.SheafOfModules.unit (structureRingSheaf Y))) : _ × _) ⟶
                ((pullbackFunctor f).obj A,
                  _root_.SheafOfModules.unit (structureRingSheaf X))) ≫
          (tensorSheafUnitRightIso X ((pullbackFunctor f).obj A)).hom) =
      (pullbackFunctor f).map (tensorSheafUnitRightIso Y A).hom := by
  refine comp_eq_pullbackMap_of_homEquiv f _ _ _ ?_
  rw [homEquiv_comparison]
  exact comparisonTranspose_rightUnitor f A

/-! ### The same coherence with the structure sheaf in the first tensor factor -/

/-- The tensor of `ν` with the identity, applied to the sheafification-unit image of a tensor of
two pullback-unit images.  This is the step of `comparisonTranspose_leftUnitor` that mentions no
unitor, isolated so that `rw` can be used for it. -/
private lemma tensorSheafMap_pullbackObjUnit_tmul
    (A : _root_.SheafOfModules.{u} (structureRingSheaf Y)) (U : (Opens Y.carrier)ᵒᵖ)
    (r : (structureRingSheaf Y).obj.obj U) (x : A.val.obj U) :
    Hom.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        X.sheaf))).map
          (((pullbackObjUnitIso f).hom ×ₘ 𝟙 ((pullbackFunctor f).obj A)) :
            (((pullbackFunctor f).obj (_root_.SheafOfModules.unit (structureRingSheaf Y)),
                (pullbackFunctor f).obj A) : _ × _) ⟶
              (_root_.SheafOfModules.unit (structureRingSheaf X),
                (pullbackFunctor f).obj A))).val
        ((opensMap f).op.obj U)
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf (X))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf (X)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := (X).presheaf) (((pullbackFunctor f).obj
            (_root_.SheafOfModules.unit (structureRingSheaf Y)))).val
            (((pullbackFunctor f).obj A)).val))
          ((opensMap f).op.obj U)
          (pullbackUnit f (_root_.SheafOfModules.unit (structureRingSheaf Y)) U r ⊗ₜ
            pullbackUnit f A U x)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf (X))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf (X)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (X).presheaf) ((_root_.SheafOfModules.unit
          (structureRingSheaf X))).val (((pullbackFunctor f).obj A)).val)) ((opensMap f).op.obj U)
        (sharp f U r ⊗ₜ pullbackUnit f A U x) := by
  have mappedTensor := tensorSheaf_map_unit_tmul X
    (pullbackObjUnitIso f).hom (𝟙 ((pullbackFunctor f).obj A))
    ((opensMap f).op.obj U)
    (pullbackUnit f (_root_.SheafOfModules.unit (structureRingSheaf Y)) U r)
    (pullbackUnit f A U x)
  refine mappedTensor.trans ?_
  exact congrArg (fun scalar =>
    Hom.app ((PresheafOfModules.sheafificationAdjunction (R := structureRingSheaf X)
      (𝟙 (structureRingSheaf X).obj)).unit.app
      (PresheafOfModules.tensorObj (O := X.presheaf)
        (_root_.SheafOfModules.unit (structureRingSheaf X)).val
        ((pullbackFunctor f).obj A).val))
      ((opensMap f).op.obj U) (scalar ⊗ₜ pullbackUnit f A U x))
    (pullbackObjUnitIso_hom_pullbackUnit f U r)

/-- **The left-unitor coherence of Tag 01CD, transposed.**  An identity of morphisms out of
`𝒪_Y ⊗_{𝒪_Y} A`, checked on local pure tensors: both sides send `r ⊗ x` to `r^♯ • η(x)`. -/
lemma comparisonTranspose_leftUnitor (A : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    comparisonTranspose f (_root_.SheafOfModules.unit (structureRingSheaf Y)) A ≫
        (pushforwardFunctor f).map
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              X.sheaf))).map
              (((pullbackObjUnitIso f).hom ×ₘ 𝟙 ((pullbackFunctor f).obj A)) :
                (((pullbackFunctor f).obj
                    (_root_.SheafOfModules.unit (structureRingSheaf Y)),
                      (pullbackFunctor f).obj A) : _ × _) ⟶
                  (_root_.SheafOfModules.unit (structureRingSheaf X),
                    (pullbackFunctor f).obj A)) ≫
            (tensorSheafUnitLeftIso X ((pullbackFunctor f).obj A)).hom) =
      (tensorSheafUnitLeftIso Y A).hom ≫ (pullbackAdjunction f).unit.app A := by
  refine sheafification_hom_ext (tensorObj_hom_ext fun U r x ↦ ?_)
  show (tensorSheafUnitLeftIso X ((pullbackFunctor f).obj A)).hom.val.app
        ((opensMap f).op.obj U)
      (Hom.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          X.sheaf))).map
          (((pullbackObjUnitIso f).hom ×ₘ 𝟙 ((pullbackFunctor f).obj A)) :
            (((pullbackFunctor f).obj (_root_.SheafOfModules.unit (structureRingSheaf Y)),
                (pullbackFunctor f).obj A) : _ × _) ⟶
              (_root_.SheafOfModules.unit (structureRingSheaf X),
                (pullbackFunctor f).obj A))).val
        ((opensMap f).op.obj U)
        (Hom.app
          (comparisonTranspose f
            (_root_.SheafOfModules.unit (structureRingSheaf Y)) A).val U
          (Hom.app
            ((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.RingedSpace.structureRingSheaf (Y))
                (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y)).obj)).unit.app
                (PresheafOfModules.tensorObj (O := (Y).presheaf) ((_root_.SheafOfModules.unit
                (structureRingSheaf Y))).val (A).val)) U
            (r ⊗ₜ x)))) =
    ((pullbackAdjunction f).unit.app A).val.app U
      ((tensorSheafUnitLeftIso Y A).hom.val.app U
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf (Y))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := (Y).presheaf) ((_root_.SheafOfModules.unit
            (structureRingSheaf Y))).val (A).val)) U
          (r ⊗ₜ x)))
  refine Eq.trans (congrArg (fun z ↦
      (tensorSheafUnitLeftIso X ((pullbackFunctor f).obj A)).hom.val.app
          ((opensMap f).op.obj U)
        (Hom.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            X.sheaf))).map
            (((pullbackObjUnitIso f).hom ×ₘ 𝟙 ((pullbackFunctor f).obj A)) :
              (((pullbackFunctor f).obj (_root_.SheafOfModules.unit (structureRingSheaf Y)),
                  (pullbackFunctor f).obj A) : _ × _) ⟶
                (_root_.SheafOfModules.unit (structureRingSheaf X),
                  (pullbackFunctor f).obj A))).val
          ((opensMap f).op.obj U) z))
    (comparisonTranspose_unit_tmul f
      (_root_.SheafOfModules.unit (structureRingSheaf Y)) A U r x)) ?_
  refine Eq.trans (congrArg
    ((tensorSheafUnitLeftIso X ((pullbackFunctor f).obj A)).hom.val.app
      ((opensMap f).op.obj U)) (tensorSheafMap_pullbackObjUnit_tmul f A U r x)) ?_
  refine Eq.trans (tensorSheafUnitLeftIso_hom_tensorSheafUnit_tmul X
    ((pullbackFunctor f).obj A) ((opensMap f).op.obj U) (sharp f U r)
    (pullbackUnit f A U x)) ?_
  exact ((congrArg (fun z ↦ ((pullbackAdjunction f).unit.app A).val.app U z)
    (tensorSheafUnitLeftIso_hom_tensorSheafUnit_tmul Y A U r x)).trans
      (pullbackUnit_smul f A U r x)).symm

/-- **The left-unitor coherence of Tag 01CD**: the comparison morphism
`f^*(𝒪_Y ⊗_{𝒪_Y} A) ⟶ f^*𝒪_Y ⊗_{𝒪_X} f^*A`, followed by `ν ⊗ 𝟙` and the left unitor on `X`,
is the pullback of the left unitor on `Y`. -/
lemma comparison_leftUnitor (A : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    comparison f (_root_.SheafOfModules.unit (structureRingSheaf Y)) A ≫
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            X.sheaf))).map
            (((pullbackObjUnitIso f).hom ×ₘ 𝟙 ((pullbackFunctor f).obj A)) :
              (((pullbackFunctor f).obj
                  (_root_.SheafOfModules.unit (structureRingSheaf Y)),
                    (pullbackFunctor f).obj A) : _ × _) ⟶
                (_root_.SheafOfModules.unit (structureRingSheaf X),
                  (pullbackFunctor f).obj A)) ≫
          (tensorSheafUnitLeftIso X ((pullbackFunctor f).obj A)).hom) =
      (pullbackFunctor f).map (tensorSheafUnitLeftIso Y A).hom := by
  refine comp_eq_pullbackMap_of_homEquiv f _ _ _ ?_
  rw [homEquiv_comparison]
  exact comparisonTranspose_leftUnitor f A

end

end Stacks.RingedSpace

namespace Stacks.AlgebraicGeometry.ProjectionFormula

/-! ### The abstract reduction -/

section Abstract

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)
  {eC : C} {eD : D} (ρA : ∀ Z : C, A.obj (Z, eC) ≅ Z) (ρB : ∀ W : D, B.obj (W, eD) ≅ W)
  (ν : L.obj eC ≅ eD)

/-- **The abstract projection-formula map at the unit object, composed with the right unitors
and the unit comparison, is the right unitor of the source.**  The two hypotheses are naturality
of the right unitor of `B` and the right-unitor coherence of `α`; everything else is the triangle
identity of `L ⊣ R`. -/
lemma adjunctionTensorMap_unitObj_comp
    (hρB : ∀ {W W' : D} (u : W ⟶ W'), B.map (u ×ₘ 𝟙 eD) ≫ (ρB W').hom = (ρB W).hom ≫ u)
    (hcoh : ∀ Z : C, α.app (Z, eC) ≫ B.map (𝟙 (L.obj Z) ×ₘ ν.hom) ≫ (ρB (L.obj Z)).hom =
      L.map (ρA Z).hom)
    (G : D) :
    adjunctionTensorMap adj A B α G eC ≫
        R.map (B.map (𝟙 G ×ₘ ν.hom) ≫ (ρB G).hom) = (ρA (R.obj G)).hom := by
  unfold adjunctionTensorMap
  rw [← Adjunction.homEquiv_naturality_right]
  have h1 : B.map (adj.counit.app G ×ₘ 𝟙 (L.obj eC)) ≫ B.map (𝟙 G ×ₘ ν.hom)
      = B.map (𝟙 (L.obj (R.obj G)) ×ₘ ν.hom) ≫ B.map (adj.counit.app G ×ₘ 𝟙 eD) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply Prod.ext <;> simp
  calc adj.homEquiv _ _ ((α.app (R.obj G, eC) ≫ B.map (adj.counit.app G ×ₘ 𝟙 (L.obj eC))) ≫
          (B.map (𝟙 G ×ₘ ν.hom) ≫ (ρB G).hom))
      = adj.homEquiv _ _ (L.map (ρA (R.obj G)).hom ≫ adj.counit.app G) := by
        congr 1
        rw [Category.assoc, ← Category.assoc (B.map (adj.counit.app G ×ₘ 𝟙 (L.obj eC))), h1,
          Category.assoc, hρB (W := L.obj (R.obj G)) (W' := G) (adj.counit.app G),
          ← Category.assoc (B.map (𝟙 (L.obj (R.obj G)) ×ₘ ν.hom)), ← Category.assoc,
          hcoh (R.obj G)]
    _ = (ρA (R.obj G)).hom := by
        rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit,
          adj.right_triangle_components, Category.comp_id]

/-- **The abstract projection-formula map at the unit object is an isomorphism** as soon as the
right-unitor coherence holds. -/
lemma isIso_adjunctionTensorMap_unitObj
    (hρB : ∀ {W W' : D} (u : W ⟶ W'), B.map (u ×ₘ 𝟙 eD) ≫ (ρB W').hom = (ρB W).hom ≫ u)
    (hcoh : ∀ Z : C, α.app (Z, eC) ≫ B.map (𝟙 (L.obj Z) ×ₘ ν.hom) ≫ (ρB (L.obj Z)).hom =
      L.map (ρA Z).hom)
    (G : D) : IsIso (adjunctionTensorMap adj A B α G eC) := by
  have : IsIso ((𝟙 G ×ₘ ν.hom) : ((G, L.obj eC) : D × D) ⟶ (G, eD)) :=
    ⟨(𝟙 G ×ₘ ν.inv), by apply Prod.ext <;> simp, by apply Prod.ext <;> simp⟩
  have : IsIso (B.map (𝟙 G ×ₘ ν.hom) ≫ (ρB G).hom) := inferInstance
  have h2 : adjunctionTensorMap adj A B α G eC =
      (ρA (R.obj G)).hom ≫ inv (R.map (B.map (𝟙 G ×ₘ ν.hom) ≫ (ρB G).hom)) := by
    rw [← adjunctionTensorMap_unitObj_comp adj A B α ρA ρB ν hρB hcoh G, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  rw [h2]
  infer_instance

/-- **The left-handed counterpart of
`Stacks.AlgebraicGeometry.ProjectionFormula.adjunctionTensorMap_unitObj_comp`**: the abstract
projection-formula map at a unit object in its **first** argument, composed with the two **left**
unitors, is the unit of the adjunction.

The data: unit objects `e` and `e'` with left unitors `unitorA` and `unitorB`, a comparison
`nu : L e ≅ e'`, and an object `G` of `D` together with `c : e ⟶ R G` and `γ : G ⟶ e'` whose
composite transpose is `nu` (`hc`); `k` is arbitrary. The two hypotheses on the comparison are
naturality of `unitorB` and the left-unitor coherence of `α`, which are for the left unitors
exactly what `hρB` and `hcoh` of the right-handed version are for the right ones.

The extra layer `c`, `γ` is what the right-handed version does not need: a consumer's first
argument is not the unit object on the nose but an object isomorphic to it, and `hc` — that the
transpose of `c` followed by `γ` is `nu` — is then the only thing the consumer has to supply. -/
lemma adjunctionTensorMap_leftUnitObj_comp {e : C} {e' : D}
    (unitorA : ∀ Z : C, A.obj (e, Z) ≅ Z) (unitorB : ∀ W : D, B.obj (e', W) ≅ W)
    (nu : L.obj e ≅ e')
    (hunitorB : ∀ {W W' : D} (u : W ⟶ W'),
      B.map (𝟙 e' ×ₘ u) ≫ (unitorB W').hom = (unitorB W).hom ≫ u)
    (hcoh : ∀ Z : C, α.app (e, Z) ≫ B.map (nu.hom ×ₘ 𝟙 (L.obj Z)) ≫ (unitorB (L.obj Z)).hom =
      L.map (unitorA Z).hom)
    {G : D} (c : e ⟶ R.obj G) (γ : G ⟶ e')
    (hc : c ≫ R.map γ = adj.unit.app e ≫ R.map nu.hom)
    (H : C) {W : D} (k : L.obj H ⟶ W) :
    (unitorA H).inv ≫ A.map (c ×ₘ 𝟙 H) ≫ adjunctionTensorMap adj A B α G H ≫
        R.map (B.map (γ ×ₘ k) ≫ (unitorB W).hom) =
      adj.unit.app H ≫ R.map k := by
  have hcγ : L.map c ≫ adj.counit.app G ≫ γ = nu.hom := by
    have h := (adj.unit_comp_map_eq_iff nu.hom (c ≫ R.map γ)).mp hc.symm
    simp only [CategoryTheory.Functor.map_comp, Category.assoc,
      Adjunction.counit_naturality] at h
    exact h.symm
  have hα : L.map (A.map ((c ×ₘ 𝟙 H) : ((e, H) : C × C) ⟶ (R.obj G, H))) ≫
      α.app (R.obj G, H) =
      α.app (e, H) ≫ B.map (L.map c ×ₘ 𝟙 (L.obj H)) := by
    have ha := α.naturality ((c ×ₘ 𝟙 H) : ((e, H) : C × C) ⟶ (R.obj G, H))
    change L.map (A.map ((c ×ₘ 𝟙 H) : ((e, H) : C × C) ⟶ (R.obj G, H))) ≫
      α.app (R.obj G, H) = α.app (e, H) ≫ B.map (L.map c ×ₘ L.map (𝟙 H)) at ha
    rw [ha, CategoryTheory.Functor.map_id]
  have hαz : ∀ {Z : D} (z : B.obj (L.obj (R.obj G), L.obj H) ⟶ Z),
      L.map (A.map ((c ×ₘ 𝟙 H) : ((e, H) : C × C) ⟶ (R.obj G, H))) ≫
          α.app (R.obj G, H) ≫ z =
        α.app (e, H) ≫ B.map (L.map c ×ₘ 𝟙 (L.obj H)) ≫ z := fun z =>
    (Category.assoc _ _ z).symm.trans
      ((congrArg (fun w => w ≫ z) hα).trans (Category.assoc _ _ z))
  have hcohz : α.app (e, H) ≫ B.map (nu.hom ×ₘ 𝟙 (L.obj H)) ≫
        (unitorB (L.obj H)).hom ≫ k =
      L.map (unitorA H).hom ≫ k :=
    (congrArg (fun w => α.app (e, H) ≫ w)
          (Category.assoc (B.map (nu.hom ×ₘ 𝟙 (L.obj H)))
            (unitorB (L.obj H)).hom k).symm).trans
      ((Category.assoc (α.app (e, H)) _ k).symm.trans
        (congrArg (fun w => w ≫ k) (hcoh H)))
  have p₁ : ((adj.counit.app G ×ₘ 𝟙 (L.obj H)) ≫ (γ ×ₘ k) :
        ((L.obj (R.obj G), L.obj H) : D × D) ⟶ (e', W)) =
      ((adj.counit.app G ≫ γ) ×ₘ k) := by
    refine Prod.ext ?_ ?_ <;> simp
  have p₂ : ((L.map c ×ₘ 𝟙 (L.obj H)) ≫ ((adj.counit.app G ≫ γ) ×ₘ k) :
        ((L.obj e, L.obj H) : D × D) ⟶ (e', W)) = (nu.hom ×ₘ k) := by
    refine Prod.ext ?_ ?_
    · simpa using hcγ
    · simp
  have p₃ : ((nu.hom ×ₘ 𝟙 (L.obj H)) ≫ (𝟙 e' ×ₘ k) :
        ((L.obj e, L.obj H) : D × D) ⟶ (e', W)) = (nu.hom ×ₘ k) := by
    refine Prod.ext ?_ ?_ <;> simp
  have key : L.map (unitorA H).inv ≫
      L.map (A.map ((c ×ₘ 𝟙 H) : ((e, H) : C × C) ⟶ (R.obj G, H))) ≫
        α.app (R.obj G, H) ≫ B.map (adj.counit.app G ×ₘ 𝟙 (L.obj H)) ≫
          B.map (γ ×ₘ k) ≫ (unitorB W).hom = k := by
    rw [← Category.assoc (B.map (adj.counit.app G ×ₘ 𝟙 (L.obj H))),
      ← CategoryTheory.Functor.map_comp, p₁, hαz,
      ← Category.assoc (B.map (L.map c ×ₘ 𝟙 (L.obj H))),
      ← CategoryTheory.Functor.map_comp, p₂, ← p₃,
      CategoryTheory.Functor.map_comp, Category.assoc, hunitorB k, hcohz,
      ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have step : (unitorA H).inv ≫ A.map ((c ×ₘ 𝟙 H) : ((e, H) : C × C) ⟶ (R.obj G, H)) ≫
      adjunctionTensorMap adj A B α G H ≫
        R.map (B.map (γ ×ₘ k) ≫ (unitorB W).hom) =
      adj.homEquiv H W (L.map (unitorA H).inv ≫
        L.map (A.map ((c ×ₘ 𝟙 H) : ((e, H) : C × C) ⟶ (R.obj G, H))) ≫
          α.app (R.obj G, H) ≫ B.map (adj.counit.app G ×ₘ 𝟙 (L.obj H)) ≫
            B.map (γ ×ₘ k) ≫ (unitorB W).hom) := by
    unfold adjunctionTensorMap
    rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left,
      ← Adjunction.homEquiv_naturality_left]
    exact congrArg (adj.homEquiv H W)
      (congrArg (fun w => L.map (unitorA H).inv ≫
          L.map (A.map ((c ×ₘ 𝟙 H) : ((e, H) : C × C) ⟶ (R.obj G, H))) ≫ w)
        (Category.assoc (α.app (R.obj G, H)) (B.map (adj.counit.app G ×ₘ 𝟙 (L.obj H)))
          (B.map (γ ×ₘ k) ≫ (unitorB W).hom)))
  rw [step, key, Adjunction.homEquiv_unit]

end Abstract

/-! ### The projection formula at the structure sheaf -/

open RingedSpaceModuleAdjunction Stacks.RingedSpace

/-- **The comparison-morphism projection formula is an isomorphism at the structure sheaf**, for
an arbitrary morphism of ringed spaces: `f_*G ⊗_{𝒪_Y} 𝒪_Y ⟶ f_*(G ⊗_{𝒪_X} f^*𝒪_Y)`. -/
lemma isIso_adjunctionTensorMap_comparisonNatTrans_unit {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : _root_.SheafOfModules.{u} (structureRingSheaf X)) :
    IsIso (adjunctionTensorMap (pullbackAdjunction f) ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf))) ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)))
      (comparisonNatTrans f) G (_root_.SheafOfModules.unit (structureRingSheaf Y))) :=
  isIso_adjunctionTensorMap_unitObj (pullbackAdjunction f) ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf))) ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)))
    (comparisonNatTrans f) (tensorSheafUnitRightIso Y) (tensorSheafUnitRightIso X)
    (pullbackObjUnitIso f) (fun u ↦ tensorSheafUnitRightIso_naturality X u)
    (fun Z ↦ comparison_rightUnitor f Z) G

/-- **The base case of Stacks Tag 0FZE**: the projection-formula morphism
`h_*G ⊗_{𝒪_S} 𝒪_S ⟶ h_*(G ⊗_{𝒪_T} h^*𝒪_S)` is an isomorphism, for every morphism of schemes
`h : T ⟶ S` and every sheaf of `𝒪_T`-modules `G` — with no affineness and no quasi-coherence. -/
lemma isIso_projectionFormulaMap_unit {T S : Scheme.{u}} (h : T ⟶ S)
    (G : _root_.SheafOfModules.{u} (structureSheafRing T.toRingedSpace)) :
    IsIso (projectionFormulaMap h G
      (_root_.SheafOfModules.unit (structureSheafRing S.toRingedSpace))) := by
  rw [projectionFormulaMap_eq]
  exact isIso_adjunctionTensorMap_comparisonNatTrans_unit h.toLRSHom.toShHom G

end Stacks.AlgebraicGeometry.ProjectionFormula

end
