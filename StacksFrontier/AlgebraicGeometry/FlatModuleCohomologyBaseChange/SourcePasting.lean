module

public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.UnderivedComparison
public import
  StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.SourceChangeCoherence
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorSections

/-!
# The pasting law along the fibre for the comparison of flat base change

Let

```
Z' --k'--> Z
|i'        |i
v          v
X' --g'--> X
|f'        |f
v          v
S' --g---> S
```

be two commutative squares of schemes stacked one above the other, so that the two vertical
morphisms compose, and let `G` be an `𝒪_{S'}`-module.  Writing

`Φ : M ↦ g^*M ⊗_{𝒪_{S'}} G` and `Ψ : F ↦ (g')^*F ⊗_{𝒪_{X'}} (f')^*G`

for the two coefficient functors of [Stacks, Tag 0GN5] attached to the lower square, and

`Ψ' : M ↦ (k')^*M ⊗_{𝒪_{Z'}} (i')^*(f')^*G`

for the coefficient functor upstairs attached to the upper square and the module `(f')^*G`, this
file proves that the comparison `Φ ∘ (i ≫ f)_* ⟶ (i' ≫ f')_* ∘ Ψ'` of the outer rectangle at an
`𝒪_Z`-module `M` is the comparison of the lower square at the direct image `i_* M`, followed by
the direct image along `f'` of the comparison of the upper square at `M`, read through two
invertible factors built from the comparison of the direct images along `i ≫ f`, the comparison
of the inverse images along `i' ≫ f'`, and the comparison of the direct images along `i' ≫ f'`.

## The route

Unwinding the comparison through
`Stacks.AlgebraicGeometry.ModuleBaseChange.underivedComparison_app`, the comparison of the
rectangle is the base-change morphism of [Stacks, Tag 02KG] for the rectangle tensored with the
identity of `G`, followed by the projection-formula morphism of [Stacks, Tag 0FZE] for the
composite `i' ≫ f'`.  The base-change morphism of the rectangle splits, by
`AlgebraicGeometry.baseChangeNatTrans_vpaste'`, as the base-change morphism of the lower square
at `i_* M` followed by the direct image along `f'` of the base-change morphism of the upper
square; tensoring with the identity of `G` is functorial, so that splitting passes to the first
factor of the comparison.  The projection-formula morphism along the composite splits, by
`AlgebraicGeometry.projectionFormulaSourceNatTrans_comp_whisker`, as the projection-formula
morphism for `f'` followed by the direct image along `f'` of the projection-formula morphism for
`i'`.  Finally naturality of the projection-formula morphism in its first variable moves the
tensored base-change morphism of the upper square past the projection-formula morphism for `f'`,
and what is left inside the direct image along `f'` is exactly the comparison of the upper
square.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleBaseChange.pushforwardSourceComp` and
  `pullbackSourceComp`: the comparisons of the direct and the inverse images along a composite
  of morphisms of schemes, at the spelling the comparison of [Stacks, Tag 0GN5] is written in.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.underivedComparison_pasteSource`: **the pasting law
  along the fibre** for the underived comparison of [Stacks, Tag 0GN5].
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_underivedComparison_app_pushforward_of_isIso`:
  invertibility of the comparison of the lower square at `i_* M`, from invertibility of the
  comparison of the rectangle at `M` and of the comparison of the upper square at `M`.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_underivedComparison_app_pushforward_of_isIso'`:
  the converse direction, invertibility of the comparison of the rectangle at `M`.

## Implementation notes

Neither square is required to be cartesian, no morphism is required to be affine, `G` is
arbitrary and no module is required to be quasi-coherent; the identity holds for two bare
commutative squares.

The two inputs are stated over `AlgebraicGeometry.Scheme.Modules`, whereas the comparison is
stated over `SheafOfModules (structureSheafRing _)`.  The two are definitionally equal but not
at reducible transparency, so a statement mixing them is not type-correct for `rw` or `simp`;
`pushforwardSourceComp` and `pullbackSourceComp` are the comparisons of the direct and inverse
images along a composite read at the second spelling, and with them every statement below stays
inside that spelling.  What remains is the discrepancy between `(F ⋙ G).obj M` and
`G.obj (F.obj M)`, which is reflexive and removed by `dsimp only`.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

variable {S S' X X' Z Z' : Scheme.{u}}

/-! ### The comparisons along a composite, at the spelling of the comparison -/

/-- **The comparison of the direct images along a composite of morphisms of schemes**,
`f_*(i_*(-)) ≅ (i ≫ f)_*(-)` read over `SheafOfModules (structureSheafRing _)`. -/
def pushforwardSourceComp (i : Z ⟶ X) (f : X ⟶ S) :
    modulePushforward i.toLRSHom.toShHom ⋙ modulePushforward f.toLRSHom.toShHom ≅
      modulePushforward (i ≫ f).toLRSHom.toShHom :=
  Scheme.Modules.pushforwardComp i f

/-- **The comparison of the inverse images along a composite of morphisms of schemes**,
`(i')^*(f')^*(-) ≅ (i' ≫ f')^*(-)` read over `SheafOfModules (structureSheafRing _)`. -/
def pullbackSourceComp (i' : Z' ⟶ X') (f' : X' ⟶ S') :
    modulePullback f'.toLRSHom.toShHom ⋙ modulePullback i'.toLRSHom.toShHom ≅
      modulePullback (i' ≫ f').toLRSHom.toShHom :=
  Scheme.Modules.pullbackComp i' f'

/-! ### Elementary rewritings -/

/-- The comparison of the direct images along two equal morphisms is the identity when the
equality is reflexive. -/
private theorem pushforwardCongr_rfl_hom {A B : Scheme.{u}} {a : A ⟶ B} (ha : a = a) :
    (Scheme.Modules.pushforwardCongr ha).hom = 𝟙 _ := by
  ext : 3
  simp

/-- The projection-formula morphism of [Stacks, Tag 0FZE], read as a component of the
transformation along which it is natural in the module upstairs. -/
private theorem projectionFormulaMap_eq_app {T S₀ : Scheme.{u}} (h : T ⟶ S₀)
    (H : SheafOfModules.{u} (structureSheafRing S₀.toRingedSpace))
    (N : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)) :
    Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap h N H =
      (AlgebraicGeometry.projectionFormulaSourceNatTrans h H).app N :=
  rfl

/-- A chain of three morphisms whose first factor is cancelled on the left and whose last factor
is cancelled on the right. -/
private theorem comp_eq_of_cancel {C : Type*} [Category* C] {V W Y₁ A₁ A₂ A₃ : C}
    {th : V ⟶ W} {ti : W ⟶ V} {p : W ⟶ Y₁}
    {r₁ : V ⟶ A₁} {r₂ : A₁ ⟶ A₂} {r₃ : A₂ ⟶ A₃} {dh : A₃ ⟶ Y₁} {di : Y₁ ⟶ A₃}
    (hid : th ≫ ti = 𝟙 V) (hid2 : di ≫ dh = 𝟙 Y₁)
    (hk : ti ≫ r₁ ≫ r₂ ≫ r₃ = p ≫ di) :
    th ≫ p = r₁ ≫ r₂ ≫ r₃ ≫ dh := by
  rw [← Category.id_comp r₁, ← hid]
  simp only [Category.assoc]
  rw [reassoc_of% hk, hid2, Category.comp_id]

/-- The second of four composable morphisms is invertible when the composite is and the other
three are. -/
private theorem isIso_second_of_four {C : Type*} [Category* C] {V W Y₀ Y T : C} {a : V ⟶ W}
    {b : W ⟶ Y₀} {c : Y₀ ⟶ Y} {d : Y ⟶ T} {r : V ⟶ T} (heq : r = a ≫ b ≫ c ≫ d) (hr : IsIso r)
    (ha : IsIso a) (hc : IsIso c) (hd : IsIso d) : IsIso b := by
  subst heq
  have hb : b = inv a ≫ (a ≫ b ≫ c ≫ d) ≫ inv d ≫ inv c := by simp
  rw [hb]
  infer_instance

/-- A composite of four invertible morphisms is invertible. -/
private theorem isIso_comp_four {C : Type*} [Category* C] {V W Y₀ Y T : C} {a : V ⟶ W}
    {b : W ⟶ Y₀} {c : Y₀ ⟶ Y} {d : Y ⟶ T} {r : V ⟶ T} (heq : r = a ≫ b ≫ c ≫ d)
    (ha : IsIso a) (hb : IsIso b) (hc : IsIso c) (hd : IsIso d) : IsIso r := by
  rw [heq]
  infer_instance

variable {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
  {i : Z ⟶ X} {k' : Z' ⟶ Z} {i' : Z' ⟶ X'}

/-! ### The two inputs, at the spelling of the comparison -/

/-- **The base-change morphism of [Stacks, Tag 02KG] for a rectangle obtained by stacking two
commutative squares along the fibre**: it is the base-change morphism of the lower square at the
direct image `i_* M`, followed by the direct image along `f'` of the base-change morphism of the
upper square, read through the comparisons of the direct images along the two composite vertical
morphisms. -/
private theorem baseChangeNatTrans_pasteSource_app (w : g' ≫ f = f' ≫ g)
    (wi : k' ≫ i = i' ≫ g') (w2 : k' ≫ (i ≫ f) = (i' ≫ f') ≫ g)
    (M : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) :
    (baseChangeNatTrans w2).app M =
      (modulePullback g.toLRSHom.toShHom).map ((pushforwardSourceComp i f).inv.app M) ≫
        (baseChangeNatTrans w).app ((modulePushforward i.toLRSHom.toShHom).obj M) ≫
          (modulePushforward f'.toLRSHom.toShHom).map ((baseChangeNatTrans wi).app M) ≫
            (pushforwardSourceComp i' f').hom.app
              ((modulePullback k'.toLRSHom.toShHom).obj M) := by
  have key := congr_app (AlgebraicGeometry.baseChangeNatTrans_vpaste' w wi w2 rfl) M
  simp only [pushforwardCongr_rfl_hom (rfl : i' ≫ f' = i' ≫ f'), Category.comp_id,
    Category.assoc] at key
  exact key

/-- **The projection-formula morphism of [Stacks, Tag 0FZE] along a composite**: it is the
projection-formula morphism for `f'` followed by the direct image along `f'` of the
projection-formula morphism for `i'`, read through the comparison of the inverse images of `G`
along `i' ≫ f'` and the comparison of the direct images along `i' ≫ f'`. -/
private theorem projectionFormulaMap_comp_whisker_app
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (N : SheafOfModules.{u} (structureSheafRing Z'.toRingedSpace)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S'.toRingedSpace.sheaf).flip.obj
        (G)).map ((pushforwardSourceComp i' f').inv.app N)) ≫
        Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f'
            ((modulePushforward i'.toLRSHom.toShHom).obj N) G ≫
          (modulePushforward f'.toLRSHom.toShHom).map
              (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap i' N
                ((modulePullback f'.toLRSHom.toShHom).obj G)) ≫
            (modulePushforward f'.toLRSHom.toShHom).map
              ((modulePushforward i'.toLRSHom.toShHom).map
                ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                    Z'.toRingedSpace.sheaf).obj (N)).map ((pullbackSourceComp i' f').hom.app G)))) =
      Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap (i' ≫ f') N G ≫
        (pushforwardSourceComp i' f').inv.app
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z'.toRingedSpace.sheaf).obj
              (N)).obj (((modulePullback (i' ≫ f').toLRSHom.toShHom).obj G)))) :=
  congr_app (AlgebraicGeometry.projectionFormulaSourceNatTrans_comp_whisker i' f' G) N

/-- The projection-formula morphism of [Stacks, Tag 0FZE] along `i' ≫ f'`, with the comparison
of the direct images along that composite moved to the other end of the chain. -/
private theorem projectionFormulaMap_comp_app
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (N : SheafOfModules.{u} (structureSheafRing Z'.toRingedSpace)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S'.toRingedSpace.sheaf).flip.obj
        (G)).map ((pushforwardSourceComp i' f').hom.app N)) ≫
        Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap (i' ≫ f') N G =
      Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f'
          ((modulePushforward i'.toLRSHom.toShHom).obj N) G ≫
        (modulePushforward f'.toLRSHom.toShHom).map
            (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap i' N
              ((modulePullback f'.toLRSHom.toShHom).obj G)) ≫
          (modulePushforward f'.toLRSHom.toShHom).map
              ((modulePushforward i'.toLRSHom.toShHom).map
                ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                    Z'.toRingedSpace.sheaf).obj (N)).map ((pullbackSourceComp i' f').hom.app G)))) ≫
            (pushforwardSourceComp i' f').hom.app
              ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                  Z'.toRingedSpace.sheaf).obj (N)).obj
                      (((modulePullback (i' ≫ f').toLRSHom.toShHom).obj G)))) := by
  have hid : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      S'.toRingedSpace.sheaf).flip.obj (G)).map ((pushforwardSourceComp i' f').hom.app N)) ≫
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S'.toRingedSpace.sheaf).flip.obj
          (G)).map ((pushforwardSourceComp i' f').inv.app N)) =
      𝟙 ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S'.toRingedSpace.sheaf).obj
          (((modulePushforward i'.toLRSHom.toShHom ⋙
          modulePushforward f'.toLRSHom.toShHom).obj N))).obj (G))) :=
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      S'.toRingedSpace.sheaf).flip.obj G).mapIso
        ((pushforwardSourceComp i' f').app N)).hom_inv_id
  exact comp_eq_of_cancel hid ((pushforwardSourceComp i' f').inv_hom_id_app _)
    (projectionFormulaMap_comp_whisker_app G N)

/-- Naturality of the projection-formula morphism of [Stacks, Tag 0FZE] in its first
variable. -/
private theorem tensorSheafMap_comp_projectionFormulaMap
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    {A B : SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)} (ψ : A ⟶ B) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S'.toRingedSpace.sheaf).flip.obj
        (G)).map ((modulePushforward f'.toLRSHom.toShHom).map ψ)) ≫
        Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f' B G =
      Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f' A G ≫
        (modulePushforward f'.toLRSHom.toShHom).map
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              X'.toRingedSpace.sheaf).flip.obj ((modulePullback f'.toLRSHom.toShHom).obj G)).map
                  (ψ))) :=
  AlgebraicGeometry.projectionFormulaMap_naturality_source f' G ψ

/-! ### The pasting law -/

/-- The comparison of the rectangle, written out in the vocabulary of the tensor product. -/
private theorem pasteSource_lhs (w : g' ≫ f = f' ≫ g) (wi : k' ≫ i = i' ≫ g')
    (w2 : k' ≫ (i ≫ f) = (i' ≫ f') ≫ g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (M : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) :
    (underivedComparison w2 G).app M =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S'.toRingedSpace.sheaf).flip.obj
          (G)).map ((modulePullback g.toLRSHom.toShHom).map
            ((pushforwardSourceComp i f).inv.app M))) ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S'.toRingedSpace.sheaf).flip.obj
            (G)).map ((baseChangeNatTrans w).app ((modulePushforward i.toLRSHom.toShHom).obj M))) ≫
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              S'.toRingedSpace.sheaf).flip.obj (G)).map
                  ((modulePushforward f'.toLRSHom.toShHom).map ((baseChangeNatTrans wi).app M))) ≫
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                S'.toRingedSpace.sheaf).flip.obj (G)).map ((pushforwardSourceComp i' f').hom.app
                  ((modulePullback k'.toLRSHom.toShHom).obj M))) ≫
              Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap (i' ≫ f')
                ((modulePullback k'.toLRSHom.toShHom).obj M) G := by
  let sourceTensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    S'.toRingedSpace.sheaf
  let rectangleMap := (baseChangeNatTrans w2).app M
  have tensorIdentity :=
    (congrArg (fun arrow => (sourceTensor.map rectangleMap).app G ≫ arrow)
      ((sourceTensor.obj ((modulePushforward (i' ≫ f').toLRSHom.toShHom).obj
        ((modulePullback k'.toLRSHom.toShHom).obj M))).map_id G)).trans
      (Category.comp_id ((sourceTensor.map rectangleMap).app G))
  have comparison := underivedComparison_app' w2 G M
  have normalized := comparison.trans
    (congrArg (fun arrow => arrow ≫
      Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap (i' ≫ f')
        ((modulePullback k'.toLRSHom.toShHom).obj M) G) tensorIdentity)
  have mappedPasting := congrArg (sourceTensor.flip.obj G).map
    (baseChangeNatTrans_pasteSource_app w wi w2 M)
  let firstMap := (modulePullback g.toLRSHom.toShHom).map
    ((pushforwardSourceComp i f).inv.app M)
  let secondMap := (baseChangeNatTrans w).app
    ((modulePushforward i.toLRSHom.toShHom).obj M)
  let thirdMap := (modulePushforward f'.toLRSHom.toShHom).map
    ((baseChangeNatTrans wi).app M)
  let fourthMap := (pushforwardSourceComp i' f').hom.app
    ((modulePullback k'.toLRSHom.toShHom).obj M)
  have expanded :=
    ((sourceTensor.flip.obj G).map_comp firstMap (secondMap ≫ thirdMap ≫ fourthMap)).trans
      (congrArg (fun arrow => (sourceTensor.flip.obj G).map firstMap ≫ arrow)
        (((sourceTensor.flip.obj G).map_comp secondMap (thirdMap ≫ fourthMap)).trans
          (congrArg (fun arrow => (sourceTensor.flip.obj G).map secondMap ≫ arrow)
            ((sourceTensor.flip.obj G).map_comp thirdMap fourthMap))))
  exact normalized.trans
    ((congrArg (fun arrow => arrow ≫
      Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap (i' ≫ f')
        ((modulePullback k'.toLRSHom.toShHom).obj M) G)
      (mappedPasting.trans expanded)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun arrow => (sourceTensor.flip.obj G).map firstMap ≫ arrow)
            ((Category.assoc _ _ _).trans
              (congrArg (fun arrow => (sourceTensor.flip.obj G).map secondMap ≫ arrow)
                (Category.assoc _ _ _))))))

/-- The mathematical content of the pasting law: the projection-formula morphism along the
composite splits, and naturality of the projection-formula morphism for `f'` moves the tensored
base-change morphism of the upper square inside the direct image along `f'`. -/
private theorem pasteSource_mid (wi : k' ≫ i = i' ≫ g')
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (M : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S'.toRingedSpace.sheaf).flip.obj
        (G)).map ((modulePushforward f'.toLRSHom.toShHom).map ((baseChangeNatTrans wi).app M))) ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S'.toRingedSpace.sheaf).flip.obj
            (G)).map ((pushforwardSourceComp i' f').hom.app
              ((modulePullback k'.toLRSHom.toShHom).obj M))) ≫
          Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap (i' ≫ f')
            ((modulePullback k'.toLRSHom.toShHom).obj M) G =
      Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f'
          ((modulePullback g'.toLRSHom.toShHom).obj
            ((modulePushforward i.toLRSHom.toShHom).obj M)) G ≫
        (modulePushforward f'.toLRSHom.toShHom).map
            ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                X'.toRingedSpace.sheaf).flip.obj ((modulePullback f'.toLRSHom.toShHom).obj G)).map
                    ((baseChangeNatTrans wi).app M))) ≫
          (modulePushforward f'.toLRSHom.toShHom).map
              (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap i'
                ((modulePullback k'.toLRSHom.toShHom).obj M)
                ((modulePullback f'.toLRSHom.toShHom).obj G)) ≫
            (modulePushforward f'.toLRSHom.toShHom).map
                ((modulePushforward i'.toLRSHom.toShHom).map
                  ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                      Z'.toRingedSpace.sheaf).obj ((modulePullback k'.toLRSHom.toShHom).obj M)).map
                          ((pullbackSourceComp i' f').hom.app G)))) ≫
              (pushforwardSourceComp i' f').hom.app
                ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                    Z'.toRingedSpace.sheaf).obj (((modulePullback k'.toLRSHom.toShHom).obj M))).obj
                        (((modulePullback (i' ≫ f').toLRSHom.toShHom).obj G)))) := by
  have hnat := tensorSheafMap_comp_projectionFormulaMap (f' := f') G
    ((baseChangeNatTrans wi).app M)
  let tensorMap := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    S'.toRingedSpace.sheaf).flip.obj G).map
      ((modulePushforward f'.toLRSHom.toShHom).map ((baseChangeNatTrans wi).app M))
  let tail := (modulePushforward f'.toLRSHom.toShHom).map
      (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap i'
        ((modulePullback k'.toLRSHom.toShHom).obj M)
        ((modulePullback f'.toLRSHom.toShHom).obj G)) ≫
    (modulePushforward f'.toLRSHom.toShHom).map
      ((modulePushforward i'.toLRSHom.toShHom).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          Z'.toRingedSpace.sheaf).obj
            ((modulePullback k'.toLRSHom.toShHom).obj M)).map
              ((pullbackSourceComp i' f').hom.app G))) ≫
    (pushforwardSourceComp i' f').hom.app
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        Z'.toRingedSpace.sheaf).obj
          ((modulePullback k'.toLRSHom.toShHom).obj M)).obj
            ((modulePullback (i' ≫ f').toLRSHom.toShHom).obj G))
  exact (congrArg (fun arrow => tensorMap ≫ arrow)
    (projectionFormulaMap_comp_app G ((modulePullback k'.toLRSHom.toShHom).obj M))).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun arrow => arrow ≫ tail) hnat).trans (Category.assoc _ _ _)))

/-- **The pasting law along the fibre for the underived comparison of [Stacks, Tag 0GN5].**  For
two commutative squares of schemes stacked one above the other and an `𝒪_{S'}`-module `G`, the
comparison of the outer rectangle at an `𝒪_Z`-module `M` is the comparison of the lower square
at the direct image `i_* M`, followed by the direct image along `f'` of the comparison of the
upper square at `M` and the module `(f')^*G`, conjugated by two invertible factors: on the left
the comparison of the direct images along `i ≫ f`, pulled back along `g` and tensored with the
identity of `G`; on the right the comparison of the inverse images of `G` along `i' ≫ f'`,
tensored into the second factor and pushed forward along `i'` and `f'`, followed by the
comparison of the direct images along `i' ≫ f'`.

Neither square is required to be cartesian and no quasi-coherence or flatness is used. -/
theorem underivedComparison_pasteSource (w : g' ≫ f = f' ≫ g) (wi : k' ≫ i = i' ≫ g')
    (w2 : k' ≫ (i ≫ f) = (i' ≫ f') ≫ g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (M : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) :
    let tensorPullbackComparison :=
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        Z'.toRingedSpace.sheaf).obj
          ((modulePullback k'.toLRSHom.toShHom).obj M)).map
            ((pullbackSourceComp i' f').hom.app G)
    (underivedComparison w2 G).app M =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S'.toRingedSpace.sheaf).flip.obj
          (G)).map ((modulePullback g.toLRSHom.toShHom).map
            ((pushforwardSourceComp i f).inv.app M))) ≫
        (underivedComparison w G).app ((modulePushforward i.toLRSHom.toShHom).obj M) ≫
          (modulePushforward f'.toLRSHom.toShHom).map
              ((underivedComparison wi ((modulePullback f'.toLRSHom.toShHom).obj G)).app M) ≫
            (modulePushforward f'.toLRSHom.toShHom).map
                ((modulePushforward i'.toLRSHom.toShHom).map
                  tensorPullbackComparison) ≫
              (pushforwardSourceComp i' f').hom.app
                ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                    Z'.toRingedSpace.sheaf).obj (((modulePullback k'.toLRSHom.toShHom).obj M))).obj
                        (((modulePullback (i' ≫ f').toLRSHom.toShHom).obj G)))) := by
  let baseTensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    S'.toRingedSpace.sheaf
  let totalTensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    X'.toRingedSpace.sheaf
  let inverseImage := (modulePullback f'.toLRSHom.toShHom).obj G
  let directImage := modulePushforward f'.toLRSHom.toShHom
  let lowerTarget := (modulePullback g'.toLRSHom.toShHom).obj
    ((modulePushforward i.toLRSHom.toShHom).obj M)
  let upperTarget := (modulePullback k'.toLRSHom.toShHom).obj M
  let lowerMap := (baseChangeNatTrans w).app
    ((modulePushforward i.toLRSHom.toShHom).obj M)
  let upperMap := (baseChangeNatTrans wi).app M
  let lowerProjection :=
    Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f' lowerTarget G
  let upperProjection :=
    Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap i' upperTarget inverseImage
  have lowerComparison :=
    underivedComparison_app w G ((modulePushforward i.toLRSHom.toShHom).obj M)
  have upperComparison := underivedComparison_app wi inverseImage M
  have mappedUpper := (congrArg directImage.map upperComparison).trans
    (directImage.map_comp ((totalTensor.flip.obj inverseImage).map upperMap) upperProjection)
  let leftArrow := (baseTensor.flip.obj G).map
    ((modulePullback g.toLRSHom.toShHom).map ((pushforwardSourceComp i f).inv.app M))
  let rightArrow := directImage.map
      ((modulePushforward i'.toLRSHom.toShHom).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          Z'.toRingedSpace.sheaf).obj upperTarget).map
            ((pullbackSourceComp i' f').hom.app G))) ≫
    (pushforwardSourceComp i' f').hom.app
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        Z'.toRingedSpace.sheaf).obj upperTarget).obj
          ((modulePullback (i' ≫ f').toLRSHom.toShHom).obj G))
  have combined :=
    (Category.assoc ((baseTensor.flip.obj G).map lowerMap) lowerProjection
      (directImage.map ((totalTensor.flip.obj inverseImage).map upperMap) ≫
        directImage.map upperProjection ≫ rightArrow)).symm.trans
      (congrArg (fun arrow => arrow ≫
        directImage.map ((totalTensor.flip.obj inverseImage).map upperMap) ≫
          directImage.map upperProjection ≫ rightArrow) lowerComparison.symm)
  have combinedUpper :=
    (Category.assoc (directImage.map ((totalTensor.flip.obj inverseImage).map upperMap))
      (directImage.map upperProjection) rightArrow).symm.trans
        (congrArg (fun arrow => arrow ≫ rightArrow) mappedUpper.symm)
  exact (pasteSource_lhs w wi w2 G M).trans
    ((congrArg (fun arrow => leftArrow ≫ (baseTensor.flip.obj G).map lowerMap ≫ arrow)
      (pasteSource_mid wi G M)).trans
        (congrArg (fun arrow => leftArrow ≫ arrow)
          (combined.trans
            (congrArg (fun arrow =>
              (underivedComparison w G).app
                ((modulePushforward i.toLRSHom.toShHom).obj M) ≫ arrow) combinedUpper))))

/-! ### Transfer of invertibility -/

/-- The left-hand invertible factor of the pasting law. -/
private theorem isIso_pasteSource_left (g : S' ⟶ S) (i : Z ⟶ X) (f : X ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (M : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) :
    IsIso ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        S'.toRingedSpace.sheaf).flip.obj (G)).map ((modulePullback g.toLRSHom.toShHom).map
        ((pushforwardSourceComp i f).inv.app M)))) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    S'.toRingedSpace.sheaf).flip.obj G).mapIso
      ((modulePullback g.toLRSHom.toShHom).mapIso
        ((pushforwardSourceComp i f).app M).symm)).isIso_hom

/-- The right-hand invertible factor of the pasting law. -/
private theorem isIso_pasteSource_right (i' : Z' ⟶ X') (f' : X' ⟶ S')
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (N : SheafOfModules.{u} (structureSheafRing Z'.toRingedSpace)) :
    IsIso ((modulePushforward f'.toLRSHom.toShHom).map
        ((modulePushforward i'.toLRSHom.toShHom).map
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z'.toRingedSpace.sheaf).obj
              (N)).map ((pullbackSourceComp i' f').hom.app G)))) ≫
      (pushforwardSourceComp i' f').hom.app
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z'.toRingedSpace.sheaf).obj
            (N)).obj (((modulePullback (i' ≫ f').toLRSHom.toShHom).obj G))))) := by
  have h1 : IsIso ((modulePushforward f'.toLRSHom.toShHom).map
      ((modulePushforward i'.toLRSHom.toShHom).map
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z'.toRingedSpace.sheaf).obj
            (N)).map ((pullbackSourceComp i' f').hom.app G))))) :=
    ((modulePushforward f'.toLRSHom.toShHom).mapIso
        ((modulePushforward i'.toLRSHom.toShHom).mapIso
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            Z'.toRingedSpace.sheaf).obj N).mapIso
              ((pullbackSourceComp i' f').app G)))).isIso_hom
  have h2 : IsIso ((pushforwardSourceComp i' f').hom.app
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z'.toRingedSpace.sheaf).obj
          (N)).obj (((modulePullback (i' ≫ f').toLRSHom.toShHom).obj G))))) :=
    inferInstanceAs (IsIso ((pushforwardSourceComp i' f').app _).hom)
  infer_instance

/-- **The comparison of the lower square is invertible at a direct image** as soon as the
comparison of the rectangle and the comparison of the upper square are invertible: by the
pasting law along the fibre it is the second of four factors of the former, the remaining three
being the latter and two isomorphisms. -/
theorem isIso_underivedComparison_app_pushforward_of_isIso (w : g' ≫ f = f' ≫ g)
    (wi : k' ≫ i = i' ≫ g') (w2 : k' ≫ (i ≫ f) = (i' ≫ f') ≫ g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (M : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    (h2 : IsIso ((underivedComparison w2 G).app M))
    (hi : IsIso ((underivedComparison wi
      ((modulePullback f'.toLRSHom.toShHom).obj G)).app M)) :
    IsIso ((underivedComparison w G).app ((modulePushforward i.toLRSHom.toShHom).obj M)) := by
  have hc := Functor.map_isIso (modulePushforward f'.toLRSHom.toShHom)
    ((underivedComparison wi ((modulePullback f'.toLRSHom.toShHom).obj G)).app M)
  exact isIso_second_of_four (underivedComparison_pasteSource w wi w2 G M) h2
    (isIso_pasteSource_left g i f G M) hc
    (isIso_pasteSource_right i' f' G ((modulePullback k'.toLRSHom.toShHom).obj M))

/-- **The comparison of the rectangle is invertible** as soon as the comparison of the lower
square at the direct image `i_* M` and the comparison of the upper square at `M` are: by the
pasting law along the fibre it is their composite, up to two isomorphisms. -/
theorem isIso_underivedComparison_app_pushforward_of_isIso' (w : g' ≫ f = f' ≫ g)
    (wi : k' ≫ i = i' ≫ g') (w2 : k' ≫ (i ≫ f) = (i' ≫ f') ≫ g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (M : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    (hw : IsIso ((underivedComparison w G).app ((modulePushforward i.toLRSHom.toShHom).obj M)))
    (hi : IsIso ((underivedComparison wi
      ((modulePullback f'.toLRSHom.toShHom).obj G)).app M)) :
    IsIso ((underivedComparison w2 G).app M) := by
  have hc := Functor.map_isIso (modulePushforward f'.toLRSHom.toShHom)
    ((underivedComparison wi ((modulePullback f'.toLRSHom.toShHom).obj G)).app M)
  exact isIso_comp_four (underivedComparison_pasteSource w wi w2 G M)
    (isIso_pasteSource_left g i f G M) hw hc
    (isIso_pasteSource_right i' f' G ((modulePullback k'.toLRSHom.toShHom).obj M))

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
