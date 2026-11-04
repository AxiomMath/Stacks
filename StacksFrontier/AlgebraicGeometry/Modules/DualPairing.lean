module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.AlgebraicGeometry.Modules.KoszulCosection
public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkGenerators
public import StacksFrontier.AlgebraicGeometry.Reflexive.DoubleDual

/-!
# The pairing of a module with the dual of its target

Let `X` be a scheme and `τ : M ⟶ L` a morphism of `𝒪_X`-modules. Evaluating local functionals on
`L` at the images under `τ` of local sections of `M` is a bilinear pairing
`M(U) × L^∨(U) ⟶ 𝒪_X(U)`, compatible with restriction; it induces a morphism

  `M ⊗_{𝒪_X} L^∨ ⟶ 𝒪_X`,  `m ⊗ λ ↦ λ(τ m)`

out of the tensor product sheaf, the sheafification of the sectionwise tensor product (Stacks
Tag 01CA). For `τ = id_L` this is the evaluation pairing `L ⊗ L^∨ ⟶ 𝒪_X`; in general it is the
cosection of `M ⊗ L^∨` attached to `τ`, whose Koszul complex is studied in
`StacksFrontier.AlgebraicGeometry.Modules.KoszulCosection`.

## Main definitions

* `Stacks.AlgebraicGeometry.ReflexiveModules.pairingPresheaf`: the sectionwise pairing.
* `Stacks.AlgebraicGeometry.ReflexiveModules.pairing`: the induced cosection of `M ⊗ L^∨`.

## Main results

* `Stacks.AlgebraicGeometry.ReflexiveModules.pairing_tmul`: its value on a pure tensor.
* `Stacks.AlgebraicGeometry.ReflexiveModules.koszulStalkDual_pairing_tensorStalkTmul`: its stalk
  on a product of germs.

## Implementation notes

The dual is `Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf`, the internal Hom into
`𝒪_X`, and the tensor product is `Stacks.SheafOfModules.Tensor.sheafTensor`; these are the
spellings of `Stacks.ProjectiveCompletion.koszulModule`. The library's other evaluation pairing,
`Stacks.SheafOfModules.evaluation`, is stated for the dual `Stacks.SheafOfModules.dualSheaf`
built from `Stacks.SheafOfModules.sheafHom`, a different construction of the dual.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {X : Scheme.{u}} {M L : X.Modules}

/-- The sectionwise pairing `M(U) ⊗ L^∨(U) ⟶ 𝒪(U)`, `m ⊗ λ ↦ λ(τ m)`. -/
def pairingPresheaf (τ : M ⟶ L) :
    PresheafOfModules.tensorObj.{u, u} M.val (dualSheaf L).val ⟶
      (SheafOfModules.unit X.ringCatSheaf).val := by
  refine PresheafOfModules.Hom.mk (fun U ↦ ?_) ?_
  · exact ModuleCat.MonoidalCategory.tensorLift
      (fun (m : M.val.obj U) (l : (dualSheaf L).val.obj U) ↦
        (evalAt L (V := U.unop) l (τ.app U.unop m) : Γ(X, U.unop)))
      (fun m m' l => (congrArg (fun z => evalAt L (V := U.unop) l z)
          (map_add (ConcreteCategory.hom (Scheme.Modules.Hom.app τ U.unop)) m m')).trans
        (evalAt_add_right L (V := U.unop) l _ _))
      (fun a m l => (congrArg (fun z => evalAt L (V := U.unop) l z)
          (Scheme.Modules.Hom.app_smul τ (U := U.unop) a m)).trans
        (evalAt_smul_right L (V := U.unop) a l _))
      (fun m l l' => evalAt_add L l l' _)
      (fun a m l => evalAt_smul L a l _)
  · intro U V i
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m l
    obtain ⟨i, rfl⟩ : ∃ j : V.unop ⟶ U.unop, i = j.op := ⟨i.unop, rfl⟩
    have hτ : Scheme.Modules.Hom.app τ V.unop (M.presheaf.map i.op m) =
        L.presheaf.map i.op (Scheme.Modules.Hom.app τ U.unop m) :=
      (PresheafOfModules.naturality_apply τ.val i.op m)
    change evalAt L (V := V.unop) ((dualSheaf L).presheaf.map i.op l)
        (Scheme.Modules.Hom.app τ V.unop (M.presheaf.map i.op m)) =
      X.presheaf.map i.op (evalAt L (V := U.unop) l (Scheme.Modules.Hom.app τ U.unop m))
    rw [hτ]
    exact evalAt_map L (leOfHom i) l _

/-- **The pairing `M ⊗ L^∨ ⟶ 𝒪`, `m ⊗ λ ↦ λ(τ m)`**, of a morphism `τ : M ⟶ L`. -/
def pairing (τ : M ⟶ L) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj (dualSheaf L) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  PresheafOfModules.tensorSheafDesc (J := Opens.grothendieckTopology X) (Osharp := X.sheaf)
    (F := M) (G := dualSheaf L) (Q := SheafOfModules.unit X.ringCatSheaf) (pairingPresheaf τ)

/-- The pairing on the image of a pure tensor of sections is the value `l(τ m)`. -/
theorem pairing_tmul (τ : M ⟶ L) (U : X.Opens) (m : M.val.obj (op U))
    (l : (dualSheaf L).val.obj (op U)) :
    (pairing τ).val.app (op U)
      ((PresheafOfModules.tensorSheafUnit M (dualSheaf L)).app (op U) (m ⊗ₜ l)) =
      evalAt L (V := U) l (Scheme.Modules.Hom.app τ U m) :=
  PresheafOfModules.tensorSheafDesc_unit (pairingPresheaf τ) (op U) m l

/-- **The stalk of the pairing on a product of germs**: the functional induced by the pairing on
the stalk at `x` sends the product of the germs of `m` and `l` to the germ of `l(τ m)`. -/
theorem koszulStalkDual_pairing_tensorStalkTmul (τ : M ⟶ L) (x : X) (U : X.Opens) (hx : x ∈ U)
    (m : M.val.obj (op U)) (l : (dualSheaf L).val.obj (op U)) :
    Scheme.Modules.koszulStalkDual (pairing τ) x
        (tensorStalkTmul M (dualSheaf L) x (M.presheaf.germ U x hx m)
          ((dualSheaf L).presheaf.germ U x hx l)) =
      TopCat.Presheaf.germ X.sheaf.obj U x hx
        (evalAt L (V := U) l (Scheme.Modules.Hom.app τ U m)) := by
  rw [tensorStalkTmul_germ]
  exact (Scheme.Modules.koszulStalkDual_germ (pairing τ) x U hx _).trans
    (congrArg (TopCat.Presheaf.germ X.sheaf.obj U x hx) (pairing_tmul τ U m l))

end Stacks.AlgebraicGeometry.ReflexiveModules

end
