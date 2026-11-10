module

public import StacksFrontier.Topology.Sheaves.Modules.ConormalSequenceStalkSquare
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentPresentationQuasiIso

/-!
# The stalks of the conormal maps of a square of sheaves of rings

Let

```
B₁ ──β──▸ B₂
▲          ▲
φ₁         φ₂
│          │
A₁ ──ψ──▸ A₂
▲          ▲
a₁         a₂
│          │
R₁ ──ρ──▸ R₂
```

be a commutative square of sheaves of commutative rings on a topological space `X` with `φ₁` and
`φ₂` locally surjective, and let `x` be a point of `X`.  The two maps of sheaves of modules it
induces — on conormal sheaves and on tensor-differentials sheaves — have stalks at `x`, and this
file identifies them with `Algebra.Extension.Cotangent.map` and
`Algebra.Extension.CotangentSpace.map` of the morphism
`Stacks.Sites.Conormal.stalkExtensionHomOfSquare` of stalk extensions.

This is the square-level analogue of the `Comparison` section of
`StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentPresentationQuasiIso`: there the base sheaf
`R` and the target sheaf `B` are fixed and only the presentation `A` varies, which is what
Stacks 08TL needs; here all three may vary, which is what Stacks 08TX needs.

## Main definitions

* `Stacks.Sites.Conormal.conormalSheafMapOfSquareStalk` and
  `Stacks.Sites.Conormal.tensorSheafMapOfSquareStalk`: the maps induced on the stalks of the two
  left-hand, respectively right-hand, terms of the conormal sequences.

## Main results

* `Stacks.Sites.Conormal.conormalSheafMapOfSquareStalk_eq_cotangentMap`: the stalk of the map of
  conormal sheaves is `Algebra.Extension.Cotangent.map` of the induced morphism of stalk
  extensions.
* `Stacks.Sites.Conormal.tensorSheafMapOfSquareStalk_eq_cotangentSpaceMap`: the stalk of the map
  of tensor-differentials sheaves is `Algebra.Extension.CotangentSpace.map` of the same morphism.
* `Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase` and
  `Stacks.Sites.Conormal.stalkIsScalarTowerSquareTarget`: the two towers
  `R₁ₓ → R₂ₓ → B₂ₓ` and `R₁ₓ → B₁ₓ → B₂ₓ` through which `B₂ₓ` is an `R₁ₓ`-algebra.

## Implementation notes

`Algebra.Extension.Cotangent.map` of a morphism from an extension of `B₁ₓ` over `R₁ₓ` to an
extension of `B₂ₓ` over `R₂ₓ` needs `B₂ₓ` to be an `R₁ₓ`-algebra for which `R₁ₓ → R₂ₓ → B₂ₓ` is
a tower.  As elsewhere in this area that algebra structure is read off a morphism `d : R₁ ⟶ B₂`
of sheaves together with an equation it satisfies, rather than off a composite, so that the
structures appearing in two different statements about the same square are the same structure and
not merely propositionally equal ones.  Both composites `ρ ≫ c₂` and `c₁ ≫ β` are available as
such a `d`; they agree by `Stacks.Sites.Conormal.baseComparison_eq_of_square`, and
`stalkIsScalarTowerSquareBase` and `stalkIsScalarTowerSquareTarget` are the two towers obtained
from the two factorisations.

Neither of the two statements is an equality of linear maps: the identification of the stalk of
the conormal sheaf is linear over `A₁ₓ` at the source and over `A₂ₓ` at the target, so the two
sides of `conormalSheafMapOfSquareStalk_eq_cotangentMap` are linear over different rings and only
their underlying additive maps can be compared.  Accordingly the degree `-1` statement is proved
pointwise, on the generators supplied by
`Stacks.Sites.Conormal.exists_germ_conormalClass_eq`, and the degree `0` statement by the
additive extensionality principle
`Stacks.Sites.Conormal.tensorDifferentialsSheafStalk_hom_ext`, whose two arguments are
`AddMonoidHom`s.

## References

* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
* [Stacks Project, Tag 07BM](https://stacks.math.columbia.edu/tag/07BM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct

universe u

noncomputable section

namespace Stacks.Sites.Conormal

open Stacks.RelativeDifferentialStalk (algebraStalk)

section Square

variable {X : TopCat.{u}}
  (R₁ R₂ A₁ A₂ B₁ B₂ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a₁ : R₁ ⟶ A₁) (a₂ : R₂ ⟶ A₂) (φ₁ : A₁ ⟶ B₁) (φ₂ : A₂ ⟶ B₂)
  (c₁ : R₁ ⟶ B₁) (c₂ : R₂ ⟶ B₂) (d : R₁ ⟶ B₂)
  (ρ : R₁ ⟶ R₂) (ψ : A₁ ⟶ A₂) (β : B₁ ⟶ B₂)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₁.hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₂.hom] (x : X)

/-! ### The outer base morphism and its two towers -/

omit [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₁.hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₂.hom] in
/-- **The two ways round the square agree.**  The composites `R₁ ⟶ R₂ ⟶ B₂` and
`R₁ ⟶ B₁ ⟶ B₂` of the structural morphisms of a commutative square are equal, so either may be
taken as the morphism `R₁ ⟶ B₂` presenting `B₂` as an `R₁`-algebra. -/
theorem baseComparison_eq_of_square (hc₁ : a₁ ≫ φ₁ = c₁) (hc₂ : a₂ ≫ φ₂ = c₂)
    (ha : ρ ≫ a₂ = a₁ ≫ ψ) (hsq : ψ ≫ φ₂ = φ₁ ≫ β) : ρ ≫ c₂ = c₁ ≫ β := by
  rw [← hc₁, ← hc₂, ← Category.assoc, ha, Category.assoc, hsq, Category.assoc]

/-- Stalks of a composite `u ≫ v = w` of morphisms of sheaves of rings form a scalar tower. -/
private theorem stalk_isScalarTower_of_comp
    {O₁ O₂ O₃ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    (u : O₁ ⟶ O₂) (v : O₂ ⟶ O₃) (w : O₁ ⟶ O₃) (h : u ≫ v = w) :
    letI := algebraStalk u.hom x
    letI := algebraStalk v.hom x
    letI := algebraStalk w.hom x
    IsScalarTower (ToType (TopCat.Presheaf.stalk O₁.obj x))
      (ToType (TopCat.Presheaf.stalk O₂.obj x)) (ToType (TopCat.Presheaf.stalk O₃.obj x)) :=
  by
  subst h
  let := algebraStalk u.hom x
  let := algebraStalk v.hom x
  let := algebraStalk (u ≫ v).hom x
  exact IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map_comp u.hom v.hom))

/-- **`R₁ₓ → R₂ₓ → B₂ₓ` is a tower.**  Both `R₂ₓ → B₂ₓ` and the chosen `R₁ₓ → B₂ₓ` are stalks of
morphisms of sheaves, and taking stalks is functorial. -/
theorem stalkIsScalarTowerSquareBase (hd : ρ ≫ c₂ = d) :
    letI := algebraStalk ρ.hom x
    letI := algebraStalk c₂.hom x
    letI := algebraStalk d.hom x
    IsScalarTower (ToType (TopCat.Presheaf.stalk R₁.obj x))
      (ToType (TopCat.Presheaf.stalk R₂.obj x)) (ToType (TopCat.Presheaf.stalk B₂.obj x)) :=
  stalk_isScalarTower_of_comp x ρ c₂ d hd

/-- **`R₁ₓ → B₁ₓ → B₂ₓ` is a tower**, for the same `R₁ₓ`-algebra structure on `B₂ₓ` read off the
other way round the square. -/
theorem stalkIsScalarTowerSquareTarget (hd : c₁ ≫ β = d) :
    letI := algebraStalk c₁.hom x
    letI := algebraStalk β.hom x
    letI := algebraStalk d.hom x
    IsScalarTower (ToType (TopCat.Presheaf.stalk R₁.obj x))
      (ToType (TopCat.Presheaf.stalk B₁.obj x)) (ToType (TopCat.Presheaf.stalk B₂.obj x)) :=
  stalk_isScalarTower_of_comp x c₁ β d hd

omit [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₁.hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₂.hom] in
/-- Taking stalks turns a commutative square of morphisms of sheaves of commutative rings into a
commutative square of ring homomorphisms. -/
theorem stalkFunctor_map_square_apply
    {O₁ O₂ O₃ O₄ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    (u : O₁ ⟶ O₂) (v : O₂ ⟶ O₄) (w : O₁ ⟶ O₃) (t : O₃ ⟶ O₄) (h : u ≫ v = w ≫ t)
    (y : ToType (TopCat.Presheaf.stalk O₁.obj x)) :
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map v.hom).hom
        (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map u.hom).hom y) =
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map t.hom).hom
        (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map w.hom).hom y) :=
  (stalkFunctor_map_comp_apply u v (u ≫ v) rfl x y).trans
    (stalkFunctor_map_comp_apply w t (u ≫ v) h.symm x y).symm

variable (hsq : ψ ≫ φ₂ = φ₁ ≫ β)

/-! ### The stalk of the map of conormal sheaves -/

/-- The map induced on the stalks of the conormal sheaves by a commutative square
`ψ ≫ φ₂ = φ₁ ≫ β`.  Restriction of scalars along `β` leaves the underlying sheaf of abelian
groups of the target untouched, so this is the stalk of the map of sheaves of modules read as a
map of abelian groups. -/
def conormalSheafMapOfSquareStalk :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (conormalSheaf (Opens.grothendieckTopology X) A₁ B₁ φ₁).val.presheaf x) →+
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (conormalSheaf (Opens.grothendieckTopology X) A₂ B₂ φ₂).val.presheaf x) :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B₁).obj).map
      (conormalSheafMapOfSquare.{u, u, u, u} (Opens.grothendieckTopology X) A₁ A₂ B₁ B₂
        φ₁ φ₂ ψ β hsq).val)).hom

/-- The stalk of the map of conormal sheaves carries the germ of a section to the germ of its
image. -/
theorem conormalSheafMapOfSquareStalk_germ (U : Opens X) (hx : x ∈ U)
    (s : (conormalSheaf (Opens.grothendieckTopology X) A₁ B₁ φ₁).val.obj (op U)) :
    conormalSheafMapOfSquareStalk A₁ A₂ B₁ B₂ φ₁ φ₂ ψ β x hsq
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (conormalSheaf (Opens.grothendieckTopology X) A₁ B₁ φ₁).val.presheaf U x hx s) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (conormalSheaf (Opens.grothendieckTopology X) A₂ B₂ φ₂).val.presheaf U x hx
        ((conormalSheafMapOfSquare.{u, u, u, u} (Opens.grothendieckTopology X) A₁ A₂ B₁ B₂
          φ₁ φ₂ ψ β hsq).val.app (op U) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hx
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B₁).obj).map
      (conormalSheafMapOfSquare.{u, u, u, u} (Opens.grothendieckTopology X) A₁ A₂ B₁ B₂
        φ₁ φ₂ ψ β hsq).val) s

/-- **The stalk of the map of conormal sheaves of a square is the cotangent map of the induced
morphism of stalk extensions.**  Both send the germ of the conormal class of a section `y` of the
kernel of `φ₁` to the conormal class of the germ of `ψ(y)`; conormal classes of sections generate
the stalk, so this determines the stalk map.

This is `Stacks.Sites.Conormal.conormalSheafMapOfFacStalk_eq_cotangentMap` with the base sheaf
and the target sheaf allowed to vary. -/
theorem conormalSheafMapOfSquareStalk_eq_cotangentMap
    (hc₁ : a₁ ≫ φ₁ = c₁) (hc₂ : a₂ ≫ φ₂ = c₂) (hd : ρ ≫ c₂ = d) (ha : ρ ≫ a₂ = a₁ ≫ ψ)
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (conormalSheaf (Opens.grothendieckTopology X) A₁ B₁ φ₁).val.presheaf x)) :
    letI := stalkAlgebraBase R₁ B₁ c₁ x
    letI := stalkAlgebraBase R₂ B₂ c₂ x
    letI := algebraStalk ρ.hom x
    letI := algebraStalk β.hom x
    letI := algebraStalk d.hom x
    letI := stalkIsScalarTowerSquareBase R₁ R₂ B₂ c₂ d ρ x hd
    conormalSheafStalkLinearEquiv A₂ B₂ φ₂ x
        (conormalSheafMapOfSquareStalk A₁ A₂ B₁ B₂ φ₁ φ₂ ψ β x hsq ξ) =
      Algebra.Extension.Cotangent.map
          (stalkExtensionHomOfSquare R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ c₁ c₂ ρ ψ β x
            hc₁ hc₂ ha hsq)
        (conormalSheafStalkLinearEquiv A₁ B₁ φ₁ x ξ) := by
  let := stalkAlgebraBase R₁ B₁ c₁ x
  let := stalkAlgebraBase R₂ B₂ c₂ x
  let := algebraStalk ρ.hom x
  let := algebraStalk β.hom x
  let := algebraStalk d.hom x
  let := stalkIsScalarTowerSquareBase R₁ R₂ B₂ c₂ d ρ x hd
  obtain ⟨U, hx, y, rfl⟩ := exists_germ_conormalClass_eq R₁ A₁ B₁ a₁ φ₁ x ξ
  refine Eq.trans (congrArg (conormalSheafStalkLinearEquiv A₂ B₂ φ₂ x)
    ((conormalSheafMapOfSquareStalk_germ A₁ A₂ B₁ B₂ φ₁ φ₂ ψ β x hsq U hx _).trans
      (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (conormalSheaf (Opens.grothendieckTopology X) A₂ B₂ φ₂).val.presheaf U x hx).hom
        (conormalSheafMapOfSquare_conormalClass.{u, u, u, u} (Opens.grothendieckTopology X)
          R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ β hsq (op U) y)))) ?_
  refine Eq.trans (conormalSheafStalkLinearEquiv_germ_conormalClass A₂ B₂ φ₂ x R₂ a₂ U hx _) ?_
  refine Eq.symm (Eq.trans (congrArg (Algebra.Extension.Cotangent.map
    (stalkExtensionHomOfSquare R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ c₁ c₂ ρ ψ β x hc₁ hc₂ ha hsq))
    (conormalSheafStalkLinearEquiv_germ_conormalClass A₁ B₁ φ₁ x R₁ a₁ U hx y)) ?_)
  refine Eq.trans (Algebra.Extension.Cotangent.map_mk
    (stalkExtensionHomOfSquare R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ c₁ c₂ ρ ψ β x
      hc₁ hc₂ ha hsq) _) ?_
  exact congrArg (stalkKernelIdeal φ₂.hom x).toCotangent
    (Subtype.ext (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx ψ.hom
      (y : A₁.obj.obj (op U))))

/-! ### The stalk of the map of tensor-differentials sheaves -/

variable (ha : ρ ≫ a₂ = a₁ ≫ ψ)

/-- The map of tensor-differentials sheaves induced by a commutative square sends the image of
`b ⊗ d f` under the unit of sheafification to the image of `ψ(b) ⊗ d (ψ f)`. -/
theorem tensorSheafMapOfSquare_toAssociatedModule_tmul_d (U : (Opens X)ᵒᵖ)
    (b : A₁.obj.obj U ⧸ kernelIdeal φ₁.hom U) (f : A₁.obj.obj U) :
    (tensorSheafMapOfSquare.{u, u, u, u} (Opens.grothendieckTopology X) R₁ R₂ A₁ A₂ B₁ B₂
          a₁ a₂ φ₁ φ₂ ψ β ρ hsq ha).val.app U
        (toAssociatedModule (Opens.grothendieckTopology X) A₁ B₁ φ₁
          (tensorPresheaf φ₁.hom a₁.hom) U
          (b ⊗ₜ[A₁.obj.obj U] CommRingCat.KaehlerDifferential.d (f := a₁.hom.app U) f)) =
      toAssociatedModule (Opens.grothendieckTopology X) A₂ B₂ φ₂
        (tensorPresheaf φ₂.hom a₂.hom) U
        (quotientMapOfSquare φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) U b
          ⊗ₜ[A₂.obj.obj U]
          CommRingCat.KaehlerDifferential.d (f := a₂.hom.app U) (ψ.hom.app U f)) := by
  refine Eq.trans (tensorSheafMapOfSquare_toAssociatedModule.{u, u, u, u}
    (Opens.grothendieckTopology X) R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ β ρ hsq ha U _) ?_
  refine congrArg (toAssociatedModule (Opens.grothendieckTopology X) A₂ B₂ φ₂
    (tensorPresheaf φ₂.hom a₂.hom) U) ?_
  refine (TensorProduct.map_tmul _ _ _ _).trans ?_
  exact congrArg₂ (fun q (ω : (differentialsPresheaf a₂.hom).obj U) ↦ q ⊗ₜ[A₂.obj.obj U] ω)
    rfl (differentialsMapOfSquare_d ψ.hom a₁.hom a₂.hom ρ.hom (hom_of_square ha) U f)

/-- The map induced on the stalks of the tensor-differentials sheaves by a commutative square
`ψ ≫ φ₂ = φ₁ ≫ β` over a square `ρ ≫ a₂ = a₁ ≫ ψ` of base rings. -/
def tensorSheafMapOfSquareStalk :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R₁ A₁ B₁ a₁ φ₁).val.presheaf
        x) →+
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R₂ A₂ B₂ a₂ φ₂).val.presheaf
        x) :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B₁).obj).map
      (tensorSheafMapOfSquare.{u, u, u, u} (Opens.grothendieckTopology X) R₁ R₂ A₁ A₂ B₁ B₂
        a₁ a₂ φ₁ φ₂ ψ β ρ hsq ha).val)).hom

/-- The stalk of the map of tensor-differentials sheaves carries the germ of a section to the
germ of its image. -/
theorem tensorSheafMapOfSquareStalk_germ (U : Opens X) (hx : x ∈ U)
    (s : (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R₁ A₁ B₁ a₁ φ₁).val.obj
      (op U)) :
    tensorSheafMapOfSquareStalk R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ρ ψ β x hsq ha
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R₁ A₁ B₁ a₁ φ₁).val.presheaf
          U x hx s) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R₂ A₂ B₂ a₂ φ₂).val.presheaf
        U x hx
        ((tensorSheafMapOfSquare.{u, u, u, u} (Opens.grothendieckTopology X) R₁ R₂ A₁ A₂ B₁ B₂
          a₁ a₂ φ₁ φ₂ ψ β ρ hsq ha).val.app (op U) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hx
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B₁).obj).map
      (tensorSheafMapOfSquare.{u, u, u, u} (Opens.grothendieckTopology X) R₁ R₂ A₁ A₂ B₁ B₂
        a₁ a₂ φ₁ φ₂ ψ β ρ hsq ha).val) s

/-- **The stalk of the map of tensor-differentials sheaves of a square is the cotangent-space map
of the induced morphism of stalk extensions.**  Both send the germ of the local section `b ⊗ d f`
to the tensor of the image of the germ of `b` in `B₂ₓ` with `d (ψ(f)ₓ)`; those germs generate the
stalk, so this determines the stalk map.

This is `Stacks.Sites.Conormal.tensorSheafMapOfFacStalk_eq_cotangentSpaceMap` with the base sheaf
and the target sheaf allowed to vary. -/
theorem tensorSheafMapOfSquareStalk_eq_cotangentSpaceMap
    (hc₁ : a₁ ≫ φ₁ = c₁) (hc₂ : a₂ ≫ φ₂ = c₂) (hd : ρ ≫ c₂ = d)
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R₁ A₁ B₁ a₁ φ₁).val.presheaf x)) :
    letI := algebraStalk a₁.hom x
    letI := algebraStalk φ₁.hom x
    letI := algebraStalk a₂.hom x
    letI := algebraStalk φ₂.hom x
    letI := stalkAlgebraBase R₁ B₁ c₁ x
    letI := stalkAlgebraBase R₂ B₂ c₂ x
    letI := algebraStalk ρ.hom x
    letI := algebraStalk β.hom x
    letI := algebraStalk d.hom x
    letI := stalkIsScalarTowerSquareBase R₁ R₂ B₂ c₂ d ρ x hd
    cotangentSpaceStalkLinearEquiv R₂ A₂ B₂ a₂ φ₂ x
        (tensorSheafMapOfSquareStalk R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ρ ψ β x hsq ha ξ) =
      Algebra.Extension.CotangentSpace.map
          (stalkExtensionHomOfSquare R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ c₁ c₂ ρ ψ β x
            hc₁ hc₂ ha hsq)
        (cotangentSpaceStalkLinearEquiv R₁ A₁ B₁ a₁ φ₁ x ξ) := by
  let := algebraStalk a₁.hom x
  let := algebraStalk φ₁.hom x
  let := algebraStalk a₂.hom x
  let := algebraStalk φ₂.hom x
  let := stalkAlgebraBase R₁ B₁ c₁ x
  let := stalkAlgebraBase R₂ B₂ c₂ x
  let := algebraStalk ρ.hom x
  let := algebraStalk β.hom x
  let := algebraStalk d.hom x
  let := stalkIsScalarTowerSquareBase R₁ R₂ B₂ c₂ d ρ x hd
  refine DFunLike.congr_fun (tensorDifferentialsSheafStalk_hom_ext R₁ A₁ B₁ a₁ φ₁ x
    ((cotangentSpaceStalkLinearEquiv R₂ A₂ B₂ a₂ φ₂ x).toLinearMap.toAddMonoidHom.comp
      (tensorSheafMapOfSquareStalk R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ρ ψ β x hsq ha))
    ((Algebra.Extension.CotangentSpace.map
        (stalkExtensionHomOfSquare R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ c₁ c₂ ρ ψ β x
          hc₁ hc₂ ha hsq)).toAddMonoidHom.comp
      (cotangentSpaceStalkLinearEquiv R₁ A₁ B₁ a₁ φ₁ x).toLinearMap.toAddMonoidHom) ?_) ξ
  intro U hx b f
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  change cotangentSpaceStalkLinearEquiv R₂ A₂ B₂ a₂ φ₂ x
      (tensorSheafMapOfSquareStalk R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ρ ψ β x hsq ha _) = _
  refine Eq.trans (congrArg (cotangentSpaceStalkLinearEquiv R₂ A₂ B₂ a₂ φ₂ x)
    ((tensorSheafMapOfSquareStalk_germ R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ρ ψ β x hsq ha
        U hx _).trans
      (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R₂ A₂ B₂ a₂ φ₂).val.presheaf
        U x hx).hom
        (tensorSheafMapOfSquare_toAssociatedModule_tmul_d R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ρ ψ β
          hsq ha (op U) _ f)))) ?_
  refine Eq.trans (cotangentSpaceStalkLinearEquiv_germ_tmul_d R₂ A₂ B₂ a₂ φ₂ x U hx _ _) ?_
  refine Eq.symm (Eq.trans (congrArg (Algebra.Extension.CotangentSpace.map
      (stalkExtensionHomOfSquare R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ c₁ c₂ ρ ψ β x hc₁ hc₂ ha hsq))
    (cotangentSpaceStalkLinearEquiv_germ_tmul_d R₁ A₁ B₁ a₁ φ₁ x U hx _ f)) ?_)
  refine Eq.trans (Algebra.Extension.CotangentSpace.map_tmul
    (stalkExtensionHomOfSquare R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ c₁ c₂ ρ ψ β x
      hc₁ hc₂ ha hsq) _ _) ?_
  refine congrArg₂ (fun (bb : ToType (TopCat.Presheaf.stalk B₂.obj x))
      (ω : KaehlerDifferential (ToType (TopCat.Presheaf.stalk R₂.obj x))
        (ToType (TopCat.Presheaf.stalk A₂.obj x))) =>
      bb ⊗ₜ[ToType (TopCat.Presheaf.stalk A₂.obj x)] ω) ?_ ?_
  · refine Eq.trans (stalkFunctor_map_square_apply x ψ φ₂ φ₁ β hsq
      ((TopCat.Presheaf.germ A₁.obj U x hx).hom b)).symm ?_
    exact congrArg ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ₂.hom).hom
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx ψ.hom b)
  · exact congrArg (KaehlerDifferential.D (ToType (TopCat.Presheaf.stalk R₂.obj x))
      (ToType (TopCat.Presheaf.stalk A₂.obj x)))
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx ψ.hom f)

end Square

end Stacks.Sites.Conormal

end

end
