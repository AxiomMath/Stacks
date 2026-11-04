module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.TensorHomAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# The tensor--internal-Hom adjunction for sheaves of modules

Let `O` be a sheaf of commutative rings on a site `(C, J)`. For sheaves of `O`-modules `F`,
`G`, `H`, morphisms out of the tensor product are canonically identified with morphisms into
the internal Hom sheaf,

`Hom(F ⊗_O G, H) = Hom(F, Hom_O(G, H))`.

This is the sheaf clause of Stacks 03EO. The tensor product of sheaves of modules is the
sheafification of the objectwise tensor product of the underlying presheaves, so a morphism
out of it is, by the sheafification adjunction, the same thing as a morphism out of the
objectwise tensor product of presheaves; and that in turn is the presheaf clause of the same
tag. The internal Hom sheaf needs no sheafification: Stacks 03EM says the internal Hom
presheaf is already a sheaf once its target is.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.siteSheafInternalHom`: the internal Hom presheaf of Stacks
  03EM, equipped with the sheaf condition that tag supplies. It is the object part of
  `Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor`.

## Main results

* `Stacks.SheafOfModules.InternalHom.sheafTensorHomEquivPlain`: the canonical correspondence of
  morphisms.
* `Stacks.SheafOfModules.InternalHom.sheafTensorHomEquivPlain_apply`: on local sections it is the
  usual currying formula, which pins the correspondence down.
* `Stacks.PresheafOfModules.InternalHom.presheafTensorHomEquiv_section_apply`: the currying
  formula for the presheaf correspondence, read on plain sections over an arbitrary object of
  the slice category.

## Implementation notes

`presheafTensorHomEquiv_section_apply` is the engine of the whole file. The presheaf
correspondence is pinned down by `presheafTensorHomEquiv_apply`, which is stated through the
retypings of the presheaf currying development of Stacks 03EO so that each identification of
a section of `M` over `W` with a section of `M|_U` over `h : W ⟶ U` is checked once, at default
transparency. Those retypings are the identity on the underlying element, so the same equation
also holds with every section written at its plain spelling; stating that form once, as a
definitional equality, means no later step has to rewrite across the identification. Nothing in
this file needs a relaxed transparency, a raised heartbeat budget or an `erw`.

The one genuinely propositional ingredient is that restricting a section along an identity does
nothing, `F.map (𝟙 U).op x = x`. This cannot be reached by `rw [PresheafOfModules.map_id]`: the
goal is stated with `x` on the right at the unrestricted spelling, which is not type-correct at
`implicit` transparency, and the rewrite is refused. Applying the coercion to the equation
instead, as `congrArg (fun φ ↦ ConcreteCategory.hom φ x) (F.map_id (op U))`, avoids the issue
entirely.

The structure sheaf is taken valued in `CommRingCat.{max u v}` and the modules at the same
universe. This is forced by the presheaf clause, whose ring universe is tied to `max u v` by
the monoidal structure on presheaves of modules.

Only the sheaf clause of Stacks 03EO is proved here; the presheaf clauses are
`Stacks.PresheafOfModules.InternalHom.presheafInternalHomTensorIso` (the slice-level currying
isomorphism and its three naturality statements) and
`Stacks.PresheafOfModules.InternalHom.presheafTensorHomAdjunction` (the
global presheaf adjunction), where they are left untagged so that the 03EO tag can be placed
once over its whole covering set.

## References

* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM), the sheaf condition
  for the internal Hom presheaf.
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB), the tensor product of
  sheaves of modules.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite

/-! ### Tag 03EO is NOT claimed here

Tag 03EO has four parts. Three are accounted for: the two presheaf clauses are untagged
(`presheafInternalHomTensorIso` and `presheafTensorHomAdjunction`), and the sheaf
adjunction is the content of this file.  The fourth,
`03EO__sheaf_internal_hom_tensor_iso` — a `sheafInternalHomTensorIso` with its `_hom_app_tmul`
and three naturality clauses — is not available, and the ringed-space statement
`Stacks.SheafOfModules.internalHomTensorIso`
(`StacksFrontier/Topology/Sheaves/Modules/TensorAndDuals/InternalHom.lean`) is a different result
carrying tag 01CN.

A tag lands only when its whole covering set lands, so nothing here carries `@[stacks 03EO]`.
-/

namespace Stacks.PresheafOfModules.InternalHom

universe v u

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{max u v})
variable (F G H : _root_.PresheafOfModules.{max u v} (Oforget O))

/-- The currying correspondence of the presheaf clause of Stacks 03EO, read on plain sections:
the morphism `F ⟶ Hom_O(G, H)` attached to `b : F ⊗ G ⟶ H` sends a section `x` of `F` over `U`
to the map taking a section `y` of `G` over an object `V` of `C/U` to `b (x|_V ⊗ y)`.

This is `presheafTensorHomEquiv_apply` with every section written at its unrestricted
spelling, which the retypings of that statement identify definitionally. -/
theorem presheafTensorHomEquiv_section_apply (b : F ⊗ G ⟶ H) (U : C) (x : F.obj (op U))
    (V : (Over U)ᵒᵖ) (y : ((restrFun O U).obj G).obj V) :
    ((((presheafTensorHomEquiv O F G H b).app (op U)).hom x).app V).hom y =
      (b.app (op V.unop.left)).hom
        ((ConcreteCategory.hom (F.map V.unop.hom.op)) x ⊗ₜ[O.obj (op V.unop.left)] y) :=
  rfl

end Stacks.PresheafOfModules.InternalHom

namespace Stacks.SheafOfModules.InternalHom

open Stacks.PresheafOfModules.InternalHom (presheafTensorHomEquiv
  presheafTensorHomEquiv_section_apply)

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})

/-- The internal Hom sheaf of two sheaves of modules: the internal Hom presheaf of Stacks
03EM, which that tag shows is already a sheaf when its target is.

The name says `site` because the sheaf of rings is spelled `underlyingRingSheaf J O` here, where
the ringed-site development spells it `AlgebraicGeometry.RingedSite.ringSheaf`;
`Stacks.SheafOfModules.InternalHom.sheafInternalHom` is the same construction at that spelling,
and instance search does not connect the two. -/
noncomputable def siteSheafInternalHom
    (G H : _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) :=
  ⟨internalHom O.obj G.val H.val, internalHom_isSheaf O.obj G.val H.val H.isSheaf⟩

/-- **Stacks 03EO, sheaf case.** The canonical tensor--internal-Hom correspondence on sheaves
of modules: morphisms out of `F ⊗_O G` are the same thing as morphisms into `Hom_O(G, H)`.

It is the presheaf correspondence transported through the sheafification adjunction: a morphism
out of the tensor sheaf is a morphism out of the objectwise tensor presheaf, hence a morphism
into the internal Hom presheaf, which is already a sheaf. -/
noncomputable def sheafTensorHomEquivPlain
    (F G H :
      _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj F).obj G ⟶ H) ≃
      (F ⟶ siteSheafInternalHom J O G H) :=
  (_root_.PresheafOfModules.sheafificationHomEquiv
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).obj)).trans
    ((presheafTensorHomEquiv O.obj F.val G.val H.val).trans
      { toFun := fun f ↦ ⟨f⟩
        invFun := fun f ↦ f.val
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl })

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
/-- **Stacks 03EO, sheaf case.** The correspondence sends `b` to the morphism locally given by
`x ↦ (y ↦ b (x ⊗ y))`, the pure tensor being read in the tensor sheaf through the unit of the
sheafification adjunction. This evaluation equation determines the correspondence. -/
theorem sheafTensorHomEquivPlain_apply
    (F G H : _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))
    (b : ((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj F).obj G ⟶ H)
    (U : C) (x : F.val.obj (op U)) (y : G.val.obj (op U)) :
    (((sheafTensorHomEquivPlain J O F G H b).val.app (op U) x).app
      (op (Over.mk (𝟙 U)))).hom y =
    b.val.app (op U)
        (((_root_.PresheafOfModules.sheafificationAdjunction
          (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).obj)).unit.app
            (F.val ⊗ G.val)).app (op U)
              (x ⊗ₜ[O.obj.obj (op U)] y)) := by
  have hid : (ConcreteCategory.hom (F.val.map (𝟙 U).op)) x = x :=
    congrArg (fun φ ↦ (ConcreteCategory.hom φ) x) (F.val.map_id (op U))
  let e := _root_.PresheafOfModules.sheafificationHomEquiv
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).obj) b
  exact (presheafTensorHomEquiv_section_apply O.obj F.val G.val H.val e U x
    (op (Over.mk (𝟙 U))) y).trans
    (congrArg (fun t ↦ ConcreteCategory.hom (e.app (op U)) (t ⊗ₜ[O.obj.obj (op U)] y)) hid)

end Stacks.SheafOfModules.InternalHom

end
