module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The degree-zero base-change comparison for a direct image

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a commuting square of schemes and let `F` be an `𝒪_X`-module. There is a canonical
comparison morphism

  `g^* f_* F ⟶ f'_* (g')^* F`

of `𝒪_{S'}`-modules, the degree-zero case of the base-change map of [Stacks, Tag 02N7]: it is
the morphism adjoint to the direct image under `f` of the unit `F ⟶ g'_* (g')^* F`, read through
the identification `g_* f'_* = f_* g'_*` supplied by the commutativity of the square. This file
constructs it and records the one computation that identifies it, namely its effect on global
sections: it carries the pullback of a global section of `f_* F` to the pullback of the
corresponding global section of `F`.

Nothing here assumes the square is cartesian, nor that `g` is flat, nor that `f` is
quasi-compact: those hypotheses enter only when one asks for the comparison to be an
isomorphism, which is [Stacks, Tag 02KH] part (1) and is treated in
`StacksFrontier.AlgebraicGeometry.FlatBaseChange.Affine`.

## Main definitions

* `Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChangeUnit`: the adjoint form
  `f_* F ⟶ g_* f'_* (g')^* F` of the comparison.
* `Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange`: the comparison morphism
  `g^* f_* F ⟶ f'_* (g')^* F` itself.

## Main results

* `Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChangeUnit_app_top`: on global
  sections the adjoint form is the unit of `(g')^* ⊣ g'_*`; all the transport through
  `Scheme.Modules.pushforwardComp` and `Scheme.Modules.pushforwardCongr` is the identity there.
* `Stacks.AlgebraicGeometry.FlatBaseChange.unit_app_top_pushforwardBaseChange_app_top`:
  **the normalisation.** Precomposing the comparison with the unit of `g^* ⊣ g_*` on global
  sections gives the unit of `(g')^* ⊣ g'_*` on global sections.
* `Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange_app_top_unit`: the same
  normalisation read on an element.
* `Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange_naturality`: the comparison is
  natural in the module.

## Implementation notes

The adjoint form is assembled as

  `f_* F ⟶ f_* g'_* (g')^* F = (g' ≫ f)_* (g')^* F = (f' ≫ g)_* (g')^* F = g_* f'_* (g')^* F`,

using `Scheme.Modules.pushforwardComp` twice and `Scheme.Modules.pushforwardCongr` once. On
sections over an open `U` of `S` the first and third of those are the identity by
`Scheme.Modules.pushforwardComp_hom_app_app`, and the middle one is the structure map of
`F` along an equality of opens; over `U = ⊤` all the opens involved are `⊤`, so that map is the
identity as well, which is `pushforwardBaseChangeUnit_app_top`.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.FlatBaseChange

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **The adjoint form of the degree-zero base-change comparison.** For a commuting square
`g' ≫ f = f' ≫ g` and an `𝒪_X`-module `F`, this is the morphism

  `f_* F ⟶ g_* f'_* (g')^* F`

obtained by pushing the unit `F ⟶ g'_* (g')^* F` of `(g')^* ⊣ g'_*` forward along `f` and then
identifying `(g' ≫ f)_*` with `(f' ≫ g)_*`. -/
def pushforwardBaseChangeUnit (w : g' ≫ f = f' ≫ g) (F : X.Modules) :
    (Scheme.Modules.pushforward f).obj F ⟶
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f').obj
        ((Scheme.Modules.pullback g').obj F)) :=
  (Scheme.Modules.pushforward f).map
      ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F) ≫
    (Scheme.Modules.pushforwardComp g' f).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr w).hom.app _ ≫
    (Scheme.Modules.pushforwardComp f' g).inv.app _

/-- **The degree-zero base-change comparison morphism** `g^* f_* F ⟶ f'_* (g')^* F` attached to
a commuting square `g' ≫ f = f' ≫ g` of schemes and an `𝒪_X`-module `F`. It is the morphism
adjoint to `Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChangeUnit` under
`g^* ⊣ g_*`, and is the degree-zero case of the base-change map of [Stacks, Tag 02N7]. -/
def pushforwardBaseChange (w : g' ≫ f = f' ≫ g) (F : X.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj F) ⟶
      (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
    (pushforwardBaseChangeUnit w F)

/-- On global sections the adjoint form of the comparison is the unit of `(g')^* ⊣ g'_*`: every
identification used to build it is the identity over `⊤`. -/
theorem pushforwardBaseChangeUnit_app_top (w : g' ≫ f = f' ≫ g) (F : X.Modules) :
    (pushforwardBaseChangeUnit w F).app ⊤ =
      ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F).app ⊤ := by
  simp only [pushforwardBaseChangeUnit, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    eqToHom_op, eqToHom_map]
  rfl

/-- The adjoint of the comparison morphism is the adjoint form, by definition. -/
theorem homEquiv_pushforwardBaseChange (w : g' ≫ f = f' ≫ g) (F : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        (pushforwardBaseChange w F) =
      pushforwardBaseChangeUnit w F :=
  Equiv.apply_symm_apply _ _

/-- **The normalisation of the comparison morphism.** Precomposing the degree-zero base-change
comparison with the unit of `g^* ⊣ g_*`, on global sections, gives the unit of
`(g')^* ⊣ g'_*` on global sections.

Equivalently: the comparison carries the pullback along `g` of a global section of `f_* F` to
the pullback along `g'` of the corresponding global section of `F`. -/
theorem unit_app_top_pushforwardBaseChange_app_top (w : g' ≫ f = f' ≫ g) (F : X.Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((Scheme.Modules.pushforward f).obj F)).app ⊤ ≫
        (pushforwardBaseChange w F).app ⊤ =
      ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F).app ⊤ := by
  rw [← pushforwardBaseChangeUnit_app_top w F, ← homEquiv_pushforwardBaseChange w F,
    Adjunction.homEquiv_unit]
  rfl

/-- **The normalisation, read on an element.** The comparison carries the image of a global
section of `f_* F` under the unit of `g^* ⊣ g_*` to the image of the corresponding global
section of `F` under the unit of `(g')^* ⊣ g'_*`. -/
theorem pushforwardBaseChange_app_top_unit (w : g' ≫ f = f' ≫ g) (F : X.Modules)
    (a : Γ((Scheme.Modules.pushforward f).obj F, ⊤)) :
    (pushforwardBaseChange w F).app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((Scheme.Modules.pushforward f).obj F)).app ⊤ a) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F).app ⊤ a :=
  congrArg (fun m : Γ((Scheme.Modules.pushforward f).obj F, ⊤) ⟶
      Γ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F), ⊤) =>
    ConcreteCategory.hom m a) (unit_app_top_pushforwardBaseChange_app_top w F)

/-- The adjoint form of the comparison is natural in the module. -/
theorem pushforwardBaseChangeUnit_naturality (w : g' ≫ f = f' ≫ g) {F G : X.Modules}
    (t : F ⟶ G) :
    (Scheme.Modules.pushforward f).map t ≫ pushforwardBaseChangeUnit w G =
      pushforwardBaseChangeUnit w F ≫
        (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f').map
          ((Scheme.Modules.pullback g').map t)) := by
  have h : t ≫ (Scheme.Modules.pullbackPushforwardAdjunction g').unit.app G =
      (Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F ≫
        (Scheme.Modules.pushforward g').map ((Scheme.Modules.pullback g').map t) :=
    (Scheme.Modules.pullbackPushforwardAdjunction g').unit.naturality t
  rw [pushforwardBaseChangeUnit, pushforwardBaseChangeUnit, ← Category.assoc,
    ← Functor.map_comp, h, Functor.map_comp]
  generalize (Scheme.Modules.pullback g').map t = s
  simp only [Category.assoc, ← Functor.comp_map, NatTrans.naturality,
    NatTrans.naturality_assoc]

/-- The degree-zero base-change comparison is natural in the module. -/
theorem pushforwardBaseChange_naturality (w : g' ≫ f = f' ≫ g) {F G : X.Modules} (t : F ⟶ G) :
    (Scheme.Modules.pullback g).map ((Scheme.Modules.pushforward f).map t) ≫
        pushforwardBaseChange w G =
      pushforwardBaseChange w F ≫
        (Scheme.Modules.pushforward f').map ((Scheme.Modules.pullback g').map t) := by
  rw [pushforwardBaseChange, pushforwardBaseChange,
    ← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm,
    pushforwardBaseChangeUnit_naturality]

end Stacks.AlgebraicGeometry.FlatBaseChange

end
