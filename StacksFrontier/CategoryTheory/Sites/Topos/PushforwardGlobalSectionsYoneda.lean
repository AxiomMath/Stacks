module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingTerminalSections
public import StacksFrontier.CategoryTheory.Sites.Topos.PushforwardSectionsRingEquiv

/-!
# A global section of a direct image, read as a function on the inverse image of a representable

Let `g` be a morphism of topoi from `Sh(C, J)` to `Sh(D, K)` with `K` subcanonical, let `E` be a
sheaf of types on `(C, J)`, and suppose the two underlying categories have terminal objects `T`
and `T'`.  Two identifications of global sections are then available:

* `MorphismOfTopoi.pushforwardTerminalSectionsEquiv`, which reads a section of `g_*E` over `T'` as
  a section of `E` over `T`; and
* `MorphismOfTopoi.inverseImageYonedaRingEquiv` (and the underlying bijection of the adjunction
  followed by Yoneda), which reads a section of `g_*E` over an object `V` of `D` as a morphism of
  sheaves `g⁻¹h_V ⟶ E`.

This file proves that the two agree in the only way they can: a **global** section `x` of `g_*E`,
restricted to `V`, is carried by the second identification to the *constant* function on `g⁻¹h_V`
whose value is the global section of `E` that the first identification attaches to `x`.

Equivalently, and this is the form proved first, the morphism `h_V ⟶ g_*E` named by the
restriction of `x` factors through the terminal sheaf, and so does its transpose
`g⁻¹h_V ⟶ E`; the factorization is forced, because `g⁻¹` carries the terminal sheaf to the
terminal sheaf (`MorphismOfTopoi.inverseImageTerminalIso`), so there is only one morphism
`g⁻¹h_V ⟶ g⁻¹1` at all.

## Main results

* `MorphismOfTopoi.yonedaEquiv_symm_map_from_terminal` — the restriction to `V` of a global
  section of `g_*E`, read through Yoneda, is the terminal map `h_V ⟶ 1` followed by the global
  section.
* `MorphismOfTopoi.homEquiv_symm_yonedaEquiv_symm_map_from_terminal` — its transpose
  `g⁻¹h_V ⟶ E` is the terminal map `g⁻¹h_V ⟶ 1` followed by the global section of `E`.
* `MorphismOfTopoi.sectionsFunctor_map_yoneda_from_terminal` — the evaluated form: at any object
  `U` of `C` and any section `s` of `g⁻¹h_V` over `U`, the value is the restriction to `U` of the
  global section of `E`.
* `MorphismOfTopoi.sectionsEvalRingHom_inverseImageYonedaRingEquiv_symm_map_from_terminal` — the
  same for a sheaf of **rings** `R`, with the identification spelled as the ring isomorphism
  `MorphismOfTopoi.inverseImageYonedaRingEquiv` and the global section of `R` as the one supplied
  by `MorphismOfTopoi.pushforwardCommRingTerminalSectionsRingEquiv`.

## Implementation notes

The hypotheses `IsTerminal T` and `IsTerminal T'` are carried as arguments rather than as
instances, as for `MorphismOfTopoi.pushforwardCommRingTerminalSectionsRingEquiv`. The site of the
target is presented at the same universe as the sections, `Category.{w} D` with sheaves of
`Type w`, because Mathlib's `CategoryTheory.GrothendieckTopology.yoneda` of a subcanonical site
lands in `Sheaf K (Type w)` for `Category.{w} D`; the universes of the source site are
unconstrained.

This is the step that the closing paragraph of the proof of [Stacks Project, Tag 04I6] uses
without comment: the coefficients of the system of étale equations are global functions on the
target, and they have to be recognised as global functions on the source pushed along the ring
map on global sections, rather than as sections over the chart `V` alone.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

universe w v u u'

namespace MorphismOfTopoi

section Sets

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{w} D] {K : GrothendieckTopology D} [K.Subcanonical]
  (g : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  {T : C} {T' : D}

omit [K.Subcanonical] in
/-- There is exactly one morphism `g⁻¹F ⟶ g⁻¹1` for any sheaf `F` on the target site, because
`g⁻¹` carries the terminal sheaf to the terminal sheaf.  In particular `g⁻¹` of the terminal map
out of `F` is the terminal map followed by
`MorphismOfTopoi.inverseImageTerminalIso`. -/
theorem inverseImage_map_terminal_from (F : Sheaf K (Type w)) :
    g.inverseImage.map (terminal.from F) =
      terminal.from (g.inverseImage.obj F) ≫ (inverseImageTerminalIso g).inv :=
  (IsTerminal.ofIso terminalIsTerminal (inverseImageTerminalIso g).symm).hom_ext _ _

/-- **The restriction of a global section of `g_*E` factors through the terminal sheaf.**  Read
through the Yoneda bijection of the subcanonical target site, the restriction to `V` of a section
of `g_*E` over the terminal object `T'` is the terminal map `h_V ⟶ 1` followed by the morphism
`1 ⟶ g_*E` naming that section. -/
theorem yonedaEquiv_symm_map_from_terminal (hT' : IsTerminal T') (E : Sheaf J (Type w)) (V : D)
    (x : (g.pushforward.obj E).obj.obj (op T')) :
    K.yonedaEquiv.symm ((g.pushforward.obj E).obj.map (hT'.from V).op x) =
      terminal.from (K.yoneda.obj V) ≫ Sheaf.terminalObjHomEquiv hT' (g.pushforward.obj E) x := by
  apply K.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, K.yonedaEquiv_comp]
  exact (Sheaf.sectionsFunctor_map_terminalObjHomEquiv hT' x (op V)
    (K.yonedaEquiv (terminal.from (K.yoneda.obj V)))).symm

/-- **The transpose of the restriction of a global section is constant.**  The morphism
`g⁻¹h_V ⟶ E` which the adjunction attaches to the restriction to `V` of a global section `x` of
`g_*E` is the terminal map `g⁻¹h_V ⟶ 1` followed by the global section of `E` attached to `x` by
`MorphismOfTopoi.pushforwardTerminalSectionsEquiv`. -/
theorem homEquiv_symm_yonedaEquiv_symm_map_from_terminal (hT : IsTerminal T) (hT' : IsTerminal T')
    (E : Sheaf J (Type w)) (V : D) (x : (g.pushforward.obj E).obj.obj (op T')) :
    (g.adj.homEquiv (K.yoneda.obj V) E).symm
        (K.yonedaEquiv.symm ((g.pushforward.obj E).obj.map (hT'.from V).op x)) =
      terminal.from (g.inverseImage.obj (K.yoneda.obj V)) ≫
        Sheaf.terminalObjHomEquiv hT E (g.pushforwardTerminalSectionsEquiv hT hT' E x) := by
  rw [g.yonedaEquiv_symm_map_from_terminal hT' E V x, g.adj.homEquiv_naturality_left_symm,
    g.inverseImage_map_terminal_from (K.yoneda.obj V), Category.assoc,
    pushforwardTerminalSectionsEquiv_apply, Equiv.apply_symm_apply]
  rfl

/-- **A global section of `g_*E`, evaluated as a function on `g⁻¹h_V`.**  At an object `U` of the
source site and a section `s` of `g⁻¹h_V` over `U`, the function on `g⁻¹h_V` attached by the
adjunction and Yoneda to the restriction to `V` of a global section `x` of `g_*E` takes the value
`x` itself, restricted from the terminal object to `U`. -/
theorem sectionsFunctor_map_yoneda_from_terminal (hT : IsTerminal T) (hT' : IsTerminal T')
    (E : Sheaf J (Type w)) (V : D) (x : (g.pushforward.obj E).obj.obj (op T')) (U : Cᵒᵖ)
    (s : (sectionsFunctor J U).obj (g.inverseImage.obj (K.yoneda.obj V))) :
    (sectionsFunctor J U).map ((g.adj.homEquiv (K.yoneda.obj V) E).symm
        (K.yonedaEquiv.symm ((g.pushforward.obj E).obj.map (hT'.from V).op x))) s =
      E.obj.map (hT.from U.unop).op (g.pushforwardTerminalSectionsEquiv hT hT' E x) := by
  rw [g.homEquiv_symm_yonedaEquiv_symm_map_from_terminal hT hT' E V x,
    (sectionsFunctor J U).map_comp_apply]
  exact Sheaf.sectionsFunctor_map_terminalObjHomEquiv hT _ U _

end Sets

section Rings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{w} D] {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] [K.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.Subcanonical]
  (g : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  (R : Sheaf J RingCat.{w}) {T : C} {T' : D}

/-- The inverse of `MorphismOfTopoi.inverseImageYonedaRingEquiv` is the inverse of the Yoneda
bijection followed by the inverse of the adjunction bijection.  The ring isomorphism is built
from bijectivity rather than from an explicit inverse, so this has to be read off from
`MorphismOfTopoi.inverseImageYonedaRingHom_apply`. -/
theorem inverseImageYonedaRingEquiv_symm_apply (V : D)
    (z : (sectionsFunctor K (op V)).obj
      (ringSheaf (pullbackRingSheaf K g.pushforward R))) :
    (inverseImageYonedaRingEquiv g R V).symm z =
      (g.adj.homEquiv (K.yoneda.obj V) (ringSheaf R)).symm (K.yonedaEquiv.symm z) := by
  apply (inverseImageYonedaRingEquiv g R V).injective
  rw [RingEquiv.apply_symm_apply, inverseImageYonedaRingEquiv_apply,
    inverseImageYonedaRingHom_apply, Equiv.apply_symm_apply]
  exact (K.yonedaEquiv.apply_symm_apply z).symm

/-- **The coefficient identification of step (3) of Stacks 04I6.**  A global section `x` of
`g_*R`, restricted to an object `V` of the target site and read as a function on `g⁻¹h_V` by the
ring isomorphism `MorphismOfTopoi.inverseImageYonedaRingEquiv`, is the *constant* function whose
value is the global section of `R` attached to `x` by
`MorphismOfTopoi.pushforwardTerminalSectionsEquiv`: at every object `U` of the source site and
every section `s` of `g⁻¹h_V` over `U`, its value is that global section restricted to `U`.

This is what lets a coefficient of a system of equations over the target be recognised, after
transport, as a function pulled back from the source's own global functions, rather than only as
a section over the chart `V`. -/
theorem sectionsEvalRingHom_inverseImageYonedaRingEquiv_symm_map_from_terminal
    (hT : IsTerminal T) (hT' : IsTerminal T') (V : D)
    (x : (g.pushforward.obj (ringSheaf R)).obj.obj (op T')) (U : Cᵒᵖ)
    (s : (sectionsFunctor J U).obj (g.inverseImage.obj (K.yoneda.obj V))) :
    sectionsEvalRingHom U s ((inverseImageYonedaRingEquiv g R V).symm
        ((g.pushforward.obj (ringSheaf R)).obj.map (hT'.from V).op x)) =
      (ringSheaf R).obj.map (hT.from U.unop).op
        (g.pushforwardTerminalSectionsEquiv hT hT' (ringSheaf R) x) := by
  refine (sectionsEvalRingHom_apply U s _).trans
    (Eq.trans ?_ (g.sectionsFunctor_map_yoneda_from_terminal hT hT' (ringSheaf R) V x U s))
  exact congrArg (fun m => (sectionsFunctor J U).map m s)
    (inverseImageYonedaRingEquiv_symm_apply g R V _)

end Rings

end MorphismOfTopoi

end
