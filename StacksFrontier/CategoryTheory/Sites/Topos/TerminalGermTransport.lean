module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingTerminalSections
public import StacksFrontier.CategoryTheory.Sites.Point.TerminalFiber

/-!
# Germs of global sections across an isomorphism of stalk functors

Let `g : Sh(C) ⟶ Sh(D)` be a morphism of topoi, `Φ` a point of the site presenting the source,
`Ψ` a point of the site presenting the target, and

`e : Ψ^{-1} ≅ g^{-1} ⋙ Φ^{-1}`

an isomorphism of stalk functors on sheaves of sets — the datum which [Stacks Project, Tag 00YA]
(2) produces for a morphism coming from a morphism of sites, and which
`Stacks.Sheaves.StalkInverseImage.stalkRingEquiv` takes as a hypothesis in order to avoid any
smallness condition on either site.

Such an `e` is *arbitrary*: nothing describes it on germs.  This file proves the one thing that
can nevertheless be computed, and it is the thing a comparison of coefficients needs — what `e`
does to the germ of a **global** section.  The answer is that it does the only possible thing: the
germ of a global section `b` of `F`, transported by `e` and pushed along the adjunct of a morphism
`m : F ⟶ g_*E`, is the germ of the global section of `E` that `m` and `b` determine.

The mechanism is naturality, and it works for every `e` because naturality does.  A global section
of `F` is a morphism `⊤ ⟶ F` of sheaves, so its germ is the image of the germ of the unique
section of the terminal sheaf; naturality of `e` at that morphism moves the problem to the
terminal sheaf, where the value of `e` is determined by nothing more than the fibre of a terminal
sheaf being a singleton
(`CategoryTheory.GrothendieckTopology.Point.eq_of_isTerminal`).

## Main results

* `MorphismOfTopoi.germ_globalSections_of_sheafFiberIso` — the computation just described.

## References

* [Stacks Project, Tag 00YA](https://stacks.math.columbia.edu/tag/00YA)
* [Stacks Project, Tag 00Y5](https://stacks.math.columbia.edu/tag/00Y5)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe w v u v' u'

namespace MorphismOfTopoi

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{w} C]
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D} [LocallySmall.{w} D]
  (g : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  (Φ : J.Point.{w}) (Ψ : K.Point.{w})
  (e : Ψ.sheafFiber (A := Type w) ≅ g.inverseImage ⋙ Φ.sheafFiber (A := Type w))
  {T : C} {T' : D}

omit [LocallySmall.{w} D] in
/-- **The germ of a global section is transported by an arbitrary isomorphism of stalk
functors to the germ of its image on global sections.**

Let `g : Sh(C) ⟶ Sh(D)` be a morphism of topoi presented by sites whose underlying categories
have terminal objects `T` and `T'`, let `Φ` and `Ψ` be points of the two sites, and let `e` be an
isomorphism identifying the stalk functor at `Ψ` with `g⁻¹` followed by the stalk functor at `Φ`.
Let `m : F ⟶ g_*E` be a morphism of sheaves of sets on the target site and `b` a global section
of `F`.  Then the germ of `b` at `Ψ`, transported by `e` and pushed along the adjunct
`g⁻¹F ⟶ E` of `m`, is the germ at `Φ` of the global section of `E` which `m` and `b` determine
through `MorphismOfTopoi.pushforwardTerminalSectionsEquiv`.

**No description of `e` on germs is used, and none is available.**  That is the point of the
statement: `e` is an arbitrary isomorphism of functors, so the only handle on it is naturality.
A global section of `F` is a morphism `⊤ ⟶ F` of sheaves
(`CategoryTheory.Sheaf.terminalObjHomEquiv`) and its germ is therefore the image of the germ of
the unique section of `⊤`; naturality of `e` at that morphism moves `e` to the terminal sheaf,
where its value is pinned down not by any formula but by
`CategoryTheory.GrothendieckTopology.Point.eq_of_isTerminal` — the fibre of a terminal sheaf is a
singleton, and `g⁻¹` carries the terminal sheaf to the terminal sheaf
(`MorphismOfTopoi.inverseImageTerminalIso`).  What is left is the terminal-object calculus of the
adjunction, which is `MorphismOfTopoi.pushforwardTerminalHomEquiv`.

This is the coefficient compatibility which step (3) of [Stacks Project, Tag 04I6] needs: taken
with `m` the structure map `g^♯` of a morphism of ringed topoi and `E`, `F` the underlying sheaves
of sets of the two structure sheaves, the right-hand side is
`AlgebraicGeometry.RingedToposHom.globalSectionsMap`. -/
theorem germ_globalSections_of_sheafFiberIso (hT : IsTerminal T) (hT' : IsTerminal T')
    {F : Sheaf K (Type w)} {E : Sheaf J (Type w)} (m : F ⟶ g.pushforward.obj E)
    (u : Ψ.fiber.obj T') (v : Φ.fiber.obj T) (b : F.obj.obj (op T')) :
    Φ.sheafFiber.map ((g.adj.homEquiv F E).symm m)
        (e.hom.app F (Ψ.toPresheafFiber T' u F.obj b)) =
      Φ.toPresheafFiber T v E.obj
        (g.pushforwardTerminalSectionsEquiv hT hT' E (m.hom.app (op T') b)) := by
  -- the germ of `b` is the image of the germ of the unique section of the terminal sheaf
  have hb : Ψ.toPresheafFiber T' u F.obj b =
      Ψ.sheafFiber.map (terminalObjHomEquiv hT' F b)
        (Ψ.toPresheafFiber T' u (⊤_ (Sheaf K (Type w))).obj
          (terminalSheafSection K (op T'))) := by
    refine Eq.symm ?_
    refine (Ψ.toPresheafFiber_naturality_apply (terminalObjHomEquiv hT' F b).hom T' u
      (terminalSheafSection K (op T'))).trans ?_
    exact congrArg (Ψ.toPresheafFiber T' u F.obj) ((terminalObjHomEquiv hT' F).left_inv b)
  have hnat := NatTrans.naturality_apply e.hom (terminalObjHomEquiv hT' F b)
    (Ψ.toPresheafFiber T' u (⊤_ (Sheaf K (Type w))).obj (terminalSheafSection K (op T')))
  have hterm : IsTerminal (g.inverseImage.obj (⊤_ (Sheaf K (Type w)))) :=
    IsTerminal.ofIso terminalIsTerminal (inverseImageTerminalIso g).symm
  have hq : e.hom.app (⊤_ (Sheaf K (Type w)))
        (Ψ.toPresheafFiber T' u (⊤_ (Sheaf K (Type w))).obj (terminalSheafSection K (op T'))) =
      Φ.sheafFiber.map (inverseImageTerminalIso g).inv
        (Φ.toPresheafFiber T v (⊤_ (Sheaf J (Type w))).obj (terminalSheafSection J (op T))) :=
    Φ.eq_of_isTerminal hterm _ _
  have hcomp : (inverseImageTerminalIso g).inv ≫
        g.inverseImage.map (terminalObjHomEquiv hT' F b) ≫ (g.adj.homEquiv F E).symm m =
      g.pushforwardTerminalHomEquiv E (terminalObjHomEquiv hT' F b ≫ m) := by
    change _ = (inverseImageTerminalIso g).inv ≫
      (g.adj.homEquiv (⊤_ (Sheaf K (Type w))) E).symm (terminalObjHomEquiv hT' F b ≫ m)
    rw [g.adj.homEquiv_naturality_left_symm]
  have hmc := (Φ.sheafFiber (A := Type w)).map_comp_apply (inverseImageTerminalIso g).inv
    (g.inverseImage.map (terminalObjHomEquiv hT' F b) ≫ (g.adj.homEquiv F E).symm m)
    (Φ.toPresheafFiber T v (⊤_ (Sheaf J (Type w))).obj (terminalSheafSection J (op T)))
  rw [hb, hnat, hq, Functor.comp_map, ← Functor.map_comp_apply, ← hmc, hcomp]
  refine (Φ.toPresheafFiber_naturality_apply
    (g.pushforwardTerminalHomEquiv E (terminalObjHomEquiv hT' F b ≫ m)).hom T v
    (terminalSheafSection J (op T))).trans ?_
  refine congrArg (Φ.toPresheafFiber T v E.obj) ?_
  rw [g.pushforwardTerminalSectionsEquiv_apply hT hT' E,
    terminalObjHomEquiv_comp hT' b m]
  rfl

end MorphismOfTopoi

end
