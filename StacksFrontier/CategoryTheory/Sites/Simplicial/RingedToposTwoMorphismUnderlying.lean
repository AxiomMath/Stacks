module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModulesMap
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RingedToposMorphism

/-!
# The underlying sheaf of sets of the mate of a 2-morphism of morphisms of ringed topoi

Let `f, g : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be two morphisms of ringed topoi whose structure maps
are invertible, and let `t : f ⟶ g` be a 2-morphism in the sense of Stacks 04IC. There are then
two mates of `t`: the transformation `g^* ⟶ f^*` of pullbacks of sheaves of *modules*
(`AlgebraicGeometry.RingedToposHom.TwoMorphism.pullbackModulesMap`) and the transformation
`g⁻¹ ⟶ f⁻¹` of inverse images of sheaves of *sets*, the conjugate of `t` itself under the two
topos adjunctions. This file says that the first has the second underneath, conjugated by the
two identifications of the underlying sheaf of a pullback of modules with an inverse image.

That is the content missing from a cube: `isIso_mateEquiv_symm_of_reflectsIsomorphisms`
transports invertibility of a mate from the back face of a cube to its front face, which here
carries invertibility *from* sheaves of sets *to* sheaves of modules. The identity below carries
it the other way, because it is an identity and not an implication.

## Main results

* `AlgebraicGeometry.RingedToposHom.isIso_comp_fSharpInverseImage`: a composite of two morphisms
  of ringed topoi with invertible structure maps has an invertible structure map, so that the
  identity below applies at a composite.
* `AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app`:
  the unit of the adjunction of Stacks 03D7, read on underlying sheaves of sets, is the unit of
  the topos adjunction followed by the direct image of the comparison
  `AlgebraicGeometry.RingedToposHom.pullbackUnderlyingIsoOfIsIso`.
* `AlgebraicGeometry.RingedToposHom.TwoMorphism.moduleSheafFunctor_map_pullbackModulesMap_app`:
  **the identity itself.** On underlying sheaves of sets the transformation of pullbacks of
  modules is the conjugate of the 2-morphism.
* `AlgebraicGeometry.RingedToposHom.TwoMorphism.isIso_conjugateEquiv_symm_app`: the invertibility
  transfer it yields. If the transformation of pullbacks of modules is invertible at a module,
  the conjugate of the 2-morphism is invertible at the underlying sheaf of sets of that module.

## Implementation notes

Both mates are characterised by their transposes: a mate `γ` of `t` satisfies
`unit₂ ≫ R₂(γ) = unit₁ ≫ t`, which is Mathlib's `CategoryTheory.unit_conjugateEquiv_symm`. So
the identity is proved by transposing it along the topos adjunction of `g`, where the two sides
become the *same* composite read through the two levels: the unit of Stacks 03D7 has the unit of
the topos adjunction underneath by
`moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app`, the transformation of direct
images of modules *is* the 2-morphism by
`AlgebraicGeometry.RingedToposHom.TwoMorphism.moduleSheafFunctor_map_pushforwardModulesMap`, and
what is left over is the naturality of the 2-morphism at the comparison
`pullbackUnderlyingIsoOfIsIso`.

The unit statement is `CategoryTheory.unit_mateEquiv` at the identification
`AlgebraicGeometry.RingedToposHom.mateEquiv_pullbackUnderlyingIsoOfIsIso_inv` of that comparison
as a mate; the vertical comparison appearing there is
`AlgebraicGeometry.RingedToposHom.pushforwardModulesUnderlyingIso`, which is `Iso.refl`, so it
drops out.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Definition 18.2.2 (Tag 04IC)](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
  Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedToposHom

universe u

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The unit of Stacks 03D7 on underlying sheaves of sets.** For a morphism of ringed topoi
with invertible structure map, the unit `M ⟶ f_*f^*M` of the pullback–pushforward adjunction of
sheaves of modules has, on underlying sheaves of sets, the unit of the topos adjunction followed
by the direct image of the comparison
`AlgebraicGeometry.RingedToposHom.pullbackUnderlyingIsoOfIsIso`.

This is `CategoryTheory.unit_mateEquiv` at the identification of that comparison as a mate,
`AlgebraicGeometry.RingedToposHom.mateEquiv_pullbackUnderlyingIsoOfIsIso_inv`; the vertical
comparison of the square is `pushforwardModulesUnderlyingIso`, which is the identity. -/
theorem moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app
    (f : RingedToposHom X Y) [IsIso f.fSharpInverseImage]
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
        ((pullbackAdjPushforwardModules f).unit.app M) =
      f.toToposHom.adj.unit.app
          (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) M) ≫
        f.toToposHom.pushforward.map ((pullbackUnderlyingIsoOfIsIso f).inv.app M) := by
  have h := unit_mateEquiv (pullbackAdjPushforwardModules f) f.toToposHom.adj
    (TwoSquare.mk _ _ _ _ (pullbackUnderlyingIsoOfIsIso f).inv) M
  rw [mateEquiv_pullbackUnderlyingIsoOfIsIso_inv f] at h
  exact (Category.comp_id _).symm.trans h

section Comp

variable {Z : RingedTopos.{u, u, u}}
  [Z.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- **The structure map of a composite of morphisms of ringed topoi with invertible structure
maps is invertible.** On underlying sheaves of sets it is the inverse image along the inner
morphism of the outer structure map followed by the inner one
(`AlgebraicGeometry.RingedToposHom.comp_fSharpInverseImage_forget`), hence invertible; and
forgetting the ring operations reflects isomorphisms.

This is what makes the identity of this file available at a composite, where the 2-morphisms
coming from a simplicial situation live. -/
instance isIso_comp_fSharpInverseImage (g : RingedToposHom Y Z) (f : RingedToposHom X Y)
    [IsIso g.fSharpInverseImage] [IsIso f.fSharpInverseImage] :
    IsIso (g.comp f).fSharpInverseImage := by
  have : IsIso (X.forgetRing.map (g.comp f).fSharpInverseImage) := by
    rw [comp_fSharpInverseImage_forget]
    exact ((f.toToposHom.inverseImage.mapIso
          (Y.forgetRing.mapIso (asIso g.fSharpInverseImage))) ≪≫
      X.forgetRing.mapIso (asIso f.fSharpInverseImage)).isIso_hom
  exact isIso_of_reflects_iso _ X.forgetRing

end Comp

namespace TwoMorphism

variable {f g : RingedToposHom X Y} [IsIso f.fSharpInverseImage] [IsIso g.fSharpInverseImage]
  (t : TwoMorphism f g)
  (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))

/-- **The transformation of pullbacks of sheaves of modules induced by a 2-morphism has the
conjugate of the 2-morphism as its underlying morphism of sheaves of sets**, for two morphisms of
ringed topoi with invertible structure maps.

Both sides are mates, so the identity is checked after transposing along the topos adjunction of
`g`, where `CategoryTheory.unit_conjugateEquiv_symm` replaces each by the unit of the other
adjunction followed by the 2-morphism; the two levels are matched by
`AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app`
and by `moduleSheafFunctor_map_pushforwardModulesMap`, and the remaining discrepancy is the
naturality of the 2-morphism at the comparison `pullbackUnderlyingIsoOfIsIso`. -/
theorem moduleSheafFunctor_map_pullbackModulesMap_app :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map
        (t.pullbackModulesMap.app M) =
      (pullbackUnderlyingIsoOfIsIso g).hom.app M ≫
        ((conjugateEquiv f.toToposHom.adj g.toToposHom.adj).symm t.t).app
            (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) M) ≫
          (pullbackUnderlyingIsoOfIsIso f).inv.app M := by
  have hA : (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
          ((pullbackAdjPushforwardModules g).unit.app M) ≫
        g.toToposHom.pushforward.map
          ((Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map
            (t.pullbackModulesMap.app M)) =
      (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
          ((pullbackAdjPushforwardModules f).unit.app M) ≫
        (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
          (t.pushforwardModulesMap.app ((f.toModulesHom.pullbackModules).obj M)) := by
    have hu : (pullbackAdjPushforwardModules g).unit.app M ≫
          g.pushforwardModules.map (t.pullbackModulesMap.app M) =
        (pullbackAdjPushforwardModules f).unit.app M ≫
          t.pushforwardModulesMap.app ((f.toModulesHom.pullbackModules).obj M) :=
      (unit_conjugateEquiv_symm (pullbackAdjPushforwardModules f)
        (pullbackAdjPushforwardModules g) t.pushforwardModulesMap M).symm
    change (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
            ((pullbackAdjPushforwardModules g).unit.app M) ≫
          (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
            (g.pushforwardModules.map (t.pullbackModulesMap.app M)) = _
    rw [← (Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map_comp,
      ← (Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map_comp, hu]
  have key : (pullbackUnderlyingIsoOfIsIso g).inv.app M ≫
        (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map
          (t.pullbackModulesMap.app M) =
      ((conjugateEquiv f.toToposHom.adj g.toToposHom.adj).symm t.t).app
          (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) M) ≫
        (pullbackUnderlyingIsoOfIsIso f).inv.app M := by
    refine (g.toToposHom.adj.homEquiv
      (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) M)
      _).injective ?_
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
      ← Category.assoc, ← Category.assoc,
      ← moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app g M,
      ← unit_conjugateEquiv_symm f.toToposHom.adj g.toToposHom.adj t.t
        (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) M)]
    refine hA.trans ?_
    rw [moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app f M]
    exact (Category.assoc _ _ _).trans (congrArg
      (f.toToposHom.adj.unit.app
        (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) M) ≫ ·)
      (t.t.naturality ((pullbackUnderlyingIsoOfIsIso f).inv.app M)))
  rw [← key, Iso.hom_inv_id_app_assoc]

/-- **The invertibility transfer.** If the transformation of pullbacks of sheaves of modules
induced by a 2-morphism is invertible at a sheaf of modules, then the conjugate of the 2-morphism
is invertible at its underlying sheaf of sets.

This is the direction a cube of mates does not give: it comes from the identity
`moduleSheafFunctor_map_pullbackModulesMap_app` and the invertibility of the two comparisons
`AlgebraicGeometry.RingedToposHom.pullbackUnderlyingIsoOfIsIso`. -/
theorem isIso_conjugateEquiv_symm_app [IsIso (t.pullbackModulesMap.app M)] :
    IsIso (((conjugateEquiv f.toToposHom.adj g.toToposHom.adj).symm t.t).app
      (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) M)) := by
  have h := t.moduleSheafFunctor_map_pullbackModulesMap_app M
  have hiso : IsIso
      ((Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map
        (t.pullbackModulesMap.app M)) :=
    ((Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).mapIso
      (asIso (t.pullbackModulesMap.app M))).isIso_hom
  rw [h] at hiso
  have h1 : IsIso (((conjugateEquiv f.toToposHom.adj g.toToposHom.adj).symm t.t).app
        (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) M) ≫
      (pullbackUnderlyingIsoOfIsIso f).inv.app M) :=
    IsIso.of_isIso_comp_left ((pullbackUnderlyingIsoOfIsIso g).hom.app M) _
  exact IsIso.of_isIso_comp_right _ ((pullbackUnderlyingIsoOfIsIso f).inv.app M)

end TwoMorphism

end AlgebraicGeometry.RingedToposHom

end
