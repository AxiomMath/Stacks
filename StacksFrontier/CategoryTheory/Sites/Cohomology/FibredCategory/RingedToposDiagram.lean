module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAMorphism
import StacksCore.Tactic.StacksAttribute

/-! # The commutative triangle of ringed topoi of a morphism of fibred categories

Let `(D, O_D)` be a ringed site, let `p : C ⥤ D` and `p' : C' ⥤ D` be fibred categories over its
underlying site and let `u : C' ⥤ C` be a 1-morphism of fibred categories over `D`. Stacks 08PA
asserts that the morphisms of topoi `π`, `π'` and `g` of Stacks 06NW, together with the structure
sheaves `O_C = π⁻¹O_D` and `O_{C'} = (π')⁻¹O_D`, assemble into a commutative diagram of ringed
topoi. The imported `FibredCategory.RingedToposOfAMorphism` module states that
assertion as `Stacks.Sites.FibredCategory.MorphismSituation.RingedToposDiagram` and supplies a
witness for every one of its fields except the final commutativity equation. This file closes
that equation and constructs the diagram.

## Main results

* `Stacks.Sites.FibredCategory.MorphismSituation.commutes_triangle`: the 2-isomorphism of the
  triangle respects the structure maps, after forgetting the ring operations.
* `Stacks.Sites.FibredCategory.MorphismSituation.ringedToposDiagram`: the canonical commutative
  triangle of ringed topoi, i.e. a term of `RingedToposDiagram`.

## Implementation notes

The mathematical content of `commutes_triangle` is one line: the structure map of the composite
`(Sh(C'), O_{C'}) ⟶ (Sh(D), O_D)` is the adjunct of the composite of the two inverse-image
structure maps, the outer one is an identity and the inner one is the comparison of restrictions,
and the mate of that comparison is by definition the 2-isomorphism of the triangle. Every
ingredient is already proved in the file this one imports.

What makes it delicate is that the same objects have two spellings in play: the structure's
fields speak of `(S.toBase pi).toToposHom.comp gRinged.toToposHom`, `(S.sourceTopos pi').J` and
`S.baseTopos.forgetRing`, while the lemmas about them are stated at `S.pi.comp S.g`,
`S.sourceTopology` and `S.baseForget`. The two agree definitionally — each difference is one
projection of a structure built by a `def` — but checking that costs heartbeats, and doing it
more than once or twice inside a single declaration exceeds the default budget; the resulting
deterministic timeout reads as a transparency failure rather than as a heartbeat limit.

Since `maxHeartbeats` is per declaration, the proof is therefore split so that each piece crosses
between the two spellings at most once: `forgetRing_map_compFSharp_eq` restates the composite's
structure map at the *structure field's* spelling, `forget_map_compFSharpInverseImage_eq`
identifies its inverse-image form with the comparison of restrictions at the *lemma's* spelling,
and `unit_comp_mate_compFSharpInverseImage` is the one declaration that crosses, by rewriting
along the previous one and then applying
`MorphismSituation.unit_comp_mate_baseTopos` verbatim. Each is a term-mode `Eq.trans`/`congrArg`
chain: `rw` and `simp` cannot be used at all here, since after the first spelling is in place the
goal is no longer type-correct at the `implicit` transparency level that they unify at, and they
report "did not find an occurrence" on patterns that are visibly present.

Even split, `commutes_triangle`, which crosses between the spellings once more, needs a little
over 200000 heartbeats, so it carries a local heartbeat budget of 250000.

## References

* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u₀ u₁ u₂ v₀ v₁ v₂ w

namespace Stacks.Sites.FibredCategory.MorphismSituation

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})

/-- The inverse-image form of the structure map of the composite
`(Sh(C'), O_{C'}) ⟶ (Sh(C), O_C) ⟶ (Sh(D), O_D)`, after forgetting the ring operations, is the
comparison of the two restrictions: the inverse image along `g` of the structure map of `π` is an
identity, and the structure map of `g` is the identification `g⁻¹O_C ≅ O_{C'}`, which forgets to
that comparison. -/
theorem forget_map_compFSharpInverseImage_eq :
    S.sourceForget.map
        (AlgebraicGeometry.RingedToposHom.compFSharpInverseImage (S.toBase S.pi) S.gRinged) =
      S.restrictionComp :=
  (AlgebraicGeometry.RingedToposHom.forget_map_compFSharpInverseImage
      (S.toBase S.pi) S.gRinged).trans
    ((congrArg₂ (· ≫ ·) S.forget_map_inverseImage_toBase_fSharpInverseImage
      S.forget_map_gRinged_fSharpInverseImage).trans (Category.id_comp _))

/-- `AlgebraicGeometry.RingedToposHom.forget_map_compFSharp` at the two canonical morphisms to the
base, spelled as the `commutes` field of `RingedToposDiagram` spells it: the forgetful functor
through `S.baseTopos.forgetRing` and the composite through
`(S.toBase S.pi).toToposHom.comp S.gRinged.toToposHom`. -/
theorem forgetRing_map_compFSharp_eq :
    S.baseTopos.forgetRing.map
        (AlgebraicGeometry.RingedToposHom.compFSharp (S.toBase S.pi) S.gRinged) =
      ((S.toBase S.pi).toToposHom.comp S.gRinged.toToposHom).adj.unit.app
          (S.baseTopos.forgetRing.obj S.baseTopos.O) ≫
        ((S.toBase S.pi).toToposHom.comp S.gRinged.toToposHom).pushforward.map
          (S.sourceForget.map
            ((S.toBase S.pi).compFSharpInverseImage S.gRinged)) :=
  AlgebraicGeometry.RingedToposHom.forget_map_compFSharp (S.toBase S.pi) S.gRinged

/-- The canonical morphism from the source to the base, after forgetting the ring operations and
composing with the comparison of the direct image with the underlying direct image, is the unit of
`(π')⁻¹ ⊣ (π')_*`: the comparison is an identity, and the structure map is the unit of the
adjunction on sheaves of commutative rings. -/
theorem forgetRing_map_sourceToBase_fSharp_eq :
    S.baseTopos.forgetRing.map (S.sourceToBase S.pi').fSharp ≫
        (pushforwardCommRingForgetIso (S.sourceToBase S.pi').toToposHom).hom.app
          (S.sourceTopos S.pi').O =
      S.pi'.adj.unit.app (S.baseTopos.forgetRing.obj S.baseTopos.O) :=
  (Category.comp_id (S.baseTopos.forgetRing.map (S.sourceToBase S.pi').fSharp)).trans
    (forgetRing_map_commRingImageAdjunction_unit_app S.baseTopos S.pi'OverBaseTopos)

/-- `MorphismSituation.unit_comp_mate_baseTopos` with the comparison of the two restrictions
replaced by the inverse-image form of the structure map of the composite, and with the composite
spelled as the structure's fields spell it. This is the one declaration that crosses between the
two spellings of the composite morphism of topoi. -/
theorem unit_comp_mate_compFSharpInverseImage :
    (((S.toBase S.pi).toToposHom.comp S.gRinged.toToposHom).adj.unit.app
          (S.baseTopos.forgetRing.obj S.baseTopos.O) ≫
        ((S.toBase S.pi).toToposHom.comp S.gRinged.toToposHom).pushforward.map
          (S.sourceForget.map
            ((S.toBase S.pi).compFSharpInverseImage S.gRinged))) ≫
      (((S.pi.comp S.g).adj.ofNatIsoLeft S.inverseImageComparison).rightAdjointUniq
        S.pi'.adj).hom.app
          ((S.sourceTopos S.pi').forgetRing.obj (S.sourceTopos S.pi').O) =
      S.pi'.adj.unit.app (S.baseTopos.forgetRing.obj S.baseTopos.O) :=
  (congrArg (fun m ↦
      (((S.toBase S.pi).toToposHom.comp S.gRinged.toToposHom).adj.unit.app
            (S.baseTopos.forgetRing.obj S.baseTopos.O) ≫
          ((S.toBase S.pi).toToposHom.comp S.gRinged.toToposHom).pushforward.map m) ≫
        (((S.pi.comp S.g).adj.ofNatIsoLeft S.inverseImageComparison).rightAdjointUniq
          S.pi'.adj).hom.app
            ((S.sourceTopos S.pi').forgetRing.obj (S.sourceTopos S.pi').O))
    S.forget_map_compFSharpInverseImage_eq).trans S.unit_comp_mate_baseTopos

/-- The structure map of the composite, after forgetting the ring operations and following the
mate of the comparison of inverse images, is the unit of `(π')⁻¹ ⊣ (π')_*`. -/
theorem forgetRing_map_compFSharp_comp_mate :
    S.baseTopos.forgetRing.map
          (AlgebraicGeometry.RingedToposHom.compFSharp (S.toBase S.pi) S.gRinged) ≫
        (((S.pi.comp S.g).adj.ofNatIsoLeft S.inverseImageComparison).rightAdjointUniq
          S.pi'.adj).hom.app
            ((S.sourceTopos S.pi').forgetRing.obj (S.sourceTopos S.pi').O) =
      S.pi'.adj.unit.app (S.baseTopos.forgetRing.obj S.baseTopos.O) :=
  (eq_whisker S.forgetRing_map_compFSharp_eq _).trans S.unit_comp_mate_compFSharpInverseImage

/-- The same statement with the 2-isomorphism of the triangle in place of its mate: the two agree
by `MorphismSituation.commutativityIso_hom_app`, whose `eqToIso` factor is an identity. -/
theorem forgetRing_map_compFSharp_comp_commutativityIso :
    S.baseTopos.forgetRing.map
          (AlgebraicGeometry.RingedToposHom.compFSharp (S.toBase S.pi) S.gRinged) ≫
        S.commutativityIso.hom.app
          ((S.sourceTopos S.pi').forgetRing.obj (S.sourceTopos S.pi').O) =
      S.pi'.adj.unit.app (S.baseTopos.forgetRing.obj S.baseTopos.O) :=
  (whisker_eq _ (S.commutativityIso_hom_app
      ((S.sourceTopos S.pi').forgetRing.obj (S.sourceTopos S.pi').O))).trans
    S.forgetRing_map_compFSharp_comp_mate

set_option maxHeartbeats 250000 in
-- Assembling the chain re-checks the two spellings of the composite once more, which costs,
-- a little over 200000 heartbeats; see the implementation notes above.
/-- **Stacks 08PA**, the commutativity of the triangle: the 2-isomorphism `π_* ∘ g_* ≅ (π')_*`
carries the structure map of the composite `π ∘ g` to the structure map of `π'`, after forgetting
the ring operations. This is the `commutes` field of `RingedToposDiagram`. -/
theorem commutes_triangle :
    S.baseTopos.forgetRing.map
          (AlgebraicGeometry.RingedToposHom.compFSharp (S.toBase S.pi) S.gRinged) ≫
        (pushforwardCommRingForgetIso
            ((S.toBase S.pi).toToposHom.comp S.gRinged.toToposHom)).hom.app
            (S.sourceTopos S.pi').O ≫
          S.commutativityIso.hom.app
            ((S.sourceTopos S.pi').forgetRing.obj (S.sourceTopos S.pi').O) =
      S.baseTopos.forgetRing.map (S.sourceToBase S.pi').fSharp ≫
        (pushforwardCommRingForgetIso (S.sourceToBase S.pi').toToposHom).hom.app
          (S.sourceTopos S.pi').O :=
  ((whisker_eq _ (Category.id_comp (S.commutativityIso.hom.app
      ((S.sourceTopos S.pi').forgetRing.obj (S.sourceTopos S.pi').O)))).trans
    S.forgetRing_map_compFSharp_comp_commutativityIso).trans
    S.forgetRing_map_sourceToBase_fSharp_eq.symm

/-- **Stacks 08PA.** The canonical commutative triangle of ringed topoi associated to a
1-morphism of fibred categories over a ringed site: the three morphisms of topoi of Stacks 06NW,
each pinned by the identification of its inverse image with restriction and of its direct image
with the right Kan extension, the morphism of ringed topoi `g` whose inverse-image structure map
is the identification `g⁻¹O_C ≅ O_{C'}`, and the 2-isomorphism `π_* ∘ g_* ≅ (π')_*` exhibited as
the mate of the comparison of inverse images. -/
@[stacks 08PA "canonical commutative triangle of ringed topoi"]
noncomputable def ringedToposDiagram : S.RingedToposDiagram where
  pContinuous := S.pContinuous
  pCocontinuous := S.pCocontinuous
  p'Continuous := S.p'Continuous
  p'Cocontinuous := S.p'Cocontinuous
  uContinuous := S.uContinuous
  uCocontinuous := S.uCocontinuous
  pi := S.pi
  pi' := S.pi'
  g := S.g
  pi_inverseImage := rfl
  pi_pushforward := rfl
  pi'_inverseImage := rfl
  pi'_pushforward := rfl
  g_inverseImage := rfl
  g_pushforward := rfl
  gRinged := S.gRinged
  g_underlying := rfl
  gRinged_fSharpInverseImage_isIso :=
    S.gRinged_fSharpInverseImage ▸ S.structureComparison.isIso_hom
  inverseImageComparison := S.inverseImageComparison
  inverseImageComparison_canonical := rfl
  commutativityIso := S.commutativityIso
  commutativityIso_isMate := rfl
  commutes := S.commutes_triangle

namespace RingedToposDiagram

variable {S}

/-- **Stacks 08PA**, the identification `g⁻¹O_C ≅ O_{C'}` of a commutative triangle of ringed
topoi: its forward map is the inverse-image form of the structure map of `g`, which the triangle
records as an isomorphism. -/
noncomputable def structureSheafComparison (D : S.RingedToposDiagram) :
    (inverseImageCommRingFunctor D.gRinged.toToposHom).obj (S.totalTopos D.pi).O ≅
      (S.sourceTopos D.pi').O :=
  letI := D.gRinged_fSharpInverseImage_isIso
  asIso D.gRinged.fSharpInverseImage

/-- The forward map of the identification `g⁻¹O_C ≅ O_{C'}` is the inverse-image form of the
structure map of `g`. -/
@[simp] theorem structureSheafComparison_hom (D : S.RingedToposDiagram) :
    D.structureSheafComparison.hom = D.gRinged.fSharpInverseImage :=
  rfl

end RingedToposDiagram

end Stacks.Sites.FibredCategory.MorphismSituation

end
