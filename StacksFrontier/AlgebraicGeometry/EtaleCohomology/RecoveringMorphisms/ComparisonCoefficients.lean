module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCoveringFpqc
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.InverseImageSolutions
public import StacksFrontier.CategoryTheory.Sites.Topos.PushforwardGlobalSectionsYoneda

/-!
# The coefficients of the comparison of step (3) of Stacks 04I6 come from the source

Let `(g, g^♯)` be a morphism of the small étale ringed topoi of two schemes `X` and `Y` of a big
étale site, let `V` be an étale chart of `Y` and let `U` be an étale chart of `X`.  A section `s`
of `g⁻¹h_V` over `U` determines, by
`AlgebraicGeometry.comparisonRingHom`, a ring homomorphism `Γ(V, ⊤) ⟶ Γ(U, ⊤)`, and the equations
of a standard presentation of `V` survive it
(`AlgebraicGeometry.isSolution_comparisonCoord`).  The *coefficients* of those equations live in
`Γ(Y, ⊤)` and reach `Γ(U, ⊤)` through the structure map `Γ(Y, ⊤) ⟶ Γ(V, ⊤)` of the chart followed
by that ring homomorphism.

This file identifies that composite:

`Γ(Y, ⊤) --φ--> Γ(X, ⊤) --restrict--> Γ(U, ⊤)`,

where `φ = AlgebraicGeometry.RingedToposHom.globalSectionsMap` is the ring map on global
functions of the source's first paragraph and the second map is restriction along the structure
morphism of the chart `U`.  In particular the coefficient map does not depend on `V`, `U`'s
section `s`, or the presentation: it is `φ`, restricted.  That is what lets the solution at
`(U, s)` be read as a point of the fibre product `X ×_Y V` over `U`, and so identifies the target
of the comparison with the representable sheaf `h_{X ×_Y V}`.

The content is
`MorphismOfTopoi.sectionsEvalRingHom_inverseImageYonedaRingEquiv_symm_map_from_terminal`, that a
global section of `g_*𝒪_X` transported to a function on `g⁻¹h_V` is constant; everything else is
naturality of `g^♯` on the small étale site of `Y`.

## Main results

* `AlgebraicGeometry.SmallEtale.commRingStructureSheaf_map_from_final` — the restriction map of
  the structure sheaf of the small étale site from the terminal chart `S / S` to a chart `U` is
  the ring map on global functions of the structure morphism of `U`.
* `AlgebraicGeometry.comparisonRingHom_appTop_schemeStructureHom` — **the coefficient
  identification**: the composite of the structure map of the chart `V` with
  `AlgebraicGeometry.comparisonRingHom` is
  `AlgebraicGeometry.RingedToposHom.globalSectionsMap` followed by restriction to `U`.
* `AlgebraicGeometry.comparisonRingHom_comp_appTop_schemeStructureHom` — the same, as an equality
  of ring homomorphisms.
* `AlgebraicGeometry.isSolution_comparisonCoord_globalSectionsMap` —
  `AlgebraicGeometry.isSolution_comparisonCoord` with its coefficient ring map replaced by the
  identified one.  This is the form in which step (3) of the proof of
  [Stacks Project, Tag 04I6] consumes the solution: the system is `P` with coefficients pushed
  along `φ`, which is the system presenting `X ×_Y V` over `X`.

## What this does not do

Nothing here carries a `@[stacks 04I6]` tag.  Two things still separate this from the comparison
`g⁻¹h_V ⟶ h_{X ×_Y V}` that the tag's proof constructs, and they are recorded in the "What is
missing" section of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/AffineCase.lean`:

* that the system `P` with coefficients pushed along `φ` *presents* the chart `X ×_Y V` of `X`,
  i.e. the base change of a standard presentation, `A ⊗_B B[x]/(P) = A[x]/(P^φ)`; and
* that the resulting comparison is an *isomorphism*, which is the stalk computation using
  Stacks 04GX.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback Stacks.EtaleCohomology AlgebraicGeometry.SmallEtale

universe u

namespace AlgebraicGeometry

/-! ### The restriction map from the terminal chart -/

section StructureSheaf

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The restriction map of the structure sheaf of the small étale site from the terminal chart
is the structure morphism of the chart, on global functions.**  The sections of the structure
sheaf over the terminal chart `S / S` are the global functions on `S`
(`Stacks.EtaleCohomology.smallEtaleRingedSite_structureSheaf_obj_final`), and the unique morphism
`U ⟶ S / S` of the site is the structure morphism of `U`
(`AlgebraicGeometry.SmallEtale.toScheme_map_from_final`). -/
theorem SmallEtale.commRingStructureSheaf_map_from_final (U : SmallEtale B S hS) :
    (SmallEtale.commRingStructureSheaf B S hS).obj.map
        ((SmallEtale.finalIsTerminal B S hS).from U).op =
      (schemeStructureHom B S hS U).appTop := by
  change Scheme.Γ.map ((SmallEtale.toScheme B S hS).map
    ((SmallEtale.finalIsTerminal B S hS).from U)).op = _
  rw [SmallEtale.toScheme_map_from_final]
  exact Scheme.Γ_map_op (schemeStructureHom B S hS U)

end StructureSheaf

/-! ### The coefficient identification -/

section Coefficients

variable (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (hY : B.Contains Y)
  (g : RingedToposHom
    (RingedSite.toRingedTopos (smallEtaleRingedSite B X hX))
    (RingedSite.toRingedTopos (smallEtaleRingedSite B Y hY)))
  (V : SmallEtale B Y hY) (U : (SmallEtale B X hX)ᵒᵖ)
  (s : (sectionsFunctor (SmallEtale.topology B X hX) U).obj
    (g.toToposHom.inverseImage.obj ((SmallEtale.topology B Y hY).yoneda.obj V)))

/-- **The coefficients of the comparison come from the global functions on `X`.**  A global
function `t` on `Y`, restricted to the chart `V` and pushed through
`AlgebraicGeometry.comparisonRingHom` at a chart `U` of `X` and a section `s` of `g⁻¹h_V` over
`U`, is the image of `t` under the ring map on global functions
`AlgebraicGeometry.RingedToposHom.globalSectionsMap` of `(g, g^♯)`, restricted to `U`.

So the coefficient map of `AlgebraicGeometry.isSolution_comparisonCoord` is independent of `V`,
of `s` and of the presentation: it is the source's `φ : B ⟶ A`, restricted. -/
theorem comparisonRingHom_appTop_schemeStructureHom (t : Γ(Y, ⊤)) :
    comparisonRingHom B hX hY g V U s ((schemeStructureHom B Y hY V).appTop.hom t) =
      (schemeStructureHom B X hX U.unop).appTop.hom
        ((g.globalSectionsMap (SmallEtale.finalIsTerminal B X hX)
          (SmallEtale.finalIsTerminal B Y hY)).hom t) := by
  have hnat := NatTrans.naturality_apply g.fSharp.hom
    ((SmallEtale.finalIsTerminal B Y hY).from V).op t
  have hkey :=
    MorphismOfTopoi.sectionsEvalRingHom_inverseImageYonedaRingEquiv_symm_map_from_terminal
      g.toToposHom (smallEtaleRingSheaf B hX) (SmallEtale.finalIsTerminal B X hX)
      (SmallEtale.finalIsTerminal B Y hY) V
      ((g.fSharp.hom.app (op (SmallEtale.final B Y hY))).hom t) U s
  rw [← SmallEtale.commRingStructureSheaf_map_from_final B X hX U.unop,
    ← SmallEtale.commRingStructureSheaf_map_from_final B Y hY V]
  exact (congrArg (fun c => sectionsEvalRingHom U s
    ((inverseImageHomRingEquiv B hX hY g V).symm c)) hnat).trans hkey

/-- **The coefficient identification of step (3) of Stacks 04I6**, as an equality of ring
homomorphisms `Γ(Y, ⊤) →+* Γ(U, ⊤)`. -/
theorem comparisonRingHom_comp_appTop_schemeStructureHom :
    (comparisonRingHom B hX hY g V U s).comp (schemeStructureHom B Y hY V).appTop.hom =
      (schemeStructureHom B X hX U.unop).appTop.hom.comp
        (g.globalSectionsMap (SmallEtale.finalIsTerminal B X hX)
          (SmallEtale.finalIsTerminal B Y hY)).hom :=
  RingHom.ext (comparisonRingHom_appTop_schemeStructureHom B hX hY g V U s)

/-- **The equations of the presentation, with the coefficients identified.**  At every étale
chart `U` of `X` and every section `s` of `g⁻¹h_V` over `U`, the `n` coordinates of the
comparison form a solution of the system `P` over `Γ(U, ⊤)` whose coefficient ring map is the
ring map on global functions of `(g, g^♯)` followed by restriction to `U`.

This is `AlgebraicGeometry.isSolution_comparisonCoord` with the coefficient map replaced by the
one of `AlgebraicGeometry.comparisonRingHom_comp_appTop_schemeStructureHom`, and it is the shape
step (3) of the proof of [Stacks Project, Tag 04I6] needs: the system is the base change of `P`
along `φ`, which is the system presenting the chart `X ×_Y V` of `X`. -/
theorem isSolution_comparisonCoord_globalSectionsMap [IsAffine Y] {n : ℕ}
    {P : Fin n → MvPolynomial (Fin n) Γ(Y, ⊤)}
    [IsAffine ((SmallEtale.toScheme B Y hY).obj V)]
    (pres : StandardPresentationOver ((SmallEtale.toScheme B Y hY).obj V)
      (schemeStructureHom B Y hY V) P) :
    MvPolynomial.IsSolution P
      ((schemeStructureHom B X hX U.unop).appTop.hom.comp
        (g.globalSectionsMap (SmallEtale.finalIsTerminal B X hX)
          (SmallEtale.finalIsTerminal B Y hY)).hom)
      (fun i => (sectionsFunctor (SmallEtale.topology B X hX) U).map
        (comparisonCoord B hX hY g V pres i) s) :=
  comparisonRingHom_comp_appTop_schemeStructureHom B hX hY g V U s ▸
    isSolution_comparisonCoord B hX hY g V pres U s

end Coefficients

end AlgebraicGeometry

end
