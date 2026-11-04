module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ComplexSystemGlueing

/-!
# The glued object of a system of complexes, read over an open containing the cover

`Stacks.DerivedGlueing.exists_glueing_of_complexSystem` assembles a system of complexes
`F : E ⥤ CochainComplex (Mod 𝒪_X) ℤ`, supported stagewise on an increasing family of opens
`W : E → Opens X`, into an object of the derived category **on `⊤`** whose restrictions are the
prescribed objects.  This file carries the same assembly over an arbitrary open `V` containing
every `W α`.

That relativization is not a convenience.  The limit stages of the transfinite recursion of
[Stacks, Tag 0D6B] compare the colimit of the stages *strictly below* `α` with the prescribed
object `K α`, and they do it over `W α`, which is in general neither `⊤` nor a member of the
collection of Situation 0D67; so the comparison the recursion needs is a solution of the glueing
problem over `W α` for the system indexed by `{β | β < α}`, which is exactly what is proved
here with `V = W α`.

## What replaces `⊤`

Nothing in the assembly uses that the big open is `⊤` except one step: `⊤` is the one open for
which extension by zero undoes restriction on *every* complex of `𝒪_X`-modules, which is
`Stacks.DerivedGlueing.topRoundTripIso`.  Over a general `V` that round trip holds only for a
complex supported on `V`, so it becomes a hypothesis, `sIso`, asserting precisely that the
colimit of the system is supported on `V`:

```
sIso : (j_V)_! (j_V)^* (colim F) ≅ colim F
```

Everything else goes through verbatim, with `V` in place of `⊤` — the counit identity
`Stacks.DerivedGlueing.openModuleRestriction_counit_key` that is the whole mathematical content
of the compatibility is stated at an arbitrary pair of opens already, and so is the coherence
`Stacks.DerivedGlueing.LocallyGiven.restrictionCompFactors'` through which the comparison of the
system is replaced by that counit.  Taking `V = ⊤` and `sIso = (topRoundTripIso X).app (colim F)`
recovers the statements of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ComplexSystemGlueing` on the nose:
`Stacks.DerivedGlueing.glueingComplexOver_top` records that the two glued complexes are the same
complex.

The transitions the system determines are untouched: `Stacks.DerivedGlueing.glueingTransitionIso`
and `Stacks.DerivedGlueing.glueingComplexLocalIso` never mention the big open, so the identical
family of transitions serves over every `V`.

## Main definitions

* `Stacks.DerivedGlueing.glueingComplexOver`, `glueingObjectOver`: the colimit of the system read
  on `V`, and its class in the derived category on `V`.
* `Stacks.DerivedGlueing.glueingRestrictionIsoOver`: the identification `σ_α` of the restriction
  from `V` to `W α` of the glued object with the prescribed object there.

## Main results

* `Stacks.DerivedGlueing.glueing_compatibility_over`: **the identifications `σ_α` of the
  restrictions of the glued object over `V` are compatible with the transitions the system
  determines**, unconditionally.
* `Stacks.DerivedGlueing.exists_glueing_of_complexSystem_over`: **the glueing problem is solved
  over `V` by a system of complexes supported inside `V`.**  This is
  `Stacks.DerivedGlueing.exists_glueing_of_complexSystem` with `⊤` replaced by `V`.

## Use in Tag 0D6B

At a stage `α` of the transfinite recursion of [Stacks, Tag 0D6B] the stages strictly below `α`
form a system of complexes supported inside `⨆_{β < α} W β`, and the assembly over that open
compares the colimit of the earlier stages with the prescribed object at `α`; see
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.WellOrderedCoverRecursion`.

Nothing here is tagged: all of it is a step of the source's *proof* of [Stacks, Tag 0D6B], not a
clause of its statement.

## References

* [Stacks Project, Tag 0D6B](https://stacks.math.columbia.edu/tag/0D6B)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open ExtensionByZeroModules

namespace Stacks.DerivedGlueing

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} {E : Type u} [LinearOrder E] [Nonempty E]

/-! ### The glued complex over an open containing the cover -/

/-- **The glued complex of a system of complexes, read on an open `V`**: the colimit of the
system, restricted to `V`.  At `V = ⊤` it is `Stacks.DerivedGlueing.glueingComplex`. -/
def glueingComplexOver (V : Opens X.carrier)
    (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ) :
    CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X V)) ℤ :=
  ((jStar V (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj (colimit F)

/-- **The glued object of the derived category on `V`** of a system of complexes. -/
def glueingObjectOver (V : Opens X.carrier)
    (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ) :
    OpenDerivedCategory X V :=
  DerivedCategory.Q.obj (glueingComplexOver V F)

omit [Nonempty E] in
/-- At `V = ⊤` the glued complex over `V` is the glued complex of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ComplexSystemGlueing`. -/
theorem glueingComplexOver_top
    (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ) :
    glueingComplexOver (⊤ : Opens X.carrier) F = glueingComplex F :=
  rfl

section Over

variable (V : Opens X.carrier)
  (W : E → Opens X.carrier)
  (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ)
  (I : ∀ α : E, CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X (W α))) ℤ)
  (hsupp : ∀ α : E, F.obj α ≅
    ((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (I α))
  (sIso : ((jShriek V (underlyingRingSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (glueingComplexOver V F) ≅ colimit F)

/-- **The restriction to `A ≤ V` of the glued complex over `V` is the restriction to `A` of the
colimit of the system.** These are the first two legs of
`Stacks.DerivedGlueing.glueingComplexRestrictionIsoOver`, and unlike the third they are
isomorphisms already on complexes.  The second leg is the support hypothesis `sIso`; at `V = ⊤`
it is `Stacks.DerivedGlueing.glueingComplexRestrictIso`. -/
def glueingComplexRestrictIsoOver (A : Opens X.carrier) (hAV : A ≤ V) :
    ((openModuleRestriction X A V hAV).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (glueingComplexOver V F) ≅
      ((jStar A (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (colimit F) :=
  (openModuleRestrictionMapIso X A V hAV).app (glueingComplexOver V F) ≪≫
    ((jStar A (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso sIso

omit [Nonempty E] in
/-- The degreewise components of `Stacks.DerivedGlueing.glueingComplexRestrictIsoOver`. -/
theorem glueingComplexRestrictIsoOver_hom_f (A : Opens X.carrier) (hAV : A ≤ V) (n : ℤ) :
    (glueingComplexRestrictIsoOver V F sIso A hAV).hom.f n =
      (jStar A (underlyingRingSheaf X)).map (sIso.hom.f n) :=
  rfl

omit [Nonempty E] in
/-- The degreewise components of the inverse of
`Stacks.DerivedGlueing.glueingComplexRestrictIsoOver`. -/
theorem glueingComplexRestrictIsoOver_inv_f (A : Opens X.carrier) (hAV : A ≤ V) (n : ℤ) :
    (glueingComplexRestrictIsoOver V F sIso A hAV).inv.f n =
      (jStar A (underlyingRingSheaf X)).map (sIso.inv.f n) :=
  rfl

variable (hqi : ∀ (β α : E) (h : β ≤ α),
    QuasiIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (F.map h.hom)))
  (hWV : ∀ α : E, W α ≤ V)

/-- **The restriction from `V` to `W α` of the glued object is the prescribed object there**, on
complexes.  This is `Stacks.DerivedGlueing.glueingComplexRestrictionIso` with `⊤` replaced by
`V`: the colimit inclusion at `α`, restricted to `W α`, is a quasi-isomorphism
(`Stacks.DerivedGlueing.quasiIso_jStar_map_colimit_ι`, which says nothing about the big open),
and the two outer legs are the support of the colimit in `V` and the support of the stage in
`W α`. -/
def glueingComplexRestrictionIsoOver (α : E) :
    DerivedCategory.Q.obj
        (((openModuleRestriction X (W α) V (hWV α)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (glueingComplexOver V F)) ≅
      DerivedCategory.Q.obj (I α) :=
  letI : IsIso (DerivedCategory.Q.map
      (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (colimit.ι F α))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_jStar_map_colimit_ι W F hqi α)
  DerivedCategory.Q.mapIso (glueingComplexRestrictIsoOver V F sIso (W α) (hWV α)) ≪≫
    (asIso (DerivedCategory.Q.map
      (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (colimit.ι F α)))).symm ≪≫
    DerivedCategory.Q.mapIso (glueingComplexLocalIso W F I hsupp α)

/-- **The restriction from `V` to `W α` of the glued object, in the system `S`, is the prescribed
object there.** -/
def glueingRestrictionIsoOver (S : LocallyGiven X) (α : E) :
    (S.restriction (W α) V (hWV α)).obj (glueingObjectOver V F) ≅
      DerivedCategory.Q.obj (I α) :=
  (S.restrictionFactors (W α) V (hWV α)).app (glueingComplexOver V F) ≪≫
    glueingComplexRestrictionIsoOver V W F I hsupp sIso hqi hWV α

/-- **The identification over `V`, with the inverse of the colimit inclusion cleared.** This is
`Stacks.DerivedGlueing.glueingComplexRestrictionIsoOver` written through forward maps only. -/
theorem Q_map_colimit_ι_comp_glueingComplexRestrictionIsoOver (α : E) :
    DerivedCategory.Q.map
          (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (colimit.ι F α)) ≫
        DerivedCategory.Q.map (glueingComplexRestrictIsoOver V F sIso (W α) (hWV α)).inv ≫
        (glueingComplexRestrictionIsoOver V W F I hsupp sIso hqi hWV α).hom =
      DerivedCategory.Q.map (glueingComplexLocalIso W F I hsupp α).hom := by
  simp [glueingComplexRestrictionIsoOver]

/-! ### The compatibility of the glued identifications over `V` -/

omit [Nonempty E] in
/-- **The compatibility of the glued complex over `V` with the transitions, on complexes.** This
is `Stacks.DerivedGlueing.glueingComplexCompatibility` with `⊤` replaced by `V`; degreewise it is
the same counit identity `Stacks.DerivedGlueing.openModuleRestriction_counit_key`, which is
stated at an arbitrary pair of opens, with the round trip along `⊤` replaced by the support
hypothesis `sIso`. -/
theorem glueingComplexCompatibilityOver {β α : E} (hβα : W β ≤ W α) :
    ((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (glueingComplexLocalIso W F I hsupp α).hom ≫
        (glueingComplexTransitionSourceIso W F I hsupp hβα).hom ≫
        ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (colimit.ι F α) =
      ((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (colimit.ι F α)) ≫
        ((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (glueingComplexRestrictIsoOver V F sIso (W α) (hWV α)).inv ≫
        (NatTrans.mapHomologicalComplex
            (openModuleRestrictionComparison X (W β) (W α) V hβα (hWV α))
            (ComplexShape.up ℤ)).app (glueingComplexOver V F) ≫
        (glueingComplexRestrictIsoOver V F sIso (W β) (hWV β)).hom := by
  have : Nonempty E := ⟨α⟩
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  have huv : (hsupp α).hom.f n ≫ (hsupp α).inv.f n = 𝟙 _ :=
    HomologicalComplex.congr_hom (hsupp α).hom_inv_id n
  have hst : sIso.inv.f n ≫ sIso.hom.f n = 𝟙 _ :=
    HomologicalComplex.congr_hom sIso.inv_hom_id n
  have he : ((jShriekJStarIso X (W α)).inv.app (I α)).f n ≫
      (jShriekAdjunction (W α) (underlyingRingSheaf X)).unit.app ((I α).X n) = 𝟙 _ := by
    rw [← jShriekJStarIso_hom_app_f]
    exact HomologicalComplex.congr_hom ((jShriekJStarIso X (W α)).inv_hom_id_app (I α)) n
  have key := openModuleRestriction_counit_key X (W β) (W α) hβα
    ((hsupp α).hom.f n) ((hsupp α).inv.f n) (((jShriekJStarIso X (W α)).inv.app (I α)).f n)
    ((colimit.ι F α).f n) (sIso.inv.f n) (sIso.hom.f n) huv hst he
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    glueingComplexLocalIso_hom_f, glueingComplexTransitionSourceIso_hom_f,
    glueingComplexRestrictIsoOver_hom_f, glueingComplexRestrictIsoOver_inv_f,
    mapHomologicalComplex_openModuleRestrictionComparison_app_f,
    CategoryTheory.Functor.map_comp, Category.assoc]
  exact key

omit [Nonempty E] in
/-- `Stacks.DerivedGlueing.glueingComplexCompatibilityOver` rearranged through forward maps: the
two identifications cancel and the cocone law `F.map h ≫ colimit.ι F α = colimit.ι F β` is what
is left. -/
theorem glueingComplexCompatibilityOver' {β α : E} (hβα : W β ≤ W α) (h : β ≤ α) :
    ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (F.map h.hom) ≫
        (glueingComplexTransitionSourceIso W F I hsupp hβα).inv ≫
        ((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (glueingComplexLocalIso W F I hsupp α).inv ≫
        ((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (colimit.ι F α)) ≫
        ((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (glueingComplexRestrictIsoOver V F sIso (W α) (hWV α)).inv ≫
        (NatTrans.mapHomologicalComplex
            (openModuleRestrictionComparison X (W β) (W α) V hβα (hWV α))
            (ComplexShape.up ℤ)).app (glueingComplexOver V F) ≫
        (glueingComplexRestrictIsoOver V F sIso (W β) (hWV β)).hom =
      ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (colimit.ι F β) := by
  have hw : ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom) ≫
      ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (colimit.ι F α) =
      ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (colimit.ι F β) := by
    rw [← CategoryTheory.Functor.map_comp, colimit.w]
  rw [← glueingComplexCompatibilityOver V W F I hsupp sIso hWV hβα,
    ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id_assoc]
  exact hw

omit [Nonempty E] in
/-- `Stacks.DerivedGlueing.glueingComplexCompatibilityOver'` with the comparison of the
restriction of the glued complex moved to the right-hand side. -/
theorem glueingComplexCompatibilityOver'' {β α : E} (hβα : W β ≤ W α) (h : β ≤ α) :
    ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (F.map h.hom) ≫
        (glueingComplexTransitionSourceIso W F I hsupp hβα).inv ≫
        ((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (glueingComplexLocalIso W F I hsupp α).inv ≫
        ((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (colimit.ι F α)) ≫
        ((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (glueingComplexRestrictIsoOver V F sIso (W α) (hWV α)).inv ≫
        (NatTrans.mapHomologicalComplex
            (openModuleRestrictionComparison X (W β) (W α) V hβα (hWV α))
            (ComplexShape.up ℤ)).app (glueingComplexOver V F) =
      ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (colimit.ι F β) ≫
        (glueingComplexRestrictIsoOver V F sIso (W β) (hWV β)).inv := by
  rw [Iso.eq_comp_inv]
  simp only [Category.assoc]
  exact glueingComplexCompatibilityOver' V W F I hsupp sIso hWV hβα h

/-- **The transported identification over `V`, composed with the transition, is the comparison
followed by the identification one stage down.** This is
`Stacks.DerivedGlueing.transportHom_glueingComplexRestrictionIso_comp` with `⊤` replaced by
`V`. -/
theorem transportHom_glueingComplexRestrictionIsoOver_comp (S : LocallyGiven X)
    {β α : E} (hβα : W β ≤ W α) (h : β ≤ α) :
    transportHom DerivedCategory.Q DerivedCategory.Q (S.restrictionFactors (W β) (W α) hβα)
          (glueingComplexRestrictionIsoOver V W F I hsupp sIso hqi hWV α).hom ≫
        (glueingComplexTransitionIso W F I hsupp hqi hβα h).hom =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (openModuleRestrictionComparison X (W β) (W α) V hβα (hWV α))
            (ComplexShape.up ℤ)).app (glueingComplexOver V F)) ≫
        (glueingComplexRestrictionIsoOver V W F I hsupp sIso hqi hWV β).hom := by
  have := quasiIso_jStar_map_colimit_ι W F hqi α
  have := hqi β α h
  have hQrν : IsIso (DerivedCategory.Q.map
      (((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (colimit.ι F α)))) := by
    rw [← transportHom_map DerivedCategory.Q DerivedCategory.Q
      (S.restrictionFactors (W β) (W α) hβα)]
    infer_instance
  have hCA := Q_map_colimit_ι_comp_glueingComplexRestrictionIsoOver V W F I hsupp sIso hqi hWV α
  have hCB := Q_map_colimit_ι_comp_glueingComplexRestrictionIsoOver V W F I hsupp sIso hqi hWV β
  have hCT := Q_map_comp_glueingComplexTransitionIso W F I hsupp hqi hβα h
  have hCA' := congrArg (transportHom DerivedCategory.Q DerivedCategory.Q
    (S.restrictionFactors (W β) (W α) hβα)) hCA
  simp only [transportHom_comp, transportHom_map] at hCA'
  refine (cancel_epi (DerivedCategory.Q.map
      (((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (colimit.ι F α))) ≫
    DerivedCategory.Q.map
      (((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (glueingComplexRestrictIsoOver V F sIso (W α) (hWV α)).inv))).mp ?_
  simp only [Category.assoc]
  rw [reassoc_of% hCA']
  refine (cancel_epi (DerivedCategory.Q.map
      (((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (glueingComplexLocalIso W F I hsupp α).inv))).mp ?_
  rw [map_map_inv_comp_map_map_hom_assoc]
  refine (cancel_epi (DerivedCategory.Q.map
      (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom)) ≫
    DerivedCategory.Q.map
      (glueingComplexTransitionSourceIso W F I hsupp hβα).inv)).mp ?_
  simp only [Category.assoc]
  refine hCT.trans (Eq.symm ?_)
  have hcc := glueingComplexCompatibilityOver'' V W F I hsupp sIso hWV hβα h
  simp only [← CategoryTheory.Functor.map_comp_assoc] at hcc ⊢
  rw [hcc]
  simp only [CategoryTheory.Functor.map_comp_assoc]
  exact hCB

/-- **The identifications of the restrictions of the glued object over `V` are compatible with
the transitions the system of complexes determines.** This is
`Stacks.DerivedGlueing.glueing_compatibility` with `⊤` replaced by `V`, and with it the assembly
over `V` is complete. -/
theorem glueing_compatibility_over (S : LocallyGiven X) {β α : E} (hβα : W β ≤ W α) (h : β ≤ α) :
    (S.restrictionComp (W β) (W α) V hβα (hWV α)).hom.app (glueingObjectOver V F) ≫
        (S.restriction (W β) (W α) hβα).map
          (glueingRestrictionIsoOver V W F I hsupp sIso hqi hWV S α).hom ≫
        (glueingTransitionIso S W F I hsupp hqi hβα h).hom =
      (glueingRestrictionIsoOver V W F I hsupp sIso hqi hWV S β).hom := by
  have hE := S.restrictionCompFactors' (W β) (W α) V hβα (hWV α) (glueingComplexOver V F)
  have hstar :=
    transportHom_glueingComplexRestrictionIsoOver_comp V W F I hsupp sIso hqi hWV S hβα h
  simp only [glueingObjectOver, glueingRestrictionIsoOver, glueingTransitionIso, Iso.trans_hom,
    CategoryTheory.Iso.app_hom, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% (map_comp_hom_app DerivedCategory.Q DerivedCategory.Q
      (S.restrictionFactors (W β) (W α) hβα)
      (glueingComplexRestrictionIsoOver V W F I hsupp sIso hqi hWV α).hom),
    hstar, reassoc_of% hE]

/-- `Stacks.DerivedGlueing.glueing_compatibility_over` transported along a choice of prescribed
objects `K α` for the classes of the complexes `I α`. -/
theorem glueing_compatibility_of_iso_over (S : LocallyGiven X)
    (K : ∀ α : E, OpenDerivedCategory X (W α))
    (hK : ∀ α : E, DerivedCategory.Q.obj (I α) ≅ K α)
    {β α : E} (hβα : W β ≤ W α) (h : β ≤ α) :
    (S.restrictionComp (W β) (W α) V hβα (hWV α)).hom.app (glueingObjectOver V F) ≫
        (S.restriction (W β) (W α) hβα).map
          (glueingRestrictionIsoOver V W F I hsupp sIso hqi hWV S α ≪≫ hK α).hom ≫
        ((S.restriction (W β) (W α) hβα).mapIso (hK α).symm ≪≫
          glueingTransitionIso S W F I hsupp hqi hβα h ≪≫ hK β).hom =
      (glueingRestrictionIsoOver V W F I hsupp sIso hqi hWV S β ≪≫ hK β).hom := by
  have hc := glueing_compatibility_over V W F I hsupp sIso hqi hWV S hβα h
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, CategoryTheory.Functor.map_comp,
    Category.assoc]
  rw [map_map_hom_inv_comp_assoc, reassoc_of% hc]

include hsupp sIso hqi hWV in
/-- **The glueing problem is solved over an open containing the cover by a system of complexes
supported inside it.** Let `W` be a family of opens all contained in `V`, let
`F : E ⥤ CochainComplex (Mod 𝒪_X) ℤ` be a system of complexes over a nonempty linear order with
`F α` the extension by zero of a complex `I α` on `W α`, and such that restricting a transition
`F β ⟶ F α` to `W β` is a quasi-isomorphism whenever `β ≤ α`.  Assume the colimit of the system
is supported on `V`, in the sense that extension by zero from `V` undoes its restriction to `V`.
Let `K α` be the class of `I α` in the derived category on `W α`.  Then there is an object `G` of
the derived category on `V`, together with identifications of its restrictions with the `K α` and
transitions between the `K α`, compatible with each other.

This is `Stacks.DerivedGlueing.exists_glueing_of_complexSystem` with `⊤` replaced by `V`, and it
is the form the limit stages of the transfinite recursion of [Stacks, Tag 0D6B] consume, with
`V = W α` and the index order the stages strictly below `α`.  The glued object is
`Stacks.DerivedGlueing.glueingObjectOver`.

It is untagged: the datum is a system of *complexes*, not the system of objects of the derived
category and prescribed transitions that [Stacks, Tag 0D6B] starts from. -/
theorem exists_glueing_of_complexSystem_over (S : LocallyGiven X)
    (K : ∀ α : E, OpenDerivedCategory X (W α))
    (hK : ∀ α : E, DerivedCategory.Q.obj (I α) ≅ K α)
    (hmono : ∀ β α : E, β ≤ α → W β ≤ W α) :
    ∃ (G : OpenDerivedCategory X V)
      (sigma : ∀ α : E, (S.restriction (W α) V (hWV α)).obj G ≅ K α)
      (rho : ∀ (β α : E) (h : β ≤ α),
        (S.restriction (W β) (W α) (hmono β α h)).obj (K α) ≅ K β),
      ∀ (β α : E) (h : β ≤ α),
        (S.restrictionComp (W β) (W α) V (hmono β α h) (hWV α)).hom.app G ≫
            (S.restriction (W β) (W α) (hmono β α h)).map (sigma α).hom ≫ (rho β α h).hom =
          (sigma β).hom :=
  ⟨glueingObjectOver V F,
    fun α => glueingRestrictionIsoOver V W F I hsupp sIso hqi hWV S α ≪≫ hK α,
    fun β α h => (S.restriction (W β) (W α) (hmono β α h)).mapIso (hK α).symm ≪≫
      glueingTransitionIso S W F I hsupp hqi (hmono β α h) h ≪≫ hK β,
    fun β α h => glueing_compatibility_of_iso_over V W F I hsupp sIso hqi hWV S K hK
      (hmono β α h) h⟩

end Over

/-! ### The support hypothesis is inhabited, and the assembly over `⊤` is the case `V = ⊤` -/

/-- **The support hypothesis of the assembly over an open is inhabited at `V = ⊤`**: every
complex of `𝒪_X`-modules is supported on `⊤`, which is
`Stacks.DerivedGlueing.topRoundTripIso`.

This is the positive test for vacuity of the binder `sIso` of
`Stacks.DerivedGlueing.exists_glueing_of_complexSystem_over`: the type that binder ranges over is
not empty.  What it does *not* supply is the inhabitant a limit stage of [Stacks, Tag 0D6B]
needs, at `V = ⨆_β W β`; that one is the statement that a colimit of complexes supported on the
`W β` is supported on their union. -/
def glueingComplexSupportIsoTop
    (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ) :
    ((jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (glueingComplexOver (⊤ : Opens X.carrier) F) ≅ colimit F :=
  (topRoundTripIso X).app (colimit F)

/-- **The assembly over `⊤` is the case `V = ⊤` of the assembly over an open.** This re-derives
`Stacks.DerivedGlueing.exists_glueing_of_complexSystem` from
`Stacks.DerivedGlueing.exists_glueing_of_complexSystem_over`, so the relativized statement is
checked to be a genuine generalization and not a differently-shaped claim: the glued object over
`⊤` *is* `Stacks.DerivedGlueing.glueingObject`, and the support hypothesis there is
`Stacks.DerivedGlueing.glueingComplexSupportIsoTop`. -/
theorem exists_glueing_of_complexSystem_of_over (S : LocallyGiven X) (W : E → Opens X.carrier)
    (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ)
    (I : ∀ α : E, CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X (W α))) ℤ)
    (hsupp : ∀ α : E, F.obj α ≅
      ((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (I α))
    (hqi : ∀ (β α : E) (h : β ≤ α),
      QuasiIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom)))
    (K : ∀ α : E, OpenDerivedCategory X (W α))
    (hK : ∀ α : E, DerivedCategory.Q.obj (I α) ≅ K α)
    (hmono : ∀ β α : E, β ≤ α → W β ≤ W α) :
    ∃ (G : OpenDerivedCategory X ⊤)
      (sigma : ∀ α : E, (S.restriction (W α) ⊤ le_top).obj G ≅ K α)
      (rho : ∀ (β α : E) (h : β ≤ α),
        (S.restriction (W β) (W α) (hmono β α h)).obj (K α) ≅ K β),
      ∀ (β α : E) (h : β ≤ α),
        (S.restrictionComp (W β) (W α) ⊤ (hmono β α h) le_top).hom.app G ≫
            (S.restriction (W β) (W α) (hmono β α h)).map (sigma α).hom ≫ (rho β α h).hom =
          (sigma β).hom :=
  exists_glueing_of_complexSystem_over (⊤ : Opens X.carrier) W F I hsupp
    (glueingComplexSupportIsoTop F) hqi (fun _ => le_top) S K hK hmono

end Stacks.DerivedGlueing

end
