module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ComplexSystemGlueingOverAnOpen
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints

/-!
# The colimit of a system of complexes supported stagewise is supported on the union

`Stacks.DerivedGlueing.exists_glueing_of_complexSystem_over` assembles a system of complexes
`F : E ⥤ CochainComplex (Mod 𝒪_X) ℤ`, with `F α` supported on `W α`, into an object of the
derived category on an open `V` containing every `W α` — provided the colimit of the system is
*supported* on `V`, which is the hypothesis `sIso` there.  This file discharges that hypothesis
whenever `V` contains every `W α`, so in particular at `V = ⨆_α W α`, which is the open the limit
stages of the transfinite recursion of [Stacks, Tag 0D6B] work over.

## The argument

Being supported on `V` means that the counit `(j_V)_! (j_V)^* M ⟶ M` of extension by zero is
invertible at `M`, and `ExtensionByZeroModules.counit_isIso_of_stalk_isZero` reads that off the
stalks away from `V`.  At `M = (j_A)_! N` with `A ≤ V` those stalks vanish by
`ExtensionByZeroModules.isZero_stalk_jShriek`, which is the one place any sheaf theory is used.

Passing from the stages to their colimit is then formal, and does **not** go through the stalks
of the colimit: a natural transformation `η : A ⟶ 𝟭` whose target preserves nothing and whose
source preserves colimits of the shape at hand is invertible at `colim D` as soon as it is
invertible at every `D j`.  That is
`Stacks.DerivedGlueing.isIso_app_colimit_of_isIso_app`, and both `j_V^*` and `(j_V)_!` preserve
colimits, being left adjoints.

Complexes add only a degreewise layer: the counit of the prolonged adjunction is degreewise the
counit (`CategoryTheory.Adjunction.mapHomologicalComplexAdjunction`), a degreewise isomorphism of
complexes is an isomorphism, and `HomologicalComplex.eval` preserves colimits, so the degree-`n`
part of `colim F` is the colimit of the degree-`n` parts.

## Main results

* `Stacks.DerivedGlueing.isIso_app_colimit_of_isIso_app`: a natural transformation into the
  identity, with colimit-preserving source, is invertible at a colimit as soon as it is
  invertible at the diagram.
* `Stacks.DerivedGlueing.isIso_jShriekAdjunction_counit_app_jShriek`: a module extended by zero
  from a smaller open is supported on the bigger one.
* `Stacks.DerivedGlueing.glueingComplexSupportIso`: **the hypothesis `sIso` of the assembly over
  an open, discharged.**
* `Stacks.DerivedGlueing.exists_glueing_of_complexSystem_over_of_le`: the assembly over an open
  containing the cover, with the support hypothesis gone.

## References

* [Stacks Project, Tag 0D6B](https://stacks.math.columbia.edu/tag/0D6B)
* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open ExtensionByZeroModules

namespace Stacks.DerivedGlueing

universe w v u

/-! ### A natural transformation into the identity, at a colimit -/

section Abstract

variable {C : Type u} [Category.{w} C] {A : C ⥤ C} (η : A ⟶ 𝟭 C)

/-- Naturality of a transformation into the identity, with `𝟭` unfolded. -/
private theorem map_comp_app_eq {M N : C} (f : M ⟶ N) :
    A.map f ≫ η.app N = η.app M ≫ f :=
  η.naturality f

/-- **Invertibility of a natural transformation into the identity transfers along an
isomorphism of objects**, by naturality. -/
theorem isIso_app_of_iso {M N : C} (e : M ≅ N) (h : IsIso (η.app M)) : IsIso (η.app N) := by
  have hn := map_comp_app_eq η e.hom
  have := h
  have : IsIso (A.map e.hom ≫ η.app N) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left (A.map e.hom) _

/-- **A natural transformation into the identity is invertible at a colimit as soon as it is
invertible at the diagram**, provided its source preserves that colimit.

No cocontinuity of the target is needed, the target being the identity: the inverse is the map
out of the colimit whose leg at `j` is the inverse at `D j` followed by the image of the colimit
inclusion, and the two triangles are checked on the two colimits — the colimit of `D` for one and
its image under the source for the other. -/
theorem isIso_app_colimit_of_isIso_app {J : Type v} [Category.{w} J] (D : J ⥤ C) [HasColimit D]
    [PreservesColimit D A] (h : ∀ j : J, IsIso (η.app (D.obj j))) :
    IsIso (η.app (colimit D)) := by
  have := h
  have hkey : ∀ {j k : J} (f : j ⟶ k),
      D.map f ≫ inv (η.app (D.obj k)) = inv (η.app (D.obj j)) ≫ A.map (D.map f) := by
    intro j k f
    have hn := map_comp_app_eq η (D.map f)
    rw [IsIso.comp_inv_eq, Category.assoc, hn, ← Category.assoc, IsIso.inv_hom_id,
      Category.id_comp]
  let c : Cocone D :=
    { pt := A.obj (colimit D)
      ι :=
        { app := fun j => inv (η.app (D.obj j)) ≫ A.map (colimit.ι D j)
          naturality := fun j k f => by
            dsimp
            rw [Category.comp_id, ← Category.assoc, hkey f, Category.assoc,
              ← CategoryTheory.Functor.map_comp, colimit.w] } }
  have hc : IsColimit (A.mapCocone (colimit.cocone D)) :=
    isColimitOfPreserves A (colimit.isColimit D)
  refine ⟨colimit.desc D c, ?_, ?_⟩
  · refine hc.hom_ext fun j => ?_
    have hn := map_comp_app_eq η (colimit.ι D j)
    dsimp
    rw [← Category.assoc, hn, Category.assoc, colimit.ι_desc]
    show η.app (D.obj j) ≫ inv (η.app (D.obj j)) ≫ A.map (colimit.ι D j) = _
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp, Category.comp_id]
  · refine colimit.hom_ext fun j => ?_
    have hn := map_comp_app_eq η (colimit.ι D j)
    rw [← Category.assoc, colimit.ι_desc]
    show (inv (η.app (D.obj j)) ≫ A.map (colimit.ι D j)) ≫ η.app (colimit D) = _
    rw [Category.assoc, hn, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    simp

end Abstract

/-! ### Extension by zero from a smaller open is supported on the bigger one -/

section Support

variable {Z : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u})

/-- **A module extended by zero from a smaller open is supported on the bigger one.** For
`A ≤ V` the counit of `j_{V,!} ⊣ j_V^*` is invertible at `(j_A)_! N`: its stalks away from `V`
are stalks away from `A`, and those vanish by
`ExtensionByZeroModules.isZero_stalk_jShriek`. -/
theorem isIso_jShriekAdjunction_counit_app_jShriek {A V : Opens Z} (hAV : A ≤ V)
    (N : SheafOfModules.{u} (resRing A O)) :
    IsIso ((jShriekAdjunction V O).counit.app ((jShriek A O).obj N)) :=
  counit_isIso_of_stalk_isZero V O _ fun x hx =>
    isZero_stalk_jShriek A O N x fun hxA => hx (hAV hxA)

end Support

/-! ### The support hypothesis of the assembly over an open, discharged -/

section ColimitSupport

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} {E : Type u} [LinearOrder E] [Nonempty E]
  (V : Opens X.carrier) (W : E → Opens X.carrier)
  (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ)
  (I : ∀ α : E, CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X (W α))) ℤ)

omit [Nonempty E] in
/-- The counit of extension by zero along `V` is invertible in each degree at each stage of a
system supported stagewise inside `V`. -/
theorem isIso_counit_app_stage
    (hsupp : ∀ α : E, F.obj α ≅
      ((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (I α))
    (hWV : ∀ α : E, W α ≤ V)
    (n : ℤ) (α : E) :
    IsIso ((jShriekAdjunction V (underlyingRingSheaf X)).counit.app
      ((F ⋙ HomologicalComplex.eval _ _ n).obj α)) :=
  isIso_app_of_iso (jShriekAdjunction V (underlyingRingSheaf X)).counit
    (((HomologicalComplex.eval _ _ n).mapIso (hsupp α)).symm)
    (isIso_jShriekAdjunction_counit_app_jShriek (underlyingRingSheaf X) (hWV α) ((I α).X n))

/-- The counit of extension by zero along `V` is invertible in each degree at the colimit of a
system supported stagewise inside `V`. -/
theorem isIso_counit_app_colimit_eval
    (hsupp : ∀ α : E, F.obj α ≅
      ((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (I α))
    (hWV : ∀ α : E, W α ≤ V)
    (n : ℤ) :
    IsIso ((jShriekAdjunction V (underlyingRingSheaf X)).counit.app ((colimit F).X n)) :=
  isIso_app_of_iso (jShriekAdjunction V (underlyingRingSheaf X)).counit
    (preservesColimitIso (HomologicalComplex.eval _ _ n) F).symm
    (isIso_app_colimit_of_isIso_app (jShriekAdjunction V (underlyingRingSheaf X)).counit
      (F ⋙ HomologicalComplex.eval _ _ n) (isIso_counit_app_stage V W F I hsupp hWV n))

/-- **The colimit of a system of complexes supported stagewise inside `V` is supported on
`V`.** -/
theorem isIso_mapHomologicalComplexAdjunction_counit_app_colimit
    (hsupp : ∀ α : E, F.obj α ≅
      ((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (I α))
    (hWV : ∀ α : E, W α ≤ V) :
    IsIso ((Adjunction.mapHomologicalComplexAdjunction
      (jShriekAdjunction V (underlyingRingSheaf X)) (ComplexShape.up ℤ)).counit.app
        (colimit F)) := by
  have : ∀ n : ℤ, IsIso (((Adjunction.mapHomologicalComplexAdjunction
      (jShriekAdjunction V (underlyingRingSheaf X))
        (ComplexShape.up ℤ)).counit.app (colimit F)).f n) := fun n => by
    show IsIso ((jShriekAdjunction V (underlyingRingSheaf X)).counit.app ((colimit F).X n))
    exact isIso_counit_app_colimit_eval V W F I hsupp hWV n
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **The support hypothesis of the assembly over an open, discharged.** If every member of the
cover is contained in `V` then extension by zero from `V` undoes restriction to `V` on the
colimit of the system — which is the hypothesis `sIso` of
`Stacks.DerivedGlueing.exists_glueing_of_complexSystem_over`, and the isomorphism is the counit
of extension by zero along `V`. -/
def glueingComplexSupportIso
    (hsupp : ∀ α : E, F.obj α ≅
      ((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (I α))
    (hWV : ∀ α : E, W α ≤ V) :
    ((jShriek V (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (glueingComplexOver V F) ≅ colimit F :=
  @asIso _ _ _ _ ((Adjunction.mapHomologicalComplexAdjunction
      (jShriekAdjunction V (underlyingRingSheaf X)) (ComplexShape.up ℤ)).counit.app (colimit F))
    (isIso_mapHomologicalComplexAdjunction_counit_app_colimit V W F I hsupp hWV)

/-- **The glueing problem is solved over any open containing the cover, by a system of complexes
supported stagewise on the cover.** This is
`Stacks.DerivedGlueing.exists_glueing_of_complexSystem_over` with its support hypothesis
discharged by `Stacks.DerivedGlueing.glueingComplexSupportIso`, so the only hypotheses left are
those of the system itself.

Read at `V = ⨆_α W α` this is the comparison the limit stages of the transfinite recursion of
[Stacks, Tag 0D6B] consume: the colimit of the stages strictly below a limit stage `α` is an
object over `W α` whose restrictions to the earlier stages are the prescribed objects there,
compatibly with the prescribed transitions. -/
theorem exists_glueing_of_complexSystem_over_of_le
    (hsupp : ∀ α : E, F.obj α ≅
      ((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (I α))
    (hWV : ∀ α : E, W α ≤ V)
    (S : LocallyGiven X)
    (hqi : ∀ (β α : E) (h : β ≤ α),
      QuasiIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom)))
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
  exists_glueing_of_complexSystem_over V W F I hsupp
    (glueingComplexSupportIso V W F I hsupp hWV) hqi hWV S K hK hmono

end ColimitSupport

end Stacks.DerivedGlueing

end
