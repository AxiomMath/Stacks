module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.Situation
public import StacksFrontier.CategoryTheory.Sites.LocallyBijective

/-!
# Exactness detected on weakly contractible objects

On a ringed site with a covering collection of weakly contractible objects, a complex of
sheaves of modules is exact if and only if its complex of sections is exact on every object
in the collection.

One direction evaluates: over a weakly contractible object, sections of abelian sheaves is an
exact functor, because a locally surjective morphism is already surjective there; combined
with exactness of the forgetful functor from sheaves of modules to abelian sheaves, an exact
complex stays exact on sections. The other direction glues: surjectivity of the map to cycles
over every member of the collection makes that map locally surjective, hence an epimorphism,
and `ShortComplex.exact_iff_epi_toCycles` reads that back as exactness.

## Main results

* `Stacks.WeaklyContractible.exact_iff_exact_sections_of_weaklyContractibleObjectsSituation`
  characterizes exactness of a short complex of sheaves of modules by exactness on the chosen
  covering collection.

## Implementation notes

A three-term complex is represented by a `ShortComplex`. Exactness of the evaluated maps is
stated as `Function.Exact`, directly on the underlying functions of the module homomorphisms
on sections.

## References

* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947)
-/

@[expose] public section

open CategoryTheory Opposite

universe w v u t

namespace Stacks.WeaklyContractible

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

private theorem preservesColimit_of_comp_preservesColimit
    {A B D : Type*} [Category A] [Category B] [Category D]
    {K : Type*} [Category K] (E : K ⥤ A) (G : A ⥤ B) (F : B ⥤ D)
    (hG : Limits.PreservesColimit E G) (hGF : Limits.PreservesColimit E (G ⋙ F))
    (hE : Limits.HasColimit E) : Limits.PreservesColimit (E ⋙ G) F :=
  Limits.preservesColimit_of_preserves_colimit_cocone
    (Limits.isColimitOfPreserves G (Limits.colimit.isColimit E))
    (Limits.isColimitOfPreserves (G ⋙ F) (Limits.colimit.isColimit E))

private theorem toSheaf_preservesFiniteColimits
    (R : Sheaf J RingCat.{w}) [HasSheafify J AddCommGrpCat.{t}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{t}] :
    Limits.PreservesFiniteColimits (SheafOfModules.toSheaf.{t} R) := by
  refine ⟨fun K _ _ => ?_⟩
  let L := PresheafOfModules.sheafification (𝟙 R.obj)
  let G := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  have hL' : Limits.PreservesColimitsOfShape K L :=
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 R.obj)).leftAdjoint_preservesColimits).preservesColimitsOfShape
  have hcomp : Limits.PreservesColimitsOfShape K (L ⋙ SheafOfModules.toSheaf R) := by
    have e : L ⋙ SheafOfModules.toSheaf R ≅
        PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat :=
      PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)
    let : Limits.PreservesColimitsOfShape K (PresheafOfModules.toPresheaf R.obj) :=
      (inferInstance : Limits.PreservesFiniteColimits _).preservesFiniteColimits K
    let : Limits.PreservesColimitsOfShape K (presheafToSheaf J AddCommGrpCat) :=
      ((sheafificationAdjunction J AddCommGrpCat).leftAdjoint_preservesColimits
        ).preservesColimitsOfShape
    exact Limits.preservesColimitsOfShape_of_natIso e.symm
  have e : G ⋙ L ≅ 𝟭 (SheafOfModules R) :=
    asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit
  refine ⟨fun {D} => ?_⟩
  have key : Limits.PreservesColimit ((D ⋙ G) ⋙ L) (SheafOfModules.toSheaf R) :=
    preservesColimit_of_comp_preservesColimit (D ⋙ G) L (SheafOfModules.toSheaf R)
      hL'.preservesColimit hcomp.preservesColimit inferInstance
  exact Limits.preservesColimit_of_iso_diagram (SheafOfModules.toSheaf R)
    ((Functor.associator D G L) ≪≫ Functor.isoWhiskerLeft D e ≪≫ D.rightUnitor)

/-- In a site covered by weakly contractible objects, a complex of sheaves of modules is
exact if and only if it is exact on sections over every chosen weakly contractible object. -/
@[stacks 0947 "exact_iff_sections"]
theorem exact_iff_exact_sections_of_weaklyContractibleObjectsSituation
    [HasSheafify J AddCommGrpCat.{t}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
    (h : WeaklyContractibleObjectsSituation.{w, v, u, t} C J)
    (S : ShortComplex (SheafOfModules.{t} h.O)) :
    S.Exact ↔ ∀ ⦃U : C⦄, h.B U →
      Function.Exact (S.f.val.app (op U)) (S.g.val.app (op U)) := by
  refine ⟨fun hS U hU => ?_, fun hs => ?_⟩
  · let evalU := (sheafSections J AddCommGrpCat).obj (op U)
    let : Limits.PreservesFiniteLimits evalU :=
      Limits.preservesFiniteLimits_of_natIso
        (sheafSectionsNatIsoEvaluation J AddCommGrpCat.{t} (X := U)).symm
    let : evalU.Additive := evalU.additive_of_preserves_binary_products
    let : evalU.PreservesEpimorphisms := by
      constructor
      intro X Y f hf
      let forgetAb := sheafCompose J (forget AddCommGrpCat.{t})
      let : Sheaf.IsLocallySurjective f :=
        (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat f).2 hf
      have hloc : Sheaf.IsLocallySurjective (forgetAb.map f) := by
        show Presheaf.IsLocallySurjective J
          (Functor.whiskerRight f.hom (forget AddCommGrpCat.{t}))
        infer_instance
      exact (AddCommGrpCat.epi_iff_surjective _).2
        (h.isWeaklyContractible hU (forgetAb.obj X) (forgetAb.obj Y)
          (forgetAb.map f) hloc)
    let : evalU.PreservesHomology :=
      Functor.preservesHomology_of_preservesEpis_and_kernels evalU
    let : Limits.PreservesFiniteColimits evalU :=
      Functor.preservesFiniteColimits_of_preservesHomology evalU
    let _ : Limits.PreservesFiniteColimits (SheafOfModules.toSheaf.{t} h.O) :=
      toSheaf_preservesFiniteColimits J h.O
    exact (ShortComplex.ab_exact_iff_function_exact _).mp
      ((hS.map (SheafOfModules.toSheaf h.O)).map evalU)
  · rw [ShortComplex.exact_iff_epi_toCycles]
    let φ := (SheafOfModules.toSheaf h.O).map S.toCycles
    have hsurj : ∀ ⦃U : C⦄, h.B U → Function.Surjective (φ.hom.app (op U)) := by
      show ∀ ⦃U : C⦄, h.B U → Function.Surjective (S.toCycles.val.app (op U))
      intro U hU z
      have hz : S.g.val.app (op U) (S.iCycles.val.app (op U) z) = 0 := by
        show ((S.iCycles ≫ S.g).val.app (op U)) z = 0
        rw [S.iCycles_g]
        rfl
      obtain ⟨x, hx⟩ := (hs hU _).mp hz
      refine ⟨x, ?_⟩
      let _ : Mono S.iCycles.val := (SheafOfModules.forget h.O).map_mono S.iCycles
      apply PresheafOfModules.injective_of_mono S.iCycles.val (op U)
      show ((S.toCycles ≫ S.iCycles).val.app (op U)) x = S.iCycles.val.app (op U) z
      rwa [S.toCycles_i]
    have : Epi φ := (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat φ).mp
      (Presheaf.isLocallySurjective_of_hasEnoughObjects_surjective
        (φ := φ.hom) J h.hasEnoughObjects hsurj)
    exact (inferInstance : (SheafOfModules.toSheaf h.O).ReflectsEpimorphisms).reflects
      S.toCycles this

end Stacks.WeaklyContractible

end
