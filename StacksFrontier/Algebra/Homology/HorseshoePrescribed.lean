module

public import StacksFrontier.Algebra.Homology.CartanEilenbergResolutions
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# The horseshoe lemma with a prescribed resolution of the third term

Let `0 → S₁ → S₂ → S₃ → 0` be a short exact sequence in an abelian category with enough
injectives, and `ι₃ : S₃[0] ⟶ T₃` a given injective resolution (`ℤ`-graded, supported in degrees
`≥ 0`). Then there are injective resolutions `T₁` of `S₁` and `T₂` of `S₂`, supported in degrees
`≥ 0`, and a short exact sequence `0 → T₁ → T₂ → T₃ → 0` of complexes over the given one, which is
split in every degree (`CategoryTheory.ShortComplex.ShortExact.exists_horseshoe_of_resolution`):
the first resolution is a chosen one, and the horseshoe lemma
(`StacksDraft.CartanEilenbergResolutions.horseshoeProperty`, Tag 013T) builds `T₂`.

Being degreewise split, the sequence stays short exact after applying any additive functor
degreewise (`HomologicalComplex.shortExact_map_mapHomologicalComplex_of_splitting`).

This is the form used in descending inductions over a family of resolutions indexed by the
object *and* its resolution: the resolution of the object being treated is fixed.

## References

* [Stacks Project, Tag 013T](https://stacks.math.columbia.edu/tag/013T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C D ι : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {c : ComplexShape ι}

/-- **A degreewise split short exact sequence of complexes stays short exact under any additive
functor applied degreewise.** -/
theorem shortExact_map_mapHomologicalComplex_of_splitting
    (S : ShortComplex (HomologicalComplex C c))
    (h : ∀ i, Nonempty ((S.map (HomologicalComplex.eval C c i)).Splitting))
    (F : C ⥤ D) [F.Additive] :
    (S.map (F.mapHomologicalComplex c)).ShortExact :=
  shortExact_of_degreewise_shortExact _ fun i => ((h i).some.map F).shortExact

end HomologicalComplex

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]

/-- **The horseshoe lemma with a prescribed resolution of the third term.** -/
theorem exists_horseshoe_of_resolution {S : ShortComplex C} (hS : S.ShortExact)
    (T₃ : CochainComplex C ℤ) [T₃.IsStrictlyGE 0] [∀ q, Injective (T₃.X q)]
    (ι₃ : (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj S.X₃ ⟶ T₃) [_root_.QuasiIso ι₃] :
    ∃ (T₁ T₂ : CochainComplex C ℤ) (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) (w : f ≫ g = 0)
      (ι₁ : (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj S.X₁ ⟶ T₁)
      (ι₂ : (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj S.X₂ ⟶ T₂),
      T₁.IsStrictlyGE 0 ∧ T₂.IsStrictlyGE 0 ∧ (∀ q, Injective (T₁.X q)) ∧
        (∀ q, Injective (T₂.X q)) ∧
        _root_.QuasiIso ι₁ ∧ _root_.QuasiIso ι₂ ∧
        (ShortComplex.mk f g w).ShortExact ∧
        ι₁ ≫ f = (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map S.f ≫ ι₂ ∧
        ι₂ ≫ g = (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map S.g ≫ ι₃ ∧
        ∀ n, Nonempty (((ShortComplex.mk f g w).map
          (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting) := by
  obtain ⟨K₁⟩ := HasInjectiveResolution.out (Z := S.X₁)
  obtain ⟨T₂, f, g, w, ι₂, hse, hge₂, hinj₂, hqi₂, hc₁, hc₂⟩ :=
    StacksDraft.CartanEilenbergResolutions.horseshoeProperty C S hS K₁.cochainComplex T₃
      inferInstance inferInstance (fun _ => inferInstance) (fun _ => inferInstance) K₁.ι' ι₃
      inferInstance inferInstance
  refine ⟨K₁.cochainComplex, T₂, f, g, w, K₁.ι', ι₂, inferInstance, hge₂, fun _ => inferInstance,
    hinj₂, inferInstance, hqi₂, hse, hc₁, hc₂, fun n => ?_⟩
  have h := hse.map_of_exact (HomologicalComplex.eval C (ComplexShape.up ℤ) n)
  have : Injective ((ShortComplex.mk f g w).map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).X₁ :=
    inferInstanceAs (Injective (K₁.cochainComplex.X n))
  exact ⟨h.splittingOfInjective⟩

end CategoryTheory.ShortComplex.ShortExact
