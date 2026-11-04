module

public import StacksFrontier.CategoryTheory.Sites.UniverseBridge.PullbackUniverseComparison
public import StacksFrontier.CategoryTheory.Sites.UniverseBridge.SheafFilteredColimits

/-!
# Universe-independent exactness from small diagram presentations

This module isolates the categorical assembly of the universe transfer. Its presentation
hypothesis must be discharged by a density theorem before the result can be used as an
unconditional universe bridge.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.Sites.UniverseBridge

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (F : C ⥤ D) [F.IsContinuous J K]

/-- If finite diagrams of large-valued sheaves have filtered presentations by small-valued
diagrams, left exactness of the small-valued pullback implies left exactness of the large one. -/
theorem preservesFiniteLimits_sheafPullback_of_small_presentations
    (hsmall : PreservesFiniteLimits (F.sheafPullback (Type u) J K))
    (hpres : ∀ (T : Type) [SmallCategory T] [FinCategory T]
      (G : T ⥤ Sheaf J (Type (max u v))),
      ∃ (I : Type (max u v)) (_ : SmallCategory I) (_ : IsFiltered I)
        (E : I ⥤ (T ⥤ Sheaf J (Type u)))
        (c : Cocone (E ⋙ (Functor.whiskeringRight T _ _).obj
          (sheafCompose J uliftFunctor.{v, u}))),
        Nonempty (c.pt ≅ G) ∧ Nonempty (IsColimit c)) :
    PreservesFiniteLimits (F.sheafPullback (Type (max u v)) J K) := by
  let P := F.sheafPullback (Type (max u v)) J K
  let Q := sheafCompose J uliftFunctor.{v, u}
  have : PreservesFiniteLimits Q := preservesFiniteLimits_sheafCompose_ulift J
  have : PreservesFiniteLimits (sheafCompose K uliftFunctor.{v, u}) :=
    preservesFiniteLimits_sheafCompose_ulift K
  have : PreservesFiniteLimits
      (F.sheafPullback (Type u) J K ⋙ sheafCompose K uliftFunctor.{v, u}) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (Q ⋙ P) :=
    preservesFiniteLimits_of_natIso (sheafPullbackUliftIso J K F).symm
  let : P.IsLeftAdjoint := (F.sheafAdjunctionContinuous (Type (max u v)) J K).isLeftAdjoint
  refine ⟨fun T _ _ ↦ ⟨fun {G} ↦ ?_⟩⟩
  obtain ⟨I, hI, hfil, E, c, ⟨e⟩, ⟨hc⟩⟩ := hpres T G
  have : PreservesFiniteLimits (colim : (I ⥤ Sheaf J (Type (max u v))) ⥤ _) :=
    preservesFiniteLimits_sheaf_colim J I
  have : PreservesFiniteLimits (colim : (I ⥤ Sheaf K (Type (max u v))) ⥤ _) :=
    preservesFiniteLimits_sheaf_colim K I
  have : PreservesColimitsOfShape I (lim : (T ⥤ Sheaf J (Type (max u v))) ⥤ _) :=
    preservesColimitsOfShape_lim_of_colim
  have : PreservesColimitsOfShape I (lim : (T ⥤ Sheaf K (Type (max u v))) ⥤ _) :=
    preservesColimitsOfShape_lim_of_colim
  have : PreservesLimit c.pt P :=
    preservesLimit_of_isColimit P _ c hc fun i ↦
      preservesLimit_image_of_comp Q P (E.obj i)
  exact preservesLimit_of_iso_diagram P e

end Stacks.Sites.UniverseBridge

end
