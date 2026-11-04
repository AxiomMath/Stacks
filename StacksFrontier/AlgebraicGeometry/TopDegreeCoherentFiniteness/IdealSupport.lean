module

public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.Scalars
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IrreducibleSupportCriterion
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleLength

/-!
# Nonzero ideals of an integral scheme near the generic point

A nonzero quasi-coherent ideal `ℐ` of an integral scheme `Z` is the whole structure sheaf on an
open neighbourhood of the generic point, so `𝒪_Z/ℐ` is supported off that open, and `ℐ` is
supported at the generic point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.TopDegree

/-- The source of an epimorphism of abelian groups has a nonzero element if the target does. -/
private theorem exists_ne_zero_of_epi {A B : Ab.{u}} (f : A ⟶ B) [Epi f] {b : B} (hb : b ≠ 0) :
    ∃ t : A, t ≠ 0 := by
  obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective f).mp inferInstance b
  exact ⟨t, fun h => hb (by rw [← ht, h]; exact map_zero _)⟩

/-- **A nonzero quasi-coherent ideal of an integral scheme fills a neighbourhood of the generic
point**, in the form: the inclusion is an isomorphism over an open containing the generic point. -/
theorem exists_isIso_restrict_ideal_ι {Z : Scheme.{u}} [IsIntegral Z]
    (H : (SheafOfModules.unit Z.ringCatSheaf).Submodule) (hz : ¬ IsZero H.toSheafOfModules) :
    ∃ U : Z.Opens, genericPoint Z ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map H.ι) := by
  classical

  have hs : ∃ (U : Z.Opens) (s : Γ(H.toSheafOfModules, U)),
      (s.val : Γ(Z, U)) ≠ 0 := by
    by_contra! h
    apply hz
    apply (IsZero.iff_id_eq_zero _).mpr
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.Hom.ext
    funext U
    apply ModuleCat.Hom.ext
    ext s
    apply Subtype.ext
    exact h U.unop s
  obtain ⟨U, s, hs⟩ := hs
  let t : Γ(Z, U) := s.val
  let V := Z.basicOpen t
  have hV : (V : Set Z).Nonempty :=
    V.ne_bot_iff_nonempty.mp (fun h => hs ((basicOpen_eq_bot_iff t).mp h))
  have hξ : genericPoint Z ∈ V :=
    ((genericPoint_spec Z).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  refine ⟨V, hξ, Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun W => ?_⟩
  let W' : Z.Opens := V.ι ''ᵁ W
  have hWV : W' ≤ V := by simpa [W'] using V.ι.image_le_opensRange W
  let k : W' ⟶ U := homOfLE (hWV.trans (Z.basicOpen_le t))
  have htH : (Z.presheaf.map k.op) t ∈ H.toSubmodule.obj (op W') :=
    H.toSubmodule.map k.op s.property
  have htUnit : IsUnit ((Z.presheaf.map k.op) t) := by
    have h := (Z.toRingedSpace.isUnit_res_basicOpen t).map
      (Z.presheaf.map (homOfLE hWV).op).hom
    change IsUnit ((Z.presheaf.map (homOfLE hWV).op)
      ((Z.presheaf.map (homOfLE (Z.basicOpen_le t)).op) t)) at h
    rwa [← CommRingCat.comp_apply, ← Functor.map_comp] at h
  have htop : H.toSubmodule.obj (op W') = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨v, hv⟩ := htUnit
    let a' : Γ(Z, W') := a
    have h := (H.toSubmodule.obj (op W')).smul_mem
      (a' * (↑(v⁻¹) : Γ(Z, W'))) htH
    change (a' * (↑(v⁻¹) : Γ(Z, W'))) * ((Z.presheaf.map k.op) t) ∈ _ at h
    rwa [← hv, mul_assoc, Units.inv_mul, mul_one] at h
  have : Mono (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor V.ι).map H.ι) W) :=
    (AddCommGrpCat.mono_iff_injective _).mpr Subtype.val_injective
  have : Epi (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor V.ι).map H.ι) W) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr fun a => ⟨⟨a, htop.ge trivial⟩, rfl⟩
  exact isIso_of_mono_of_epi _


/-- A nonzero quasi-coherent ideal of an integral scheme is supported at the generic point. -/
theorem genericPoint_mem_supp_ideal {Z : Scheme.{u}} [IsIntegral Z]
    (H : (SheafOfModules.unit Z.ringCatSheaf).Submodule) (hz : ¬ IsZero H.toSheafOfModules) :
    genericPoint Z ∈ SheafOfModules.supp H.toSheafOfModules := by
  obtain ⟨U, hU, hi⟩ := exists_isIso_restrict_ideal_ι H hz
  have := hi
  have hst : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} (genericPoint Z)).map
      (Scheme.Modules.Hom.mapPresheaf H.ι)) :=
    (NatIso.isIso_map_iff
      (Scheme.Modules.restrictStalkNatIso U.ι (⟨genericPoint Z, hU⟩ : U)) H.ι).mp
        (by
          show IsIso ((Scheme.Modules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} _).map
            ((Scheme.Modules.restrictFunctor U.ι).map H.ι))
          infer_instance)
  let O : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  have h1 : O.presheaf.germ ⊤ (genericPoint Z) trivial (1 : Γ(Z, ⊤)) ≠ 0 := by
    intro h
    have h' : O.presheaf.germ ⊤ (genericPoint Z) trivial (1 : Γ(Z, ⊤)) =
        O.presheaf.germ ⊤ (genericPoint Z) trivial (0 : Γ(Z, ⊤)) := by
      have hz : (ConcreteCategory.hom (O.presheaf.germ ⊤ (genericPoint Z) trivial))
          (0 : Γ(Z, ⊤)) = 0 := map_zero _
      rwa [hz]
    obtain ⟨W, hxW, k, l, hW⟩ := O.presheaf.germ_eq (genericPoint Z) (by trivial) (by trivial)
      (1 : Γ(Z, ⊤)) (0 : Γ(Z, ⊤)) h'
    have : Nonempty W := ⟨⟨genericPoint Z, hxW⟩⟩
    change (Z.presheaf.map k.op) 1 = (Z.presheaf.map l.op) 0 at hW
    simp at hW
  have : Epi ((TopCat.Presheaf.stalkFunctor Ab.{u} (genericPoint Z)).map
    (Scheme.Modules.Hom.mapPresheaf H.ι)) := inferInstance
  exact @exists_ne_zero_of_epi _ _ _ this _ h1

/-- A point in the support of a module is carried into the support of its direct image along a
closed immersion. -/
theorem mem_supp_pushforward_of_mem {W X : Scheme.{u}} (i : W ⟶ X) [IsClosedImmersion i]
    (F : W.Modules) (x : W) (hx : x ∈ SheafOfModules.supp F) :
    i.base x ∈ SheafOfModules.supp ((Scheme.Modules.pushforward i).obj F) := by
  let a := TopCat.Presheaf.stalkPushforward Ab.{u} i.base F.presheaf x
  have : IsIso a := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
    (C := Ab.{u}) i.isClosedEmbedding.isInducing F.presheaf x
  obtain ⟨s, hs⟩ := hx
  have : Epi a := inferInstance
  exact @exists_ne_zero_of_epi _ _ _ this _ hs

/-- **The direct image of a nonzero ideal of an integral closed subscheme is supported on the
whole subscheme**, in the form: every closed set containing its support contains the image. -/
theorem range_subset_of_supp_pushforward_ideal_subset {W X : Scheme.{u}} (i : W ⟶ X)
    [IsClosedImmersion i] [IsIntegral W]
    (H : (SheafOfModules.unit W.ringCatSheaf).Submodule) (hz : ¬ IsZero H.toSheafOfModules)
    (T : Set X) (hTc : IsClosed T)
    (hT : SheafOfModules.supp ((Scheme.Modules.pushforward i).obj H.toSheafOfModules) ⊆ T) :
    Set.range i.base ⊆ T := by
  have hη := hT (mem_supp_pushforward_of_mem i _ _ (genericPoint_mem_supp_ideal H hz))
  rintro _ ⟨w, rfl⟩
  have hspec : genericPoint W ⤳ w := (genericPoint_spec W).specializes (Set.mem_univ w)
  exact hTc.stableUnderSpecialization (hspec.map i.continuous) hη

end AlgebraicGeometry.TopDegree

end
