module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Depth
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.WeakAssPushforward
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.RingTheory.Depth.Defs.Defs

/-!
# Hartogs extension for coherent sheaves of depth at least two

A coherent module on a locally Noetherian scheme is recovered from its restriction to an
open subscheme if its stalks have depth at least two at every point of the complement.
Consequently, global sections extend uniquely across that complement.

## Main results

* `AlgebraicGeometry.isIso_stalkFunctor_map_unit_of_mem` says that the canonical map to the
  pushforward of the restriction is already a stalk isomorphism at the points of the open,
  with no hypothesis on the module.
* `AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two` says that the canonical
  map to the pushforward of the restriction is an isomorphism.
* `AlgebraicGeometry.restriction_bijective_of_depth_ge_two` says that restriction of global
  sections to the open subscheme is bijective.

## Implementation notes

Restriction to the open subscheme `U` is represented by pullback along `U.ι`. The
canonical map to the pushforward is the unit of the pullback--pushforward adjunction.
Sections on the open subscheme are identified with sections of the original sheaf on
the open set `U`, so their restriction map is the presheaf map from `⊤` to `U`.
The module structure on a stalk is made explicit in the depth hypothesis.

Quasi-coherence of the pushforward along `U.ι` is the quasi-compact quasi-separated case,
`AlgebraicGeometry.pushforward_isQuasicoherent`: on a locally Noetherian scheme an open
immersion is quasi-compact by [Stacks, Tag 01OX], and it is quasi-separated because it is a
monomorphism, so both hypotheses of that instance are available here without being assumed.

## References

* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.WeakAssPushforward (IsWeaklyAssociatedPoint
  not_isWeaklyAssociatedPoint_pushforward_of_not_mem_range)

universe u

namespace AlgebraicGeometry

/-- **The canonical map to the pushforward of a restriction is a stalk isomorphism over the
open.** For an open `U` of `X` and a module `F` on `X`, the unit of the
pullback--pushforward adjunction at `F` induces an isomorphism on the stalk at every point of
`U`: the restriction of that unit to `U` is already an isomorphism, by the triangle identity
and the invertibility of the counit of the restriction adjunction, and the stalk of a
restriction at a point of `U` is the stalk on `X`.

No depth hypothesis and no coherence is needed; the depth hypothesis of
[Stacks, Tag 0E9I] is what upgrades this to an isomorphism of modules, below. -/
private lemma stalk_unit_isIso_of_mem
    (X : Scheme.{u}) (U : X.Opens) (F : X.Modules) (x : X) (hx : x ∈ U) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F).val))) := by
  let L := Scheme.Modules.restrictFunctor U.ι
  let R := Scheme.Modules.pushforward U.ι
  let adjL := Scheme.Modules.restrictAdjunction U.ι
  let adjP := Scheme.Modules.pullbackPushforwardAdjunction U.ι
  let α := Scheme.Modules.restrictFunctorIsoPullback U.ι
  have hunit : adjL.unit.app F ≫ R.map (α.hom.app F) = adjP.unit.app F :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ F
  have hLunit : IsIso (L.map (adjL.unit.app F)) := by
    have htri : L.map (adjL.unit.app F) ≫ adjL.counit.app (L.obj F) = 𝟙 (L.obj F) := by
      simp [L, adjL, (Scheme.Modules.restrictAdjunction U.ι).left_triangle_components F]
    have : IsIso (L.map (adjL.unit.app F) ≫ adjL.counit.app (L.obj F)) := by
      rw [htri]
      infer_instance
    exact IsIso.of_isIso_comp_right (L.map (adjL.unit.app F)) (adjL.counit.app (L.obj F))
  have hLunitP : IsIso (L.map (adjP.unit.app F)) := by
    rw [← hunit, Functor.map_comp]
    infer_instance
  let xU : (U : Scheme) := ⟨x, hx⟩
  let κ := Scheme.Modules.restrictStalkNatIso U.ι xU
  have hrestricted : IsIso ((Scheme.Modules.toPresheaf (U : Scheme) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
        (L.map (adjP.unit.app F))) :=
    Functor.map_isIso _ _
  let m₁ := ((Scheme.Modules.toPresheaf (U : Scheme) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map (L.map (adjP.unit.app F)))
  let m₂ := κ.hom.app (R.obj ((Scheme.Modules.pullback U.ι).obj F))
  let m₃ := κ.hom.app F
  let m₄ := ((Scheme.Modules.toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.ι xU)).map (adjP.unit.app F))
  have hnat' : m₁ ≫ m₂ = m₃ ≫ m₄ := by
    simpa [m₁, m₂, m₃, m₄] using κ.hom.naturality (adjP.unit.app F)
  have : IsIso (m₃ ≫ m₄) := by
    rw [← hnat']
    infer_instance
  exact IsIso.of_isIso_comp_left m₃ m₄

/-- **The canonical map to the pushforward of a restriction is a stalk isomorphism over the
open**, with no hypothesis on the module: the public form of the stalk clause above, for the
consumers that build a stabilized open extension out of a pushforward. -/
alias isIso_stalkFunctor_map_unit_of_mem := stalk_unit_isIso_of_mem

/-- **Stacks Project, Tag 0E9I.** A coherent sheaf with depth at least two along the
complement of an open subscheme is canonically the pushforward of its restriction. -/
@[stacks 0E9I "canonical sheaf isomorphism", ega "IV 5.10.6" "sufficiency"]
theorem isIso_unit_restrict_pushforward_of_depth_ge_two
    (X : Scheme.{u}) [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      let M := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
      letI : Module (X.presheaf.stalk x) M :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          F.val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) M) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F) := by
  have : F.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  have : ((𝟭 X.Modules).obj F).IsQuasicoherent := by
    simpa using (inferInstance : F.IsQuasicoherent)
  have : ((𝟭 X.Modules).obj F).IsCoherent := by
    simpa using (inferInstance : F.IsCoherent)
  have : ((Scheme.Modules.restrictFunctor U.ι).obj F).IsQuasicoherent := inferInstance
  have : ((Scheme.Modules.pullback U.ι).obj F).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (U : Scheme).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F) inferInstance
  let G := (Scheme.Modules.pushforward U.ι).obj ((Scheme.Modules.pullback U.ι).obj F)
  have : G.IsQuasicoherent := by
    dsimp [G]
    infer_instance
  have : ((Scheme.Modules.pullback U.ι ⋙
      Scheme.Modules.pushforward U.ι).obj F).IsQuasicoherent := by
    simpa [G] using (inferInstance : G.IsQuasicoherent)
  have hf : ∀ x : X,
      let : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
          ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F).val)) ∨
      ((2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) ∧
        x ∉ Stacks.Divisors.associatedPoints G) := by
    intro x
    let : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    by_cases hx : x ∈ U
    · exact Or.inl (isIso_stalkFunctor_map_unit_of_mem X U F x hx)
    · refine Or.inr ⟨hdepth x hx, fun hxass => ?_⟩
      have hxrange : x ∉ Set.range U.ι := by
        rintro ⟨y, rfl⟩
        exact hx y.2
      exact not_isWeaklyAssociatedPoint_pushforward_of_not_mem_range U.ι
        ((Scheme.Modules.pullback U.ι).obj F) x hxrange
        (AlgebraicGeometry.associatedPoints_subset_weaklyAssociatedPoints G hxass)
  exact AlgebraicGeometry.isIso_of_stalk_isIso_or_depth_two_and_not_associated
    ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F) hf

/-- **Stacks Project, Tag 0E9I.** Under the same depth hypothesis, every section on
the open subscheme extends uniquely to a global section. -/
@[stacks 0E9I "global sections"]
theorem restriction_bijective_of_depth_ge_two
    (X : Scheme.{u}) [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      let M := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
      letI : Module (X.presheaf.stalk x) M :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          F.val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) M) :
    Function.Bijective
      (F.presheaf.map (homOfLE (show U ≤ (⊤ : X.Opens) from le_top)).op) := by
  let adjL := Scheme.Modules.restrictAdjunction U.ι
  let adjP := Scheme.Modules.pullbackPushforwardAdjunction U.ι
  let α := Scheme.Modules.restrictFunctorIsoPullback U.ι
  have hunit : adjL.unit.app F ≫ (Scheme.Modules.pushforward U.ι).map (α.hom.app F) =
      adjP.unit.app F := Adjunction.unit_leftAdjointUniq_hom_app _ _ F
  have : IsIso (adjL.unit.app F ≫ (Scheme.Modules.pushforward U.ι).map (α.hom.app F)) := by
    rw [hunit]
    exact isIso_unit_restrict_pushforward_of_depth_ge_two X F U hdepth
  have : IsIso (adjL.unit.app F) :=
    IsIso.of_isIso_comp_right _ ((Scheme.Modules.pushforward U.ι).map (α.hom.app F))
  let E := Scheme.Modules.toPresheaf X ⋙
    (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : X.Opens))
  have hb : Function.Bijective (ConcreteCategory.hom (E.map (adjL.unit.app F))) :=
    (ConcreteCategory.isIso_iff_bijective _).mp (by infer_instance)
  have htopcomp : ((Scheme.Modules.toPresheaf X).map (adjL.unit.app F)).app
      (op (⊤ : X.Opens)) ≫
      F.presheaf.map (eqToHom U.ι_image_top.symm).op =
        F.presheaf.map (homOfLE (show U ≤ (⊤ : X.Opens) from le_top)).op := by
    simp only [Scheme.Modules.toPresheaf_map, Scheme.Modules.mapPresheaf_app]
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    exact (F.presheaf.map_comp _ _).symm.trans (by congr 1)
  have hbEq : Function.Bijective (F.presheaf.map (eqToHom U.ι_image_top.symm).op) :=
    (ConcreteCategory.isIso_iff_bijective _).mp (by infer_instance)
  have hfun : ⇑(ConcreteCategory.hom (F.presheaf.map
      (homOfLE (show U ≤ (⊤ : X.Opens) from le_top)).op)) =
      ⇑(ConcreteCategory.hom (F.presheaf.map (eqToHom U.ι_image_top.symm).op)) ∘
        ⇑(ConcreteCategory.hom (((Scheme.Modules.toPresheaf X).map (adjL.unit.app F)).app
          (op (⊤ : X.Opens)))) := by
    rw [← htopcomp]
    exact CategoryTheory.hom_comp _ _
  exact hfun ▸ hbEq.comp hb

end AlgebraicGeometry

end
