module

public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.LocalityRingedSpace
public import StacksFrontier.AlgebraicGeometry.Descent.TrivialOnOpen0BF3
public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximationLocal

/-!
# A module trivial over a cover of the base, and along a section, is trivial

Let `p : P ⟶ S` be a morphism of schemes for which `𝒪_S ⟶ p_*𝒪_P` is an isomorphism, let `L` be a
sheaf of modules on `P`, and suppose every point of `S` has an open neighbourhood `U` such that `L`
is trivial over `P ×_S U`. Then `L` is the pullback of `p_*L`: the counit `p^*p_*L ⟶ L` is an
isomorphism. If moreover `L` is trivial along a section `δ` of `p`, then `L` is trivial, because
`p_*L ≅ δ^*p^*p_*L ≅ δ^*L`.

This is the last step of the proof of [Stacks, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4)
(the theorem of the cube): there the neighbourhoods are supplied by
[Stacks, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3), `𝒪_S = p_*𝒪_P` by
[Stacks, Tag 0E0L](https://stacks.math.columbia.edu/tag/0E0L), and the section is
`x × y × 1`.

## Main results

* `RingedSpaceModuleAdjunction.isIso_counit_app_of_isIso_structureSheafHom`: for a morphism of
  ringed spaces `f : X ⟶ Y` with `𝒪_Y ≅ f_*𝒪_X`, the counit `f^*f_*L ⟶ L` is invertible at every
  module `L` that is trivial over the preimage of each member of an open cover of `Y`.
* `AlgebraicGeometry.SheafOfModules.isTrivial_of_isTrivial_modulePullback_fst_ι`: the scheme
  statement: a module trivial over `P ×_S U` for a neighbourhood `U` of every point, and trivial
  along a section of `p`, is trivial.

## Implementation notes

No compatibility of the counit with restriction to an open is used. On `W = f⁻¹V` the counit at
`L` is compared with the counit at `𝒪_X`, which is invertible everywhere by the triangle identity
(the unit at `𝒪_Y` is `𝒪_Y ⟶ f_*𝒪_X`), through the two global morphisms
`L ⟶ j_*(L|_W) ≅ j_*(𝒪_X|_W) ⟵ 𝒪_X` along the inclusion `j : W ⟶ X`. Both become invertible on
`W`, and so do their images under `f^*f_*`
(`Stacks.AffineProjectionFormula.isIso_moduleRestriction_pushforward_map` and
`…pullback_map`), so the naturality square of the counit carries invertibility on `W` from
`𝒪_X` to `j_*(𝒪_X|_W)` and from there to `L`.

No invertibility of `L` is used.

## References

* [Stacks Project, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.HigherDirectImage Stacks.AffineProjectionFormula Stacks.RingedSpace

universe u

namespace RingedSpaceModuleAdjunction

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

/-- In a commutative square `f ≫ g = h ≫ k` with `f` and `k` invertible, `g` is invertible
iff `h` is. -/
private theorem isIso_iff_of_comp_eq_comp {C : Type*} [Category C] {A B A' B' : C} {f : A ⟶ B}
    {g : B ⟶ B'} {h : A ⟶ A'} {k : A' ⟶ B'} (w : f ≫ g = h ≫ k) [IsIso f] [IsIso k] :
    IsIso g ↔ IsIso h :=
  ⟨fun _ => IsIso.of_isIso_fac_right w.symm, fun _ => IsIso.of_isIso_fac_left w⟩

/-- **Invertibility of the restricted counit is transported along a morphism invertible on the
restriction.** If `k : A ⟶ B` becomes invertible on `f⁻¹V`, then the counit of `f^* ⊣ f_*` is
invertible on `f⁻¹V` at `A` exactly when it is at `B`: the naturality square of the counit, whose
other two sides `k` and `f^*f_*k` are invertible on `f⁻¹V`. -/
theorem isIso_moduleRestriction_counit_app_iff (V : Opens Y)
    {A B : SheafOfModules.{u} (structureSheafRing X)} (k : A ⟶ B)
    (hk : IsIso ((moduleRestriction X (preimageOpen f V)).map k)) :
    IsIso ((moduleRestriction X (preimageOpen f V)).map
        ((modulePullbackPushforwardAdjunction f).counit.app A)) ↔
      IsIso ((moduleRestriction X (preimageOpen f V)).map
        ((modulePullbackPushforwardAdjunction f).counit.app B)) := by
  have hpp : IsIso ((moduleRestriction X (preimageOpen f V)).map
      ((modulePullback f).map ((modulePushforward f).map k))) :=
    isIso_moduleRestriction_pullback_map f V _ (isIso_moduleRestriction_pushforward_map f V k hk)
  have hnat := congrArg (moduleRestriction X (preimageOpen f V)).map
    ((modulePullbackPushforwardAdjunction f).counit.naturality k)
  simp only [Functor.map_comp, Functor.comp_map, Functor.id_map] at hnat
  exact (isIso_iff_of_comp_eq_comp hnat).symm

/-- **The counit at the structure sheaf is invertible when `𝒪_Y ⟶ f_*𝒪_X` is.** The unit of
`f^* ⊣ f_*` at `𝒪_Y` is then invertible (`RingedSpaceModuleAdjunction.unit_app_unit`), so the
counit at `f^*𝒪_Y` is, by the triangle identity, and `f^*𝒪_Y ≅ 𝒪_X`. -/
theorem isIso_counit_app_unit_of_isIso_structureSheafHom
    (hO : IsIso (structureSheafHom f)) :
    IsIso ((modulePullbackPushforwardAdjunction f).counit.app
      (SheafOfModules.unit (structureSheafRing X))) := by
  have hmod : IsIso (structureSheafModuleHom f) :=
    Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit (structureSheafHom f)
  have hη : IsIso ((modulePullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit (structureSheafRing Y))) := by
    rw [unit_app_unit]
    infer_instance
  have htri := (modulePullbackPushforwardAdjunction f).left_triangle_components
    (SheafOfModules.unit (structureSheafRing Y))
  have hεF : IsIso ((modulePullbackPushforwardAdjunction f).counit.app
      ((modulePullback f).obj (SheafOfModules.unit (structureSheafRing Y)))) := by
    have : IsIso ((modulePullback f).map ((modulePullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit (structureSheafRing Y))) ≫
        (modulePullbackPushforwardAdjunction f).counit.app
          ((modulePullback f).obj (SheafOfModules.unit (structureSheafRing Y)))) := by
      rw [htri]
      infer_instance
    exact IsIso.of_isIso_comp_left ((modulePullback f).map
      ((modulePullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit (structureSheafRing Y)))) _
  have hnat := (modulePullbackPushforwardAdjunction f).counit.naturality
    (modulePullbackUnitIso f).hom
  simp only [Functor.comp_map, Functor.id_map] at hnat
  exact (isIso_iff_of_comp_eq_comp hnat).2 hεF

/-- **A module trivial over the preimage of each member of an open cover of the base is pulled
back from the base**, for a morphism of ringed spaces `f : X ⟶ Y` with `𝒪_Y ≅ f_*𝒪_X`: the counit
`f^*f_*L ⟶ L` is an isomorphism. -/
theorem isIso_counit_app_of_isIso_structureSheafHom (hO : IsIso (structureSheafHom f))
    {ι : Type*} (V : ι → Opens Y) (hV : iSup V = ⊤)
    (L : SheafOfModules.{u} (structureSheafRing X))
    (hL : ∀ i, Nonempty ((moduleRestriction X (preimageOpen f (V i))).obj L ≅
      (moduleRestriction X (preimageOpen f (V i))).obj
        (SheafOfModules.unit (structureSheafRing X)))) :
    IsIso ((modulePullbackPushforwardAdjunction f).counit.app L) := by
  have hεO := isIso_counit_app_unit_of_isIso_structureSheafHom f hO
  refine isIso_of_isIso_moduleRestriction X (fun i => preimageOpen f (V i)) ?_ _ fun i => ?_
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hV ▸ trivial : f.hom.base x ∈ iSup V)
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  · have h1 := isIso_moduleRestriction_moduleRestrictUnit X (preimageOpen f (V i)) L
    have h2 : IsIso ((moduleRestriction X (preimageOpen f (V i))).map
        ((pushforwardFunctor (openSubspaceInclusion X (preimageOpen f (V i)))).map
          (hL i).some.hom)) :=
      Functor.map_isIso _ _
    have hkL : IsIso ((moduleRestriction X (preimageOpen f (V i))).map
        (moduleRestrictUnit X (preimageOpen f (V i)) L ≫
          (pushforwardFunctor (openSubspaceInclusion X (preimageOpen f (V i)))).map
            (hL i).some.hom)) := by
      have hc := Functor.map_comp (moduleRestriction X (preimageOpen f (V i)))
        (moduleRestrictUnit X (preimageOpen f (V i)) L)
        ((pushforwardFunctor (openSubspaceInclusion X (preimageOpen f (V i)))).map
          (hL i).some.hom)
      exact hc ▸ IsIso.comp_isIso
    exact (isIso_moduleRestriction_counit_app_iff f (V i) _ hkL).2
      ((isIso_moduleRestriction_counit_app_iff f (V i) _
        (isIso_moduleRestriction_moduleRestrictUnit X (preimageOpen f (V i))
          (SheafOfModules.unit (structureSheafRing X)))).1 inferInstance)

end RingedSpaceModuleAdjunction

namespace AlgebraicGeometry.SheafOfModules

open RingedSpaceModuleAdjunction

/-- Triviality over `P ×_S U` gives triviality of the restriction to the open `p⁻¹U`, read as an
isomorphism of restrictions. The inclusion of `p⁻¹U` factors through `P ×_S U` by Mathlib's
`pullbackRestrictIsoRestrict`, and restriction is the pullback along the inclusion
(`Stacks.AffineProjectionFormula.moduleRestrictionIsoPullback`). -/
theorem nonempty_moduleRestriction_iso_of_isTrivial_modulePullback_fst_ι {S P : Scheme.{u}}
    (p : P ⟶ S) (U : S.Opens)
    (L : _root_.SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    (hU : IsTrivial (pullback p U.ι).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback p U.ι).IsSheaf)
      ((modulePullback (pullback.fst p U.ι).toLRSHom.toShHom).obj L)) :
    Nonempty ((moduleRestriction P.toRingedSpace (preimageOpen p.toLRSHom.toShHom U)).obj L ≅
      (moduleRestriction P.toRingedSpace (preimageOpen p.toLRSHom.toShHom U)).obj
        (_root_.SheafOfModules.unit (structureSheafRing P.toRingedSpace))) := by
  have hfac : (pullbackRestrictIsoRestrict p U).inv.toLRSHom.toShHom ≫
      (pullback.fst p U.ι).toLRSHom.toShHom =
      openSubspaceInclusion P.toRingedSpace (preimageOpen p.toLRSHom.toShHom U) := by
    change ((pullbackRestrictIsoRestrict p U).inv ≫ pullback.fst p U.ι).toLRSHom.toShHom = _
    rw [pullbackRestrictIsoRestrict_inv_fst]
    rfl
  have hj := isTrivial_modulePullback_of_comp _ _ _ hfac hU
  exact ⟨(moduleRestrictionIsoPullback _ _).app L ≪≫ hj.some ≪≫
    (modulePullbackUnitIso _).symm ≪≫ ((moduleRestrictionIsoPullback _ _).app _).symm⟩

/-- **A module trivial over `P ×_S U` for a neighbourhood `U` of every point of `S`, and trivial
along a section of `p`, is trivial**, when `𝒪_S ⟶ p_*𝒪_P` is an isomorphism.

The counit `p^*p_*L ⟶ L` is an isomorphism
(`RingedSpaceModuleAdjunction.isIso_counit_app_of_isIso_structureSheafHom`), so `L ≅ p^*N` with
`N = p_*L`; pulling back along the section `δ` identifies `N` with `δ^*L`, which is trivial, so
`L ≅ p^*𝒪_S ≅ 𝒪_P`. This is the final step of the proof of
[Stacks, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4). The invertibility of `L` is not
used. -/
theorem isTrivial_of_isTrivial_modulePullback_fst_ι {S P : Scheme.{u}} (p : P ⟶ S)
    (_hO : IsIso (structureSheafHom p.toLRSHom.toShHom))
    (δ : S ⟶ P) (_hδ : δ ≫ p = 𝟙 S)
    (L : _root_.SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    [IsInvertible P.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) P.IsSheaf) L]
    (_hδL : IsTrivial S.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) S.IsSheaf)
      ((modulePullback δ.toLRSHom.toShHom).obj L))
    (_hloc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      IsTrivial (pullback p U.ι).presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
          (pullback p U.ι).IsSheaf)
        ((modulePullback (pullback.fst p U.ι).toLRSHom.toShHom).obj L)) :
    IsTrivial P.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) P.IsSheaf) L := by
  choose U hsU hU using _hloc
  have hε := isIso_counit_app_of_isIso_structureSheafHom p.toLRSHom.toShHom _hO U
    (eq_top_iff.2 fun s _ => Opens.mem_iSup.2 ⟨s, hsU s⟩) L
    fun s => nonempty_moduleRestriction_iso_of_isTrivial_modulePullback_fst_ι p (U s) L (hU s)
  let N := (modulePushforward p.toLRSHom.toShHom).obj L
  let e : (modulePullback p.toLRSHom.toShHom).obj N ≅ L :=
    asIso ((modulePullbackPushforwardAdjunction p.toLRSHom.toShHom).counit.app L)
  -- `δ^*L ≅ δ^*p^*N ≅ (δ ≫ p)^*N = (𝟙 S)^*N ≅ N`.
  have hcomp : δ.toLRSHom.toShHom ≫ p.toLRSHom.toShHom = 𝟙 S.toRingedSpace := by
    change (δ ≫ p).toLRSHom.toShHom = _
    rw [_hδ]
    rfl
  have hN₁ : Nonempty ((modulePullback (δ.toLRSHom.toShHom ≫ p.toLRSHom.toShHom)).obj N ≅
      _root_.SheafOfModules.unit (structureSheafRing S.toRingedSpace)) :=
    ⟨(modulePullbackComp δ.toLRSHom.toShHom p.toLRSHom.toShHom).app N ≪≫
      (modulePullback δ.toLRSHom.toShHom).mapIso e ≪≫ _hδL.some⟩
  rw [hcomp] at hN₁
  exact ⟨e.symm ≪≫ (isTrivial_modulePullback p.toLRSHom.toShHom
    ⟨((modulePullbackId S.toRingedSpace).app N).symm ≪≫ hN₁.some⟩).some⟩

end AlgebraicGeometry.SheafOfModules

end
