module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.GlobalGeneration
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.MateComparison
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.ProperFibreDimensionNeighbourhood.Basic
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FirstDirectImageBaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafIsoNearSpecialFibreStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Transport of `𝒪_Y ≅ f_* 𝒪_X` along flat base change

For a cartesian square with flat bottom morphism `g` and quasi-compact quasi-separated `f`,
`𝒪_{Y'} ⟶ f'_* 𝒪_{X'}` is an isomorphism exactly when the pullback of `𝒪_Y ⟶ f_* 𝒪_X` along `g`
is ([Stacks, Tag 02KH] in degree zero), and pullback along a faithfully flat morphism reflects
isomorphisms and zero modules. These are the moves by which the special-fibre hypotheses of
[Stacks, Tag 0E7L] pass between the fibre over a point and the fibre over its image under a
morphism of bases, the residue field extension being faithfully flat.

## Main results

* `isIso_of_isIso_pullback_map`, `isZero_of_isZero_pullback_obj`: faithfully flat pullback
  reflects isomorphisms and zero modules.
* `isIso_unitToPushforwardUnit_iff_of_isPullback`: flat base change of `𝒪_Y ⟶ f_* 𝒪_X`.
* `isIso_unitToPushforwardUnit_of_isPullback`,
  `isIso_unitToPushforwardUnit_of_isPullback_of_surjective`: its two directions.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0E7L](https://stacks.math.columbia.edu/tag/0E7L)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 2000] HasDerivedCategory.standard

noncomputable section

section Stalkwise

variable {Y Y' : Scheme.{u}}

/-- A morphism of `𝒪_Y`-modules bijective on every stalk is an isomorphism. -/
theorem isIso_of_bijective_modulesStalkFunctor_map {M N : Y.Modules} (φ : M ⟶ N)
    (h : ∀ y : Y, Function.Bijective ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).map φ)) :
    IsIso φ :=
  (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap (O := Y.ringCatSheaf) φ).2 h

/-- An isomorphism of `𝒪_Y`-modules is bijective on every stalk. -/
theorem bijective_modulesStalkFunctor_map_of_isIso {M N : Y.Modules} (φ : M ⟶ N) [IsIso φ]
    (y : Y) : Function.Bijective ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).map φ) :=
  ConcreteCategory.bijective_of_isIso _

/-- The stalk at `y'` of the pullback of `φ` along `g` is the extension of scalars of the stalk
of `φ` at `g y'` ([Stacks, Tag 0098]); bijectivity of one is bijectivity of the other. -/
theorem bijective_modulesStalkFunctor_map_pullback_iff (g : Y' ⟶ Y) {M N : Y.Modules}
    (φ : M ⟶ N) (y' : Y') :
    Function.Bijective ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y' y').map
        ((Scheme.Modules.pullback g).map φ)) ↔
      Function.Bijective ((ModuleCat.extendScalars (g.stalkMap y').hom).map
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y (g y')).map φ)) := by
  have hnat := (Stacks.ModuleSkyscraper.pullbackStalkIso g y').hom.naturality φ
  have hM := ConcreteCategory.bijective_of_isIso
    ((Stacks.ModuleSkyscraper.pullbackStalkIso g y').app M).hom
  have hN := ConcreteCategory.bijective_of_isIso
    ((Stacks.ModuleSkyscraper.pullbackStalkIso g y').app N).hom
  rw [← Function.Bijective.of_comp_iff _ hM, ← Function.Bijective.of_comp_iff' hN]
  have h2 : ⇑((Stacks.ModuleSkyscraper.pullbackStalkIso g y').app N).hom ∘
      ⇑((ModuleCat.extendScalars (g.stalkMap y').hom).map
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y (g y')).map φ)) =
      ⇑((Stacks.ModuleSkyscraper.modulesStalkFunctor Y' y').map
        ((Scheme.Modules.pullback g).map φ)) ∘
      ⇑((Stacks.ModuleSkyscraper.pullbackStalkIso g y').app M).hom := by
    ext a
    exact congrArg (fun u => u a) hnat
  rw [h2]

/-- Stalkwise bijectivity passes to the pullback. -/
theorem bijective_modulesStalkFunctor_map_pullback (g : Y' ⟶ Y) {M N : Y.Modules}
    (φ : M ⟶ N) (y' : Y')
    (h : Function.Bijective ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y (g y')).map φ)) :
    Function.Bijective ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y' y').map
        ((Scheme.Modules.pullback g).map φ)) := by
  rw [bijective_modulesStalkFunctor_map_pullback_iff]
  have : IsIso ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y (g y')).map φ) :=
    (ConcreteCategory.isIso_iff_bijective _).2 h
  exact ConcreteCategory.bijective_of_isIso _

/-- Stalkwise bijectivity descends along a flat morphism, at the image point: a flat local
homomorphism of local rings is faithfully flat. -/
@[ega "IV 2.2.9" "special case"]
theorem bijective_modulesStalkFunctor_map_of_pullback (g : Y' ⟶ Y) {M N : Y.Modules}
    (φ : M ⟶ N) (y' : Y') (hg : (g.stalkMap y').hom.Flat)
    (h : Function.Bijective ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y' y').map
        ((Scheme.Modules.pullback g).map φ))) :
    Function.Bijective ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y (g y')).map φ) := by
  rw [bijective_modulesStalkFunctor_map_pullback_iff] at h
  let _ := (g.stalkMap y').hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (g y')) (Y'.presheaf.stalk y') := hg
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (g y')) (Y'.presheaf.stalk y')) :=
    inferInstanceAs (IsLocalHom (g.stalkMap y').hom)
  have : Module.FaithfullyFlat (Y.presheaf.stalk (g y')) (Y'.presheaf.stalk y') :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective (Y.presheaf.stalk (g y'))
    (Y'.presheaf.stalk y') ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y (g y')).map φ).hom).1
    (by rwa [← LinearMap.baseChange_eq_ltensor])

end Stalkwise

section Reflection

variable {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) [Flat g] [Surjective g]

/-- **Pullback along a faithfully flat morphism reflects isomorphisms of modules.** -/
theorem isIso_of_isIso_pullback_map {M N : Y.Modules} (φ : M ⟶ N)
    [IsIso ((Scheme.Modules.pullback g).map φ)] : IsIso φ :=
  isIso_of_bijective_modulesStalkFunctor_map φ fun y => by
    obtain ⟨y', rfl⟩ := g.surjective y
    exact bijective_modulesStalkFunctor_map_of_pullback g φ y' (Flat.stalkMap g y')
      (bijective_modulesStalkFunctor_map_of_isIso _ y')

/-- **Pullback along a faithfully flat morphism reflects the zero module.** -/
theorem isZero_of_isZero_pullback_obj (M : Y.Modules)
    (h : IsZero ((Scheme.Modules.pullback g).obj M)) : IsZero M := by
  refine isZero_of_forall_isZero_stalk M fun y => ?_
  obtain ⟨y', rfl⟩ := g.surjective y
  let _ := (g.stalkMap y').hom.toAlgebra
  have : Module.FaithfullyFlat (Y.presheaf.stalk (g y')) (Y'.presheaf.stalk y') :=
    Stacks.AlgebraicGeometry.FlatBaseChange.faithfullyFlat_stalkMap g y'
  have h1 : IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y' y').obj
      ((Scheme.Modules.pullback g).obj M)) :=
    (Stacks.ModuleSkyscraper.modulesStalkFunctor Y' y').map_isZero h
  have h2 : IsZero ((ModuleCat.extendScalars (g.stalkMap y').hom).obj
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y (g y')).obj M)) :=
    IsZero.of_iso h1 ((Stacks.ModuleSkyscraper.pullbackStalkIso g y').app M)
  have h3 : Subsingleton ((Y'.presheaf.stalk y') ⊗[Y.presheaf.stalk (g y')]
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y (g y')).obj M)) :=
    ModuleCat.subsingleton_of_isZero h2
  exact AddCommGrpCat.isZero_iff_subsingleton.mpr
    ((Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right
      (R := Y.presheaf.stalk (g y')) (M := Y'.presheaf.stalk y')).1 h3)

end Reflection

section BaseChange

variable {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}

/-- The degree-zero base-change comparison at `𝒪_X` is invertible along a flat morphism
([Stacks, Tag 02KH]). -/
private theorem isIso_pushforwardBaseChange_unit_of_flat_aux (H : IsPullback g' f' f g) [Flat g]
    [QuasiCompact f] [QuasiSeparated f] :
    IsIso (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange H.w
      (Scheme.unitModule X)) := by
  rw [← Stacks.AlgebraicGeometry.FlatBaseChange.baseChangeNatTrans_app_eq_pushforwardBaseChange]
  exact Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat H _

/-- **Flat base change of `𝒪_Y ⟶ f_* 𝒪_X`.** For a cartesian square with `g` flat and `f`
quasi-compact and quasi-separated, `𝒪_{Y'} ⟶ f'_* 𝒪_{X'}` is an isomorphism exactly when the
pullback along `g` of `𝒪_Y ⟶ f_* 𝒪_X` is: the degree-zero base-change comparison is invertible
(Tag 02KH) and compatible with the two canonical maps. -/
theorem isIso_unitToPushforwardUnit_iff_of_isPullback (H : IsPullback g' f' f g) [Flat g]
    [QuasiCompact f] [QuasiSeparated f] :
    IsIso (Scheme.Modules.unitToPushforwardUnit f') ↔
      IsIso ((Scheme.Modules.pullback g).map (Scheme.Modules.unitToPushforwardUnit f)) := by
  have hbc := isIso_pushforwardBaseChange_unit_of_flat_aux H
  have hc := unitToPushforwardUnit_comp_pushforwardBaseChange H.w
  constructor
  · intro h
    have : IsIso ((Scheme.Modules.pullback g).map (Scheme.Modules.unitToPushforwardUnit f) ≫
        Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange H.w
          (Scheme.unitModule X)) := by
      rw [← hc]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange H.w (Scheme.unitModule X))
  · intro h
    have : IsIso ((Scheme.Modules.pullbackUnitIso g).hom ≫
        Scheme.Modules.unitToPushforwardUnit f' ≫ (Scheme.Modules.pushforward f').map
          (Scheme.Modules.pullbackUnitIso g').inv) := by
      rw [hc]
      infer_instance
    have : IsIso (Scheme.Modules.unitToPushforwardUnit f' ≫
        (Scheme.Modules.pushforward f').map (Scheme.Modules.pullbackUnitIso g').inv) :=
      IsIso.of_isIso_comp_left (Scheme.Modules.pullbackUnitIso g).hom _
    exact IsIso.of_isIso_comp_right _ ((Scheme.Modules.pushforward f').map
      (Scheme.Modules.pullbackUnitIso g').inv)

/-- `𝒪_Y ⟶ f_* 𝒪_X` an isomorphism passes to a flat base change. -/
theorem isIso_unitToPushforwardUnit_of_isPullback (H : IsPullback g' f' f g) [Flat g]
    [QuasiCompact f] [QuasiSeparated f] [IsIso (Scheme.Modules.unitToPushforwardUnit f)] :
    IsIso (Scheme.Modules.unitToPushforwardUnit f') :=
  (isIso_unitToPushforwardUnit_iff_of_isPullback H).2 inferInstance

/-- `𝒪_Y ⟶ f_* 𝒪_X` an isomorphism descends along a faithfully flat base change. -/
theorem isIso_unitToPushforwardUnit_of_isPullback_of_surjective (H : IsPullback g' f' f g)
    [Flat g] [Surjective g] [QuasiCompact f] [QuasiSeparated f]
    [IsIso (Scheme.Modules.unitToPushforwardUnit f')] :
    IsIso (Scheme.Modules.unitToPushforwardUnit f) :=
  have := (isIso_unitToPushforwardUnit_iff_of_isPullback H).1 inferInstance
  isIso_of_isIso_pullback_map g _

/-- **Stalkwise form of the transport of `𝒪 ⟶ f_* 𝒪` along a base change**, granted that the
degree-zero base-change comparison is invertible (for instance because `g` is flat, or by
[Stacks, Tag 0E7K]): `𝒪_{Y'} ⟶ f'_* 𝒪_{X'}` is bijective on the stalk at `y'` exactly when the
pullback of `𝒪_Y ⟶ f_* 𝒪_X` is. -/
theorem bijective_stalk_unitToPushforwardUnit_iff_of_isPullback (H : IsPullback g' f' f g)
    [IsIso (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange H.w
      (Scheme.unitModule X))] (y' : Y') :
    Function.Bijective ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y' y').map
        (Scheme.Modules.unitToPushforwardUnit f')) ↔
      Function.Bijective ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y' y').map
        ((Scheme.Modules.pullback g).map (Scheme.Modules.unitToPushforwardUnit f))) := by
  have hc := congrArg (Stacks.ModuleSkyscraper.modulesStalkFunctor Y' y').map
    (unitToPushforwardUnit_comp_pushforwardBaseChange H.w)
  simp only [Functor.map_comp] at hc
  have hA := bijective_modulesStalkFunctor_map_of_isIso (Scheme.Modules.pullbackUnitIso g).hom y'
  have hB := bijective_modulesStalkFunctor_map_of_isIso
    ((Scheme.Modules.pushforward f').map (Scheme.Modules.pullbackUnitIso g').inv) y'
  have hC := bijective_modulesStalkFunctor_map_of_isIso
    (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange H.w (Scheme.unitModule X)) y'
  have key : ∀ {A B C D : ModuleCat.{u} (Y'.presheaf.stalk y')} (a : A ⟶ B) (b : B ⟶ C)
      (c : C ⟶ D) (d : A ⟶ D), a ≫ b ≫ c = d → Function.Bijective a → Function.Bijective c →
        (Function.Bijective b ↔ Function.Bijective d) := by
    intro A B C D a b c d h ha hc
    have hd : ⇑(ConcreteCategory.hom d) =
        ⇑(ConcreteCategory.hom c) ∘ ⇑(ConcreteCategory.hom b) ∘ ⇑(ConcreteCategory.hom a) := by
      rw [← h]
      funext x
      simp
    rw [hd]
    exact ⟨fun hb => (hc.comp hb).comp ha, fun hd => (Function.Bijective.of_comp_iff' hc _).1
      ((Function.Bijective.of_comp_iff (⇑(ConcreteCategory.hom c) ∘ ⇑(ConcreteCategory.hom b))
        ha).1 hd)⟩
  rw [key _ _ _ _ hc hA hB]
  exact (key (𝟙 _) _ _ _ (by simp) (ConcreteCategory.bijective_of_isIso _) hC).symm

/-- The vanishing of `H²` over the affine opens of the target, for a proper morphism whose
fibres have dimension at most one ([Stacks, Tag 0E7D]); the hypothesis under which
`isZero_pullback_firstDirectImage_iff_of_isPullback` transports `R¹f_* 𝒪_X = 0`. -/
theorem isZero_cohomology_two_of_fibreDimension_le_one (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (U : Y.Opens) (hU : IsAffineOpen U) (G : (f ⁻¹ᵁ U).toScheme.Modules)
    (hG : G.IsQuasicoherent) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections
      (f ⁻¹ᵁ U).toScheme).rightDerivedPlus 2).obj G) := by
  have _ : IsAffine U.toScheme := hU
  have _ : G.IsQuasicoherent := hG
  exact isZero_cohomology_of_affine_base (d := 1) (f ∣_ U)
    (topologicalKrullDim_fiber_morphismRestrict_le f U 1 fun t _ => hdim t) G 2 (by norm_num)

/-- **The special-fibre hypotheses of [Stacks, Tag 0E7L] pass to a flat base change.** For a
cartesian square with `k` flat and `f` proper with fibres of dimension at most one,
`R¹f_* 𝒪 = 0` and `𝒪 ≅ f_* 𝒪` pass from `f` to its base change `f'`. -/
theorem isZero_and_isIso_of_isPullback (H : IsPullback g' f' f g) [Flat g] [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf f))
    (hU : IsIso (Scheme.Modules.unitToPushforwardUnit f)) :
    IsZero (firstDirectImageStructureSheaf f') ∧
      IsIso (Scheme.Modules.unitToPushforwardUnit f') :=
  ⟨(isZero_pullback_firstDirectImage_iff_of_isPullback H
      (isZero_cohomology_two_of_fibreDimension_le_one f hdim)).1 (Functor.map_isZero _ hR),
    isIso_unitToPushforwardUnit_of_isPullback H⟩

/-- **The special-fibre hypotheses of [Stacks, Tag 0E7L] descend along a faithfully flat base
change.** -/
theorem isZero_and_isIso_of_isPullback_of_surjective (H : IsPullback g' f' f g) [Flat g]
    [Surjective g] [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf f'))
    (hU : IsIso (Scheme.Modules.unitToPushforwardUnit f')) :
    IsZero (firstDirectImageStructureSheaf f) ∧
      IsIso (Scheme.Modules.unitToPushforwardUnit f) :=
  ⟨isZero_of_isZero_pullback_obj g _ ((isZero_pullback_firstDirectImage_iff_of_isPullback H
      (isZero_cohomology_two_of_fibreDimension_le_one f hdim)).2 hR),
    isIso_unitToPushforwardUnit_of_isPullback_of_surjective H⟩

/-- The degree-zero base-change comparison at `𝒪_X` is invertible along a flat morphism
([Stacks, Tag 02KH]). -/
theorem isIso_pushforwardBaseChange_unit_of_flat (H : IsPullback g' f' f g) [Flat g]
    [QuasiCompact f] [QuasiSeparated f] :
    IsIso (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange H.w
      (Scheme.unitModule X)) :=
  isIso_pushforwardBaseChange_unit_of_flat_aux H

/-- Bijectivity of `𝒪 ⟶ f_* 𝒪` on a stalk passes up a flat base change. -/
theorem bijective_stalk_unitToPushforwardUnit_of_isPullback (H : IsPullback g' f' f g) [Flat g]
    [QuasiCompact f] [QuasiSeparated f] (y' : Y')
    (h : Function.Bijective ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y (g y')).map
      (Scheme.Modules.unitToPushforwardUnit f))) :
    Function.Bijective ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y' y').map
      (Scheme.Modules.unitToPushforwardUnit f')) := by
  have := isIso_pushforwardBaseChange_unit_of_flat H
  exact (bijective_stalk_unitToPushforwardUnit_iff_of_isPullback H y').2
    (bijective_modulesStalkFunctor_map_pullback g _ y' h)

/-- Bijectivity of `𝒪 ⟶ f_* 𝒪` on a stalk descends along a flat base change, to the image
point. -/
theorem bijective_stalk_unitToPushforwardUnit_of_isPullback' (H : IsPullback g' f' f g) [Flat g]
    [QuasiCompact f] [QuasiSeparated f] (y' : Y')
    (h : Function.Bijective ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y' y').map
      (Scheme.Modules.unitToPushforwardUnit f'))) :
    Function.Bijective ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y (g y')).map
      (Scheme.Modules.unitToPushforwardUnit f)) := by
  have := isIso_pushforwardBaseChange_unit_of_flat H
  exact bijective_modulesStalkFunctor_map_of_pullback g _ y' (Flat.stalkMap g y')
    ((bijective_stalk_unitToPushforwardUnit_iff_of_isPullback H y').1 h)

/-- **A fibre-dimension bound descends along a base change, one fibre at a time.** In a fibre
product square, the fibre of `f` over `g y'` has dimension at most that of the fibre of the
base change over `y'`: every point of the former lifts to the latter, and local fibre dimension
is invariant ([Stacks, Tag 02FY]). -/
theorem topologicalKrullDim_fiber_le_of_isPullback' (H : IsPullback g' f' f g)
    [LocallyOfFiniteType f] (d : ℕ) (y' : Y')
    (hdim : topologicalKrullDim (f'.fiber y') ≤ (d : WithBot ℕ∞)) :
    topologicalKrullDim (f.fiber (g y')) ≤ (d : WithBot ℕ∞) := by
  refine ProperFibreDimension.topologicalKrullDim_fiber_le_of_forall f (g y') d fun x hx => ?_
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x y' hx
  set x' := H.isoPullback.inv z
  have h1 : g' x' = x := by
    simp only [x', ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz1]
  have h2 : f' x' = y' := by
    simp only [x', ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hz2]
  have heq := topologicalKrullDimAt_fiber_eq_of_isPullback H x'
  rw [h1] at heq
  rw [← heq]
  exact ProperFibreDimension.topologicalKrullDimAt_asFiber_le f' h2 d hdim

/-- **A base change of a base change, over a factorization of the bottom morphism.** If `v`
is the base change of `f` along `g` and `k : B' ⟶ B`, then the base change of `f` along `k ≫ g`
is the base change of `v` along `k`. -/
theorem exists_isPullback_pullback_snd_comp {A B B' : Scheme.{u}} {c : A ⟶ X} {v : A ⟶ B}
    {g : B ⟶ Y} (H : IsPullback c v f g) (k : B' ⟶ B) :
    ∃ k' : pullback f (k ≫ g) ⟶ A, IsPullback k' (pullback.snd f (k ≫ g)) v k :=
  ⟨_, IsPullback.of_right' (IsPullback.of_hasPullback f (k ≫ g)) H⟩

end BaseChange

section Fibres

variable {X Y S P : Scheme.{u}}

/-- A fibre product is unchanged by composing both legs with the same monomorphism. -/
theorem isPullback_comp_mono {A B C D : Scheme.{u}} (a : A ⟶ C) (b : B ⟶ C) (m : C ⟶ D)
    [Mono m] : IsPullback (pullback.fst a b) (pullback.snd a b) (a ≫ m) (b ≫ m) := by
  have h2 : IsPullback (𝟙 A) a (a ≫ m) m := IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  simpa using (IsPullback.of_hasPullback a b).paste_horiz h2

/-- The base change of `f ∣_ V` along `a : A ⟶ V` is a base change of the base change of `f` along
`b : C ⟶ Y`, along a flat morphism `k`, when `a, k, V.ι, b` form a pullback square. -/
private theorem flat_and_exists_isPullback_morphismRestrict {A C : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (a : A ⟶ V.toScheme) (b : C ⟶ Y) (k : A ⟶ C) (hsq : IsPullback a k V.ι b) :
    Flat k ∧ ∃ k', IsPullback k' (pullback.snd (f ∣_ V) a) (pullback.snd f b) k := by
  have hout := (IsPullback.of_hasPullback (f ∣_ V) a).paste_horiz
    (isPullback_morphismRestrict f V).flip
  rw [hsq.w] at hout
  exact ⟨MorphismProperty.of_isPullback hsq inferInstance, _,
    IsPullback.of_right' hout (IsPullback.of_hasPullback f b)⟩

/-- **The fibre of a restriction over opens of the target and of the base.** Let `f : X ⟶ Y`,
`q : Y ⟶ S`, `V ⊆ Y` and `S₁ ⊆ S` open with `qV : V ⟶ S₁` and `qV ≫ S₁.ι = V.ι ≫ q`, and let
`t₁ : P ⟶ S₁`. Then the base change of `f ∣_ V` along `V ×_{S₁} P ⟶ V` is the base change of
the base change of `f` along `Y ×_S P ⟶ Y` along a flat morphism `V ×_{S₁} P ⟶ Y ×_S P`. -/
theorem exists_isPullback_fibre_morphismRestrict (f : X ⟶ Y) (q : Y ⟶ S) (V : Y.Opens)
    (S₁ : S.Opens) (qV : V.toScheme ⟶ S₁.toScheme) (hqV : qV ≫ S₁.ι = V.ι ≫ q)
    (t₁ : P ⟶ S₁.toScheme) :
    ∃ (k : pullback qV t₁ ⟶ pullback q (t₁ ≫ S₁.ι))
      (k' : pullback (f ∣_ V) (pullback.fst qV t₁) ⟶ pullback f (pullback.fst q (t₁ ≫ S₁.ι))),
      Flat k ∧ IsPullback k' (pullback.snd (f ∣_ V) (pullback.fst qV t₁))
        (pullback.snd f (pullback.fst q (t₁ ≫ S₁.ι))) k := by
  set t := t₁ ≫ S₁.ι
  let k : pullback qV t₁ ⟶ pullback q t :=
    pullback.map qV t₁ q t V.ι (𝟙 P) S₁.ι hqV (by simp [t])
  have hk : k ≫ pullback.fst q t = pullback.fst qV t₁ ≫ V.ι := pullback.lift_fst _ _ _
  have hksnd : k ≫ pullback.snd q t = pullback.snd qV t₁ :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hsq : IsPullback (pullback.fst qV t₁) k V.ι (pullback.fst q t) := by
    refine IsPullback.of_bot ?_ hk.symm (IsPullback.of_hasPullback q t)
    rw [hksnd, ← hqV]
    exact isPullback_comp_mono qV t₁ S₁.ι
  obtain ⟨hf, k', h⟩ := flat_and_exists_isPullback_morphismRestrict f V _ _ k hsq
  exact ⟨k, k', hf, h⟩

/-- **The fibre of a restriction over an open of the target.** For `f : X ⟶ Y`, `q : Y ⟶ S`, an
open `V ⊆ Y` and `t : P ⟶ S`, the base change of `f ∣_ V` along `V ×_S P ⟶ V` is the base change
of the base change of `f` along `Y ×_S P ⟶ Y` along the open immersion `V ×_S P ⟶ Y ×_S P`. -/
theorem exists_isPullback_fibre_morphismRestrict' (f : X ⟶ Y) (q : Y ⟶ S) (t : P ⟶ S)
    (V : Y.Opens) :
    ∃ (k : pullback (V.ι ≫ q) t ⟶ pullback q t)
      (k' : pullback (f ∣_ V) (pullback.fst (V.ι ≫ q) t) ⟶ pullback f (pullback.fst q t)),
      Flat k ∧ IsPullback k' (pullback.snd (f ∣_ V) (pullback.fst (V.ι ≫ q) t))
        (pullback.snd f (pullback.fst q t)) k := by
  let k : pullback (V.ι ≫ q) t ⟶ pullback q t :=
    pullback.map (V.ι ≫ q) t q t V.ι (𝟙 P) (𝟙 S) (by simp) (by simp)
  have hk : k ≫ pullback.fst q t = pullback.fst (V.ι ≫ q) t ≫ V.ι := pullback.lift_fst _ _ _
  have hksnd : k ≫ pullback.snd q t = pullback.snd (V.ι ≫ q) t :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hsq : IsPullback (pullback.fst (V.ι ≫ q) t) k V.ι (pullback.fst q t) := by
    refine IsPullback.of_bot ?_ hk.symm (IsPullback.of_hasPullback q t)
    rw [hksnd]
    exact IsPullback.of_hasPullback (V.ι ≫ q) t
  obtain ⟨hf, k', h⟩ := flat_and_exists_isPullback_morphismRestrict f V _ _ k hsq
  exact ⟨k, k', hf, h⟩

/-- **Fibres over points of a model.** Let `X ⟶ Y ⟶ S` be the base change of
`X₀ ⟶ Y₀ ⟶ S₀` along `π : S ⟶ S₀`, and let `t : P ⟶ S`, `t₀ : P₀ ⟶ S₀`, `e : P ⟶ P₀` with
`t ≫ π = e ≫ t₀`. Then the fibre of `X ⟶ Y` over `t` is the base change of the fibre of
`X₀ ⟶ Y₀` over `t₀` along the base change of `e`. -/
theorem exists_isPullback_fibre_of_model {X₀ Y₀ S₀ P₀ : Scheme.{u}} {q : Y ⟶ S} {q₀ : Y₀ ⟶ S₀}
    {f : X ⟶ Y} {f₀ : X₀ ⟶ Y₀} {π : S ⟶ S₀} {πY : Y ⟶ Y₀} {πX : X ⟶ X₀}
    (hY : IsPullback πY q q₀ π) (hX : IsPullback πX f f₀ πY) (t : P ⟶ S) (t₀ : P₀ ⟶ S₀)
    (e : P ⟶ P₀) (he : t ≫ π = e ≫ t₀) :
    ∃ (a : pullback q t ⟶ pullback q₀ t₀)
      (b : pullback f (pullback.fst q t) ⟶ pullback f₀ (pullback.fst q₀ t₀)),
      IsPullback a (pullback.snd q t) (pullback.snd q₀ t₀) e ∧
      IsPullback b (pullback.snd f (pullback.fst q t))
        (pullback.snd f₀ (pullback.fst q₀ t₀)) a := by
  have h1 := (IsPullback.of_hasPullback q t).paste_horiz hY
  rw [he] at h1
  have ha := IsPullback.of_right' h1 (IsPullback.of_hasPullback q₀ t₀)
  set a := (IsPullback.of_hasPullback q₀ t₀).lift (pullback.fst q t ≫ πY)
    (pullback.snd q t ≫ e) (by rw [h1.w, Category.assoc])
  have hfa : pullback.fst q t ≫ πY = a ≫ pullback.fst q₀ t₀ :=
    ((IsPullback.of_hasPullback q₀ t₀).lift_fst _ _ _).symm
  have h2 := (IsPullback.of_hasPullback f (pullback.fst q t)).paste_horiz hX
  rw [hfa] at h2
  exact ⟨a, _, ha, IsPullback.of_right' h2 (IsPullback.of_hasPullback f₀ (pullback.fst q₀ t₀))⟩

end Fibres

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange
