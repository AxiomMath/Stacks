module

public import StacksFrontier.AlgebraicGeometry.Thickenings.TransitivityConormal
public import StacksFrontier.AlgebraicGeometry.Conormal.RestrictSquareMap
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersectionAffine
public import StacksFrontier.AlgebraicGeometry.Modules.MonoRestrictLocality
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularSchemes
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FormallyUnramifiedDiagonal
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.AffineSpaceImmersion
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.ConormalSequence
public import StacksFrontier.AlgebraicGeometry.Thickenings.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Thickenings.InfinitesimalConormalSheaf
public import StacksFrontier.AlgebraicGeometry.Thickenings.InfinitesimalUniversal
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.CategoryTheory.Functor.NatIsoMonoEpi
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Short exactness of the conormal sequence of a local complete intersection

Let `Z --i--→ Y --p--→ X` be morphisms of schemes, let `Z ⊂ Z'` be a universal first-order
thickening of `Z` over `X` and `Y ⊂ Y'` one of `Y` over `X`. Part (2) of
[Stacks Project, Tag 06AE], proved in
`StacksFrontier.AlgebraicGeometry.Thickenings.TransitivityConormal`, gives the canonical sequence
```
i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0
```
and its exactness at the middle and right-hand terms. [Stacks Project, Tag 06BA] adds that when
`i` is a local complete intersection morphism the sequence is **short exact**, that is, the
left-hand arrow is a monomorphism as well.

## Main results

* `Stacks.Thickenings.mono_transitivityConormalLeftMap` is the content [Stacks Project, Tag 06BA]
  adds to part (2) of [Stacks Project, Tag 06AE]: the first arrow
  `Stacks.Thickenings.transitivityConormalLeftMap` is a monomorphism.
* `Stacks.Thickenings.transitivityConormalShortComplex_shortExact` is
  [Stacks Project, Tag 06BA]: the short complex
  `Stacks.Thickenings.transitivityConormalShortComplex` is
  `CategoryTheory.ShortComplex.ShortExact`.

## References

* [Stacks Project, Tag 06BA](https://stacks.math.columbia.edu/tag/06BA)
* [Stacks Project, Tag 06AE](https://stacks.math.columbia.edu/tag/06AE)
* [Stacks Project, Tag 063N](https://stacks.math.columbia.edu/tag/063N)
* [Stacks Project, Tag 069G](https://stacks.math.columbia.edu/tag/069G)
* [Stacks Project, Tag 04F0](https://stacks.math.columbia.edu/tag/04F0)
* [Stacks Project, Tag 04F9](https://stacks.math.columbia.edu/tag/04F9)
* [Stacks Project, Tag 04II](https://stacks.math.columbia.edu/tag/04II)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.ClosedImmersion Stacks.Immersion
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Thickenings

/-! ### Generalities -/

/-- Pullback along the identity preserves monomorphisms. -/
private theorem mono_modulePullbackId_map {W : RingedSpace.{u, u}}
    {M N : SheafOfModules.{u} (structureSheafRing W)} (f : M ⟶ N) (h : Mono f) :
    Mono ((modulePullback (𝟙 W)).map f) :=
  (NatIso.mono_map_iff (modulePullbackId W) f).2 h

/-- The first factor of a monomorphic composite is a monomorphism. -/
private theorem mono_of_mono_comp {C : Type*} [Category C] {A B D : C} (a : A ⟶ B) (b : B ⟶ D)
    (h : Mono (a ≫ b)) : Mono a :=
  mono_of_mono a b

/-- **The components of a natural isomorphism are isomorphisms.** -/
private theorem isIso_natIso_hom_app {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) (A : C) : IsIso (e.hom.app A) :=
  ⟨e.inv.app A, e.hom_inv_id_app A, e.inv_hom_id_app A⟩

/-- A monomorphism preceded by a component of a natural isomorphism is a monomorphism. -/
private theorem mono_natIsoApp_comp {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) (A : C) {B : D} {b : G.obj A ⟶ B} (h : Mono b) : Mono (e.hom.app A ≫ b) := by
  have := isIso_natIso_hom_app e A
  infer_instance

/-- The second factor of a monomorphic composite whose first factor is a component of a natural
isomorphism is a monomorphism. -/
private theorem mono_of_mono_natIsoApp_comp {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) (A : C) {B : D} (b : G.obj A ⟶ B) (h : Mono (e.hom.app A ≫ b)) : Mono b := by
  have := isIso_natIso_hom_app e A
  have h' : Mono (inv (e.hom.app A) ≫ e.hom.app A ≫ b) := inferInstance
  rwa [IsIso.inv_hom_id_assoc] at h'

/-- **Two morphisms into the ambient scheme of a universal first-order thickening agree** when
they restrict to the same morphism on the closed subscheme and lie over the same morphism to the
base. -/
private theorem universalThickening_lift_ext {T T' W V : Scheme.{u}} {h : W ⟶ V}
    (t : UniversalFirstOrderThickening h) {jj : T ⟶ T'} (hj : IsFirstOrderThickening jj)
    (a : T ⟶ W) (b : T' ⟶ V) (hab : jj ≫ b = a ≫ h) (f g : T' ⟶ t.ambient)
    (hf : jj ≫ f = a ≫ t.inclusion) (hf' : f ≫ t.toBase = b)
    (hg : jj ≫ g = a ≫ t.inclusion) (hg' : g ≫ t.toBase = b) : f = g :=
  (t.isUniversal.existsUnique_lift jj hj a b hab).unique ⟨hf, hf'⟩ ⟨hg, hg'⟩

/-! ### The local step -/

variable {Z Y X : Scheme.{u}} (i : Z ⟶ Y) (p : Y ⟶ X)
  (tZ : UniversalFirstOrderThickening (i ≫ p)) (tY : UniversalFirstOrderThickening p)

/-- **The first arrow of the conormal sequence of part (2) of [Stacks Project, Tag 06AE] is a
monomorphism after pullback along a morphism that factors through an `H₁`-regular immersion into
a flat base change.** -/
@[sga "6 VIII 2.6" "partial"]
private theorem mono_modulePullback_transitivityConormalLeftMap
    {U PY PX : Scheme.{u}} (j : U ⟶ Z) {π : PY ⟶ Y} {q : PX ⟶ X} {r : PY ⟶ PX} [Flat q]
    (sq : IsPullback r π q p) (t : UniversalFirstOrderThickening r)
    (k : U ⟶ PY) [IsImmersion k] (hkH1 : IsH1RegularImmersion k) (hki : k ≫ π = j ≫ i) :
    Mono ((modulePullback j.toLRSHom.toShHom).map (transitivityConormalLeftMap i p tZ tY)) := by
  have himm : IsImmersion (k ≫ t.inclusion) := inferInstance
  set m : U ⟶ t.ambient := k ≫ t.inclusion with hmdef
  set nI := nthOrderInclusion m 1 with hnIdef
  set nT := nthOrderToBase m 1 with hnTdef
  have hcomm₁ : nI ≫ nT = 𝟙 U ≫ m := nthOrderSquare m
  have hNS' : nI ≫ nT = m := by rw [hcomm₁, Category.id_comp]
  have hFO : IsFirstOrderThickening nI :=
    (isUniversalFirstOrderThickening_nthOrderInclusion_one m).isFirstOrderThickening
  have hcomm₂ : m ≫ 𝟙 t.ambient = k ≫ t.inclusion := by rw [Category.comp_id, hmdef]
  have hcommΘ : nI ≫ nT = k ≫ t.inclusion := by rw [hNS', hmdef]
  set b₀ := universalFirstOrderThickeningMap t tY π q sq.w with hb₀def
  have hb₀ : t.inclusion ≫ b₀ = π ≫ tY.inclusion :=
    universalFirstOrderThickeningMap_inclusion t tY π q sq.w
  have hb₀' : b₀ ≫ tY.toBase = t.toBase ≫ q :=
    universalFirstOrderThickeningMap_toBase t tY π q sq.w
  have h04F0 : IsIso (immersionConormalSheafMap nI m (𝟙 U) nT (toShHom_square hcomm₁)) :=
    isIso_infinitesimalImmersionConormalSheafMap m
  have h063N : Mono (immersionConormalSheafMap m t.inclusion k (𝟙 t.ambient)
      (toShHom_square hcomm₂)) :=
    mono_conormalLeftMap k t.inclusion hkH1
  have hstep1 : Mono (immersionConormalSheafMap nI t.inclusion (𝟙 U ≫ k) (nT ≫ 𝟙 t.ambient)
      (toShHom_square (square_comp hcomm₁ hcomm₂))) := by
    rw [immersionConormalSheafMap_comp nI m t.inclusion (𝟙 U) nT hcomm₁ k (𝟙 t.ambient) hcomm₂]
    refine mono_natIsoApp_comp _ _ ?_
    have hpb : Mono ((modulePullback (𝟙 U : U ⟶ U).toLRSHom.toShHom).map
        (immersionConormalSheafMap m t.inclusion k (𝟙 t.ambient) (toShHom_square hcomm₂))) :=
      mono_modulePullbackId_map _ h063N
    infer_instance
  have hΘ : Mono (immersionConormalSheafMap nI t.inclusion k nT (toShHom_square hcommΘ)) := by
    rw [immersionConormalSheafMap_congr nI t.inclusion (Category.id_comp k)
      (Category.comp_id nT) (toShHom_square (square_comp hcomm₁ hcomm₂))
      (toShHom_square hcommΘ)]
    infer_instance
  have h04F9 : IsIso (immersionConormalSheafMap t.inclusion tY.inclusion π b₀
      (toShHom_square hb₀)) :=
    isIso_immersionConormalSheafMap_of_isPullback_of_flat t sq tY
  have hΨ : Mono (immersionConormalSheafMap nI tY.inclusion (k ≫ π) (nT ≫ b₀)
      (toShHom_square (square_comp hcommΘ hb₀))) := by
    rw [immersionConormalSheafMap_comp nI t.inclusion tY.inclusion k nT hcommΘ π b₀ hb₀]
    refine mono_natIsoApp_comp _ _ ?_
    have hpb : IsIso ((modulePullback k.toLRSHom.toShHom).map
        (immersionConormalSheafMap t.inclusion tY.inclusion π b₀ (toShHom_square hb₀))) :=
      inferInstance
    infer_instance
  have hsq : nI ≫ (nT ≫ t.toBase ≫ q) = j ≫ (i ≫ p) := by
    rw [← Category.assoc, hNS', hmdef, Category.assoc,
      ← Category.assoc t.inclusion t.toBase q, t.isUniversal.inclusion_toBase, sq.w,
      ← Category.assoc, hki, Category.assoc]
  obtain ⟨a₀, ⟨ha₀, ha₀'⟩, -⟩ :=
    tZ.isUniversal.existsUnique_lift nI hFO j (nT ≫ t.toBase ≫ q) hsq
  have htm : tZ.inclusion ≫ transitivityMap i p tZ tY = i ≫ tY.inclusion :=
    (inclusion_comp_transitivityMap i p tZ tY).symm
  have htri : nT ≫ b₀ = a₀ ≫ transitivityMap i p tZ tY := by
    refine universalThickening_lift_ext tY hFO (j ≫ i) (nT ≫ t.toBase ≫ q)
      (by rw [hsq, Category.assoc]) _ _ ?_ ?_ ?_ ?_
    · rw [← Category.assoc, hNS', hmdef, Category.assoc, hb₀, ← Category.assoc, hki]
    · rw [Category.assoc, hb₀']
    · rw [← Category.assoc, ha₀, Category.assoc, htm, ← Category.assoc]
    · rw [Category.assoc, transitivityMap_comp_toBase, ha₀']
  have hΨ' : Mono (immersionConormalSheafMap nI tY.inclusion (j ≫ i)
      (a₀ ≫ transitivityMap i p tZ tY) (toShHom_square (square_comp ha₀ htm))) := by
    rw [immersionConormalSheafMap_congr nI tY.inclusion hki htri
      (toShHom_square (square_comp hcommΘ hb₀)) (toShHom_square (square_comp ha₀ htm))]
    infer_instance
  rw [immersionConormalSheafMap_comp nI tZ.inclusion tY.inclusion j a₀ ha₀ i
    (transitivityMap i p tZ tY) htm] at hΨ'
  have hmid : Mono ((modulePullback j.toLRSHom.toShHom).map
      (transitivityConormalLeftMap i p tZ tY) ≫
        immersionConormalSheafMap nI tZ.inclusion j a₀ (toShHom_square ha₀)) :=
    mono_of_mono_natIsoApp_comp
      (modulePullbackComp j.toLRSHom.toShHom i.toLRSHom.toShHom) _ _ hΨ'
  exact mono_of_mono_comp _ _ hmid

/-! ### Stacks 06BA -/

/-- **The first arrow of the conormal sequence of part (2) of [Stacks Project, Tag 06AE] is a
monomorphism** when `Z ⟶ Y` is a local complete intersection morphism. -/
@[stacks 06BA "the left arrow of the sequence of Stacks 06AE is a monomorphism"]
theorem mono_transitivityConormalLeftMap (hi : IsLocalCompleteIntersectionMorphism i) :
    Mono (transitivityConormalLeftMap i p tZ tY) := by
  have hlfp : LocallyOfFinitePresentation i :=
    locallyOfFinitePresentation_of_isLocalCompleteIntersectionMorphism hi
  have hfu : FormallyUnramified p :=
    formallyUnramified_of_isUniversalFirstOrderThickening tY.isUniversal
  have key : ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧
      Mono ((Scheme.Modules.pullback U.ι).map (transitivityConormalLeftMap i p tZ tY)) := by
    intro z
    obtain ⟨U, hU, hzU⟩ : ∃ U : Z.Opens, IsAffineOpen U ∧ z ∈ U := by
      obtain ⟨-, ⟨V, hV, rfl⟩, hzV, -⟩ :=
        Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
      exact ⟨V, hV, hzV⟩
    refine ⟨U, hzU, ?_⟩
    have hUaff : IsAffine U.toScheme := hU
    obtain ⟨n, k, hkimm, hki⟩ := exists_immersion_affineSpace (U.ι ≫ i)
    have hsmY : Smooth (AffineSpace (ULift.{u} (Fin n)) Y ↘ Y) := AffineSpace.smooth_over _ _
    have hsmX : Smooth (AffineSpace (ULift.{u} (Fin n)) X ↘ X) := AffineSpace.smooth_over _ _
    have hkos : IsKoszulRegularImmersion k :=
      isKoszulRegularImmersion_of_koszul i (AffineSpace (ULift.{u} (Fin n)) Y ↘ Y) U k hi hki.symm
    have hkH1 : IsH1RegularImmersion k := isH1RegularImmersion_of_isKoszulRegularImmersion k hkos
    have hfur : FormallyUnramified (AffineSpace.map (ULift.{u} (Fin n)) p) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (AffineSpace.isPullback_map (n := ULift.{u} (Fin n)) p).flip hfu
    exact mono_modulePullback_transitivityConormalLeftMap i p tZ tY U.ι
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin n)) p)
      (universalFirstOrderThickening (AffineSpace.map (ULift.{u} (Fin n)) p)) k hkH1 hki
  choose U hzU hmono using key
  exact Stacks.AlgebraicGeometry.Modules.mono_of_mono_pullback_cover
    (transitivityConormalLeftMap i p tZ tY) (fun z => (U z).ι)
    (fun z => ⟨z, ⟨z, hzU z⟩, rfl⟩) hmono

/-- Let `Z --i--→ Y --p--→ X` be morphisms of schemes with universal first-order thickenings
`Z ⊂ Z'` of `Z` over `X` and `Y ⊂ Y'` of `Y` over `X`, and assume `i` is a local complete
intersection morphism. Then the conormal sequence
```
0 ⟶ i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0
```
of part (2) of [Stacks Project, Tag 06AE] is **short exact**: its left arrow is a monomorphism,
it is exact at the middle term, and its right arrow is an epimorphism. -/
@[stacks 06BA "the conormal sequence of Stacks 06AE is short exact", sga "6 VIII 2.6" "partial"]
theorem transitivityConormalShortComplex_shortExact
    (hi : IsLocalCompleteIntersectionMorphism i) :
    (transitivityConormalShortComplex i p tZ tY).ShortExact where
  exact := transitivityConormalShortComplex_exact i p tZ tY
  mono_f := mono_transitivityConormalLeftMap i p tZ tY hi
  epi_g := epi_transitivityConormalRightMap i p tZ tY

end Stacks.Thickenings

end
