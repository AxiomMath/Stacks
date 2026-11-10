module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitModules
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackStageSystem
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Sheafify
public import StacksFrontier.CategoryTheory.Sites.CostructuredArrowRestrictedTopology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFinitePresentationOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteLocallyFreeModuleDescent
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
import StacksFrontier.AlgebraicGeometry.Stacks.InvertibleCoherent

/-!
# The relative Picard functor is limit preserving

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is of
finite presentation, and let `Pic_{X/B}` be its relative Picard functor (Stacks 0D25), the fppf
sheafification of `T ↦ Pic(X_T)` on the schemes over `B`. This file proves that `Pic_{X/B} ⟶ B`
is limit preserving: for a cofiltered inverse system `T_i` of affine schemes over `B` whose limit
`T` in schemes is affine, `Pic_{X/B}(T) = colim_i Pic_{X/B}(T_i)`.

## Main results

* `AlgebraicGeometry.Space.PicardSituation.limitPreserving_picardFunctor`: the relative Picard
  functor of a morphism of finite presentation is limit preserving, in the sense of Stacks 049J
  for functors on the schemes over `B`.

## Implementation notes

The argument has two halves, both following the source's arguments for the presheaf and for its
sheafification.

*The presheaf `T ↦ Pic(X_T)`.* Since `X_T = lim X_{T_i}` with the `X_{T_i}` quasi-compact and
quasi-separated and with affine transition morphisms, Stacks 07V7 (in the form
`AlgebraicGeometry.Space.CoherentSituation.finitePresentationModule_isColimit_baseChange`) says
that finitely presented modules and their isomorphisms on `X_T` come from a stage. An invertible
module is finitely presented, and invertibility descends by the tensor-inverse argument of Stacks
0B8K, as in the proof of Stacks 0D2X (2): a tensor inverse `N` of `L` and the trivialization of
`L ⊗ N` descend to a stage, which needs the tensor product of finitely presented modules to be
finitely presented on the site (Stacks 03L6). This is done for the given cone, with no bound on
the size of the index category; the registered Stacks 0D2X (2),
`AlgebraicGeometry.Space.exists_isInvertibleModule_stage_model`, is stated for the limit
constructed in the site under a size bound on the index, and so does not apply directly.

*Sheafification.* The comparison of the presheaf with its fppf sheafification is locally
bijective, and the formal argument of Stacks 049O
(`AlgebraicGeometry.exists_sheaf_section_at_stage` and its companions) applies on any site whose
coverings of a cofiltered affine limit descend to a stage and whose coverings of an affine object
have finite affine refinements. The test schemes over `B` carry the topology restricted along the
projection to the big fppf site, whose covering sieves are exactly those with covering image
(`CategoryTheory.CostructuredArrow.mem_restrictedTopology_proj_iff`), so both properties are
inherited from the big fppf site (`AlgebraicGeometry.affineCoversDescend_bigFppfOver` and
`AlgebraicGeometry.finiteAffineRefinements_bigFppfOver`).

The index categories are taken in the universe of the schemes, as in Stacks 07V7.

## References

* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 049O](https://stacks.math.columbia.edu/tag/049O)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 0D2X](https://stacks.math.columbia.edu/tag/0D2X)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Stacks 03L6 for the covering-family rendering of finite presentation, on the small étale
site of an algebraic space. -/
private theorem tensorFinitePresentationOnSite_smallEtale :
    TensorFinitePresentationOnSite B S hS := by
  intro Z M N hM hN
  exact Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFinitePresentationOnSite
    (smallEtaleRingedSite B S hS Z.1 Z.2) M N hM hN

namespace PicardSituation

variable (s : PicardSituation B S hS)

/-- The situation of Stacks 08KB attached to a Picard situation whose morphism is of finite
presentation. -/
private abbrev coherentSituation (hf : IsFinitePresentation B S hS s.f.hom) :
    CoherentSituation B S hS :=
  ⟨s.X, s.base, s.f, hf⟩

section Limits

variable {s : PicardSituation B S hS}
  {I : Type u} [Category.{u} I] (D : I ⥤ s.SchemesOver) (c : Cone D)
  (hD : ∀ i, IsAffine ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base ⋙
      BigFppfOver.toScheme B S hS).obj (D.obj i)))
  (hC : IsAffine ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base ⋙
      BigFppfOver.toScheme B S hS).obj c.pt))

/-- The underlying system of affine objects of the site. -/
private abbrev affineSystem : I ⥤ BigAffineFppf B S hS :=
  ObjectProperty.lift _ (D ⋙ CostructuredArrow.proj _ _) hD

/-- The underlying cone of affine objects of the site. -/
private def affineCone : Cone (affineSystem D hD) where
  pt := ⟨c.pt.left, hC⟩
  π :=
    { app i := ObjectProperty.homMk (c.π.app i).left
      naturality i j f := by
        apply ObjectProperty.hom_ext
        change 𝟙 _ ≫ (c.π.app j).left = (c.π.app i).left ≫ (D.map f).left
        rw [Category.id_comp, ← CostructuredArrow.comp_left, c.w f] }

variable [IsCofiltered I]
  (hc : IsLimit ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base ⋙
      BigFppfOver.toScheme B S hS).mapCone c))

include hc in
/-- The test schemes form a limit of representable presheaves. -/
private def isLimit_yoneda : IsLimit
    ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base ⋙ yoneda).mapCone c) :=
  isLimit_affineYoneda_mapCone_of_isLimit_toScheme (affineSystem D hD) (affineCone D c hD hC) hc

variable (hf : IsFinitePresentation B S hS s.f.hom)

omit [IsCofiltered I] in
include hD in
/-- The transition morphisms `X_{T_j} ⟶ X_{T_k}` are affine, as base changes of morphisms of
affine schemes. -/
private theorem isAffineHom_system {j k : I} (e : j ⟶ k) :
    IsAffineHom B S hS ((testBaseChangeSystem s.f D).map e) := by
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((CostructuredArrow.proj _ s.base).obj (D.obj j))) := hD j
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((CostructuredArrow.proj _ s.base).obj (D.obj k))) := hD k
  exact IsAffineHom.of_isPullback (isPullback_testBaseChangeSystem s.f D e).flip
    (isAffineHom_yoneda_map B S hS _)

include hc hD hC hf in
/-- **Stacks 07V7 for the base changes `X_{T_i}` along a cofiltered limit of affine test
schemes**, essential surjectivity. -/
private theorem exists_model (P : Modules.{u, u} B S hS (s.baseChange c.pt).1 (s.baseChange c.pt).2)
    (hP : P.IsFinitePresentationOnSite) :
    ∃ (k : I) (Q : Modules.{u, u} B S hS (s.baseChange (D.obj k)).1 (s.baseChange (D.obj k)).2),
      Q.IsFinitePresentationOnSite ∧
        Nonempty (P ≅ (modulePullback B S hS (baseChangeMap s.f (c.π.app k))).obj Q) :=
  ((s.coherentSituation hf).finitePresentationModule_isColimit_baseChange D c B.contains_terminal
    (isAffineHom_system D hD)
    (fun j => (s.coherentSituation hf).isQuasiCompactSpace_space (D.obj j) (hD j))
    (fun j => (s.coherentSituation hf).isAbsolutelyQuasiSeparated_space B.contains_terminal
      (D.obj j) (hD j))
    (isLimit_testBaseChangeSystem s.f D c (isLimit_yoneda D c hD hC hc))
    (siteContainsBaseChangeLimits_testBaseChangeSystem s.f D
      (siteContainsBaseChangeLimits_affineYoneda (affineSystem D hD) (affineCone D c hD hC)
        hc))).2.2 P hP

include hc hD hC hf in
/-- **Stacks 07V7 for the base changes `X_{T_i}`**, in the form: two finitely presented modules
on a stage whose inverse images to `X_T` are isomorphic have isomorphic inverse images to a later
stage. -/
private theorem exists_stage_iso (j : I)
    (M N : Modules.{u, u} B S hS (s.baseChange (D.obj j)).1 (s.baseChange (D.obj j)).2)
    (hM : M.IsFinitePresentationOnSite) (hN : N.IsFinitePresentationOnSite)
    (χ : (modulePullback B S hS (baseChangeMap s.f (c.π.app j))).obj M ≅
      (modulePullback B S hS (baseChangeMap s.f (c.π.app j))).obj N) :
    ∃ (k : I) (e : k ⟶ j), Nonempty ((modulePullback B S hS (baseChangeMap s.f (D.map e))).obj M ≅
        (modulePullback B S hS (baseChangeMap s.f (D.map e))).obj N) := by
  obtain ⟨k, e, ψ, -⟩ := (s.coherentSituation hf).exists_stage_iso_of_cone D c B.contains_terminal
    (isAffineHom_system D hD)
    (fun j => (s.coherentSituation hf).isQuasiCompactSpace_space (D.obj j) (hD j))
    (fun j => (s.coherentSituation hf).isAbsolutelyQuasiSeparated_space B.contains_terminal
      (D.obj j) (hD j))
    (isLimit_testBaseChangeSystem s.f D c (isLimit_yoneda D c hD hC hc))
    (siteContainsBaseChangeLimits_testBaseChangeSystem s.f D
      (siteContainsBaseChangeLimits_affineYoneda (affineSystem D hD) (affineCone D c hD hC)
        hc)) j M N hM hN χ
  exact ⟨k, e, ⟨ψ⟩⟩

omit [IsCofiltered I] in
/-- The projections of the base changes along a cone of test schemes are compatible with the
transition morphisms. -/
private theorem baseChangeMap_cone_comp {i k : I} (t : k ⟶ i) :
    baseChangeMap s.f (c.π.app k) ≫ baseChangeMap s.f (D.map t) = baseChangeMap s.f (c.π.app i) :=
  (baseChangeMap_comp s.f _ _).symm.trans (congrArg (baseChangeMap s.f) (c.w t))

omit [IsCofiltered I] in
/-- The inverse image along the projection to a stage, read through a transition morphism. -/
private def conePullbackIso {i k : I} (t : k ⟶ i)
    (M : Modules.{u, u} B S hS (s.baseChange (D.obj i)).1 (s.baseChange (D.obj i)).2) :
    (modulePullback B S hS (baseChangeMap s.f (c.π.app i))).obj M ≅
      (modulePullback B S hS (baseChangeMap s.f (c.π.app k))).obj
        ((modulePullback B S hS (baseChangeMap s.f (D.map t))).obj M) :=
  eqToIso (congrArg (fun g => (modulePullback B S hS g).obj M)
      (baseChangeMap_cone_comp D c t).symm) ≪≫
    ((modulePullbackCompIso B S hS (baseChangeMap s.f (c.π.app k))
      (baseChangeMap s.f (D.map t))).app M).symm

include hc hD hC hf in
/-- **Stacks 0D2X (2) for the base changes `X_{T_i}`**: an invertible module on `X_T` is the
inverse image of an invertible module on some `X_{T_k}`. The argument is the tensor-inverse
argument of Stacks 0B8K: descend `L` and a tensor inverse `N` by Stacks 07V7, and descend the
trivialization of `L ⊗ N`. -/
private theorem exists_invertible_model
    (L : Modules.{u, u} B S hS (s.baseChange c.pt).1 (s.baseChange c.pt).2)
    (hL : IsInvertibleModule (s.baseChange c.pt) L) :
    ∃ (k : I) (Lk : Modules.{u, u} B S hS (s.baseChange (D.obj k)).1
        (s.baseChange (D.obj k)).2),
      IsInvertibleModule (s.baseChange (D.obj k)) Lk ∧
        Nonempty (L ≅ (modulePullback B S hS (baseChangeMap s.f (c.π.app k))).obj Lk) := by
  classical
  obtain ⟨N, ⟨e⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit L).mp hL
  have hN : IsInvertibleModule (s.baseChange c.pt) N :=
    (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit N).mpr
      ⟨L, ⟨Stacks.SheafOfModules.Invertible.tensorLeftFunctorSwap _ _ L N ≪≫ e⟩⟩
  obtain ⟨i, Li, hLi, ⟨eL⟩⟩ := exists_model D c hD hC hc hf L
    (Stacks.SheafOfModules.isFinitePresentationOnSite_of_isInvertible _ L hL)
  obtain ⟨i', Ni, hNi, ⟨eN⟩⟩ := exists_model D c hD hC hc hf N
    (Stacks.SheafOfModules.isFinitePresentationOnSite_of_isInvertible _ N hN)
  obtain ⟨k, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs i i'
  set Lk := (modulePullback B S hS (baseChangeMap s.f (D.map a))).obj Li
  set Nk := (modulePullback B S hS (baseChangeMap s.f (D.map b))).obj Ni
  have hLk := isFinitePresentationOnSite_modulePullback B S hS
    (baseChangeMap s.f (D.map a)) Li hLi
  have hNk := isFinitePresentationOnSite_modulePullback B S hS
    (baseChangeMap s.f (D.map b)) Ni hNi
  have eLk := eL ≪≫ conePullbackIso D c a Li
  have eNk := eN ≪≫ conePullbackIso D c b Ni
  set fk := smallEtaleRingedToposModulesHom B S hS (baseChangeMap s.f (c.π.app k))
  let key : (modulePullback B S hS (baseChangeMap s.f (c.π.app k))).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨(structureSheaf B S hS (s.baseChange (D.obj k)).1 (s.baseChange (D.obj k)).2).obj,
            Presheaf.isSheaf_of_isSheaf_comp _ ((structureSheaf B S hS (s.baseChange (D.obj k)).1
              (s.baseChange (D.obj k)).2).obj) (forget₂ CommRingCat RingCat)
              ((structureRingPresheaf_isSheaf B S hS (s.baseChange (D.obj k)).1
                (s.baseChange (D.obj k)).2))⟩).obj Lk)).obj Nk) ≅
      (modulePullback B S hS (baseChangeMap s.f (c.π.app k))).obj
        (SheafOfModules.unit (structureRingSheaf B S hS (s.baseChange (D.obj k)))) :=
    (Stacks.SheafOfModules.pullbackTensorIso fk).app (Lk, Nk) ≪≫
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          ((smallEtaleRingedTopos B S hS (s.baseChange c.pt)).O)).mapIso eLk.symm).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          ((smallEtaleRingedTopos B S hS (s.baseChange c.pt)).O)).obj _).mapIso eNk.symm) ≪≫
      e ≪≫ Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso fk
  obtain ⟨j, t, ⟨ψ⟩⟩ := exists_stage_iso D c hD hC hc hf k _ _
    (tensorFinitePresentationOnSite_smallEtale _ Lk Nk hLk hNk)
    SheafOfModules.isFinitePresentationOnSite_unit key
  set gt := smallEtaleRingedToposModulesHom B S hS (baseChangeMap s.f (D.map t))
  refine ⟨j, (modulePullback B S hS (baseChangeMap s.f (D.map t))).obj Lk,
    (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit _).mpr
      ⟨(modulePullback B S hS (baseChangeMap s.f (D.map t))).obj Nk,
        ⟨((Stacks.SheafOfModules.pullbackTensorIso gt).app (Lk, Nk)).symm ≪≫ ψ ≪≫
          (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso gt).symm⟩⟩,
    ⟨eLk ≪≫ conePullbackIso D c t Lk⟩⟩

include hc hD hC hf in
/-- The presheaf `T ↦ Pic(X_T)` turns the cofiltered limit of affine test schemes into a filtered
colimit of sets. -/
private theorem isColimit_picardPresheaf :
    Nonempty (IsColimit (s.picardPresheaf.mapCocone c.op)) := by
  refine isColimit_mapCocone_of_exists_of_eventually_eq _ D c ?_ ?_
  · intro x
    obtain ⟨L, hL, rfl⟩ := exists_picardClass _ x
    obtain ⟨k, Lk, hLk, ⟨e⟩⟩ := exists_invertible_model D c hD hC hc hf L hL
    refine ⟨k, picardClass _ Lk hLk, ?_⟩
    change s.picardMap (c.π.app k) _ = _
    rw [picardMap_eq, picardPullback_picardClass]
    exact (picardClass_eq_picardClass_iff _ _ _ _ _).2 ⟨e.symm⟩
  · intro i x y hxy
    obtain ⟨L, hL, rfl⟩ := exists_picardClass _ x
    obtain ⟨N, hN, rfl⟩ := exists_picardClass _ y
    change s.picardMap (c.π.app i) _ = s.picardMap (c.π.app i) _ at hxy
    rw [picardMap_eq, picardPullback_picardClass, picardPullback_picardClass,
      picardClass_eq_picardClass_iff] at hxy
    obtain ⟨χ⟩ := hxy
    obtain ⟨k, e, ⟨ψ⟩⟩ := exists_stage_iso D c hD hC hc hf i L N
      (Stacks.SheafOfModules.isFinitePresentationOnSite_of_isInvertible _ L hL)
      (Stacks.SheafOfModules.isFinitePresentationOnSite_of_isInvertible _ N hN) χ
    refine ⟨k, e, ?_⟩
    change s.picardMap (D.map e) _ = s.picardMap (D.map e) _
    rw [picardMap_eq, picardPullback_picardClass, picardPullback_picardClass]
    exact (picardClass_eq_picardClass_iff _ _ _ _ _).2 ⟨ψ⟩

end Limits

/-! ### Coverings of test schemes -/


/-- The lift of a family of morphisms of the site into the underlying object of a test scheme to
a family of test schemes. -/
private abbrev liftHypercover {X : s.SchemesOver} (E : PreZeroHypercover.{u + 1} X.left) :
    PreZeroHypercover.{u + 1} X :=
  ⟨E.I₀, fun k => CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map (E.f k) ≫ X.hom),
    fun k => CostructuredArrow.liftHom _ _ X (E.f k)⟩

/-- A family of test schemes lifting a covering family of the site generates a covering sieve. -/
private theorem liftHypercover_mem {X : s.SchemesOver} (E : PreZeroHypercover.{u + 1} X.left)
    (hE : E.sieve₀ ∈ BigFppfOver.topology B S hS X.left) :
    (s.liftHypercover E).sieve₀ ∈ s.fppfTopology X := by
  rw [CostructuredArrow.mem_restrictedTopology_proj_iff]
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hE
  rintro Z g ⟨W, a, b, ⟨k⟩, rfl⟩
  exact ⟨(s.liftHypercover E).X k, (s.liftHypercover E).f k, a,
    ⟨_, 𝟙 _, _, ⟨k⟩, Category.id_comp _⟩, rfl⟩

/-- **Coverings of a cofiltered affine limit of test schemes descend.** -/
private theorem affineCoversDescend_schemesOver :
    AffineCoversDescend.{u, u, u} (CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base ⋙
      BigFppfOver.toScheme B S hS) s.fppfTopology := by
  intro I _ _ D c hc hD hC R
  let P := CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base
  have hR : R.1.functorPushforward P ∈ BigFppfOver.topology B S hS c.pt.left :=
    (CostructuredArrow.mem_restrictedTopology_proj_iff _ _ _ c.pt R.1).1 R.2
  obtain ⟨i, E, hfin, haff, hE, hER⟩ := affineCoversDescend_bigFppfOver.{u, u, u} B S hS I
    (D ⋙ P) (P.mapCone c) hc hD hC ⟨_, hR⟩
  refine ⟨i, s.liftHypercover E, hfin, haff, s.liftHypercover_mem E hE, fun k => ?_⟩
  rw [← CostructuredArrow.mem_functorPushforward_proj_iff]
  change (R.1.functorPushforward P).arrows
    (P.map (pullback.fst (c.π.app i) ((s.liftHypercover E).f k)))
  rw [show P.map (pullback.fst (c.π.app i) ((s.liftHypercover E).f k)) =
      (PreservesPullback.iso P (c.π.app i) ((s.liftHypercover E).f k)).hom ≫
        pullback.fst (P.map (c.π.app i)) (E.f k) from (PreservesPullback.iso_hom_fst P _ _).symm]
  exact Sieve.downward_closed _ (hER k) _

/-- **Coverings of an affine test scheme have finite affine refinements.** -/
private theorem finiteAffineRefinements_schemesOver :
    FiniteAffineRefinements (CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base ⋙
      BigFppfOver.toScheme B S hS) s.fppfTopology := by
  intro X hX R
  have hR := (CostructuredArrow.mem_restrictedTopology_proj_iff _ _ _ X R.1).1 R.2
  obtain ⟨E, hfin, haff, hE, hER⟩ := finiteAffineRefinements_bigFppfOver B S hS X.left hX ⟨_, hR⟩
  exact ⟨s.liftHypercover E, hfin, haff, s.liftHypercover_mem E hE,
    fun k => (CostructuredArrow.mem_functorPushforward_proj_liftHom_iff _ _ R.1 (E.f k)).1 (hER k)⟩

/-- **The relative Picard functor is limit preserving.** Let `f : X ⟶ B` be a morphism of
algebraic spaces over `S` which is of finite presentation. For every cofiltered inverse system
`T_i` of affine schemes over `B` whose limit `T` in schemes is affine, the canonical map
`colim_i Pic_{X/B}(T_i) ⟶ Pic_{X/B}(T)` is bijective.

This holds in particular under the standing assumptions of Stacks 0DMD (`f` flat, proper and of
finite presentation), where it is the limit-preservation input of the local finite presentation
of `Pic_{X/B} ⟶ B` in Stacks 0DNI. -/
theorem limitPreserving_picardFunctor (hf : IsFinitePresentation B S hS s.f.hom) :
    LimitPreserving.{u, u + 1, u, u, u + 1}
      (CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base ⋙ BigFppfOver.toScheme B S hS)
      s.picardFunctor := by
  let T := CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base ⋙
    BigFppfOver.toScheme B S hS
  let J := s.fppfTopology
  have hdesc := s.affineCoversDescend_schemesOver
  have hF : LimitPreserving.{u, u + 1, u, u, u + 1} T s.picardPresheaf :=
    fun I _ _ D c hc hD hC => isColimit_picardPresheaf D c hD hC hc hf
  have hG : Presieve.IsSheaf J s.picardFunctor :=
    (isSheaf_iff_isSheaf_of_type J _).mp s.isSheaf_picardFunctor
  have : Presheaf.IsLocallySurjective J s.toPicardFunctor :=
    Presheaf.isLocallySurjective_toSheafify' J s.picardPresheaf
  have : Presheaf.IsLocallyInjective J s.toPicardFunctor :=
    Presheaf.isLocallyInjective_toSheafify' J s.picardPresheaf
  have hη := images_eventually_equal_of_locally_injective T J hdesc s.toPicardFunctor hG hF
  have hinj := images_eventually_equal_of_locally_surjective T J
    s.finiteAffineRefinements_schemesOver s.toPicardFunctor hG hη
  intro I _ _ D c hc hD hC
  exact isColimit_mapCocone_of_exists_of_eventually_eq _ D c
    (exists_sheaf_section_at_stage T J hdesc s.toPicardFunctor hG hF hinj D c hc hD hC)
    (hinj I D c hc hD hC)

end PicardSituation

end AlgebraicGeometry.Space
