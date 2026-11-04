module

public import StacksFrontier.AlgebraicGeometry.Descent.UniversallyInjective.Exactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatReflection
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FaithfullyFlatLocalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModulePullbackFlatExact
public import StacksFrontier.RingTheory.Flat.FaithfullyFlatComp

/-!
# Pullback of modules along a flat surjective morphism is faithful on the spaces-étale sites

Let `f : X ⟶ Y` be a flat and surjective morphism of algebraic spaces over a scheme `S`. The
pullback `f^*` of modules along the morphism of spaces-étale ringed topoi of `f` (Stacks 0DE7),
with sections in the universe of the spaces-étale site, reflects zero objects and
monomorphisms. Consequently the unit `G ⟶ f_*f^*G` of `f^* ⊣ f_*` is a monomorphism for every
`𝒪_Y`-module `G`.

The proof is stalkwise. The points of the spaces-étale site of `Y` of the form `f ∘ x̄`, for
`x̄` a geometric point of `X`, form a conservative family since `f` is surjective. At such a
point the stalk of `f^*G` at `x̄` is the stalk of `G` at `f ∘ x̄` with scalars extended along
the homomorphism of structure-sheaf stalks (Stacks 05V5). That homomorphism is the map of étale
local rings, hence faithfully flat for flat `f` (Stacks 03MK), and a faithfully flat base change
of a nonzero module is nonzero. Nothing here is registered.

## Main results

* `AlgebraicGeometry.Space.faithfullyFlat_spacesEtaleStalkPullbackRingMap`: the homomorphism of
  structure-sheaf stalks of a flat morphism is faithfully flat.
* `AlgebraicGeometry.Space.isConservativeFamilyOfPoints_sitePoint_geometricPointMap`: for
  surjective `f` the points `f ∘ x̄` form a conservative family of points of the spaces-étale
  site of `Y`.
* `AlgebraicGeometry.Space.isZero_of_isZero_spacesEtalePullbackModules_obj`: `f^*` reflects zero
  objects.
* `AlgebraicGeometry.Space.mono_spacesEtalePullbackAdjunction_unit_app`: the unit of
  `f^* ⊣ f_*` is a monomorphism.

## References

* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 03MK](https://stacks.math.columbia.edu/tag/03MK)
* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

open SimplicialSpacesEtaleSite ExtensionByZeroStalk

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **The homomorphism of structure-sheaf stalks of a flat morphism is faithfully flat**:
transported to the étale local rings it is the homomorphism of Stacks 04NG, which is faithfully
flat by Stacks 03MK. -/
theorem faithfullyFlat_spacesEtaleStalkPullbackRingMap (hf : IsFlat B S hS f.hom)
    (x : GeometricPoint B S hS X.1) :
    (spacesEtaleStalkPullbackRingMapSpacesEtaleModulePullbackFlatExact f x).FaithfullyFlat := by
  set eX := spacesPointStalkRingEquivSpacesEtaleModulePullbackFlatExact x
  set eY := spacesPointStalkRingEquivSpacesEtaleModulePullbackFlatExact (geometricPointMap f.hom x)
  set φ := spacesEtaleStalkPullbackRingMapSpacesEtaleModulePullbackFlatExact f x
  have hcomp : ((eX.toRingHom.comp φ).comp eY.symm.toRingHom).FaithfullyFlat := by
    rw [eq_etaleLocalRingMap X.2 f.hom x
      (isEtaleLocalRingMap_spacesEtaleStalkPullbackRingMap_spacesEtaleModulePullbackFlatExact f x)]
    exact faithfullyFlat_etaleLocalRingMap B S hS X.2 Y.2 f.hom hf x
  have hsrm : φ = eX.symm.toRingHom.comp (((eX.toRingHom.comp φ).comp eY.symm.toRingHom).comp
      eY.toRingHom) := RingHom.ext fun _ => by simp
  rw [hsrm]
  exact ((RingHom.FaithfullyFlat.of_bijective eY.bijective).comp hcomp).comp
    (RingHom.FaithfullyFlat.of_bijective eX.symm.bijective)

/-- **The images of the geometric points of `X` are a conservative family of points of the
spaces-étale site of `Y`** when `f : X ⟶ Y` is surjective. A point of an object `V` étale over
`Y` lifts to the base change `V ×_Y X` (Stacks 03MH), whose points are images of geometric
points; the image of such a geometric point in `X` gives a point `f ∘ x̄` lifting through `V`. -/
theorem isConservativeFamilyOfPoints_sitePoint_geometricPointMap
    (hs : IsSurjective B S hS f.hom) :
    ObjectProperty.IsConservativeFamilyOfPoints
      (ObjectProperty.ofObj
        (fun x : GeometricPoint B S hS X.1 => sitePoint (geometricPointMap f.hom x))) := by
  apply ObjectProperty.IsConservativeFamilyOfPoints.mk'
  intro V R hR
  let E : PreZeroHypercover.{u + 1} V :=
    { I₀ := Σ W : SpacesEtale B S hS Y, {g : W ⟶ V // R g}
      X i := i.1
      f i := i.2.1 }
  have hcov : SpacesEtale.IsCovering B S hS Y ⟨V, E⟩ := by
    intro z
    let V' := (spacesBaseChange B S hS f).functor.obj V
    let π := (spacesBaseChange B S hS f).projection.app V
    have hπ : IsSurjective B S hS π.hom :=
      isSurjective_of_isPullback B S hS ((spacesBaseChange B S hS f).isPullback V).flip hs
    obtain ⟨z', hz'⟩ := hπ z
    obtain ⟨p, hp⟩ := exists_geometricRepresentative B S hS
      ((SpacesEtale.toSpaces B S hS X).obj V').1 z'
    let x := geometricPointMap ((SpacesEtale.inclusion B S hS X).obj V').hom.hom p
    have hsq := congrArg (fun k => k.hom.app (Opposite.op p.val.siteObject) p.val.value)
      ((spacesBaseChange B S hS f).isPullback V).w
    let v : Lifts V (geometricPointMap f.hom x) := ⟨π.hom.app _ p.val.value, hsq⟩
    obtain ⟨W, g, hg, w, hw⟩ :=
      hR ⟨sitePoint (geometricPointMap f.hom x), ObjectProperty.ofObj_apply _ x⟩ (ULift.up v)
    refine ⟨⟨W, g, hg⟩, (liftGeometricPoint w.down).image, ?_⟩
    rw [← hz', ← hp, ← geometricPointMap_image, ← geometricPointMap_image]
    congr 1
    apply Subtype.ext
    dsimp only [geometricPointMap, liftGeometricPoint, FieldValuedPoint.map]
    congr 1
    exact congrArg (fun t => t.down.1) hw
  refine GrothendieckTopology.superset_covering _ ?_
    (Precoverage.generate_mem_toGrothendieck
      ((SpacesEtale.mem_precoverage_iff B S hS Y).2 ⟨E, rfl, hcov⟩))
  rintro W g ⟨Z, k, h, ⟨i⟩, rfl⟩
  exact R.downward_closed i.2.2 k

/-- A composite `A ⋙ F` with `F` preserving zero morphisms carries an object which `A` sends to
zero to zero. Stated for the composite, so that it applies to a composite functor appearing in
the type of a natural isomorphism without restating its factors. -/
theorem _root_.CategoryTheory.Functor.isZero_comp_obj_of_isZero {C D E : Type*} [Category* C]
    [Category* D] [Category* E] [HasZeroMorphisms D] [HasZeroMorphisms E] (A : C ⥤ D) (F : D ⥤ E)
    (hF : F.PreservesZeroMorphisms) {G : C} (h : IsZero (A.obj G)) : IsZero ((A ⋙ F).obj G) :=
  F.map_isZero h

/-- A module whose faithfully flat extension of scalars is zero is zero. -/
theorem isZero_of_extendScalars_obj_isZero_of_faithfullyFlat {R T : Type u} [CommRing R]
    [CommRing T] {φ : R →+* T} (hφ : φ.FaithfullyFlat) (M : ModuleCat.{u} R)
    (hM : IsZero ((ModuleCat.extendScalars φ).obj M)) : IsZero M := by
  rw [ModuleCat.isZero_iff_subsingleton] at hM ⊢
  exact not_nontrivial_iff_subsingleton.1 fun _ =>
    not_nontrivial_iff_subsingleton.2 hM (nontrivial_extendScalars_of_faithfullyFlat hφ M)

/-- At a point `f ∘ x̄`, the stalk of an `𝒪_Y`-module `G` vanishes as soon as the stalk of
`f^*G` at `x̄` does: by Stacks 05V5 the latter is the extension of scalars of the former along a
faithfully flat homomorphism. -/
theorem isZero_sheafModuleFiberOfCommRing_geometricPointMap (hf : IsFlat B S hS f.hom)
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS Y).O))
    (x : GeometricPoint B S hS X.1)
    (h : IsZero (((spacesEtaleRingedToposHom f).toModulesHom.pullbackModules ⋙
      Stacks.sheafModuleFiberOfCommRing (sitePoint x) (spacesEtaleRingedTopos B S hS X).O).obj G)) :
    IsZero ((Stacks.sheafModuleFiberOfCommRing (sitePoint (geometricPointMap f.hom x))
      (spacesEtaleRingedTopos B S hS Y).O).obj G) := by
  have h₁ := ((Stacks.Sheaves.StalkPullback.stalkFunctorIso
    (spacesEtaleRingedToposHom f).toModulesHom (sitePoint x)
    (sitePoint (geometricPointMap f.hom x))
    (spacesEtaleInverseImageFiberIsoSpacesEtaleModulePullbackFlatExact f x)).app G).isZero_iff.1 h
  dsimp only [Functor.comp_obj] at h₁
  exact isZero_of_extendScalars_obj_isZero_of_faithfullyFlat
    (faithfullyFlat_spacesEtaleStalkPullbackRingMap f hf x) _ h₁

/-- **Pullback along a flat surjective morphism reflects zero objects** on the spaces-étale
sites: at a point `f ∘ x̄` the stalk of `G` becomes, after the faithfully flat extension of
scalars of Stacks 05V5, the stalk of `f^*G` at `x̄`, and these points form a conservative
family. -/
theorem isZero_of_isZero_spacesEtalePullbackModules_obj (hf : IsFlat B S hS f.hom)
    (hs : IsSurjective B S hS f.hom)
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS Y).O))
    (hG : IsZero ((spacesEtaleRingedToposHom f).toModulesHom.pullbackModules.obj G)) :
    IsZero G := by
  have hT : (ShortComplex.mk (0 : G ⟶ G) (0 : G ⟶ G) zero_comp).Exact := by
    refine (Stacks.shortComplex_exact_iff_forall_exact_map_sheafModuleFiberOfCommRing
      (spacesEtaleRingedTopos B S hS Y).O
      (isConservativeFamilyOfPoints_sitePoint_geometricPointMap f hs)).2 ?_
    rintro ⟨Φ, hΦ⟩
    obtain ⟨x, rfl⟩ := (ObjectProperty.ofObj_iff _ Φ).1 hΦ
    refine ShortComplex.exact_of_isZero_X₂ _ ?_
    dsimp only [ShortComplex.map]
    exact isZero_sheafModuleFiberOfCommRing_geometricPointMap f hf G x
      (Functor.isZero_comp_obj_of_isZero _ _
        (Stacks.preservesZeroMorphisms_sheafModuleFiberOfCommRing
          (spacesEtaleRingedTopos B S hS X).O (sitePoint x)) hG)
  have : Mono (0 : G ⟶ G) := (ShortComplex.exact_iff_mono _ rfl).1 hT
  exact IsZero.of_mono_zero G G

/-- **Pullback along a flat surjective morphism reflects monomorphisms** on the spaces-étale
sites: it is left exact and reflects zero objects. -/
theorem reflectsMonomorphisms_spacesEtalePullbackModules (hf : IsFlat B S hS f.hom)
    (hs : IsSurjective B S hS f.hom) :
    (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules.ReflectsMonomorphisms := by
  have := (
  preservesFiniteLimits_spacesEtaleRingedToposHom_pullbackModules_spacesEtaleModulePullbackFlatExact
    f hf)
  exact Functor.reflectsMonomorphisms_of_preservesFiniteLimits_of_reflectsZeroObjects _
    (isZero_of_isZero_spacesEtalePullbackModules_obj f hf hs)

/-- **The unit `G ⟶ f_*f^*G` is a monomorphism** for a flat surjective morphism `f` on the
spaces-étale sites: `f^*` of it is split by the counit, and `f^*` reflects monomorphisms. -/
theorem mono_spacesEtalePullbackAdjunction_unit_app (hf : IsFlat B S hS f.hom)
    (hs : IsSurjective B S hS f.hom)
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS Y).O)) :
    Mono ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (spacesEtaleRingedToposHom f).toModulesHom).unit.app G) := by
  have := reflectsMonomorphisms_spacesEtalePullbackModules f hf hs
  apply (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules.mono_of_mono_map
  exact mono_of_mono_fac ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
    (spacesEtaleRingedToposHom f).toModulesHom).left_triangle_components G)

end AlgebraicGeometry.Space

end
