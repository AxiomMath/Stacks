module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationConeBase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber

/-!
# The legs of the strict henselization cone are the canonical lifts

The strict henselization `Spec(𝒪^{sh}_{S,s})` is the limit of the étale neighbourhoods of `s`
(`AlgebraicGeometry.strictHenselizationCone`), and it maps to each étale neighbourhood `W` by the
unique morphism over `S` carrying its canonical geometric point to the chosen lift of `s`
(`AlgebraicGeometry.strictHenselizationNeighborhoodLift`). This file shows that the legs of the
limit cone carry the canonical geometric point to the chosen lifts, so that they are those unique
morphisms.

## Main definitions

* `AlgebraicGeometry.etaleNeighborhoodForgetCutoff` — the étale neighbourhoods of `s` in the chosen
  site, as étale neighbourhoods in the small étale site of `S`; this functor is initial.

## Main results

* `AlgebraicGeometry.geometricPointToStrictHenselization_comp_strictHenselizationCone_π_app` —
  the leg at an affine member of the small cofinal family carries the geometric point to the
  chosen lift, and `AlgebraicGeometry.strictHenselizationCone_π_app_eq_neighborhoodLift` — it is
  the canonical lift.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- **The leg of the strict henselization cone at an affine neighbourhood carries the canonical
geometric point to the chosen lift**: both are morphisms into an affine scheme, and on global
functions both are evaluation at the geometric point. -/
theorem geometricPointToStrictHenselization_comp_strictHenselizationCone_π_app
    (a : etaleNeighborhoodAffineIndex B S hS s) :
    geometricPointToStrictHenselization B S hS s ≫
        (strictHenselizationCone B S hS s).π.app
          ((etaleNeighborhoodAffineInclusion B S hS s).obj a) =
      ((etaleNeighborhoodAffineInclusion B S hS s).obj a).2.1 := by
  have : IsAffine ((etaleNeighborhoodDiagram B S hS s).obj
      ((etaleNeighborhoodAffineInclusion B S hS s).obj a)) :=
    isAffine_etaleNeighborhoodAffineDiagram_obj B S hS s a
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of s.residueField)).hom]
  ext b
  let π := (strictHenselizationCone B S hS s).π.app
    ((etaleNeighborhoodAffineInclusion B S hS s).obj a)
  show (Scheme.ΓSpecIso (CommRingCat.of s.residueField)).hom.hom
      ((geometricPointToStrictHenselization B S hS s).appTop.hom (π.appTop.hom b)) = _
  have hn := congrArg (fun φ => CommRingCat.Hom.hom φ (π.appTop.hom b))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (structureSheafStalkToGeometricField B S hS s)))
  beta_reduce at hn
  have h2 := congrArg (fun φ => φ b) (structureSheafStalkToGeometricField_ι B S hS s
    (op ((etaleNeighborhoodAffineInclusion B S hS s).obj a)))
  beta_reduce at h2
  exact hn.trans ((congrArg (structureSheafStalkToGeometricField B S hS s)
    (strictHenselizationCone_π_appTop_affine B S hS s a b)).trans h2)

/-- Forget the size cutoff on an étale neighborhood. -/
def etaleNeighborhoodForgetCutoff : (geometricPointFiber B S hS s).Elements ⥤
    (Scheme.pointSmallEtale s.hom).fiber.Elements where
  obj U := ⟨MorphismProperty.Over.mk _ (B.inclusion.map U.1.obj.hom) U.1.property,
    Over.homMk U.2.1 U.2.2⟩
  map {U V} f := ⟨MorphismProperty.Over.homMk ((SmallEtale.toScheme B S hS).map f.1)
    (by
      change B.inclusion.map f.1.hom.left ≫ B.inclusion.map V.1.obj.hom =
        B.inclusion.map U.1.obj.hom
      rw [← Functor.map_comp, Over.w]) (by trivial),
    Over.OverMorphism.ext (congrArg Subtype.val f.2)⟩

/-- The functor `etaleNeighborhoodForgetCutoff` is faithful. -/
instance faithful_etaleNeighborhoodForgetCutoff :
    (etaleNeighborhoodForgetCutoff B S hS s).Faithful where
  map_injective {U V} f g h := by
    apply Subtype.ext
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact congrArg (fun k => k.1.left) h

/-- The functor `etaleNeighborhoodForgetCutoff` is full. -/
instance full_etaleNeighborhoodForgetCutoff :
    (etaleNeighborhoodForgetCutoff B S hS s).Full where
  map_surjective {U V} f := by
    refine ⟨⟨ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk f.1.left) ?_), ?_⟩, ?_⟩
    · apply ObjectProperty.hom_ext
      exact f.1.w
    · exact Subtype.ext (congrArg (fun k => k.left) f.2)
    · apply Subtype.ext
      apply MorphismProperty.Over.Hom.ext
      rfl

/-- Every neighborhood has an affine refinement inside the chosen size cutoff. -/
theorem exists_etaleNeighborhoodForgetCutoff_refinement
    (U : (Scheme.pointSmallEtale s.hom).fiber.Elements) :
    ∃ V, IsAffine ((SmallEtale.toScheme B S hS).obj V.1) ∧
      Nonempty ((etaleNeighborhoodForgetCutoff B S hS s).obj V ⟶ U) := by
  let p : s.source ⟶ U.1.left := U.2.left
  obtain ⟨R, j, hj, y, hy⟩ : ∃ (R : CommRingCat.{u}) (j : Spec R ⟶ U.1.left)
      (_ : IsOpenImmersion j) (y : s.source ⟶ Spec R), y ≫ j = U.2.left := by
    obtain ⟨R, j, _, hj, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (x := p.base (default : s.source)) (U := ⊤) (by simp)
    refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j p ?_⟩
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  have hR : B.Contains (Spec R) :=
    (Scheme.size_le_of_locallyOfFiniteType (j ≫ U.1.hom)).trans_lt hS
  let V : SmallEtale B S hS :=
    ⟨Over.mk (ObjectProperty.homMk (j ≫ U.1.hom) : B.obj (Spec R) hR ⟶ B.obj S hS),
      inferInstanceAs (Etale (j ≫ U.1.hom))⟩
  have hyS : y ≫ (j ≫ U.1.hom) = s.hom := by
    rw [← Category.assoc, hy]
    exact Over.w U.2
  exact ⟨⟨V, ⟨y, hyS⟩⟩, inferInstanceAs (IsAffine (Spec R)),
    ⟨⟨MorphismProperty.Over.homMk j rfl (by trivial), Over.OverMorphism.ext hy⟩⟩⟩

/-- Forgetting the size cutoff on étale neighbourhoods is initial: every étale neighbourhood of
`s` is refined by one inside the chosen site, and the inclusion is fully faithful. -/
instance initial_etaleNeighborhoodForgetCutoff :
    (etaleNeighborhoodForgetCutoff B S hS s).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
    (etaleNeighborhoodForgetCutoff B S hS s)
    (fun U => (exists_etaleNeighborhoodForgetCutoff_refinement B S hS s U).imp fun _ => And.right)

/-- **The leg of the strict henselization cone at an affine neighbourhood is the canonical lift**
`AlgebraicGeometry.strictHenselizationNeighborhoodLift` to that neighbourhood, read in the small
étale site of `S`. -/
theorem strictHenselizationCone_π_app_eq_neighborhoodLift
    (a : etaleNeighborhoodAffineIndex B S hS s) :
    (strictHenselizationCone B S hS s).π.app ((etaleNeighborhoodAffineInclusion B S hS s).obj a) =
      strictHenselizationNeighborhoodLift B S hS s
        ((etaleNeighborhoodForgetCutoff B S hS s).obj
          ((etaleNeighborhoodAffineInclusion B S hS s).obj a)).1
        ((etaleNeighborhoodForgetCutoff B S hS s).obj
          ((etaleNeighborhoodAffineInclusion B S hS s).obj a)).2 :=
  strictHenselizationNeighborhoodLift_eq B S hS s
    ((etaleNeighborhoodForgetCutoff B S hS s).obj
      ((etaleNeighborhoodAffineInclusion B S hS s).obj a)).1
    ((etaleNeighborhoodForgetCutoff B S hS s).obj
      ((etaleNeighborhoodAffineInclusion B S hS s).obj a)).2
    (show strictHenselization B S hS s ⟶ _ from (strictHenselizationCone B S hS s).π.app
      ((etaleNeighborhoodAffineInclusion B S hS s).obj a))
    (strictHenselizationCone_π_comp_hom_eq B S hS s
      ((etaleNeighborhoodAffineInclusion B S hS s).obj a))
    (geometricPointToStrictHenselization_comp_strictHenselizationCone_π_app B S hS s a)

end AlgebraicGeometry

end
