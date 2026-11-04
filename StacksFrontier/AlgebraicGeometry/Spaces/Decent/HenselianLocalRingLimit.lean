module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Opposites
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingStalk

/-!
# The spectrum of the henselian local ring as a limit of elementary étale neighbourhoods

Let `x` be a point of a decent algebraic space `X` over `S`. The henselian local ring
`𝒪^h_{X, x}` of Stacks 0BGW is the colimit of the rings of global sections over the elementary
étale neighbourhoods of `x`; it lives one universe up, because those neighbourhoods form a large
category. Let `G : I ⥤ ElementaryEtaleNeighborhood X x` be an initial functor from a small
category, and let `R` be a ring in the base universe together with a ring isomorphism
`R ≃ 𝒪^h_{X, x}`.

Then `R`, with the homomorphisms `Γ(G i) ⟶ R` obtained from the canonical ones into
`𝒪^h_{X, x}`, is the colimit of the rings of global sections over `I`; and when every stage is
affine, `Spec R` is the limit of the schemes of the stages, with the projections
`Spec R ⟶ Spec Γ(G i) ≅ G i`.

## Main definitions

* `AlgebraicGeometry.Space.henselianLeg`: the homomorphism `Γ(G i) ⟶ R`.
* `AlgebraicGeometry.Space.henselianCocone`: the cocone of rings over `I` with vertex `R`.
* `AlgebraicGeometry.Space.henselianSchemeCone`: the cone of schemes over `I` with vertex
  `Spec R`.

## Main results

* `AlgebraicGeometry.Space.isColimitHenselianCocone`: the cocone is a colimit.
* `AlgebraicGeometry.Space.isLimitHenselianSchemeCone`: the cone is a limit.

## Implementation notes

That `R` is the colimit over `I` is not read off a comparison of colimits in two universes. A
cocone over `I` is extended to the category of all neighbourhoods along the final functor
`G.op`, and the universal property of `𝒪^h_{X, x}`,
`AlgebraicGeometry.Space.existsUnique_lift`, which holds for targets in any universe, produces
the factorisation; uniqueness is checked on the extended cocone, whose legs are determined by
the legs over `I` because every neighbourhood receives a map from a stage. The limit of schemes
is the image of the colimit of rings under `Spec`, which preserves limits, transported along the
isomorphisms `G i ≅ Spec Γ(G i)` of the affine stages.

## References

* [Stacks Project, Tag 0BGW](https://stacks.math.columbia.edu/tag/0BGW)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  (x : points B S hS X) (hdec : IsDecentSpace B S hS X)
  {I : Type u} [SmallCategory I] (G : I ⥤ ElementaryEtaleNeighborhood B S hS X hX x)
  {R : Type u} [CommRing R]
  (e : R ≃+* (henselianLocalRing B S hS X hX x hdec : Type (u + 1)))

/-- The homomorphism from the global sections of a stage into `R`: the canonical homomorphism
into the henselian local ring followed by the inverse of the given isomorphism. -/
def henselianLeg (i : I) : (globalSections B S hS X hX x).obj (op (G.obj i)) →+* R :=
  e.symm.toRingHom.comp (sectionHom B S hS X hX x hdec (op (G.obj i)))

/-- The legs into `R` are compatible with restriction along the stages. -/
theorem henselianLeg_naturality {i j : I} (f : i ⟶ j)
    (t : (globalSections B S hS X hX x).obj (op (G.obj j))) :
    henselianLeg B S hS hX x hdec G e i ((globalSections B S hS X hX x).map (G.map f).op t) =
      henselianLeg B S hS hX x hdec G e j t := by
  simp only [henselianLeg, RingHom.comp_apply]
  rw [sectionHom_naturality B S hS X hX x hdec (G.map f).op t]

/-- The cocone of rings of global sections over `I` with vertex `R`. -/
@[simps]
def henselianCocone : Cocone (G.op ⋙ globalSections B S hS X hX x) where
  pt := CommRingCat.of R
  ι :=
    { app := fun i => CommRingCat.ofHom (henselianLeg B S hS hX x hdec G e i.unop)
      naturality := fun i j f => by
        ext t
        simp only [Functor.comp_obj, Functor.op_obj, Functor.const_obj_obj, Functor.comp_map,
          Functor.op_map, Functor.const_obj_map]
        exact henselianLeg_naturality B S hS hX x hdec G e f.unop t }

/-- **`R` is the colimit of the rings of global sections of the stages.** -/
def isColimitHenselianCocone [G.Initial] :
    IsColimit (henselianCocone B S hS hX x hdec G e) := by
  have hext : ∀ s : Cocone (G.op ⋙ globalSections B S hS X hX x),
      ∃! ψ : henselianLocalRing B S hS X hX x hdec →+* s.pt,
        ∀ U t, ψ (sectionHom B S hS X hX x hdec U t) =
          (((Functor.Final.extendCocone (F := G.op)).obj s).ι.app U).hom t := fun s =>
    existsUnique_lift B S hS X hX x hdec s.pt
      (fun U => (((Functor.Final.extendCocone (F := G.op)).obj s).ι.app U).hom)
      (fun {U V} f t => (ConcreteCategory.comp_apply _ _ t).symm.trans
        (ConcreteCategory.congr_hom (((Functor.Final.extendCocone (F := G.op)).obj s).w f) t))
  refine
    { desc := fun s => CommRingCat.ofHom ((hext s).exists.choose.comp e.toRingHom)
      fac := fun s i => ?_
      uniq := fun s m hm => ?_ }
  · ext t
    have h₂ := Functor.Final.extendCocone_obj_ι_app' s (𝟙 (G.op.obj i))
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at h₂
    exact (congrArg (hext s).exists.choose (e.apply_symm_apply _)).trans
      (((hext s).exists.choose_spec (G.op.obj i) t).trans
        (congrArg (fun k => (CommRingCat.Hom.hom k) t) h₂))
  · let ψ' : henselianLocalRing B S hS X hX x hdec →+* s.pt := m.hom.comp e.symm.toRingHom
    have hψ' : ∀ U t, ψ' (sectionHom B S hS X hX x hdec U t) =
        (((Functor.Final.extendCocone (F := G.op)).obj s).ι.app U).hom t := by
      intro U t
      let k := Functor.Final.lift G.op U
      let f : U ⟶ G.op.obj k := Functor.Final.homToLift G.op U
      rw [Functor.Final.extendCocone_obj_ι_app' s f, ←
        sectionHom_naturality B S hS X hX x hdec f t]
      exact congrArg
        (fun q => (CommRingCat.Hom.hom q) ((globalSections B S hS X hX x).map f t)) (hm k)
    ext r
    exact (congrArg m.hom (e.symm_apply_apply r)).symm.trans
      (DFunLike.congr_fun ((hext s).unique hψ' (hext s).exists.choose_spec) (e r))

variable (hGaff : ∀ i, IsAffine (G.obj i).scheme.left.1)

/-- The stages are isomorphic to the spectra of their rings of global sections, naturally. -/
def henselianStageIso :
    G ⋙ neighborhoodScheme B S hS X hX x ≅
      (G.op ⋙ globalSections B S hS X hX x).rightOp ⋙ Scheme.Spec :=
  NatIso.ofComponents (fun i => haveI := hGaff i; (G.obj i).scheme.left.1.isoSpec) (by
    intro i j f
    have := hGaff i
    have := hGaff j
    exact (Scheme.isoSpec_hom_naturality ((G.map f).hom.left.1)).symm)

/-- The cone of schemes over `I` with vertex `Spec R`: the spectrum of the colimit cocone of
rings, transported along the isomorphisms of the affine stages with the spectra of their rings
of global sections. -/
def henselianSchemeCone : Cone (G ⋙ neighborhoodScheme B S hS X hX x) :=
  (Cone.postcompose (henselianStageIso B S hS hX x G hGaff).inv).obj
    (Scheme.Spec.mapCone (coneRightOpOfCocone (henselianCocone B S hS hX x hdec G e)))

/-- The vertex of the cone of schemes is `Spec R`, by definition. -/
theorem henselianSchemeCone_pt :
    (henselianSchemeCone B S hS hX x hdec G e hGaff).pt = Spec (CommRingCat.of R) := rfl

/-- The projection of the cone of schemes to the stage `i` is the spectrum of the homomorphism
`Γ(G i) ⟶ R` followed by the inverse of the isomorphism `G i ≅ Spec Γ(G i)`, by definition. -/
theorem henselianSchemeCone_π_app (i : I) :
    (henselianSchemeCone B S hS hX x hdec G e hGaff).π.app i =
      Spec.map (CommRingCat.ofHom (henselianLeg B S hS hX x hdec G e i)) ≫
        (haveI := hGaff i; (G.obj i).scheme.left.1.isoSpec.inv) := rfl

/-- **`Spec R` is the limit of the affine stages.** -/
def isLimitHenselianSchemeCone [G.Initial] :
    IsLimit (henselianSchemeCone B S hS hX x hdec G e hGaff) :=
  (IsLimit.postcomposeInvEquiv (henselianStageIso B S hS hX x G hGaff) _).symm
    (isLimitOfPreserves Scheme.Spec
      (isLimitConeRightOpOfCocone _ (isColimitHenselianCocone B S hS hX x hdec G e)))

end AlgebraicGeometry.Space

end
