module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCokernelSheafData
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesOnAffineSite

/-!
# Sections over affine objects of the fppf sheafification of a presheaf cartesian along flat maps

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `P` be a presheaf of
modules over the structure sheaf of the associated fppf site, with module sections in the universe
`u` of the schemes.  Suppose `P` is *cartesian along flat morphisms of affines*: for every arrow
`φ : z ⟶ x` of `𝒳` between objects lying over affine schemes, whose image `Z ⟶ X` in schemes is
flat, the base-change comparison `Γ(Z, 𝒪) ⊗_{Γ(X, 𝒪)} P(x) ⟶ P(z)` is an isomorphism.  Then
the sheafification unit `P ⟶ P^#` for the fppf topology is bijective on the sections over every
object lying over an affine scheme
(`AlgebraicGeometry.FibredSite.bijective_sheafificationAdjunction_unit_app_of_isAffine_of_flat`).

## The proof

A covering sieve of an object `x` lying over an affine scheme contains a finite family of arrows
from objects lying over affine schemes whose image in schemes is an fppf covering
(`AlgebraicGeometry.FibredSite.exists_finite_affine_fppf_ofArrows_le`).  Its arrows are flat
morphisms of affines, and so are the arrows from its pairwise fibre products to `x`: those fibre
products lie over the fibre products of the underlying affine schemes.  So the cartesian
hypothesis identifies all the sections the sheaf condition for that family mentions with base
changes of `P(x)`, and descent along the faithfully flat ring map `Γ(X) ⟶ ∏ Γ(Z_i)` gives the
sheaf condition for the family
(`Stacks.PresheafOfModules.isSheafFor_of_isIso_restrictionBaseChange`, Stacks 023M).  In
particular `P` is separated for every covering sieve of `x`.

The unit of sheafification is locally injective and locally surjective.  Separatedness at `x`
turns local injectivity into injectivity on the sections over `x`; a section of `P^#` over `x`
lifts over the members of a covering sieve, hence over a finite flat family of affines as above,
on whose members and pairwise fibre products `P` is separated and for which `P` satisfies the
sheaf condition, so it lifts over `x`
(`CategoryTheory.Presheaf.surjective_app_of_forall_exists_isSheafFor_arrows`).

This is the argument of
`AlgebraicGeometry.SmallEtale.bijective_sheafificationAdjunction_unit_app_of_isAffine` for the
small étale site, carried out on the big fppf site of a category fibred in groupoids,
where the hypothesis is needed along flat arrows only.

## Main results

* `AlgebraicGeometry.FibredSite.isSheafFor_ofArrows_of_isIso_restrictionBaseChange`: the sheaf
  condition for a finite family of objects over affine schemes lying over an fppf covering of an
  affine scheme.
* `AlgebraicGeometry.FibredSite.isSeparatedFor_of_isIso_restrictionBaseChange`: separatedness for
  every covering sieve of an object lying over an affine scheme.
* `AlgebraicGeometry.FibredSite.bijective_app_of_isIso_restrictionBaseChange`: **a locally
  injective and locally surjective morphism from such a presheaf to a sheaf is bijective on the
  sections over every object lying over an affine scheme.**
* `AlgebraicGeometry.FibredSite.bijective_sheafificationAdjunction_unit_app_of_isAffine_of_flat`:
  the same for the unit of sheafification of presheaves of modules.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The image in schemes of the pullback square of two arrows of `𝒳` is a pullback square. -/
private theorem isPullback_toScheme_map_pullback (hp : p.IsFiberedInGroupoids)
    [HasPullbacks 𝒳] {x y z : 𝒳} (f : y ⟶ x)
    (g : z ⟶ x) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (p.map (pullback.fst f g)))
      ((BigFppfOver.toScheme B S hS).map (p.map (pullback.snd f g)))
      ((BigFppfOver.toScheme B S hS).map (p.map f))
      ((BigFppfOver.toScheme B S hS).map (p.map g)) :=
  (Functor.IsFiberedInGroupoids.map_isPullback p hp f g _ _
    (IsPullback.of_hasPullback _ _)).map (BigFppfOver.toScheme B S hS)

/-- The pullback of two arrows of `𝒳` between objects over affine schemes lies over an affine
scheme. -/
private theorem isAffine_toScheme_obj_pullback (hp : p.IsFiberedInGroupoids)
    [HasPullbacks 𝒳] {x y z : 𝒳} (f : y ⟶ x)
    (g : z ⟶ x) [IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z))] :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (pullback f g))) :=
  IsAffine.of_isPullback (isPullback_toScheme_map_pullback B S hS p hp f g)

include hp in
/-- **A presheaf of modules cartesian along flat morphisms of affines satisfies the sheaf
condition for a finite family of objects over affine schemes lying over an fppf covering of an
affine scheme.**  The members of the family and its pairwise fibre products lie over affine
schemes flat over the one below `x`, so the cartesian hypothesis applies to all the arrows the
descent argument of Stacks 023M uses. -/
theorem isSheafFor_ofArrows_of_isIso_restrictionBaseChange
    (P : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf).obj)
    (hP : ∀ {z x : 𝒳} (φ : z ⟶ x), IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) →
      Flat ((BigFppfOver.toScheme B S hS).map (p.map φ)) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (structureSheaf B S hS p hp .fppf).obj) P φ.op))
    {x : 𝒳} (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)))
    {I : Type*} [Finite I] (z : I → 𝒳) (φ : ∀ i, z i ⟶ x)
    (hz : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (z i))))
    (hfppf : Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (p.obj (z i)))
        (fun i => (BigFppfOver.toScheme B S hS).map (p.map (φ i))) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj (p.obj x))) :
    Presieve.IsSheafFor (P.presheaf ⋙ forget AddCommGrpCat) (Presieve.ofArrows z φ) := by
  let : HasPullbacks 𝒳 := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp
  let v : 𝒳 ⥤ Scheme.{u} := p ⋙ BigFppfOver.toScheme B S hS
  unfold Scheme.fppfPrecoverage at hfppf
  have hcov := (Scheme.ofArrows_mem_precoverage_iff _).1 hfppf
  have hflat : ∀ i, Flat (v.map (φ i)) := fun i => (hcov.2 i).1
  have hpb := fun i j => isPullback_toScheme_map_pullback B S hS p hp (φ i) (φ j)
  have : IsAffine (v.obj x) := hx
  have : ∀ i, IsAffine (v.obj (z i)) := hz
  have hpaff : ∀ i j, IsAffine (v.obj (pullback (φ i) (φ j))) := fun i j =>
    isAffine_toScheme_obj_pullback B S hS p hp (φ i) (φ j)
  refine Stacks.PresheafOfModules.isSheafFor_of_isIso_restrictionBaseChange
    (structureSheaf B S hS p hp .fppf).obj P z φ (fun i j => pullback (φ i) (φ j))
    (fun i j => pullback.fst (φ i) (φ j)) (fun i j => pullback.snd (φ i) (φ j))
    (fun i j => pullback.condition) ?_ ?_ (fun i => hP _ (hz i) hx (hflat i))
    (fun i j => hP _ (hpaff i j) hx ?_)
  · exact Scheme.faithfullyFlat_pi_appTop (fun i => v.obj (z i)) (fun i => v.map (φ i))
      fun y => by
        obtain ⟨i, w, hw⟩ := hcov.1 y
        exact ⟨i, w, hw⟩
  · intro i j
    have : IsAffine (v.obj (pullback (φ i) (φ j))) := hpaff i j
    have h := isPushout_appTop_of_isPullback (hpb i j)
    exact h
  · have h1 : Flat (v.map (pullback.fst (φ i) (φ j))) :=
      MorphismProperty.of_isPullback (P := @Flat) (hpb i j).flip (hflat j)
    rw [Functor.map_comp, Functor.map_comp]
    exact MorphismProperty.comp_mem @Flat _ _ h1 (hflat i)

include hp in
/-- **A presheaf of modules cartesian along flat morphisms of affines is separated for every
covering sieve of an object lying over an affine scheme.**  The sieve contains a finite family of
objects over affine schemes lying over an fppf covering, for which the presheaf satisfies the
sheaf condition. -/
theorem isSeparatedFor_of_isIso_restrictionBaseChange
    (P : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf).obj)
    (hP : ∀ {z x : 𝒳} (φ : z ⟶ x), IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) →
      Flat ((BigFppfOver.toScheme B S hS).map (p.map φ)) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (structureSheaf B S hS p hp .fppf).obj) P φ.op))
    {x : 𝒳} (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)))
    (R : Sieve x) (hR : R ∈ BigFppfOver.associatedTopology B S hS p .fppf x) :
    Presieve.IsSeparatedFor (P.presheaf ⋙ forget AddCommGrpCat) (R : Presieve x) := by
  obtain ⟨n, z, φ, hz, hmem, -, hfppf⟩ := exists_finite_affine_fppf_ofArrows_le B S hS p hp hx hR
  refine (isSheafFor_ofArrows_of_isIso_restrictionBaseChange B S hS p hp P hP hx z φ hz
    hfppf).isSeparatedFor.of_le ?_
  rintro _ _ ⟨i⟩
  exact hmem i

include hp in
/-- **A locally injective and locally surjective morphism from a presheaf of modules cartesian
along flat morphisms of affines to a sheaf is bijective on the sections over every object lying
over an affine scheme.**  Injectivity is separatedness of the source at `x`; a section of the
target over `x` lifts over a finite family of objects over affine schemes lying over an fppf
covering, for which the source satisfies the sheaf condition and on whose pairwise fibre products
it is separated, so it lifts over `x`. -/
theorem bijective_app_of_isIso_restrictionBaseChange
    (P : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf).obj)
    (hP : ∀ {z x : 𝒳} (φ : z ⟶ x), IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) →
      Flat ((BigFppfOver.toScheme B S hS).map (p.map φ)) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (structureSheaf B S hS p hp .fppf).obj) P φ.op))
    {G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{u}}
    (hG : Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS p .fppf)
      (G ⋙ forget AddCommGrpCat))
    (θ : P.presheaf ⟶ G)
    [Presheaf.IsLocallyInjective (BigFppfOver.associatedTopology B S hS p .fppf) θ]
    [Presheaf.IsLocallySurjective (BigFppfOver.associatedTopology B S hS p .fppf) θ]
    {x : 𝒳} (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x))) :
    Function.Bijective (θ.app (op x)) := by
  let : HasPullbacks 𝒳 := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp
  let J := BigFppfOver.associatedTopology B S hS p .fppf
  let θ' : P.presheaf ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat :=
    Functor.whiskerRight θ (forget AddCommGrpCat)
  have hloc : ∀ (Z : 𝒳) (a b : (P.presheaf ⋙ forget AddCommGrpCat).obj (op Z)),
      θ'.app (op Z) a = θ'.app (op Z) b →
      ∃ T : Sieve Z, T ∈ J Z ∧ ∀ ⦃V : 𝒳⦄ (f : V ⟶ Z), T f →
        (P.presheaf ⋙ forget AddCommGrpCat).map f.op a =
          (P.presheaf ⋙ forget AddCommGrpCat).map f.op b := fun Z a b hab =>
    ⟨Presheaf.equalizerSieve (F := P.presheaf) a b, Presheaf.equalizerSieve_mem J θ a b hab,
      fun _ _ hf => hf⟩
  refine ⟨Presheaf.injective_app_of_isSeparatedFor θ' J x (hloc x)
    (isSeparatedFor_of_isIso_restrictionBaseChange B S hS p hp P hP hx), ?_⟩
  refine Presheaf.surjective_app_of_forall_exists_isSheafFor_arrows θ' J hloc fun s => ?_
  obtain ⟨n, z, φ, hz, hmem, hcov, hfppf⟩ := exists_finite_affine_fppf_ofArrows_le B S hS p hp hx
    (Presheaf.imageSieve_mem J θ s)
  have hpaff : ∀ i j, IsAffine ((BigFppfOver.toScheme B S hS).obj
      (p.obj (pullback (φ i) (φ j)))) := fun i j => by
    have := hz i
    have := hz j
    exact isAffine_toScheme_obj_pullback B S hS p hp (φ i) (φ j)
  refine ⟨Fin n, z, φ, inferInstance,
    isSheafFor_ofArrows_of_isIso_restrictionBaseChange B S hS p hp P hP hx z φ hz hfppf,
    Presieve.isSeparatedFor_iff_generate.2 (hG.isSheafFor _ hcov).isSeparatedFor,
    fun i j => isSeparatedFor_of_isIso_restrictionBaseChange B S hS p hp P hP (hpaff i j),
    fun i => hmem i⟩

include hp in
/-- **The fppf sheafification unit of a presheaf of modules cartesian along flat morphisms of
affines is bijective on the sections over every object lying over an affine scheme.**  This is
the input (C) of Stacks 0771 (6) and (7): sections over affine objects of a sheafified presheaf
of modules cartesian along flat morphisms of affines are the sections of the presheaf. -/
theorem bijective_sheafificationAdjunction_unit_app_of_isAffine_of_flat
    [HasWeakSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
    [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (P : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf).obj)
    (hP : ∀ {z x : 𝒳} (φ : z ⟶ x), IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) →
      Flat ((BigFppfOver.toScheme B S hS).map (p.map φ)) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (structureSheaf B S hS p hp .fppf).obj) P φ.op))
    {x : 𝒳} (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x))) :
    Function.Bijective (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringStructureSheafCore B S hS p hp .fppf).obj)).unit.app P).app (op x)) := by
  change Function.Bijective ((CategoryTheory.toSheafify
    (BigFppfOver.associatedTopology B S hS p .fppf) P.presheaf).app (op x))
  have hW := (BigFppfOver.associatedTopology B S hS p .fppf).W_toSheafify P.presheaf
  have := hW.isLocallyInjective
  have := hW.isLocallySurjective
  have hG : Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS p .fppf)
      (CategoryTheory.sheafify (BigFppfOver.associatedTopology B S hS p .fppf) P.presheaf ⋙
        forget AddCommGrpCat) :=
    SheafOfModules.isSheaf_sections
      ((PresheafOfModules.sheafification (𝟙 (ringStructureSheafCore B S hS p hp .fppf).obj)).obj
        P)
  exact bijective_app_of_isIso_restrictionBaseChange B S hS p hp P hP hG
    (CategoryTheory.toSheafify (BigFppfOver.associatedTopology B S hS p .fppf) P.presheaf) hx

end AlgebraicGeometry.FibredSite
