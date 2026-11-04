module

public import Mathlib.CategoryTheory.Sites.Coverage
public import StacksFrontier.AlgebraicGeometry.Descent.OpenSubsetFpqc
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.OpenEqualityLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackSections
public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsMate

/-!
# fpqc descent for a sheaf pulled back from the small étale site

Let `S` be a scheme in a big étale site `B`, let `F` be a sheaf of sets on the small étale site
of `S`, and let `π_S` be the projection from the big étale topos over `S` to the small étale
topos of `S`. The presheaf underlying `π_S⁻¹F` — by the sections formula, the presheaf
`X ↦ Γ(X_ét, f_X⁻¹F)` on the big étale site over `S` — satisfies descent not only for étale
coverings but for the much finer fpqc coverings.

This file proves the *uniqueness* half of that fpqc sheaf condition and reduces the sheaf
condition itself to the existence of amalgamations. Two sections of `π_S⁻¹F` over `X` which
agree on the members of an fpqc covering family of `X` are identified by the sections formula
with two global sections of the small-site pullback of `F` to `X`, and restriction along a
member of the family corresponds to inverse image along it. By Stacks 09XM the two global
sections agree on a largest open of `X`, and every member of the family factors through that
open; an fpqc covering family is jointly surjective, so the open is all of `X` and the sections
agree.

## Main results

* `AlgebraicGeometry.eq_of_smallEtalePullback_map_eq` — two global sections of a sheaf on the
  small étale site of `X` with equal inverse images along a jointly surjective family of
  morphisms of `B` are equal.
* `AlgebraicGeometry.bigEtaleOver_isSheaf_fpqc_of_isSheafFor` — the fpqc sheaf condition on the
  big étale category over `S` follows from the sheaf condition for the covering presieves.
* `AlgebraicGeometry.bigEtaleToSmallEtale_inverseImage_isSeparatedFor_fpqc` — the uniqueness
  half of the fpqc sheaf condition for `π_S⁻¹F`.
* `AlgebraicGeometry.bigEtaleToSmallEtale_inverseImage_isSheaf_fpqc_of_exists_isAmalgamation` —
  consequently the fpqc sheaf condition for `π_S⁻¹F` reduces to the existence of amalgamations.

## Implementation notes

The fpqc precoverage of the big étale category over `S` is the comap of
`AlgebraicGeometry.Scheme.fpqcPrecoverage` along the canonical functor to schemes. That functor
preserves fibre products and the category has all fibre products, so the precoverage is stable
under base change and has pullbacks, and Mathlib's
`CategoryTheory.Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange` reduces the
sheaf condition for the generated topology to the covering presieves.

The passage from sections of `π_S⁻¹F` to global sections on small étale sites is the sections
formula `AlgebraicGeometry.etaleInverseImageSectionsIso`, whose restriction maps are the
abstract mates `CategoryTheory.sheafPullbackSectionsRestriction`; that those mates reflect
inverse images is `CategoryTheory.sheafPullback_map_eq_of_sheafPullbackSectionsRestriction_eq`.
Stacks 09XM is stated for sections presented as morphisms out of a terminal sheaf, which is
what `CategoryTheory.Sheaf.ΓEquivHomTerminal` supplies, and for the explicit sheaf-pullback
construction rather than the abstract left adjoint, which is what
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackIso` bridges.

The *existence* half of the fpqc sheaf condition is not proved here. It rests on the local
representation step in the proof of Stacks 09XN: after an étale refinement of the covering, a
section of `g⁻¹F` over `T` comes from a pair consisting of an object `V` of the small étale
site of the base and a section of `F` over `V`, through which `T` factors.

## References

* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
* [Stacks Project, Tag 09XM](https://stacks.math.columbia.edu/tag/09XM)
* [Stacks Project, Tag 09XN](https://stacks.math.columbia.edu/tag/09XN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- An open subscheme which is the whole space is retracted by its own inclusion. -/
private theorem exists_section_ι_of_eq_top {Z : Scheme.{u}} (V : Z.Opens) (hV : V = ⊤) :
    ∃ q : Z ⟶ V.toScheme, q ≫ V.ι = 𝟙 Z := by
  subst hV
  exact ⟨Z.topIso.inv, Z.toIso_inv_ι⟩

/-- Inverse image along the identity morphism of a scheme is the identity functor on sheaves
of sets on its small étale site. -/
private noncomputable def smallEtalePullbackIdIso (B : BigEtaleSite.{u}) (X : B.Scheme) :
    smallEtalePullback.{u, v} B X X (𝟙 X) ≅
      𝟭 (Sheaf (SmallEtale.topology B X.obj X.property) (Type (max (u + 1) v))) :=
  (Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange B (𝟙 X))
      (Type (max (u + 1) v)) (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X.obj X.property)).symm ≪≫
    smallEtaleSheafPullbackIdIso B X (Type (max (u + 1) v))

/-- Naturally isomorphic functors agree on which pairs of morphisms they identify. -/
private theorem map_eq_of_natIso_aux {C D : Type*} [Category* C] [Category* D] {P Q : C ⥤ D}
    (i : P ≅ Q) {A A' : C} {σ₁ σ₂ : A ⟶ A'} (h : P.map σ₁ = P.map σ₂) :
    Q.map σ₁ = Q.map σ₂ := by
  have h1 := i.hom.naturality σ₁
  rw [h, i.hom.naturality σ₂] at h1
  exact (cancel_epi (i.hom.app A)).mp h1.symm

/-- **The uniqueness half of Stacks 09XN, geometric form.** Two global sections of a sheaf of
sets on the small étale site of `X` which agree after inverse image along every member of a
jointly surjective family of morphisms of `B` are equal.

By Stacks 09XM the two sections agree on a largest open of `X`, and every member of the family
factors through that open; joint surjectivity then forces the open to be all of `X`, so the
identity of `X` factors through it and the sections agree. -/
public theorem eq_of_smallEtalePullback_map_eq (B : BigEtaleSite.{u}) (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (max (u + 1) v)))
    (s t : terminal (Sheaf (SmallEtale.topology B X.obj X.property)
      (Type (max (u + 1) v))) ⟶ F)
    {I : Type*} (Y : I → B.Scheme) (g : ∀ i, Y i ⟶ X)
    (hsurj : ∀ x : B.inclusion.obj X, ∃ i, x ∈ Set.range (B.inclusion.map (g i)))
    (h : ∀ i, (smallEtalePullback.{u, v} B X (Y i) (g i)).map s =
      (smallEtalePullback.{u, v} B X (Y i) (g i)).map t) :
    s = t := by
  have hW : openEqLocus.{u, v} B X F s t = ⊤ := by
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun x => ?_)
    obtain ⟨i, y, hy⟩ := hsurj x
    obtain ⟨q, hq⟩ := (factorsThrough_openEqLocus_iff.{u, v} B X (Y i) F s t (g i)).mpr (h i)
    have hraw : (openEqLocus.{u, v} B X F s t).ι (q y) = B.inclusion.map (g i) y :=
      congrArg (fun k : B.inclusion.obj (Y i) ⟶ B.inclusion.obj X => k y) hq
    rw [← hy, ← hraw]
    exact (q y).property
  obtain ⟨q, hq⟩ := exists_section_ι_of_eq_top _ hW
  have hfin := (factorsThrough_openEqLocus_iff.{u, v} B X X F s t (𝟙 X)).mp
    ⟨q, hq.trans (B.inclusion.map_id X).symm⟩
  exact map_eq_of_natIso_aux (smallEtalePullbackIdIso.{u, v} B X) hfin

/-- Naturally isomorphic functors agree on which pairs of morphisms they identify. -/
public theorem map_eq_of_natIso {C D : Type*} [Category* C] [Category* D] {P Q : C ⥤ D}
    (i : P ≅ Q) {A A' : C} {σ₁ σ₂ : A ⟶ A'} (h : P.map σ₁ = P.map σ₂) :
    Q.map σ₁ = Q.map σ₂ := by
  exact map_eq_of_natIso_aux i h

/-- A section of `π_S⁻¹F` over `X`, read through the sections formula as a morphism from the
terminal sheaf on the small étale site of `X` to the small-site pullback of `F` to `X`. -/
private noncomputable def sectionAsHom (B : BigEtaleSite.{u}) (S : B.Scheme)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))
    (X : BigEtaleOver B S.obj S.property)
    (t : ((bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage.obj F).obj.obj
      (Opposite.op X)) :
    (⊤_ (Sheaf (SmallEtale.topology B X.left.obj X.left.property) (Type (u + 1)))) ⟶
      ((smallEtaleBaseChange B X.hom).sheafPullback (Type (u + 1))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B X.left.obj X.left.property)).obj F :=
  Sheaf.ΓEquivHomTerminal (SmallEtale.topology B X.left.obj X.left.property) _
    ((etaleInverseImageSectionsIso B S X).hom.app F t)

/-- Reading a section through the sections formula loses no information. -/
private theorem sectionAsHom_injective (B : BigEtaleSite.{u}) (S : B.Scheme)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))
    (X : BigEtaleOver B S.obj S.property) :
    Function.Injective (sectionAsHom B S F X) := by
  have hiso : IsIso ((etaleInverseImageSectionsIso B S X).hom.app F) :=
    ((etaleInverseImageSectionsIso B S X).app F).isIso_hom
  intro a b hab
  exact (mono_iff_injective ((etaleInverseImageSectionsIso B S X).hom.app F)).mp inferInstance
    ((Sheaf.ΓEquivHomTerminal (SmallEtale.topology B X.left.obj X.left.property)
      (((smallEtaleBaseChange B X.hom).sheafPullback (Type (u + 1))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B X.left.obj X.left.property)).obj F)).injective hab)

/-- **The uniqueness half of the fpqc sheaf condition of Stacks 09XN.** Two sections of
`π_S⁻¹F` over an object `X` of the big étale site over `S` which agree on the members of an
fpqc covering presieve of `X` are equal.

The sections formula identifies them with two global sections of the small-site pullback of
`F` to `X`; restriction along a member of the covering becomes inverse image along it, so by
Stacks 09XM the two global sections agree on a largest open of `X` through which every member
of the covering factors, and an fpqc covering is jointly surjective. -/
public theorem bigEtaleToSmallEtale_inverseImage_isSeparatedFor_fpqc (B : BigEtaleSite.{u})
    (S : B.Scheme) (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))
    {X : BigEtaleOver B S.obj S.property} (R : Presieve X)
    (hR : R ∈ Scheme.fpqcPrecoverage.comap (BigEtaleOver.toScheme B S.obj S.property) X) :
    Presieve.IsSeparatedFor
      ((bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage.obj F).obj R := by
  obtain ⟨ι, Z, p, rfl⟩ := R.exists_eq_ofArrows
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hR
  intro x t₁ t₂ h₁ h₂
  have hres : ∀ i, ((bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage.obj F).obj.map
      (p i).op t₁ =
    ((bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage.obj F).obj.map (p i).op t₂ :=
    fun i => (h₁ (p i) (.mk i)).trans (h₂ (p i) (.mk i)).symm
  -- Restriction along a member of the covering, read through the sections formula.
  have happ : ∀ (i : ι) (t : _),
      etalePullbackSectionsRestriction B S (p i) F
          ((etaleInverseImageSectionsIso B S X).hom.app F t) =
        (etaleInverseImageSectionsIso B S (Z i)).hom.app F
          (((bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage.obj F).obj.map
            (p i).op t) := by
    intro i t
    rw [← types_comp_apply, ← types_comp_apply,
      etaleInverseImageSectionsIso_naturality B S (p i) F]
  have hsec : ∀ i, etalePullbackSectionsRestriction B S (p i) F
        ((etaleInverseImageSectionsIso B S X).hom.app F t₁) =
      etalePullbackSectionsRestriction B S (p i) F
        ((etaleInverseImageSectionsIso B S X).hom.app F t₂) := fun i =>
    ((happ i t₁).trans (congrArg _ (hres i))).trans (happ i t₂).symm
  -- The restriction maps reflect inverse images, so the two global sections have equal
  -- inverse images along every member of the covering.
  have habs : ∀ i, ((smallEtaleBaseChange B (p i).left).sheafPullback (Type (u + 1))
          (SmallEtale.topology B X.left.obj X.left.property)
          (SmallEtale.topology B (Z i).left.obj (Z i).left.property)).map
        (sectionAsHom B S F X t₁) =
      ((smallEtaleBaseChange B (p i).left).sheafPullback (Type (u + 1))
          (SmallEtale.topology B X.left.obj X.left.property)
          (SmallEtale.topology B (Z i).left.obj (Z i).left.property)).map
        (sectionAsHom B S F X t₂) := fun i =>
    sheafPullback_map_eq_of_sheafPullbackSectionsRestriction_eq
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B X.left.obj X.left.property)
      (SmallEtale.topology B (Z i).left.obj (Z i).left.property)
      (smallEtaleBaseChange B X.hom) (smallEtaleBaseChange B (p i).left)
      (smallEtaleBaseChange B (Z i).hom)
      ((smallEtaleBaseChange_compIso B (Z i).left X.left S (p i).left X.hom).val ≪≫
        eqToIso (congrArg (smallEtaleBaseChange B) (Over.w (p i))))
      (SmallEtale.finalIsTerminal B X.left.obj X.left.property)
      (smallEtaleBaseChange_finalIsTerminal B (p i).left) F _ _ (hsec i)
  -- Stacks 09XM and joint surjectivity of an fpqc covering finish the argument.
  refine sectionAsHom_injective B S F X (eq_of_smallEtalePullback_map_eq.{u, u + 1} B X.left
    (((smallEtaleBaseChange B X.hom).sheafPullback (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B X.left.obj X.left.property)).obj F)
    (sectionAsHom B S F X t₁) (sectionAsHom B S F X t₂)
    (fun i => (Z i).left) (fun i => (p i).left) (fpqc_jointly_surjective _ hR)
    (fun i => map_eq_of_natIso
      (Functor.sheafPullbackConstruction.sheafPullbackIso
        (smallEtaleBaseChange B (p i).left) (Type (u + 1))
        (SmallEtale.topology B X.left.obj X.left.property)
        (SmallEtale.topology B (Z i).left.obj (Z i).left.property)) (habs i)))

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A presheaf on the big étale category over `S` is a sheaf for the fpqc topology as soon as
it satisfies the sheaf condition for every fpqc covering presieve. -/
public theorem bigEtaleOver_isSheaf_fpqc_of_isSheafFor
    {P : (BigEtaleOver B S hS)ᵒᵖ ⥤ Type w}
    (h : ∀ ⦃X : BigEtaleOver B S hS⦄ (R : Presieve X),
      R ∈ Scheme.fpqcPrecoverage.comap (BigEtaleOver.toScheme B S hS) X →
      Presieve.IsSheafFor P R) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigEtaleOver.toScheme B S hS)).toGrothendieck) P := by
  have : PreservesLimitsOfShape WalkingCospan (BigEtaleOver.toScheme B S hS) := by
    infer_instance
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  exact h

/-- **The fpqc sheaf condition of Stacks 09XN, reduced to its existence half.** The presheaf
`X ↦ Γ(X_ét, f_X⁻¹F)` on the big étale site over `S` — that is, the underlying presheaf of
`π_S⁻¹F` — is a sheaf for the fpqc topology as soon as every compatible family of its sections
on an fpqc covering presieve has an amalgamation.

The uniqueness half is unconditional:
`AlgebraicGeometry.bigEtaleToSmallEtale_inverseImage_isSeparatedFor_fpqc`. The existence half
is the hypothesis `h`; it is the part of the proof of Stacks 09XN which produces, after an
étale refinement of the covering, a pair consisting of an object of the small étale site of `X`
and a section of `F` over it representing a given local section. -/
public theorem bigEtaleToSmallEtale_inverseImage_isSheaf_fpqc_of_exists_isAmalgamation
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1)))
    (h : ∀ ⦃X : BigEtaleOver B S hS⦄ (R : Presieve X),
      R ∈ Scheme.fpqcPrecoverage.comap (BigEtaleOver.toScheme B S hS) X →
      ∀ x : Presieve.FamilyOfElements
        ((bigEtaleToSmallEtaleMorphism B S hS).inverseImage.obj F).obj R,
        x.Compatible → ∃ t, x.IsAmalgamation t) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigEtaleOver.toScheme B S hS)).toGrothendieck)
      ((bigEtaleToSmallEtaleMorphism B S hS).inverseImage.obj F).obj := by
  refine bigEtaleOver_isSheaf_fpqc_of_isSheafFor B S hS ?_
  intro X R hR
  exact (bigEtaleToSmallEtale_inverseImage_isSeparatedFor_fpqc B (B.obj S hS) F R hR).isSheafFor
    (h R hR)

end AlgebraicGeometry
