module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas

/-!
# Étale and surjective morphisms on the big fppf site and lifted étale presentations

Stability properties of étale and surjective morphisms of presheaves on the big fppf site over a
scheme: under composition, isomorphism and base change. A surjective étale chart of an algebraic
space with representable kernel pair is an effective epimorphism onto sheaves, and the quotient
map of a lifted étale presentation is surjective and étale.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

private instance : MorphismProperty.IsMultiplicative (etaleOnSite B S hS) where
  id_mem A := by
    change Etale ((BigFppfOver.toScheme B S hS).map (𝟙 A))
    simpa using (inferInstance : Etale (𝟙 ((BigFppfOver.toScheme B S hS).obj A)))
  comp_mem {A C D} p q hp hq := by
    have hp' : Etale ((BigFppfOver.toScheme B S hS).map p) := hp
    have hq' : Etale ((BigFppfOver.toScheme B S hS).map q) := hq
    change Etale ((BigFppfOver.toScheme B S hS).map (p ≫ q))
    rw [Functor.map_comp]
    infer_instance

private instance : MorphismProperty.IsMultiplicative (surjectiveOnSite B S hS) where
  id_mem A := by
    change Surjective ((BigFppfOver.toScheme B S hS).map (𝟙 A))
    simpa using (inferInstance : Surjective (𝟙 ((BigFppfOver.toScheme B S hS).obj A)))
  comp_mem {A C D} p q hp hq := by
    have hp' : Surjective ((BigFppfOver.toScheme B S hS).map p) := hp
    have hq' : Surjective ((BigFppfOver.toScheme B S hS).map q) := hq
    change Surjective ((BigFppfOver.toScheme B S hS).map (p ≫ q))
    rw [Functor.map_comp]
    infer_instance

private instance : (etaleOnSite B S hS).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ k hk ↦ by
      have : IsIso k := hk
      exact (inferInstance : Etale ((BigFppfOver.toScheme B S hS).map k)))

private instance : (surjectiveOnSite B S hS).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ k hk ↦ by
      have : IsIso k := hk
      exact (inferInstance : Surjective ((BigFppfOver.toScheme B S hS).map k)))

/-- Étaleness on the site is stable under base change, because étaleness of schemes is and
the forgetful functor to schemes preserves fibre products. -/
theorem etaleSite_isStableUnderBaseChange' :
    (etaleOnSite B S hS).IsStableUnderBaseChange where
  of_isPullback sq hg :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale)
      (sq.map (BigFppfOver.toScheme B S hS)) hg

/-- An étale morphism of presheaves out of a representable one is relatively étale: test the
defining condition of Stacks 03FR on the identity chart. -/
theorem etalePresheaf_of_isEtale_yonedaDomain' {A : BigFppfOver B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : yoneda.obj A ⟶ F) (hg : IsEtale B S hS g) :
    (etaleOnSite B S hS).presheaf g := by
  simpa using hg A (𝟙 (yoneda.obj A)) (presheaf_etale_id B S hS A)

/-- Relative étaleness of presheaf morphisms is stable under base change. -/
theorem etalePresheaf_of_isPullback'
    {A C D E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : A ⟶ C} {q : A ⟶ D} {g : C ⟶ E} {h : D ⟶ E}
    (sq : IsPullback p q g h) (hg : (etaleOnSite B S hS).presheaf g) :
    (etaleOnSite B S hS).presheaf q :=
  (MorphismProperty.relative_isStableUnderBaseChange (etaleOnSite B S hS)).of_isPullback sq hg

/-- Relative surjectivity of presheaf morphisms is stable under base change. -/
theorem surjectivePresheaf_of_isPullback'
    {A C D E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : A ⟶ C} {q : A ⟶ D} {g : C ⟶ E} {h : D ⟶ E}
    (sq : IsPullback p q g h) (hg : (surjectiveOnSite B S hS).presheaf g) :
    (surjectiveOnSite B S hS).presheaf q :=
  (MorphismProperty.relative_isStableUnderBaseChange (surjectiveOnSite B S hS)).of_isPullback sq hg

/-- Surjectivity after every representable base change is stable under composition on the site,
being the relatively representable form of a multiplicative property. -/
theorem surjectiveOnSite_presheaf_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : F ⟶ G} {q : G ⟶ H} (hp : (surjectiveOnSite B S hS).presheaf p)
    (hq : (surjectiveOnSite B S hS).presheaf q) : (surjectiveOnSite B S hS).presheaf (p ≫ q) :=
  have : MorphismProperty.IsStableUnderComposition (surjectiveOnSite B S hS) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  MorphismProperty.comp_mem _ _ _ hp hq

/-- Étaleness after every representable base change is stable under composition on the site. -/
theorem etaleSite_presheaf_comp' {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : F ⟶ G} {q : G ⟶ H} (hp : (etaleOnSite B S hS).presheaf p)
    (hq : (etaleOnSite B S hS).presheaf q) : (etaleOnSite B S hS).presheaf (p ≫ q) :=
  have : MorphismProperty.IsStableUnderComposition (etaleOnSite B S hS) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  MorphismProperty.comp_mem _ _ _ hp hq

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 0262, part (3) as a descent statement.** A surjective étale chart of an algebraic
space whose kernel pair is representable is an epimorphism onto sheaves: every morphism out of
the chart which identifies the two projections of the kernel pair factors uniquely through
it. -/
theorem existsUnique_desc_of_surjectiveEtale'
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {A E : BigFppfOver B S hS}
    (q : yoneda.obj A ⟶ F) (p₁ p₂ : E ⟶ A)
    (hq : IsPullback (yoneda.map p₁) (yoneda.map p₂) q q)
    (hF : IsAlgebraicSpace B S hS F)
    (hqSurj : (surjectiveOnSite B S hS).presheaf q) (hqEtale : (etaleOnSite B S hS).presheaf q)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (g : yoneda.obj A ⟶ G) (hg : yoneda.map p₁ ≫ g = yoneda.map p₂ ≫ g) :
    ∃! e : F ⟶ G, q ≫ e = g := by
  obtain ⟨hEsh, hAsh, ⟨hcol⟩⟩ :=
    isCoequalizer_of_surjectiveEtale B S hS q p₁ p₂ hq hF hqSurj hqEtale
  let AF : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨yoneda.obj A, hAsh⟩
  let EF : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨yoneda.obj E, hEsh⟩
  let FF : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨F, hF.isSheaf⟩
  let GF : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨G, hG⟩
  let sp₁ : EF ⟶ AF := ⟨yoneda.map p₁⟩
  let sp₂ : EF ⟶ AF := ⟨yoneda.map p₂⟩
  let sg : AF ⟶ GF := ⟨g⟩
  have hg' : sp₁ ≫ sg = sp₂ ≫ sg := Sheaf.hom_ext hg
  have hdesc : q ≫ (hcol.desc (Cofork.ofπ sg hg')).hom = g :=
    congrArg (fun k : AF ⟶ GF ↦ k.hom) (Cofork.IsColimit.π_desc hcol (t := Cofork.ofπ sg hg'))
  refine ⟨(hcol.desc (Cofork.ofπ sg hg')).hom, hdesc, fun e he ↦ ?_⟩
  have hsh : (⟨e⟩ : FF ⟶ GF) = hcol.desc (Cofork.ofπ sg hg') :=
    Cofork.IsColimit.hom_ext hcol (Sheaf.hom_ext (he.trans hdesc.symm))
  exact congrArg (fun k : FF ⟶ GF ↦ k.hom) hsh

namespace LiftedEtalePresentation

variable {B S hS}

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} {C : SpacesEtale B S hS X}
  (P : LiftedEtalePresentation B S hS f C)

/-- The quotient map is surjective, by Stacks 02WW. -/
theorem surjective_toQuotient' : (surjectiveOnSite B S hS).presheaf P.toQuotient :=
  let := BigFppfOver.hasSheafify_type B S hS
  let := P.isEtaleEquivalenceRelation
  quotientMap_surjective_unconditional B S hS P.k₁ P.k₂

/-- The quotient map is étale, by Stacks 02WW. -/
theorem etale_toQuotient' : (etaleOnSite B S hS).presheaf P.toQuotient :=
  let := BigFppfOver.hasSheafify_type B S hS
  let := P.isEtaleEquivalenceRelation
  quotientMap_etale_unconditional B S hS P.k₁ P.k₂

end LiftedEtalePresentation

/-! ### Existence of a lifted étale presentation at a thickening -/

variable {f : X ⟶ Y} {C : SpacesEtale B S hS X}

end AlgebraicGeometry.Space

end
