module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineCase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DescentEffective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceSize
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.CartesianFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSectionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyInjectiveSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleFull
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleFaithfulGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleFullGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalHomeomorphismRepresentable

/-!
# Charts and unique extensions for essential surjectivity on spaces-étale sites

Part of `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj`. Étaleness and
surjectivity as relative properties on the big fppf site, the transport of cartesian squares of
schemes to the site and to presheaves, the chart-level closed immersion of a surjective closed
immersion and the étale lift across it, unique extension of presheaf morphisms across a first-order
thickening and across a surjective closed immersion, and the charts and the two étale lifts of a
lifted étale presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Étaleness and surjectivity as relative properties on the site -/

/-- Surjectivity of scheme morphisms, read as a property of morphisms of the big fppf site. -/
abbrev SurjSite : MorphismProperty (BigFppfOver B S hS) :=
  MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)

private instance :
    MorphismProperty.IsMultiplicative (AlgebraicGeometry.FormalSpace.etaleProperty B S hS) where
  id_mem A := by
    change Etale ((BigFppfOver.toScheme B S hS).map (𝟙 A))
    simpa using (inferInstance : Etale (𝟙 ((BigFppfOver.toScheme B S hS).obj A)))
  comp_mem {A C D} p q hp hq := by
    have hp' : Etale ((BigFppfOver.toScheme B S hS).map p) := hp
    have hq' : Etale ((BigFppfOver.toScheme B S hS).map q) := hq
    change Etale ((BigFppfOver.toScheme B S hS).map (p ≫ q))
    rw [Functor.map_comp]
    infer_instance

private instance : MorphismProperty.IsMultiplicative (SurjSite B S hS) where
  id_mem A := by
    change Surjective ((BigFppfOver.toScheme B S hS).map (𝟙 A))
    simpa using (inferInstance : Surjective (𝟙 ((BigFppfOver.toScheme B S hS).obj A)))
  comp_mem {A C D} p q hp hq := by
    have hp' : Surjective ((BigFppfOver.toScheme B S hS).map p) := hp
    have hq' : Surjective ((BigFppfOver.toScheme B S hS).map q) := hq
    change Surjective ((BigFppfOver.toScheme B S hS).map (p ≫ q))
    rw [Functor.map_comp]
    infer_instance

private instance : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ k hk ↦ by
      have : IsIso k := hk
      exact (inferInstance : Etale ((BigFppfOver.toScheme B S hS).map k)))

private instance : (SurjSite B S hS).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ k hk ↦ by
      have : IsIso k := hk
      exact (inferInstance : Surjective ((BigFppfOver.toScheme B S hS).map k)))

/-- Étaleness on the site is stable under base change. -/
private theorem etaleSite_isStableUnderBaseChange :
    (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).IsStableUnderBaseChange where
  of_isPullback sq hg :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale)
      (sq.map (BigFppfOver.toScheme B S hS)) hg

/-! ### Transporting étaleness between its two spellings -/

/-- An étale morphism of presheaves out of a representable presheaf is relatively étale. -/
theorem etalePresheaf_of_isEtale_yonedaDomain {A : BigFppfOver B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : yoneda.obj A ⟶ F) (hg : IsEtale B S hS g) :
    (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf g := by
  simpa using hg A (𝟙 (yoneda.obj A)) (presheaf_etale_id B S hS A)

/-- Relative étaleness of presheaf morphisms is stable under base change. -/
theorem etalePresheaf_of_isPullback
    {A C D E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : A ⟶ C} {q : A ⟶ D} {g : C ⟶ E} {h : D ⟶ E}
    (sq : IsPullback p q g h)
    (hg : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf g) :
    (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf q :=
  (MorphismProperty.relative_isStableUnderBaseChange
    (AlgebraicGeometry.FormalSpace.etaleProperty B S hS)).of_isPullback sq hg

/-- Relative surjectivity of presheaf morphisms is stable under base change. -/
theorem surjectivePresheaf_of_isPullback
    {A C D E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : A ⟶ C} {q : A ⟶ D} {g : C ⟶ E} {h : D ⟶ E}
    (sq : IsPullback p q g h) (hg : (SurjSite B S hS).presheaf g) :
    (SurjSite B S hS).presheaf q :=
  (MorphismProperty.relative_isStableUnderBaseChange (SurjSite B S hS)).of_isPullback sq hg

/-! ### Transporting a cartesian square of schemes to the site and to presheaves -/

/-- A cartesian square of schemes between objects of the site is a cartesian square of the site:
given an isomorphism `e : pullback q j ≅ U` of the underlying schemes compatible with a morphism
`k : U ⟶ J` of the site, there is a morphism `p : U ⟶ V` of the site making the square of `p`,
`k`, `q` and `j` cartesian. -/
theorem exists_isPullback_of_iso_pullback_toScheme {U V Z J : BigFppfOver B S hS}
    (q : V ⟶ Z) (j : J ⟶ Z) (k : U ⟶ J)
    (e : pullback ((BigFppfOver.toScheme B S hS).map q)
        ((BigFppfOver.toScheme B S hS).map j) ≅ (BigFppfOver.toScheme B S hS).obj U)
    (he : e.hom ≫ (BigFppfOver.toScheme B S hS).map k =
      pullback.snd ((BigFppfOver.toScheme B S hS).map q)
        ((BigFppfOver.toScheme B S hS).map j)) :
    ∃ p : U ⟶ V, IsPullback p k q j := by
  have hinv : e.inv ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map q)
      ((BigFppfOver.toScheme B S hS).map j) = (BigFppfOver.toScheme B S hS).map k := by
    rw [← he, Iso.inv_hom_id_assoc]
  have hscheme : IsPullback
      (e.inv ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map q)
        ((BigFppfOver.toScheme B S hS).map j))
      ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map q)
      ((BigFppfOver.toScheme B S hS).map j) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ e.symm rfl hinv
    rw [Category.assoc, pullback.condition, ← Category.assoc, hinv]
  have hwq : (BigFppfOver.toScheme B S hS).map q ≫ B.inclusion.map Z.hom =
      B.inclusion.map V.hom :=
    (B.inclusion.map_comp q.left Z.hom).symm.trans (congrArg B.inclusion.map (Over.w q))
  have hwj : (BigFppfOver.toScheme B S hS).map j ≫ B.inclusion.map Z.hom =
      B.inclusion.map J.hom :=
    (B.inclusion.map_comp j.left Z.hom).symm.trans (congrArg B.inclusion.map (Over.w j))
  have hwk : (BigFppfOver.toScheme B S hS).map k ≫ B.inclusion.map J.hom =
      B.inclusion.map U.hom :=
    (B.inclusion.map_comp k.left J.hom).symm.trans (congrArg B.inclusion.map (Over.w k))
  have hw : (e.inv ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map q)
      ((BigFppfOver.toScheme B S hS).map j)) ≫ B.inclusion.map V.hom =
      B.inclusion.map U.hom := by
    rw [← hwq, ← Category.assoc, hscheme.w, Category.assoc, hwj, hwk]
  obtain ⟨p, hp⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS
    (e.inv ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map q)
      ((BigFppfOver.toScheme B S hS).map j)) hw
  refine ⟨p, IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) ?_⟩
  rw [hp]
  exact hscheme

/-- A cartesian square of schemes between objects of the site, pasted onto a cartesian square
exhibiting `J` as the base change along `g` of a chart `Z` of the target, is a cartesian square
of the site and a cartesian square of presheaves over `g`. -/
theorem exists_isPullback_presheaf_of_iso_pullback_toScheme
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g : F ⟶ G} {U V Z J : BigFppfOver B S hS}
    (q : V ⟶ Z) (j : J ⟶ Z) (k : U ⟶ J)
    (η : yoneda.obj J ⟶ F) (ζ : yoneda.obj Z ⟶ G)
    (hchart : IsPullback (yoneda.map j) η ζ g)
    (e : pullback ((BigFppfOver.toScheme B S hS).map q)
        ((BigFppfOver.toScheme B S hS).map j) ≅ (BigFppfOver.toScheme B S hS).obj U)
    (he : e.hom ≫ (BigFppfOver.toScheme B S hS).map k =
      pullback.snd ((BigFppfOver.toScheme B S hS).map q)
        ((BigFppfOver.toScheme B S hS).map j)) :
    ∃ p : U ⟶ V, IsPullback p k q j ∧
      IsPullback (yoneda.map p) (yoneda.map k ≫ η) (yoneda.map q ≫ ζ) g := by
  obtain ⟨p, hp⟩ := exists_isPullback_of_iso_pullback_toScheme B S hS q j k e he
  exact ⟨p, hp, (((hp.map yoneda).flip).paste_horiz hchart.flip).flip⟩

/-! ### The chart-level closed immersion of a thickening, and the étale lift across it -/

/-- For a monomorphism `f`, the inverse of `toRange` exhibits `f` as a base change of the inclusion
of its range. -/
private theorem isPullback_inv_toRange_range_ι {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    [Mono f.hom] :
    IsPullback (inv (Subfunctor.toRange f.hom)) (Subfunctor.range f.hom).ι f.hom (𝟙 Y.1) := by
  have hinv : inv (Subfunctor.toRange f.hom) ≫ f.hom = (Subfunctor.range f.hom).ι :=
    (cancel_epi (Subfunctor.toRange f.hom)).1 (by
      rw [IsIso.hom_inv_id_assoc]
      exact (Subfunctor.toRange_ι f.hom).symm)
  exact IsPullback.of_horiz_isIso ⟨by rwa [Category.comp_id]⟩

/-- For a monomorphism `f`, the preimage of its range along `τ` is a base change of `f` along
`τ`. -/
private theorem exists_isPullback_preimage_range {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    [Mono f.hom] {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (τ : F ⟶ Y.1) :
    ∃ q, IsPullback ((Subfunctor.range f.hom).preimage τ).ι q τ f.hom := by
  have hpaste := (Subfunctor.isPullback_preimage τ (Subfunctor.range f.hom)).paste_horiz
    (isPullback_inv_toRange_range_ι B S hS f)
  rw [Category.comp_id] at hpaste
  exact ⟨_, hpaste.flip⟩

/-- A surjective closed immersion `f` of algebraic spaces restricts to a surjective closed
immersion over any chart of the target: for a morphism `ζ` from an object `Z` of the site to
`Y`, the base change of `f` along `ζ` is represented by an object `J` of the site, and the
morphism `j : J ⟶ Z` is a closed immersion of schemes which is surjective on points. -/
theorem exists_chart_isClosedImmersion_of_isClosedImmersion_of_isSurjective
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hci : IsClosedImmersion B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom)
    (Z : BigFppfOver B S hS) (ζ : yoneda.obj Z ⟶ Y.1) :
    ∃ (J : BigFppfOver B S hS) (j : J ⟶ Z) (η : yoneda.obj J ⟶ X.1),
      IsPullback (yoneda.map j) η ζ f.hom ∧
        _root_.AlgebraicGeometry.IsClosedImmersion
          ((BigFppfOver.toScheme B S hS).map j) ∧
        Function.Surjective ((BigFppfOver.toScheme B S hS).map j).base := by
  have hsurjP : (SurjSite B S hS).presheaf f.hom :=
    presheafSurjective_of_isSurjective B S hS f.hom hci.rep hsurj
  have hj : _root_.AlgebraicGeometry.Surjective
      ((BigFppfOver.toScheme B S hS).map (hci.rep.snd ζ)) :=
    hsurjP.property ζ _ _ (hci.rep.isPullback ζ)
  exact ⟨hci.rep.pullback ζ, hci.rep.snd ζ, hci.rep.fst ζ, (hci.rep.isPullback ζ).flip,
    hci.property ζ _ _ (hci.rep.isPullback ζ), hj.surj⟩

/-- The inclusion `f` of a first-order thickening restricts to a surjective closed immersion over
any étale chart of the ambient space: for an étale chart `ζ` of `Y` by an object `Z` of the
site, the base change of `f` along `ζ` is represented by an object `J` of the site, and the
morphism `j : J ⟶ Z` is a closed immersion of schemes which is surjective on points. -/
theorem exists_chart_isClosedImmersion_of_isFirstOrderThickening
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Mono f.hom]
    (hT : IsFirstOrderThickening B S hS Y (Subfunctor.range f.hom))
    (Z : BigFppfOver B S hS) (ζ : yoneda.obj Z ⟶ Y.1) (hζ : IsEtale B S hS ζ) :
    ∃ (J : BigFppfOver B S hS) (j : J ⟶ Z) (η : yoneda.obj J ⟶ X.1),
      IsPullback (yoneda.map j) η ζ f.hom ∧
        _root_.AlgebraicGeometry.IsClosedImmersion
          ((BigFppfOver.toScheme B S hS).map j) ∧
        Function.Surjective ((BigFppfOver.toScheme B S hS).map j).base := by
  obtain ⟨J, j, p, hpb, hci, hker⟩ :=
    exists_nthOrderThickening_chart_pullback B S hS hT Z ζ
      ((isEtale_iff_presheaf_of_yoneda B S hS ζ).1 hζ)
  have hpaste := hpb.paste_horiz (isPullback_inv_toRange_range_ι B S hS f)
  rw [Category.comp_id] at hpaste
  exact ⟨J, j, p ≫ inv (Subfunctor.toRange f.hom), hpaste.flip, hci,
    (Stacks.Thickenings.isThickening_of_ker_pow_eq_bot _ hci hker).2⟩

/-- Let `j : J ⟶ Z` be a closed immersion of objects of the site which is surjective on points and
exhibits `J` as the base change along `g` of an étale chart `ζ` of the target, and let
`k : U ⟶ J` be étale. Then `U` lifts to an object `V` of the site étale over `Z`, and the lift is
cartesian both over `j` inside the site and over `g` in presheaves. -/
theorem exists_etaleLift_isPullback_of_chart
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g : F ⟶ G} {Z J U : BigFppfOver B S hS}
    (j : J ⟶ Z)
    [_root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (hj : Function.Surjective ((BigFppfOver.toScheme B S hS).map j).base)
    (η : yoneda.obj J ⟶ F) (ζ : yoneda.obj Z ⟶ G) (hζ : IsEtale B S hS ζ)
    (hchart : IsPullback (yoneda.map j) η ζ g)
    (k : U ⟶ J)
    (hk : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k)) :
    ∃ (V : BigFppfOver B S hS) (q : V ⟶ Z) (p : U ⟶ V),
      _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map q) ∧
        IsEtale B S hS (yoneda.map q ≫ ζ) ∧
        IsPullback p k q j ∧
        IsPullback (yoneda.map p) (yoneda.map k ≫ η) (yoneda.map q ≫ ζ) g := by
  obtain ⟨V, q, hqE, e, he⟩ :=
    Stacks.Etale.exists_bigFppfOver_etale_pullback_iso_of_isClosedImmersion_of_surjective
      B S hS j hj U ((BigFppfOver.toScheme B S hS).map k) hk
  obtain ⟨p, hsite, hpres⟩ :=
    exists_isPullback_presheaf_of_iso_pullback_toScheme B S hS q j k η ζ hchart e he
  refine ⟨V, q, p, hqE, isEtale_comp B S hS ?_ hζ, hsite, hpres⟩
  exact (isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map q)).2
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqE)

/-- Surjectivity after every representable base change is stable under composition on the
site. -/
theorem surjSite_presheaf_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : F ⟶ G} {q : G ⟶ H} (hp : (SurjSite B S hS).presheaf p)
    (hq : (SurjSite B S hS).presheaf q) : (SurjSite B S hS).presheaf (p ≫ q) :=
  have : MorphismProperty.IsStableUnderComposition (SurjSite B S hS) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  MorphismProperty.comp_mem _ _ _ hp hq

/-- Étaleness after every representable base change is stable under composition on the site. -/
theorem etaleSite_presheaf_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : F ⟶ G} {q : G ⟶ H} (hp : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf p)
    (hq : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf q) :
    (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf (p ≫ q) :=
  have : MorphismProperty.IsStableUnderComposition
      (AlgebraicGeometry.FormalSpace.etaleProperty B S hS) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  MorphismProperty.comp_mem _ _ _ hp hq

/-! ### Unique extension of presheaf morphisms across a first-order thickening -/

/-- Let `f : X ⟶ Y` be a monomorphism whose range is a first-order thickening of `Y`, let
`π : H ⟶ F` be a base change of `f` along a morphism `v : F ⟶ Y.1` with `F` an algebraic space,
and let `w : G ⟶ Y.1` be formally étale with `G` an algebraic space. Every morphism `H ⟶ G` over
`Y` extends uniquely to a morphism `F ⟶ G` over `Y`. -/
theorem existsUnique_hom_presheaf_of_isFirstOrderThickening
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Mono f.hom]
    (hT : IsFirstOrderThickening B S hS Y (Subfunctor.range f.hom))
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    {v : F ⟶ Y.1} {π : H ⟶ F} {q : H ⟶ X.1} (hpb : IsPullback π q v f.hom)
    (w : G ⟶ Y.1) (hw : FormallyEtale w)
    (d : H ⟶ G) (hd : d ≫ w = π ≫ v) :
    ∃! α : F ⟶ G, π ≫ α = d ∧ α ≫ w = v := by
  obtain ⟨q', hpaste⟩ := exists_isPullback_preimage_range B S hS f v
  obtain ⟨θ, hθiso, hθ⟩ :
      ∃ θ : H ⟶ ((Subfunctor.range f.hom).preimage v).toFunctor,
        IsIso θ ∧ θ ≫ ((Subfunctor.range f.hom).preimage v).ι = π :=
    ⟨(hpb.isoIsPullback _ _ hpaste).hom, inferInstance,
      IsPullback.isoIsPullback_hom_fst _ _ hpb hpaste⟩
  have := hθiso
  have hGp : IsFirstOrderThickening B S hS (⟨F, hF⟩ : AlgebraicSpaces B S hS)
      ((Subfunctor.range f.hom).preimage v) :=
    isFirstOrderThickening_preimage B S hS (Subfunctor.range f.hom)
      (ObjectProperty.homMk v : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ Y) hT
  have hsq : (inv θ ≫ d) ≫ w = ((Subfunctor.range f.hom).preimage v).ι ≫ v := by
    rw [Category.assoc, hd, ← hθ]
    simp
  obtain ⟨α, ⟨ha1, ha2⟩, hauniq⟩ :=
    FormallyEtale.existsUnique_lift_of_firstOrderThickening B S hS
      (T' := (⟨F, hF⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk w : (⟨G, hG⟩ : AlgebraicSpaces B S hS) ⟶ Y) hw
      ((Subfunctor.range f.hom).preimage v) hGp (inv θ ≫ d) v hsq
  refine ⟨α, ⟨?_, ha2⟩, fun β ⟨hb1, hb2⟩ ↦ hauniq β ⟨?_, hb2⟩⟩
  · rw [← hθ, Category.assoc, ha1, IsIso.hom_inv_id_assoc]
  · rw [← hb1, ← hθ]
    simp

/-- Two morphisms over `Y` into a formally étale algebraic space which agree after composing with
a base change of the inclusion of a first-order thickening are equal. -/
theorem hom_ext_presheaf_of_isFirstOrderThickening
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Mono f.hom]
    (hT : IsFirstOrderThickening B S hS Y (Subfunctor.range f.hom))
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    {v : F ⟶ Y.1} {π : H ⟶ F} {q : H ⟶ X.1} (hpb : IsPullback π q v f.hom)
    (w : G ⟶ Y.1) (hw : FormallyEtale w) (α β : F ⟶ G)
    (hα : α ≫ w = v) (hβ : β ≫ w = v) (h : π ≫ α = π ≫ β) : α = β := by
  obtain ⟨α₀, -, huniq⟩ := existsUnique_hom_presheaf_of_isFirstOrderThickening B S hS f hT hF hG
    hpb w hw (π ≫ α) (by rw [Category.assoc, hα])
  rw [huniq α ⟨rfl, hα⟩, huniq β ⟨h.symm, hβ⟩]

/-- For a monomorphism `f`, every morphism to `Y` from a presheaf has a base change of `f` over
it. -/
theorem exists_isPullback_range_of_mono {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    [Mono f.hom] {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (τ : F ⟶ Y.1) :
    ∃ (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (π : Q ⟶ F) (q : Q ⟶ X.1),
      IsPullback π q τ f.hom := by
  obtain ⟨q, hq⟩ := exists_isPullback_preimage_range B S hS f τ
  exact ⟨_, _, q, hq⟩

/-! ### Unique extension of presheaf morphisms across a surjective closed immersion -/

/-- A base change of a morphism of presheaves which is surjective on points is surjective on
points. -/
private theorem isSurjective_of_isPullback_presheaf
    {W Z F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : W ⟶ Z} {q : W ⟶ F} {g : Z ⟶ G}
    {h : F ⟶ G} (sq : IsPullback p q g h) (hh : IsSurjective B S hS h) :
    IsSurjective B S hS p := by
  intro z
  obtain ⟨x, hx⟩ := hh (pointsMap B S hS Z g z)
  obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS sq z x hx.symm
  exact ⟨w, hw⟩

/-- Two morphisms over `Y` into an algebraic space étale over `Y` which agree after composing with
a base change of a surjective morphism are equal. -/
private theorem hom_ext_presheaf_of_isSurjective {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hsurj : IsSurjective B S hS f.hom) {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H)
    {v : F ⟶ Y.1} {π : H ⟶ F} {q : H ⟶ X.1} (hpb : IsPullback π q v f.hom)
    (w : G ⟶ Y.1) (hw : IsEtale B S hS w) (α β : F ⟶ G)
    (hα : α ≫ w = v) (hβ : β ≫ w = v) (h : π ≫ α = π ≫ β) :
    α = β :=
  eq_of_isSurjective_of_isEtale B S hS Y.property hG hF hH w hw (hα.trans hβ.symm)
    (isSurjective_of_isPullback_presheaf B S hS hpb hsurj) h

/-- Let `f : X ⟶ Y` be integral, universally injective and surjective, let `π : H ⟶ F` be a base
change of `f` along a morphism `v : F ⟶ Y.1` with `F` an algebraic space, and let `w : G ⟶ Y.1`
be étale with `G` an algebraic space. Every morphism `H ⟶ G` over `Y` extends uniquely to a
morphism `F ⟶ G` over `Y`. -/
theorem existsUnique_hom_presheaf_of_isIntegralHom_of_universallyInjective
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hint : IsIntegralHom B S hS f.hom)
    (hui : UniversallyInjective B S hS f.hom) (hsurj : IsSurjective B S hS f.hom)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H)
    {v : F ⟶ Y.1} {π : H ⟶ F} {q : H ⟶ X.1} (hpb : IsPullback π q v f.hom)
    (w : G ⟶ Y.1) (hw : IsEtale B S hS w)
    (d : H ⟶ G) (hd : d ≫ w = π ≫ v) :
    ∃! α : F ⟶ G, π ≫ α = d ∧ α ≫ w = v := by
  obtain ⟨α, hα, hαv⟩ :=
    exists_hom_of_section_descent B S hS Y.property hF hH hG hw
      (isIntegralHom_of_isPullback B S hS hpb.flip hint)
      (universallyInjective_of_isPullback B S hS X.property hF Y.property f.hom v hui hpb)
      (isSurjective_of_isPullback_presheaf B S hS hpb hsurj) d hd
  exact ⟨α, ⟨hα, hαv⟩, fun β ⟨hb1, hb2⟩ ↦
    hom_ext_presheaf_of_isSurjective B S hS f hsurj hF hG hH hpb w hw β α hb2 hαv
      (hb1.trans hα.symm)⟩

/-- A closed immersion of presheaves is integral and universally injective. -/
theorem isIntegralHom_universallyInjective_of_isClosedImmersion
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ G) (hci : IsClosedImmersion B S hS g) :
    IsIntegralHom B S hS g ∧ UniversallyInjective B S hS g :=
  ⟨isIntegralHom_of_isClosedImmersion B S hS g hci,
    universallyInjective_of_mono B S hS g (mono_of_isClosedImmersion B S hS g hci)⟩

/-! ### Equivalence relations of the site, read in the slice over the base scheme -/

/-- An equivalence relation inside the site is an equivalence relation over the base scheme: its
image under `CategoryTheory.Over.post` of the inclusion of the site is an equivalence
relation. -/
theorem isEquivalenceRelation_post_inclusion {A D : BigFppfOver B S hS} {p₁ p₂ : A ⟶ D}
    (e : EquivalenceRelation p₁ p₂) :
    IsEquivalenceRelation ((Over.post B.inclusion).map p₁) ((Over.post B.inclusion).map p₂) := by
  let : HasTerminal B.Schemes := inferInstance
  let : HasFiniteLimits B.Schemes := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : PreservesLimitsOfShape WalkingCospan B.inclusion := by infer_instance
  let : PreservesLimitsOfShape (Discrete PEmpty) B.inclusion := by infer_instance
  let : PreservesFiniteLimits B.inclusion :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks B.inclusion
  let G : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  let : PreservesFiniteLimits G :=
    PreservesFiniteLimits.overPost (F := B.inclusion) (X := B.obj hS)
  let : PreservesLimitsOfShape WalkingCospan G := by infer_instance
  let : PreservesLimitsOfShape (Discrete WalkingPair) G := by infer_instance
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let p : A ⟶ D ⨯ D := prod.lift p₁ p₂
  have hp : Mono p := by
    constructor
    intro Z x y hxy
    apply e.right_cancellation x y
    · simpa [p] using congrArg (fun k => k ≫ prod.fst) hxy
    · simpa [p] using congrArg (fun k => k ≫ prod.snd) hxy
  let : Mono (G.map p) := preserves_mono_of_preservesLimit G p
  let eprod : G.obj (D ⨯ D) ≅ G.obj D ⨯ G.obj D := PreservesLimitPair.iso G D D
  let : JointlyMono₂ (G.map p₁) (G.map p₂) := by
    constructor
    intro Z x y h₁ h₂
    apply (cancel_mono (G.map p)).mp
    apply (cancel_mono eprod.hom).mp
    apply prod.hom_ext
    · simpa [eprod, p, PreservesLimitPair.iso_hom, ← G.map_comp] using h₁
    · simpa [eprod, p, PreservesLimitPair.iso_hom, ← G.map_comp] using h₂
  exact EquivalenceRelation.isEquivalenceRelation
    { __ := e.toReflexiveRelation.map G
      __ := e.toSymmetricRelation.map G
      __ := e.toTransitiveRelation.map G }


variable {X Y : AlgebraicSpaces B S hS}

/-- A monomorphism whose range is a thickening of the target is a surjective closed immersion. -/
theorem isClosedImmersion_isSurjective_of_isThickening_range (f : X ⟶ Y) [Mono f.hom]
    (hT : IsThickening B S hS Y (Subfunctor.range f.hom)) :
    IsClosedImmersion B S hS f.hom ∧ IsSurjective B S hS f.hom := by
  refine ⟨?_, ?_⟩
  · rw [← Subfunctor.toRange_ι f.hom]
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2 hT.1.2
  · have h := hT.2.comp (pointsMap_surjective_of_isIso B S hS (Subfunctor.toRange f.hom))
    rwa [← pointsMap_comp, Subfunctor.toRange_ι] at h

/-! ### The charts and the two étale lifts of a lifted étale presentation -/

/-- For a surjective closed immersion `f` and an object `C` of the spaces-étale site of `X`, there
are objects `V`, `W`, `U`, `R` of the site, structure morphisms `v`, `w` making `V` and `W` étale
over `Y`, a surjective étale chart `c` of `C` by `U` with kernel pair `(s, t)` by `R`, and
projections `a : U ⟶ V`, `b : R ⟶ W` exhibiting `U` and `R` as the base changes of `V` and of
`W` along `f`. -/
theorem exists_liftedEtalePresentation_charts_of_isClosedImmersion_of_isSurjective (f : X ⟶ Y)
    (hci : IsClosedImmersion B S hS f.hom) (hsurj : IsSurjective B S hS f.hom)
    (C : SpacesEtale B S hS X) :
    ∃ (V W U R : BigFppfOver B S hS) (v : yoneda.obj V ⟶ Y.1) (w : yoneda.obj W ⟶ Y.1)
        (c : yoneda.obj U ⟶ C.1.left.1) (a : U ⟶ V) (b : R ⟶ W) (s t : R ⟶ U),
      IsEtale B S hS v ∧ IsEtale B S hS w ∧ IsEtale B S hS c ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) c ∧
        IsPullback (yoneda.map a) (c ≫ C.1.hom.hom) v f.hom ∧
        IsPullback (yoneda.map t) (yoneda.map s) c c ∧
        IsPullback (yoneda.map b) (yoneda.map t ≫ c ≫ C.1.hom.hom) w f.hom := by
  obtain ⟨Z, ζ, hζS, hζE⟩ := Y.2.exists_atlas
  have hζI : IsEtale B S hS ζ := isEtale_of_presheaf_etale B S hS hζE
  obtain ⟨J, j, η, hchart, hjci, hjsurj⟩ :=
    exists_chart_isClosedImmersion_of_isClosedImmersion_of_isSurjective B S hS f hci hsurj Z ζ
  have : _root_.AlgebraicGeometry.IsClosedImmersion
    ((BigFppfOver.toScheme B S hS).map j) := hjci
  have hηE : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf η :=
    etalePresheaf_of_isPullback B S hS hchart hζE
  have hηS : (SurjSite B S hS).presheaf η := surjectivePresheaf_of_isPullback B S hS hchart hζS
  obtain ⟨U', c', hc'S, hc'E⟩ := C.1.left.2.exists_atlas
  have hg₀E : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf (c' ≫ C.1.hom.hom) :=
    presheaf_etale_of_isEtale B S hS
      (isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS hc'E) C.2)
  obtain ⟨U, κ, m, hUpb⟩ :
      ∃ (U : BigFppfOver B S hS) (κ : yoneda.obj U ⟶ yoneda.obj J) (m : U ⟶ U'),
        IsPullback κ (yoneda.map m) η (c' ≫ C.1.hom.hom) :=
    ⟨_, _, _, hηE.rep.isPullback (c' ≫ C.1.hom.hom)⟩
  obtain ⟨k, hkmap⟩ : ∃ k : U ⟶ J, yoneda.map k = κ :=
    ⟨yoneda.preimage κ, yoneda.map_preimage κ⟩
  rw [← hkmap] at hUpb
  have hmE : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf (yoneda.map m) :=
    etalePresheaf_of_isPullback B S hS hUpb hηE
  have hmS : (SurjSite B S hS).presheaf (yoneda.map m) :=
    surjectivePresheaf_of_isPullback B S hS hUpb hηS
  have hkE : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ k).1
      (etalePresheaf_of_isPullback B S hS hUpb.flip hg₀E)
  have hcE : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf (yoneda.map m ≫ c') :=
    etaleSite_presheaf_comp B S hS hmE hc'E
  have hcS : (SurjSite B S hS).presheaf (yoneda.map m ≫ c') :=
    surjSite_presheaf_comp B S hS hmS hc'S
  have hcw : yoneda.map k ≫ η = (yoneda.map m ≫ c') ≫ C.1.hom.hom := by
    rw [Category.assoc]; exact hUpb.w
  obtain ⟨R, s₀, t₀, hker⟩ :
      ∃ (R : BigFppfOver B S hS) (s t : R ⟶ U),
        IsPullback (yoneda.map s) (yoneda.map t) (yoneda.map m ≫ c') (yoneda.map m ≫ c') :=
    ⟨hcE.rep.pullback _, yoneda.preimage (hcE.rep.fst _), hcE.rep.snd _, by
      rw [yoneda.map_preimage]; exact hcE.rep.isPullback _⟩
  have htE : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (s₀ ≫ k)) := by
    have h₁ : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map s₀) :=
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ s₀).1
        (etalePresheaf_of_isPullback B S hS hker.flip hcE)
    have : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k) := hkE
    rw [Functor.map_comp]
    infer_instance
  obtain ⟨V, q, a, -, hvE, -, hpresA⟩ :=
    exists_etaleLift_isPullback_of_chart B S hS j hjsurj η ζ hζI hchart k hkE
  obtain ⟨W, qW, b, -, hwE, -, hpresB⟩ :=
    exists_etaleLift_isPullback_of_chart B S hS j hjsurj η ζ hζI hchart (s₀ ≫ k) htE
  refine ⟨V, W, U, R, yoneda.map q ≫ ζ, yoneda.map qW ≫ ζ, yoneda.map m ≫ c', a, b, t₀, s₀,
    hvE, hwE, isEtale_of_presheaf_etale B S hS hcE, hcS, ?_, hker, ?_⟩
  · rwa [← hcw]
  · rw [Functor.map_comp, Category.assoc, hcw] at hpresB
    simpa only [Category.assoc] using hpresB

/-- For the inclusion `f` of a first-order thickening and an object `C` of the spaces-étale site
of `X`, there are objects `V`, `W`, `U`, `R` of the site, structure morphisms `v`, `w` making
`V` and `W` étale over `Y`, a surjective étale chart `c` of `C` by `U` with kernel pair `(s, t)`
by `R`, and projections `a : U ⟶ V`, `b : R ⟶ W` exhibiting `U` and `R` as the base changes of
`V` and of `W` along `f`. -/
theorem exists_liftedEtalePresentation_charts (f : X ⟶ Y) [Mono f.hom]
    (hT : IsFirstOrderThickening B S hS Y (Subfunctor.range f.hom))
    (C : SpacesEtale B S hS X) :
    ∃ (V W U R : BigFppfOver B S hS) (v : yoneda.obj V ⟶ Y.1) (w : yoneda.obj W ⟶ Y.1)
        (c : yoneda.obj U ⟶ C.1.left.1) (a : U ⟶ V) (b : R ⟶ W) (s t : R ⟶ U),
      IsEtale B S hS v ∧ IsEtale B S hS w ∧ IsEtale B S hS c ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) c ∧
        IsPullback (yoneda.map a) (c ≫ C.1.hom.hom) v f.hom ∧
        IsPullback (yoneda.map t) (yoneda.map s) c c ∧
        IsPullback (yoneda.map b) (yoneda.map t ≫ c ≫ C.1.hom.hom) w f.hom :=
  have h := isClosedImmersion_isSurjective_of_isThickening_range B S hS f
    (hT.isThickening B S hS)
  exists_liftedEtalePresentation_charts_of_isClosedImmersion_of_isSurjective B S hS f h.1 h.2 C

end AlgebraicGeometry.Space

end
