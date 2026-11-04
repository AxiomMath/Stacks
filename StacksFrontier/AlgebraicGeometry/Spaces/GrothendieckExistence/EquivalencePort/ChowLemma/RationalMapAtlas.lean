module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChowLemma.GraphClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDenseAffineOpen
public import StacksFrontier.AlgebraicGeometry.C1573Port.Blowup.ProjectiveExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InvariantSubschemeDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.WeilDivisor

/-!
# A rational map on an algebraic space, read on an étale atlas

A rational map to projective space on an algebraic space `X`, defined on an open subspace
`u : h_D ⟶ X` by sections `s` of `𝒪_D`, is read on an affine étale atlas `φ : h_V ⟶ X` as an open
`U₀ ⊆ V` (the inverse image of the open), an ideal of `Γ(V, 𝒪_V)` whose basic opens cover `U₀`,
and the pulled back sections on `U₀`. This file proves the facts about these data used by
`AlgebraicGeometry.Space.C1573.exists_isBlowupAlong_comp_of_rationalMap`: the open over the open
subspace, the agreement of the data on the two legs of the relation `V ×_X V`, the description of
a chart of the graph closure over `U₀`, and the disjointness of the resulting centre from the
open subspace.

## Main results

* `AlgebraicGeometry.Space.C1573.exists_openSub_isPullback`: the inverse image of a representable
  open on an atlas is an open of the atlas.
* `AlgebraicGeometry.Space.C1573.atlasRelation_presheaf_map_app_eq`: functions pulled back from the
  open subspace agree on the relation.
* `AlgebraicGeometry.Space.C1573.isIso_morphismRestrict_of_isPullback_section`: over the open, the
  chart of a morphism with a section over `D` is the atlas.
* `AlgebraicGeometry.C1573.isClosedImmersion_lift_comp_snd`: `V ×_S Z ⟶ ℙᵐ_V` is a closed immersion
  for a closed immersion `Z ⟶ ℙᵐ_S`.
* `AlgebraicGeometry.Space.C1573.disjoint_subspacePointSet_of_preimage_eq`: a closed subspace whose
  inverse image on the atlas is a closed subscheme avoids the points outside its support.
-/

namespace AlgebraicGeometry.Scheme.Opens.C1573
end AlgebraicGeometry.Scheme.Opens.C1573
namespace AlgebraicGeometry.Scheme.C1573
end AlgebraicGeometry.Scheme.C1573
namespace AlgebraicGeometry.Scheme.IdealSheafData.C1573
end AlgebraicGeometry.Scheme.IdealSheafData.C1573
namespace AlgebraicGeometry.C1573
end AlgebraicGeometry.C1573
namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry.C1573 _root_.CategoryTheory.Limits.C1573
/-- Restricting a section along an equality of opens is the pullback along the comparison
isomorphism of the two open subschemes. -/
theorem Scheme.Opens.C1573.topIso_inv_map_eqToHom {Y : Scheme.{u}} {O O' : Y.Opens} (h : O = O')
    (y : Γ(Y, O)) :
    O'.topIso.inv (Y.presheaf.map (eqToHom h.symm).op y) =
      (Y.isoOfEq h.symm).hom.appTop (O.topIso.inv y) := by
  subst h
  simp [Scheme.isoOfEq_rfl]

/-- **Pulled back functions agree on a relation when the pulled back morphisms do.** Let
`p q : Y ⟶ V` have the same preimage of an open `U`, and let `ψ : U ⟶ W`. If the two
composites `p⁻¹U ⟶ U ⟶ W` and `q⁻¹U ⟶ U ⟶ W` agree, then the pullbacks along `p` and `q` of
any function pulled back from `W` agree. -/
theorem Scheme.C1573.presheaf_map_app_eq_of_comp_eq {Y V W : Scheme.{u}} (p q : Y ⟶ V) (U : V.Opens)
    (hpq : p ⁻¹ᵁ U = q ⁻¹ᵁ U) (ψ : U.toScheme ⟶ W)
    (e : (q ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ U).toScheme) (he : e ≫ (p ⁻¹ᵁ U).ι = (q ⁻¹ᵁ U).ι)
    (h : e ≫ (p ∣_ U) ≫ ψ = (q ∣_ U) ≫ ψ) (t : Γ(W, ⊤)) :
    Y.presheaf.map (eqToHom hpq.symm).op (p.app U (U.topIso.hom (ψ.appTop t))) =
      q.app U (U.topIso.hom (ψ.appTop t)) := by
  have hee : e = (Y.isoOfEq hpq.symm).hom := by
    rw [← cancel_mono (p ⁻¹ᵁ U).ι, he, Scheme.isoOfEq_hom_ι]
  subst hee
  have hinj : ∀ a b : Γ(Y, q ⁻¹ᵁ U), (q ⁻¹ᵁ U).topIso.inv a = (q ⁻¹ᵁ U).topIso.inv b → a = b :=
    fun a b hab => by
      have := congrArg (q ⁻¹ᵁ U).topIso.hom hab
      rwa [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at this
  apply hinj
  rw [Scheme.Opens.C1573.topIso_inv_map_eqToHom hpq,
    ← Stacks.ProjectiveExtension.C1573.morphismRestrict_appTop_topIso_inv,
    ← Stacks.ProjectiveExtension.C1573.morphismRestrict_appTop_topIso_inv]
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Iso.hom_inv_id_apply] using
    congrArg (fun m => m.appTop t) h

/-- On an affine scheme, the basic open of a global function in the ideal of an ideal sheaf
whose support is the complement of an open `U` lies in `U`. -/
theorem Scheme.IdealSheafData.C1573.basicOpen_le_of_mem_ideal_top {V : Scheme.{u}} [IsAffine V]
    (J : V.IdealSheafData) (U₀ : V.Opens) (hJ : (J.support : Set V) = (U₀ : Set V)ᶜ) :
    ∀ f ∈ J.ideal ⟨⊤, isAffineOpen_top V⟩, V.basicOpen f ≤ U₀ := by
  intro f hf y hy
  by_contra hyU
  have hy' : y ∈ J.support := by rwa [← SetLike.mem_coe, hJ]
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨⊤, isAffineOpen_top V⟩) trivial,
    Scheme.mem_zeroLocus_iff] at hy'
  exact hy' f hf hy

/-- On an affine scheme, the basic opens of the global functions in the ideal of an ideal sheaf
whose support is the complement of an open `U` cover `U`. -/
theorem Scheme.IdealSheafData.C1573.exists_mem_ideal_top {V : Scheme.{u}} [IsAffine V]
    (J : V.IdealSheafData) (U₀ : V.Opens) (hJ : (J.support : Set V) = (U₀ : Set V)ᶜ) :
    ∀ x ∈ U₀, ∃ f ∈ J.ideal ⟨⊤, isAffineOpen_top V⟩, x ∈ V.basicOpen f := by
  intro x hx
  by_contra h
  push Not at h
  have hx' : x ∈ J.support :=
    (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨⊤, isAffineOpen_top V⟩) trivial).2
      ((Scheme.mem_zeroLocus_iff _ _ _).2 h)
  rw [← SetLike.mem_coe, hJ] at hx'
  exact hx' hx

/-- **The vanishing ideal of the complement of an open extends equally along two étale maps
with the same preimage of the open.** -/
theorem Scheme.IdealSheafData.C1573.map_ideal_top_vanishingIdeal_eq {R V : Scheme.{u}} [IsAffine R]
    [IsAffine V] (U₀ : V.Opens) (p q : R ⟶ V) [Etale p] [Etale q] (hpq : p ⁻¹ᵁ U₀ = q ⁻¹ᵁ U₀) :
    Ideal.map p.appTop.hom ((Scheme.IdealSheafData.vanishingIdeal
        ⟨(U₀ : Set V)ᶜ, U₀.isOpen.isClosed_compl⟩).ideal ⟨⊤, isAffineOpen_top V⟩) =
      Ideal.map q.appTop.hom ((Scheme.IdealSheafData.vanishingIdeal
        ⟨(U₀ : Set V)ᶜ, U₀.isOpen.isClosed_compl⟩).ideal ⟨⊤, isAffineOpen_top V⟩) := by
  rw [← Stacks.IdealSheaf.ideal_comap_top_of_isAffine,
    ← Stacks.IdealSheaf.ideal_comap_top_of_isAffine,
    Scheme.IdealSheafData.comap_vanishingIdeal_of_etale p _
      ⟨((p ⁻¹ᵁ U₀ : R.Opens) : Set R)ᶜ, (p ⁻¹ᵁ U₀).isOpen.isClosed_compl⟩ rfl,
    Scheme.IdealSheafData.comap_vanishingIdeal_of_etale q _
      ⟨((q ⁻¹ᵁ U₀ : R.Opens) : Set R)ᶜ, (q ⁻¹ᵁ U₀).isOpen.isClosed_compl⟩ rfl]
  simp only [hpq]

/-- **Projective space over a scheme is the base change of projective space over another.**
For `g : A ⟶ A'`, the square formed by `A ×_ℤ P ⟶ A' ×_ℤ P` and the two first projections is
cartesian. -/
theorem C1573.isPullback_pullbackMap_terminal {A A' P : Scheme.{u}} (g : A ⟶ A') :
    IsPullback (pullback.map (terminal.from A) (terminal.from P) (terminal.from A')
        (terminal.from P) g (𝟙 P) (𝟙 _) (terminal.hom_ext _ _) (terminal.hom_ext _ _))
      (pullback.fst _ _) (pullback.fst _ _) g := by
  refine IsPullback.of_right ?_ (by rw [pullback.lift_fst])
    (IsPullback.of_hasPullback (terminal.from A') (terminal.from P)).flip
  rw [pullback.lift_snd, Category.comp_id,
    show g ≫ terminal.from A' = terminal.from A from terminal.hom_ext _ _]
  exact (IsPullback.of_hasPullback (terminal.from A) (terminal.from P)).flip

/-- **The graph of a morphism to a projective space, read in projective space over the chart.**
For a closed immersion `i : Z ⟶ ℙᵐ_S` over `S` and any `V ⟶ S`, the morphism
`V ×_S Z ⟶ ℙᵐ_V` is a closed immersion: it is the base change of `i`. -/
theorem C1573.isClosedImmersion_lift_comp_snd {V S Z P : Scheme.{u}} (pV : V ⟶ S) (pZ : Z ⟶ S)
    (i : Z ⟶ pullback (terminal.from S) (terminal.from P)) [IsClosedImmersion i]
    (hi : i ≫ pullback.fst _ _ = pZ) :
    IsClosedImmersion (pullback.lift (pullback.fst pV pZ)
      (pullback.snd pV pZ ≫ i ≫ pullback.snd _ _) (terminal.hom_ext _ _) :
        pullback pV pZ ⟶ pullback (terminal.from V) (terminal.from P)) := by
  set L : pullback pV pZ ⟶ pullback (terminal.from V) (terminal.from P) :=
    pullback.lift (pullback.fst pV pZ) (pullback.snd pV pZ ≫ i ≫ pullback.snd _ _)
      (terminal.hom_ext _ _) with hL
  set M : pullback (terminal.from V) (terminal.from P) ⟶
      pullback (terminal.from S) (terminal.from P) :=
    pullback.map _ _ _ _ pV (𝟙 P) (𝟙 _) (terminal.hom_ext _ _) (terminal.hom_ext _ _) with hM
  have hbot : IsPullback M (pullback.fst _ _) (pullback.fst _ _) pV :=
    isPullback_pullbackMap_terminal pV
  have sq : IsPullback (pullback.snd pV pZ) L i M := by
    refine IsPullback.of_bot ?_ ?_ hbot
    · rw [hL, pullback.lift_fst, hi]
      exact (IsPullback.of_hasPullback pV pZ).flip
    · apply pullback.hom_ext
      · rw [Category.assoc, hi, Category.assoc, hM, pullback.lift_fst, hL, pullback.lift_fst_assoc,
          pullback.condition]
      · rw [Category.assoc, Category.assoc, hM, pullback.lift_snd, Category.comp_id, hL,
          pullback.lift_snd]
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq inferInstance

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
  _root_.CategoryTheory.Limits.C1573
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Lifting through an open immersion of the site.** A morphism of the site whose image on
schemes lies in the image of an open immersion factors through it. -/
noncomputable def C1573.siteLift {A T T' : BigFppfOver B S hS} (j : T ⟶ T')
    [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)] (a : A ⟶ T')
    (h : Set.range ((BigFppfOver.toScheme B S hS).map a).base ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map j).base) : A ⟶ T :=
  Over.homMk (B.inclusion.preimage (X := A.left) (Y := T.left)
    (AlgebraicGeometry.IsOpenImmersion.lift ((BigFppfOver.toScheme B S hS).map j)
      ((BigFppfOver.toScheme B S hS).map a) h)) (by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, Functor.map_preimage]
    have hj : B.inclusion.map T.hom =
        (BigFppfOver.toScheme B S hS).map j ≫ B.inclusion.map T'.hom := by
      change _ = B.inclusion.map j.left ≫ _
      rw [← B.inclusion.map_comp, Over.w j]
    rw [hj, ← Category.assoc, AlgebraicGeometry.IsOpenImmersion.lift_fac]
    change B.inclusion.map a.left ≫ _ = _
    rw [← B.inclusion.map_comp, Over.w a])

/-- The image on schemes of `C1573.siteLift j a h` is the lift of the image of `a` through the open
immersion given by the image of `j`. -/
theorem C1573.toScheme_map_siteLift {A T T' : BigFppfOver B S hS} (j : T ⟶ T')
    [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)] (a : A ⟶ T')
    (h : Set.range ((BigFppfOver.toScheme B S hS).map a).base ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map j).base) :
    (BigFppfOver.toScheme B S hS).map (siteLift j a h) =
      AlgebraicGeometry.IsOpenImmersion.lift ((BigFppfOver.toScheme B S hS).map j)
        ((BigFppfOver.toScheme B S hS).map a) h :=
  B.inclusion.map_preimage _

/-- The lift `C1573.siteLift j a h` composed with `j` is `a`. -/
@[reassoc (attr := simp)]
theorem C1573.siteLift_comp {A T T' : BigFppfOver B S hS} (j : T ⟶ T')
    [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)] (a : A ⟶ T')
    (h : Set.range ((BigFppfOver.toScheme B S hS).map a).base ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map j).base) :
    siteLift j a h ≫ j = a := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [CategoryTheory.Functor.map_comp, toScheme_map_siteLift,
    AlgebraicGeometry.IsOpenImmersion.lift_fac]

/-- The inclusion of an open subscheme into a site object is an open immersion on schemes. -/
instance C1573.isOpenImmersion_toScheme_map_openSubHom (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (openSubHom A O)) := by
  rw [toScheme_map_openSubHom]
  exact inferInstanceAs (AlgebraicGeometry.IsOpenImmersion O.ι)

/-- The image on schemes of the inclusion of an open `O` into a site object is `O`. -/
theorem C1573.range_toScheme_map_openSubHom (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    Set.range ((BigFppfOver.toScheme B S hS).map (openSubHom A O)).base = (O : Set _) := by
  rw [toScheme_map_openSubHom]
  exact Scheme.Opens.range_ι O

/-- A morphism of the site whose image on schemes is an open immersion is a monomorphism. -/
private theorem mono_of_isOpenImmersion_toScheme_map {T T' : BigFppfOver B S hS} (j : T ⟶ T')
    [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)] : Mono j :=
  (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance

/-- **The inverse image of a representable open on an atlas, as an open of the atlas.** For an
open immersion `u : h_D ⟶ X` and any `φ : h_V ⟶ X`, the fibre product `D ×_X V` is an open
`U₀` of the scheme `V`, over the part of `V` lying over the image of `u`. -/
theorem C1573.exists_openSub_isPullback (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {D V : BigFppfOver B S hS} (u : yoneda.obj D ⟶ X) (hu : IsOpenImmersion B S hS u)
    (φ : yoneda.obj V ⟶ X) :
    ∃ (U₀ : ((BigFppfOver.toScheme B S hS).obj V).Opens) (ψ : openSub V U₀ ⟶ D),
      IsPullback (yoneda.map ψ) (yoneda.map (openSubHom V U₀)) u φ ∧
      (U₀ : Set ((BigFppfOver.toScheme B S hS).obj V)) =
        atlasPointSet B S hS φ (Set.range (pointsMap B S hS (yoneda.obj D) u)) := by
  set F := BigFppfOver.toScheme B S hS with hF
  have hrep := hu.rep
  set V' := hrep.pullback φ with hV'
  set k : V' ⟶ V := hrep.snd φ with hk
  set pr : V' ⟶ D := hrep.fst' φ with hpr
  have hsq : IsPullback (yoneda.map pr) (yoneda.map k) u φ := hrep.isPullback' φ
  have hko : AlgebraicGeometry.IsOpenImmersion (F.map k) := hu.property φ _ _ (hrep.isPullback φ)
  set U₀ := (F.map k).opensRange with hU₀
  have hr : Set.range (F.map (openSubHom V U₀)).base = Set.range (F.map k).base := by
    rw [range_toScheme_map_openSubHom, hU₀, Scheme.Hom.coe_opensRange]
  set e : V' ⟶ openSub V U₀ := siteLift (openSubHom V U₀) k hr.ge with he
  set e' : openSub V U₀ ⟶ V' := siteLift k (openSubHom V U₀) hr.le with he'
  have hek : e ≫ openSubHom V U₀ = k := siteLift_comp _ _ _
  have he'k : e' ≫ k = openSubHom V U₀ := siteLift_comp _ _ _
  have := mono_of_isOpenImmersion_toScheme_map k
  have := mono_of_isOpenImmersion_toScheme_map (openSubHom V U₀)
  have h1 : e ≫ e' = 𝟙 _ := (cancel_mono k).1 (by rw [Category.assoc, he'k, hek, Category.id_comp])
  have h2 : e' ≫ e = 𝟙 _ :=
    (cancel_mono (openSubHom V U₀)).1 (by rw [Category.assoc, hek, he'k, Category.id_comp])
  refine ⟨U₀, e' ≫ pr, ?_, ?_⟩
  · refine hsq.of_iso (yoneda.mapIso ⟨e, e', h1, h2⟩) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ (by simp) (by simp)
    · simp only [Functor.mapIso_hom, Iso.refl_hom, Category.comp_id, ← yoneda.map_comp,
        ← Category.assoc, h1, Category.id_comp]
    · simp only [Functor.mapIso_hom, Iso.refl_hom, Category.comp_id, ← yoneda.map_comp, hek]
  · rw [hU₀, Scheme.Hom.coe_opensRange]
    exact range_toScheme_map_eq_atlasPointSet B S hS hsq

section Relation

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V D : BigFppfOver B S hS}
  {φ : yoneda.obj V ⟶ X}
  (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)

include hs in
/-- **The open over an open subspace has the same preimage under both legs of the relation.** -/
theorem C1573.preimage_atlasRelationTarget_eq_of_eq_atlasPointSet
    (U₀ : ((BigFppfOver.toScheme B S hS).obj V).Opens) (T : Set (points B S hS X))
    (hU₀ : (U₀ : Set ((BigFppfOver.toScheme B S hS).obj V)) = atlasPointSet B S hS φ T) :
    (BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs) ⁻¹ᵁ U₀ =
      (BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs) ⁻¹ᵁ U₀ := by
  have hw := (isPullback_yoneda_map_atlasRelation B S hS hs).w
  ext x
  show ((BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs)).base x ∈
      (U₀ : Set _) ↔
    ((BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs)).base x ∈ (U₀ : Set _)
  rw [hU₀, mem_atlasPointSet_map_iff, mem_atlasPointSet_map_iff, hw]

include hs in
/-- **Functions pulled back from an open subspace agree on the relation.** Let `ψ : U₀ ⟶ D` be
the restriction over an open `U₀` of the atlas of a monomorphism `u : h_D ⟶ X`. Then the
pullbacks along the two legs of the relation of a function pulled back along `ψ` agree. -/
theorem C1573.atlasRelation_presheaf_map_app_eq (u : yoneda.obj D ⟶ X) [Mono u]
    (U₀ : ((BigFppfOver.toScheme B S hS).obj V).Opens) (ψ : openSub V U₀ ⟶ D)
    (hψ : yoneda.map ψ ≫ u = yoneda.map (openSubHom V U₀) ≫ φ)
    (hpq : (BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs) ⁻¹ᵁ U₀ =
      (BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs) ⁻¹ᵁ U₀)
    (t : Γ((BigFppfOver.toScheme B S hS).obj D, ⊤)) :
    ((BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hs)).presheaf.map
        (eqToHom hpq.symm).op
        (((BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs)).app U₀
          (U₀.topIso.hom (((BigFppfOver.toScheme B S hS).map ψ).appTop t))) =
      ((BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs)).app U₀
        (U₀.topIso.hom (((BigFppfOver.toScheme B S hS).map ψ).appTop t)) := by
  have hw : yoneda.map (atlasRelationTarget B S hS hs) ≫ φ =
      yoneda.map (atlasRelationSource B S hS hs) ≫ φ :=
    (isPullback_yoneda_map_atlasRelation B S hS hs).w
  have hr : Set.range ((BigFppfOver.toScheme B S hS).map (openSubHom (atlasRelation B S hS hs)
      ((BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs) ⁻¹ᵁ U₀))).base ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map (openSubHom (atlasRelation B S hS hs)
      ((BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs) ⁻¹ᵁ U₀))).base := by
    rw [range_toScheme_map_openSubHom, range_toScheme_map_openSubHom, hpq]
  have heA := siteLift_comp _ _ hr
  have key : siteLift _ _ hr ≫ openSubHomOfRestrict (atlasRelationTarget B S hS hs) U₀ ≫ ψ =
      openSubHomOfRestrict (atlasRelationSource B S hS hs) U₀ ≫ ψ := by
    apply yoneda.map_injective
    rw [← cancel_mono u]
    simp only [yoneda.map_comp, Category.assoc, hψ]
    rw [← yoneda.map_comp_assoc (openSubHomOfRestrict _ U₀), openSubHomOfRestrict_comp_openSubHom,
      ← yoneda.map_comp_assoc (openSubHomOfRestrict _ U₀), openSubHomOfRestrict_comp_openSubHom,
      yoneda.map_comp_assoc, yoneda.map_comp_assoc, hw, ← yoneda.map_comp_assoc, heA]
  refine Scheme.C1573.presheaf_map_app_eq_of_comp_eq _ _ U₀ hpq _
    ((BigFppfOver.toScheme B S hS).map (siteLift _ _ hr)) ?_ ?_ t
  · rw [← toScheme_map_openSubHom, ← toScheme_map_openSubHom]
    exact ((CategoryTheory.Functor.map_comp _ _ _).symm.trans
      (congrArg (BigFppfOver.toScheme B S hS).map heA))
  · have := congrArg (BigFppfOver.toScheme B S hS).map key
    simp only [CategoryTheory.Functor.map_comp] at this
    exact this

end Relation

section Section

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Over an open of the atlas lying over a section, the chart of the closure is the atlas.**
Let `TV = T₀ ×_X V` be the chart over an atlas `φ` of a morphism `τ : h_{T₀} ⟶ X` which is an
isomorphism over an open `u : h_D ⟶ X`, with section `σ`. Over an open `U₀` of `V` lying over
`D`, the projection `TV ⟶ V` is an isomorphism, and `TV ⟶ T₀` is the section. -/
theorem C1573.isIso_morphismRestrict_of_isPullback_section {T₀ TV V D : BigFppfOver B S hS}
    (τ : yoneda.obj T₀ ⟶ X) (pT : TV ⟶ T₀) (tV : TV ⟶ V) (φ : yoneda.obj V ⟶ X)
    (hsq : IsPullback (yoneda.map pT) (yoneda.map tV) τ φ) (σ : D ⟶ T₀) (u : yoneda.obj D ⟶ X)
    (hσ : IsPullback (yoneda.map σ) (𝟙 _) τ u)
    (U₀ : ((BigFppfOver.toScheme B S hS).obj V).Opens) (ψ : openSub V U₀ ⟶ D)
    (hψ : yoneda.map ψ ≫ u = yoneda.map (openSubHom V U₀) ≫ φ) :
    IsIso ((BigFppfOver.toScheme B S hS).map tV ∣_ U₀) ∧
      ((BigFppfOver.toScheme B S hS).map tV ⁻¹ᵁ U₀).ι ≫ (BigFppfOver.toScheme B S hS).map pT =
        ((BigFppfOver.toScheme B S hS).map tV ∣_ U₀) ≫ (BigFppfOver.toScheme B S hS).map ψ ≫
          (BigFppfOver.toScheme B S hS).map σ := by
  have hr : (openSubHomOfRestrict tV U₀) ≫ (openSubHom V U₀) =
      (openSubHom TV ((BigFppfOver.toScheme B S hS).map tV ⁻¹ᵁ U₀)) ≫ tV :=
    openSubHomOfRestrict_comp_openSubHom tV U₀
  have fac : (openSubHom TV ((BigFppfOver.toScheme B S hS).map tV ⁻¹ᵁ U₀)) ≫ pT =
      (openSubHomOfRestrict tV U₀) ≫ ψ ≫ σ := by
    have h3 : yoneda.map (openSubHomOfRestrict tV U₀) ≫ yoneda.map (openSubHom V U₀) =
        yoneda.map (openSubHom TV ((BigFppfOver.toScheme B S hS).map tV ⁻¹ᵁ U₀)) ≫
          yoneda.map tV := by
      rw [← yoneda.map_comp, hr, yoneda.map_comp]
    have hw : yoneda.map ((openSubHom TV ((BigFppfOver.toScheme B S hS).map tV ⁻¹ᵁ U₀)) ≫ pT) ≫
        τ = yoneda.map ((openSubHomOfRestrict tV U₀) ≫ ψ) ≫ u := by
      simp only [yoneda.map_comp, Category.assoc, hsq.w, hψ]
      rw [reassoc_of% h3]
      rfl
    have h1 := hσ.lift_fst _ _ hw
    have h2 := hσ.lift_snd _ _ hw
    rw [Category.comp_id] at h2
    apply yoneda.map_injective
    rw [← h1, h2, ← yoneda.map_comp, Category.assoc]
  have hw₀ : yoneda.map (ψ ≫ σ) ≫ τ = yoneda.map (openSubHom V U₀) ≫ φ := by
    rw [yoneda.map_comp, Category.assoc, hσ.w, Category.id_comp, hψ]
  set m₀ : openSub V U₀ ⟶ TV := yoneda.preimage (hsq.lift _ _ hw₀) with hm₀
  have hm₀t : m₀ ≫ tV = (openSubHom V U₀) := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hm₀, Functor.map_preimage, hsq.lift_snd]
  have hm₀p : m₀ ≫ pT = ψ ≫ σ := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hm₀, Functor.map_preimage, hsq.lift_fst]
  have hrange : Set.range ((BigFppfOver.toScheme B S hS).map m₀).base ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map
        (openSubHom TV ((BigFppfOver.toScheme B S hS).map tV ⁻¹ᵁ U₀))).base := by
    rw [range_toScheme_map_openSubHom]
    rintro _ ⟨x, rfl⟩
    show ((BigFppfOver.toScheme B S hS).map m₀ ≫ (BigFppfOver.toScheme B S hS).map tV).base x ∈ U₀
    rw [← CategoryTheory.Functor.map_comp, hm₀t]
    have h4 : ((BigFppfOver.toScheme B S hS).map (openSubHom V U₀)).base x ∈ (U₀ : Set _) :=
      (range_toScheme_map_openSubHom V U₀) ▸ Set.mem_range_self x
    exact h4
  set m := siteLift (openSubHom TV ((BigFppfOver.toScheme B S hS).map tV ⁻¹ᵁ U₀)) m₀ hrange
  have hm : m ≫ (openSubHom TV ((BigFppfOver.toScheme B S hS).map tV ⁻¹ᵁ U₀)) = m₀ :=
    siteLift_comp _ _ _
  have := mono_of_isOpenImmersion_toScheme_map (openSubHom V U₀)
  have := mono_of_isOpenImmersion_toScheme_map
    (openSubHom TV ((BigFppfOver.toScheme B S hS).map tV ⁻¹ᵁ U₀))
  have hmr : m ≫ (openSubHomOfRestrict tV U₀) = 𝟙 _ :=
    (cancel_mono (openSubHom V U₀)).1
      (by rw [Category.assoc, hr, ← Category.assoc, hm, hm₀t, Category.id_comp])
  have hrm : (openSubHomOfRestrict tV U₀) ≫ m = 𝟙 _ := by
    rw [← cancel_mono (openSubHom TV ((BigFppfOver.toScheme B S hS).map tV ⁻¹ᵁ U₀)),
      Category.assoc, hm, Category.id_comp]
    apply yoneda.map_injective
    apply hsq.hom_ext
    · rw [← yoneda.map_comp, ← yoneda.map_comp, Category.assoc, hm₀p, fac]
    · rw [← yoneda.map_comp, ← yoneda.map_comp, Category.assoc, hm₀t, hr]
  have : IsIso (openSubHomOfRestrict tV U₀) := ⟨m, hrm, hmr⟩
  have hFr : IsIso ((BigFppfOver.toScheme B S hS).map (openSubHomOfRestrict tV U₀)) := inferInstance
  refine ⟨hFr, ?_⟩
  have := congrArg (BigFppfOver.toScheme B S hS).map fac
  simp only [CategoryTheory.Functor.map_comp] at this
  rw [toScheme_map_openSubHom] at this
  exact this

end Section

/-- **A closed subspace whose inverse image on a surjective chart is a closed subscheme
avoids every set of points lying, on the chart, outside the support of that subscheme.** -/
theorem C1573.disjoint_subspacePointSet_of_preimage_eq (X : AlgebraicSpaces B S hS)
    {V : BigFppfOver B S hS} {φ : yoneda.obj V ⟶ X.1} (hφ : IsSurjective B S hS φ)
    (Z : ClosedSubspaces B S hS X.1) (J : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData)
    (hZ : Z.1.preimage φ = subschemePoints B S hS (Subobject.mk J.subschemeι))
    (T : Set (points B S hS X.1))
    (hT : ∀ v ∈ atlasPointSet B S hS φ T, v ∉ J.support) :
    Disjoint T (subspacePointSet B S hS X.1 Z.1) := by
  rw [Set.disjoint_left]
  rintro x hxT hxZ
  obtain ⟨y, rfl⟩ := hφ x
  have hy : y ∈ subspacePointSet B S hS (yoneda.obj V) (Z.1.preimage φ) := by
    rwa [subspacePointSet_preimage]
  have himm : _root_.AlgebraicGeometry.IsImmersion (Subobject.mk J.subschemeι).arrow := by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk]
    infer_instance
  rw [hZ, subschemePoints_eq_range_of_isImmersion B S hS _ himm] at hy
  set m : siteObjectOfImmersedSubobject B S hS _ himm ⟶ V :=
    Over.homMk (B.inclusion.preimage (Subobject.mk J.subschemeι).arrow) with hm
  have hFm : (BigFppfOver.toScheme B S hS).map m = (Subobject.mk J.subschemeι).arrow :=
    B.inclusion.map_preimage _
  have : Mono ((BigFppfOver.toScheme B S hS).map m) := by rw [hFm]; infer_instance
  have : Mono m := (BigFppfOver.toScheme B S hS).mono_of_mono_map this
  have : Mono (yoneda.map m) := inferInstance
  rw [subspacePointSet, range_pointsMap_ι_range, mem_range_pointsMap_yoneda_map_iff, hFm] at hy
  refine hT (pointsToScheme B S hS V y) ?_ ?_
  · rw [mem_atlasPointSet_iff]
    show pointsMap B S hS (yoneda.obj V) φ
      ((pointsEquivScheme B S hS V).symm (pointsEquivScheme B S hS V y)) ∈ T
    rw [Equiv.symm_apply_apply]
    exact hxT
  · rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
    rw [← Subobject.underlyingIso_hom_comp_eq_mk] at hy
    obtain ⟨z, hz⟩ := hy
    rw [← hz]
    exact ⟨_, rfl⟩

end AlgebraicGeometry.Space

end
