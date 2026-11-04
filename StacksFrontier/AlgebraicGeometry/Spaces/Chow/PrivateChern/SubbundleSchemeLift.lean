module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.BundleEmbeddingTwist
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.OverQuotients

/-!
# The points of `𝐏(𝒬) ⊂ 𝐏(𝒢)` on which the section of `𝒪(1) ⊗ π^*ℳ^{-1}` vanishes

Let `X` be a scheme, `ℳ ⟶ 𝒢 ⟶ 𝒬 ⟶ 0` exact with `g : 𝒢 ⟶ 𝒬` a surjection of finite locally free
modules, and `ι : 𝐏(𝒬) ⟶ 𝐏(𝒢)` the closed immersion of projective bundles. **A morphism
`t : T ⟶ 𝐏(𝒢)` along which `π^*ℳ ⟶ π^*𝒢 ⟶ 𝒪(1)` pulls back to zero factors through `ι`.**

Indeed `t` is classified by the invertible quotient `f^*𝒢 ⟶ t^*𝒪(1)` of Stacks 01O4, for
`f = π ∘ t`; it kills `f^*ℳ`, so it factors through the cokernel `f^*𝒬` of `f^*ℳ ⟶ f^*𝒢`,
and the quotient of `f^*𝒬` so obtained classifies a morphism `t' : T ⟶ 𝐏(𝒬)`. The composite
`ι ∘ t'` classifies the composite quotient `f^*𝒢 ⟶ f^*𝒬 ⟶ t'^*𝒪(1)`
(`AlgebraicGeometry.Space.PrivateChern.exists_situationEmbedding_twistIso`), which is the quotient
of `t`, so `ι ∘ t' = t`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.exists_comp_situationEmbedding_eq`: the factorization.
* `AlgebraicGeometry.Space.PrivateChern.quotientMapAlong_comp_of_iso`: the quotient induced along
  `t' ≫ ι` is the one induced along `t'` precomposed with `g`, when `ι^*u` is `u'` precomposed with
  `g` up to an isomorphism of the targets.

## Implementation notes

The coherences between the comparisons of iterated inverse images are proved at variable
morphisms and modules, and the classifying morphisms are compared through invertible quotients
whose targets are spelled as the targets of the pulled-back tautological quotients.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback

section Coherence

variable {X P P' T : Scheme.{u}} (π : P ⟶ X) (π' : P' ⟶ X) (ι : P' ⟶ P) (hι : ι ≫ π = π')
  {F F' : X.Modules} (g : F ⟶ F') {L : P.Modules} {L' : P'.Modules}
  (u : (Scheme.Modules.pullback π).obj F ⟶ L) (u' : (Scheme.Modules.pullback π').obj F' ⟶ L')
  (θ : (Scheme.Modules.pullback ι).obj L ≅ L')

include hι in
/-- **The quotient induced along `t' ≫ ι`**, when `ι^*u` is `u'` precomposed with `g` through an
isomorphism `θ` of the targets: it is the quotient induced along `t'` by `u'`, precomposed with
`g`. -/
theorem quotientMapAlong_comp_of_iso
    (hθ : (Scheme.Modules.pullback ι).map u ≫ θ.hom =
      (Scheme.Modules.pullbackComp ι π).hom.app F ≫ (Scheme.Modules.pullbackCongr hι).hom.app F ≫
        (Scheme.Modules.pullback π').map g ≫ u') (t' : T ⟶ P') :
    Stacks.Modules.quotientMapAlong π u (t' ≫ ι) ≫
        (Scheme.Modules.pullbackComp t' ι).inv.app L ≫ (Scheme.Modules.pullback t').map θ.hom =
      (Scheme.Modules.pullbackCongr (by rw [Category.assoc, hι])).hom.app F ≫
        (Scheme.Modules.pullback (t' ≫ π')).map g ≫ Stacks.Modules.quotientMapAlong π' u' t' := by
  subst hι
  rw [Stacks.Modules.quotientMapAlong_comp, Stacks.Modules.quotientMapAlong_eq,
    Stacks.Modules.quotientMapAlong_eq]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp]
  rw [hθ]
  simp only [Functor.map_comp, Iso.inv_hom_id_app_assoc, Scheme.Modules.pullbackCongr,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  have hnat := (Scheme.Modules.pullbackComp t' (ι ≫ π)).inv.naturality g
  dsimp only [Functor.comp_map] at hnat
  rw [reassoc_of% hnat]

omit hι in
/-- `Scheme.Modules.pullbackCongr` is natural in the module. -/
theorem pullbackCongr_hom_app_naturality {a b : T ⟶ X} (e : a = b) (k : F ⟶ F') :
    (Scheme.Modules.pullbackCongr e).hom.app F ≫ (Scheme.Modules.pullback b).map k =
      (Scheme.Modules.pullback a).map k ≫ (Scheme.Modules.pullbackCongr e).hom.app F' := by
  subst e
  simp [Scheme.Modules.pullbackCongr]

omit hι in
/-- Composites of `Scheme.Modules.pullbackCongr` are `Scheme.Modules.pullbackCongr`. -/
theorem pullbackCongr_inv_app_hom_app {a b c : T ⟶ X} (e : b = a) (e' : b = c) (e'' : a = c) :
    (Scheme.Modules.pullbackCongr e).inv.app F ≫ (Scheme.Modules.pullbackCongr e').hom.app F =
      (Scheme.Modules.pullbackCongr e'').hom.app F := by
  subst e e'
  simp [Scheme.Modules.pullbackCongr]

omit hι in
/-- `Scheme.Modules.pullbackCongr e` is the inverse of `Scheme.Modules.pullbackCongr e.symm`. -/
theorem pullbackCongr_hom_app_eq_inv_app {a b : T ⟶ X} (e : a = b) :
    (Scheme.Modules.pullbackCongr e).hom.app F =
      (Scheme.Modules.pullbackCongr e.symm).inv.app F := by
  subst e
  rfl

include hι in
/-- `AlgebraicGeometry.Space.PrivateChern.quotientMapAlong_comp_of_iso` read out of `f^*F` for
`f = t ≫ π`, through the identifications `(t' ≫ ι) ≫ π = f` and `t' ≫ π' = f`. -/
theorem quotientMapAlong_comp_of_iso_of_eq
    (hθ : (Scheme.Modules.pullback ι).map u ≫ θ.hom =
      (Scheme.Modules.pullbackComp ι π).hom.app F ≫ (Scheme.Modules.pullbackCongr hι).hom.app F ≫
        (Scheme.Modules.pullback π').map g ≫ u') {t : T ⟶ P} (t' : T ⟶ P')
    (h₁ : (t' ≫ ι) ≫ π = t ≫ π) (h₂ : t' ≫ π' = t ≫ π) :
    (Scheme.Modules.pullbackCongr h₁).inv.app F ≫ Stacks.Modules.quotientMapAlong π u (t' ≫ ι) ≫
        (Scheme.Modules.pullbackComp t' ι).inv.app L ≫ (Scheme.Modules.pullback t').map θ.hom =
      (Scheme.Modules.pullback (t ≫ π)).map g ≫ (Scheme.Modules.pullbackCongr h₂).inv.app F' ≫
        Stacks.Modules.quotientMapAlong π' u' t' := by
  rw [quotientMapAlong_comp_of_iso π π' ι hι g u u' θ hθ t', ← Category.assoc,
    pullbackCongr_inv_app_hom_app _ _ h₂.symm, ← Category.assoc,
    pullbackCongr_hom_app_naturality, Category.assoc, pullbackCongr_hom_app_eq_inv_app]

end Coherence

variable {X : Scheme.{u}} {M G Q : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} Q] (g : G ⟶ Q) [Epi g]
  [G.IsQuasicoherent] [Q.IsQuasicoherent] (m : M ⟶ G) (hmg : m ≫ g = 0)
  (hcok : IsColimit (CokernelCofork.ofπ g hmg))

include hcok in
/-- **A morphism into `𝐏(𝒢)` along which `π^*ℳ ⟶ 𝒪(1)` vanishes factors through `𝐏(𝒬)`.** -/
theorem exists_comp_situationEmbedding_eq {T : Scheme.{u}}
    (t : T ⟶ Stacks.RelativeProj.projectiveBundle X G)
    (ht : (Scheme.Modules.pullback t).map
      ((Scheme.Modules.pullback (Stacks.RelativeProj.projectiveBundleToBase X G)).map m ≫
        Stacks.RelativeProj.tautologicalDatumUniv G) = 0) :
    ∃ t' : T ⟶ Stacks.RelativeProj.projectiveBundle X Q, t' ≫ situationEmbedding g = t := by
  have h0 : (Scheme.Modules.pullback (t ≫ Stacks.RelativeProj.projectiveBundleToBase X G)).map m ≫
      (Stacks.RelativeProj.tautologicalDatum G).overQuotientMap t rfl = 0 := by
    rw [Stacks.RelativeProj.TautologicalDatum.overQuotientMap]
    have hnat := (Scheme.Modules.pullbackComp t
      (Stacks.RelativeProj.projectiveBundleToBase X G)).inv.naturality m
    dsimp only [Functor.comp_map] at hnat
    simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app,
      Category.id_comp]
    rw [← Category.assoc, hnat, Category.assoc, ← Functor.map_comp]
    show _ ≫ (Scheme.Modules.pullback t).map
      ((Scheme.Modules.pullback (Stacks.RelativeProj.projectiveBundleToBase X G)).map m ≫
        Stacks.RelativeProj.tautologicalDatumUniv G) = 0
    rw [ht, comp_zero]
  -- the quotient factors through the cokernel `f^*𝒬`
  have : (Scheme.Modules.pullback
      (t ≫ Stacks.RelativeProj.projectiveBundleToBase X G)).IsLeftAdjoint :=
    ⟨_, ⟨Scheme.Modules.pullbackPushforwardAdjunction _⟩⟩
  have hcok' := CokernelCofork.mapIsColimit _ hcok
    (Scheme.Modules.pullback (t ≫ Stacks.RelativeProj.projectiveBundleToBase X G))
  obtain ⟨Q', hQ'⟩ := CokernelCofork.IsColimit.desc' hcok'
    ((Stacks.RelativeProj.tautologicalDatum G).overQuotientMap t rfl) h0
  change (Scheme.Modules.pullback (t ≫ Stacks.RelativeProj.projectiveBundleToBase X G)).map g ≫ Q' =
    (Stacks.RelativeProj.tautologicalDatum G).overQuotientMap t rfl at hQ'
  have hQ'epi : Epi Q' := epi_of_epi_fac hQ'
  -- the quotient of `f^*𝒬` classifies `t'`
  let IQ : Stacks.Divisors.InvertibleQuotient T
      ((Scheme.Modules.pullback (t ≫ Stacks.RelativeProj.projectiveBundleToBase X G)).obj Q) :=
    { L := ((Stacks.RelativeProj.tautologicalDatum G).overQuotient
        ((Scheme.Modules.pullback (t ≫ Stacks.RelativeProj.projectiveBundleToBase X G)).obj G)
        (Iso.refl _) t rfl).L
      invertible := ((Stacks.RelativeProj.tautologicalDatum G).overQuotient
        ((Scheme.Modules.pullback (t ≫ Stacks.RelativeProj.projectiveBundleToBase X G)).obj G)
        (Iso.refl _) t rfl).invertible
      q := Q'
      epi := hQ'epi }
  let e := Stacks.RelativeProj.projectiveBundleOverEquiv (X := X) (F := Q)
    (f := t ≫ Stacks.RelativeProj.projectiveBundleToBase X G)
    ((Scheme.Modules.pullback (t ≫ Stacks.RelativeProj.projectiveBundleToBase X G)).obj Q)
    (Iso.refl _)
  obtain ⟨t', ht'⟩ : ∃ t', e t' = Quotient.mk _ IQ := ⟨e.symm _, e.apply_symm_apply _⟩
  obtain ⟨α, hα'⟩ : ∃ α : (Scheme.Modules.pullback t'.1).obj
        (Stacks.RelativeProj.tautologicalDatum Q).twist ≅
        (Scheme.Modules.pullback t).obj (Stacks.RelativeProj.tautologicalDatum G).twist,
      (Stacks.RelativeProj.tautologicalDatum Q).overQuotientMap t'.1 t'.2 ≫ α.hom = Q' := by
    obtain ⟨α, hα⟩ := (Stacks.RelativeProj.projectiveBundleOverEquiv_eq_iff _ _ t' IQ).1 ht'
    rw [Iso.refl_hom, Category.id_comp] at hα
    exact ⟨α, hα⟩
  clear_value e
  clear ht'
  refine ⟨t'.1, ?_⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : (Scheme.Modules.pullback (situationEmbedding g)).obj
        (Stacks.RelativeProj.tautologicalDatum G).twist ≅
        (Stacks.RelativeProj.tautologicalDatum Q).twist,
      (Scheme.Modules.pullback (situationEmbedding g)).map
          (Stacks.RelativeProj.tautologicalDatum G).univ ≫ θ.hom =
        (Scheme.Modules.pullbackComp (situationEmbedding g)
            (Stacks.RelativeProj.projectiveBundleToBase X G)).hom.app G ≫
          (Scheme.Modules.pullbackCongr (situationEmbedding_comp_toBase' g)).hom.app G ≫
          (Scheme.Modules.pullback (Stacks.RelativeProj.projectiveBundleToBase X Q)).map g ≫
          (Stacks.RelativeProj.tautologicalDatum Q).univ :=
    exists_situationEmbedding_twistIso g
  have ht'' : (t'.1 ≫ situationEmbedding g) ≫ Stacks.RelativeProj.projectiveBundleToBase X G =
      t ≫ Stacks.RelativeProj.projectiveBundleToBase X G := by
    rw [Category.assoc, situationEmbedding_comp_toBase', t'.2]
  let eG := Stacks.RelativeProj.projectiveBundleOverEquiv (X := X) (F := G)
    (f := t ≫ Stacks.RelativeProj.projectiveBundleToBase X G)
    ((Scheme.Modules.pullback (t ≫ Stacks.RelativeProj.projectiveBundleToBase X G)).obj G)
    (Iso.refl _)
  have K : (Stacks.RelativeProj.tautologicalDatum G).overQuotientMap (t'.1 ≫ situationEmbedding g)
        ht'' ≫ (Scheme.Modules.pullbackComp t'.1 (situationEmbedding g)).inv.app
          (Stacks.RelativeProj.tautologicalDatum G).twist ≫
        (Scheme.Modules.pullback t'.1).map θ.hom =
      (Scheme.Modules.pullback (t ≫ Stacks.RelativeProj.projectiveBundleToBase X G)).map g ≫
        (Stacks.RelativeProj.tautologicalDatum Q).overQuotientMap t'.1 t'.2 := by
    rw [Stacks.RelativeProj.TautologicalDatum.overQuotientMap_eq,
      Stacks.RelativeProj.TautologicalDatum.overQuotientMap_eq, Category.assoc]
    exact quotientMapAlong_comp_of_iso_of_eq _ _ _ (situationEmbedding_comp_toBase' g) g _ _ θ hθ
      t'.1 ht'' t'.2
  -- the invertible quotient classifying `t`, spelled on `t^*𝒪(1)`
  let IQG : Stacks.Divisors.InvertibleQuotient T
      ((Scheme.Modules.pullback (t ≫ Stacks.RelativeProj.projectiveBundleToBase X G)).obj G) :=
    { L := (Scheme.Modules.pullback t).obj (Stacks.RelativeProj.tautologicalDatum G).twist
      invertible := IQ.invertible
      q := (Stacks.RelativeProj.tautologicalDatum G).overQuotientMap t rfl
      epi := Stacks.RelativeProj.TautologicalDatum.epi_overQuotientMap _ _ _ }
  obtain ⟨α', hα'def⟩ : ∃ α' : (Scheme.Modules.pullback (t'.1 ≫ situationEmbedding g)).obj
        (Stacks.RelativeProj.tautologicalDatum G).twist ≅
        (Scheme.Modules.pullback t).obj (Stacks.RelativeProj.tautologicalDatum G).twist,
      α'.hom = (Scheme.Modules.pullbackComp t'.1 (situationEmbedding g)).inv.app
          (Stacks.RelativeProj.tautologicalDatum G).twist ≫
        (Scheme.Modules.pullback t'.1).map θ.hom ≫ α.hom :=
    ⟨(Scheme.Modules.pullbackComp t'.1 (situationEmbedding g)).symm.app _ ≪≫
      (Scheme.Modules.pullback t'.1).mapIso θ ≪≫ α, rfl⟩
  have E : (Stacks.RelativeProj.tautologicalDatum G).overQuotientMap
      (t'.1 ≫ situationEmbedding g) ht'' ≫ α'.hom =
      (Stacks.RelativeProj.tautologicalDatum G).overQuotientMap t rfl := by
    rw [hα'def, ← hQ', ← hα', reassoc_of% K]
  have kgen : ∀ (s : T ⟶ Stacks.RelativeProj.projectiveBundle X G)
      (hs : s ≫ Stacks.RelativeProj.projectiveBundleToBase X G =
        t ≫ Stacks.RelativeProj.projectiveBundleToBase X G)
      (β : (Scheme.Modules.pullback s).obj (Stacks.RelativeProj.tautologicalDatum G).twist ≅
        (Scheme.Modules.pullback t).obj (Stacks.RelativeProj.tautologicalDatum G).twist),
      (Stacks.RelativeProj.tautologicalDatum G).overQuotientMap s hs ≫ β.hom =
        (Stacks.RelativeProj.tautologicalDatum G).overQuotientMap t rfl →
      eG ⟨s, hs⟩ = Quotient.mk _ IQG := by
    intro s hs β hβ
    exact (Stacks.RelativeProj.projectiveBundleOverEquiv_eq_iff _ _ ⟨s, hs⟩ IQG).2
      ⟨β, (Category.id_comp _).trans hβ⟩
  have k1 := kgen t rfl (Iso.refl _) (Category.comp_id _)
  have k2 := kgen _ ht'' α' E
  exact congrArg Subtype.val (eG.injective (k2.trans k1.symm))

end AlgebraicGeometry.Space.PrivateChern

end
