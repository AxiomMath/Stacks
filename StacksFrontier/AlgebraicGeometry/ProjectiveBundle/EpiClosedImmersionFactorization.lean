module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.EpiClosedImmersionTwist
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumUniversalOver

/-!
# The closed immersion of a split quotient is the vanishing locus of the hyperplane section

Let `X` be a scheme and `0 ⟶ 𝒩 ⟶ F ⟶ F' ⟶ 0` a split short exact sequence of quasi-coherent
modules: `σ : 𝒩 ⟶ F`, `u : F ⟶ F'` an epimorphism with `σ ≫ u = 0`, and `τ : F ⟶ 𝒩`,
`σ' : F' ⟶ F` with `τ ≫ σ + u ≫ σ' = 𝟙`. Let `π : 𝐏(F) ⟶ X` be the projective bundle with its
tautological quotient `π^*F ⟶ 𝒪(1)`, and `i : 𝐏(F') ⟶ 𝐏(F)` the closed immersion of
`Stacks.RelativeProj.projectiveBundleMapOfEpi`. Then a morphism `f : T ⟶ 𝐏(F)` factors through
`i` exactly when the pullback along `f` of the composite `π^*𝒩 ⟶ π^*F ⟶ 𝒪(1)` vanishes.

For `𝒩 = 𝒪_X` the composite is the hyperplane section `s` of `𝒪(1)` attached to `σ`, so this
says that `𝐏(F')` is the zero locus `Z(s)`, on points.

The proof is the universal property of the projective bundle over the base
(`Stacks.RelativeProj.isUniversalOver_tautologicalDatum`). If the pullback vanishes, the invertible
quotient `f^*𝒪(1)` of `g^*F`, `g = f ≫ π`, kills `g^*𝒩`, so it factors through `g^*u`; the
resulting quotient of `g^*F'` is classified by a morphism `h : T ⟶ 𝐏(F')`, and `h ≫ i` pulls back
the same quotient of `g^*F` as `f` because `i^*𝒪_{𝐏(F)}(1) ≅ 𝒪_{𝐏(F')}(1)` compatibly with the
tautological quotients (`Stacks.RelativeProj.tautologicalDatumTwistMapOfEpiIso_spec`).

## Main results

* `Stacks.Modules.overBase_comp_coherence`: the pasting coherence of the pullback pseudofunctor
  for a composite `h ≫ i` over the base.
* `Stacks.RelativeProj.TautologicalDatum.overQuotientMap_projectiveBundleMapOfEpi`: the
  quotient that `h ≫ i` pulls back is `g^*u` followed by the quotient `h` pulls back.
* `Stacks.RelativeProj.exists_comp_projectiveBundleMapOfEpi_iff`: **the factorization
  criterion.**

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Modules

variable {T X P P' : Scheme.{u}}

/-- **The pasting coherence of a composite over the base.** For `i : P' ⟶ P` over `X`
(`i ≫ π = π' ≫ 𝟙`) and `h : T ⟶ P'` over `g`, the identification of `g^*M` with `(h ≫ i)^*π^*M`
read through `i` is the direct one with `h^*π'^*M`. -/
theorem overBase_comp_coherence (g : T ⟶ X) (π : P ⟶ X) (π' : P' ⟶ X) (i : P' ⟶ P)
    (hi : i ≫ π = π' ≫ 𝟙 X) (h : T ⟶ P') (hh : h ≫ π' = g) (hh₁ : (h ≫ i) ≫ π = g)
    (M : X.Modules) :
    (Scheme.Modules.pullbackCongr hh₁).inv.app M ≫
        (Scheme.Modules.pullbackComp (h ≫ i) π).inv.app M ≫
        (Scheme.Modules.pullbackComp h i).inv.app ((Scheme.Modules.pullback π).obj M) ≫
        (Scheme.Modules.pullback h).map ((Scheme.Modules.pullbackComp i π).hom.app M) ≫
        (Scheme.Modules.pullback h).map ((Scheme.Modules.pullbackCongr hi).hom.app M) ≫
        (Scheme.Modules.pullback h).map ((Scheme.Modules.pullbackComp π' (𝟙 X)).inv.app M) ≫
        (Scheme.Modules.pullback h).map
          ((Scheme.Modules.pullback π').map ((Scheme.Modules.pullbackId X).hom.app M)) =
      (Scheme.Modules.pullbackCongr hh).inv.app M ≫
        (Scheme.Modules.pullbackComp h π').inv.app M := by
  have hd : i ≫ π = π' := hi.trans (Category.comp_id π')
  have hA := pullbackComp_congr_assoc h i π (h ≫ i) rfl π' hd g hh₁ M
  have lu := NatTrans.congr_app (Scheme.Modules.pseudofunctor_left_unitality (f := π')) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    eqToHom_app] at lu
  have lu' : (Scheme.Modules.pullbackComp π' (𝟙 X)).inv.app M ≫
      (Scheme.Modules.pullback π').map ((Scheme.Modules.pullbackId X).hom.app M) =
        eqToHom (by simp) := by
    simpa using lu
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_refl,
    NatTrans.id_app, Category.comp_id, Functor.map_comp, Category.assoc] at hA ⊢
  have e : (Scheme.Modules.pullback h).map ((Scheme.Modules.pullbackComp π' (𝟙 X)).inv.app M) ≫
      (Scheme.Modules.pullback h).map
        ((Scheme.Modules.pullback π').map ((Scheme.Modules.pullbackId X).hom.app M)) =
      (Scheme.Modules.pullback h).map (eqToHom (by simp)) := by
    rw [← Functor.map_comp, lu']
  rw [e]
  simp only [eqToHom_map, eqToHom_trans] at hA ⊢
  refine (((Scheme.Modules.pullbackComp h π').app M).cancel_iso_hom_right _ _).1 ?_
  simp only [Iso.app_hom, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hA' := hA =≫ eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj M) hh.symm)
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at hA'
  rw [hA']
  simp

end Stacks.Modules

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
  (u : F ⟶ G) [Epi u]

/-- **The quotient `h ≫ i` pulls back is `g^*u` followed by the quotient `h` pulls back**, for
`i = projectiveBundleMapOfEpi u` and `h : T ⟶ 𝐏(G)` over `g`. -/
theorem exists_overQuotientMap_comp_projectiveBundleMapOfEpi {T : Scheme.{u}} {g : T ⟶ X}
    (h : T ⟶ projectiveBundle X G) (hh : h ≫ projectiveBundleToBase X G = g)
    (hh₁ : (h ≫ projectiveBundleMapOfEpi u) ≫ projectiveBundleToBase X F = g) :
    ∃ β : (Scheme.Modules.pullback (h ≫ projectiveBundleMapOfEpi u)).obj
        (tautologicalDatum F).twist ≅ (Scheme.Modules.pullback h).obj (tautologicalDatum G).twist,
      (tautologicalDatum F).overQuotientMap (h ≫ projectiveBundleMapOfEpi u) hh₁ ≫ β.hom =
        (Scheme.Modules.pullback g).map u ≫ (tautologicalDatum G).overQuotientMap h hh := by
  refine ⟨((Scheme.Modules.pullbackComp h (projectiveBundleMapOfEpi u)).app
      (tautologicalDatumTwist F)).symm ≪≫
    (Scheme.Modules.pullback h).mapIso (tautologicalDatumTwistMapOfEpiIso u), ?_⟩
  have spec := tautologicalDatumTwistMapOfEpiIso_spec u
  have coh := Stacks.Modules.overBase_comp_coherence g (projectiveBundleToBase X F)
    (projectiveBundleToBase X G) (projectiveBundleMapOfEpi u)
    ((projectiveBundleMapOfEpi_comp_toBase u).trans (Category.comp_id _).symm) h hh hh₁ F
  have n₁ := (Scheme.Modules.pullbackComp h (projectiveBundleMapOfEpi u)).inv.naturality
    (tautologicalDatumUniv F)
  have n₂ := (Scheme.Modules.pullbackCongr hh).inv.naturality u
  have n₃ := (Scheme.Modules.pullbackComp h (projectiveBundleToBase X G)).inv.naturality u
  simp only [Functor.comp_map] at n₁ n₂ n₃
  change ((Scheme.Modules.pullbackCongr hh₁).inv.app F ≫
      (Scheme.Modules.pullbackComp (h ≫ projectiveBundleMapOfEpi u)
        (projectiveBundleToBase X F)).inv.app F ≫
      (Scheme.Modules.pullback (h ≫ projectiveBundleMapOfEpi u)).map (tautologicalDatumUniv F)) ≫
      ((Scheme.Modules.pullbackComp h (projectiveBundleMapOfEpi u)).inv.app
          (tautologicalDatumTwist F) ≫
        (Scheme.Modules.pullback h).map (tautologicalDatumTwistMapOfEpiIso u).hom) =
    (Scheme.Modules.pullback g).map u ≫ (Scheme.Modules.pullbackCongr hh).inv.app G ≫
      (Scheme.Modules.pullbackComp h (projectiveBundleToBase X G)).inv.app G ≫
      (Scheme.Modules.pullback h).map (tautologicalDatumUniv G)
  simp only [Category.assoc]
  rw [reassoc_of% n₁, ← Functor.map_comp, spec, reassoc_of% n₂, reassoc_of% n₃]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% coh]

/-- **The pullback of the hyperplane section along the closed immersion of a quotient vanishes**:
for `σ : 𝒩 ⟶ F` with `σ ≫ u = 0`, the composite `π^*𝒩 ⟶ π^*F ⟶ 𝒪(1)` pulls back to zero on
`𝐏(G)` along `i = projectiveBundleMapOfEpi u`. -/
theorem pullback_map_projectiveBundleMapOfEpi_eq_zero {N : X.Modules} (σ : N ⟶ F)
    (hσu : σ ≫ u = 0) :
    (Scheme.Modules.pullback (projectiveBundleMapOfEpi u)).map
      ((Scheme.Modules.pullback (projectiveBundleToBase X F)).map σ ≫ tautologicalDatumUniv F) =
      0 := by
  rw [← cancel_mono (tautologicalDatumTwistMapOfEpiIso u).hom, zero_comp, Functor.map_comp,
    Category.assoc, tautologicalDatumTwistMapOfEpiIso_spec]
  have n₁ := (Scheme.Modules.pullbackComp (projectiveBundleMapOfEpi u)
    (projectiveBundleToBase X F)).hom.naturality σ
  have n₂ := (Scheme.Modules.pullbackCongr ((projectiveBundleMapOfEpi_comp_toBase u).trans
    (Category.comp_id _).symm)).hom.naturality σ
  have n₃ := (Scheme.Modules.pullbackComp (projectiveBundleToBase X G) (𝟙 X)).inv.naturality σ
  have n₄ := (Scheme.Modules.pullbackId X).hom.naturality σ
  simp only [Functor.comp_map, Functor.id_map] at n₁ n₂ n₃ n₄
  rw [reassoc_of% n₁, reassoc_of% n₂, reassoc_of% n₃, ← Functor.map_comp_assoc,
    ← Category.assoc ((Scheme.Modules.pullback (𝟙 X)).map σ), n₄,
    Category.assoc, hσu, comp_zero, Functor.map_zero, zero_comp, comp_zero, comp_zero,
    comp_zero]

/-- The pullback of the hyperplane section along a morphism factoring through the closed immersion
of a quotient vanishes. -/
theorem pullback_map_eq_zero_of_comp_projectiveBundleMapOfEpi {N : X.Modules} (σ : N ⟶ F)
    (hσu : σ ≫ u = 0) {T : Scheme.{u}} (h : T ⟶ projectiveBundle X G) :
    (Scheme.Modules.pullback (h ≫ projectiveBundleMapOfEpi u)).map
        ((Scheme.Modules.pullback (projectiveBundleToBase X F)).map σ ≫
          tautologicalDatumUniv F) = 0 := by
  have h0 := pullback_map_projectiveBundleMapOfEpi_eq_zero u σ hσu
  have n := (Scheme.Modules.pullbackComp h (projectiveBundleMapOfEpi u)).hom.naturality
    ((Scheme.Modules.pullback (projectiveBundleToBase X F)).map σ ≫ tautologicalDatumUniv F)
  simp only [Functor.comp_map] at n
  rw [← ((Scheme.Modules.pullbackComp h (projectiveBundleMapOfEpi u)).app
      ((Scheme.Modules.pullback (projectiveBundleToBase X F)).obj N)).cancel_iso_hom_left,
    Iso.app_hom,
    ← n, h0, Functor.map_zero, zero_comp, comp_zero]

/-- A morphism along which the hyperplane section pulls back to zero factors through the closed
immersion of the quotient. -/
theorem exists_comp_projectiveBundleMapOfEpi_of_eq_zero {N : X.Modules} (σ : N ⟶ F) (τ : F ⟶ N)
    (σ' : G ⟶ F) (hsplit : τ ≫ σ + u ≫ σ' = 𝟙 F) {T : Scheme.{u}}
    (f : T ⟶ projectiveBundle X F)
    (H : (Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullback (projectiveBundleToBase X F)).map σ ≫
          tautologicalDatumUniv F) = 0) :
    ∃ h : T ⟶ projectiveBundle X G, h ≫ projectiveBundleMapOfEpi u = f := by
  obtain ⟨g, hg⟩ : ∃ g, f ≫ projectiveBundleToBase X F = g := ⟨_, rfl⟩
  have hσQ : (Scheme.Modules.pullback g).map σ ≫
      (tautologicalDatum F).overQuotientMap f hg = 0 := by
    have n₁ := (Scheme.Modules.pullbackCongr hg).inv.naturality σ
    have n₂ := (Scheme.Modules.pullbackComp f (projectiveBundleToBase X F)).inv.naturality σ
    simp only [Functor.comp_map] at n₁ n₂
    have H' : (Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullback (projectiveBundleToBase X F)).map σ ≫
          (tautologicalDatum F).univ) = 0 := H
    rw [TautologicalDatum.overQuotientMap, reassoc_of% n₁, reassoc_of% n₂, ← Functor.map_comp, H',
      comp_zero, comp_zero]
  obtain ⟨q', hq'⟩ : ∃ q', (Scheme.Modules.pullback g).map σ' ≫
      (tautologicalDatum F).overQuotientMap f hg = q' := ⟨_, rfl⟩
  have hq : (Scheme.Modules.pullback g).map u ≫ q' =
      (tautologicalDatum F).overQuotientMap f hg := by
    have e := congrArg (fun φ => (Scheme.Modules.pullback g).map φ ≫
      (tautologicalDatum F).overQuotientMap f hg) hsplit
    simp only [Functor.map_add, Preadditive.add_comp, Functor.map_comp, Category.assoc,
      CategoryTheory.Functor.map_id, Category.id_comp, hσQ, comp_zero, zero_add, hq'] at e
    exact e
  have hepi₀ : Epi ((tautologicalDatum F).overQuotientMap f hg) :=
    (tautologicalDatum F).epi_overQuotientMap f hg
  have hepi : Epi q' := by
    have : Epi ((Scheme.Modules.pullback g).map u ≫ q') := by
      rw [hq]
      exact hepi₀
    exact epi_of_epi ((Scheme.Modules.pullback g).map u) q'
  let Q' : Stacks.Divisors.InvertibleQuotient T ((Scheme.Modules.pullback g).obj G) :=
    ⟨_, ((tautologicalDatum F).overQuotient ((Scheme.Modules.pullback g).obj F) (Iso.refl _) f
      hg).invertible, q', hepi⟩
  have hγ₀ := (tautologicalDatum G).overQuotient_classifyingMorphismOver_isEquivalent
    ((Scheme.Modules.pullback g).obj G) (Iso.refl _) Q'
  generalize (tautologicalDatum G).classifyingMorphismOver ((Scheme.Modules.pullback g).obj G)
    (Iso.refl _) Q' = c at hγ₀
  obtain ⟨hm, hhm⟩ := c
  refine ⟨hm, ?_⟩
  have hh₁ : (hm ≫ projectiveBundleMapOfEpi u) ≫ projectiveBundleToBase X F = g := by
    rw [Category.assoc, projectiveBundleMapOfEpi_comp_toBase]
    exact hhm
  refine (tautologicalDatum F).eq_of_overQuotient_isEquivalent ((Scheme.Modules.pullback g).obj F)
    (Iso.refl _) _ _ hh₁ hg ?_
  obtain ⟨β, hβ⟩ := exists_overQuotientMap_comp_projectiveBundleMapOfEpi u hm hhm hh₁
  obtain ⟨γ, hγ⟩ := hγ₀
  have hγ' : (tautologicalDatum G).overQuotientMap hm hhm ≫ γ.hom = q' := by
    have h₀ := hγ
    simp only [TautologicalDatum.overQuotient_q, Iso.refl_hom, Category.id_comp] at h₀
    exact h₀
  refine ⟨β ≪≫ γ, ?_⟩
  change (Iso.refl _).hom ≫ (tautologicalDatum F).overQuotientMap _ hh₁ ≫ (β ≪≫ γ).hom =
    (Iso.refl _).hom ≫ (tautologicalDatum F).overQuotientMap f hg
  rw [Iso.refl_hom, Category.id_comp, Category.id_comp]
  exact (Category.assoc _ β.hom γ.hom).symm.trans ((congrArg (· ≫ γ.hom) hβ).trans
    ((Category.assoc _ _ _).trans
      ((congrArg ((Scheme.Modules.pullback g).map u ≫ ·) hγ').trans hq)))

/-- **The closed immersion of a split quotient is the vanishing locus of the hyperplane
section, on points.** For a split short exact sequence `0 ⟶ 𝒩 ⟶ F ⟶ G ⟶ 0` (`σ`, `u` with
`σ ≫ u = 0`, and `τ`, `σ'` with `τ ≫ σ + u ≫ σ' = 𝟙`), a morphism `f : T ⟶ 𝐏(F)` factors
through `i = projectiveBundleMapOfEpi u : 𝐏(G) ⟶ 𝐏(F)` exactly when the pullback along `f` of
`π^*σ` followed by the tautological quotient `π^*F ⟶ 𝒪(1)` vanishes. -/
theorem exists_comp_projectiveBundleMapOfEpi_iff {N : X.Modules} (σ : N ⟶ F) (τ : F ⟶ N)
    (σ' : G ⟶ F) (hsplit : τ ≫ σ + u ≫ σ' = 𝟙 F) (hσu : σ ≫ u = 0) {T : Scheme.{u}}
    (f : T ⟶ projectiveBundle X F) :
    (∃ h : T ⟶ projectiveBundle X G, h ≫ projectiveBundleMapOfEpi u = f) ↔
      (Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullback (projectiveBundleToBase X F)).map σ ≫
          tautologicalDatumUniv F) = 0 :=
  ⟨fun ⟨h, hh⟩ => hh ▸ pullback_map_eq_zero_of_comp_projectiveBundleMapOfEpi u σ hσu h,
    exists_comp_projectiveBundleMapOfEpi_of_eq_zero u σ τ σ' hsplit f⟩

end Stacks.RelativeProj

end
