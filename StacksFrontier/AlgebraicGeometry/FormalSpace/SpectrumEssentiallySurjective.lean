module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumEtaleCompletion
public import StacksFrontier.RingTheory.Etale.Lifting

/-!
# Essential surjectivity of the formal spectrum on étale algebras

Let `S` be a scheme contained in a big fppf site `B` and let `R` be a weakly admissible
topological ring over `S` by a quotient system `D` whose atlas lies in the site. Every affine
formal algebraic space `V` over `S` carrying a morphism `v : V ⟶ Spf R` which is representable
by algebraic spaces and étale is, over `Spf R`, the formal spectrum of the relative completion
`A^∧` of an étale `R`-algebra `A`.

This is the essential-surjectivity half of the equivalence of categories of **Stacks 0AN8**.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_etale_lift_of_quotient_etale`: **Stacks 04D1** in the
  shape the proof uses — an étale algebra over `R ⧸ J` is the reduction of an étale
  `R`-algebra.
* `AlgebraicGeometry.FormalSpace.exists_etale_completion_formalSpectrum`: the
  essential-surjectivity half of **Stacks 0AN8**.

## Implementation notes

The proof is the source's. Choose a weak ideal of definition `J₀ ⊆ R`. Stacks 0AKN
(`AlgebraicGeometry.FormalSpace.relative_isAffineHom_of_isRepresentableByAlgebraicSpaces`) makes
the base change `V₀ = Spec (R ⧸ J₀) ×_{Spf R} V` an affine scheme of the site, and it is étale
over `Spec (R ⧸ J₀)`, so its coordinate ring is an étale `R ⧸ J₀`-algebra. Stacks 04D1 lifts
that to an étale `R`-algebra `A` with `A ⧸ J₀A` its coordinate ring, and Stacks 0ANM gives the
relative completion `A^∧` a quotient system over `S` and the morphism `Spf A^∧ ⟶ Spf R`, whose
base change to `Spec (R ⧸ J₀)` is `Spec (A ⧸ J₀A)` — the same affine scheme. Both morphisms to
`Spf R` are representable and étale after every represented base change, so
`AlgebraicGeometry.FormalSpace.exists_iso_of_isPullback_stage` propagates the identification at
`J₀` to an isomorphism `V ≅ Spf A^∧` over `Spf R`. That last step is where the source invokes
the uniqueness clause of Stacks 0ALI, the étale lifting across the thickenings between the
quotient stages.

The only hypothesis beyond the source's is the large-site condition
`AlgebraicGeometry.FormalSpace.QuotientSystem.HasLargeSite` on `D`, which says that the chosen
big fppf site contains the atlas `∐_J Spec (R ⧸ J)`. It is used only to see that `Spf R` is an
affine formal algebraic space at all (Stacks 0AIF,
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_formalSpectrum`), which Stacks 0AKN
needs; the quotient stages of `A^∧` lie in the site by Stacks 0ANM, with no further hypothesis.
A bound on the cardinality of `R` implies it,
`AlgebraicGeometry.FormalSpace.hasLargeSite_of_mk_lt_cutoff`, but is not needed.

## References

* [Stacks Project, Tag 04D1](https://stacks.math.columbia.edu/tag/04D1)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0ALI](https://stacks.math.columbia.edu/tag/0ALI)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0ANM](https://stacks.math.columbia.edu/tag/0ANM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.FormalSpace

section Lift

/-- **Stacks 04D1**, in the shape the proof of Stacks 0AN8 uses: an étale algebra over a
quotient `R ⧸ J` is the reduction modulo `J` of an étale `R`-algebra, by a ring isomorphism
compatible with the two structure maps.

`etale_lift_along_surjection`, this library's Stacks 04D1, produces the étale `R`-algebra `A`
together with a surjection `A → R₀` whose kernel is `JA`; the isomorphism is the induced one on
`A ⧸ JA`. -/
theorem exists_etale_lift_of_quotient_etale {R : Type u} [CommRing R] (J : Ideal R)
    {R₀ : Type u} [CommRing R₀] (f₀ : R ⧸ J →+* R₀) (hf₀ : RingHom.Etale f₀) :
    ∃ (A : Type u) (_ : CommRing A) (f : R →+* A), RingHom.Etale f ∧
      ∃ e : (A ⧸ J.map f) ≃+* R₀,
        e.toRingHom.comp (Ideal.quotientMap (J.map f) f Ideal.le_comap_map) = f₀ := by
  let : Algebra (R ⧸ J) R₀ := f₀.toAlgebra
  let : Algebra R R₀ := (f₀.comp (Ideal.Quotient.mk J)).toAlgebra
  have : IsScalarTower R (R ⧸ J) R₀ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.Etale (R ⧸ J) R₀ := hf₀
  obtain ⟨C, hC, hRC, hCet, ψ, hψ, hker⟩ :=
    etale_lift_along_surjection R (R ⧸ J) R₀ Ideal.Quotient.mk_surjective
  let := hC
  let := hRC
  have hker' : RingHom.ker (ψ : C →+* R₀) = J.map (algebraMap R C) := by
    rw [hker, show RingHom.ker (algebraMap R (R ⧸ J)) = J from Ideal.mk_ker]
  refine ⟨C, hC, algebraMap R C, RingHom.etale_algebraMap.mpr hCet,
    (Ideal.quotEquivOfEq hker'.symm).trans (RingHom.quotientKerEquivOfSurjective hψ), ?_⟩
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r ↦ ?_)
  change (Ideal.quotEquivOfEq hker'.symm).trans (RingHom.quotientKerEquivOfSurjective hψ)
      (Ideal.Quotient.mk (J.map (algebraMap R C)) (algebraMap R C r)) =
    f₀ (Ideal.Quotient.mk J r)
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact (RingHom.quotientKerEquivOfSurjective_apply_mk _ _).trans (ψ.commutes r)

end Lift

section SpecIso

/-- For an affine scheme `X` and a morphism `φ : X ⟶ Spec R`, composing the isomorphism
`X ≅ Spec Γ(X, ⊤)` with the spectrum of `R ≅ Γ(Spec R, ⊤) ⟶ Γ(X, ⊤)` recovers `φ`. -/
theorem isoSpec_hom_comp_Spec_map_ΓSpecIso_inv_appTop {X : Scheme.{u}} [IsAffine X]
    {R : CommRingCat.{u}} (φ : X ⟶ Spec R) :
    X.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ φ.appTop) = φ := by
  rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
    Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

end SpecIso

section Main

open TopologicalRing TopologicalRing.CompletionOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]

attribute [local instance] sheaf_hasColimits

/-- An isomorphism of underlying schemes compatible with morphisms `q : X ⟶ Z` and
`p : Y ⟶ Z` of the big fppf category over `S` lifts to an isomorphism `X ≅ Y` over `Z`. -/
theorem exists_iso_comp_eq_of_toScheme_iso {X Y Z : BigFppfOver B S hS} (q : X ⟶ Z) (p : Y ⟶ Z)
    (e : (BigFppfOver.toScheme B S hS).obj X ≅ (BigFppfOver.toScheme B S hS).obj Y)
    (he : e.hom ≫ (BigFppfOver.toScheme B S hS).map p = (BigFppfOver.toScheme B S hS).map q) :
    ∃ e' : X ≅ Y, e'.hom ≫ p = q := by
  let ie : X.left ≅ Y.left := B.inclusion.preimageIso e
  have hie : ie.hom ≫ p.left = q.left := by
    refine B.inclusion.map_injective ?_
    rwa [CategoryTheory.Functor.map_comp,
      show B.inclusion.map ie.hom = e.hom from B.inclusion.map_preimage _]
  exact ⟨Over.isoMk ie (by rw [← Over.w p, ← Category.assoc, hie, Over.w q]),
    Over.OverMorphism.ext hie⟩

/-- An isomorphism `A ⧸ JA ≃+* R₀` compatible with a map `R ⧸ J → R₀` induces an isomorphism
from the quotient of the relative completion by the kernel of its projection at `J`. -/
theorem exists_ringEquiv_quotient_kerProjectionIdeal {A : Type u} [CommRing A] (f : R →+* A)
    (J : WeakIdealOfDefinitionIndex R) {R₀ : Type u} [CommRing R₀] {f₀ : R ⧸ J.1 →+* R₀}
    (e₀ : (A ⧸ J.1.map f) ≃+* R₀)
    (he₀ : e₀.toRingHom.comp (Ideal.quotientMap (J.1.map f) f Ideal.le_comap_map) = f₀)
    (φ : R →+* CompletionOver f) (hφ : φ = canonicalMap f)
    (hJ : J.1 ≤ Ideal.comap φ (kerProjectionIdeal f J).1) :
    ∃ e : (CompletionOver f ⧸ (kerProjectionIdeal f J).1) ≃+* R₀,
      e.toRingHom.comp (Ideal.quotientMap _ φ hJ) = f₀ := by
  refine ⟨((projection f J).quotientKerEquivOfSurjective (projection_surjective f J)).trans e₀,
    Ideal.Quotient.ringHom_ext (RingHom.ext fun b ↦ ?_)⟩
  change e₀ ((projection f J).quotientKerEquivOfSurjective (projection_surjective f J)
    (Ideal.Quotient.mk (RingHom.ker (projection f J)) (φ b))) = f₀ (Ideal.Quotient.mk J.1 b)
  rw [RingHom.quotientKerEquivOfSurjective_apply_mk, hφ, projection_canonicalMap]
  exact RingHom.congr_fun he₀ (Ideal.Quotient.mk J.1 b)

/-- If the coordinate ring of an affine object `W` over the stage `Spec (R ⧸ J₀)` is identified
with `A ⧸ J₀A`, compatibly with the structure maps, then `W` is the base change of the morphism
`Spf A^∧ ⟶ Spf R` to that stage. -/
theorem exists_isPullback_formalSpectrumMap_of_ringEquiv (hR : IsWeaklyAdmissible R)
    {A : Type u} [CommRing A] (f : R →+* A) {D : QuotientSystem B S hS R}
    {E : QuotientSystem B S hS (CompletionOver f)} (g : ContinuousHom D E)
    (hg : g.toRingHom = canonicalMap f) (J₀ : WeakIdealOfDefinitionIndex R)
    {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (q : W ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage J₀))
    (e₀ : (A ⧸ J₀.1.map f) ≃+* Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (he₀ : e₀.toRingHom.comp (Ideal.quotientMap (J₀.1.map f) f Ideal.le_comap_map) =
      ((BigFppfOver.toScheme B S hS).map q).appTop.hom.comp
        (Scheme.ΓSpecIso (.of (R ⧸ J₀.1))).inv.hom) :
    ∃ p, IsPullback p ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q)
      (formalSpectrumMap hR g) (formalSpectrumInclusion D (OrderDual.toDual J₀)) := by
  have hJK := le_comap_kerProjectionIdeal f g hg J₀
  let u₀ : R ⧸ J₀.1 →+* CompletionOver f ⧸ (kerProjectionIdeal f J₀).1 :=
    Ideal.quotientMap (kerProjectionIdeal f J₀).1 g.toRingHom hJK
  obtain ⟨er, her⟩ := exists_ringEquiv_quotient_kerProjectionIdeal f J₀ e₀ he₀ g.toRingHom hg hJK
  let eSch : (BigFppfOver.toScheme B S hS).obj W ≅
      (BigFppfOver.toScheme B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj (E.stage (kerProjectionIdeal f J₀))) :=
    ((BigFppfOver.toScheme B S hS).obj W).isoSpec ≪≫
      Scheme.Spec.mapIso er.toCommRingCatIso.op
  have heSch : eSch.hom ≫ (BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (g.stageMap J₀ (kerProjectionIdeal f J₀) hJK)) =
      (BigFppfOver.toScheme B S hS).map q := by
    change ((BigFppfOver.toScheme B S hS).obj W).isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom er.toRingHom) ≫ Spec.map (CommRingCat.ofHom u₀) = _
    rw [← Spec.map_comp, show CommRingCat.ofHom u₀ ≫ CommRingCat.ofHom er.toRingHom =
      (Scheme.ΓSpecIso (.of (R ⧸ J₀.1))).inv ≫ ((BigFppfOver.toScheme B S hS).map q).appTop
      from CommRingCat.hom_ext her]
    exact isoSpec_hom_comp_Spec_map_ΓSpecIso_inv_appTop _
  obtain ⟨eSite, heSite⟩ := exists_iso_comp_eq_of_toScheme_iso q
    ((BigAffineFppf.inclusion B S hS).map (g.stageMap J₀ (kerProjectionIdeal f J₀) hJK)) eSch heSch
  refine ⟨_, (isPullback_formalSpectrumMap_kerProjection f hR g hg J₀ hJK).flip.of_iso'
    ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).mapIso eSite)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Category.comp_id _).symm ?_
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)⟩
  change (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map eSite.hom ≫
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((BigAffineFppf.inclusion B S hS).map (g.stageMap J₀ (kerProjectionIdeal f J₀) hJK)) =
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q ≫ 𝟙 _
  rw [Category.comp_id, ← CategoryTheory.Functor.map_comp, heSite]

/-- **The essential-surjectivity half of Stacks 0AN8.** Let `R` be a weakly admissible
topological ring over `S` with quotient system `D` whose atlas lies in the site. Every affine
formal algebraic space `V` over `S` with a morphism `v : V ⟶ Spf R` which is representable by
algebraic spaces and étale is the formal spectrum of the relative completion of an étale
`R`-algebra, compatibly with the morphisms to `Spf R`. -/
theorem exists_etale_completion_formalSpectrum (hR : IsWeaklyAdmissible R)
    (D : QuotientSystem B S hS R) (hD : D.HasLargeSite)
    {V : FppfSheaf B S hS} (v : V ⟶ formalSpectrum D)
    (hV : IsAffineFormalAlgebraicSpace B S hS V) (hvet : IsRepresentableEtale B S hS v) :
    ∃ (A : Type u) (_ : CommRing A) (f : R →+* A), RingHom.Etale f ∧
      ∃ (E : QuotientSystem B S hS (CompletionOver f)) (g : ContinuousHom D E),
        g.toRingHom = canonicalMap f ∧
          ∃ ε : V ≅ formalSpectrum E, ε.hom ≫ formalSpectrumMap hR g = v := by
  classical
  have : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  -- `Spf R` is an affine formal algebraic space, so Stacks 0AKN applies to `v`
  have hvAff := relative_isAffineHom_of_hasThickeningPresentation B S hS v hV.2
    (isAffineFormalAlgebraicSpace_formalSpectrum hR D hD).2 hvet.1
  have hvEt := relative_etale_of_isRepresentableEtale B S hS v hvet hvAff.rep
  -- the chosen weak ideal of definition and the base change of `v` to its stage
  let J₀ : WeakIdealOfDefinitionIndex R := ⟨hR.1.choose, hR.1.choose_spec⟩
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj (D.stage J₀))) := (D.stage J₀).2
  let W₀ := hvAff.rep.pullback (formalSpectrumInclusion D J₀)
  let q₀ : W₀ ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage J₀) :=
    hvAff.rep.snd (formalSpectrumInclusion D J₀)
  have hpb : IsPullback (hvAff.rep.fst (formalSpectrumInclusion D J₀))
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q₀) v
      (formalSpectrumInclusion D J₀) :=
    hvAff.rep.isPullback (formalSpectrumInclusion D J₀)
  have : AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map q₀) :=
    hvAff.property_snd (formalSpectrumInclusion D J₀)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W₀) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map q₀)
  -- the coordinate ring of the base change is an étale `R ⧸ J₀`-algebra
  let f₀ : R ⧸ J₀.1 →+* Γ((BigFppfOver.toScheme B S hS).obj W₀, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map q₀).appTop.hom.comp
      (Scheme.ΓSpecIso (.of (R ⧸ J₀.1))).inv.hom
  have hf₀ : RingHom.Etale f₀ :=
    RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (.of (R ⧸ J₀.1))).inv))
      (AlgebraicGeometry.HasRingHomProperty.appTop (@AlgebraicGeometry.Etale.{u})
        (Q := @RingHom.Etale) _ (hvEt.property_snd (formalSpectrumInclusion D J₀)))
  -- Stacks 04D1 lifts it to an étale `R`-algebra
  obtain ⟨A, instA, f, hf, e₀, he₀⟩ := exists_etale_lift_of_quotient_etale J₀.1 f₀ hf₀
  let := instA
  have hfft : f.FiniteType := finiteType_of_etale f hf
  -- Stacks 0ANM: the relative completion over `S`, and the morphism of formal spectra
  obtain ⟨E, g, hg⟩ := exists_completionOver_quotientSystem B S hS f hfft hR D hD
  refine ⟨A, instA, f, hf, E, g, hg, ?_⟩
  -- the stage of `Spf A^∧` over `J₀` is the base change of `v`, by a ring isomorphism
  obtain ⟨p, hp⟩ := exists_isPullback_formalSpectrumMap_of_ringEquiv hR f g hg J₀ q₀ e₀ he₀
  -- the stagewise identification propagates to the whole formal spectrum
  obtain ⟨t, ht⟩ := exists_iso_of_isPullback_stage D J₀ v (formalSpectrumMap hR g) hvEt
    (relative_etale_formalSpectrumMap_completionOver hR f hf D hD E g hg) hpb hp
  exact ⟨t, ht.symm⟩

end Main

end AlgebraicGeometry.FormalSpace

end
