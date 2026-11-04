module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.PuncturedSpectrumAffineCriterion
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingModuleProperties
public import StacksFrontier.RingTheory.AdicCompletion.QuotientBijective

/-!
# Filling in a finite cover of a punctured spectrum from the completion

Let `A` be a Noetherian local ring with maximal ideal `𝔪`, let `U = Spec A ∖ {𝔪}` be its
punctured spectrum and let `V ⟶ U` be a finite morphism. Write `Â` for the `𝔪`-adic completion
of `A`, and let `U'` and `V'` be the base changes of `U` and `V` to `X' = Spec Â`. If `V'`
extends to a finite morphism `Y' ⟶ X'`, then `V` already extends to a finite morphism `Y ⟶ X`
whose base change to `X'` is `Y'`.

This is formal glueing: `Â` is faithfully flat over `A` and `A / 𝔪^n = Â / 𝔪^n Â`, so an
`A`-algebra may be assembled from an `Â`-algebra together with its localizations away from a
generating family of `𝔪`, which is exactly the data `V ⟶ U` and `Y' ⟶ X'` provide.

## Main results

* `AlgebraicGeometry.exists_finite_extension_of_completion` — the extension `Y ⟶ X` together
  with the two cartesian squares and the compatibility of the induced maps out of `V'`.

## Implementation notes

The distinguished element of the local Lefschetz situation plays no role, so the statement is
made for an arbitrary Noetherian local ring. Both base changes are the categorical pullback, and
the asserted identifications are stated as `CategoryTheory.IsPullback` squares rather than as
isomorphisms, so that no choice of pullback has to be transported.

The algebra that does the work is the *patching algebra* of a ring map `D →ₐ[S] S ⊗[R] C`: the
equalizer, inside `D × C`, of the two maps to `S ⊗[R] C`. The formal glueing machinery of
the `FormalGlueing` namespace identifies its base change to `S` with `D`, which is what makes it
finite over `R`, and the geometric statement follows by taking global sections of everything
in sight. These algebraic steps are the private part of this file.

## References

* [Stacks Project, Tag 0BLH](https://stacks.math.columbia.edu/tag/0BLH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open IsLocalRing

universe u

namespace AlgebraicGeometry

private theorem finiteMapAlgebraOverSpec_isFinite
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsFinite f] :
    let g : R →+* Γ(X, ⊤) :=
      f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI : Algebra R Γ(X, ⊤) := g.toAlgebra
    Module.Finite R Γ(X, ⊤) := by
  intro g
  let : Algebra R Γ(X, ⊤) := g.toAlgebra
  exact RingHom.finite_algebraMap.mp (f.finite_appTop.comp
    (RingEquiv.finite (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv))

section PatchingAlgebra

open FormalGlueing TensorProduct

attribute [local instance] moduleGlueingCategory

variable {R S C D : Type u} [CommRing R] [CommRing S] [CommRing C] [CommRing D]
  [Algebra R S] [Algebra R C] [Algebra R D] [Algebra S D] [IsScalarTower R S D]
  {n : ℕ} (f : Fin n → R) (g : D →ₐ[S] S ⊗[R] C)
  (hg : ∀ i, Function.Bijective
    (LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) g.toLinearMap))

private noncomputable abbrev patchingAlgebra : Subalgebra R (D × C) :=
  ((g.restrictScalars R).comp (AlgHom.fst R D C)).equalizer
    (Algebra.TensorProduct.includeRight.comp (AlgHom.snd R D C))

private noncomputable abbrev patchingDatum :=
  pullGeneric (canonicalDatum S f (ModuleCat.of R C))
    (ModuleCat.of S D) (ModuleCat.ofHom g.toLinearMap) hg

private noncomputable def patchingToSections :
    patchingAlgebra g →ₗ[R]
      compatibleSections S f (localizationComparisons f) (patchingDatum f g hg) where
  toFun b := ⟨⟨b.1.1, fun i => canonicalLocalMk f (ModuleCat.of R C) i b.1.2⟩, by
    refine ⟨fun i => ?_, fun i j => canonicalAlphaIJ_mk f (ModuleCat.of R C) i j b.1.2⟩
    change canonicalAlpha S f (ModuleCat.of R C) i
      (LocalizedModule.map _ g.toLinearMap (LocalizedModule.mk b.1.1 1)) = _
    rw [LocalizedModule.map_mk]
    change canonicalAlpha S f (ModuleCat.of R C) i
      (LocalizedModule.mk (g b.1.1) 1) =
        (1 : S) ⊗ₜ[R] canonicalLocalMk f (ModuleCat.of R C) i b.1.2
    rw [show g b.1.1 = (1 : S) ⊗ₜ[R] b.1.2 from b.2]
    exact canonicalAlpha_mk S f (ModuleCat.of R C) i 1 b.1.2⟩
  map_add' x y := Subtype.ext (Prod.ext rfl (funext fun i => map_add _ _ _))
  map_smul' a x := Subtype.ext (Prod.ext (IsScalarTower.algebraMap_smul S a x.1.1).symm
    (funext fun i => (canonicalLocalMk f (ModuleCat.of R C) i).map_smul a x.1.2))

private theorem patchingToSections_bijective
    (hcan : Function.Bijective (canonicalToCompatibleSections S f (ModuleCat.of R C))) :
    Function.Bijective (patchingToSections f g hg) := by
  refine ⟨fun x y h => ?_, fun x => ?_⟩
  · have hd : x.1.1 = y.1.1 := congrArg (fun z => z.1.1) h
    have hc : x.1.2 = y.1.2 := by
      refine hcan.1 (Subtype.ext (Prod.ext ?_ (congrArg (fun z => z.1.2) h)))
      change (1 : S) ⊗ₜ[R] x.1.2 = (1 : S) ⊗ₜ[R] y.1.2
      exact (show g x.1.1 = (1 : S) ⊗ₜ[R] x.1.2 from x.2).symm.trans
        ((congrArg g hd).trans y.2)
    exact Subtype.ext (Prod.ext hd hc)
  · let t := compatibleSectionsMap S f
      (pullGenericMap (canonicalDatum S f (ModuleCat.of R C))
        (ModuleCat.of S D) (ModuleCat.ofHom g.toLinearMap) hg) x
    obtain ⟨c, hc⟩ := hcan.2 t
    have he : (1 : S) ⊗ₜ[R] c = g x.1.1 := congrArg (fun z => z.1.1) hc
    exact ⟨⟨(x.1.1, c), he.symm⟩, Subtype.ext (Prod.ext rfl (congrArg (fun z => z.1.2) hc))⟩

private noncomputable abbrev patchingGenericMap : patchingAlgebra g →ₐ[R] D :=
  (AlgHom.fst R D C).comp (patchingAlgebra g).val

private noncomputable abbrev patchingLocalMap : patchingAlgebra g →ₐ[R] C :=
  (AlgHom.snd R D C).comp (patchingAlgebra g).val

private noncomputable def patchingBaseChange : S ⊗[R] patchingAlgebra g →ₐ[S] D :=
  Algebra.TensorProduct.lift (Algebra.ofId S D) (patchingGenericMap g)
    (fun _ _ => Commute.all _ _)

private theorem patchingBaseChange_tmul (s : S) (b : patchingAlgebra g) :
    patchingBaseChange g (s ⊗ₜ[R] b) = s • b.1.1 := by
  simp [patchingBaseChange, Algebra.smul_def]

private noncomputable def patchingComparison :
    ModuleGlueingMap S f (localizationComparisons f)
      (canonicalDatum S f (ModuleCat.of R (patchingAlgebra g))) (patchingDatum f g hg) where
  generic := ModuleCat.ofHom (patchingBaseChange g).toLinearMap
  localPiece :=
    (canonicalDatumMap S f (ModuleCat.ofHom (patchingLocalMap g).toLinearMap)).localPiece
  alpha_compatibility i m := by
    have he : g.toLinearMap.comp (patchingBaseChange g).toLinearMap =
        AlgebraTensorModule.lTensor S S (patchingLocalMap g).toLinearMap := by
      ext b
      change g (patchingBaseChange g ((1 : S) ⊗ₜ[R] b)) = (1 : S) ⊗ₜ[R] b.1.2
      rw [patchingBaseChange_tmul, one_smul]
      exact b.2
    change canonicalAlpha S f (ModuleCat.of R C) i
      (LocalizedModule.map _ g.toLinearMap (LocalizedModule.mk (patchingBaseChange g m) 1)) = _
    rw [LocalizedModule.map_mk]
    change canonicalAlpha S f (ModuleCat.of R C) i
      (LocalizedModule.mk ((g.toLinearMap.comp (patchingBaseChange g).toLinearMap) m) 1) = _
    rw [he]
    exact (canonicalDatumMap S f
      (ModuleCat.ofHom (patchingLocalMap g).toLinearMap)).alpha_compatibility i m
  alphaIJ_compatibility :=
    (canonicalDatumMap S f (ModuleCat.ofHom (patchingLocalMap g).toLinearMap)).alphaIJ_compatibility

private theorem patchingComparison_sections :
    letI := (moduleGlueingConstruction.{u, u, u} S f).category
    (canonicalSectionsUnit S f).app (ModuleCat.of R (patchingAlgebra g)) ≫
      (compatibleSectionsFunctor S f (localizationComparisons f)).map
        (patchingComparison f g hg) = ModuleCat.ofHom (patchingToSections f g hg) := by
  apply ModuleCat.hom_ext
  ext b
  exact Subtype.ext (Prod.ext ((patchingBaseChange_tmul g 1 b).trans (one_smul S b.1.1))
    (funext fun i => LocalizedModule.map_mk _ _ _ _))

-- Comparing the explicit glueing category with its bundled construction requires unfolding.
private theorem patchingComparison_isIso
    (hflat : Module.Flat R S)
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range f)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) :
    letI := (moduleGlueingConstruction.{u, u, u} S f).category
    @IsIso (ModuleGlueingDatum.{u, u, u} S f (localizationComparisons f))
      (moduleGlueingConstruction.{u, u, u} S f).category
      (canonicalDatum S f (ModuleCat.of R (patchingAlgebra g)))
      (patchingDatum f g hg) (patchingComparison f g hg) := by
  let := (moduleGlueingConstruction.{u, u, u} S f).category
  obtain ⟨_, _, hi⟩ := canonicalFunctor_sections_areQuasiInverse.{u, u, u} R S f hflat hq
  have : (compatibleSectionsFunctor S f (localizationComparisons f)).IsEquivalence := by
    change (moduleGlueingConstruction.{u, u, u} S f).sections.IsEquivalence
    rw [← hi]
    infer_instance
  have : IsIso (canonicalSectionsUnit S f) :=
    canonicalSectionsUnit_isIso.{u, u, u} R S f hflat hq
  have : IsIso (ModuleCat.ofHom (patchingToSections f g hg)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (patchingToSections_bijective f g hg
      (ConcreteCategory.bijective_of_isIso ((canonicalSectionsUnit S f).app (ModuleCat.of R C))))
  have : IsIso ((compatibleSectionsFunctor S f (localizationComparisons f)).map
      (patchingComparison f g hg)) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _
      ((canonicalSectionsUnit S f).app (ModuleCat.of R (patchingAlgebra g)))
      ((compatibleSectionsFunctor S f (localizationComparisons f)).map
        (patchingComparison f g hg)) inferInstance
      (by
        rw [patchingComparison_sections]
        exact ‹IsIso (ModuleCat.ofHom (patchingToSections f g hg))›)
  exact isIso_of_reflects_iso (patchingComparison f g hg)
    (compatibleSectionsFunctor S f (localizationComparisons f))

include hg in
private theorem patchingBaseChange_bijective
    (hflat : Module.Flat R S)
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range f)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) :
    Function.Bijective (patchingBaseChange g) := by
  let := (moduleGlueingConstruction.{u, u, u} S f).category
  have : IsIso (patchingComparison f g hg).generic :=
    @Functor.map_isIso _ _ _ _ _ _
      (genericProjection S f (moduleGlueingConstruction.{u, u, u} S f))
      (patchingComparison f g hg) (patchingComparison_isIso f g hg hflat hq)
  exact ConcreteCategory.bijective_of_isIso (patchingComparison f g hg).generic

include hg in
private theorem patchingAlgebra_finite [Module.FaithfullyFlat R S] [Module.Finite S D]
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range f)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) :
    Module.Finite R (patchingAlgebra g) := by
  have : Module.Finite S (S ⊗[R] patchingAlgebra g) :=
    .equiv (AlgEquiv.ofBijective (patchingBaseChange g)
      (patchingBaseChange_bijective f g hg inferInstance hq)).symm.toLinearEquiv
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S

include hg in
private theorem isPushout_patchingAlgebra
    (hflat : Module.Flat R S)
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range f)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) :
    IsPushout (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (algebraMap R (patchingAlgebra g)))
      (CommRingCat.ofHom (algebraMap S D))
      (CommRingCat.ofHom (patchingGenericMap g).toRingHom) := by
  let e := (AlgEquiv.ofBijective (patchingBaseChange g)
    (patchingBaseChange_bijective f g hg hflat hq)).toRingEquiv.toCommRingCatIso
  refine (CommRingCat.isPushout_tensorProduct R S (patchingAlgebra g)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp) ?_ ?_
  · ext s
    change patchingBaseChange g (s ⊗ₜ[R] 1) = algebraMap S D s
    simp [patchingBaseChange_tmul, Algebra.smul_def]
  · ext b
    change patchingBaseChange g ((1 : S) ⊗ₜ[R] b) = b.1.1
    simp [patchingBaseChange_tmul]

end PatchingAlgebra

section GlobalSections

private noncomputable abbrev globalSectionsAlgebraMap
    {R : Type u} [CommRing R] {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) :
    R →+* Γ(X, ⊤) :=
  p.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom

private theorem isPushout_globalSectionsAlgebraMap
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {X Y : Scheme.{u}} {p : X ⟶ Spec (.of R)} {q : Y ⟶ Spec (.of S)}
    {a : Y ⟶ X} (H : IsPullback a q p (Spec.map (CommRingCat.ofHom φ)))
    [Flat (Spec.map (CommRingCat.ofHom φ))]
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsPushout (CommRingCat.ofHom (globalSectionsAlgebraMap p)) (CommRingCat.ofHom φ)
      a.appTop (CommRingCat.ofHom (globalSectionsAlgebraMap q)) := by
  apply (isPushout_appTop_of_flat H).of_iso (Scheme.ΓSpecIso (.of R))
    (Iso.refl _) (Scheme.ΓSpecIso (.of S)) (Iso.refl _) <;> simp [globalSectionsAlgebraMap]

private theorem basicOpen_globalSectionsAlgebraMap_algebraMap
    {A S : Type u} [CommRing A] [CommRing S] [Algebra A S] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of S)) (r : A) :
    Y.basicOpen (globalSectionsAlgebraMap f (algebraMap A S r)) =
      f ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap A S)) ⁻¹ᵁ PrimeSpectrum.basicOpen r) := by
  have hc : Spec.map (CommRingCat.ofHom (algebraMap A S)) ⁻¹ᵁ PrimeSpectrum.basicOpen r =
      PrimeSpectrum.basicOpen (algebraMap A S r) := by
    ext x
    rfl
  rw [hc, ← basicOpen_eq_of_affine (R := CommRingCat.of S) (algebraMap A S r),
    Scheme.preimage_basicOpen_top]
  rfl

end GlobalSections

section GeometricGlueing

private theorem localizedMap_bijective_of_comp
    {R M N P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (S : Submonoid R) (l : M →ₗ[R] N) (q : N →ₗ[R] P)
    [IsLocalizedModule S q] [IsLocalizedModule S (q.comp l)] :
    Function.Bijective (LocalizedModule.map S l) := by
  apply (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective (q.comp l) q).mp
  have h : IsLocalizedModule.map S (q.comp l) q l = LinearMap.id :=
    IsLocalizedModule.ext S (q.comp l) (IsLocalizedModule.map_units q)
      (LinearMap.ext fun x => IsLocalizedModule.map_apply S (q.comp l) q l x)
  rw [h]
  exact Function.bijective_id

private theorem localizedMap_bijective_of_linearEquiv_comp
    {R M N P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (T : Submonoid R) (l : M →ₗ[R] N) (e : N ≃ₗ[R] P)
    {k : M →ₗ[R] P} (hk : ∀ m, k m = e (l m))
    (hl : Function.Bijective (LocalizedModule.map T l)) :
    Function.Bijective (LocalizedModule.map T k) := by
  have he : LocalizedModule.map T k =
      (LocalizedModule.map T e.toLinearMap).comp (LocalizedModule.map T l) := by
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.ext T (LocalizedModule.mkLinearMap T M)
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap T P))
    ext m
    change LocalizedModule.map T k (LocalizedModule.mk m 1) =
      LocalizedModule.map T e.toLinearMap (LocalizedModule.map T l (LocalizedModule.mk m 1))
    simp [LocalizedModule.map_mk, hk]
  rw [he]
  exact (show Function.Bijective (LocalizedModule.map T e.toLinearMap) from
    ⟨LocalizedModule.map_injective T _ e.injective,
      LocalizedModule.map_surjective T _ e.surjective⟩).comp hl

private theorem localized_appTop_bijective
    {X Y : Scheme.{u}} (h : X ⟶ Y) [IsOpenImmersion h]
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (r : Γ(Y, ⊤)) (hr : Y.basicOpen r ≤ h.opensRange) :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := h.appTop.hom.toAlgebra
    Function.Bijective (LocalizedModule.map (.powers r) (Algebra.linearMap Γ(Y, ⊤) Γ(X, ⊤))) := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := h.appTop.hom.toAlgebra
  let V := Y.basicOpen r
  let W := X.basicOpen (h.appTop r)
  have he : h ⁻¹ᵁ V = W := Scheme.preimage_basicOpen_top h r
  let q : Γ(X, ⊤) →+* Γ(X, W) := (X.presheaf.map (homOfLE le_top).op).hom
  let : Algebra Γ(Y, ⊤) Γ(X, W) := (q.comp h.appTop.hom).toAlgebra
  have : IsScalarTower Γ(Y, ⊤) Γ(X, ⊤) Γ(X, W) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let ql := (Algebra.linearMap Γ(X, ⊤) Γ(X, W)).restrictScalars Γ(Y, ⊤)
  have : IsLocalization.Away (h.appTop r) Γ(X, W) :=
    isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ _
  have : IsLocalizedModule (.powers r) ql :=
    IsLocalizedModule.restrictScalars_powers r (Algebra.linearMap Γ(X, ⊤) Γ(X, W))
  let a := h.appLE V W he.ge
  have : IsIso a := by
    dsimp [a, Scheme.Hom.appLE]
    have := h.isIso_app V hr
    have : IsIso (homOfLE he.ge) := by
      rw [show homOfLE he.ge = eqToHom he.symm from Subsingleton.elim _ _]
      infer_instance
    infer_instance
  have ha : a.hom.comp (algebraMap Γ(Y, ⊤) Γ(Y, V)) =
      algebraMap Γ(Y, ⊤) Γ(X, W) := by
    change CommRingCat.Hom.hom (Y.presheaf.map (homOfLE le_top).op ≫ a) =
      CommRingCat.Hom.hom (h.appTop ≫ X.presheaf.map (homOfLE le_top).op)
    congr 1
    dsimp [a]
    rw [Scheme.Hom.map_appLE]
    rfl
  have : IsLocalization.Away r Γ(Y, V) :=
    isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ _
  have : IsLocalization.Away r Γ(X, W) :=
    IsLocalization.isLocalization_of_algEquiv (.powers r)
      (AlgEquiv.ofRingEquiv (f := (asIso a).commRingCatIsoToRingEquiv)
        (fun x => congrArg (fun k : Γ(Y, ⊤) →+* Γ(X, W) => k x) ha))
  have : IsLocalizedModule (.powers r)
      (ql.comp (Algebra.linearMap Γ(Y, ⊤) Γ(X, ⊤))) := by
    change IsLocalizedModule (.powers r) (Algebra.linearMap Γ(Y, ⊤) Γ(X, W))
    infer_instance
  exact localizedMap_bijective_of_comp (.powers r) _ ql

private theorem localizedMap_restrictScalars_bijective
    {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    [Module R M] [Module R N] [IsScalarTower R A M] [IsScalarTower R A N]
    (r : R) (l : M →ₗ[A] N)
    (hl : Function.Bijective (LocalizedModule.map (.powers (algebraMap R A r)) l)) :
    Function.Bijective (LocalizedModule.map (.powers r) (l.restrictScalars R)) := by
  let qM := (LocalizedModule.mkLinearMap (.powers (algebraMap R A r)) M).restrictScalars R
  let qN := (LocalizedModule.mkLinearMap (.powers (algebraMap R A r)) N).restrictScalars R
  have := IsLocalizedModule.restrictScalars_powers r
    (LocalizedModule.mkLinearMap (.powers (algebraMap R A r)) M)
  have := IsLocalizedModule.restrictScalars_powers r
    (LocalizedModule.mkLinearMap (.powers (algebraMap R A r)) N)
  apply (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective qM qN).mp
  have he : IsLocalizedModule.map (.powers r) qM qN (l.restrictScalars R) =
      (LocalizedModule.map (.powers (algebraMap R A r)) l).restrictScalars R := by
    apply IsLocalizedModule.ext (.powers r) qM (IsLocalizedModule.map_units qN)
    ext m
    change IsLocalizedModule.map (.powers r) qM qN (l.restrictScalars R) (qM m) = _
    rw [IsLocalizedModule.map_apply]
    exact (LocalizedModule.map_mk (.powers (algebraMap R A r)) l m 1).symm
  rwa [he]

private theorem localized_appTop_bijective_over
    {R : Type u} [CommRing R] {X Y : Scheme.{u}} (h : X ⟶ Y) [IsOpenImmersion h]
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [Algebra R Γ(Y, ⊤)] [Algebra R Γ(X, ⊤)]
    (φ : Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤)) (hφ : φ.toRingHom = h.appTop.hom)
    (r : R) (hr : Y.basicOpen (algebraMap R Γ(Y, ⊤) r) ≤ h.opensRange) :
    Function.Bijective (LocalizedModule.map (.powers r) φ.toLinearMap) := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := h.appTop.hom.toAlgebra
  have : IsScalarTower R Γ(Y, ⊤) Γ(X, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      change algebraMap R Γ(X, ⊤) x = h.appTop.hom (algebraMap R Γ(Y, ⊤) x)
      rw [← hφ]
      exact (φ.commutes x).symm)
  have he : φ.toLinearMap =
      (Algebra.linearMap Γ(Y, ⊤) Γ(X, ⊤)).restrictScalars R := by
    ext x
    exact congrArg (fun k : Γ(Y, ⊤) →+* Γ(X, ⊤) => k x) hφ
  rw [he]
  exact localizedMap_restrictScalars_bijective r
    (Algebra.linearMap Γ(Y, ⊤) Γ(X, ⊤)) (localized_appTop_bijective h _ hr)

private theorem isPullback_of_fpqc_open
    {U V X Y Y' V' : Scheme.{u}} {i : U ⟶ X} [IsOpenImmersion i]
    {p : V ⟶ U} {g : V ⟶ Y} {f : Y ⟶ X} (w : g ≫ f = p ≫ i)
    {h : Y' ⟶ Y} [Surjective h] [Flat h] [QuasiCompact h]
    {a : V' ⟶ V} {g' : V' ⟶ Y'} (H : IsPullback g' a h g)
    (H' : IsPullback (a ≫ p) g' i (h ≫ f)) :
    IsPullback p g i f := by
  have : IsOpenImmersion g' := MorphismProperty.of_isPullback H' inferInstance
  have : IsOpenImmersion g := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    H ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  apply IsOpenImmersion.isPullback p g i f w
  have he : h ⁻¹ᵁ g.opensRange = (h ≫ f) ⁻¹ᵁ i.opensRange := by
    simpa only [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange] using
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H.flip ⊤).symm.trans
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H' ⊤)
  ext y
  obtain ⟨y', rfl⟩ := h.surjective y
  exact (SetLike.ext_iff.mp he y').symm

private theorem toSpecΓ_map_globalSections
    {R : Type u} [CommRing R] {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) :
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (p.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)) = p := by
  calc
    _ = X.toSpecΓ ≫ Spec.map p.appTop ≫ Spec.map (Scheme.ΓSpecIso (.of R)).inv := by
      congr 1
      rw [← Spec.map_comp]
      rfl
    _ = p ≫ (Spec (.of R)).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso (.of R)).inv := by
      rw [Scheme.toSpecΓ_naturality_assoc]
    _ = p := by simp

end GeometricGlueing

open TensorProduct

private theorem quotientMap_bijective_of_span_eq
    {A : Type u} [CommRing A] {I : Ideal A} (hI : I.FG) {n : ℕ} {r : Fin n → A}
    (hr : Ideal.span (Set.range r) = I) :
    Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range r)).map (algebraMap A (AdicCompletion I A)))
      (algebraMap A (AdicCompletion I A)) Ideal.le_comap_map) := by
  rw [hr]
  exact AdicCompletion.quotientMap_bijective I hI

private theorem exists_patching_of_isPullback
    {A S : Type u} [CommRing A] [CommRing S] [Algebra A S] [Module.FaithfullyFlat A S]
    [Flat (Spec.map (CommRingCat.ofHom (algebraMap A S)))]
    {V Vhat Yhat : Scheme.{u}} [CompactSpace V] [QuasiSeparatedSpace V]
    [CompactSpace Vhat] [QuasiSeparatedSpace Vhat]
    {v : V ⟶ Spec (.of A)} {a : Vhat ⟶ V} {q : Vhat ⟶ Spec (.of S)}
    {fhat : Yhat ⟶ Spec (.of S)} [IsFinite fhat] {ghat : Vhat ⟶ Yhat} [IsOpenImmersion ghat]
    (hqf : q = ghat ≫ fhat)
    (HVX : IsPullback a q v (Spec.map (CommRingCat.ofHom (algebraMap A S))))
    {n : ℕ} (r : Fin n → A)
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range r)).map (algebraMap A S)) (algebraMap A S) Ideal.le_comap_map))
    (hr : ∀ i, Yhat.basicOpen (globalSectionsAlgebraMap fhat (algebraMap A S (r i))) ≤
      ghat.opensRange) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Finite A B)
      (kC : B →+* Γ(V, ⊤)) (kD : B →+* Γ(Yhat, ⊤)),
      kC.comp (algebraMap A B) = globalSectionsAlgebraMap v ∧
      IsPushout (CommRingCat.ofHom (algebraMap A S)) (CommRingCat.ofHom (algebraMap A B))
        (CommRingCat.ofHom (globalSectionsAlgebraMap fhat)) (CommRingCat.ofHom kD) ∧
      ∀ b, a.appTop.hom (kC b) = ghat.appTop.hom (kD b) := by
  have : IsAffine Yhat := isAffine_of_isAffineHom fhat
  let C := Γ(V, ⊤)
  let D := Γ(Yhat, ⊤)
  let E := Γ(Vhat, ⊤)
  let : Algebra A C := (globalSectionsAlgebraMap v).toAlgebra
  let : Algebra S D := (globalSectionsAlgebraMap fhat).toAlgebra
  let : Algebra A D := ((algebraMap S D).comp (algebraMap A S)).toAlgebra
  have : IsScalarTower A S D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra S E := (globalSectionsAlgebraMap q).toAlgebra
  let : Algebra A E := ((algebraMap S E).comp (algebraMap A S)).toAlgebra
  have : IsScalarTower A S E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra C E := a.appTop.hom.toAlgebra
  have HB := isPushout_globalSectionsAlgebraMap (algebraMap A S) HVX
  have : IsScalarTower A C E := IsScalarTower.of_algebraMap_eq fun x =>
    (congrArg (fun k : CommRingCat.of A ⟶ E => k.hom x) HB.w).symm
  have : Algebra.IsPushout A S C E := CommRingCat.isPushout_iff_isPushout.mp HB.flip
  let e : S ⊗[A] C ≃ₐ[S] E := Algebra.IsPushout.equiv A S C E
  let φ : D →ₐ[S] E :=
    { ghat.appTop.hom with
      commutes' := fun s => by
        change ghat.appTop.hom (globalSectionsAlgebraMap fhat s) = globalSectionsAlgebraMap q s
        rw [hqf]
        simp only [globalSectionsAlgebraMap, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
          RingHom.comp_apply] }
  let θ : D →ₐ[S] S ⊗[A] C := e.symm.toAlgHom.comp φ
  have hθ (i : Fin n) : Function.Bijective
      (LocalizedModule.map (.powers (algebraMap A S (r i))) θ.toLinearMap) :=
    localizedMap_bijective_of_linearEquiv_comp _ φ.toLinearMap e.symm.toLinearEquiv
      (fun _ => rfl) (localized_appTop_bijective_over ghat φ rfl _ (hr i))
  have : Module.Finite S D := finiteMapAlgebraOverSpec_isFinite fhat
  refine ⟨patchingAlgebra θ, inferInstance, inferInstance, patchingAlgebra_finite r θ hθ hq,
    (patchingLocalMap θ).toRingHom, (patchingGenericMap θ).toRingHom,
    RingHom.ext (patchingLocalMap θ).commutes, isPushout_patchingAlgebra r θ hθ inferInstance hq,
    fun b => ?_⟩
  exact (show φ b.1.1 = algebraMap C E b.1.2 by
    simpa [θ, e, Algebra.IsPushout.equiv_tmul] using
      congrArg e (show θ b.1.1 = (1 : S) ⊗ₜ[A] b.1.2 from b.2)).symm

private theorem exists_extension_of_isPushout
    {A S B : Type u} [CommRing A] [CommRing S] [CommRing B] [Algebra A S] [Algebra A B]
    [Module.Finite A B] [Flat (Spec.map (CommRingCat.ofHom (algebraMap A S)))]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap A S)))]
    {U V Uhat Vhat Yhat : Scheme.{u}} {i : U ⟶ Spec (.of A)} [IsOpenImmersion i]
    {pi : V ⟶ U} {u : Uhat ⟶ U} {t : Uhat ⟶ Spec (.of S)} {a : Vhat ⟶ V} {p : Vhat ⟶ Uhat}
    {fhat : Yhat ⟶ Spec (.of S)} [IsFinite fhat] {ghat : Vhat ⟶ Yhat}
    (HU : IsPullback u t i (Spec.map (CommRingCat.ofHom (algebraMap A S))))
    (HV : IsPullback a p pi u) (H' : IsPullback p ghat t fhat)
    (kC : B →+* Γ(V, ⊤)) (kD : B →+* Γ(Yhat, ⊤))
    (hC : kC.comp (algebraMap A B) = globalSectionsAlgebraMap (pi ≫ i))
    (hD : IsPushout (CommRingCat.ofHom (algebraMap A S)) (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (globalSectionsAlgebraMap fhat)) (CommRingCat.ofHom kD))
    (hk : ∀ b, a.appTop.hom (kC b) = ghat.appTop.hom (kD b)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)) (g : V ⟶ Y) (h : Yhat ⟶ Y),
      IsFinite f ∧ IsPullback pi g i f ∧
        IsPullback fhat h (Spec.map (CommRingCat.ofHom (algebraMap A S))) f ∧
          a ≫ g = ghat ≫ h := by
  have : IsAffine Yhat := isAffine_of_isAffineHom fhat
  let f : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g : V ⟶ Spec (.of B) := V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom kC)
  let h : Yhat ⟶ Spec (.of B) := Yhat.toSpecΓ ≫ Spec.map (CommRingCat.ofHom kD)
  have : IsFinite f := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  have Hh : IsPullback fhat h (Spec.map (CommRingCat.ofHom (algebraMap A S))) f := by
    apply (hD.op.map Scheme.Spec).flip.of_iso
      Yhat.isoSpec.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · change Spec.map (CommRingCat.ofHom (globalSectionsAlgebraMap fhat)) ≫ 𝟙 _ =
        Yhat.isoSpec.inv ≫ fhat
      rw [Category.comp_id]
      exact Yhat.isoSpec.eq_inv_comp.mpr (toSpecΓ_map_globalSections fhat)
    · simp [h, Scheme.isoSpec]
    · simp
    · simp [f]
  have Hcompat : a ≫ g = ghat ≫ h := by
    dsimp only [g, h]
    rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp,
      ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
    congr 1
    apply congrArg Spec.map
    ext b
    exact hk b
  have Hg : g ≫ f = pi ≫ i := by
    have he : CommRingCat.ofHom (algebraMap A B) ≫ CommRingCat.ofHom kC =
        CommRingCat.ofHom (globalSectionsAlgebraMap (pi ≫ i)) := by
      ext x
      exact RingHom.congr_fun hC x
    dsimp only [g, f]
    rw [Category.assoc, ← Spec.map_comp, he]
    exact toSpecΓ_map_globalSections (pi ≫ i)
  have Hvg : IsPullback ghat a h g := by
    apply IsPullback.of_right (s := ?_) Hcompat.symm Hh
    simpa only [← H'.w, Hg] using (HV.paste_vert HU).flip
  have Hopen : IsPullback (a ≫ pi) ghat i (h ≫ f) := by
    simpa only [Hh.w, ← HV.w] using H'.paste_horiz HU
  have : Flat h := MorphismProperty.of_isPullback Hh inferInstance
  have : Surjective h := MorphismProperty.of_isPullback Hh inferInstance
  have : QuasiCompact h := MorphismProperty.of_isPullback Hh inferInstance
  exact ⟨_, f, g, h, inferInstance, isPullback_of_fpqc_open Hg Hvg Hopen, Hh, Hcompat⟩

/-- A finite cover of the punctured spectrum which extends over the completed
spectrum extends over the original local spectrum, compatibly with both given
covers. -/
@[stacks 0BLH]
lemma exists_finite_extension_of_completion
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (V : Scheme.{u}) (pi : V ⟶ (Stacks.Divisors.puncturedSpectrum A).toScheme)
    [IsFinite pi] :
    let Ahat := AdicCompletion (maximalIdeal A) A
    let Xhat := Spec (.of Ahat)
    let completionMap : Xhat ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
    let Uhat := pullback (Stacks.Divisors.puncturedSpectrum A).ι completionMap
    let UhatToU : Uhat ⟶ (Stacks.Divisors.puncturedSpectrum A).toScheme := pullback.fst _ _
    let Vhat := pullback pi UhatToU
    let pihat : Vhat ⟶ Uhat := pullback.snd _ _
    ∀ (Yhat : Scheme.{u}) (fhat : Yhat ⟶ Xhat) [IsFinite fhat]
      (ghat : Vhat ⟶ Yhat),
      IsPullback pihat ghat
          (pullback.snd (Stacks.Divisors.puncturedSpectrum A).ι completionMap) fhat →
        (∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)) (g : V ⟶ Y) (h : Yhat ⟶ Y),
          IsFinite f ∧
            IsPullback pi g (Stacks.Divisors.puncturedSpectrum A).ι f ∧
            IsPullback fhat h completionMap f ∧
            (pullback.fst pi UhatToU ≫ g = ghat ≫ h)) := by
  classical
  dsimp only
  intro Yhat fhat _ ghat H
  let S := AdicCompletion (maximalIdeal A) A
  let U := Stacks.Divisors.puncturedSpectrum A
  let c : Spec (.of S) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A S))
  let u := pullback.fst U.ι c
  let t := pullback.snd U.ι c
  let a := pullback.fst pi u
  let p := pullback.snd pi u
  have HU : IsPullback u t U.ι c := .of_hasPullback _ _
  have HV : IsPullback a p pi u := .of_hasPullback _ _
  have HVX := HV.paste_vert HU
  have H' : IsPullback p ghat t fhat := H
  have : Module.FaithfullyFlat A S :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson (maximalIdeal A)
      (by simpa only [Ideal.jacobson_bot] using
        (IsLocalRing.maximalIdeal_le_jacobson (R := A) ⊥))
  have : Flat c := (HasRingHomProperty.Spec_iff (P := @Flat)).mpr
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : Surjective c := (flat_and_surjective_SpecMap_iff _).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance) |>.2
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : U.toScheme.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion U.ι
  have : V.IsQuasiAffine := Scheme.IsQuasiAffine.of_isAffineHom pi
  have : IsAffineHom a := MorphismProperty.of_isPullback HVX.flip inferInstance
  have : (pullback pi u).IsQuasiAffine := Scheme.IsQuasiAffine.of_isAffineHom a
  have : IsOpenImmersion ghat := MorphismProperty.of_isPullback H' inferInstance
  obtain ⟨n, r, hr⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (maximalIdeal A).fg_of_isNoetherianRing
  change Ideal.span (Set.range r) = maximalIdeal A at hr
  have Hrange : ghat.opensRange = fhat ⁻¹ᵁ (c ⁻¹ᵁ U) := by
    simpa only [t, Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.opensRange_pullbackSnd, Scheme.Opens.opensRange_ι] using
      IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H' ⊤
  obtain ⟨B, _, _, _, kC, kD, hC, hD, hk⟩ := exists_patching_of_isPullback H'.w HVX r
    (quotientMap_bijective_of_span_eq (maximalIdeal A).fg_of_isNoetherianRing hr) fun i => by
      rw [Hrange]
      exact (basicOpen_globalSectionsAlgebraMap_algebraMap fhat (r i)).le.trans fun x hx =>
        Stacks.Divisors.basicOpen_le_puncturedSpectrum (g := r i)
          (hr ▸ Ideal.subset_span ⟨i, rfl⟩) hx
  exact exists_extension_of_isPushout HU HV H' kC kD hC hD hk

end AlgebraicGeometry

end
