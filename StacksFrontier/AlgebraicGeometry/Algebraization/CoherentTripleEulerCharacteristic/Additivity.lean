module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleEulerCharacteristic.ShortExact
import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.AffineOpen

/-!
# Additivity of the Euler characteristic of coherent triples

Prepared extensions assembled from their data, the comparison with the direct image from the
punctured spectrum, the construction of a middle prepared extension in a short exact sequence,
and **Stacks Tag 0F26**: the Euler characteristic is additive along a short exact sequence of
coherent triples (`eulerCharacteristic_add_of_shortExact`,
`PreparedExtension.eulerCharacteristic_add_of_shortExact`).

This file is part of
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleEulerCharacteristic`; see there
for the overview and references.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Algebraization

-- The complete-lattice structure on `F.Submodule` already exists upstream; it is made available
-- locally rather than re-declared, because an anonymous `local instance` with this type gets a
-- derived name that collides with the identical one in
-- `StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerComplement.Basic`.
attribute [local instance] SheafOfModules.Submodule.instCompleteLattice

/-! ### Building prepared extensions -/

/-- **A prepared extension assembled from its data**, with the compatibility condition written
through the two comparison natural transformations rather than through the `let`-bindings of the
structure field. -/
private noncomputable def preparedExtensionMk
    (A : Type u) [CommRing A] [IsLocalRing A] {f : A} (T : CoherentTriple A f)
    (G : (baseScheme A).Modules) (hG : _root_.SheafOfModules.IsCoherent G)
    (hreg : ∀ V : (baseScheme A).Opens,
      IsSMulRegular Γ(G, V) ((baseScheme A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))
    (alpha' : (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).obj G ≅ T.F)
    (alpha₀' : (Scheme.Modules.pullback (closedImmersion A f)).obj G ⟶ T.F₀)
    (hcompat : (puncturedClosedFibrePullbackOpen A f).app G ≫
        (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).map alpha'.hom ≫ T.alpha.hom =
      (puncturedClosedFibrePullbackClosed A f).app G ≫
        (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map alpha₀') :
    PreparedExtension A f T where
  F' := G
  coherent := hG
  regular := hreg
  alpha' := alpha'
  alpha₀' := alpha₀'
  compatible := by
    simpa only [puncturedClosedFibrePullbackOpen, puncturedClosedFibrePullbackClosed,
      NatTrans.comp_app, Category.assoc] using hcompat

/-- **A prepared extension transported along a map which is an isomorphism over the punctured
spectrum.** A coherent module on `Spec A` on whose sections `f` acts regularly and which agrees
with a prepared extension over the punctured spectrum is itself a prepared extension. -/
private noncomputable def preparedExtensionOfIsoOnPunctured
    (A : Type u) [CommRing A] [IsLocalRing A] {f : A} {T : CoherentTriple A f}
    (P : PreparedExtension A f T) (G : (baseScheme A).Modules)
    (hG : _root_.SheafOfModules.IsCoherent G)
    (hreg : ∀ V : (baseScheme A).Opens,
      IsSMulRegular Γ(G, V) ((baseScheme A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))
    (g : G ⟶ P.F')
    (hg : IsIso ((Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map g)) :
    PreparedExtension A f T :=
  preparedExtensionMk A T G hG hreg
    ((@asIso _ _ _ _ _ hg).trans P.alpha')
    ((Scheme.Modules.pullback (closedImmersion A f)).map g ≫ P.alpha₀')
    (by
      simpa only [Iso.trans_hom, asIso_hom, Functor.map_comp, Category.assoc] using
        (preparedExtension_pullback_compat_apply A P g).symm)

/-- The Euler characteristic of a transported prepared extension is computed by the same
closed-fibre map. -/
private theorem preparedExtensionOfIsoOnPunctured_alpha₀'
    (A : Type u) [CommRing A] [IsLocalRing A] {f : A} {T : CoherentTriple A f}
    (P : PreparedExtension A f T) (G : (baseScheme A).Modules)
    (hG : _root_.SheafOfModules.IsCoherent G)
    (hreg : ∀ V : (baseScheme A).Opens,
      IsSMulRegular Γ(G, V) ((baseScheme A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))
    (g : G ⟶ P.F')
    (hg : IsIso ((Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map g)) :
    (preparedExtensionOfIsoOnPunctured A P G hG hreg g hg).alpha₀' =
      (Scheme.Modules.pullback (closedImmersion A f)).map g ≫ P.alpha₀' := rfl

/-- The punctured-spectrum isomorphism of a transported prepared extension. -/
private theorem preparedExtensionOfIsoOnPunctured_alpha'
    (A : Type u) [CommRing A] [IsLocalRing A] {f : A} {T : CoherentTriple A f}
    (P : PreparedExtension A f T) (G : (baseScheme A).Modules)
    (hG : _root_.SheafOfModules.IsCoherent G)
    (hreg : ∀ V : (baseScheme A).Opens,
      IsSMulRegular Γ(G, V) ((baseScheme A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))
    (g : G ⟶ P.F')
    (hg : IsIso ((Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map g)) :
    (preparedExtensionOfIsoOnPunctured A P G hG hreg g hg).alpha'.hom =
      (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map g ≫
        P.alpha'.hom := rfl


/-! ### Comparison with the direct image from the punctured spectrum -/

/-- `f` acts regularly on the sections of a submodule of a biproduct of two modules on whose
sections it acts regularly. -/
private lemma regular_of_mono_biprod'
    (A : Type u) [CommRing A] (f : A) {H K : (baseScheme A).Modules}
    (hH : ∀ V : (baseScheme A).Opens,
      IsSMulRegular Γ(H, V) ((baseScheme A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))
    (hK : ∀ V : (baseScheme A).Opens,
      IsSMulRegular Γ(K, V) ((baseScheme A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))
    {G : (baseScheme A).Modules} (φ : G ⟶ H ⊞ K) [Mono φ] :
    ∀ V : (baseScheme A).Opens,
      IsSMulRegular Γ(G, V) ((baseScheme A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)) := by
  intro V
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro value hvalue
  have hleft : (φ ≫ biprod.fst).app V value = 0 := by
    apply (hH V).right_eq_zero_of_smul
    rw [← Scheme.Modules.Hom.app_smul, hvalue, map_zero]
  have hright : (φ ≫ biprod.snd).app V value = 0 := by
    apply (hK V).right_eq_zero_of_smul
    rw [← Scheme.Modules.Hom.app_smul, hvalue, map_zero]
  have htotal : φ.app V value = 0 := by
    have hsplit : φ = (φ ≫ biprod.fst) ≫ biprod.inl + (φ ≫ biprod.snd) ≫ biprod.inr := by
      simpa only [Preadditive.comp_add, Category.assoc, Category.comp_id] using
        congrArg (fun morphism => φ ≫ morphism) (biprod.total (X := H) (Y := K)).symm
    rw [hsplit]
    change ((show H ⟶ H ⊞ K from biprod.inl).app V) ((φ ≫ biprod.fst).app V value) +
      ((show K ⟶ H ⊞ K from biprod.inr).app V) ((φ ≫ biprod.snd).app V value) = 0
    rw [hleft, hright, map_zero, map_zero, add_zero]
  exact mono_app_injective φ V (htotal.trans (map_zero _).symm)

/-- **A map out of a coherent `f`-regular module which is a monomorphism over the punctured
spectrum is a monomorphism.** Its kernel is coherent and vanishes on the punctured spectrum, so
it has finite length; but `f` acts regularly on it, which forces it to vanish. -/
private lemma mono_of_mono_restrict
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (f : A)
    (hf : f ∈ IsLocalRing.maximalIdeal A)
    {G H : (baseScheme A).Modules} [G.IsCoherent] [H.IsQuasicoherent]
    (g : G ⟶ H)
    (hregG : ∀ V : (baseScheme A).Opens,
      IsSMulRegular Γ(G, V) ((baseScheme A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))
    (hg : Mono ((Scheme.Modules.restrictFunctor
      (Stacks.Divisors.puncturedSpectrum A).ι).map g)) : Mono g := by
  have : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  have : (kernel g).IsQuasicoherent := inferInstance
  have hcoh : (kernel g).IsCoherent :=
    StacksDraft.AlgebraicGeometry.CoherentSubquotients.QuasicoherentSubmodule.isCoherent_of_mono
      (kernel.ι g)
  have hzero : IsZero ((Scheme.Modules.restrictFunctor
      (Stacks.Divisors.puncturedSpectrum A).ι).obj (kernel g)) :=
    isZero_restrict_kernel_of_mono_restrict _ g hg
  obtain ⟨n, hn⟩ := maximalIdealPower_smul_top_eq_bot A (kernel g) hcoh hzero
  have hreg := regular_of_mono A f (kernel.ι g) hregG ⊤
  have hpow : IsSMulRegular ((moduleSpecΓFunctor (R := .of A)).obj (kernel g)) (f ^ n) :=
    IsSMulRegular.pow n hreg
  have hmem : f ^ n ∈ IsLocalRing.maximalIdeal A ^ n := Ideal.pow_mem_pow hf n
  have : Subsingleton ((moduleSpecΓFunctor (R := .of A)).obj (kernel g)) := by
    refine ⟨fun value other => hpow ?_⟩
    have hz (value : (moduleSpecΓFunctor (R := .of A)).obj (kernel g)) :
        f ^ n • value = 0 := by
      have hm := Submodule.smul_mem_smul hmem
        (show value ∈ (⊤ : Submodule A ((moduleSpecΓFunctor (R := .of A)).obj
          (kernel g))) from trivial)
      rwa [hn] at hm
    exact (hz value).trans (hz other).symm
  have hzΓ : IsZero ((moduleSpecΓFunctor (R := .of A)).obj (kernel g)) :=
    ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  have : (tilde.functor (.of A)).IsLeftAdjoint := (tilde.adjunction (R := .of A)).isLeftAdjoint
  have hzker : IsZero (kernel g) :=
    ((tilde.functor (.of A)).map_isZero hzΓ).of_iso (asIso (kernel g).fromTildeΓ).symm
  exact Abelian.mono_of_kernel_ι_eq_zero g (hzker.eq_of_src _ _)

/-- The map from a prepared extension to the direct image of a module on the punctured spectrum
determined by a map out of the punctured-spectrum member of its triple. -/
private noncomputable def puncturedComparison
    (A : Type u) [CommRing A] [IsLocalRing A] {f : A} {T : CoherentTriple A f}
    (P : PreparedExtension A f T)
    {H : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules} (p : T.F ⟶ H) :
    P.F' ⟶ (Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj H :=
  (Scheme.Modules.restrictAdjunction (Stacks.Divisors.puncturedSpectrum A).ι).homEquiv P.F' H
    ((Scheme.Modules.restrictFunctorIsoPullback
      (Stacks.Divisors.puncturedSpectrum A).ι).hom.app P.F' ≫ P.alpha'.hom ≫ p)

/-- **Two maps that agree after comparison with the direct image agree over the punctured
spectrum.** -/
private lemma puncturedComparison_eq
    (A : Type u) [CommRing A] [IsLocalRing A] {f : A} {T T₂ : CoherentTriple A f}
    (P : PreparedExtension A f T) (P₂ : PreparedExtension A f T₂)
    {H : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules}
    (p : T.F ⟶ H) (q : T₂.F ⟶ H)
    {G : (baseScheme A).Modules} (u : G ⟶ P.F') (v : G ⟶ P₂.F')
    (h : u ≫ puncturedComparison A P p = v ≫ puncturedComparison A P₂ q) :
    (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map u ≫
        P.alpha'.hom ≫ p =
      (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map v ≫
        P₂.alpha'.hom ≫ q := by
  have hsymm := congrArg (fun morphism =>
      ((Scheme.Modules.restrictAdjunction (Stacks.Divisors.puncturedSpectrum A).ι).homEquiv
        G H).symm morphism) h
  simp only [Adjunction.homEquiv_naturality_left_symm, puncturedComparison,
    Equiv.symm_apply_apply] at hsymm
  rw [← Category.assoc, (Scheme.Modules.restrictFunctorIsoPullback
      (Stacks.Divisors.puncturedSpectrum A).ι).hom.naturality u, Category.assoc,
    ← Category.assoc ((Scheme.Modules.restrictFunctor
      (Stacks.Divisors.puncturedSpectrum A).ι).map v),
    (Scheme.Modules.restrictFunctorIsoPullback
      (Stacks.Divisors.puncturedSpectrum A).ι).hom.naturality v, Category.assoc] at hsymm
  exact (cancel_epi ((Scheme.Modules.restrictFunctorIsoPullback
    (Stacks.Divisors.puncturedSpectrum A).ι).hom.app G)).1 hsymm

/-- The comparison of a prepared extension with the direct image of its own punctured-spectrum
member is an isomorphism over the punctured spectrum. -/
private lemma isIso_restrict_puncturedComparison_id
    (A : Type u) [CommRing A] [IsLocalRing A] {f : A} {T : CoherentTriple A f}
    (P : PreparedExtension A f T) :
    IsIso ((Scheme.Modules.restrictFunctor (Stacks.Divisors.puncturedSpectrum A).ι).map
      (puncturedComparison A P (𝟙 T.F))) := by
  have hcomp : puncturedComparison A P (𝟙 T.F) =
      (Scheme.Modules.restrictAdjunction (Stacks.Divisors.puncturedSpectrum A).ι).homEquiv
        P.F' T.F
        (((Scheme.Modules.restrictFunctorIsoPullback
          (Stacks.Divisors.puncturedSpectrum A).ι).app P.F').trans P.alpha').hom := by
    simp only [puncturedComparison, Iso.trans_hom, Category.comp_id]
    rfl
  rw [hcomp]
  exact isIso_restrict_adjunctionMap_of_iso _ P.F' T.F _


/-! ### The middle term of the short exact sequence of prepared extensions -/

/-- **Prepared extensions related by a morphism of triples have closed-fibre maps that agree
over the punctured closed fibre**, as soon as the comparison holds over the punctured
spectrum. -/
private lemma closedFibreMap_restrict_eq_of_hom
    (A : Type u) [CommRing A] [IsLocalRing A] {f : A}
    {S R : CoherentTriple A f} (ψ : S.Hom R)
    (Q : PreparedExtension A f S) (N : PreparedExtension A f R)
    {G : (baseScheme A).Modules} (u : G ⟶ Q.F') (v : G ⟶ N.F')
    (hopen : (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map u ≫
        Q.alpha'.hom ≫ ψ.onPunctured =
      (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map v ≫
        N.alpha'.hom) :
    (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
        ((Scheme.Modules.pullback (closedImmersion A f)).map u ≫
          Q.alpha₀' ≫ ψ.onClosedFibre) =
      (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
        ((Scheme.Modules.pullback (closedImmersion A f)).map v ≫ N.alpha₀') := by
  apply (cancel_epi ((puncturedClosedFibrePullbackClosed A f).app G)).1
  rw [show (Scheme.Modules.pullback (closedImmersion A f)).map u ≫
        Q.alpha₀' ≫ ψ.onClosedFibre =
      ((Scheme.Modules.pullback (closedImmersion A f)).map u ≫ Q.alpha₀') ≫
        ψ.onClosedFibre from (Category.assoc _ _ _).symm,
    Functor.map_comp, ← Category.assoc,
    preparedExtension_pullback_compat_apply A Q u,
    preparedExtension_pullback_compat_apply A N v]
  simp only [Category.assoc]
  rw [← ψ.compatible]
  congr 1
  rw [← Category.assoc, ← Functor.map_comp, Category.assoc, hopen]



/-- **A prepared extension of the first term of a short exact sequence of coherent triples.**
A coherent `f`-regular module mapping to a prepared extension of the second term, realizing the
first term over the punctured spectrum and over the closed fibre, is a prepared extension of the
first term. -/
private noncomputable def preparedExtensionOfSub
    (A : Type u) [CommRing A] [IsLocalRing A] {f : A} {T S : CoherentTriple A f}
    (φ : T.Hom S)
    (hmono : Mono ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map φ.onClosedFibre))
    (W : PreparedExtension A f S) (K : (baseScheme A).Modules)
    (hK : _root_.SheafOfModules.IsCoherent K)
    (hregK : ∀ V : (baseScheme A).Opens,
      IsSMulRegular Γ(K, V) ((baseScheme A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))
    (g : K ⟶ W.F')
    (alphaK : (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).obj K ≅ T.F)
    (alpha₀K : (Scheme.Modules.pullback (closedImmersion A f)).obj K ⟶ T.F₀)
    (hopen : (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map g ≫
      W.alpha'.hom = alphaK.hom ≫ φ.onPunctured)
    (hclosed : (Scheme.Modules.pullback (closedImmersion A f)).map g ≫ W.alpha₀' =
      alpha₀K ≫ φ.onClosedFibre) :
    PreparedExtension A f T :=
  preparedExtensionMk A T K hK hregK alphaK alpha₀K (by
    have := hmono
    apply (cancel_mono ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
      φ.onClosedFibre)).1
    have h1 := preparedExtension_pullback_compat_apply A W g
    rw [hclosed, hopen, Functor.map_comp, Functor.map_comp] at h1
    simp only [Category.assoc] at h1 ⊢
    rw [φ.compatible] at h1
    exact h1.symm)

/-- **A prepared extension of the third term of a short exact sequence of coherent triples.**
A coherent `f`-regular module receiving a map from a prepared extension of the second term,
realizing the third term over the punctured spectrum and over the closed fibre, is a prepared
extension of the third term. -/
private noncomputable def preparedExtensionOfQuot
    (A : Type u) [CommRing A] [IsLocalRing A] {f : A} {S R : CoherentTriple A f}
    (ψ : S.Hom R) (W : PreparedExtension A f S) (I : (baseScheme A).Modules)
    (hI : _root_.SheafOfModules.IsCoherent I)
    (hregI : ∀ V : (baseScheme A).Opens,
      IsSMulRegular Γ(I, V) ((baseScheme A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))
    (h : W.F' ⟶ I)
    (hepi : Epi ((Scheme.Modules.pullback
      ((puncturedClosedFibre A f).ι ≫ closedImmersion A f)).map h))
    (alphaI : (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).obj I ≅ R.F)
    (alpha₀I : (Scheme.Modules.pullback (closedImmersion A f)).obj I ⟶ R.F₀)
    (hopen : (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map h ≫
      alphaI.hom = W.alpha'.hom ≫ ψ.onPunctured)
    (hclosed : (Scheme.Modules.pullback (closedImmersion A f)).map h ≫ alpha₀I =
      W.alpha₀' ≫ ψ.onClosedFibre) :
    PreparedExtension A f R :=
  preparedExtensionMk A R I hI hregI alphaI alpha₀I (by
    have := hepi
    have hopen' : (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map
            ((Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map h) ≫
          (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map alphaI.hom ≫ R.alpha.hom =
        (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map W.alpha'.hom ≫
          (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map ψ.onPunctured ≫ R.alpha.hom := by
      rw [← Category.assoc, ← Functor.map_comp, hopen, Functor.map_comp, Category.assoc]
    have hclosed' : (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
            ((Scheme.Modules.pullback (closedImmersion A f)).map h) ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map alpha₀I =
        (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map W.alpha₀' ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map ψ.onClosedFibre := by
      rw [← Functor.map_comp, hclosed, Functor.map_comp]
    have hWc := congrArg (fun morphism => morphism ≫
      (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map ψ.onClosedFibre)
      (preparedExtension_compatible' A W)
    simp only [Category.assoc] at hWc
    apply (cancel_epi ((Scheme.Modules.pullback
      ((puncturedClosedFibre A f).ι ≫ closedImmersion A f)).map h)).1
    simp only [← Category.assoc]
    rw [(puncturedClosedFibrePullbackOpen A f).naturality h,
      (puncturedClosedFibrePullbackClosed A f).naturality h]
    simp only [Category.assoc, Functor.comp_map]
    rw [hopen', hclosed', ψ.compatible]
    exact hWc)


/-- A map of modules on `Spec A` which is an isomorphism after restriction to the punctured
spectrum is one after pullback to it. -/
private lemma isIso_pullback_map_of_isIso_restrict
    (A : Type u) [CommRing A] [IsLocalRing A] {X Y : (baseScheme A).Modules} (g : X ⟶ Y)
    (hg : IsIso ((Scheme.Modules.restrictFunctor (Stacks.Divisors.puncturedSpectrum A).ι).map g)) :
    IsIso ((Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map g) :=
  (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback
    (Stacks.Divisors.puncturedSpectrum A).ι) g).mp hg

/-- **The fibre product of a prepared extension of the second term with one of the third.** It
is coherent, `f` acts regularly on its sections, it agrees with the second prepared extension
over the punctured spectrum, and its two projections agree there after the map of triples. -/
private theorem exists_fibreProduct
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (f : A)
    {S R : CoherentTriple A f} (ψ : S.Hom R)
    (Q : PreparedExtension A f S) (N : PreparedExtension A f R) :
    ∃ (V : (baseScheme A).Modules) (pV : V ⟶ Q.F') (qV : V ⟶ N.F'),
      _root_.SheafOfModules.IsCoherent V ∧
      (∀ U : (baseScheme A).Opens,
        IsSMulRegular Γ(V, U) ((baseScheme A).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f))) ∧
      IsIso ((Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map pV) ∧
      (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map pV ≫
          Q.alpha'.hom ≫ ψ.onPunctured =
        (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map qV ≫
          N.alpha'.hom := by
  have : Q.F'.IsCoherent := Q.coherent
  have : N.F'.IsCoherent := N.coherent
  have : R.F.IsCoherent := R.coherent_F
  have : R.F.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : (Q.F' ⊞ N.F').IsCoherent := isCoherent_biprod _ _ Q.coherent N.coherent
  have : (Q.F' ⊞ N.F').IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : ((Scheme.Modules.pushforward
    (Stacks.Divisors.puncturedSpectrum A).ι).obj R.F).IsQuasicoherent := inferInstance
  have : IsLocallyNoetherian (baseScheme A) := inferInstance
  set d := puncturedComparison A Q ψ.onPunctured with hd
  set e := puncturedComparison A N (𝟙 R.F) with he
  set D := biprod.desc d (-e) with hD
  have hVq : (kernel D).IsQuasicoherent := inferInstance
  have hVcoh : (kernel D).IsCoherent :=
    StacksDraft.AlgebraicGeometry.CoherentSubquotients.QuasicoherentSubmodule.isCoherent_of_mono
      (kernel.ι D)
  have hregV := regular_of_mono_biprod' A f Q.regular N.regular (kernel.ι D)
  have heIso : IsIso ((Scheme.Modules.restrictFunctor
      (Stacks.Divisors.puncturedSpectrum A).ι).map e) :=
    isIso_restrict_puncturedComparison_id A N
  have hpIso' : IsIso ((Scheme.Modules.pullback
      (Stacks.Divisors.puncturedSpectrum A).ι).map (kernel.ι D ≫ biprod.fst)) :=
    isIso_pullback_map_of_isIso_restrict A _ (isIso_map_kernel_biprod_fst
      (Scheme.Modules.restrictFunctor (Stacks.Divisors.puncturedSpectrum A).ι) d e)
  have hrelation : (kernel.ι D ≫ biprod.fst) ≫ d = (kernel.ι D ≫ biprod.snd) ≫ e := by
    apply sub_eq_zero.mp
    simpa [hD, biprod.desc_eq, Preadditive.comp_add, Category.assoc, sub_eq_add_neg] using
      kernel.condition D
  refine ⟨kernel D, kernel.ι D ≫ biprod.fst, kernel.ι D ≫ biprod.snd, hVcoh, hregV, hpIso',
    ?_⟩
  have hopen := puncturedComparison_eq A Q N ψ.onPunctured (𝟙 R.F)
    (kernel.ι D ≫ biprod.fst) (kernel.ι D ≫ biprod.snd) hrelation
  simpa only [Category.comp_id] using hopen


/-- **The middle prepared extension.** Given prepared extensions of the second and third terms
of a morphism of coherent triples, there is a prepared extension of the second term carrying a
map to the third one's module for which both comparison squares commute on the nose. -/
private theorem exists_middle_preparedExtension
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (f : A)
    {S R : CoherentTriple A f} (ψ : S.Hom R)
    (Q : PreparedExtension A f S) (N : PreparedExtension A f R) :
    ∃ (W : PreparedExtension A f S) (bW : W.F' ⟶ N.F'),
      W.alpha'.hom ≫ ψ.onPunctured =
        (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map bW ≫
          N.alpha'.hom ∧
      W.alpha₀' ≫ ψ.onClosedFibre =
        (Scheme.Modules.pullback (closedImmersion A f)).map bW ≫ N.alpha₀' := by
  obtain ⟨V, pV, qV, hVcoh, hregV, hpIso, hopen⟩ := exists_fibreProduct A f ψ Q N
  have : V.IsCoherent := hVcoh
  have : R.F₀.IsCoherent := R.coherent_F₀
  have : R.F₀.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : IsClosedImmersion (closedImmersion A f) := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) Ideal.Quotient.mk_surjective
  have : IsFinite (closedImmersion A f) := inferInstance
  have : ((Scheme.Modules.pushforward (closedImmersion A f)).obj R.F₀).IsCoherent :=
    inferInstance
  set ε := (Scheme.Modules.pullback (closedImmersion A f)).map pV ≫
      Q.alpha₀' ≫ ψ.onClosedFibre -
    (Scheme.Modules.pullback (closedImmersion A f)).map qV ≫ N.alpha₀' with hεdef
  have hεzero : (Scheme.Modules.restrictFunctor (puncturedClosedFibre A f).ι).map ε = 0 := by
    have heq := closedFibreMap_restrict_eq_of_hom A ψ Q N pV qV hopen
    have E := Scheme.Modules.restrictFunctorIsoPullback (puncturedClosedFibre A f).ι
    have heq' : (Scheme.Modules.restrictFunctor (puncturedClosedFibre A f).ι).map
          ((Scheme.Modules.pullback (closedImmersion A f)).map pV ≫
            Q.alpha₀' ≫ ψ.onClosedFibre) =
        (Scheme.Modules.restrictFunctor (puncturedClosedFibre A f).ι).map
          ((Scheme.Modules.pullback (closedImmersion A f)).map qV ≫ N.alpha₀') := by
      apply (cancel_mono (E.hom.app R.F₀)).mp
      rw [E.hom.naturality, E.hom.naturality, heq]
    simpa only [hεdef, Functor.map_sub, sub_eq_zero] using heq'
  set EE := closedFibreAdjunctionMap A f ε with hEEdef
  have hEzero : (Scheme.Modules.restrictFunctor
      (Stacks.Divisors.puncturedSpectrum A).ι).map EE = 0 :=
    restrict_closedFibreAdjunctionMap_eq_zero A f ε hεzero
  have hWcoh : (kernel EE).IsCoherent := SheafOfModules.kernel_isCoherent EE
  have hregW := regular_of_mono A f (kernel.ι EE) hregV
  have hcIso' : IsIso ((Scheme.Modules.pullback
      (Stacks.Divisors.puncturedSpectrum A).ι).map (kernel.ι EE)) :=
    isIso_pullback_map_of_isIso_restrict A _ (isIso_restrict_kernel_ι_of_map_eq_zero _ EE hEzero)
  have haWIso : IsIso ((Scheme.Modules.pullback
      (Stacks.Divisors.puncturedSpectrum A).ι).map (kernel.ι EE ≫ pV)) := by
    rw [Functor.map_comp]
    have := hcIso'
    have := hpIso
    infer_instance
  refine ⟨preparedExtensionOfIsoOnPunctured A Q (kernel EE) hWcoh hregW
    (kernel.ι EE ≫ pV) haWIso, kernel.ι EE ≫ qV, ?_, ?_⟩
  · have h := congrArg (fun morphism => (Scheme.Modules.pullback
      (Stacks.Divisors.puncturedSpectrum A).ι).map (kernel.ι EE) ≫ morphism) hopen
    simp only [← Category.assoc] at h
    rw [← (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map_comp,
      ← (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map_comp] at h
    rw [preparedExtensionOfIsoOnPunctured_alpha']
    exact h
  · rw [preparedExtensionOfIsoOnPunctured_alpha₀']
    have hdiff : ((Scheme.Modules.pullback (closedImmersion A f)).map (kernel.ι EE ≫ pV) ≫
          Q.alpha₀') ≫ ψ.onClosedFibre -
        (Scheme.Modules.pullback (closedImmersion A f)).map (kernel.ι EE ≫ qV) ≫ N.alpha₀' =
      (Scheme.Modules.pullback (closedImmersion A f)).map (kernel.ι EE) ≫ ε := by
      simp only [hεdef, (Scheme.Modules.pullback (closedImmersion A f)).map_comp,
        Category.assoc, Preadditive.comp_sub]
    have hmain : closedFibreAdjunctionMap A f
        (((Scheme.Modules.pullback (closedImmersion A f)).map (kernel.ι EE ≫ pV) ≫
            Q.alpha₀') ≫ ψ.onClosedFibre -
          (Scheme.Modules.pullback (closedImmersion A f)).map (kernel.ι EE ≫ qV) ≫
            N.alpha₀') = 0 := by
      rw [hdiff, closedFibreAdjunctionMap_comp]
      exact kernel.condition EE
    have hez : ((Scheme.Modules.pullbackPushforwardAdjunction (closedImmersion A f)).homEquiv
        (kernel EE) R.F₀) 0 = 0 := by
      rw [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
    apply sub_eq_zero.mp
    apply ((Scheme.Modules.pullbackPushforwardAdjunction (closedImmersion A f)).homEquiv
      (kernel EE) R.F₀).injective
    exact hmain.trans hez.symm


/-- Pullback to the punctured closed fibre preserves finite limits, being isomorphic to
restriction along an open immersion. -/
private instance preservesFiniteLimits_pullback_opens {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits (Scheme.Modules.pullback U.ι) :=
  preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback U.ι)

/-- **The comparison data for the first term of a short exact sequence of coherent triples.**
The kernel of the map to the third term's module realizes the first term both over the punctured
spectrum and over the closed fibre. -/
private theorem exists_sub_comparison
    (A : Type u) [CommRing A] [IsLocalRing A] {f : A}
    {T S R : CoherentTriple A f} {φ : T.Hom S} {ψ : S.Hom R}
    (hT : CoherentTriple.ShortExact φ ψ)
    (W : PreparedExtension A f S) (N : PreparedExtension A f R) (bW : W.F' ⟶ N.F')
    (hopenW : W.alpha'.hom ≫ ψ.onPunctured =
      (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map bW ≫
        N.alpha'.hom)
    (hclosedW : W.alpha₀' ≫ ψ.onClosedFibre =
      (Scheme.Modules.pullback (closedImmersion A f)).map bW ≫ N.alpha₀') :
    ∃ (alphaK : (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).obj
          (kernel bW) ≅ T.F)
      (alpha₀K : (Scheme.Modules.pullback (closedImmersion A f)).obj (kernel bW) ⟶ T.F₀),
      (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map (kernel.ι bW) ≫
          W.alpha'.hom = alphaK.hom ≫ φ.onPunctured ∧
        (Scheme.Modules.pullback (closedImmersion A f)).map (kernel.ι bW) ≫ W.alpha₀' =
          alpha₀K ≫ φ.onClosedFibre := by
  have := hT.punctured.mono_f
  have := hT.closedFibre.mono_f
  have hker := hT.punctured.exact.fIsKernel
  have hker₀ := hT.closedFibre.exact.fIsKernel
  -- the punctured-spectrum isomorphism
  have hsq : (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map bW ≫
      N.alpha'.hom = W.alpha'.hom ≫ ψ.onPunctured := hopenW.symm
  let e1 := PreservesKernel.iso
    (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι) bW
  let e2 := kernel.mapIso
    ((Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map bW)
    ψ.onPunctured W.alpha' N.alpha' hsq
  let e3 := IsLimit.conePointUniqueUpToIso (kernelIsKernel ψ.onPunctured) hker
  have hz : ((Scheme.Modules.pullback (closedImmersion A f)).map (kernel.ι bW) ≫ W.alpha₀') ≫
      ψ.onClosedFibre = 0 := by
    rw [Category.assoc, hclosedW, ← Category.assoc, ← Functor.map_comp, kernel.condition,
      Functor.map_zero, zero_comp]
  refine ⟨e1 ≪≫ e2 ≪≫ e3, hker₀.lift (KernelFork.ofι
    ((Scheme.Modules.pullback (closedImmersion A f)).map (kernel.ι bW) ≫ W.alpha₀') hz),
    ?_, ?_⟩
  · have ha : e1.hom ≫ kernel.ι
        ((Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map bW) =
        (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map
          (kernel.ι bW) := by
      simp [e1, PreservesKernel.iso]
    have hb : e2.hom ≫ kernel.ι ψ.onPunctured =
        kernel.ι ((Scheme.Modules.pullback
          (Stacks.Divisors.puncturedSpectrum A).ι).map bW) ≫ W.alpha'.hom := by
      simp [e2]
    have hc : e3.hom ≫ φ.onPunctured = kernel.ι ψ.onPunctured := by
      simpa [e3] using IsLimit.conePointUniqueUpToIso_hom_comp (kernelIsKernel ψ.onPunctured)
        hker WalkingParallelPair.zero
    rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc, hc, hb, ← Category.assoc,
      ha]
  · simpa using (hker₀.fac (KernelFork.ofι
      ((Scheme.Modules.pullback (closedImmersion A f)).map (kernel.ι bW) ≫ W.alpha₀') hz)
      WalkingParallelPair.zero).symm


/-- Pullback of modules along any morphism of schemes preserves finite colimits, being a left
adjoint. -/
private instance preservesFiniteColimits_pullback {X Y : Scheme.{u}} (g : X ⟶ Y) :
    PreservesFiniteColimits (Scheme.Modules.pullback g) := by
  have : (Scheme.Modules.pullback g).IsLeftAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isLeftAdjoint
  infer_instance

/-- **The comparison data for the third term of a short exact sequence of coherent triples.**
The quotient by the kernel realizes the third term both over the punctured spectrum and over the
closed fibre. -/
private theorem exists_quot_comparison
    (A : Type u) [CommRing A] [IsLocalRing A] {f : A}
    {T S R : CoherentTriple A f} {φ : T.Hom S} {ψ : S.Hom R}
    (hT : CoherentTriple.ShortExact φ ψ)
    (W : PreparedExtension A f S) (N : PreparedExtension A f R) (bW : W.F' ⟶ N.F')
    (alphaK : (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).obj
      (kernel bW) ≅ T.F)
    (alpha₀K : (Scheme.Modules.pullback (closedImmersion A f)).obj (kernel bW) ⟶ T.F₀)
    (hopenK : (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map
        (kernel.ι bW) ≫ W.alpha'.hom = alphaK.hom ≫ φ.onPunctured)
    (hclosedK : (Scheme.Modules.pullback (closedImmersion A f)).map (kernel.ι bW) ≫
      W.alpha₀' = alpha₀K ≫ φ.onClosedFibre) :
    ∃ (alphaI : (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).obj
          (cokernel (kernel.ι bW)) ≅ R.F)
      (alpha₀I : (Scheme.Modules.pullback (closedImmersion A f)).obj
        (cokernel (kernel.ι bW)) ⟶ R.F₀),
      (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map
          (cokernel.π (kernel.ι bW)) ≫ alphaI.hom = W.alpha'.hom ≫ ψ.onPunctured ∧
        (Scheme.Modules.pullback (closedImmersion A f)).map (cokernel.π (kernel.ι bW)) ≫
          alpha₀I = W.alpha₀' ≫ ψ.onClosedFibre := by
  have := hT.punctured.epi_g
  have hcoker := hT.punctured.exact.gIsCokernel
  have hz₀ : (Scheme.Modules.pullback (closedImmersion A f)).map (kernel.ι bW) ≫
      W.alpha₀' ≫ ψ.onClosedFibre = 0 := by
    rw [← Category.assoc, hclosedK, Category.assoc, hT.zero_closedFibre, comp_zero]
  let c1 := PreservesCokernel.iso
    (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι) (kernel.ι bW)
  let c2 := cokernel.mapIso
    ((Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map (kernel.ι bW))
    φ.onPunctured alphaK W.alpha' hopenK
  let c3 := IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel φ.onPunctured) hcoker
  refine ⟨c1 ≪≫ c2 ≪≫ c3,
    (PreservesCokernel.iso (Scheme.Modules.pullback (closedImmersion A f))
        (kernel.ι bW)).hom ≫
      cokernel.desc ((Scheme.Modules.pullback (closedImmersion A f)).map (kernel.ι bW))
        (W.alpha₀' ≫ ψ.onClosedFibre) hz₀, ?_, ?_⟩
  · have ha : (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map
        (cokernel.π (kernel.ι bW)) ≫ c1.hom =
        cokernel.π ((Scheme.Modules.pullback
          (Stacks.Divisors.puncturedSpectrum A).ι).map (kernel.ι bW)) :=
      PreservesCokernel.π_iso_hom _ _
    have hb : cokernel.π ((Scheme.Modules.pullback
          (Stacks.Divisors.puncturedSpectrum A).ι).map (kernel.ι bW)) ≫ c2.hom =
        W.alpha'.hom ≫ cokernel.π φ.onPunctured := by
      simp [c2]
    have hc : cokernel.π φ.onPunctured ≫ c3.hom = ψ.onPunctured := by
      simpa [c3] using IsColimit.comp_coconePointUniqueUpToIso_hom
        (cokernelIsCokernel φ.onPunctured) hcoker WalkingParallelPair.one
    rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc, ha, ← Category.assoc, hb,
      Category.assoc, hc]
  · rw [← Category.assoc]
    have ha : (Scheme.Modules.pullback (closedImmersion A f)).map
          (cokernel.π (kernel.ι bW)) ≫
        (PreservesCokernel.iso (Scheme.Modules.pullback (closedImmersion A f))
          (kernel.ι bW)).hom =
        cokernel.π ((Scheme.Modules.pullback (closedImmersion A f)).map (kernel.ι bW)) :=
      PreservesCokernel.π_iso_hom _ _
    rw [ha, cokernel.π_desc]

/-! ### Additivity of the Euler characteristic -/

/-- **The Euler characteristic is additive along a short exact sequence of prepared
extensions.** If the prepared extensions `P`, `Q`, `N` of the three terms of a short exact
sequence of coherent triples sit in a short exact sequence on `Spec A` whose closed-fibre maps
commute with the maps of the triples, then the Euler characteristic of `Q` is the sum of those
of `P` and `N`. -/
public theorem PreparedExtension.eulerCharacteristic_add_of_shortExact
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (f : A)
    {T S R : CoherentTriple A f} {φ : T.Hom S} {ψ : S.Hom R}
    (hT : CoherentTriple.ShortExact φ ψ)
    (P : PreparedExtension A f T) (Q : PreparedExtension A f S) (N : PreparedExtension A f R)
    (a : P.F' ⟶ Q.F') (b : Q.F' ⟶ N.F') (hab : a ≫ b = 0)
    (hSE : (ShortComplex.mk a b hab).ShortExact)
    (hleft : (Scheme.Modules.pullback (closedImmersion A f)).map a ≫ Q.alpha₀' =
      P.alpha₀' ≫ φ.onClosedFibre)
    (hright : (Scheme.Modules.pullback (closedImmersion A f)).map b ≫ N.alpha₀' =
      Q.alpha₀' ≫ ψ.onClosedFibre) :
    Q.eulerCharacteristic = P.eulerCharacteristic + N.eulerCharacteristic := by
  have : P.F'.IsCoherent := P.coherent
  have : Q.F'.IsCoherent := Q.coherent
  have : N.F'.IsCoherent := N.coherent
  have : T.F₀.IsCoherent := T.coherent_F₀
  have : S.F₀.IsCoherent := S.coherent_F₀
  have : R.F₀.IsCoherent := R.coherent_F₀
  have : P.F'.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : Q.F'.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : N.F'.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : T.F₀.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : S.F₀.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : R.F₀.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have hreg : IsSMulRegular ((moduleSpecΓFunctor (R := .of A)).obj N.F') f := N.regular ⊤
  have hrow1 := closedFibreSections_shortExact A f (ShortComplex.mk a b hab) hSE hreg
  have hrow2 := closedFibreGamma_shortExact A f
    (ShortComplex.mk φ.onClosedFibre ψ.onClosedFibre hT.zero_closedFibre) hT.closedFibre
  -- the two rows, as linear maps
  have hrow : ∀ {S : ShortComplex (ModuleCat A)}, S.ShortExact →
      Function.Injective S.f.hom ∧ Function.Surjective S.g.hom ∧
        Function.Exact S.f.hom S.g.hom := fun h =>
    ⟨(ModuleCat.mono_iff_injective _).mp h.mono_f, (ModuleCat.epi_iff_surjective _).mp h.epi_g,
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h.exact⟩
  obtain ⟨hu, hv, huv⟩ := hrow hrow1
  obtain ⟨hs, ht, hst⟩ := hrow hrow2
  -- the two commuting squares
  have hsqleft : ((closedFibreGammaFunctor A f).map φ.onClosedFibre).hom.comp
        P.closedFibreMap.hom =
      Q.closedFibreMap.hom.comp ((closedFibreSectionsFunctor A f).map a).hom := by
    have h := congrArg (fun morphism => (closedFibreGammaFunctor A f).map morphism) hleft
    rw [Functor.map_comp, Functor.map_comp] at h
    exact congrArg ModuleCat.Hom.hom h.symm
  have hsqright : ((closedFibreGammaFunctor A f).map ψ.onClosedFibre).hom.comp
        Q.closedFibreMap.hom =
      N.closedFibreMap.hom.comp ((closedFibreSectionsFunctor A f).map b).hom := by
    have h := congrArg (fun morphism => (closedFibreGammaFunctor A f).map morphism) hright
    rw [Functor.map_comp, Functor.map_comp] at h
    exact congrArg ModuleCat.Hom.hom h.symm
  -- finiteness of the outer kernels and cokernels
  have hkP := ModuleCat.isFiniteLength_of_iso (ModuleCat.kernelIsoKer P.closedFibreMap)
    (kernel_finiteLength A f T P)
  have hcP := ModuleCat.isFiniteLength_of_iso
    (ModuleCat.cokernelIsoRangeQuotient P.closedFibreMap) (cokernel_finiteLength A f T P)
  have hkN := ModuleCat.isFiniteLength_of_iso (ModuleCat.kernelIsoKer N.closedFibreMap)
    (kernel_finiteLength A f R N)
  have hcN := ModuleCat.isFiniteLength_of_iso
    (ModuleCat.cokernelIsoRangeQuotient N.closedFibreMap) (cokernel_finiteLength A f R N)
  obtain ⟨-, -, hindex⟩ := Module.lengthIndex_add_of_ladder
    ((closedFibreSectionsFunctor A f).map a).hom
    ((closedFibreSectionsFunctor A f).map b).hom
    ((closedFibreGammaFunctor A f).map φ.onClosedFibre).hom
    ((closedFibreGammaFunctor A f).map ψ.onClosedFibre).hom
    P.closedFibreMap.hom Q.closedFibreMap.hom N.closedFibreMap.hom
    hu hv huv hs ht hst hsqleft hsqright hkP hcP hkN hcN
  unfold PreparedExtension.eulerCharacteristic
  rw [ModuleCat.length_eq_of_iso (ModuleCat.kernelIsoKer P.closedFibreMap),
    ModuleCat.length_eq_of_iso (ModuleCat.cokernelIsoRangeQuotient P.closedFibreMap),
    ModuleCat.length_eq_of_iso (ModuleCat.kernelIsoKer Q.closedFibreMap),
    ModuleCat.length_eq_of_iso (ModuleCat.cokernelIsoRangeQuotient Q.closedFibreMap),
    ModuleCat.length_eq_of_iso (ModuleCat.kernelIsoKer N.closedFibreMap),
    ModuleCat.length_eq_of_iso (ModuleCat.cokernelIsoRangeQuotient N.closedFibreMap)]
  exact hindex


/-- **Stacks Project, Tag 0F26.** The Euler characteristic of a coherent triple is additive
along a short exact sequence of coherent triples: for any prepared extensions `P`, `Q` and `N`
of the three terms, the Euler characteristic of `Q` is the sum of those of `P` and `N`. -/
@[stacks 0F26]
public theorem eulerCharacteristic_add_of_shortExact
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (f : A)
    (hf : f ∈ IsLocalRing.maximalIdeal A)
    {T S R : CoherentTriple A f} {φ : T.Hom S} {ψ : S.Hom R}
    (hT : CoherentTriple.ShortExact φ ψ)
    (P : PreparedExtension A f T) (Q : PreparedExtension A f S)
    (N : PreparedExtension A f R) :
    Q.eulerCharacteristic = P.eulerCharacteristic + N.eulerCharacteristic := by
  obtain ⟨W, bW, hopenW, hclosedW⟩ := exists_middle_preparedExtension A f ψ Q N
  obtain ⟨alphaK, alpha₀K, hopenK, hclosedK⟩ :=
    exists_sub_comparison A hT W N bW hopenW hclosedW
  obtain ⟨alphaI, alpha₀I, hopenI, hclosedI⟩ :=
    exists_quot_comparison A hT W N bW alphaK alpha₀K hopenK hclosedK
  have : W.F'.IsCoherent := W.coherent
  have : N.F'.IsCoherent := N.coherent
  have hKcoh : (kernel bW).IsCoherent := SheafOfModules.kernel_isCoherent bW
  have hIcoh : (cokernel (kernel.ι bW)).IsCoherent :=
    SheafOfModules.cokernel_isCoherent (kernel.ι bW)
  have hregK := regular_of_mono A f (kernel.ι bW) W.regular
  have hregI := regular_of_mono A f (Abelian.factorThruCoimage bW) N.regular
  have hmono₀ : Mono ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
      φ.onClosedFibre) := by
    have := hT.closedFibre.mono_f
    infer_instance
  have hepi : Epi ((Scheme.Modules.pullback
      ((puncturedClosedFibre A f).ι ≫ closedImmersion A f)).map
      (cokernel.π (kernel.ι bW))) := inferInstance
  have hSE : (ShortComplex.mk (kernel.ι bW) (cokernel.π (kernel.ι bW))
      (cokernel.condition (kernel.ι bW))).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (kernel.ι bW))
      mono_f := inferInstance
      epi_g := inferInstance }
  have hmid := PreparedExtension.eulerCharacteristic_add_of_shortExact A f hT
    (preparedExtensionOfSub A φ hmono₀ W (kernel bW) hKcoh hregK (kernel.ι bW)
      alphaK alpha₀K hopenK hclosedK)
    W
    (preparedExtensionOfQuot A ψ W (cokernel (kernel.ι bW)) hIcoh hregI
      (cokernel.π (kernel.ι bW)) hepi alphaI alpha₀I hopenI hclosedI)
    (kernel.ι bW) (cokernel.π (kernel.ι bW)) (cokernel.condition (kernel.ι bW)) hSE
    hclosedK hclosedI
  rw [PreparedExtension.eulerCharacteristic_eq A f hf S Q W, hmid,
    PreparedExtension.eulerCharacteristic_eq A f hf T
      (preparedExtensionOfSub A φ hmono₀ W (kernel bW) hKcoh hregK (kernel.ι bW)
        alphaK alpha₀K hopenK hclosedK) P,
    PreparedExtension.eulerCharacteristic_eq A f hf R
      (preparedExtensionOfQuot A ψ W (cokernel (kernel.ι bW)) hIcoh hregI
        (cokernel.π (kernel.ι bW)) hepi alphaI alpha₀I hopenI hclosedI) N]

end Stacks.Algebraization

end
