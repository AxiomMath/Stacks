module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitFinitePresentationSite
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.ClosedImmersionIntoFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.PushforwardFinite
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FiniteTypePushforward
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.StalkFinitePresentation
public import StacksFrontier.AlgebraicGeometry.QcohPushforwardOpen.Basic
public import StacksFrontier.RingTheory.Flat.OpenFlatLocus
public import StacksFrontier.Topology.Sheaves.Modules.ClosedImmersion
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections
import StacksFrontier.RingTheory.Flat.Finiteness
import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.FlatLocus

/-!
# Finite presentation from a dense open

A quasi-coherent module of finite type which is flat over the base is finitely presented if it
is finitely presented over a retrocompact, scheme-theoretically dense open of the base.  The
same holds for a morphism in place of a module: a flat morphism locally of finite type which is
locally of finite presentation over such an open is locally of finite presentation.

## Main definitions

There are no new definitions.

## Main results

* `isFinitePresentation_of_isFlatOver_of_retrocompact_dense_open`, in the namespace
  `AlgebraicGeometry.FinitePresentationFromDenseOpen`: **[Stacks, Tag 081N]**. Finite
  presentation descends from the inverse image of a retrocompact, scheme-theoretically dense
  open of the base.
* `locallyOfFinitePresentation_of_flat_of_retrocompact_dense_open`, in the same namespace:
  **[Stacks, Tag 081P]**. A flat morphism locally of finite type which is locally of finite
  presentation over a retrocompact, scheme-theoretically dense open of the target is locally of
  finite presentation.

## Implementation notes

Restriction to the inverse image of the open is represented by pullback of modules along its
open immersion. Flatness over the base is the stalkwise predicate
`AlgebraicGeometry.IsFlatOver` on the underlying morphism of ringed spaces.

Tag 081P is deduced from Tag 081N as in the source: local finite presentation of a morphism may
be tested on affine opens of source and target, and over an affine base an affine source
embeds as a closed subscheme of a scheme of finite presentation
(`AlgebraicGeometry.exists_finitePresentation_closedImmersion`, Tag 01ZG).  Tag 081N applied to
the direct image of the structure sheaf along that closed immersion makes the direct image
finitely presented, hence the ideal sheaf of finite type by Tag 01BP, hence the closed
immersion of finite presentation by Tag 01TV.  The restricted morphism into the affine base is
then a composition of two morphisms locally of finite presentation.

The restriction of the given morphism to an affine open `W` of the target is again locally of
finite presentation over the retrocompact scheme-theoretically dense open `W ∩ U`, which is the
content of the two auxiliary statements `locallyOfFinitePresentation_restrict_inter` and
`isSchemeTheoreticallyDense_preimage_ι`.

## References

* [The Stacks Project, Tag 081N](https://stacks.math.columbia.edu/tag/081N)
* [The Stacks Project, Tag 081P](https://stacks.math.columbia.edu/tag/081P)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.FinitePresentationFromDenseOpen

universe u

attribute [local instance] IsAffineOpen.isOpenImmersion_fromSpec

private theorem localized_liftQ_injective_of_detecting
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module S M]
    {n k : ℕ} (a : Fin n → R)
    (ha : Function.Injective fun r : R ↦ fun i : Fin n ↦ algebraMap R (Localization.Away (a i)) r)
    (f : (Fin k → S) →ₗ[S] M) (L : Submodule S (Fin k → S)) (hL : L ≤ LinearMap.ker f)
    (hden : ∀ i, ∀ x ∈ LinearMap.ker f, ∃ m : ℕ, algebraMap R S (a i) ^ m • x ∈ L)
    (g : S) [Module.Flat R (LocalizedModule.Away g ((Fin k → S) ⧸ L))] :
    Function.Injective (LocalizedModule.map (Submonoid.powers g) (L.liftQ f hL)) := by
  apply Submodule.localized_liftQ_injective (Submonoid.powers g) f L hL
  intro x hx
  apply Module.eq_zero_of_forall_exists_smul_eq_zero_of_flat
    (fun i : Fin n ↦ Submonoid.powers (a i)) ha
  intro i
  obtain ⟨m, hm⟩ := hden i x hx
  refine ⟨⟨a i ^ m, ⟨m, rfl⟩⟩, ?_⟩
  rw [← algebraMap_smul S (a i ^ m), map_pow, LocalizedModule.smul'_mk, ← map_smul,
    show L.mkQ (algebraMap R S (a i) ^ m • x) = 0 from (Submodule.Quotient.mk_eq_zero L).mpr hm]
  exact LocalizedModule.zero_mk _

private theorem exists_away_finitePresentation_of_dense_localizations
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [AddCommGroup M] [Module S M]
    [Module R M] [IsScalarTower R S M] [Module.Finite S M]
    {n : ℕ} (a : Fin n → R)
    (ha : Function.Injective fun r : R ↦ fun i : Fin n ↦ algebraMap R (Localization.Away (a i)) r)
    (hfp : ∀ i, Module.FinitePresentation (Localization.Away (algebraMap R S (a i)))
      (LocalizedModule.Away (algebraMap R S (a i)) M))
    (q : PrimeSpectrum S)
    (hqfp : Module.FinitePresentation (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal M))
    (hqflat : Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)) :
    ∃ g ∉ q.asIdeal, Module.FinitePresentation (Localization.Away g)
      (LocalizedModule.Away g M) := by
  classical
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' S M
  let K : Submodule S (Fin k → S) := LinearMap.ker f
  let T : (Fin n ⊕ Unit) → Submonoid S := fun i =>
    match i with
    | Sum.inl j => Submonoid.powers (algebraMap R S (a j))
    | Sum.inr _ => q.asIdeal.primeCompl
  have hK : ∀ i : Fin n ⊕ Unit, (K.localized (T i)).FG := by
    rintro (j | j)
    · have : Module.FinitePresentation (Localization (T (Sum.inl j)))
          (LocalizedModule (T (Sum.inl j)) M) := by
        simpa [T, LocalizedModule.Away] using hfp j
      exact Submodule.fg_localized_ker (T (Sum.inl j)) f hf
    · have : Module.FinitePresentation (Localization (T (Sum.inr j)))
          (LocalizedModule (T (Sum.inr j)) M) := by
        simpa [T] using hqfp
      exact Submodule.fg_localized_ker (T (Sum.inr j)) f hf
  obtain ⟨L, hL, hLfg, hLeq⟩ := Submodule.exists_fg_le_forall_localized_eq T K hK
  have hden (i : Fin n ⊕ Unit) (x : Fin k → S) (hx : x ∈ K) :
      ∃ t : T i, (t : S) • x ∈ L :=
    Submodule.exists_smul_mem_of_localized_le (T i) (le_of_eq (hLeq i).symm) hx
  have hfp' : Module.FinitePresentation S ((Fin k → S) ⧸ L) :=
    Module.finitePresentation_of_surjective L.mkQ L.mkQ_surjective
      (by simpa only [Submodule.ker_mkQ] using hLfg)
  let f' := L.liftQ f hL
  have hf' : Function.Surjective f' := fun m ↦ let ⟨x, hx⟩ := hf m; ⟨L.mkQ x, hx⟩
  have hqi : Function.Injective (LocalizedModule.map q.asIdeal.primeCompl f') := by
    apply Submodule.localized_liftQ_injective q.asIdeal.primeCompl f L hL
    intro x hx
    obtain ⟨t, ht⟩ := hden (Sum.inr ()) x hx
    apply (IsLocalizedModule.eq_zero_iff q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl ((Fin k → S) ⧸ L))).mpr
    refine ⟨⟨t, t.property⟩, ?_⟩
    change (t : S) • L.mkQ x = 0
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero L).mpr ht
  have hflatq : Module.Flat R
      (LocalizedModule.AtPrime q.asIdeal ((Fin k → S) ⧸ L)) :=
    Module.Flat.of_linearEquiv ((LinearEquiv.ofBijective
      (LocalizedModule.map q.asIdeal.primeCompl f')
      ⟨hqi, LocalizedModule.map_surjective q.asIdeal.primeCompl f' hf'⟩).restrictScalars R)
  obtain ⟨g, hg, hflatg⟩ := Module.exists_away_flat_of_flat_atPrime (R := R) q hflatq
  have hgi : Function.Injective (LocalizedModule.map (Submonoid.powers g) f') :=
    localized_liftQ_injective_of_detecting a ha f L hL (fun i x hx ↦ by
      obtain ⟨⟨_, m, rfl⟩, ht⟩ := hden (Sum.inl i) x hx
      exact ⟨m, ht⟩) g
  exact ⟨g, hg, Module.FinitePresentation.of_equiv (LinearEquiv.ofBijective
    (LocalizedModule.map (Submonoid.powers g) f')
    ⟨hgi, LocalizedModule.map_surjective (Submonoid.powers g) f' hf'⟩)⟩

private theorem finitePresentation_of_dense_localizations
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [AddCommGroup M] [Module S M]
    [Module R M] [IsScalarTower R S M] [Module.Finite S M]
    {n : ℕ} (a : Fin n → R)
    (ha : Function.Injective fun r : R ↦ fun i : Fin n ↦ algebraMap R (Localization.Away (a i)) r)
    (hfp : ∀ i, Module.FinitePresentation (Localization.Away (algebraMap R S (a i)))
      (LocalizedModule.Away (algebraMap R S (a i)) M))
    (hqfp : ∀ q : PrimeSpectrum S,
      Module.FinitePresentation (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal M))
    (hqflat : ∀ q : PrimeSpectrum S,
      Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)) :
    Module.FinitePresentation S M := by
  let t : Set S := {g | Module.FinitePresentation (Localization.Away g)
    (LocalizedModule.Away g M)}
  have ht : Ideal.span t = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal (Ideal.span t) hne
    obtain ⟨g, hgq, hfg⟩ := exists_away_finitePresentation_of_dense_localizations
      a ha hfp ⟨q, hq.isPrime⟩ (hqfp ⟨q, hq.isPrime⟩) (hqflat ⟨q, hq.isPrime⟩)
    exact hgq (hle (Ideal.subset_span hfg))
  exact Module.FinitePresentation.of_localizationSpan t ht (fun g => g.property)

private theorem affine_module_finitePresentation_of_globalSections
    {R : CommRingCat.{u}} (F : (Spec R).Modules) [F.IsQuasicoherent]
    (h : Module.FinitePresentation R Γ(F, ⊤)) :
    SheafOfModules.IsFinitePresentation.{u, u, u} F :=
  (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso
    (@asIso _ _ _ _ F.fromTildeΓ
      (@Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent R F inferInstance))
    ((AlgebraicGeometry.tilde_isFinitePresentation_iff (ModuleCat.of R Γ(F, ⊤))).2 h)

private theorem globalSections_finitePresentation_of_affine_module
    {R : CommRingCat.{u}} (F : (Spec R).Modules) [F.IsQuasicoherent]
    [SheafOfModules.IsFinitePresentation.{u, u, u} F] :
    Module.FinitePresentation R Γ(F, ⊤) :=
  (AlgebraicGeometry.tilde_isFinitePresentation_iff (ModuleCat.of R Γ(F, ⊤))).mp
    ((SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso
      (asIso F.fromTildeΓ).symm inferInstance)

/-- Finite presentation of the pullback along an open immersion is that of the restriction. -/
private theorem isFinitePresentation_pullback_iff_restrict
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i] (F : X.Modules) :
    ((Scheme.Modules.pullback i).obj F).IsFinitePresentation ↔
      (F.restrict i).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_iff_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback i).app F).symm

private theorem finitePresentation_restrict_factor
    {X Y Z T : Scheme.{u}} (F : X.Modules) (i : Y ⟶ X) [IsOpenImmersion i]
    (k : Z ⟶ Y) [IsOpenImmersion k] (j : T ⟶ X) [IsOpenImmersion j]
    (d : Z ⟶ T) [IsOpenImmersion d] (h : k ≫ i = d ≫ j)
    (hfp : ((Scheme.Modules.pullback i).obj F).IsFinitePresentation) :
    ((F.restrict j).restrict d).IsFinitePresentation := by
  have hI := (isFinitePresentation_pullback_iff_restrict i F).1 hfp
  let e : (F.restrict i).restrict k ≅ (F.restrict j).restrict d :=
    ((Scheme.Modules.restrictFunctorComp k i).app F).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr h).app F ≪≫
        (Scheme.Modules.restrictFunctorComp d j).app F
  exact (SheafOfModules.isFinitePresentation Z.ringCatSheaf).prop_of_iso e
    (AlgebraicGeometry.finitePresentation_restrict k (F.restrict i))

private lemma isFiniteType_of_scheme_iso {X : Scheme.{u}} {F G : X.Modules}
    (e : F ≅ G) [F.IsFiniteType] : G.IsFiniteType := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  let q' : G.LocalGeneratorsData.{u, u, u, u} := {
    I := q.I
    X := q.X
    coversTop := q.coversTop
    generators := fun i => by
      have : (q.generators i).IsFiniteType := hq.isFiniteType i
      exact (q.generators i).ofEpi
        ((SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e).hom
  }
  have hq' : q'.IsFiniteType := by
    constructor
    intro i
    dsimp [q']
    have : (q.generators i).IsFiniteType := hq.isFiniteType i
    infer_instance
  exact SheafOfModules.IsFiniteType.mk.{u, u, u} ⟨q', hq'⟩

private lemma moduleFinite_of_isFiniteType
    {R : CommRingCat.{u}} (F : (Spec R).Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    Module.Finite (↑R) (AlgebraicGeometry.moduleSpecΓFunctor.obj F) :=
  (AlgebraicGeometry.tilde_isFiniteType_iff (moduleSpecΓFunctor.obj F)).mp
    (isFiniteType_of_scheme_iso (asIso F.fromTildeΓ).symm)

private theorem flatOverAt_iff_flat_localizedSections
    {B : CommRingCat.{u}} {S : Scheme.{u}} {V : S.Opens}
    (hV : IsAffineOpen V) (φ : Γ(S, V) ⟶ B)
    (F : (Spec B).Modules) [F.IsQuasicoherent] (q : Spec B) :
    AlgebraicGeometry.IsFlatOverAt (Spec.map φ ≫ hV.fromSpec).toLRSHom.toShHom F q ↔
      let M := AlgebraicGeometry.moduleSpecΓFunctor.obj F
      letI : q.asIdeal.IsPrime := q.2
      letI : Algebra Γ(S, V) B := φ.hom.toAlgebra
      letI : Module Γ(S, V) (↑M) := Module.compHom _ φ.hom
      letI : IsScalarTower Γ(S, V) B (↑M) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      letI : Module B ((AlgebraicGeometry.tilde M).presheaf.stalk q) :=
        tilde.instModuleCarrierCarrierStalkAbPresheaf M q
      letI : Module Γ(S, V) ((AlgebraicGeometry.tilde M).presheaf.stalk q) :=
        Module.compHom _ φ.hom
      letI : Module Γ(S, V) (LocalizedModule.AtPrime q.asIdeal (↑M)) :=
        Module.compHom _ φ.hom
      Module.Flat Γ(S, V) (LocalizedModule.AtPrime q.asIdeal (↑M)) := by
  let M := AlgebraicGeometry.moduleSpecΓFunctor.obj F
  let G := AlgebraicGeometry.tilde M
  let e : F ≅ G := (asIso F.fromTildeΓ).symm
  let : q.asIdeal.IsPrime := q.2
  let : Algebra Γ(S, V) B := φ.hom.toAlgebra
  let : Module Γ(S, V) (↑M) := Module.compHom _ φ.hom
  let : IsScalarTower Γ(S, V) B (↑M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module B ((AlgebraicGeometry.tilde M).presheaf.stalk q) :=
    tilde.instModuleCarrierCarrierStalkAbPresheaf M q
  let : Module Γ(S, V) ((AlgebraicGeometry.tilde M).presheaf.stalk q) :=
    Module.compHom _ φ.hom
  let : Module Γ(S, V) (LocalizedModule.AtPrime q.asIdeal (↑M)) :=
    Module.compHom _ φ.hom
  change AlgebraicGeometry.IsFlatOverAt
      (Spec.map φ ≫ hV.fromSpec).toLRSHom.toShHom F q ↔
    Module.Flat Γ(S, V) (LocalizedModule.AtPrime q.asIdeal (↑M))
  rw [flatOverAt_iff_of_iso (Spec.map φ ≫ hV.fromSpec) e q]
  have hx : (Spec.map φ ≫ hV.fromSpec) q ∈ V := by
    change (Spec.map φ q) ∈ hV.fromSpec ⁻¹ᵁ V
    rw [hV.fromSpec_preimage_self]
    trivial
  rw [flatOverAt_iff_flat_sectionsStalk
    (Spec.map φ ≫ hV.fromSpec) G hV q hx]
  let N := G.presheaf.stalk q
  let : Module ((Spec B).presheaf.stalk q) N :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf G q
  let : Algebra B ((Spec B).presheaf.stalk q) := StructureSheaf.stalkAlgebra B q
  let moduleS : Module (S.presheaf.stalk ((Spec.map φ ≫ hV.fromSpec) q)) N :=
    Module.compHom N ((Spec.map φ ≫ hV.fromSpec).stalkMap q).hom
  let moduleLeft : Module Γ(S, V) N :=
    let : Module (S.presheaf.stalk ((Spec.map φ ≫ hV.fromSpec) q)) N := moduleS
    Module.compHom N (S.presheaf.germ V _ hx).hom
  let moduleRight : Module Γ(S, V) N := Module.compHom N φ.hom
  have hmodule : moduleLeft = moduleRight := by
    apply Module.ext'
    intro a m
    change ((Spec.map φ ≫ hV.fromSpec).stalkMap q).hom
      ((S.presheaf.germ V _ hx).hom a) • m = (φ.hom a) • m
    have hval : ((Spec.map φ ≫ hV.fromSpec).stalkMap q).hom ((S.presheaf.germ V _ hx).hom a) =
        algebraMap B ((Spec B).presheaf.stalk q) (φ.hom a) :=
      congrArg (fun t : Γ(S, V) ⟶ (Spec B).presheaf.stalk q => t a)
        (germ_spec_comp_stalkMap hV φ q hx)
    exact congrArg (· • m) hval
  change @Module.Flat Γ(S, V) N _ _ moduleLeft ↔
    @Module.Flat Γ(S, V) (LocalizedModule.AtPrime q.asIdeal (↑M)) _ _ _
  rw [hmodule]
  simpa [N, G] using (flat_tilde_stalk_iff_localizedModule φ M q)

private theorem restrictStalkMap_smul
    {W X : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (w : W)
    (a : X.presheaf.stalk (j w))
    (m : (F.restrict j).presheaf.stalk w) :
    letI : Module (W.presheaf.stalk w) ((F.restrict j).presheaf.stalk w) :=
      AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf (F.restrict j) w
    letI : Module (X.presheaf.stalk (j w)) (F.presheaf.stalk (j w)) :=
      AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf F (j w)
    AlgebraicGeometry.restrictStalkMap j F w ((j.stalkMap w).hom a • m) =
      a • AlgebraicGeometry.restrictStalkMap j F w m := by
  let : Module (W.presheaf.stalk w) ((F.restrict j).presheaf.stalk w) :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf (F.restrict j) w
  let : Module (X.presheaf.stalk (j w)) (F.presheaf.stalk (j w)) :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf F (j w)
  let G := F.restrict j
  obtain ⟨V, hV, r, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨T, hT, t, rfl⟩ := G.presheaf.exists_germ_eq m
  let T' : W.Opens := T ⊓ j ⁻¹ᵁ V
  have hT' : w ∈ T' := ⟨hT, hV⟩
  let r' : Γ(W, T') := W.presheaf.map (homOfLE inf_le_right).op (j.app V r)
  let t' : Γ(G, T') := G.presheaf.map (homOfLE inf_le_left).op t
  let J : X.Opens := j ''ᵁ T'
  have hJ : j w ∈ J := ⟨w, hT', rfl⟩
  have hJV : J ≤ V := by
    rintro _ ⟨z, hz, rfl⟩
    exact hz.2
  let rJ : Γ(X, J) := X.presheaf.map (homOfLE hJV).op r
  have hr : (j.stalkMap w).hom (X.presheaf.germ V (j w) hV r) =
      W.presheaf.germ T' w hT' r' := by
    rw [Scheme.Hom.germ_stalkMap_apply]
    exact (W.presheaf.germ_res_apply
      (homOfLE inf_le_right) w hT' (j.app V r)).symm
  have hm : G.presheaf.germ T w hT t = G.presheaf.germ T' w hT' t' :=
    (G.presheaf.germ_res_apply (homOfLE inf_le_left) w hT' t).symm
  have hrJ : X.presheaf.germ V (j w) hV r = X.presheaf.germ J (j w) hJ rJ :=
    (X.presheaf.germ_res_apply (homOfLE hJV) (j w) hJ r).symm
  have hscalar : (j.appIso T').inv r' = rJ := (congrArg (fun z : Γ(X, V) ⟶ Γ(X, J) => z r)
    (Scheme.Hom.appLE_appIso_inv j (inf_le_right : T' ≤ j ⁻¹ᵁ V)) :)
  let eT : Γ(G, T') ≅ Γ(F, J) := F.restrictAppIso j T'
  let tF : Γ(F, J) := eT.hom t'
  have hsection : eT.hom (r' • t') = rJ • tF := by
    have h := Scheme.Modules.smul_restrictAppIso_hom_apply j F T' r' t'
    change eT.hom (r' • t') = (j.appIso T').inv r' • tF at h
    rwa [hscalar] at h
  rw [hr, hm, hrJ]
  calc
    _ = AlgebraicGeometry.restrictStalkMap j F w (G.presheaf.germ T' w hT' (r' • t')) :=
      congrArg (AlgebraicGeometry.restrictStalkMap j F w)
        (PresheafOfModules.germ_smul G.val w T' hT' r' t').symm
    _ = F.presheaf.germ J (j w) hJ (eT.hom (r' • t')) := (congrArg
        (fun z : Γ(G, T') ⟶ F.presheaf.stalk (j w) => z (r' • t'))
        (Scheme.Modules.germ_restrictStalkNatIso_hom_app j w F hT') :)
    _ = F.presheaf.germ J (j w) hJ (rJ • tF) := by rw [hsection]
    _ = X.presheaf.germ J (j w) hJ rJ • F.presheaf.germ J (j w) hJ tF :=
      PresheafOfModules.germ_smul F.val (j w) J hJ rJ tF
    _ = _ := congrArg (X.presheaf.germ J (j w) hJ rJ • ·)
      (congrArg (fun z : Γ(G, T') ⟶ F.presheaf.stalk (j w) => z t')
        (Scheme.Modules.germ_restrictStalkNatIso_hom_app j w F hT')).symm

private theorem flatOverAt_iff_restrict
    {W X S : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    (f : X ⟶ S) (F : X.Modules) (w : W) :
    AlgebraicGeometry.IsFlatOverAt (j ≫ f).toLRSHom.toShHom (F.restrict j) w ↔
      AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F (j w) := by
  let G := F.restrict j
  let : Module (W.presheaf.stalk w) (G.presheaf.stalk w) :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf G w
  let : Module (X.presheaf.stalk (j w)) (F.presheaf.stalk (j w)) :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf F (j w)
  let : Module (S.presheaf.stalk (f (j w))) (G.presheaf.stalk w) :=
    Module.compHom _ ((j ≫ f).stalkMap w).hom
  let : Module (S.presheaf.stalk (f (j w))) (F.presheaf.stalk (j w)) :=
    Module.compHom _ (f.stalkMap (j w)).hom
  have hsmul (a : S.presheaf.stalk (f (j w))) (m : G.presheaf.stalk w) :
      AlgebraicGeometry.restrictStalkMap j F w (a • m) =
        a • AlgebraicGeometry.restrictStalkMap j F w m := by
    change AlgebraicGeometry.restrictStalkMap j F w (((j ≫ f).stalkMap w).hom a • m) =
      (f.stalkMap (j w)).hom a • AlgebraicGeometry.restrictStalkMap j F w m
    rw [Scheme.Hom.stalkMap_comp]
    exact restrictStalkMap_smul j F w ((f.stalkMap (j w)).hom a) m
  have : IsIso (AlgebraicGeometry.restrictStalkMap j F w) := by
    unfold AlgebraicGeometry.restrictStalkMap
    exact (Scheme.Modules.restrictStalkNatIso j w).app F |>.isIso_hom
  let e : G.presheaf.stalk w ≃ₗ[S.presheaf.stalk (f (j w))]
      F.presheaf.stalk (j w) := LinearEquiv.ofBijective
      { toFun := AlgebraicGeometry.restrictStalkMap j F w
        map_add' := (AlgebraicGeometry.restrictStalkMap j F w).hom.map_add
        map_smul' := hsmul }
      (ConcreteCategory.bijective_of_isIso (AlgebraicGeometry.restrictStalkMap j F w))
  change Module.Flat (S.presheaf.stalk (f (j w))) (G.presheaf.stalk w) ↔
    Module.Flat (S.presheaf.stalk (f (j w))) (F.presheaf.stalk (j w))
  exact Module.Flat.equiv_iff e

private theorem finitePresentation_localizedModule_of_sections
    {P A M N : Type*} [CommRing P] [CommRing A] [Algebra P A]
    [AddCommGroup M] [Module P M] [AddCommGroup N] [Module P N]
    [Module A N] (hsc : IsScalarTower P A N)
    (T : Submonoid P) [IsLocalization T A]
    (f : M →ₗ[P] N) (hf : IsLocalizedModule T f)
    [Module.FinitePresentation A N] :
    Module.FinitePresentation (Localization T) (LocalizedModule T M) := by
  let e := IsLocalization.algEquiv T (Localization T) A
  let : Algebra (Localization T) A := e.toRingHom.toAlgebra
  let : Module (Localization T) N := Module.compHom N e.toRingHom
  have : IsScalarTower (Localization T) A N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower P (Localization T) N :=
    IsScalarTower.of_algebraMap_smul fun r m => by
      change e (algebraMap P (Localization T) r) • m = r • m
      rw [e.commutes, algebraMap_smul]
  have : Module.FinitePresentation (Localization T) A :=
    Module.FinitePresentation.of_equiv
      (LinearEquiv.ofBijective (Algebra.linearMap (Localization T) A) e.bijective)
  have : Module.FinitePresentation (Localization T) N :=
    Module.FinitePresentation.trans (Localization T) N A
  exact Module.FinitePresentation.of_equiv
    ((IsLocalizedModule.iso T f).extendScalarsOfIsLocalization T (Localization T)).symm

private theorem finitePresentation_localizedSectionsAtPrime
    {B : CommRingCat.{u}} (F : (Spec B).Modules) [F.IsQuasicoherent]
    (q : Spec B)
    (hfp : letI : q.asIdeal.IsPrime := q.2
      letI : Module ((Spec B).presheaf.stalk q) (F.presheaf.stalk q) :=
        AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf F q
      Module.FinitePresentation ((Spec B).presheaf.stalk q)
      (F.presheaf.stalk q)) :
    letI : q.asIdeal.IsPrime := q.2
    Module.FinitePresentation (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal
        (AlgebraicGeometry.moduleSpecΓFunctor.obj F)) := by
  let M := AlgebraicGeometry.moduleSpecΓFunctor.obj F
  let G := AlgebraicGeometry.tilde M
  let : q.asIdeal.IsPrime := q.2
  have hIso : IsIso F.fromTildeΓ :=
    @Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent B F inferInstance
  let e : G ≅ F := @asIso _ _ _ _ F.fromTildeΓ hIso
  let : Algebra B ((Spec B).presheaf.stalk q) := StructureSheaf.stalkAlgebra B q
  let : IsLocalization.AtPrime ((Spec B).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk B q
  let : Module ((Spec B).presheaf.stalk q) (G.presheaf.stalk q) :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf G q
  let : Module B (G.presheaf.stalk q) :=
    tilde.instModuleCarrierCarrierStalkAbPresheaf M q
  let : Module ((Spec B).presheaf.stalk q) (F.presheaf.stalk q) :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf F q
  have : Module.FinitePresentation ((Spec B).presheaf.stalk q)
      (F.presheaf.stalk q) := hfp
  have hfpG : Module.FinitePresentation ((Spec B).presheaf.stalk q)
      (G.presheaf.stalk q) := Module.FinitePresentation.of_equiv
        (_root_.AlgebraicGeometry.moduleStalkLinearEquiv e q).symm
  let f : M →ₗ[B] G.presheaf.stalk q :=
    (tilde.toStalk M q).hom
  have : IsLocalizedModule q.asIdeal.primeCompl f :=
    tilde.instIsLocalizedModuleCarrierCarrierOfCarrierStalkAbPresheafPrimeComplAsIdealHomToStalk M q
  have : IsScalarTower B ((Spec B).presheaf.stalk q) (G.presheaf.stalk q) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact finitePresentation_localizedModule_of_sections
    (A := (Spec B).presheaf.stalk q) inferInstance q.asIdeal.primeCompl f inferInstance

private theorem exists_finite_basicOpen_cover {R : CommRingCat.{u}}
    (U : (Spec R).Opens) (hUc : IsCompact (U : Set (Spec R))) :
    ∃ n : ℕ, ∃ a : Fin n → R, U = ⨆ i, PrimeSpectrum.basicOpen (a i) := by
  classical
  obtain ⟨ι, hι, a, ha⟩ := PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact U hUc
  have : Finite ι := hι
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  refine ⟨n, fun i ↦ a (e.symm i), ?_⟩
  rw [ha]
  exact Equiv.iSup_congr e (fun i ↦
    congrArg PrimeSpectrum.basicOpen (congrArg a (e.symm_apply_apply i)))

private theorem schemeTheoreticallyDominant_of_dense_open
    {S : Scheme.{u}} (U : S.Opens)
    (hUdense : AlgebraicGeometry.Scheme.Opens.IsSchemeTheoreticallyDense U) :
    IsSchemeTheoreticallyDominant U.ι := by
  let V : S.Opens := ⊤
  let e : (V.ι ⁻¹ᵁ U).toScheme ≅ U := Scheme.Opens.isoOfLE le_top
  have hcomp : IsSchemeTheoreticallyDominant (e.hom ≫ U.ι) := by
    rw [Scheme.Opens.isoOfLE_hom_ι]
    have : MorphismProperty.IsStableUnderComposition
        (@IsSchemeTheoreticallyDominant) :=
      MorphismProperty.IsMultiplicative.toIsStableUnderComposition
    have : IsIso V.ι := (S.topIso).isIso_hom
    exact MorphismProperty.comp_mem _ _ _ (hUdense V) inferInstance
  have hker := IsSchemeTheoreticallyDominant.ker_eq_bot (e.hom ≫ U.ι)
  rw [Scheme.Hom.ker_comp_of_isIso] at hker
  exact (isSchemeTheoreticallyDominant_iff U.ι).2 hker

private theorem finitePresentation_localized_of_restrict
    {B : CommRingCat.{u}} (F : (Spec B).Modules) [F.IsQuasicoherent]
    (b : B)
    (hfp : letI : IsOpenImmersion (IsAffineOpen.Spec_basicOpen b).fromSpec :=
      (IsAffineOpen.Spec_basicOpen b).isOpenImmersion_fromSpec
      (F.restrict (IsAffineOpen.Spec_basicOpen b).fromSpec).IsFinitePresentation) :
    Module.FinitePresentation (Localization.Away b)
      (LocalizedModule.Away b (moduleSpecΓFunctor.obj F)) := by
  let D : (Spec B).affineOpens := ⟨PrimeSpectrum.basicOpen b, IsAffineOpen.Spec_basicOpen b⟩
  let : IsOpenImmersion D.2.fromSpec := D.2.isOpenImmersion_fromSpec
  let G := F.restrict D.2.fromSpec
  have : G.IsFinitePresentation := hfp
  have : Module.FinitePresentation Γ(Spec B, D.1) Γ(G, ⊤) :=
    globalSections_finitePresentation_of_affine_module G
  have : Module.FinitePresentation Γ(Spec B, D.1) Γ(F, D.1) :=
    Module.FinitePresentation.of_equiv (affineSectionsLinearEquiv F D.2)
  let : Algebra B Γ(Spec B, D.1) := by
    change Algebra B ((Spec.structureSheaf B).obj.obj (.op D.1))
    exact StructureSheaf.openAlgebra B _
  let : IsLocalization.Away b Γ(Spec B, D.1) := by
    change IsLocalization.Away b ((Spec.structureSheaf B).obj.obj (.op (PrimeSpectrum.basicOpen b)))
    exact StructureSheaf.IsLocalization.to_basicOpen B b
  exact finitePresentation_localizedModule_of_sections
    (A := Γ(Spec B, D.1)) (M := Γ(F, ⊤)) (N := Γ(F, D.1))
    (IsScalarTower.of_compHom B Γ(Spec B, D.1) Γ(F, D.1)) (Submonoid.powers b)
    ((modulesSpecToSheaf.obj F).obj.map D.1.leTop.op).hom
    ((isIso_fromTildeΓ_iff_isLocalizing F).mp inferInstance b)

private theorem finiteType_restrict
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (F : Y.Modules) [F.IsFiniteType] : (F.restrict j).IsFiniteType := by
  have : ((Scheme.Modules.pullback j).obj F).IsFiniteType :=
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType j.toLRSHom.toShHom F
  exact isFiniteType_of_scheme_iso
    ((Scheme.Modules.restrictFunctorIsoPullback j).app F).symm

private theorem dense_localizations_injective
    {R : CommRingCat.{u}} (D : (Spec R).Opens)
    [IsSchemeTheoreticallyDominant D.ι] [QuasiCompact D.ι]
    {n : ℕ} (a : Fin n → R) (ha : D = ⨆ i, PrimeSpectrum.basicOpen (a i)) :
    Function.Injective (fun r : R ↦ fun i : Fin n ↦
      algebraMap R (Localization.Away (a i)) r) := by
  intro r s hrs
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).injective
  apply D.ι.app_injective ⊤
  apply (Spec R).IsSheaf.section_ext
  intro x hx
  have hxD : x ∈ D := by
    obtain ⟨z, hz, rfl⟩ := hx
    exact z.2
  rw [ha] at hxD
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxD
  have hle : PrimeSpectrum.basicOpen (a i) ≤ D.ι ''ᵁ D.ι ⁻¹ᵁ ⊤ := by
    simpa using (ha ▸ le_iSup (fun i ↦ PrimeSpectrum.basicOpen (a i)) i)
  refine ⟨PrimeSpectrum.basicOpen (a i), hle, hi, ?_⟩
  let : Algebra R Γ(Spec R, PrimeSpectrum.basicOpen (a i)) := by
    change Algebra R ((Spec.structureSheaf R).obj.obj _)
    exact StructureSheaf.openAlgebra R _
  let : IsLocalization.Away (a i) Γ(Spec R, PrimeSpectrum.basicOpen (a i)) :=
    StructureSheaf.IsLocalization.to_basicOpen R (a i)
  have heq : algebraMap R Γ(Spec R, PrimeSpectrum.basicOpen (a i)) r =
      algebraMap R Γ(Spec R, PrimeSpectrum.basicOpen (a i)) s := by
    simpa using congrArg
      (IsLocalization.algEquiv (Submonoid.powers (a i))
        (Localization.Away (a i)) Γ(Spec R, PrimeSpectrum.basicOpen (a i)))
      (congrFun hrs i)
  convert! heq using 1

/-- A retrocompact open pulls back to a retrocompact open along an open immersion. -/
private theorem isRetrocompact_preimage_of_isOpenImmersion {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] {U : Y.Opens} (h : IsRetrocompact (U : Set Y)) :
    IsRetrocompact ((j ⁻¹ᵁ U : X.Opens) : Set X) :=
  IsRetrocompact.preimage_of_isOpenEmbedding (f := j.base) j.isOpenEmbedding h

private theorem quasiCompact_ι_of_isRetrocompact {X : Scheme.{u}} (U : X.Opens)
    (h : IsRetrocompact (U : Set X)) : QuasiCompact U.ι :=
  quasiCompact_iff_isSpectralMap.mpr (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp h)

private theorem finitePresentation_affine_source
    {B : CommRingCat.{u}} {S : Scheme.{u}} {V : S.Opens}
    (hV : IsAffineOpen V) (φ : Γ(S, V) ⟶ B)
    (hφ : φ.hom.FinitePresentation)
    (F : (Spec B).Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    [LocallyOfFinitePresentation (Spec.map φ ≫ hV.fromSpec)]
    (hflat : AlgebraicGeometry.IsFlatOver (Spec.map φ ≫ hV.fromSpec).toLRSHom.toShHom F)
    (U : S.Opens) (hUretro : IsRetrocompact (U : Set S))
    (hUdense : AlgebraicGeometry.Scheme.Opens.IsSchemeTheoreticallyDense U)
    (hfp : ∀ b : B, PrimeSpectrum.basicOpen b ≤ (Spec.map φ ≫ hV.fromSpec) ⁻¹ᵁ U →
      letI : IsOpenImmersion (IsAffineOpen.Spec_basicOpen b).fromSpec :=
        (IsAffineOpen.Spec_basicOpen b).isOpenImmersion_fromSpec
      (F.restrict (IsAffineOpen.Spec_basicOpen b).fromSpec).IsFinitePresentation) :
    F.IsFinitePresentation := by
  let : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  let D := hV.fromSpec ⁻¹ᵁ U
  have hDretro : IsRetrocompact (D : Set (Spec Γ(S, V))) :=
    isRetrocompact_preimage_of_isOpenImmersion hV.fromSpec hUretro
  have hDc : IsCompact (D : Set (Spec Γ(S, V))) := by
    simpa using hDretro isCompact_univ isOpen_univ
  have := quasiCompact_ι_of_isRetrocompact U hUretro
  have := quasiCompact_ι_of_isRetrocompact D hDretro
  have : IsSchemeTheoreticallyDominant U.ι :=
    schemeTheoreticallyDominant_of_dense_open U hUdense
  have : IsSchemeTheoreticallyDominant D.ι :=
    IsSchemeTheoreticallyDominant.of_isPullback
      (isPullback_morphismRestrict hV.fromSpec U)
  obtain ⟨n, a, ha⟩ := exists_finite_basicOpen_cover D hDc
  let : Algebra Γ(S, V) B := φ.hom.toAlgebra
  have : Algebra.FinitePresentation Γ(S, V) B := hφ
  let M := moduleSpecΓFunctor.obj F
  let : Module Γ(S, V) M := Module.compHom M φ.hom
  have : IsScalarTower Γ(S, V) B M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite B M := moduleFinite_of_isFiniteType F
  have hmfp : Module.FinitePresentation B M := by
    apply finitePresentation_of_dense_localizations a (dense_localizations_injective D a ha)
    · intro i
      apply finitePresentation_localized_of_restrict F (φ.hom (a i))
      apply hfp
      intro x hx
      change PrimeSpectrum.comap φ.hom x ∈ D
      rw [ha]
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx⟩
    · exact fun q ↦ finitePresentation_localizedSectionsAtPrime F q
        (Stacks.Flatness.finitePresentation_stalk_of_isFlatOverAt
          (Spec.map φ ≫ hV.fromSpec) F q (hflat q))
    · intro q
      convert! (flatOverAt_iff_flat_localizedSections hV φ F q).mp (hflat q) using 1
      apply Module.ext'
      intro r m
      induction m using LocalizedModule.induction_on with
      | _ m s =>
        change r • LocalizedModule.mk m s = (φ.hom r) • LocalizedModule.mk m s
        rw [LocalizedModule.smul'_mk, LocalizedModule.smul'_mk]
        rfl
  exact affine_module_finitePresentation_of_globalSections F hmfp

private theorem finitePresentation_affine_chart
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent]
    [LocallyOfFinitePresentation f] [F.IsFiniteType]
    (hflat : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F)
    (U : S.Opens) (hUretro : IsRetrocompact (U : Set S))
    (hUdense : AlgebraicGeometry.Scheme.Opens.IsSchemeTheoreticallyDense U)
    (hfp : ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F).IsFinitePresentation)
    (V : S.affineOpens) (W : X.affineOpens) (hle : W.1 ≤ f ⁻¹ᵁ V.1) :
    (letI : IsOpenImmersion W.2.fromSpec := W.2.isOpenImmersion_fromSpec;
      (F.restrict W.2.fromSpec).IsFinitePresentation) := by
  let : IsOpenImmersion W.2.fromSpec := W.2.isOpenImmersion_fromSpec
  let j := W.2.fromSpec
  let G := F.restrict j
  let φ := f.appLE V.1 W.1 hle
  have he : Spec.map φ ≫ V.2.fromSpec = j ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f V.2 W.2 hle
  have : G.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor j F
  have : G.IsFiniteType := finiteType_restrict j F
  have : LocallyOfFinitePresentation (Spec.map φ ≫ V.2.fromSpec) := by
    rw [he]
    infer_instance
  have hflatG : AlgebraicGeometry.IsFlatOver
      (Spec.map φ ≫ V.2.fromSpec).toLRSHom.toShHom G := by
    rw [he]
    exact fun q ↦ (flatOverAt_iff_restrict j f F q).mpr (hflat (j q))
  apply finitePresentation_affine_source V.2 φ
    (f.finitePresentation_appLE V.2 W.2 hle) G hflatG U hUretro hUdense
  intro b hb
  let d := (IsAffineOpen.Spec_basicOpen b).fromSpec
  have hrange : Set.range (d ≫ j) ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rintro _ ⟨q, rfl⟩
    have hsub : Set.range d ⊆
        ((Spec.map φ ≫ V.2.fromSpec) ⁻¹ᵁ U : Set (Spec Γ(X, W.1))) :=
      (le_of_eq (IsAffineOpen.Spec_basicOpen b).range_fromSpec).trans hb
    have hmem := hsub (Set.mem_range_self q)
    change (Spec.map φ ≫ V.2.fromSpec) (d q) ∈ U at hmem
    rw [he] at hmem
    exact ⟨⟨(d ≫ j) q, hmem⟩, rfl⟩
  let k := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι (d ≫ j) hrange
  let : IsOpenImmersion d := (IsAffineOpen.Spec_basicOpen b).isOpenImmersion_fromSpec
  exact finitePresentation_restrict_factor F (f ⁻¹ᵁ U).ι k j d
    (IsOpenImmersion.lift_fac _ _ hrange) hfp

-- The proof imports add a definitionally equal quiver instance. Preserve the instance
-- selected by the accepted statement while elaborating this declaration.
attribute [-instance] CategoryTheory.ReflQuiver.toQuiver in
/-- **Stacks Project, Tag 081N.** A quasi-coherent module of finite type, flat over the base,
which is finitely presented over the inverse image of a retrocompact scheme-theoretically dense
open of the base is finitely presented. -/
@[stacks 081N]
public theorem isFinitePresentation_of_isFlatOver_of_retrocompact_dense_open
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent]
    [LocallyOfFinitePresentation f] [F.IsFiniteType]
    (hflat : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F)
    (U : S.Opens) (hUretro : IsRetrocompact (U : Set S))
    (hUdense : AlgebraicGeometry.Scheme.Opens.IsSchemeTheoreticallyDense U)
    (hfp : ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F).IsFinitePresentation) :
    F.IsFinitePresentation := by
  classical
  have hcharts (x : X) : ∃ (V : S.affineOpens) (W : X.affineOpens),
      x ∈ W.1 ∧ W.1 ≤ f ⁻¹ᵁ V.1 := by
    obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show f x ∈ (⊤ : S.Opens) from trivial)
    obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ f ⁻¹ᵁ V from hxV)
    exact ⟨⟨V, hV⟩, ⟨W, hW⟩, hxW, hWV⟩
  choose V W hxW hWV using hcharts
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers X
    (fun x ↦ Spec Γ(X, (W x).1)) (fun x ↦ (W x).2.fromSpec)
    (fun x ↦ ⟨x, show x ∈ Set.range (W x).2.fromSpec by
      rw [(W x).2.range_fromSpec]
      exact hxW x⟩)
    (fun x ↦ (W x).2.isOpenImmersion_fromSpec)
  apply AlgebraicGeometry.isFinitePresentation_of_pullback_fpqcCover F
    (𝒰.weaken Scheme.zariskiPrecoverage_le_fpqcPrecoverage)
  intro x
  let : IsOpenImmersion (W x).2.fromSpec := (W x).2.isOpenImmersion_fromSpec
  exact (isFinitePresentation_pullback_iff_restrict (W x).2.fromSpec F).2
    (finitePresentation_affine_chart f F hflat U hUretro hUdense hfp (V x) (W x) (hWV x))

section Morphism

open CategoryTheory.Limits RingedSpaceModuleAdjunction

/-! ### Local finite presentation of a flat morphism (Tag 081P) -/

/-- Scheme-theoretic density of a retrocompact open subscheme passes to its intersection with
any open subscheme. -/
private theorem isSchemeTheoreticallyDense_preimage_ι
    {S : Scheme.{u}} (U V : S.Opens) (hUretro : IsRetrocompact (U : Set S))
    (hUdense : Scheme.Opens.IsSchemeTheoreticallyDense U) :
    Scheme.Opens.IsSchemeTheoreticallyDense (V.ι ⁻¹ᵁ U) := by
  set D : V.toScheme.Opens := V.ι ⁻¹ᵁ U
  have hDretro : IsRetrocompact (D : Set V.toScheme) :=
    isRetrocompact_preimage_of_isOpenImmersion V.ι hUretro
  have := quasiCompact_ι_of_isRetrocompact D hDretro
  have : IsSchemeTheoreticallyDominant D.ι := hUdense V
  intro W
  have hdom : IsSchemeTheoreticallyDominant (D.ι ∣_ W) :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict D.ι W).flip
  let e := Scheme.restrictRestrictComm V.toScheme D W
  have he : e.hom ≫ (W.ι ⁻¹ᵁ D).ι = D.ι ∣_ W := by
    apply (cancel_mono W.ι).mp
    rw [Category.assoc, morphismRestrict_ι]
    exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have : IsSchemeTheoreticallyDominant (e.hom ≫ (W.ι ⁻¹ᵁ D).ι) := he ▸ hdom
  simpa only [Iso.inv_hom_id_assoc] using
    (inferInstance : IsSchemeTheoreticallyDominant (e.inv ≫ e.hom ≫ (W.ι ⁻¹ᵁ D).ι))

/-- Local finite presentation over an open `U` of the target restricts to local finite
presentation over `U ∩ W` for any other open `W`. -/
private theorem locallyOfFinitePresentation_restrict_inter
    {X S : Scheme.{u}} (f : X ⟶ S) (U W : S.Opens)
    [LocallyOfFinitePresentation (f ∣_ U)] :
    LocallyOfFinitePresentation (f ∣_ W ∣_ (W.ι ⁻¹ᵁ U)) := by
  set D : W.toScheme.Opens := W.ι ⁻¹ᵁ U
  set E : U.toScheme.Opens := U.ι ⁻¹ᵁ W
  have hDE : W.ι ''ᵁ D = U.ι ''ᵁ E := by
    ext x
    constructor
    · rintro ⟨y, hyD, hyx⟩
      change W.ι y ∈ U at hyD
      exact ⟨⟨W.ι y, hyD⟩, y.property, by simpa using hyx⟩
    · rintro ⟨y, hyE, hyx⟩
      change U.ι y ∈ W at hyE
      exact ⟨⟨U.ι y, hyE⟩, y.property, by simpa using hyx⟩
  have hIso : Arrow.mk (f ∣_ W ∣_ D) ≅ Arrow.mk (f ∣_ U ∣_ E) :=
    morphismRestrictRestrict f W D ≪≫
      (morphismRestrictEq f hDE ≪≫ (morphismRestrictRestrict f U E).symm)
  have : MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (MorphismProperty.arrow_mk_iso_iff
    (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) hIso).mpr inferInstance

open Stacks.AlgebraicGeometry.ClosedImmersionTFAE in
/-- A closed immersion whose direct image of the structure sheaf is finitely presented is
locally of finite presentation: that direct image is the quotient of the structure sheaf of the
target by the ideal sheaf, so [Stacks, Tag 01BP] makes the ideal sheaf of finite type and
[Stacks, Tag 01TV] applies. -/
private theorem locallyOfFinitePresentation_of_isFinitePresentation_pushforward_unit
    {X X' : Scheme.{u}} (i : X ⟶ X') [IsClosedImmersion i]
    (h : ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit X.ringCatSheaf)).IsFinitePresentation) :
    LocallyOfFinitePresentation i := by
  have hI : (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).IsFiniteType := by
    have hGfp : ((SheafOfModules.pushforward
        (structureSheafHom i.toLRSHom.toShHom)).obj
        (SheafOfModules.unit (structureSheafRing X.toRingedSpace))).IsFinitePresentation := h
    have hEpi := epi_unitToPushforwardObjUnit_of_isClosedImmersion i
    exact Stacks.SheafOfModules.LocalKernel.kernel_isFiniteType_of_epi_from_finiteType
      (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i.toLRSHom.toShHom))
  exact ((AlgebraicGeometry.finitePresentation_iff_isFiniteType_idealSheaf i).2 hI).1

/-- The case of affine source and target of [Stacks, Tag 081P]. -/
private theorem locallyOfFinitePresentation_of_flat_dense_open_affine
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [IsAffine S]
    [LocallyOfFiniteType f] [Flat f]
    (U : S.Opens) (hUretro : IsRetrocompact (U : Set S))
    (hUdense : Scheme.Opens.IsSchemeTheoreticallyDense U)
    [LocallyOfFinitePresentation (f ∣_ U)] :
    LocallyOfFinitePresentation f := by
  obtain ⟨X', p, i, hp, hi, rfl⟩ :=
    AlgebraicGeometry.exists_finitePresentation_closedImmersion f
  have : IsClosedImmersion i := hi
  have : LocallyOfFinitePresentation p := hp.1
  set OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  set F : X'.Modules := (Scheme.Modules.pushforward i).obj OX
  have : F.IsFiniteType := (isFiniteType_iff_pushforward_isFiniteType i OX).1 inferInstance
  have hflat : AlgebraicGeometry.IsFlatOver p.toLRSHom.toShHom F :=
    (isFlatOver_pushforward_iff i p OX).mp fun x ↦
      (isFlatOverAt_unit_iff_isFlatAt (i ≫ p) x).2 (Flat.stalkMap (i ≫ p) x)
  have hfp : ((Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj F).IsFinitePresentation := by
    set V : X'.Opens := p ⁻¹ᵁ U
    have hcompU : LocallyOfFinitePresentation ((i ∣_ V) ≫ (p ∣_ U)) := by
      have hloc : LocallyOfFinitePresentation ((i ≫ p) ∣_ U) := inferInstance
      rwa [morphismRestrict_comp] at hloc
    have hiV : LocallyOfFinitePresentation (i ∣_ V) :=
      AlgebraicGeometry.locallyOfFinitePresentation_of_comp (i ∣_ V) (p ∣_ U)
    set OXV := (Scheme.Modules.restrictFunctor (i ⁻¹ᵁ V).ι).obj OX
    have : OXV.IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation (i ⁻¹ᵁ V).toScheme.ringCatSheaf).prop_of_iso
        (Scheme.Modules.restrictUnitIso (i ⁻¹ᵁ V).ι).symm inferInstance
    have hpushFP : ((Scheme.Modules.pushforward (i ∣_ V)).obj OXV).IsFinitePresentation :=
      (AlgebraicGeometry.isFinitePresentation_iff_pushforward_isFinitePresentation
        (i ∣_ V) ⟨hiV, inferInstance, inferInstance⟩ OXV).1 inferInstance
    have hRestrFP : ((Scheme.Modules.restrictFunctor V.ι).obj F).IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation V.toScheme.ringCatSheaf).prop_of_iso
        ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso i V).app OX).symm
        hpushFP
    exact (isFinitePresentation_pullback_iff_restrict V.ι F).2 hRestrFP
  have : LocallyOfFinitePresentation i :=
    locallyOfFinitePresentation_of_isFinitePresentation_pushforward_unit i
      (isFinitePresentation_of_isFlatOver_of_retrocompact_dense_open p F hflat U hUretro hUdense
        hfp)
  infer_instance

/-- **Stacks Project, Tag 081P.** A flat morphism of schemes which is locally of finite type,
and which is locally of finite presentation over a retrocompact scheme-theoretically dense open
of the target, is locally of finite presentation. -/
@[stacks 081P]
public theorem locallyOfFinitePresentation_of_flat_of_retrocompact_dense_open
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [Flat f]
    (U : S.Opens) (hUretro : IsRetrocompact (U : Set S))
    (hUdense : Scheme.Opens.IsSchemeTheoreticallyDense U)
    [LocallyOfFinitePresentation (f ∣_ U)] :
    LocallyOfFinitePresentation f := by
  rw [locallyOfFinitePresentation_iff]
  intro W hW V hV e
  have : IsAffine V.toScheme := hV
  have : IsAffine W.toScheme := hW
  set D : W.toScheme.Opens := W.ι ⁻¹ᵁ U
  have hDretro : IsRetrocompact (D : Set W.toScheme) :=
    isRetrocompact_preimage_of_isOpenImmersion W.ι hUretro
  have hDdense : Scheme.Opens.IsSchemeTheoreticallyDense D :=
    isSchemeTheoreticallyDense_preimage_ι U W hUretro hUdense
  have hWD : LocallyOfFinitePresentation (f ∣_ W ∣_ D) :=
    locallyOfFinitePresentation_restrict_inter f U W
  have hfpD : LocallyOfFinitePresentation (f.resLE W V e ∣_ D) := by
    change LocallyOfFinitePresentation ((X.homOfLE e ≫ f ∣_ W) ∣_ D)
    rw [morphismRestrict_comp]
    exact MorphismProperty.comp_mem _ _ _
      (inferInstanceAs (LocallyOfFinitePresentation (X.homOfLE e ∣_ ((f ∣_ W) ⁻¹ᵁ D)))) hWD
  have : LocallyOfFinitePresentation (f.resLE W V e) :=
    locallyOfFinitePresentation_of_flat_dense_open_affine (f.resLE W V e) D hDretro hDdense
  exact (RingHom.finitePresentation_respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f W V e)).mp (f.resLE W V e).finitePresentation_appTop

end Morphism

end AlgebraicGeometry.FinitePresentationFromDenseOpen
