module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Artinian.Ring
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.ArtinianLocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.BaseChangeLocus
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
public import StacksFrontier.AlgebraicGeometry.SpecResidueFieldClosedPoint
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.Thickenings.Infinitesimal
public import StacksCore.Tactic.StacksAttribute

/-!
# Smoothness over a Noetherian base

For a morphism locally of finite type to a locally Noetherian scheme, smoothness can be tested
by infinitesimal lifting. Pointwise, the lifting criterion is the equivalence of smoothness at
a point with the lifting properties for square-zero surjections, small extensions, and
residually trivial small extensions. Globally, smoothness is equivalent to lifting every
commutative square along a small extension of Artinian local rings whose map from the thicker
spectrum to the base is of finite type.

## Main results

* `InfinitesimalLifting.infinitesimal_lifting_criterion_for_smoothness`: the pointwise
  equivalent conditions.
* `AlgebraicGeometry.smooth_iff_lifts_finiteType_smallExtensions`: the global lifting criterion.
* `AlgebraicGeometry.smoothAt_of_smooth_infinitesimalNeighbourhoods` and
  `AlgebraicGeometry.etaleAt_of_etale_infinitesimalNeighbourhoods`: smoothness, respectively
  étaleness, of every base change to an infinitesimal neighbourhood of a closed subscheme of the
  base implies smoothness, respectively étaleness, at every point above that subscheme.

## References

* [Stacks Project, Tag 02HX](https://stacks.math.columbia.edu/tag/02HX)
* [Stacks Project, Tag 02HY](https://stacks.math.columbia.edu/tag/02HY)
* [Stacks Project, Tag 0A43](https://stacks.math.columbia.edu/tag/0A43)
* [Stacks Project, Tag 04EY](https://stacks.math.columbia.edu/tag/04EY)
* [Stacks Project, Tag 02GK](https://stacks.math.columbia.edu/tag/02GK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

add_to_stacks 02HX InfinitesimalLifting.infinitesimal_lifting_criterion_for_smoothness

namespace AlgebraicGeometry

universe u

/-- Under the identification of the two residue fields, the canonical morphism from the
spectrum of the residue field of `Spec B` at its closed point is `Spec` of the residue map
of `B`. -/
private theorem specMap_residueFieldAtClosedPointEquiv_comp_fromSpec
    {B : CommRingCat.{u}} [IsLocalRing B] :
    Spec.map (CommRingCat.ofHom
        (residueFieldAtClosedPointEquiv (R := B)).toRingHom) ≫
      (Spec B).fromSpecResidueField (IsLocalRing.closedPoint B : Spec B) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) := by
  let cp : Spec B := IsLocalRing.closedPoint B
  let _ : IsLocalRing ((Spec B).presheaf.stalk cp) :=
    (Spec.stalkIso B cp).commRingCatIsoToRingEquiv.symm.isLocalRing
  simp only [Scheme.fromSpecResidueField]
  rw [← Spec_stalkClosedPointIso, ← Spec.map_comp, ← Spec.map_comp]
  apply Spec.map_inj.mpr
  apply CommRingCat.hom_ext
  ext a
  change IsLocalRing.ResidueField.map (stalkClosedPointIso B).hom.hom
    (IsLocalRing.residue _ ((stalkClosedPointIso B).inv.hom a)) =
      IsLocalRing.residue B a
  rw [IsLocalRing.ResidueField.map_residue]
  simp

/-- At a finite type point `x`, the canonical morphism `Spec κ(x) ⟶ X` followed by a morphism
locally of finite type is locally of finite type and quasi-compact. -/
private theorem IsFiniteTypePoint.locallyOfFiniteType_quasiCompact_fromSpecResidueField_comp
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] {x : X} (hx : IsFiniteTypePoint x) :
    LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) ∧
      QuasiCompact (X.fromSpecResidueField x ≫ f) := by
  have := hx.1
  refine ⟨inferInstance, ⟨fun _ _ _ => ?_⟩⟩
  have : Subsingleton (Spec (CommRingCat.of (X.residueField x))) := inferInstance
  exact (Set.finite_univ.subset (Set.subset_univ _)).isCompact

/-- If `α : Spec B ⟶ X` sends the closed point to `x`, then the morphism from the spectrum of the
residue field of `B` at its closed point factors through `Spec κ(x) ⟶ X` along the residue field
map of `α`. -/
private theorem specMap_residueFieldMap_comp_fromSpecResidueField_of_closedPoint
    {X : Scheme.{u}} {B : CommRingCat.{u}} [IsLocalRing B] (α : Spec B ⟶ X) {x : X}
    (hclosed : α.base (IsLocalRing.closedPoint B) = x) :
    Spec.map ((X.residueFieldCongr hclosed.symm).hom ≫
        α.residueFieldMap (IsLocalRing.closedPoint B)) ≫ X.fromSpecResidueField x =
      (Spec B).fromSpecResidueField (IsLocalRing.closedPoint B : Spec B) ≫ α := by
  rw [Spec.map_comp, Category.assoc,
    Scheme.residueFieldCongr_fromSpecResidueField hclosed.symm]
  simpa using Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField α
    (IsLocalRing.closedPoint B)

/-- In a lifting square along a surjection `φ : B' ⟶ B` of local rings whose closed point goes
to a finite type point `x` with trivial residue field extension, the composite of the residue
map of `B'` with the morphism to the base is locally of finite type and quasi-compact. -/
private theorem locallyOfFiniteType_quasiCompact_residue_comp_of_isIso_residueFieldMap
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] {x : X} (hx : IsFiniteTypePoint x)
    {B' B : CommRingCat.{u}} [IsLocalRing B'] [IsLocalRing B] (φ : B' ⟶ B)
    (hsurj : Function.Surjective φ.hom) (α : Spec B ⟶ X) (β : Spec B' ⟶ S)
    (hcomm : α ≫ f = Spec.map φ ≫ β) (hclosed : α.base (IsLocalRing.closedPoint B) = x)
    (hiso : IsIso (α.residueFieldMap (IsLocalRing.closedPoint B))) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B')) ≫ β) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B')) ≫ β) := by
  have : IsLocalHom φ.hom := IsLocalHom.of_surjective φ.hom hsurj
  have hψ : Function.Surjective (IsLocalRing.ResidueField.map φ.hom) := by
    intro y
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨b', rfl⟩ := hsurj b
    exact ⟨IsLocalRing.residue B' b', by simp [IsLocalRing.ResidueField.map_residue]⟩
  let eψ := RingEquiv.ofBijective _ ⟨RingHom.injective _, hψ⟩
  let ψ : CommRingCat.of (IsLocalRing.ResidueField B') ⟶
      CommRingCat.of (IsLocalRing.ResidueField B) := CommRingCat.ofHom eψ.toRingHom
  have hψeq : CommRingCat.ofHom (IsLocalRing.residue B') ≫ ψ =
      φ ≫ CommRingCat.ofHom (IsLocalRing.residue B) := by
    ext a
    exact IsLocalRing.ResidueField.map_residue φ.hom a
  have : IsIso ψ := eψ.toCommRingCatIso.isIso_hom
  have : IsIso (CommRingCat.ofHom (residueFieldAtClosedPointEquiv (R := B)).toRingHom) :=
    (residueFieldAtClosedPointEquiv (R := B)).toCommRingCatIso.isIso_hom
  have := hx.1
  have hfin := hx.locallyOfFiniteType_quasiCompact_fromSpecResidueField_comp f
  have := hfin.1
  have := hfin.2
  have key : LocallyOfFiniteType (Spec.map ψ ≫ Spec.map (CommRingCat.ofHom
        (IsLocalRing.residue B')) ≫ β) ∧
      QuasiCompact (Spec.map ψ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B')) ≫ β) := by
    rw [← Category.assoc, ← Spec.map_comp, hψeq, Spec.map_comp, Category.assoc, ← hcomm,
      ← specMap_residueFieldAtClosedPointEquiv_comp_fromSpec, Category.assoc,
      ← reassoc_of% (specMap_residueFieldMap_comp_fromSpecResidueField_of_closedPoint α hclosed)]
    exact ⟨inferInstance, inferInstance⟩
  have := key.1
  have := key.2
  constructor
  · simpa using (inferInstance : LocallyOfFiniteType (inv (Spec.map ψ) ≫ Spec.map ψ ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue B')) ≫ β))
  · simpa using (inferInstance : QuasiCompact (inv (Spec.map ψ) ≫ Spec.map ψ ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue B')) ≫ β))

/-- A morphism locally of finite type which lifts against every small extension whose map to the
base is of finite type lifts, at every finite type point, against residually trivial small
extensions. -/
private theorem liftsAgainstResiduallyTrivialSmallExtension_of_lifts_finiteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] {x : X} (hx : IsFiniteTypePoint x)
    (h : ∀ ⦃B' B : CommRingCat.{u}⦄ (φ : B' ⟶ B),
      InfinitesimalLifting.IsSmallExtension φ →
      ∀ (α : Spec B ⟶ X) (β : Spec B' ⟶ S),
        (LocallyOfFiniteType β ∧ QuasiCompact β) →
        α ≫ f = Spec.map φ ≫ β →
        ∃ γ : Spec B' ⟶ X, Spec.map φ ≫ γ = α ∧ γ ≫ f = β) :
    InfinitesimalLifting.LiftsAgainstResiduallyTrivialSmallExtension f x := by
  intro B' B φ hφ _ α β hcomm hclosed hiso
  have hφsmall := hφ
  rcases hφ with ⟨_, _, _, _, hsurj, _⟩
  exact h φ hφsmall α β ((finiteType_iff_residueField_comp_finiteType S B' β).mpr
    (locallyOfFiniteType_quasiCompact_residue_comp_of_isIso_residueFieldMap f hx φ hsurj α β
      hcomm hclosed hiso)) hcomm

/-- A locally finite type morphism to a locally Noetherian scheme
is smooth exactly when it lifts against all Artinian small extensions whose map to the base is
of finite type. -/
@[stacks 02HY, ega "IV 17.5.4", sga "1 III 3.1" "(i)<=>(iii), Noetherian"]
public theorem smooth_iff_lifts_finiteType_smallExtensions
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] :
    Smooth f ↔
      ∀ ⦃B' B : CommRingCat.{u}⦄ (φ : B' ⟶ B),
        InfinitesimalLifting.IsSmallExtension φ →
        ∀ (α : Spec B ⟶ X) (β : Spec B' ⟶ S),
          (LocallyOfFiniteType β ∧ QuasiCompact β) →
          α ≫ f = Spec.map φ ≫ β →
          ∃ γ : Spec B' ⟶ X, Spec.map φ ≫ γ = α ∧ γ ≫ f = β := by
  constructor
  · intro hf B' B φ hφ α β _ hcomm
    have := hφ.2.1
    let x : X := α.base (IsLocalRing.closedPoint B)
    have hx : x ∈ f.smoothLocus := by
      rw [f.smoothLocus_eq_top]
      trivial
    have hlift : InfinitesimalLifting.LiftsAgainstSmallExtension f x :=
      ((InfinitesimalLifting.infinitesimal_lifting_criterion_for_smoothness f x).out 1 3).mp
        (InfinitesimalLifting.formallySmooth_stalkMap_smoothAt f x
          (Scheme.Hom.mem_smoothLocus.mp hx))
    exact hlift φ hφ α β hcomm rfl
  · intro h
    by_contra hnot
    have hTne : ((f.smoothLocus : Set X)ᶜ).Nonempty := Set.nonempty_compl.2 fun h ↦
      hnot (Scheme.Hom.smoothLocus_eq_top_iff.mp (SetLike.coe_injective h))
    obtain ⟨x, hxT⟩ :=
      inter_finiteTypePoints_nonempty f.smoothLocus.2.isClosed_compl.isLocallyClosed hTne
    have hx : InfinitesimalLifting.SmoothAt f x :=
      ((InfinitesimalLifting.infinitesimal_lifting_criterion_for_smoothness f x).out 4 1).mp
        (liftsAgainstResiduallyTrivialSmallExtension_of_lifts_finiteType f hxT.2 h)
    exact hxT.1 (Scheme.Hom.mem_smoothLocus.mpr (hx.formallySmooth_stalkMap f x))

/-! ### Smoothness and étaleness over a closed subscheme -/

/-- The spectrum of an Artinian local ring is a one-point space. -/
private theorem subsingleton_spec_of_isArtinianRing (R : CommRingCat.{u})
    [IsLocalRing R] [IsArtinianRing R] : Subsingleton (Spec R) :=
  ⟨fun p q => PrimeSpectrum.ext (by
    rw [IsLocalRing.eq_maximalIdeal
        ((IsArtinianRing.isPrime_iff_isMaximal p.asIdeal).mp p.isPrime),
      IsLocalRing.eq_maximalIdeal
        ((IsArtinianRing.isPrime_iff_isMaximal q.asIdeal).mp q.isPrime)])⟩

/-- The maximal ideal of an Artinian local ring is nilpotent. -/
private theorem _root_.IsArtinianRing.exists_maximalIdeal_pow_succ_eq_bot (R : Type*) [CommRing R]
    [IsLocalRing R] [IsArtinianRing R] :
    ∃ n : ℕ, IsLocalRing.maximalIdeal R ^ (n + 1) = ⊥ := by
  obtain ⟨n, hn⟩ : IsNilpotent (IsLocalRing.maximalIdeal R) := by
    rw [← IsLocalRing.ringJacobson_eq_maximalIdeal]
    simpa [Ideal.jacobson_bot] using IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  refine ⟨n, ?_⟩
  rw [pow_succ, hn]
  simp

/-- On an affine open `V` of `Y`, an ideal sheaf `K` is contained in the prime of any point of
`V` in its support. -/
private theorem Scheme.IdealSheafData.ideal_le_primeIdealOf_of_mem_support {Y : Scheme.{u}}
    (K : Y.IdealSheafData) (V : Y.affineOpens) {y : Y} (hyV : y ∈ V.1) (hyK : y ∈ K.support) :
    K.ideal V ≤ (V.2.primeIdealOf ⟨y, hyV⟩).asIdeal := by
  have hz := (K.mem_support_iff_of_mem hyV).mp hyK
  rw [Scheme.mem_zeroLocus_iff] at hz
  intro a ha
  have hnot : V.2.primeIdealOf ⟨y, hyV⟩ ∉ PrimeSpectrum.basicOpen a := by
    rw [← V.2.fromSpec_preimage_basicOpen]
    change ¬ (V.2.fromSpec _ ∈ Y.basicOpen a)
    rw [V.2.fromSpec_primeIdealOf ⟨y, hyV⟩]
    exact hz a ha
  by_contra hmem
  exact hnot ((PrimeSpectrum.mem_basicOpen a _).2 hmem)

/-- Let `β : Spec R ⟶ Y` with `R` Artinian local and `𝔪ᴿ ^ (n + 1) = 0`, whose closed point lies
in the support of an ideal sheaf `K` and in an affine open `V`. Then `K(V) ^ (n + 1)` is killed
by `β` on `V`. -/
private theorem ideal_pow_le_ker_app_of_closedPoint_mem {Y : Scheme.{u}} {R : CommRingCat.{u}}
    [IsLocalRing R] [IsArtinianRing R] (β : Spec R ⟶ Y) (K : Y.IdealSheafData)
    (hyK : β (IsLocalRing.closedPoint R) ∈ K.support) {n : ℕ}
    (hn : IsLocalRing.maximalIdeal R ^ (n + 1) = ⊥) (V : Y.affineOpens)
    (hyV : β (IsLocalRing.closedPoint R) ∈ V.1) :
    K.ideal V ^ (n + 1) ≤ RingHom.ker (β.app V.1).hom := by
  have : Subsingleton (Spec R) := subsingleton_spec_of_isArtinianRing R
  have hpre : β ⁻¹ᵁ V.1 = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem β hyV
  let W := β ⁻¹ᵁ V.1
  have hW : IsAffineOpen W := by rw [show W = ⊤ from hpre]; exact isAffineOpen_top _
  have hWpoint : IsLocalRing.closedPoint R ∈ W := by rw [show W = ⊤ from hpre]; trivial
  let T := Γ(Spec R, W)
  let e : R ≅ T := (Scheme.ΓSpecIso R).symm ≪≫ (Spec R).presheaf.mapIso (eqToIso hpre).op
  have : IsLocalRing T := e.commRingCatIsoToRingEquiv.isLocalRing
  let q := hW.primeIdealOf ⟨IsLocalRing.closedPoint R, hWpoint⟩
  have hq : q = IsLocalRing.closedPoint T := hW.fromSpec.isEmbedding.injective
    ((hW.fromSpec_primeIdealOf ⟨IsLocalRing.closedPoint R, hWpoint⟩).trans (Subsingleton.elim _ _))
  have hmaxpow : IsLocalRing.maximalIdeal T ^ (n + 1) = ⊥ := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e.commRingCatIsoToRingEquiv, ← Ideal.map_pow, hn,
      Ideal.map_bot]
  have hqpow : q.asIdeal ^ (n + 1) = ⊥ := by
    simpa [hq, IsLocalRing.closedPoint] using hmaxpow
  have hcomap : q.comap (β.app V.1).hom = V.2.primeIdealOf
      ⟨β (IsLocalRing.closedPoint R), hyV⟩ := by
    change q.comap (β.appLE V.1 W le_rfl).hom = _
    exact IsAffineOpen.comap_primeIdealOf_appLE V.1 V.2 W hW le_rfl hWpoint
  have hmapK : Ideal.map (β.app V.1).hom (K.ideal V) ≤ q.asIdeal := by
    rw [Ideal.map_le_iff_le_comap, show Ideal.comap (β.app V.1).hom q.asIdeal =
        (V.2.primeIdealOf ⟨β (IsLocalRing.closedPoint R), hyV⟩).asIdeal from
      congrArg PrimeSpectrum.asIdeal hcomap]
    exact K.ideal_le_primeIdealOf_of_mem_support V hyV hyK
  have hle : Ideal.map (β.app V.1).hom (K.ideal V ^ (n + 1)) ≤ ⊥ := by
    rw [Ideal.map_pow, ← hqpow]
    gcongr
  simpa [RingHom.ker] using Ideal.map_le_iff_le_comap.mp hle

/-- A morphism to `S` from the spectrum of an Artinian local ring whose closed point lands in a
closed subscheme `i : Z ⟶ S` factors through one of the infinitesimal neighbourhoods of `Z`. -/
public theorem exists_nthOrderToBase_factorization
    {Z S : Scheme.{u}} (i : Z ⟶ S) [IsClosedImmersion i]
    (R : CommRingCat.{u}) [IsLocalRing R] [IsArtinianRing R]
    (β : Spec R ⟶ S) (z : Z) (hβ : β (IsLocalRing.closedPoint R) = i z) :
    ∃ n : ℕ, ∃ βn : Spec R ⟶ Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood i n,
      βn ≫ Stacks.Thickenings.nthOrderToBase i n = β := by
  let j := i.coborderRange.ι
  let g := i.liftCoborder
  have : Subsingleton (Spec R) := subsingleton_spec_of_isArtinianRing R
  have hgz : j (g z) = i z := congrArg (fun k : Z ⟶ S => k z) i.liftCoborder_ι
  let βo : Spec R ⟶ i.coborderRange.toScheme :=
    IsOpenImmersion.lift j β (by
      rintro y ⟨p, rfl⟩
      rw [Subsingleton.elim p (IsLocalRing.closedPoint R), hβ]
      exact ⟨g z, hgz⟩)
  have hβo : βo ≫ j = β := IsOpenImmersion.lift_fac j β _
  have hpoint : ∀ p : Spec R, βo p = βo (IsLocalRing.closedPoint R) :=
    fun p => congrArg βo (Subsingleton.elim p _)
  have hyK : βo (IsLocalRing.closedPoint R) ∈ g.ker.support := by
    have himage : g z = βo (IsLocalRing.closedPoint R) := by
      apply j.isEmbedding.injective
      rw [hgz, hβ.symm, ← hβo]
      rfl
    rw [← himage]
    exact g.range_subset_ker_support ⟨z, rfl⟩
  let K := g.ker
  obtain ⟨n, hn⟩ := IsArtinianRing.exists_maximalIdeal_pow_succ_eq_bot R
  have hKpow : K ^ (n + 1) ≤ βo.ker := by
    rw [Scheme.IdealSheafData.le_def]
    intro V
    rw [Scheme.Hom.ker_apply]
    by_cases hyV : βo (IsLocalRing.closedPoint R) ∈ V.1
    · exact ideal_pow_le_ker_app_of_closedPoint_mem βo K hyK hn V hyV
    · have hpre : βo ⁻¹ᵁ V.1 = ⊥ := by
        ext p
        exact ⟨fun hp => (hyV (by simpa [hpoint p] using hp)).elim, by simp⟩
      have : Subsingleton Γ(Spec R, βo ⁻¹ᵁ V.1) := by
        rw [hpre]
        infer_instance
      have hkerTop : RingHom.ker (βo.app V.1).hom = ⊤ := by
        ext a
        change ((βo.app V.1).hom a = 0) ↔ a ∈ (⊤ : Ideal Γ(i.coborderRange.toScheme, V.1))
        exact ⟨fun _ => Set.mem_univ _, fun _ => Subsingleton.elim _ _⟩
      exact hkerTop ▸ le_top
  refine ⟨n, IsClosedImmersion.lift (K ^ (n + 1)).subschemeι βo
    (by rwa [Scheme.IdealSheafData.ker_subschemeι]), ?_⟩
  change IsClosedImmersion.lift (K ^ (n + 1)).subschemeι βo _ ≫
    (K ^ (n + 1)).subschemeι ≫ j = β
  rw [← Category.assoc, IsClosedImmersion.lift_fac, hβo]

/-- Let `f : X ⟶ S` be a morphism locally of finite type to a locally Noetherian scheme and let
`i : Z ⟶ S` be a closed subscheme. If the base change `Xₙ = Zₙ ×_S X ⟶ Zₙ` of `f` to the `n`th
infinitesimal neighbourhood of `Z` is smooth for every `n`, then `f` is smooth at every point of
`f⁻¹(Z)`. -/
@[stacks 0A43 "smooth"]
public theorem smoothAt_of_smooth_infinitesimalNeighbourhoods
    {X S Z : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) (i : Z ⟶ S) [LocallyOfFiniteType f] [IsClosedImmersion i]
    (hsmooth : ∀ n : ℕ, Smooth (pullback.snd f (Stacks.Thickenings.nthOrderToBase i n)))
    (x : X) (hx : f x ∈ Set.range i) :
    InfinitesimalLifting.SmoothAt f x := by
  refine ((InfinitesimalLifting.infinitesimal_lifting_criterion_for_smoothness
    f x).out 1 3).mpr ?_
  intro B' B φ hφ _ α β hcomm hclosed
  have hφsmall := hφ
  obtain ⟨_, _, _, _, hsurj, _⟩ := hφ
  have : IsLocalHom φ.hom := Function.Surjective.isLocalHom φ.hom hsurj
  obtain ⟨z, hz⟩ := hx
  have hβclosed : β (IsLocalRing.closedPoint B') = i z := by
    have hpt := congrArg (fun g : Spec B ⟶ S => g.base (IsLocalRing.closedPoint B)) hcomm
    change f (α (IsLocalRing.closedPoint B)) =
      β ((Spec.map φ).base (IsLocalRing.closedPoint B)) at hpt
    rw [hclosed, AlgebraicGeometry.Spec_closedPoint (f := φ)] at hpt
    exact hpt.symm.trans hz.symm
  obtain ⟨n, βn, hβn⟩ := exists_nthOrderToBase_factorization i B' β z hβclosed
  set t := Stacks.Thickenings.nthOrderToBase i n
  have hαcompat : α ≫ f = Spec.map φ ≫ βn ≫ t := by rw [hcomm, ← hβn]
  let αn : Spec B ⟶ pullback f t := pullback.lift α (Spec.map φ ≫ βn) hαcompat
  have hloc : InfinitesimalLifting.SmoothAt (pullback.snd f t) (αn.base
      (IsLocalRing.closedPoint B)) := by
    have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth)
    have := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
    exact ⟨⊤, trivial, IsZariskiLocalAtSource.resLE le_top (hsmooth n)⟩
  obtain ⟨γn, hγn₁, hγn₂⟩ :=
    InfinitesimalLifting.formallySmooth_stalkMap_liftsAgainstSquareZero (pullback.snd f t) _
      (hloc.formallySmooth_stalkMap (pullback.snd f t) _) φ
      (InfinitesimalLifting.IsSmallExtension.isSquareZeroSurjection φ hφsmall) αn βn
      (pullback.lift_snd α (Spec.map φ ≫ βn) hαcompat) rfl
  refine ⟨γn ≫ pullback.fst f t, ?_, ?_⟩
  · rw [← Category.assoc, hγn₁]
    exact pullback.lift_fst α (Spec.map φ ≫ βn) hαcompat
  · calc
      (γn ≫ pullback.fst f t) ≫ f = γn ≫ pullback.snd f t ≫ t := by
        rw [Category.assoc, pullback.condition]
      _ = βn ≫ t := by rw [← Category.assoc, hγn₂]
      _ = β := hβn

/-- Let `f : X ⟶ S` be a morphism locally of finite type to a locally Noetherian scheme and let
`i : Z ⟶ S` be a closed subscheme. If the base change `Xₙ = Zₙ ×_S X ⟶ Zₙ` of `f` to the `n`th
infinitesimal neighbourhood of `Z` is étale for every `n`, then `f` is étale at every point of
`f⁻¹(Z)`. -/
@[stacks 0A43 "etale"]
public theorem etaleAt_of_etale_infinitesimalNeighbourhoods
    {X S Z : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) (i : Z ⟶ S) [LocallyOfFiniteType f] [IsClosedImmersion i]
    (hetale : ∀ n : ℕ, Etale (pullback.snd f (Stacks.Thickenings.nthOrderToBase i n)))
    (x : X) (hx : f x ∈ Set.range i) :
    EtaleAt f x := by
  refine (etaleAt_iff_smoothAt_and_unramifiedAt f x).mpr
    ⟨smoothAt_of_smooth_infinitesimalNeighbourhoods f i
      (fun n => have := hetale n; inferInstance) x hx, ?_⟩
  set t := Stacks.Thickenings.nthOrderToBase i 0 with ht
  have hx0 : x ∈ Set.range (pullback.fst f t) := by
    rw [Scheme.Pullback.range_fst]
    obtain ⟨z, hz⟩ := hx
    refine ⟨Stacks.Thickenings.nthOrderInclusion i 0 z, ?_⟩
    change (Stacks.Thickenings.nthOrderInclusion i 0 ≫ t) z = f x
    rw [ht, Stacks.Thickenings.nthOrderInclusion_toBase]
    exact hz
  obtain ⟨x', hx'⟩ := hx0
  have hpb := unramifiedAt_iff_of_isPullback (IsPullback.of_hasPullback f t) x'
  rw [hx'] at hpb
  exact hpb.mpr (((etaleAt_iff_smoothAt_and_unramifiedAt (pullback.snd f t) x').mp
    ((etale_iff_forall_etaleAt (pullback.snd f t)).mp (by rw [ht]; exact hetale 0) x')).2)

end AlgebraicGeometry
