module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Defs
public import StacksFrontier.RingTheory.Etale.StandardEtale
public import StacksFrontier.RingTheory.Unramified.LocalStructure
public import StacksCore.Tactic.StacksAttribute

/-!
# Local geometric structure of unramified morphisms

At a point where a morphism of schemes is unramified, the morphism is, on a small enough affine
neighbourhood of that point and over any prescribed affine open of the target, an immersion into
the spectrum of a *derivative-localized monic hypersurface*: the standard étale algebra
`A[t]_{f'}/(f)` attached to a monic `f ∈ A[t]`, where `A` is the ring of sections over the
prescribed affine open. At a point where the morphism is étale the immersion may be taken open.

## Main definitions

* `StandardEtalePair.derivativePair` normalizes a standard étale pair `(f, g)` to the pair
  `(f, f')` with the same monic polynomial.
* `StandardEtalePair.fromDerivativePair` is the canonical algebra map
  `A[t]_{f'}/(f) → A[t]_g/(f)` that the normalization induces.

## Main results

* `StandardEtalePair.isImmersion_specMap_aeval_X` exhibits a standard étale algebra as a
  locally closed subscheme of the affine line.
* `AlgebraicGeometry.exists_affineOpen_unramified_of_unramifiedAt` shrinks the affine
  neighbourhood witnessing unramifiedness at a point so that it lies over a prescribed affine
  open of the target.
* `AlgebraicGeometry.exists_affineOpen_etale_of_etaleAt` is the same for étaleness.
* `AlgebraicGeometry.exists_isImmersion_specMap_derivativePair_of_unramifiedAt` is the
  unramified case of the local structure theorem.
* `AlgebraicGeometry.exists_isOpenImmersion_specMap_derivativePair_of_etaleAt` is its étale
  case.

## Implementation notes

Mathlib's `StandardEtalePair A` records a monic `f` together with a `g` whose powers lie in the
ideal `(f', f)`; the associated algebra `P.Ring` presents `A[t]_g/(f)`. The source normalizes `g`
to `f'`, which is legitimate because `f' * 1 + f * 0 = (f')^1`, and the normalized algebra maps
*into* the original one: `f'` is already invertible in `A[t]_g/(f)`, so `A[t]_{f'}/(f)` localizes
to `A[t]_g/(f)` and the induced map on spectra is an open immersion
(`StandardEtalePair.isOpenImmersion_specMap_fromDerivativePair`). Composing the closed immersion
coming from the ring-level surjection of Lemma 0395 with that open immersion gives the immersion
of the statement; in the étale case the ring-level input of Lemma 00UE is an isomorphism, so the
first factor is an open immersion too.

The commuting triangle is stated through the two canonical arrows
`Spec P.Ring ⟶ Spec A[t] ⟶ Spec A`, which exhibit `Spec A[t]` as the affine line over the
prescribed affine open, and `Scheme.Hom.resLE` for the restriction of the morphism.

## References

* [Stacks Project, Tag 0CBJ](https://stacks.math.columbia.edu/tag/0CBJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Polynomial

universe u

namespace StandardEtalePair

variable {R : Type u} [CommRing R]

/-- The standard étale pair `(f, f')` attached to a standard étale pair `(f, g)`: the same monic
polynomial, localized at its own derivative instead of at `g`. -/
public noncomputable def derivativePair (P : StandardEtalePair R) : StandardEtalePair R :=
  ⟨P.f, P.monic_f, P.f.derivative, ⟨1, 0, 1, by simp⟩⟩

/-- The monic polynomial of `P.derivativePair` is that of `P`. -/
@[simp]
public lemma derivativePair_f (P : StandardEtalePair R) : P.derivativePair.f = P.f := rfl

/-- The localizing polynomial of `P.derivativePair` is the derivative of `P.f`. -/
@[simp]
public lemma derivativePair_g (P : StandardEtalePair R) :
    P.derivativePair.g = P.f.derivative := rfl

/-- The canonical `R`-algebra map `A[t]_{f'}/(f) → A[t]_g/(f)`, available because the derivative
of `f` is invertible in any standard étale algebra built from `f`. -/
public noncomputable def fromDerivativePair (P : StandardEtalePair R) :
    P.derivativePair.Ring →ₐ[R] P.Ring :=
  P.derivativePair.lift P.X ⟨P.hasMap_X.1, P.hasMap_X.isUnit_derivative_f⟩

/-- The identification `A[t]_g/(f) ≃ (A[t]/(f))[1/g]` sends `t` to the class of the root. -/
private lemma equivAwayAdjoinRoot_X (P : StandardEtalePair R) :
    P.equivAwayAdjoinRoot P.X =
      algebraMap (AdjoinRoot P.f) (Localization.Away (AdjoinRoot.mk P.f P.g))
        (AdjoinRoot.root P.f) := by
  have h : P.HasMap (algebraMap (AdjoinRoot P.f) (Localization.Away (AdjoinRoot.mk P.f P.g))
      (AdjoinRoot.root P.f)) := by
    constructor
    · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
    · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq]
      exact IsLocalization.Away.algebraMap_isUnit _
  change P.lift _ h P.X = _
  rw [P.lift_X]

/-- Localizing `A[t]_{f'}/(f)` further at `g` gives `A[t]_g/(f)`, so the normalization map of
`StandardEtalePair.fromDerivativePair` is an open immersion on spectra. -/
public lemma isOpenImmersion_specMap_fromDerivativePair (P : StandardEtalePair R) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom P.fromDerivativePair.toRingHom) :
      Spec (CommRingCat.of P.Ring) ⟶ Spec (CommRingCat.of P.derivativePair.Ring)) := by
  classical
  let P' := P.derivativePair
  let A := AdjoinRoot P.f
  let d : A := AdjoinRoot.mk P.f P.f.derivative
  let g : A := AdjoinRoot.mk P.f P.g
  let D := Localization.Away d
  let T := Localization.Away (algebraMap A D g)
  let G := Localization.Away g
  have hx := P.equivAwayAdjoinRoot_X
  have hd : IsUnit (algebraMap A G d) := by
    have hm := P.hasMap_X.isUnit_derivative_f.map P.equivAwayAdjoinRoot.toRingHom
    have heq : P.equivAwayAdjoinRoot (aeval P.X P.f.derivative) =
        algebraMap A G (AdjoinRoot.mk P.f P.f.derivative) := by
      calc
        P.equivAwayAdjoinRoot (aeval P.X P.f.derivative) =
            aeval (P.equivAwayAdjoinRoot P.X) P.f.derivative :=
              (aeval_algHom_apply P.equivAwayAdjoinRoot P.X P.f.derivative).symm
        _ = aeval (algebraMap A G (AdjoinRoot.root P.f)) P.f.derivative := by rw [hx]
        _ = algebraMap A G (AdjoinRoot.mk P.f P.f.derivative) := by
              rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq]
    simpa [A, G, d, heq] using hm
  have : IsLocalization.Away (d * g) T := IsLocalization.Away.mul' (R := A) D T d g
  have : IsLocalization.Away (d * g) G := IsLocalization.Away.mul_of_isUnit' d g hd
  let eD : P'.Ring ≃ₐ[R] D := P'.equivAwayAdjoinRoot
  let eP : P.Ring ≃ₐ[R] G := P.equivAwayAdjoinRoot
  let eTG : T ≃ₐ[A] G := IsLocalization.algEquiv (.powers (d * g)) T G
  let loc : D →ₐ[A] T := IsScalarTower.toAlgHom A D T
  let k : P'.Ring →ₐ[R] P.Ring :=
    eP.symm.toAlgHom.comp ((eTG.restrictScalars R).toAlgHom.comp
      ((loc.restrictScalars R).comp eD.toAlgHom))
  let iP : Spec (CommRingCat.of P.Ring) ≅ Spec (CommRingCat.of G) :=
    (Scheme.Spec.mapIso eP.toRingEquiv.toCommRingCatIso.op).symm
  let iD : Spec (CommRingCat.of P'.Ring) ≅ Spec (CommRingCat.of D) :=
    (Scheme.Spec.mapIso eD.toRingEquiv.toCommRingCatIso.op).symm
  let iTG : Spec (CommRingCat.of T) ≅ Spec (CommRingCat.of G) :=
    (Scheme.Spec.mapIso eTG.toRingEquiv.toCommRingCatIso.op).symm
  let o : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of D) :=
    Spec.map (CommRingCat.ofHom (algebraMap D T))
  let j : Spec (CommRingCat.of P.Ring) ⟶ Spec (CommRingCat.of P'.Ring) :=
    iP.hom ≫ iTG.inv ≫ o ≫ iD.inv
  have : IsOpenImmersion o := IsOpenImmersion.of_isLocalization (algebraMap A D g)
  have hj : j = Spec.map (CommRingCat.ofHom k.toRingHom) := by
    dsimp [j, iP, iD, iTG, o, k, loc]
    rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun _ => rfl))
  have hk : k = P.fromDerivativePair := by
    apply StandardEtalePair.hom_ext
    have heD_X : eD P'.X = algebraMap A D (AdjoinRoot.root P.f) := P'.equivAwayAdjoinRoot_X
    have hrootP : P'.HasMap P.X := ⟨P.hasMap_X.1, P.hasMap_X.isUnit_derivative_f⟩
    dsimp [k, loc]
    rw [heD_X]
    change eP.symm (eTG (algebraMap D T (algebraMap A D (AdjoinRoot.root P.f)))) =
      P'.lift P.X hrootP P'.X
    rw [P'.lift_X]
    have hTG : eTG (algebraMap D T (algebraMap A D (AdjoinRoot.root P.f))) =
        algebraMap A G (AdjoinRoot.root P.f) := by
      rw [← IsScalarTower.algebraMap_apply A D T (AdjoinRoot.root P.f)]
      simp
    rw [hTG, ← hx]
    exact eP.symm_apply_apply P.X
  rw [← hk, ← hj]
  infer_instance

/-- A standard étale algebra is cut out of the affine line as a locally closed subscheme: the
map of spectra induced by `aeval P.X : R[X] →ₐ[R] P.Ring` is an immersion. It factors as the
open immersion localizing `R[X]` away from `P.g` followed by the closed immersion cutting out
`P.f`. -/
public lemma isImmersion_specMap_aeval_X (P : StandardEtalePair R) :
    IsImmersion (Spec.map (CommRingCat.ofHom (aeval (R := R) P.X).toRingHom)) := by
  let L := Localization.Away P.g
  let I : Ideal L := Ideal.span {algebraMap R[X] L P.f}
  let e := P.equivAwayQuotient
  have he : e.toRingHom.comp (aeval (R := R) P.X).toRingHom =
      (Ideal.Quotient.mk I).comp (algebraMap R[X] L) := by
    refine RingHom.ext fun p => ?_
    change e ((aeval P.X) p) = algebraMap R[X] (L ⧸ I) p
    rw [← Polynomial.aeval_algHom_apply]
    have hx : e P.X = algebraMap R[X] (L ⧸ I) Polynomial.X := by
      have h : P.HasMap (algebraMap R[X] (L ⧸ I) Polynomial.X) := by
        constructor
        · rw [aeval_algebraMap_apply, IsScalarTower.algebraMap_apply _ L (L ⧸ I),
            Ideal.Quotient.algebraMap_eq, aeval_X_left_apply]
          exact Ideal.Quotient.mk_singleton_self _
        · rw [aeval_algebraMap_apply, IsScalarTower.algebraMap_apply _ L (L ⧸ I),
            aeval_X_left_apply]
          exact (IsLocalization.Away.algebraMap_isUnit P.g).map _
      change (P.lift _ h) P.X = _
      exact P.lift_X _ h
    rw [hx, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  have hinv : (aeval (R := R) P.X).toRingHom =
      e.symm.toRingHom.comp ((Ideal.Quotient.mk I).comp (algebraMap R[X] L)) := by
    rw [← he]
    exact RingHom.ext fun p => (e.symm_apply_apply _).symm
  rw [hinv, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_comp, Spec.map_comp]
  have : IsIso (CommRingCat.ofHom e.symm.toRingHom) :=
    e.symm.toRingEquiv.toCommRingCatIso.isIso_hom
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R[X] L))) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of R[X]) P.g
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_quotient_mk (R := .of L) I
  have : IsIso (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) := inferInstance
  exact IsImmersion.comp _ _

end StandardEtalePair

namespace AlgebraicGeometry

/-- A ring-level property of `f.appLE V₀ U₀` for affine opens passes to `f.appLE V U` for affine
opens `U ≤ U₀`, provided the morphism property is stable and contains open immersions. -/
private theorem appLE_of_appLE_of_le {Q : MorphismProperty Scheme.{u}}
    {QR : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    [HasRingHomProperty Q QR] [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
    (hop : ∀ {A B : Scheme.{u}} (i : A ⟶ B) [IsOpenImmersion i], Q i)
    {X S : Scheme.{u}} (f : X ⟶ S) {U₀ U : X.Opens} {V₀ V : S.Opens}
    (hU₀ : IsAffineOpen U₀) (hU : IsAffineOpen U) (hV₀ : IsAffineOpen V₀) (hV : IsAffineOpen V)
    (e₀ : U₀ ≤ f ⁻¹ᵁ V₀) (e : U ≤ f ⁻¹ᵁ V) (hUU₀ : U ≤ U₀)
    (h : QR (f.appLE V₀ U₀ e₀).hom) : QR (f.appLE V U e).hom := by
  have : IsAffine U₀.toScheme := hU₀
  have : IsAffine V₀.toScheme := hV₀
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have hres := (HasRingHomProperty.isLocal_ringHomProperty Q).respectsIso
  have h₀ : Q (f.resLE V₀ U₀ e₀) :=
    (HasRingHomProperty.iff_of_isAffine (P := Q)).2
      ((hres.arrow_mk_iso_iff (arrowResLEAppIso f V₀ U₀ e₀)).2 h)
  have h₁ : Q (U₀.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f e₀]
    exact MorphismProperty.comp_mem Q _ _ h₀ (hop _)
  have h₂ : Q (U.ι ≫ f) := by
    rw [← Scheme.homOfLE_ι X hUU₀, Category.assoc]
    exact MorphismProperty.comp_mem Q _ _ (hop _) h₁
  have h₃ : Q (f.resLE V U e) :=
    MorphismProperty.HasOfPostcompProperty.of_postcomp (W' := @IsOpenImmersion) _ V.ι
      inferInstance (by rwa [Scheme.Hom.resLE_comp_ι])
  exact (hres.arrow_mk_iso_iff (arrowResLEAppIso f V U e)).1
    ((HasRingHomProperty.iff_of_isAffine (P := Q)).1 h₃)

/-- Unramifiedness at a point may be witnessed over any prescribed affine open of the target:
there is an affine open neighbourhood of the point contained in the preimage of that open on
which the induced map of section rings is unramified. -/
public lemma exists_affineOpen_unramified_of_unramifiedAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (V : S.Opens)
    (hV : IsAffineOpen V) (hxV : f x ∈ V) (hf : UnramifiedAt f x) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (e : U ≤ f ⁻¹ᵁ V),
      letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
      Algebra.Unramified Γ(S, V) Γ(X, U) := by
  obtain ⟨U₀, hU₀, hxU₀, V₀, hV₀, e₀, hunram⟩ := hf
  obtain ⟨U, hU, hxU, hUW⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ U₀ ⊓ f ⁻¹ᵁ V from ⟨hxU₀, hxV⟩)
  have e : U ≤ f ⁻¹ᵁ V := hUW.trans inf_le_right
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  exact ⟨U, hU, hxU, e,
    appLE_of_appLE_of_le (Q := @FormallyUnramified) (fun _ _ => inferInstance) f hU₀ hU hV₀ hV
      e₀ e (hUW.trans inf_le_left) hunram.formallyUnramified,
    RingHom.finiteType_algebraMap.mp
      (appLE_of_appLE_of_le (Q := @LocallyOfFiniteType) (fun _ _ => inferInstance) f hU₀ hU
        hV₀ hV e₀ e (hUW.trans inf_le_left) hunram.finiteType)⟩

/-- Étaleness at a point may be witnessed over any prescribed affine open of the target:
there is an affine open neighbourhood of the point contained in the preimage of that open on
which the induced map of section rings is étale. -/
public lemma exists_affineOpen_etale_of_etaleAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (V : S.Opens)
    (hV : IsAffineOpen V) (hxV : f x ∈ V) (hf : EtaleAt f x) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (e : U ≤ f ⁻¹ᵁ V),
      letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
      Algebra.Etale Γ(S, V) Γ(X, U) := by
  obtain ⟨U₀, hU₀, hxU₀, V₀, hV₀, e₀, hetale⟩ := hf
  obtain ⟨U, hU, hxU, hUW⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ U₀ ⊓ f ⁻¹ᵁ V from ⟨hxU₀, hxV⟩)
  exact ⟨U, hU, hxU, hUW.trans inf_le_right,
    appLE_of_appLE_of_le (Q := @Etale) (fun _ _ => inferInstance) f hU₀ hU hV₀ hV e₀ _
      (hUW.trans inf_le_left) hetale⟩

/-- Localizing the sections over an affine open `U` away from `g`, not vanishing at `x`, gives
the sections over a smaller affine neighbourhood `W` of `x`, compatibly with the maps from the
sections over `V`. -/
private theorem exists_affineOpen_equiv_localizationAway
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (V : S.Opens) {U : X.Opens} (hU : IsAffineOpen U)
    (hxU : x ∈ U) (hUV : U ≤ f ⁻¹ᵁ V) [Algebra Γ(S, V) Γ(X, U)]
    (hR : algebraMap Γ(S, V) Γ(X, U) = (f.appLE V U hUV).hom) {g : Γ(X, U)}
    (hg : g ∉ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) :
    ∃ (W : X.Opens) (_ : IsAffineOpen W) (_ : x ∈ W) (hWV : W ≤ f ⁻¹ᵁ V)
      (ε : Localization.Away g ≃+* Γ(X, W)),
      ∀ r, ε (algebraMap Γ(S, V) (Localization.Away g) r) = (f.appLE V W hWV).hom r := by
  let p : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨x, hxU⟩
  let W : X.affineOpens := X.affineBasicOpen (U := (⟨U, hU⟩ : X.affineOpens)) g
  have hxW : x ∈ W.1 := by
    have hxm : hU.fromSpec p ∈ X.basicOpen g := by
      rw [← hU.fromSpec_image_basicOpen g]
      exact Set.mem_image_of_mem _ ((PrimeSpectrum.mem_basicOpen g p).2 hg)
    change x ∈ X.basicOpen g
    simpa [p, IsAffineOpen.fromSpec_primeIdealOf] using hxm
  have hWU : W.1 ≤ U := Scheme.basicOpen_le X g
  let : Algebra Γ(X, U) Γ(X, W.1) := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
  have : IsLocalization.Away g Γ(X, W.1) := hU.isLocalization_basicOpen g
  let eLoc : Γ(X, W.1) ≃ₐ[Γ(X, U)] Localization.Away g :=
    IsLocalization.algEquiv (Submonoid.powers g) Γ(X, W.1) (Localization.Away g)
  refine ⟨W.1, W.2, hxW, hWU.trans hUV, eLoc.symm.toRingEquiv, fun r => ?_⟩
  rw [IsScalarTower.algebraMap_apply Γ(S, V) Γ(X, U) (Localization.Away g)]
  refine (eLoc.symm.commutes (algebraMap Γ(S, V) Γ(X, U) r)).trans ?_
  rw [hR]
  exact congrArg (fun φ => φ.hom r) (by rw [Scheme.Hom.appLE_map] :
    f.appLE V U hUV ≫ X.presheaf.map (homOfLE hWU).op = f.appLE V W.1 (hWU.trans hUV))

/-- The commuting triangle of the local structure theorem, for a map `ψ` out of the ring of a
standard étale pair `P` that is compatible with the sections of `f` over `V` and `W`. -/
private theorem spec_comp_derivativePair_comp_eq_resLE
    {X S : Scheme.{u}} (f : X ⟶ S) {V : S.Opens} (hV : IsAffineOpen V) {W : X.Opens}
    (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V) (P : StandardEtalePair Γ(S, V))
    (ψ : P.Ring →+* Γ(X, W))
    (hψ : ∀ r, ψ (algebraMap Γ(S, V) P.Ring r) = (f.appLE V W hWV).hom r) :
    ((hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ)) ≫
        Spec.map (CommRingCat.ofHom P.fromDerivativePair.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (aeval P.derivativePair.X).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : Γ(S, V) →+* Γ(S, V)[X])) =
      f.resLE V W hWV ≫ hV.isoSpec.hom := by
  have hρ : ψ.comp (P.fromDerivativePair.toRingHom.comp
      ((aeval P.derivativePair.X).toRingHom.comp Polynomial.C)) = (f.appLE V W hWV).hom :=
    RingHom.ext fun r => by
      simpa [StandardEtalePair.fromDerivativePair] using hψ r
  calc
    _ = W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (ψ.comp (P.fromDerivativePair.toRingHom.comp
        ((aeval P.derivativePair.X).toRingHom.comp Polynomial.C)))) := by
      simp only [Category.assoc, ← Spec.map_comp]
      rfl
    _ = f.resLE V W hWV ≫ hV.isoSpec.hom := by
      rw [hρ]
      simp [IsAffineOpen.isoSpec_hom]

/-- **Stacks Project, Tag 0CBJ, unramified case.** A morphism of schemes unramified at `x`
factors, on an affine open neighbourhood of `x` lying over a prescribed affine open `V` of the
target, as an immersion into the spectrum of the derivative-localized monic hypersurface
`Γ(S, V)[t]_{g'}/(g)`, followed by the canonical map to the affine line over `V`. -/
@[stacks 0CBJ "unramified case; the étale case is
`AlgebraicGeometry.exists_isOpenImmersion_specMap_derivativePair_of_etaleAt`"]
public lemma exists_isImmersion_specMap_derivativePair_of_unramifiedAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (V : S.Opens)
    (hV : IsAffineOpen V) (hxV : f x ∈ V) (hf : UnramifiedAt f x) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U)
      (hUV : U ≤ f ⁻¹ᵁ V) (P : StandardEtalePair Γ(S, V)),
      P.g = P.f.derivative ∧
        ∃ (j : U.toScheme ⟶ Spec (CommRingCat.of P.Ring)),
          IsImmersion j ∧
            j ≫ Spec.map (CommRingCat.ofHom (aeval P.X).toRingHom) ≫
                Spec.map (CommRingCat.ofHom (Polynomial.C : Γ(S, V) →+* Γ(S, V)[X])) =
              f.resLE V U hUV ≫ hV.isoSpec.hom := by
  obtain ⟨U, hU, hxU, hUV, hunram⟩ :=
    exists_affineOpen_unramified_of_unramifiedAt f x V hV hxV hf
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let p : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨x, hxU⟩
  have : p.asIdeal.IsPrime := p.isPrime
  have hlocal : ∃ s ∉ p.asIdeal, Algebra.Unramified Γ(S, V) (Localization.Away s) := by
    refine ⟨1, (Ideal.ne_top_iff_one _).mp p.isPrime.ne_top, ?_⟩
    have : Algebra.Unramified Γ(S, V) Γ(X, U) := hunram
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨g, hgQ, P, φ, hφ⟩ :=
    Algebra.exists_hasStandardEtaleSurjectionOn_of_exists_unramified p.asIdeal hlocal
  obtain ⟨W, hW, hxW, hWV, ε, hε⟩ :=
    exists_affineOpen_equiv_localizationAway f x V hU hxU hUV rfl hgQ
  let φW : P.Ring →+* Γ(X, W) := ε.toRingHom.comp φ.toRingHom
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φW)) :=
    IsClosedImmersion.spec_of_surjective _ (ε.surjective.comp hφ)
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom P.fromDerivativePair.toRingHom)) :=
    P.isOpenImmersion_specMap_fromDerivativePair
  exact ⟨W, hW, hxW, hWV, P.derivativePair, rfl, _, inferInstance,
    spec_comp_derivativePair_comp_eq_resLE f hV hW hWV P φW fun r =>
      (congrArg ε (φ.commutes r)).trans (hε r)⟩

/-- **Stacks Project, Tag 0CBJ, étale case.** At a point where the morphism is étale, the
immersion of `AlgebraicGeometry.exists_isImmersion_specMap_derivativePair_of_unramifiedAt` may
be chosen to be an open immersion. -/
@[stacks 0CBJ "étale case; the unramified case", stacks 025C "the étale local structure theorem"]
public lemma exists_isOpenImmersion_specMap_derivativePair_of_etaleAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (V : S.Opens)
    (hV : IsAffineOpen V) (hxV : f x ∈ V) (hf : EtaleAt f x) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U)
      (hUV : U ≤ f ⁻¹ᵁ V) (P : StandardEtalePair Γ(S, V)),
      P.g = P.f.derivative ∧
        ∃ (j : U.toScheme ⟶ Spec (CommRingCat.of P.Ring)),
          IsOpenImmersion j ∧
            j ≫ Spec.map (CommRingCat.ofHom (aeval P.X).toRingHom) ≫
                Spec.map (CommRingCat.ofHom (Polynomial.C : Γ(S, V) →+* Γ(S, V)[X])) =
              f.resLE V U hUV ≫ hV.isoSpec.hom := by
  obtain ⟨U, hU, hxU, hUV, hetale⟩ := exists_affineOpen_etale_of_etaleAt f x V hV hxV hf
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let p : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨x, hxU⟩
  have : p.asIdeal.IsPrime := p.isPrime
  have hlocal : ∃ s ∉ p.asIdeal, Algebra.Etale Γ(S, V) (Localization.Away s) := by
    refine ⟨1, (Ideal.ne_top_iff_one _).mp p.isPrime.ne_top, ?_⟩
    have : Algebra.Etale Γ(S, V) Γ(X, U) := hetale
    infer_instance
  obtain ⟨g, hgQ, hstandard⟩ := Algebra.exists_isStandardEtale_of_exists_etale p.asIdeal hlocal
  let presentation : StandardEtalePresentation Γ(S, V) (Localization.Away g) :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  let P := presentation.P
  obtain ⟨W, hW, hxW, hWV, ε, hε⟩ :=
    exists_affineOpen_equiv_localizationAway f x V hU hxU hUV rfl hgQ
  let e : P.Ring ≃+* Γ(X, W) := presentation.equivRing.symm.toRingEquiv.trans ε
  have : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) :=
    (Scheme.Spec.mapIso e.toCommRingCatIso.op).isIso_hom
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom P.fromDerivativePair.toRingHom)) :=
    P.isOpenImmersion_specMap_fromDerivativePair
  exact ⟨W, hW, hxW, hWV, P.derivativePair, rfl, _, inferInstance,
    spec_comp_derivativePair_comp_eq_resLE f hV hW hWV P e.toRingHom fun r =>
      (congrArg ε (presentation.equivRing.symm.commutes r)).trans (hε r)⟩

end AlgebraicGeometry

end
