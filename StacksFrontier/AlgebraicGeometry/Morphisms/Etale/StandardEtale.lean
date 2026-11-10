module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.RingTheory.Etale.StandardEtale
public import StacksFrontier.Topology.Dimension.CounterexampleCodimension

/-!
# Standard étale morphisms of affine schemes

A morphism between affine schemes is standard étale when its contravariant map on global sections
is a standard étale ring map. An étale morphism is, near each point of its source and over any
prescribed affine neighbourhood of the image, standard étale.

## Main definitions

* `AlgebraicGeometry.IsStandardEtale` is the predicate that an affine-scheme morphism is standard
  étale.

## Main results

* `AlgebraicGeometry.isStandardEtale_iff_exists_specMap_isomorphisms` identifies the definition
  with an explicit commuting presentation by a `Spec.map` of the canonical standard étale ring
  map.
* `AlgebraicGeometry.etaleAt_iff_exists_isStandardEtale_restrict` characterizes étaleness at a
  point by a standard étale restriction over a prescribed affine neighbourhood of its image.

## Implementation notes

Affine schemes are canonically isomorphic to the spectra of their rings of global sections. Thus
the predicate uses Mathlib's `Algebra.IsStandardEtale` for the algebra structure induced by the
map on global sections. The characterization theorem identifies the target with the spectrum of
its global sections and the source with the spectrum of a `StandardEtalePair` algebra.

Open subschemes are represented by `AlgebraicGeometry.Scheme.Opens.toScheme`, and the induced
morphism between two open subschemes is `AlgebraicGeometry.Scheme.Hom.resLE`. The witnesses that
the opens are affine supply the instances required by the standard étale predicate. Transporting
the predicate from the sections over an open to the global sections of the corresponding open
subscheme is isolated in `AlgebraicGeometry.isStandardEtale_sections_congr`, which keeps the
transport along the two `eqToHom`s separate from the shrinking argument.

## References

* [Stacks Project, Tag 02GI](https://stacks.math.columbia.edu/tag/02GI)
* [Stacks Project, Tag 02GT](https://stacks.math.columbia.edu/tag/02GT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Polynomial

universe u

namespace AlgebraicGeometry

/-- A morphism of affine schemes is *standard étale* if its map on global sections is a
standard étale ring map. -/
@[stacks 02GI "standard_etale_morphism"]
public abbrev IsStandardEtale {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) : Prop :=
  letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  Algebra.IsStandardEtale Γ(S, ⊤) Γ(X, ⊤)

/-- A morphism of affine schemes is standard étale exactly when, through the canonical affine
scheme isomorphisms, it is isomorphic to the spectrum of a standard étale pair's algebra map.

Here `e` induces the displayed source isomorphism, while `S.isoSpec` is the target isomorphism;
the equality is the commuting square from the definition. -/
public theorem isStandardEtale_iff_exists_specMap_isomorphisms
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) :
    IsStandardEtale f ↔
      letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
      ∃ (P : StandardEtalePair Γ(S, ⊤)) (e : Γ(X, ⊤) ≃ₐ[Γ(S, ⊤)] P.Ring),
        f ≫ S.isoSpec.hom =
          (X.isoSpec ≪≫ (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).symm).hom ≫
            Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) P.Ring)) := by
  constructor
  · intro h
    let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    let p := h.nonempty_standardEtalePresentation.some
    refine ⟨p.P, p.equivRing, ?_⟩
    rw [← Scheme.isoSpec_hom_naturality]
    simp only [Iso.trans_hom, Category.assoc]
    rw [cancel_epi X.isoSpec.hom]
    change Spec.map f.appTop = Spec.map p.equivRing.toRingEquiv.toCommRingCatIso.inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) p.P.Ring))
    rw [← Spec.map_comp]
    congr 1
    rw [← cancel_mono p.equivRing.toRingEquiv.toCommRingCatIso.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact congrArg CommRingCat.ofHom (RingHom.ext p.equivRing.commutes)
  · rintro ⟨_, e, _⟩
    let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    exact Algebra.IsStandardEtale.of_equiv e.symm

/-- Standard étaleness of the map on sections is unchanged by replacing the two opens with equal
ones and transporting along the corresponding presheaf restriction isomorphisms. -/
public lemma isStandardEtale_sections_congr {X Y : Scheme.{u}}
    {U U' : Y.Opens} {V V' : X.Opens}
    (hU : U' = U) (hV : V' = V) (φ : Γ(Y, U) ⟶ Γ(X, V)) :
    (letI := φ.hom.toAlgebra; Algebra.IsStandardEtale Γ(Y, U) Γ(X, V)) ↔
      (letI := (Y.presheaf.map (eqToHom hU.symm).op ≫ φ ≫
          X.presheaf.map (eqToHom hV).op).hom.toAlgebra
       Algebra.IsStandardEtale Γ(Y, U') Γ(X, V')) := by
  cases hU
  cases hV
  rw [show (Y.presheaf.map (eqToHom (Eq.refl U)).op ≫ φ ≫
    X.presheaf.map (eqToHom (Eq.refl V)).op).hom = φ.hom by simp]

private alias etale_resLE_of_etale_appLE := etale_resLE_of_appLE_etale

private lemma exists_etale_affine_restrict_of_etaleAt {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) (V : S.Opens) (hV : IsAffineOpen V)
    (hxV : f x ∈ V) (h : EtaleAt f x) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U)
      (e : U ≤ f ⁻¹ᵁ V), (f.appLE V U e).hom.Etale := by
  obtain ⟨U₀, hU₀, hxU₀, V₀, hV₀, e₀, h₀⟩ := h
  have hres : Etale (f.resLE V₀ U₀ e₀) :=
    etale_resLE_of_etale_appLE f U₀ hU₀ V₀ hV₀ e₀ h₀
  have hopen : Etale (U₀.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f e₀]
    infer_instance
  obtain ⟨U, hU, hxU, hUW⟩ :=
    exists_isAffineOpen_mem_and_subset
      (show x ∈ U₀ ⊓ f ⁻¹ᵁ V from ⟨hxU₀, hxV⟩)
  have hUU₀ : U ≤ U₀ := hUW.trans inf_le_left
  have e : U ≤ f ⁻¹ᵁ V := hUW.trans inf_le_right
  have hsource : Etale (U.ι ≫ f) := by
    rw [← Scheme.homOfLE_ι X hUU₀, Category.assoc]
    infer_instance
  have hcomp : Etale (f.resLE V U e ≫ V.ι) := by rwa [Scheme.Hom.resLE_comp_ι]
  have hrestricted : Etale (f.resLE V U e) :=
    Etale.of_comp (f.resLE V U e) V.ι
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  exact ⟨U, hU, hxU, e, (RingHom.Etale.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f V U e)).1
    ((HasRingHomProperty.iff_of_isAffine (P := @Etale)).1 hrestricted)⟩

/-- A scheme morphism is étale at a point if and only if, over any fixed
affine open neighbourhood of its image, it is standard étale on some affine
open neighbourhood of the point. -/
@[stacks 02GT]
public lemma etaleAt_iff_exists_isStandardEtale_restrict
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (V : S.Opens)
    (hV : IsAffineOpen V) (hxV : f x ∈ V) :
    EtaleAt f x ↔
      ∃ (U : X.Opens) (hU : IsAffineOpen U) (_ : x ∈ U)
        (hUV : U ≤ f ⁻¹ᵁ V),
        @AlgebraicGeometry.IsStandardEtale
          U.toScheme V.toScheme hU hV (f.resLE V U hUV) := by
  constructor
  · intro h
    obtain ⟨U, hU, hxU, e, hEt⟩ :=
      exists_etale_affine_restrict_of_etaleAt f x V hV hxV h
    let R := Γ(S, V)
    let A := Γ(X, U)
    let : Algebra R A := (f.appLE V U e).hom.toAlgebra
    let Q : Ideal A := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
    have : Algebra.Etale R A := hEt.toAlgebra
    have : Algebra.IsEtaleAt R Q := inferInstance
    obtain ⟨g, hg, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale
      (R := R) (S := A) Q
    let W : X.Opens := X.basicOpen g
    have hW : IsAffineOpen W := hU.basicOpen g
    have hxW : x ∈ W := by
      have hpre : hU.primeIdealOf ⟨x, hxU⟩ ∈
          hU.fromSpec ⁻¹ᵁ X.basicOpen g := by
        rwa [hU.fromSpec_preimage_basicOpen]
      have hx : hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) ∈ X.basicOpen g := hpre
      simpa [W, hU.fromSpec_primeIdealOf] using hx
    have hWU : W ≤ U := Scheme.basicOpen_le X g
    have eW : W ≤ f ⁻¹ᵁ V := hWU.trans e
    let : Algebra A Γ(X, W) :=
      (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
    have : IsLocalization.Away g Γ(X, W) := hU.isLocalization_basicOpen g
    let : Algebra R Γ(X, W) := (f.appLE V W eW).hom.toAlgebra
    have : IsScalarTower R A Γ(X, W) :=
      IsScalarTower.of_algebraMap_eq (by
        intro r
        have hm := Scheme.Hom.appLE_map (f := f) (U := V) (V := U)
          e (homOfLE hWU).op
        exact (congrArg (fun φ : Γ(S, V) ⟶ Γ(X, W) => φ.hom r) hm).symm)
    have : Algebra.IsStandardEtale R (Localization.Away g) := hstd
    have : Algebra.IsStandardEtale R Γ(X, W) :=
      Algebra.IsStandardEtale.of_equiv
        ((IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g)
          Γ(X, W)).restrictScalars R)
    refine ⟨W, hW, hxW, eW, ?_⟩
    have hproject := (isStandardEtale_sections_congr V.ι_image_top W.ι_image_top
      (f.appLE V W eW)).mp (show Algebra.IsStandardEtale R Γ(X, W) from inferInstance)
    change
      (let := (V.topIso.hom ≫ f.appLE V W eW ≫ W.topIso.inv).hom.toAlgebra
       Algebra.IsStandardEtale Γ(V.toScheme, ⊤) Γ(W.toScheme, ⊤)) at hproject
    rwa [← Scheme.Hom.resLE_app_top] at hproject
  · rintro ⟨U, hU, hxU, e, hstd⟩
    have : IsAffine U.toScheme := hU
    have : IsAffine V.toScheme := hV
    let : Algebra Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤) :=
      ((f.resLE V U e).appTop).hom.toAlgebra
    have hring : ((f.resLE V U e).appTop).hom.Etale :=
      RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale _ _)
    exact ⟨U, hU, hxU, V, hV, e,
      (RingHom.Etale.respectsIso.arrow_mk_iso_iff
        (arrowResLEAppIso f V U e)).1 hring⟩

end AlgebraicGeometry
