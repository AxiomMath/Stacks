module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureUniversal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIn

/-!
# The universal property of the relative normalization

Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` and let `ν : X' ⟶ X` be the
normalization of `X` in `Y`, with its factorization `f = ν ∘ f'`.  Stacks 0823 says that this
factorization is characterized by two properties: `ν` is integral, and every factorization
`f = π ∘ g` through an integral morphism `π : Z ⟶ X` of algebraic spaces receives a *unique*
morphism `h : X' ⟶ Z` with `f' ∘ h = g` and `π ∘ h = ν`; and moreover that this `h` is the
normalization of `Z` in `Y`.

The conjunction of the two properties is `AlgebraicGeometry.Space.IsRelativeNormalization` of
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeNormalization`.  This file proves all
three assertions of the tag: that the two properties determine the factorization up to a
unique isomorphism, that the comparison morphism `h` is again a relative normalization, and
that the factorization constructed in
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIn` has the two properties.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardAlgebraHom` is the morphism of direct-image algebras
  attached to a morphism of algebraic spaces affine over `X` by the anti-equivalence of
  Stacks 081V.
* `AlgebraicGeometry.Space.RelativeSpecUniversalProperty` is the universal property of the
  relative spectrum: a morphism over `X` from an arbitrary algebraic space into one affine
  over `X` is a morphism of `𝒪_X`-algebras in the other direction.
* `AlgebraicGeometry.Space.IntegralAlgebraDictionary` is the clause of Stacks 03ZP which reads
  integrality of a morphism affine over `X` off its algebra, in both directions.

## Main results

* `AlgebraicGeometry.Space.IsRelativeNormalization.existsUnique_iso`: two factorizations with
  the two properties are joined by a unique isomorphism compatible with both.  This is the
  word *characterized* of the source, which reads the two properties as initiality.
* `AlgebraicGeometry.Space.IsRelativeNormalization.comparison`: the comparison morphism
  `h : X' ⟶ Z` of the universal property exhibits `X'` as the normalization of `Z` in `Y`.
  This is the final clause of the source.
* `AlgebraicGeometry.Space.isRelativeNormalization_toNormalizationIn`: the factorization of
  Stacks 0822 has the two properties, with
  `AlgebraicGeometry.Space.existsUnique_hom_normalizationIn` the second of them in the
  over-category.
* `AlgebraicGeometry.Space.isAffineHom_of_isIntegralHom`: an integral morphism of algebraic
  spaces is affine.
* `AlgebraicGeometry.Space.AlgebraSheaf.isIntegral_integralClosureSheaf`: the integral closure
  of the structure sheaf in an algebra sheaf is an integral algebra sheaf, granted that over an
  affine chart its locally integral sections are integral.

## Implementation notes

**The shape of the two properties.**  A morphism `h : X' ⟶ Z` of the over-category `Over X`
carries the equation `π ∘ h = ν` in its structure, so that equation is not a side condition
but the typing of `h`; the source's commutative diagram is exactly a morphism of `Over X`, and
its uniqueness is `ExistsUnique`.  The test objects `Z` are algebraic spaces over `S`, as in
the source.  No quasi-compactness or quasi-separatedness hypothesis appears: those enter the
source only through the existence of the normalization, which is the content of Stacks 0822
and not of this tag, and the two formal results below hold for every factorization with the
two properties.

**What is carried for the canonical factorization, and why none of it is the content of this
tag.**  `AlgebraicGeometry.Space.isRelativeNormalization_toNormalizationIn` is stated for the
`ν` and `f'` of `StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIn`, so it carries the four
hypotheses that definition carries — the anti-equivalence `E` and base-change compatibility
`C` of Stacks 081V, quasi-coherence `hqc` of `f_* 𝒪_Y` from Stacks 03M9 and `hqc'` of the
integral closure from Stacks 0820, and the identity clause `hid` of Stacks 03G8 — together
with three more:

* `hloc`, the hypothesis `IsIntegralLocalOnAffineCharts` of
  `StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureSheaf`: over an affine chart a locally
  integral section is integral.  It is the other assertion of Stacks 0820, and it is what
  makes the integral closure an *integral* algebra sheaf, which is property (1).
* `D : IntegralAlgebraDictionary`, the translation of Stacks 03ZP between integral morphisms
  affine over `X` and integral algebras.  Both directions are used: the forward one gives
  property (1), the backward one supplies the integrality of the algebra `ℬ = π_* 𝒪_Z` of a
  test object, which is the hypothesis of the universal property of the integral closure.
  Neither direction is available, for the same reason the anti-equivalence is not: passing
  between the sections of a quasi-coherent sheaf over an affine chart and the represented base
  change is Descent, Proposition 03DX(2); see the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureSheaf`.
* `P : RelativeSpecUniversalProperty`, the universal property of the relative spectrum,
  `Mor_X(T, \underline{Spec}_X(𝒜)) = Hom_{𝒪_X}(𝒜, (T ⟶ X)_* 𝒪_T)`.  This is the input the
  source itself cites for the existence and uniqueness of `h`, as the functoriality of the
  relative spectrum; `AlgebraicGeometry.Space.relativeSpec` is built from the anti-equivalence
  of Stacks 081V, which gives this bijection only for a source `T` affine over `X`, and an
  arbitrary `T` needs in addition the formula for the sections of a direct image of sheaves of
  commutative rings that the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence` record as absent.  Its
  two compatibility fields pin it to the rest of the development rather than leaving it free:
  `equiv_affine` says that on an affine source it is the anti-equivalence, and
  `equiv_relativeSpecDirectImageMap` says that the canonical morphism of Stacks 081X
  corresponds to the canonical identification of `(\underline{Spec}_X(f_*𝒪_Y) ⟶ X)_* 𝒪` with
  `f_* 𝒪_Y`.  Those two are what let
  `AlgebraicGeometry.Space.RelativeSpecUniversalProperty.equiv_toNormalizationIn` be *proved*:
  the morphism `f'` corresponds to the inclusion `𝒪' ⊂ f_* 𝒪_Y`, which is the step the
  universal property of the normalization turns on, and it is a computation with the
  anti-equivalence rather than an assumption.

**The proof of the second property.**  It is the source's: the algebra `ℬ` of the test object
is integral, so its map `χ : ℬ ⟶ f_* 𝒪_Y` factors through the integral closure `𝒪'` and does so
in exactly one way — that is
`AlgebraicGeometry.Space.AlgebraSheaf.existsUnique_hom_integralClosureSheaf` of
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureUniversal`, the step the source performs
with Stacks 0820 — and the universal property of the relative spectrum turns that unique
factorization of algebras into the unique factorization of morphisms.  Nothing is chosen: the
morphism `h` is the image of the corestriction of `χ` under a bijection, and the source's "the
commutativity of the diagram is left to the reader" is the computation
`equiv_toNormalizationIn` together with the two-sided faithfulness of that bijection.

## References

* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 0821](https://stacks.math.columbia.edu/tag/0821)
* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
* [Stacks Project, Tag 081Z](https://stacks.math.columbia.edu/tag/081Z)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

/-! ### Integral morphisms are affine -/

/-- An integral morphism of algebraic spaces over `S` is affine: an integral morphism of
schemes is affine, so the representative of a base change to an affine test object is affine
over that test object. -/
theorem isAffineHom_of_isIntegralHom {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : IsIntegralHom B S hS f) : IsAffineHom B S hS f := by
  refine (isAffineHom_iff_holdsOnAffineBaseChange f).2 fun Z hZ g => ?_
  obtain ⟨W, p, q, hpb, hW, hp⟩ := hf Z hZ g
  exact ⟨W, p, q, hpb, hW, hp.toIsAffineHom⟩

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y X X' X'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : Y ⟶ X} {ν : X' ⟶ X} {f' : Y ⟶ X'}

namespace IsRelativeNormalization

/-! ### The characterization -/

/-- A morphism `X' ⟶ X'` compatible with the factorization and the integral morphism is the
identity, by the uniqueness in the universal property. -/
private theorem comp_eq_id_of_comp_eq (h : IsRelativeNormalization B S hS f ν f')
    (hX' : IsAlgebraicSpace B S hS X') (e : X' ⟶ X') (he : f' ≫ e = f') (heν : e ≫ ν = ν) :
    e = 𝟙 X' :=
  (h.existsUnique_lift hX' ν h.isIntegralHom f' h.fac).unique ⟨he, heν⟩
    ⟨Category.comp_id f', Category.id_comp ν⟩

/-- **Stacks 0823, the characterization.**  Two factorizations of `f` through an integral
morphism of algebraic spaces which both have the universal property are joined by a unique
isomorphism compatible with the two factorizations and the two integral morphisms. -/
@[stacks 0823 "properties (1) and (2) characterize the factorization"]
theorem existsUnique_iso {ν' : X'' ⟶ X} {f'' : Y ⟶ X''}
    (h : IsRelativeNormalization B S hS f ν f')
    (h' : IsRelativeNormalization B S hS f ν' f'')
    (hX' : IsAlgebraicSpace B S hS X') (hX'' : IsAlgebraicSpace B S hS X'') :
    ∃! e : X' ≅ X'', f' ≫ e.hom = f'' ∧ e.hom ≫ ν' = ν := by
  obtain ⟨a, ⟨ha, haν⟩, hauniq⟩ := h.existsUnique_lift hX'' ν' h'.isIntegralHom f'' h'.fac
  obtain ⟨b, ⟨hb, hbν⟩, -⟩ := h'.existsUnique_lift hX' ν h.isIntegralHom f' h.fac
  have hab := h.comp_eq_id_of_comp_eq hX' (a ≫ b)
    (by rw [← Category.assoc, ha, hb]) (by rw [Category.assoc, hbν, haν])
  have hba := h'.comp_eq_id_of_comp_eq hX'' (b ≫ a)
    (by rw [← Category.assoc, hb, ha]) (by rw [Category.assoc, haν, hbν])
  exact ⟨⟨a, b, hab, hba⟩, ⟨ha, haν⟩, fun e he => Iso.ext (hauniq e.hom he)⟩

/-! ### The comparison morphism is itself a relative normalization -/

/-- **Stacks 0823, the final clause.**  Let `f = π ∘ g` be a factorization of `f` through an
integral morphism `π : Z ⟶ X`, and let `k : X' ⟶ Z` be the comparison morphism supplied by the
universal property.  Then `k` exhibits `X'` as the normalization of `Z` in `Y`. -/
@[stacks 0823 "moreover, the comparison morphism is the normalization of Z in Y"]
theorem comparison {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : IsRelativeNormalization B S hS f ν f')
    (hX : IsAlgebraicSpace B S hS X) (hZ : IsAlgebraicSpace B S hS Z)
    {π : Z ⟶ X} (hπ : IsIntegralHom B S hS π) {g : Y ⟶ Z}
    {k : X' ⟶ Z} (hk : f' ≫ k = g) (hkν : k ≫ π = ν) :
    IsRelativeNormalization B S hS g k f' := by
  have hg : g ≫ π = f := by rw [← hk, Category.assoc, hkν, h.fac]
  refine ⟨hk, ?_, ?_⟩
  · refine isIntegralHom_of_comp_of_isSeparated B S hS k π ?_
      (isSeparated_of_isAffineHom B S hS π hZ hX (isAffineHom_of_isIntegralHom π hπ))
    rw [hkν]
    exact h.isIntegralHom
  · intro Z' hZ' π' hπ' g' hg'
    obtain ⟨l, ⟨hl, hlν⟩, hluniq⟩ := h.existsUnique_lift hZ' (π' ≫ π)
      (isIntegralHom_comp B S hS hπ' hπ) g' (by rw [← Category.assoc, hg', hg])
    refine ⟨l, ⟨hl, (h.existsUnique_lift hZ π hπ g hg).unique
      ⟨by rw [← Category.assoc, hl, hg'], by rw [Category.assoc, hlν]⟩ ⟨hk, hkν⟩⟩, ?_⟩
    rintro y ⟨hy, hyπ⟩
    exact hluniq y ⟨hy, by rw [← Category.assoc, hyπ, hkν]⟩

end IsRelativeNormalization

/-! ### The algebra map of a morphism of spaces affine over the base -/

variable (B S hS) in
/-- The morphism of direct-image algebras attached to a morphism of algebraic spaces affine
over `X`: the anti-equivalence of Stacks 081V applied to it, read through its identification
with direct image. -/
def pushforwardAlgebraHom (E : AffineAlgebraAntiEquivalence B S hS)
    {X : AlgebraicSpaces B S hS} {W W' : AffineOver B S hS X} (k : W ⟶ W') :
    pushforwardAlgebra B S hS W'.obj ⟶ pushforwardAlgebra B S hS W.obj :=
  (E.pushforward_obj X W').inv ≫
    (quasicoherentAlgebraInclusion B S hS X).map ((E.pushforward X).map k.op) ≫
    (E.pushforward_obj X W).hom

variable (B S hS) in
/-- The morphism of relative spectra induced by a morphism of quasi-coherent algebras has that
morphism for its algebra map, read through the identification of the direct image of the
structure sheaf of a relative spectrum with the algebra it is formed from. -/
theorem pushforwardAlgebraHom_inverse_map (E : AffineAlgebraAntiEquivalence B S hS)
    {X : AlgebraicSpaces B S hS} {A A' : QuasicoherentAlgebra B S hS X} (φ : A' ⟶ A) :
    pushforwardAlgebraHom B S hS E ((E.equivalence X).inverse.map φ).unop =
      (relativeSpecPushforwardIso B S hS E A').hom ≫ φ.hom ≫
        (relativeSpecPushforwardIso B S hS E A).inv := by
  dsimp only [pushforwardAlgebraHom, relativeSpec, Quiver.Hom.op_unop]
  rw [← NatIso.naturality_1 (E.pushforwardIso X), Equivalence.fun_inv_map]
  dsimp only [relativeSpecPushforwardIso, relativeSpec]
  simp

/-! ### The integral closure is an integral algebra -/

namespace AlgebraSheaf

/-- Integrality descends along an injective ring homomorphism over a common coefficient ring:
if `σ ∘ g = f` with `σ` injective, then an element whose image under `σ` is integral over `f`
is itself integral over `g`, the same monic polynomial witnessing both. -/
theorem isIntegralElem_of_injective {R A A' : Type*} [CommRing R] [CommRing A] [CommRing A']
    {f : R →+* A} {g : R →+* A'} (σ : A' →+* A) (hσ : Function.Injective σ)
    (hcomm : σ.comp g = f) {x : A'} (hx : f.IsIntegralElem (σ x)) : g.IsIntegralElem x := by
  obtain ⟨p, hp, hp0⟩ := hx
  refine ⟨p, hp, hσ ?_⟩
  rw [map_zero, Polynomial.hom_eval₂, hcomm, hp0]

/-- **The integral closure of the structure sheaf is an integral algebra sheaf**, granted that
over an affine chart its locally integral sections are already integral.  Its sections are a
subring of those of the ambient algebra, and integrality descends along that inclusion. -/
theorem isIntegral_integralClosureSheaf {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} {A : AlgebraSheaf.{u, m} B S hS F hF}
    (h : A.IsIntegralLocalOnAffineCharts) : (integralClosureSheaf A).IsIntegral := by
  intro V hV a
  exact isIntegralElem_of_injective ((A.locallyIntegralSections (op V)).subtype)
    Subtype.val_injective (RingHom.ext fun _ => rfl)
    (mem_integralSections.1 (h V hV a.1 a.2))

end AlgebraSheaf

/-! ### The two clauses of Stacks 081V and 03ZP that are carried -/

variable (B S hS) in
/-- The universal property of the relative spectrum over an algebraic space `X`: a morphism
over `X` from an arbitrary algebraic space into one affine over `X` is the same thing as a
morphism of `𝒪_X`-algebras in the other direction, the correspondence turning composition into
composition in the other order, agreeing on affine sources with the anti-equivalence of
Stacks 081V, and matching the canonical morphism of Stacks 081X with the canonical
identification of `(\underline{Spec}_X(f_*𝒪_Y) ⟶ X)_* 𝒪` with `f_* 𝒪_Y`. -/
structure RelativeSpecUniversalProperty (E : AffineAlgebraAntiEquivalence B S hS)
    (C : BaseChangeCompatibility B S hS E) where
  /-- Morphisms over `X` into a space affine over `X` are algebra maps in the other
  direction. -/
  equiv : ∀ {X : AlgebraicSpaces B S hS} (T : Over X) (W : AffineOver B S hS X),
    (T ⟶ W.obj) ≃ (pushforwardAlgebra B S hS W.obj ⟶ pushforwardAlgebra B S hS T)
  /-- The correspondence turns composition into composition in the other order. -/
  equiv_comp : ∀ {X : AlgebraicSpaces B S hS} (T : Over X) {W W' : AffineOver B S hS X}
      (u : T ⟶ W.obj) (k : W.obj ⟶ W'.obj),
    equiv T W' (u ≫ k) = equiv W.obj W' k ≫ equiv T W u
  /-- On a source affine over `X` the correspondence is the anti-equivalence of Stacks 081V. -/
  equiv_affine : ∀ {X : AlgebraicSpaces B S hS} {W W' : AffineOver B S hS X} (k : W ⟶ W'),
    equiv W.obj W' k.hom = pushforwardAlgebraHom B S hS E k
  /-- The canonical morphism of Stacks 081X corresponds to the canonical identification of the
  direct image of the structure sheaf of `\underline{Spec}_X(f_*𝒪_Y)` with `f_* 𝒪_Y`. -/
  equiv_relativeSpecDirectImageMap : ∀ {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
      (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
      (hid : pushforwardAlgebra B S hS (idAffineOver B S hS Y).obj ≅ unitAlgebra B S hS Y),
    equiv (Over.mk f) (relativeSpecDirectImage B S hS E f hqc)
        (relativeSpecDirectImageMap B S hS E C f hqc hid) =
      (relativeSpecDirectImagePushforwardIso B S hS E f hqc).hom

variable (B S hS) in
/-- The dictionary between integral morphisms and integral algebras, which is the clause of
Stacks 03ZP that reads integrality of a morphism affine over `X` off its algebra: the relative
spectrum of an integral quasi-coherent algebra is an integral morphism, and the direct-image
algebra of an integral morphism is an integral algebra. -/
structure IntegralAlgebraDictionary (E : AffineAlgebraAntiEquivalence B S hS) where
  /-- The relative spectrum of an integral quasi-coherent algebra is an integral morphism. -/
  isIntegralHom_relativeSpec : ∀ {X : AlgebraicSpaces B S hS}
      (A : QuasicoherentAlgebra B S hS X),
    A.obj.IsIntegral → IsIntegralHom B S hS (relativeSpec B S hS E A).obj.hom.hom
  /-- The direct-image algebra of an integral morphism is an integral algebra. -/
  isIntegral_pushforwardAlgebra : ∀ {X : AlgebraicSpaces B S hS} (W : AffineOver B S hS X),
    IsIntegralHom B S hS W.obj.hom.hom → (pushforwardAlgebra B S hS W.obj).IsIntegral

/-! ### The canonical factorization has the universal property -/

variable {E : AffineAlgebraAntiEquivalence B S hS} {C : BaseChangeCompatibility B S hS E}
    {X Y : AlgebraicSpaces B S hS}

/-- The canonical morphism `f' : Y ⟶ X'` to the normalization of `X` in `Y` corresponds, under
the universal property of the relative spectrum, to the inclusion `𝒪' ⊂ f_* 𝒪_Y` of the
integral closure. -/
theorem RelativeSpecUniversalProperty.equiv_toNormalizationIn
    (P : RelativeSpecUniversalProperty B S hS E C) (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent)
    (hid : pushforwardAlgebra B S hS (idAffineOver B S hS Y).obj ≅ unitAlgebra B S hS Y) :
    P.equiv (Over.mk f) (normalizationIn B S hS E f hqc')
        (toNormalizationIn B S hS E C f hqc hqc' hid) =
      (normalizationInPushforwardIso B S hS E f hqc').hom ≫
        AlgebraSheaf.integralClosureInclusion (pushforwardAlgebra B S hS (Over.mk f)) := by
  have key : pushforwardAlgebraHom B S hS E
        (relativeSpecDirectImageToNormalizationIn B S hS E f hqc hqc') =
      (normalizationInPushforwardIso B S hS E f hqc').hom ≫
        AlgebraSheaf.integralClosureInclusion (pushforwardAlgebra B S hS (Over.mk f)) ≫
        (relativeSpecDirectImagePushforwardIso B S hS E f hqc).inv :=
    pushforwardAlgebraHom_inverse_map B S hS E
      (normalizationInAlgebraInclusion B S hS f hqc hqc')
  rw [toNormalizationIn, P.equiv_comp, P.equiv_affine, key,
    P.equiv_relativeSpecDirectImageMap]
  simp

/-- The universal property of the normalization of `X` in `Y` in the over-category: a morphism
over `X` from `Y` to an algebraic space affine over `X` whose structure morphism is integral
factors through the normalization in exactly one way.

The algebra of the target is integral, so its map to `f_* 𝒪_Y` lands in the integral closure
`𝒪'` and does so uniquely; the universal property of the relative spectrum turns that unique
factorization of algebras into the unique factorization of morphisms. -/
theorem existsUnique_hom_normalizationIn (P : RelativeSpecUniversalProperty B S hS E C)
    (D : IntegralAlgebraDictionary B S hS E) (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent)
    (hid : pushforwardAlgebra B S hS (idAffineOver B S hS Y).obj ≅ unitAlgebra B S hS Y)
    (W : AffineOver B S hS X) (hW : IsIntegralHom B S hS W.obj.hom.hom)
    (u : Over.mk f ⟶ W.obj) :
    ∃! k : (normalizationIn B S hS E f hqc').obj ⟶ W.obj,
      toNormalizationIn B S hS E C f hqc hqc' hid ≫ k = u := by
  obtain ⟨ψ, hψ, hψuniq⟩ := AlgebraSheaf.existsUnique_hom_integralClosureSheaf
    (P.equiv (Over.mk f) W u) (D.isIntegral_pushforwardAlgebra W hW)
  refine ⟨(P.equiv (normalizationIn B S hS E f hqc').obj W).symm
      (ψ ≫ (normalizationInPushforwardIso B S hS E f hqc').inv), ?_, fun k hk => ?_⟩
  · refine (P.equiv (Over.mk f) W).injective ?_
    rw [P.equiv_comp, Equiv.apply_symm_apply, P.equiv_toNormalizationIn]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact hψ
  · refine (P.equiv (normalizationIn B S hS E f hqc').obj W).injective ?_
    rw [Equiv.apply_symm_apply]
    refine (Iso.eq_comp_inv _).2 (hψuniq _ ?_)
    simp only [Category.assoc]
    rw [← P.equiv_toNormalizationIn f hqc hqc' hid, ← P.equiv_comp, hk]

/-- **Stacks 0823, properties (1) and (2) for the canonical factorization.**  The factorization
`f = ν ∘ f'` of `f` through the normalization `ν : X' ⟶ X` of `X` in `Y` has `ν` integral, and
every factorization of `f` through an integral morphism `π : Z ⟶ X` of algebraic spaces
receives a unique morphism `h : X' ⟶ Z` with `f' ∘ h = g` and `π ∘ h = ν`. -/
@[stacks 0823 "the canonical factorization has properties (1) and (2)"]
theorem isRelativeNormalization_toNormalizationIn
    (P : RelativeSpecUniversalProperty B S hS E C)
    (D : IntegralAlgebraDictionary B S hS E) (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent)
    (hid : pushforwardAlgebra B S hS (idAffineOver B S hS Y).obj ≅ unitAlgebra B S hS Y)
    (hloc : (pushforwardAlgebra B S hS (Over.mk f)).IsIntegralLocalOnAffineCharts) :
    IsRelativeNormalization B S hS f.hom
      (normalizationIn B S hS E f hqc').obj.hom.hom
      (toNormalizationIn B S hS E C f hqc hqc' hid).left.hom := by
  refine ⟨congrArg (fun k => k.hom)
      (toNormalizationIn_factorization B S hS E C f hqc hqc' hid),
    D.isIntegralHom_relativeSpec (normalizationInAlgebra B S hS f hqc')
      (AlgebraSheaf.isIntegral_integralClosureSheaf hloc), ?_⟩
  intro Z hZ π hπ g hg
  obtain ⟨k, hk, hkuniq⟩ := existsUnique_hom_normalizationIn P D f hqc hqc' hid
    ⟨Over.mk (ObjectProperty.homMk π : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ X),
      isAffineHom_of_isIntegralHom π hπ⟩ hπ
    (Over.homMk (ObjectProperty.homMk g) (by exact ObjectProperty.hom_ext _ hg))
  refine ⟨k.left.hom, ⟨congrArg (fun m => m.left.hom) hk,
    congrArg (fun m => m.hom) (Over.w k)⟩, ?_⟩
  rintro h ⟨h1, h2⟩
  exact congrArg (fun m => m.left.hom)
    (hkuniq (Over.homMk (ObjectProperty.homMk h) (by exact ObjectProperty.hom_ext _ h2))
      (Over.OverMorphism.ext (ObjectProperty.hom_ext _ h1)))

end AlgebraicGeometry.Space

end
