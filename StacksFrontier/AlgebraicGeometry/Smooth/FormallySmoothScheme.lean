module

public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothCriterion
public import StacksFrontier.AlgebraicGeometry.Thickenings
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Formally smooth morphisms of schemes

A morphism of schemes `f : X ⟶ S` is *formally smooth* when every morphism to `X` from the
closed subscheme of an affine first-order thickening extends, over `S`, to the whole
thickening. This file states that lifting property in the geometric language of thickenings
and identifies it with the ring-theoretic presentation
`Stacks.Smooth.FormallySmooth` already available, which lets the consequences proved there be
restated in the geometric vocabulary.

## Main definitions

* `Stacks.Smooth.FormallySmoothScheme` is the infinitesimal lifting property, quantified over
  first-order thickenings `i : T ⟶ T'` of affine schemes.

## Main results

* `Stacks.Smooth.isFirstOrderThickening_specMap`: a surjection of rings with square-zero
  kernel induces a first-order thickening of affine schemes.
* `Stacks.Smooth.formallySmoothScheme_iff`: the two presentations of formal smoothness agree,
  `FormallySmoothScheme f ↔ FormallySmooth f`. Both directions are proved.
* `Stacks.Smooth.smooth_of_formallySmoothScheme`: a formally smooth morphism that is locally of
  finite presentation is smooth. This is the hard direction of Stacks Project, Tag 02H6, stated
  with the geometric lifting property.
* `Stacks.Smooth.smooth_iff_formallySmoothScheme_of_isAffineHom`: for an affine morphism,
  smoothness is equivalent to being formally smooth and locally of finite presentation.

## Implementation notes

The two presentations of formal smoothness quantify over the same data in different shapes.
`Stacks.Smooth.FormallySmoothScheme` takes a closed immersion `i : T ⟶ T'` of affine schemes
with square-zero kernel ideal sheaf, while `Stacks.Smooth.FormallySmooth` takes a surjection of
rings `φ : R ⟶ A` with square-zero kernel and uses `Spec.map φ`. Translating between them needs
two dictionaries:

* the closed-immersion dictionary, which is
  `AlgebraicGeometry.IsClosedImmersion.spec_of_surjective` one way and
  `AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine` the other; and
* the ideal dictionary `Stacks.Smooth.ker_pow_eq_bot_iff_of_isAffine`, which identifies a power
  of `AlgebraicGeometry.Scheme.Hom.ker` with the corresponding power of `RingHom.ker` on global
  sections. Over an affine target, ideal sheaves are determined by their ideal of global
  sections — `AlgebraicGeometry.Scheme.IdealSheafData.ext_of_isAffine` — and the ideal of
  global sections of the kernel ideal sheaf of a quasi-compact morphism is the kernel of the
  map on global sections, by `AlgebraicGeometry.Scheme.Hom.ker_apply`.

Going from a ring surjection to a thickening also needs the kernel of
`(Spec.map φ).appTop`, which is the kernel of `φ` pulled back along the unit isomorphism
`AlgebraicGeometry.Scheme.ΓSpecIso`; this is `Stacks.Smooth.ker_specMap_appTop`. Transporting
the vanishing of a power through that pullback uses only the inequality `Ideal.le_comap_pow`,
which holds for any ring map: a power of a pullback is contained in the pullback of the power,
which here is the pullback of `⊥` along an injective map and so is `⊥`. The reverse inequality,
which would need surjectivity, is not required.

The direction `FormallySmooth f → FormallySmoothScheme f` replaces an affine thickening
`i : T ⟶ T'` by `Spec.map i.appTop` using the canonical isomorphisms
`AlgebraicGeometry.Scheme.isoSpec` and their naturality, rather than
`Stacks.Smooth.FormallySmooth.of_iso`, because the source and target of the thickening are
transported simultaneously with the lift.

Nothing here carries `@[stacks 02H6]`; only the affine case and the hard direction are stated
here. The unrestricted equivalence
`Smooth f ↔ LocallyOfFinitePresentation f ∧ FormallySmoothScheme f` is proved in
`StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag`, as
`Stacks.Smooth.smooth_iff_locallyOfFinitePresentation_and_formallySmooth`, which carries the
tag. The missing half had been that a smooth morphism which is not affine is formally smooth:
on a cover of the source one gets local lifts, but the set of lifts on an open is a torsor
under the sections of `Hom(g^*Ω, I)`, so gluing them is obstructed by the first cohomology of a
quasi-coherent sheaf on the affine thickening. That obstruction is what the Čech assembly in
`SmoothFormallySmoothTag` discharges.

## References

* [Stacks Project, Tag 02H0](https://stacks.math.columbia.edu/tag/02H0)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Smooth

/-- A morphism of schemes `f : X ⟶ S` is **formally smooth** when it has the infinitesimal
lifting property: for every first-order thickening `i : T ⟶ T'` of affine schemes, every
commutative square
```
T  --g--→ X
|         |
i         f
↓         ↓
T' --h--→ S
```
has a diagonal filler `g' : T' ⟶ X`, that is a morphism with `g' ≫ f = h` and `i ≫ g' = g`. -/
@[stacks 02H0, ega "IV 17.1.1", sga "3 XVII 5.7.1"]
abbrev FormallySmoothScheme {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ {T T' : Scheme.{u}} (_ : IsAffine T) (_ : IsAffine T') (i : T ⟶ T'),
    Thickenings.IsFirstOrderThickening i → ∀ (g : T ⟶ X) (h : T' ⟶ S), g ≫ f = i ≫ h →
      ∃ g' : T' ⟶ X, (g' ≫ f = h) ∧ (i ≫ g' = g)

/-- Over an affine target, a power of the kernel ideal sheaf of a quasi-compact morphism
vanishes exactly when the corresponding power of the kernel of the map on global sections
vanishes. Ideal sheaves on an affine scheme are determined by their ideal of global sections,
and that ideal of the kernel ideal sheaf is the kernel on global sections. -/
theorem ker_pow_eq_bot_iff_of_isAffine {T T' : Scheme.{u}} [IsAffine T'] (i : T ⟶ T')
    [QuasiCompact i] (n : ℕ) : i.ker ^ n = ⊥ ↔ RingHom.ker i.appTop.hom ^ n = ⊥ := by
  have key : (i.ker ^ n).ideal ⟨⊤, isAffineOpen_top T'⟩ = RingHom.ker i.appTop.hom ^ n := by
    simp
    rfl
  exact ⟨fun h => by rw [← key, h]; simp, fun h => Scheme.IdealSheafData.ext_of_isAffine
    (by rw [key, h]; simp)⟩

/-- The kernel of the map on global sections induced by `Spec.map φ` is the kernel of `φ`
pulled back along the unit isomorphism `AlgebraicGeometry.Scheme.ΓSpecIso`. -/
theorem ker_specMap_appTop {R A : CommRingCat.{u}} (φ : R ⟶ A) :
    RingHom.ker (Spec.map φ).appTop.hom =
      (RingHom.ker φ.hom).comap (Scheme.ΓSpecIso R).hom.hom := by
  rw [RingHom.comap_ker, ← CommRingCat.hom_comp, ← Scheme.ΓSpecIso_naturality,
    CommRingCat.hom_comp]
  exact (RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv).symm

/-- If a power of the kernel of `φ` vanishes, so does the same power of the kernel of the map
on global sections induced by `Spec.map φ`. -/
theorem ker_specMap_appTop_pow_eq_bot {R A : CommRingCat.{u}} (φ : R ⟶ A) {n : ℕ}
    (h : RingHom.ker φ.hom ^ n = ⊥) : RingHom.ker (Spec.map φ).appTop.hom ^ n = ⊥ :=
  le_bot_iff.mp (ker_specMap_appTop φ ▸ (Ideal.le_comap_pow _ n).trans
    (h ▸ (Ideal.comap_bot_of_injective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1).le))

/-- A surjection of rings with square-zero kernel presents a first-order thickening of affine
schemes. -/
theorem isFirstOrderThickening_specMap {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (hφ : Function.Surjective φ.hom) (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥) :
    Thickenings.IsFirstOrderThickening (Spec.map φ) :=
  ⟨IsClosedImmersion.spec_of_surjective φ hφ,
    (ker_pow_eq_bot_iff_of_isAffine (Spec.map φ) 2).mpr (ker_specMap_appTop_pow_eq_bot φ hφ2)⟩

/-- The geometric lifting property implies the ring-theoretic one: a surjection of rings with
square-zero kernel is an affine first-order thickening. -/
theorem formallySmooth_of_formallySmoothScheme {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : FormallySmoothScheme f) : FormallySmooth f := by
  intro R A φ hφ hφ2 g h hcomm
  obtain ⟨g', hg1, hg2⟩ := hf (T := Spec A) (T' := Spec R) inferInstance inferInstance
    (Spec.map φ) (isFirstOrderThickening_specMap φ hφ hφ2) g h hcomm
  exact ⟨g', hg2, hg1⟩

/-- The ring-theoretic lifting property implies the geometric one: an affine first-order
thickening `i : T ⟶ T'` is isomorphic, as an arrow, to `Spec.map i.appTop`, which is the
spectrum of a surjection with square-zero kernel. -/
theorem formallySmoothScheme_of_formallySmooth {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : FormallySmooth f) : FormallySmoothScheme f := by
  rintro T T' hT hT' i ⟨hci, hker⟩ g h hcomm
  obtain ⟨g₀, hg1, hg2⟩ := hf Γ(T', ⊤) Γ(T, ⊤) i.appTop
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
    ((ker_pow_eq_bot_iff_of_isAffine i 2).mp hker) (T.isoSpec.inv ≫ g) (T'.isoSpec.inv ≫ h)
    (by rw [Category.assoc, hcomm, ← Category.assoc, ← Category.assoc,
      Scheme.isoSpec_inv_naturality])
  refine ⟨T'.isoSpec.hom ≫ g₀, ?_, ?_⟩
  · rw [Category.assoc, hg2, Iso.hom_inv_id_assoc]
  · rw [← Category.assoc, ← Scheme.isoSpec_hom_naturality, Category.assoc, hg1,
      Iso.hom_inv_id_assoc]

/-- **The two presentations of formal smoothness agree.** The geometric lifting property
against affine first-order thickenings is the same condition as the ring-theoretic lifting
property against spectra of ring surjections with square-zero kernel. -/
theorem formallySmoothScheme_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    FormallySmoothScheme f ↔ FormallySmooth f :=
  ⟨formallySmooth_of_formallySmoothScheme, formallySmoothScheme_of_formallySmooth⟩

/-- **The hard direction of Stacks Project, Tag 02H6**, in the geometric vocabulary: a formally
smooth morphism that is locally of finite presentation is smooth. -/
@[ega "IV 17.3.1" "sufficiency", sga "3 XI 1.1" "partial"]
theorem smooth_of_formallySmoothScheme {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (hf : FormallySmoothScheme f) :
    AlgebraicGeometry.Smooth f :=
  smooth_of_formallySmooth f (formallySmooth_of_formallySmoothScheme hf)

/-- **The easy direction of Stacks Project, Tag 02H6 for an affine morphism**, in the geometric
vocabulary: a smooth affine morphism is formally smooth. -/
@[ega "IV 17.14.1" "partial", sga "3 III 0.16" "special case", sga "3 III 0.17" "more general"]
theorem formallySmoothScheme_of_isAffineHom {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.Smooth f] [IsAffineHom f] : FormallySmoothScheme f :=
  formallySmoothScheme_of_formallySmooth (formallySmooth_of_isAffineHom f)

/-- **Stacks Project, Tag 02H6 for an affine morphism**, in the geometric vocabulary: an affine
morphism is smooth if and only if it is formally smooth and locally of finite presentation. -/
@[ega "IV 17.14.1" "partial",
  ega "IV 17.3.1" "special case",
  sga "1 III 5.5" "special case",
  sga "3 III 0.16" "special case",
  sga "3 III 0.17" "more general",
  sga "3 III 2.5" "(a), partial",
  sga "3 XI 1.1" "special case"]
theorem smooth_iff_formallySmoothScheme_of_isAffineHom {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffineHom f] :
    AlgebraicGeometry.Smooth f ↔ FormallySmoothScheme f ∧ LocallyOfFinitePresentation f := by
  rw [smooth_iff_of_isAffineHom f, formallySmoothScheme_iff]

end Stacks.Smooth

end
