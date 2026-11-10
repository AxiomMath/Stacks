module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute

/-!
# The infinitesimal lifting criterion for smoothness

A morphism of schemes is smooth exactly when it is locally of finite presentation and formally
smooth, where formal smoothness is the requirement that every morphism into the source from a
first-order thickening of an affine scheme over the base extends to the thickening. This file
sets up the scheme-level lifting property, identifies it with `Algebra.FormallySmooth` in the
affine case, and proves the two implications of the criterion that follow from that dictionary.

## Main definitions

* `Stacks.Smooth.FormallySmooth` is the scheme-level lifting property: for every surjection of
  rings `φ : R ⟶ A` with square-zero kernel — that is, for every first-order thickening
  `Spec A ⟶ Spec R` of affine schemes — every `Spec A ⟶ X` over a given `Spec R ⟶ S` extends
  along `Spec A ⟶ Spec R` to a morphism `Spec R ⟶ X` over `S`.

## Main results

* `Stacks.Smooth.formallySmooth_specMap_iff` is the ring dictionary: the lifting property for
  `Spec.map φ` is exactly `RingHom.FormallySmooth φ.hom`, hence exactly
  `Algebra.FormallySmooth` for the algebra structure induced by `φ`.
* `Stacks.Smooth.formallySmooth_iff_of_isAffine` is the same statement for an arbitrary morphism
  of affine schemes, in terms of the map on global sections.
* `Stacks.Smooth.smooth_iff_of_isAffine` is the smoothness criterion for a morphism of affine
  schemes: it is smooth iff it is formally smooth and locally of finite presentation.
* `Stacks.Smooth.FormallySmooth.resLE` is Tag 02H3: formal smoothness passes to the restriction
  of a morphism to an open of the source lying over an open of the target.
* `Stacks.Smooth.smooth_of_formallySmooth` is the hard direction of the criterion in full
  generality: a formally smooth morphism that is locally of finite presentation is smooth.
* `Stacks.Smooth.formallySmooth_of_isAffineHom` is the easy direction, proved here only for an
  affine morphism: a smooth affine morphism is formally smooth.
* `Stacks.Smooth.smooth_iff_of_isAffineHom` assembles the two into the criterion for affine
  morphisms.

## Implementation notes

The thickening in `Stacks.Smooth.FormallySmooth` is presented by a ring surjection with
square-zero kernel rather than by a closed immersion of schemes with square-zero ideal sheaf.
The two presentations agree because an affine first-order thickening is the spectrum of such a
surjection, and the ring-theoretic form is what Mathlib's `Algebra.FormallySmooth` API consumes.
This is also the shape in which Mathlib states the companion criterion
`AlgebraicGeometry.FormallyUnramified.of_hom_ext`.

The easy direction `smooth → formally smooth` is proved only for affine morphisms. For an affine
morphism one may base change to the thickening, where source and target both become affine and
the ring dictionary applies directly. In general the local lifts produced that way have to be
glued, and the gluing is governed by the vanishing of the first cohomology of a quasi-coherent
sheaf on the affine thickening; that argument is not carried out here.

The hard direction, by contrast, is proved in full generality: formal smoothness passes to the
restrictions `Scheme.Hom.resLE` (the only input being that a first-order thickening of affine
schemes is surjective on points, so that a lift automatically factors through an open
neighbourhood of the image), and smoothness is Zariski-local at source and target.

## References

* [Stacks Project, Tag 02H3](https://stacks.math.columbia.edu/tag/02H3)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Smooth

/-- The infinitesimal lifting property for a morphism of schemes `f : X ⟶ S`: for every
first-order thickening of affine schemes, presented as `Spec.map φ : Spec A ⟶ Spec R` for a
surjection of rings `φ : R ⟶ A` with square-zero kernel, every commutative square
```
Spec A --g--→ X
  |           |
Spec φ        f
  ↓           ↓
Spec R --h--→ S
```
has a diagonal filler `g' : Spec R ⟶ X`, that is a morphism with `Spec.map φ ≫ g' = g` and
`g' ≫ f = h`. -/
@[ega "0 19.0.1", sga "3 XVII 5.7.1"]
def FormallySmooth : MorphismProperty Scheme.{u} := fun X S f =>
  ∀ (R A : CommRingCat.{u}) (φ : R ⟶ A), Function.Surjective φ.hom →
    RingHom.ker φ.hom ^ 2 = ⊥ →
    ∀ (g : Spec A ⟶ X) (h : Spec R ⟶ S), g ≫ f = Spec.map φ ≫ h →
      ∃ g' : Spec R ⟶ X, Spec.map φ ≫ g' = g ∧ g' ≫ f = h

/-- A first-order thickening of affine schemes is surjective on points: if `φ` is surjective
with square-zero kernel then every prime of `R` is the contraction of a prime of `A`, because
the kernel consists of nilpotents and so lies in every prime. -/
theorem specMap_base_surjective {R A : CommRingCat.{u}} {φ : R ⟶ A}
    (hφ : Function.Surjective φ.hom) (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥) :
    Function.Surjective (Spec.map φ).base := by
  have hrange : Set.range (PrimeSpectrum.comap φ.hom) = Set.univ := by
    rw [range_comap_of_surjective _ _ hφ, Set.eq_univ_iff_forall]
    intro p x hx
    refine p.isPrime.mem_of_pow_mem 2 ?_
    have hxx := Ideal.mul_mem_mul hx hx
    rw [← pow_two, hφ2, Ideal.mem_bot] at hxx
    rw [pow_two, hxx]
    exact zero_mem _
  exact fun p => (hrange.ge (Set.mem_univ p)).imp fun _ h => h

/-- The lifting property transports along an isomorphism of arrows. -/
theorem FormallySmooth.of_iso {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    (eX : X ≅ X') (eS : S ≅ S') (he : f ≫ eS.hom = eX.hom ≫ f') (hf : FormallySmooth f) :
    FormallySmooth f' := by
  have he' : eX.inv ≫ f = f' ≫ eS.inv := by
    rw [Iso.eq_comp_inv, Category.assoc, he, Iso.inv_hom_id_assoc]
  intro R A φ hφ hφ2 g h hcomm
  obtain ⟨k, hk1, hk2⟩ := hf R A φ hφ hφ2 (g ≫ eX.inv) (h ≫ eS.inv)
    (by rw [Category.assoc, he', ← Category.assoc, hcomm, Category.assoc])
  refine ⟨k ≫ eX.hom, ?_, ?_⟩
  · rw [← Category.assoc, hk1, Category.assoc, eX.inv_hom_id, Category.comp_id]
  · rw [Category.assoc, ← he, ← Category.assoc, hk2, Category.assoc, eS.inv_hom_id,
      Category.comp_id]

/-- The ring dictionary, in the direction that turns a formally smooth ring map into the
scheme-level lifting property: the lift is `Algebra.FormallySmooth.liftOfSurjective`. -/
theorem formallySmooth_specMap {R A : CommRingCat.{u}} {ψ : R ⟶ A} (hψ : ψ.hom.FormallySmooth) :
    FormallySmooth (Spec.map ψ) := by
  intro R' A' φ hφ hφ2 g h hcomm
  obtain ⟨a, rfl⟩ := Spec.map_surjective g
  obtain ⟨b, rfl⟩ := Spec.map_surjective h
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at hcomm
  let : Algebra R A := ψ.hom.toAlgebra
  let : Algebra R R' := b.hom.toAlgebra
  let : Algebra R A' := (b ≫ φ).hom.toAlgebra
  have hfs : Algebra.FormallySmooth R A := hψ
  let aA : A →ₐ[R] A' :=
    { a.hom with
      commutes' := fun r => by
        change a.hom (ψ.hom r) = (b ≫ φ).hom r
        rw [← hcomm]
        rfl }
  let φA : R' →ₐ[R] A' := { φ.hom with commutes' := fun _ => rfl }
  have hnil : IsNilpotent (RingHom.ker (φA : R' →+* A')) :=
    ⟨2, show RingHom.ker φ.hom ^ 2 = 0 by simpa using hφ2⟩
  refine ⟨Spec.map (CommRingCat.ofHom
      (Algebra.FormallySmooth.liftOfSurjective aA φA hφ hnil).toRingHom), ?_, ?_⟩
  · rw [← Spec.map_comp, Spec.map_inj]
    ext x
    exact Algebra.FormallySmooth.liftOfSurjective_apply aA φA hφ hnil x
  · rw [← Spec.map_comp, Spec.map_inj]
    ext r
    exact (Algebra.FormallySmooth.liftOfSurjective aA φA hφ hnil).commutes r

/-- The ring dictionary, in the direction that reads a formally smooth ring map off the
scheme-level lifting property: the square-zero extensions of `R`-algebras tested by
`Algebra.FormallySmooth.of_comp_surjective` are exactly the affine first-order thickenings. -/
@[ega "IV 17.1.2" "(i)"]
theorem formallySmooth_ringHom_of_formallySmooth {R A : CommRingCat.{u}} {ψ : R ⟶ A}
    (hψ : FormallySmooth (Spec.map ψ)) : ψ.hom.FormallySmooth := by
  let : Algebra R A := ψ.hom.toAlgebra
  change Algebra.FormallySmooth R A
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ I hI G => ?_
  obtain ⟨g', hg1, hg2⟩ := hψ (.of B) (.of (B ⧸ I))
    (CommRingCat.ofHom (Ideal.Quotient.mk I)) Ideal.Quotient.mk_surjective (by simpa using hI)
    (Spec.map (CommRingCat.ofHom G.toRingHom))
    (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (by rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
        ext r
        simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
          CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        exact G.commutes r)
  obtain ⟨a', rfl⟩ := Spec.map_surjective g'
  rw [← Spec.map_comp, Spec.map_inj] at hg1 hg2
  exact ⟨{ a'.hom with commutes' := fun r => congr($hg2 r) }, by ext x; exact congr($hg1 x)⟩

/-- **The ring dictionary.** For a map of rings `ψ`, the scheme-level infinitesimal lifting
property for `Spec.map ψ` is precisely formal smoothness of `ψ`. -/
@[ega "0 19.0.1" "affine case"]
theorem formallySmooth_specMap_iff {R A : CommRingCat.{u}} (ψ : R ⟶ A) :
    FormallySmooth (Spec.map ψ) ↔ ψ.hom.FormallySmooth :=
  ⟨formallySmooth_ringHom_of_formallySmooth, formallySmooth_specMap⟩

/-- The ring dictionary for an arbitrary morphism of affine schemes, read on global sections. -/
theorem formallySmooth_iff_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [IsAffine S] :
    FormallySmooth f ↔ (f.appTop).hom.FormallySmooth :=
  ⟨fun hf => (formallySmooth_specMap_iff _).mp
      (hf.of_iso X.isoSpec S.isoSpec (Scheme.isoSpec_hom_naturality f).symm),
    fun hf => (formallySmooth_specMap hf).of_iso X.isoSpec.symm S.isoSpec.symm
      (Scheme.isoSpec_inv_naturality f)⟩

/-- **Stacks Project, Tag 02H6** for a morphism of affine schemes: it is smooth if and only if it
is formally smooth and locally of finite presentation. -/
@[ega "IV 17.3.1" "affine source and target",
  sga "1 III 5.5" "special case",
  sga "3 III 2.5" "partial",
  sga "3 XI 1.1" "special case"]
theorem smooth_iff_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [IsAffine S] :
    AlgebraicGeometry.Smooth f ↔ FormallySmooth f ∧ LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.Smooth),
    HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation),
    formallySmooth_iff_of_isAffine, RingHom.smooth_def]

/-- **Stacks Project, Tag 02H3.** Formal smoothness passes to the restriction of a morphism to
opens of the source and of the target. The point is that a first-order thickening of affine
schemes is surjective on points, so a lift over the ambient morphism has the same image as the
morphism it extends and therefore factors through the given open of the source. -/
@[stacks 02H3]
theorem FormallySmooth.resLE {X S : Scheme.{u}} {f : X ⟶ S} (hf : FormallySmooth f)
    {U : S.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) : FormallySmooth (f.resLE U V e) := by
  intro R A φ hφ hφ2 g h hcomm
  obtain ⟨g', hg1, hg2⟩ := hf R A φ hφ hφ2 (g ≫ V.ι) (h ≫ U.ι)
    (by rw [Category.assoc, ← Scheme.Hom.resLE_comp_ι f e, ← Category.assoc, hcomm,
      Category.assoc])
  have hran : Set.range g'.base ⊆ Set.range V.ι.base := by
    rintro y ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := specMap_base_surjective hφ hφ2 p
    rw [← Scheme.Hom.comp_apply, hg1, Scheme.Hom.comp_apply]
    exact Set.mem_range_self _
  refine ⟨IsOpenImmersion.lift V.ι g' hran, ?_, ?_⟩
  · rw [← cancel_mono V.ι, Category.assoc, IsOpenImmersion.lift_fac, hg1]
  · rw [← cancel_mono U.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      IsOpenImmersion.lift_fac, hg2]

/-- **The hard direction of Stacks Project, Tag 02H6.** A formally smooth morphism that is
locally of finite presentation is smooth. Smoothness is Zariski-local at source and target, and
on a pair of affine opens the ring dictionary applies. -/
theorem smooth_of_formallySmooth {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (hf : FormallySmooth f) : AlgebraicGeometry.Smooth f := by
  have hsrc : IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have htgt : IsZariskiLocalAtTarget (@AlgebraicGeometry.Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  have hres : MorphismProperty.RespectsRight (@AlgebraicGeometry.Smooth.{u}) @IsOpenImmersion :=
    MorphismProperty.Respects.toRespectsRight
  have hsrc' : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have htgt' : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  refine IsZariskiLocalAtSource.iff_exists_resLE.mpr fun x => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, e⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have hUa : IsAffine _ := hU
  have hVa : IsAffine _ := hV
  exact ⟨U, V, hxV, e, (smooth_iff_of_isAffine _).mpr
    ⟨hf.resLE e, IsZariskiLocalAtSource.resLE _ inferInstance⟩⟩

/-- **The easy direction of Stacks Project, Tag 02H6, for an affine morphism.** A smooth affine
morphism is formally smooth: base changing to the affine thickening makes both source and target
affine, where the ring dictionary applies, and a section of the base change is the same thing as
a lift. -/
theorem formallySmooth_of_isAffineHom {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.Smooth f] [IsAffineHom f] : FormallySmooth f := by
  intro R A φ hφ hφ2 g h hcomm
  have hsnd : FormallySmooth (pullback.snd f h) :=
    ((smooth_iff_of_isAffine _).mp inferInstance).1
  obtain ⟨k, hk1, hk2⟩ :=
    hsnd R A φ hφ hφ2 (pullback.lift g (Spec.map φ) hcomm) (𝟙 _)
      (by rw [Category.comp_id, pullback.lift_snd])
  refine ⟨k ≫ pullback.fst f h, ?_, ?_⟩
  · rw [← Category.assoc, hk1, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hk2, Category.id_comp]

/-- **Stacks Project, Tag 02H6** for an affine morphism: it is smooth if and only if it is
formally smooth and locally of finite presentation. -/
theorem smooth_iff_of_isAffineHom {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] :
    AlgebraicGeometry.Smooth f ↔ FormallySmooth f ∧ LocallyOfFinitePresentation f :=
  ⟨fun _ => ⟨formallySmooth_of_isAffineHom f, inferInstance⟩,
    fun ⟨hf, _⟩ => smooth_of_formallySmooth f hf⟩

end Stacks.Smooth

end
