module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.MvPolynomial.Basic
public import StacksFrontier.AlgebraicGeometry.FreeIndex.Diagram

/-!
# Every point of a scheme is covered flatly from a non-affine scheme

The covering hypothesis that Descent, Lemma 0GN7 carries on the abstract site of Tag 03OJ asks
that the arrows factoring through an object whose **underlying scheme is affine** cover every
object.  Condition (2) of Tag 03OJ asks instead that every Zariski covering of an object be
refined by a covering family of the site, and says nothing about the underlying schemes of the
objects that do the refining.  This file shows that the two are genuinely different demands, by
producing the refinements out of non-affine schemes:

**inside every open neighbourhood of every point of a quasi-separated scheme there is the image
of a flat, quasi-compact morphism whose source is quasi-compact, quasi-separated and not affine.**

So a site of schemes over `S` all of whose objects have non-affine underlying scheme can still
satisfy condition (2) — refine a Zariski covering `R` of an object by the family of these
morphisms, one through each point, each of which factors through a member of `R` because its image
lies inside one — and conditions (4), (3) and the full-subcategory half of (1) place no obstruction
either.  Together with
`Stacks.Sites.not_coverByImage_isAffine_of_forall_not_isAffine`, which refutes the covering
hypothesis on any such site, this is why that hypothesis does not follow from the conditions of
Tag 03OJ.

## The covering scheme

The non-affine cover is the **punctured plane** `Stacks.Refute09ZM.punctured A` over the ring of
functions of an affine open: it is quasi-compact, quasi-separated and not affine over any nonzero
ring (`StacksFrontier.AlgebraicGeometry.FreeIndex.Punctured`), and this file adds its structure
morphism over the base and the three properties of that morphism which the fpqc precoverage asks
of a covering family — flatness, quasi-compactness and surjectivity.

Surjectivity is got from a **section** and not from faithful flatness: the `A`-algebra map
`A[x, y] → A` sending both coordinates to `1` lands in the coordinate standard open `D(x)`, hence
in the punctured plane, and is a right inverse of the structure morphism.  That is cheaper than
faithful flatness and needs nothing about `A`.

## Main definitions

* `Stacks.Refute09ZM.puncturedBase`: the structure morphism `punctured A ⟶ Spec A`.
* `Stacks.Refute09ZM.planeUnitSection` and `Stacks.Refute09ZM.puncturedUnitSection`: the section
  at `x = y = 1`, of the affine plane and of the punctured plane.

## Main results

* `Stacks.Refute09ZM.flat_puncturedBase`, `Stacks.Refute09ZM.quasiCompact_puncturedBase` and
  `Stacks.Refute09ZM.surjective_puncturedBase`: **the punctured plane is a flat, quasi-compact,
  surjective cover of its base** — an fpqc covering of `Spec A` by a scheme that is not affine.
* `AlgebraicGeometry.exists_nonaffine_flat_quasiCompact_cover`: **inside every open neighbourhood
  of every point of a quasi-separated scheme there is the image of a flat, quasi-compact morphism
  from a non-affine, quasi-compact, quasi-separated scheme.**

## Implementation notes

No `@[stacks]` attribute is claimed: nothing here is an assertion of the source.  Tag 022B is the
definition of an fpqc covering and Tag 01IL the punctured plane; both are registered where they
are proved.

The quasi-separatedness hypothesis on the target is what makes quasi-compactness of the morphism
free, through `AlgebraicGeometry.quasiCompact_of_compactSpace`, whose hypotheses are a compact
source and a quasi-separated target — not an affine target, as one might expect.  It is harmless
for the application: the objects of a site refuting the covering hypothesis may be taken
quasi-separated, the punctured plane being quasi-separated itself, so the condition propagates
through the refinement.

`Stacks.Refute09ZM.puncturedBase` is built from `Stacks.Refute09ZM.specPlaneBase`, which already
existed for the limit diagram of Tag 09ZM; only the restriction to the punctured open and the
three morphism properties are new.

## References

* [Stacks Project, Tag 01IL](https://stacks.math.columbia.edu/tag/01IL)
* [Stacks Project, Tag 022B](https://stacks.math.columbia.edu/tag/022B)
* [Stacks Project, Tag 03OJ](https://stacks.math.columbia.edu/tag/03OJ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Refute09ZM

variable (A : Type u) [CommRing A]

/-- **The structure morphism of the punctured plane over its base ring.**  The open immersion of
the punctured open into the affine plane, followed by the structure morphism of the plane. -/
public def puncturedBase : punctured A ⟶ Spec (CommRingCat.of A) :=
  (puncturedOpen A).ι ≫ specPlaneBase A

/-- **The punctured plane is flat over its base.**  The polynomial ring is free, hence flat, over
the base ring, and the punctured open is an open immersion into the plane. -/
public instance flat_puncturedBase : Flat (puncturedBase A) := by
  have hbase : Flat (specPlaneBase A) := by
    rw [specPlaneBase, Flat.SpecMap_iff, CommRingCat.hom_ofHom, ← MvPolynomial.algebraMap_eq]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  unfold puncturedBase
  infer_instance

/-- **The punctured plane is quasi-compact over its base.**  Its underlying space is compact and
the base is affine, hence quasi-separated. -/
public instance quasiCompact_puncturedBase : QuasiCompact (puncturedBase A) :=
  quasiCompact_of_compactSpace _

/-- The section of the affine plane over its base at `x = y = 1`. -/
public def planeUnitSection : Spec (CommRingCat.of A) ⟶ affinePlane A :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.eval (fun _ : Fin 2 => (1 : A))))

/-- The section at `x = y = 1` is a right inverse of the structure morphism of the plane: the
composite ring map fixes the base, by `MvPolynomial.eval_C`. -/
public theorem planeUnitSection_comp_specPlaneBase :
    planeUnitSection A ≫ specPlaneBase A = 𝟙 (Spec (CommRingCat.of A)) := by
  rw [planeUnitSection, specPlaneBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show (MvPolynomial.eval (fun _ : Fin 2 => (1 : A))).comp
        (MvPolynomial.C (σ := Fin 2) (R := A)) = RingHom.id A from
      RingHom.ext fun a => by simp, CommRingCat.ofHom_id, Spec.map_id]

/-- **The section at `x = y = 1` lands in the first coordinate standard open**: the first
coordinate is carried to `1`, whose standard open is everything. -/
public theorem preimage_coordOpen_planeUnitSection :
    planeUnitSection A ⁻¹ᵁ coordOpen A 0 = ⊤ :=
  (PrimeSpectrum.comap_basicOpen _ (MvPolynomial.X (0 : Fin 2))).trans (by
    rw [CommRingCat.hom_ofHom]
    simp only [MvPolynomial.eval_X]
    exact PrimeSpectrum.basicOpen_one)

/-- The section at `x = y = 1` lands in the punctured plane. -/
public theorem range_planeUnitSection_subset :
    Set.range (planeUnitSection A).base ⊆ (puncturedOpen A : Set (affinePlane A)) := by
  rintro z ⟨w, rfl⟩
  have hw : w ∈ planeUnitSection A ⁻¹ᵁ coordOpen A 0 := by
    rw [preimage_coordOpen_planeUnitSection]; trivial
  rw [puncturedOpen, Opens.coe_sup]
  exact Or.inl hw

/-- The section of the punctured plane over its base at `x = y = 1`. -/
public def puncturedUnitSection : Spec (CommRingCat.of A) ⟶ punctured A :=
  IsOpenImmersion.lift (puncturedOpen A).ι (planeUnitSection A)
    (by rw [Scheme.Opens.range_ι]; exact range_planeUnitSection_subset A)

/-- The section at `x = y = 1` is a right inverse of the structure morphism of the punctured
plane. -/
public theorem puncturedUnitSection_comp_puncturedBase :
    puncturedUnitSection A ≫ puncturedBase A = 𝟙 (Spec (CommRingCat.of A)) := by
  rw [puncturedBase, ← Category.assoc, puncturedUnitSection, IsOpenImmersion.lift_fac,
    planeUnitSection_comp_specPlaneBase]

/-- **The punctured plane is surjective over its base**, having a section. -/
public instance surjective_puncturedBase : Surjective (puncturedBase A) := by
  have : Surjective (puncturedUnitSection A ≫ puncturedBase A) := by
    rw [puncturedUnitSection_comp_puncturedBase]; infer_instance
  exact Surjective.of_comp (puncturedUnitSection A) (puncturedBase A)

end Stacks.Refute09ZM

namespace AlgebraicGeometry

/-- **Inside every open neighbourhood of every point of a quasi-separated scheme there is the
image of a flat, quasi-compact morphism whose source is quasi-compact, quasi-separated and not
affine.**

Take an affine open `W` with `x ∈ W ⊆ U`.  Its ring of functions is nonzero, `W` having a point,
so the punctured plane over that ring is not affine
(`Stacks.Refute09ZM.not_isAffine_punctured`); its structure morphism is flat, quasi-compact and
surjective onto `Spec Γ(X, W)`, and `AlgebraicGeometry.IsAffineOpen.fromSpec` identifies the image
of the latter in `X` with `W`.

This is condition (2) of Tag 03OJ realized by objects which are **not** affine, and so the reason
that condition does not supply the covering hypothesis of Descent, Lemma 0GN7 at the affine
objects. -/
public theorem exists_nonaffine_flat_quasiCompact_cover {X : Scheme.{u}}
    [QuasiSeparatedSpace X] {x : X} {U : X.Opens} (hxU : x ∈ U) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X), ¬ IsAffine Z ∧ CompactSpace Z ∧
      QuasiSeparatedSpace Z ∧ Flat f ∧ QuasiCompact f ∧
      x ∈ Set.range f.base ∧ Set.range f.base ⊆ (U : Set X) := by
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hxU
  have hnt : Nontrivial Γ(X, W) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨hW.isoSpec.hom.base ⟨x, hxW⟩⟩
  have hrange : Set.range (Stacks.Refute09ZM.puncturedBase Γ(X, W) ≫ hW.fromSpec).base
      = (W : Set X) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      (Stacks.Refute09ZM.puncturedBase Γ(X, W)).surjective.range_eq, Set.image_univ,
      hW.range_fromSpec]
  refine ⟨Stacks.Refute09ZM.punctured Γ(X, W),
    Stacks.Refute09ZM.puncturedBase Γ(X, W) ≫ hW.fromSpec,
    Stacks.Refute09ZM.not_isAffine_punctured _, inferInstance, inferInstance, inferInstance,
    quasiCompact_of_compactSpace _, ?_, ?_⟩
  · rw [hrange]; exact hxW
  · rw [hrange]; exact hWU

end AlgebraicGeometry

end
