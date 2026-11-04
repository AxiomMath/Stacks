module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiGluing

/-!
# The fpqc prestack condition is Zariski-local on the base

The descent of morphisms for the fpqc topology — `CategoryTheory.Pseudofunctor.IsPrestack` at
`AlgebraicGeometry.Scheme.fpqcTopology` — is a condition at *every* scheme.  This file shows that
for a pseudofunctor which is already a prestack for the **Zariski** topology it is enough to
check it over **affine** bases.

This is the prestack analogue of Stacks 022H, which says that a presheaf on the category of
schemes is a sheaf for a quasi-compact topology as soon as it is a Zariski sheaf and satisfies
the sheaf condition for a single flat surjective morphism of affine schemes
(`AlgebraicGeometry.isSheaf_type_propQCTopology_iff`).  That statement cannot be applied here:
the presheaf whose sheaf condition *is* the prestack condition,
`CategoryTheory.Pseudofunctor.presheafHom`, lives on the slice category `Over S`, not on the
category of schemes.  What is used instead is the slice-category instance of the general locality
principle `CategoryTheory.GrothendieckTopology.OneHypercover.isSheafFor_sieve_of_pullback`, fed
with the Zariski `1`-hypercover by affine opens of Mathlib's
`AlgebraicGeometry.Scheme.affineOneHypercover`, lifted from the category of schemes to the slice
category.

## Main definitions

* `CategoryTheory.PreOneHypercover.over` and
  `CategoryTheory.GrothendieckTopology.OneHypercover.over`: a `1`-hypercover of `T.left` for `J`
  read as a `1`-hypercover of `T : Over X` for the induced topology `J.over X`.  Both index types
  and all the morphisms are unchanged; only the structure morphisms to `X` are added.

## Main results

* `CategoryTheory.Pseudofunctor.isPrestackFor_of_isAffine`: for a pseudofunctor which is a
  prestack for the Zariski topology, the descent of morphisms along an fpqc covering family of an
  arbitrary scheme follows from the descent of morphisms along the fpqc covering families of
  affine schemes.
* `CategoryTheory.Pseudofunctor.isPrestack_fpqcTopology_of_isAffine`: consequently such a
  pseudofunctor is a prestack for the fpqc topology as soon as it is one over affine bases.
* `Stacks.Descent.isPrestack_qcohPseudofunctor_fpqc_of_isAffine`: the case of quasi-coherent
  modules, where the Zariski hypothesis is discharged by
  `Stacks.Descent.isPrestack_qcohPseudofunctor`.  The only remaining hypothesis is the descent of
  morphisms of quasi-coherent modules along the fpqc covering families of *affine* schemes, which
  is the full faithfulness half of Stacks 023S.
* `Stacks.Descent.isPrestack_qcohPseudofunctor_of_isPrestackFor`: the same conclusion from the
  descent of morphisms along the fpqc covering families of *every* scheme, with no affineness
  reduction; this is `CategoryTheory.Pseudofunctor.IsPrestack.of_precoverage` instantiated.

## What this leaves open

The hypothesis `haff` of `Stacks.Descent.isPrestack_qcohPseudofunctor_fpqc_of_isAffine` is the
descent of morphisms along *every* fpqc covering presieve of an affine scheme; by
`CategoryTheory.Pseudofunctor.isPrestackFor_ofArrows_iff` it says that
`CategoryTheory.Pseudofunctor.toDescentData` of `Stacks.Descent.qcohPseudofunctor` is fully
faithful for every fpqc covering family of an affine scheme.  Two things are left to do.

First, **fullness for a standard family over an affine base**, the missing half of Stacks 023S:
by the product trick of `Stacks.Descent.familyPullFunctor` it comes down to a single faithfully
flat ring map `R ⟶ B`, where it says that a `B`-linear morphism `M ⊗ B ⟶ N ⊗ B` whose two base
changes to `B ⊗[R] B` agree is the base change of an `R`-linear morphism `M ⟶ N` — the left
exactness of `Hom_R(M, -)` applied to the Amitsur complex of `R ⟶ B`, whose exactness is
`Stacks.Descent.amitsurExtendedCochainComplex_acyclic_of_faithfullyFlat` (Stacks 023M).  The
faithfulness half for a standard family *is* proved, as
`Stacks.Descent.faithful_qcohToDescentData_of_mem_fpqcPrecoverage` in
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/StandardAffineSeparated.lean`.

Second, the passage from a **standard** family to an arbitrary fpqc covering presieve of an
affine scheme.  Stacks 022E
(`AlgebraicGeometry.exists_affineCover_flat_sieve_le_of_mem_fpqcPrecoverage`) refines the given
presieve by a standard family, so the passage is a refinement *upwards*, from the finer family to
the coarser one.  Mathlib's
`CategoryTheory.Pseudofunctor.DescentData.fullyFaithfulPullFunctor` does that but carries
`[F.IsPrestack J]`, which here is the conclusion, so it must not be used; the usable form is
`CategoryTheory.Pseudofunctor.DescentData.nonempty_fullyFaithful_pullFunctor` in
`StacksFrontier/CategoryTheory/Sites/Descent/OfRefinement.lean`, whose hypotheses are local: the
descent of morphisms along the pullback of the refining sieve to each member of the coarse
family, and its separatedness at the chosen fibre products.  Those members are *not* affine, so
that step consumes a general-base statement — the separatedness half of what this file reduces,
which the same `1`-hypercover locality argument would supply from the affine
faithfulness.

## Implementation notes

The reduction is run through `CategoryTheory.Pseudofunctor.IsPrestack.of_precoverage`, so only
the presieves of `AlgebraicGeometry.Scheme.fpqcPrecoverage` have to be treated, and through
`CategoryTheory.Pseudofunctor.isPrestackFor_iff_isSheafFor`, which turns the descent of morphisms
along a family on `S` into the sheaf condition for
`CategoryTheory.Pseudofunctor.presheafHom` at the object `Over.mk (𝟙 S)` of `Over S`.  The
hypotheses of the locality principle are then the same sheaf condition at the objects
`Over.mk (V ⟶ S)` for `V` an affine open of `S`, and at the affine opens of the intersections of
two of those; that is where the affine hypothesis is consumed, after a base change of the family,
which stays fpqc by `CategoryTheory.Precoverage.pullbackArrows_mem`.

Nothing here assumes the fpqc prestack condition being reduced, nor any form of effective
descent: the only descent input is the Zariski prestack condition, which for quasi-coherent
modules is the gluing of morphisms of Sheaves, Section 00AK, proved in
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/ZariskiGluing.lean`.

The affineness of the components of `AlgebraicGeometry.Scheme.affineOneHypercover` is supplied as
`inferInstanceAs (IsAffine (Spec _))` rather than by `inferInstance`: the components are
definitionally spectra, but instance search does not unfold the `1`-hypercover to see it.  For
the same reason the affineness is an explicit argument of
`CategoryTheory.Pseudofunctor.isSheafFor_presheafHom_pullback_of_isAffine` and not an instance
argument.

## References

* [Stacks Project, Tag 022H](https://stacks.math.columbia.edu/tag/022H)
* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

universe w v' u' v u

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C]

namespace PreOneHypercover

/-- A pre-`1`-hypercover of `T.left` read as a pre-`1`-hypercover of `T : Over X`: the components
are the components of the given one equipped with their composite structure morphisms to `X`, and
all the index types and all the morphisms are unchanged. -/
def over {X : C} (T : Over X) (E : PreOneHypercover.{w} T.left) : PreOneHypercover.{w} T where
  I₀ := E.I₀
  X i := Over.mk (E.f i ≫ T.hom)
  f i := Over.homMk (E.f i)
  I₁ := E.I₁
  Y _ _ j := Over.mk (E.p₁ j ≫ E.f _ ≫ T.hom)
  p₁ _ _ j := Over.homMk (E.p₁ j)
  p₂ _ _ j := Over.homMk (E.p₂ j) (by simpa using (E.w j =≫ T.hom).symm)
  w _ _ j := by
    ext
    exact E.w j

variable {X : C} (T : Over X) (E : PreOneHypercover.{w} T.left)

/-- The sieve generated by the `0`-components of `CategoryTheory.PreOneHypercover.over` is the
one generated by the `0`-components of the given pre-`1`-hypercover. -/
lemma overEquiv_over_sieve₀ : Sieve.overEquiv T (over T E).sieve₀ = E.sieve₀ := by
  rw [Sieve.overEquiv_ofArrows]; rfl

/-- The sieves on the overlaps of `CategoryTheory.PreOneHypercover.over` are the sieves on the
overlaps of the given pre-`1`-hypercover. -/
lemma overEquiv_over_sieve₁ {i₁ i₂ : (over T E).I₀} {W : Over X}
    (p₁ : W ⟶ (over T E).X i₁) (p₂ : W ⟶ (over T E).X i₂) :
    Sieve.overEquiv W ((over T E).sieve₁ p₁ p₂) = E.sieve₁ p₁.left p₂.left := by
  rw [Sieve.overEquiv_preOneHypercover_sieve₁]; rfl

end PreOneHypercover

namespace GrothendieckTopology.OneHypercover

/-- A `1`-hypercover of `T.left` for `J` read as a `1`-hypercover of `T : Over X` for the induced
topology `J.over X`. -/
def over (J : GrothendieckTopology C) {X : C} (T : Over X) (E : J.OneHypercover.{w} T.left) :
    (J.over X).OneHypercover.{w} T where
  toPreOneHypercover := .over T E.toPreOneHypercover
  mem₀ := by
    rw [GrothendieckTopology.mem_over_iff, PreOneHypercover.overEquiv_over_sieve₀]
    exact E.mem₀
  mem₁ i₁ i₂ W p₁ p₂ w := by
    rw [GrothendieckTopology.mem_over_iff, PreOneHypercover.overEquiv_over_sieve₁]
    exact E.mem₁ i₁ i₂ p₁.left p₂.left (congrArg Over.Hom.left w)

end GrothendieckTopology.OneHypercover

namespace Pseudofunctor

open AlgebraicGeometry

variable {F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{v', u'}}

/-- The sheaf condition for `CategoryTheory.Pseudofunctor.presheafHom` along the base change of an
fpqc covering presieve to an object of `Over S` with affine source, from the descent of morphisms
along the fpqc covering presieves of affine schemes.  This is the hypothesis of
`CategoryTheory.GrothendieckTopology.OneHypercover.isSheafFor_sieve_of_pullback` at both the
`0`-components and the `1`-components of the affine Zariski `1`-hypercover. -/
theorem isSheafFor_presheafHom_pullback_of_isAffine
    (haff : ∀ (T : Scheme.{u}), IsAffine T → ∀ (R : Presieve T),
      R ∈ Scheme.fpqcPrecoverage.{u} T → F.IsPrestackFor R)
    {S : Scheme.{u}} {T U : Over S} {R : Presieve U.left}
    (hR : R ∈ Scheme.fpqcPrecoverage.{u} U.left)
    (M N : F.obj (.mk (op S))) (q : T ⟶ U) (hT : IsAffine T.left) :
    Presieve.IsSheafFor (F.presheafHom M N)
      (Sieve.pullback q ((Sieve.overEquiv U).symm (Sieve.generate R))).arrows := by
  rw [← Sieve.overEquiv_symm_pullback]
  refine IsPrestackFor.isSheafFor' T ?_ M N
  rw [OrderIso.apply_symm_apply, ← Sieve.pullbackArrows_comm, IsPrestackFor_generate_iff]
  exact haff T.left hT _ (Precoverage.pullbackArrows_mem q.left hR)

/-- **The descent of morphisms along an fpqc covering family is Zariski-local on the base.**  For
a pseudofunctor which is a prestack for the Zariski topology, the descent of morphisms along the
fpqc covering presieves of affine schemes implies the descent of morphisms along the fpqc
covering presieves of every scheme.

The locality is Mathlib's
`CategoryTheory.GrothendieckTopology.OneHypercover.isSheafFor_sieve_of_pullback`, applied in the
slice category `Over S` to the affine Zariski `1`-hypercover of `S`. -/
theorem isPrestackFor_of_isAffine [F.IsPrestack Scheme.zariskiTopology.{u}]
    (haff : ∀ (T : Scheme.{u}), IsAffine T → ∀ (R : Presieve T),
      R ∈ Scheme.fpqcPrecoverage.{u} T → F.IsPrestackFor R)
    {S : Scheme.{u}} (R : Presieve S) (hR : R ∈ Scheme.fpqcPrecoverage.{u} S) :
    F.IsPrestackFor R := by
  rw [← IsPrestackFor_generate_iff, isPrestackFor_iff_isSheafFor]
  intro M N
  have hsh : Presieve.IsSheaf (Scheme.zariskiTopology.{u}.over S) (F.presheafHom M N) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact IsPrestack.isSheaf _ M N
  exact (GrothendieckTopology.OneHypercover.over Scheme.zariskiTopology.{u} (Over.mk (𝟙 S))
    (Scheme.affineOneHypercover S)).isSheafFor_sieve_of_pullback hsh
      (fun _ ↦ isSheafFor_presheafHom_pullback_of_isAffine haff hR M N _
        (inferInstanceAs (IsAffine (Spec _))))
      (fun _ _ _ ↦ (isSheafFor_presheafHom_pullback_of_isAffine haff hR M N _
        (inferInstanceAs (IsAffine (Spec _)))).isSeparatedFor)

/-- **The fpqc prestack condition reduced to affine bases.**  A pseudofunctor on the category of
schemes which is a prestack for the Zariski topology is a prestack for the fpqc topology as soon
as the descent of morphisms holds along the fpqc covering presieves of affine schemes. -/
theorem isPrestack_fpqcTopology_of_isAffine [F.IsPrestack Scheme.zariskiTopology.{u}]
    (haff : ∀ (T : Scheme.{u}), IsAffine T → ∀ (R : Presieve T),
      R ∈ Scheme.fpqcPrecoverage.{u} T → F.IsPrestackFor R) :
    F.IsPrestack Scheme.fpqcTopology.{u} :=
  IsPrestack.of_precoverage (J := Scheme.fpqcPrecoverage.{u})
    fun _ R hR ↦ isPrestackFor_of_isAffine haff R hR

end Pseudofunctor

end CategoryTheory

namespace Stacks.Descent

open _root_.AlgebraicGeometry CategoryTheory Opposite

/-- **The fpqc prestack condition for quasi-coherent modules, reduced to affine bases.**  Granting
the descent of morphisms of quasi-coherent modules along the fpqc covering presieves of affine
schemes, quasi-coherent modules form a prestack for the fpqc topology.  See the section "What
this leaves open" of the module documentation for what the hypothesis still costs.

The Zariski prestack condition, the other input of
`CategoryTheory.Pseudofunctor.isPrestack_fpqcTopology_of_isAffine`, is
`Stacks.Descent.isPrestack_qcohPseudofunctor`.  This reduces the standing hypothesis
`qcohPseudofunctor.IsPrestack AlgebraicGeometry.Scheme.fpqcTopology` of
`Stacks.Descent.isStackFor_qcohPseudofunctor_of_isAffine` and of
`Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_of_isPrestack` to that one affine
statement. -/
theorem isPrestack_qcohPseudofunctor_fpqc_of_isAffine
    (haff : ∀ (T : Scheme.{u}), IsAffine T → ∀ (R : Presieve T),
      R ∈ Scheme.fpqcPrecoverage.{u} T → qcohPseudofunctor.{u}.IsPrestackFor R) :
    qcohPseudofunctor.{u}.IsPrestack Scheme.fpqcTopology.{u} :=
  Pseudofunctor.isPrestack_fpqcTopology_of_isAffine haff

/-- **The fpqc prestack condition reduced from covering sieves to covering families.**  The fpqc
precoverage has isomorphisms and is stable under base change and composition, so by
`CategoryTheory.Pseudofunctor.IsPrestack.of_precoverage` it suffices to check the descent of
morphisms for the presieves that are themselves fpqc covering families. -/
theorem isPrestack_qcohPseudofunctor_of_isPrestackFor
    (h : ∀ (T : Scheme.{u}) (R : Presieve T), R ∈ Scheme.fpqcPrecoverage.{u} T →
      qcohPseudofunctor.{u}.IsPrestackFor R) :
    qcohPseudofunctor.{u}.IsPrestack Scheme.fpqcTopology.{u} :=
  Pseudofunctor.IsPrestack.of_precoverage (J := Scheme.fpqcPrecoverage.{u}) h

end Stacks.Descent

end
