module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.StructureSections
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Faithful flatness of the global functions along an fppf covering of affines

Descent along a covering of a site computes the sections of a sheaf of modules over the base from
the sections over the members of the covering together with the gluing data, and over affine
objects of an fppf site that computation is the Amitsur complex of a ring map.  The ring map is
the one the covering induces on global functions, and the Amitsur complex computes with it
because it is *faithfully flat*: that is the single ring-theoretic input the whole descent
argument rests on, and it is what this file supplies.

Two shapes of covering are treated, and the second is the one a covering family has.  For a
single covering morphism the ring map is the one it induces on global functions.  For a family,
no member need be surjective, so no member's ring map is faithfully flat on its own; what is
faithfully flat is the *product* of the rings of global functions on the members, and it is so
because the family is jointly surjective.  That product is what the separatedness half of the
sheaf condition for a family runs through.

The single-morphism input is produced in three forms, of increasing distance from the ring
theory.  For one morphism of affine schemes which is flat and surjective, the map of global
functions is a faithfully flat ring map; this is Mathlib's
`AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine` read in one
direction, packaged here together with the transport which turns it into the
`Module.FaithfullyFlat` instance an Amitsur complex is stated for.  For a one-element covering
family of the fppf precoverage of schemes, flatness and surjectivity are exactly what membership
unfolds to, so the same conclusion is available from the covering alone.  And for a standard fppf
covering of an affine scheme by finitely many affine schemes, the morphism out of the coproduct of
the family is a single flat surjective morphism of affine schemes, so the ring of functions on the
disjoint union of the family is faithfully flat over the ring of functions on the base.

The same statements are then given for a slice of the fppf site associated with a category fibred
in groupoids over a big fppf category of schemes, which is where a sheaf of modules whose sections
are to be computed lives.  There the ring of sections of the coefficient sheaf of rings at an
object *is* the ring of global functions on the underlying scheme, and the restriction map along a
morphism *is* the induced map of global functions, both definitionally; the second of those is
recorded as a named equation, since definitional equations are neither rewritable nor visible to
instance search.

## Main results

* `AlgebraicGeometry.faithfullyFlat_appTop_of_flat_of_surjective`: **the map of global functions
  along a flat surjective morphism of affine schemes is a faithfully flat ring map.**
* `AlgebraicGeometry.faithfullyFlat_gamma_of_flat_of_surjective` and
  `AlgebraicGeometry.faithfullyFlat_of_ringEquiv_gamma`: **the same as the statement
  `Module.FaithfullyFlat` which faithfully flat descent of modules is phrased with**, for the
  rings of global functions themselves and for rings identified with them by a ring equivalence.
* `AlgebraicGeometry.flat_and_surjective_of_singleton_mem_fppfPrecoverage`: **a morphism of
  schemes whose one-element family is an fppf covering is flat, surjective and locally of finite
  presentation**, the converse direction of
  `AlgebraicGeometry.Scheme.Hom.singleton_mem_fppfPrecoverage`.
* `AlgebraicGeometry.faithfullyFlat_appTop_of_singleton_mem_fppfPrecoverage` and
  `AlgebraicGeometry.faithfullyFlat_gamma_of_singleton_mem_fppfPrecoverage`: **the ring of global
  functions on the source of a one-element fppf covering of an affine scheme by an affine scheme
  is faithfully flat over the ring of global functions on the target.**
* `AlgebraicGeometry.IsStandardFppfCovering.faithfullyFlat_appTop_sigmaDesc` and
  `AlgebraicGeometry.IsStandardFppfCovering.faithfullyFlat_gamma_sigmaDesc`: **the ring of global
  functions on the coproduct of a standard fppf covering is faithfully flat over the ring of
  global functions on the base.**
* `AlgebraicGeometry.faithfullyFlat_pi_of_exists_comap_eq`: **a finite product of flat algebras is
  faithfully flat as soon as every prime of the base lies under a prime of one of the factors.**
* `AlgebraicGeometry.exists_comap_appTop_eq_of_iUnion_range_eq_univ`: every prime of the ring of
  global functions on an affine scheme lies under a prime of the ring of global functions on a
  member of a jointly surjective family of morphisms from affine schemes.
* `AlgebraicGeometry.faithfullyFlat_pi_gamma_of_iUnion_range_eq_univ` and
  `AlgebraicGeometry.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage`: **the product of the
  rings of global functions on the members of a finite fppf covering family of an affine scheme by
  affine schemes is faithfully flat over the ring of global functions on the target.**
* `AlgebraicGeometry.FibredSite.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage`: the same
  for a finite fppf covering family of affine objects of a slice of an associated fppf site, which
  is the form `AlgebraicGeometry.FibredSite.exists_finite_affine_fppf_ofArrows_le_over` produces.
* `AlgebraicGeometry.BigFppfSite.flat_and_surjective_of_singleton_mem_precoverage`: a morphism of
  a big fppf category of schemes whose one-element family is a selected covering family has flat,
  surjective and locally finitely presented image in schemes.
* `AlgebraicGeometry.BigFppfSite.faithfullyFlat_appTop_of_singleton_mem_precoverage`: and the
  induced map of global functions is faithfully flat when both schemes are affine.
* `AlgebraicGeometry.FibredSite.ringStructureSheafCore_over_map`: the restriction map of the
  coefficient sheaf of rings of a slice of an associated site along a morphism is the map of
  global functions along the underlying morphism of schemes.
* `AlgebraicGeometry.FibredSite.faithfullyFlat_gamma_of_flat_of_surjective`: **the global
  functions on the scheme underlying an affine object of a slice of an associated fppf site are
  faithfully flat over the global functions on the scheme underlying another affine object, along
  a morphism whose underlying morphism of schemes is flat and surjective.**  For a consumer whose
  rings are the rings of sections of the coefficient sheaf of rings rather than rings of global
  functions, `AlgebraicGeometry.faithfullyFlat_of_ringEquiv_gamma` composed with
  `AlgebraicGeometry.FibredSite.sectionRingEquivGamma` is the same statement.

## Implementation notes

The algebra structure relating the two rings of global functions is an instance *argument*
together with an equation identifying its `algebraMap` with the map of global functions, rather
than being built here.  A consumer arrives carrying its own algebra structure, and often a scalar
tower stated for it; a second structure minted here would not be the one the tower is stated for.
The equation is discharged by `rfl` whenever the consumer's structure is the induced one.

`AlgebraicGeometry.faithfullyFlat_of_ringEquiv_gamma` is the form for a consumer whose two
commutative rings are not literally the rings of global functions but are identified with them —
for the slices of an associated fppf site the identification is
`AlgebraicGeometry.FibredSite.sectionRingEquivGamma` and is the identity, but a statement should
not have to know that.

The index type of a standard fppf covering is required to be small relative to the universe of
the schemes, so that the coproduct of the family exists.  This is implied by the finiteness which
is part of being a standard fppf covering, but it has to be an instance argument of the statement:
the coproduct occurs in the statement itself, before the hypothesis is available.

Nothing here needs the structure functor of the fibred category to be fibred in groupoids, and
nothing needs the covering to be locally of finite presentation: faithful flatness of a map of
affine schemes is flatness and surjectivity alone, and finite presentation is carried along only
because membership in the fppf precoverage supplies it.

The index type of a covering family is free of the universe of the schemes throughout, so a
consumer indexing a family by something of its own is not obliged to lift it; and the two
universes of the fibred category are free of the universe of the schemes as well.  The exceptions
are the statements naming a ring identified with a ring of global functions, where the universe of
that ring is the universe of the schemes: the global functions on a scheme in `Scheme.{u}` live in
`Type u`, and a ring equivalence onto them forces its source there.  In
`AlgebraicGeometry.faithfullyFlat_pi_of_exists_comap_eq`, which names no scheme, the base ring,
the index type and the factors live at three independent universes.

## References

* [Stacks Project, Tag 0238](https://stacks.math.columbia.edu/tag/0238)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' w v u

namespace AlgebraicGeometry

section OneMorphism

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- An algebra whose structure map is a faithfully flat ring map is faithfully flat. -/
private theorem faithfullyFlat_of_algebraMap_eq {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] {φ : A →+* B} (halg : algebraMap A B = φ) (hφ : φ.FaithfullyFlat) :
    Module.FaithfullyFlat A B := by
  rw [← RingHom.faithfullyFlat_algebraMap_iff, halg]
  exact hφ

/-- **The map of global functions along a flat surjective morphism of affine schemes is a
faithfully flat ring map.**  A morphism of affine schemes is flat and surjective exactly when the
induced ring map is faithfully flat, by
`AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine`; this is the direction
which turns geometry into ring theory. -/
theorem faithfullyFlat_appTop_of_flat_of_surjective [IsAffine X] [IsAffine Y] [Flat f]
    [Surjective f] : f.appTop.hom.FaithfullyFlat :=
  (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).1 ⟨inferInstance, inferInstance⟩

/-- **Faithful flatness of the global functions along a flat surjective morphism of affine
schemes, as a statement about modules.**  Faithfully flat descent of modules is stated for
`Module.FaithfullyFlat` over an algebra, which is what
`AlgebraicGeometry.faithfullyFlat_appTop_of_flat_of_surjective` becomes once the ring map is
recognised as the structure map of the algebra.

The algebra structure is an instance argument identified with the map of global functions by a
hypothesis, not one built here: a consumer holding the algebra structure as part of a scalar
tower must be given a conclusion about *its* structure. -/
theorem faithfullyFlat_gamma_of_flat_of_surjective [IsAffine X] [IsAffine Y] [Flat f]
    [Surjective f] [Algebra Γ(Y, ⊤) Γ(X, ⊤)]
    (halg : algebraMap Γ(Y, ⊤) Γ(X, ⊤) = f.appTop.hom) :
    Module.FaithfullyFlat Γ(Y, ⊤) Γ(X, ⊤) := by
  exact faithfullyFlat_of_algebraMap_eq halg (faithfullyFlat_appTop_of_flat_of_surjective f)

/-- **Faithful flatness along a flat surjective morphism of affine schemes, for rings identified
with the rings of global functions.**  The two ring equivalences carry the map of global functions
to the structure map of the algebra, and faithful flatness of a ring map is invariant under
pre- and post-composition with ring equivalences
(`RingHom.FaithfullyFlat.respectsIso`).

This is the form to use when the two commutative rings arise as rings of sections of a sheaf of
rings, which are only identified with rings of global functions and are not literally them. -/
theorem faithfullyFlat_of_ringEquiv_gamma {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    [IsAffine X] [IsAffine Y] [Flat f] [Surjective f] (eA : A ≃+* Γ(Y, ⊤)) (eC : C ≃+* Γ(X, ⊤))
    (halg : ∀ a, eC (algebraMap A C a) = f.appTop.hom (eA a)) :
    Module.FaithfullyFlat A C := by
  have hiso := RingHom.FaithfullyFlat.respectsIso
  have h0 : RingHom.FaithfullyFlat f.appTop.hom :=
    faithfullyFlat_appTop_of_flat_of_surjective f
  have h1 : RingHom.FaithfullyFlat
      ((eC.symm : Γ(X, ⊤) →+* C).comp (f.appTop.hom.comp (eA : A →+* Γ(Y, ⊤)))) :=
    hiso.1 _ eC.symm (hiso.2 _ eA h0)
  exact faithfullyFlat_of_algebraMap_eq (RingHom.ext fun a =>
    (eC.symm_apply_apply _).symm.trans (congrArg eC.symm (halg a))) h1

end OneMorphism

section FppfPrecoverage

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **A morphism of schemes whose one-element family is an fppf covering is flat, surjective and
locally of finite presentation.**  The fppf precoverage of schemes consists of the jointly
surjective families of flat morphisms locally of finite presentation, and for a one-element family
joint surjectivity is surjectivity of the single morphism; so this is what membership unfolds to,
by `AlgebraicGeometry.Scheme.singleton_mem_precoverage_iff`.

This is the converse of `AlgebraicGeometry.Scheme.Hom.singleton_mem_fppfPrecoverage`, which
produces an fppf covering from the three properties. -/
theorem flat_and_surjective_of_singleton_mem_fppfPrecoverage
    (hf : Presieve.singleton f ∈ Scheme.fppfPrecoverage Y) :
    Flat f ∧ Surjective f ∧ LocallyOfFinitePresentation f := by
  rw [Scheme.fppfPrecoverage, Scheme.singleton_mem_precoverage_iff] at hf
  exact ⟨hf.2.1, ⟨hf.1⟩, hf.2.2⟩

/-- **The map of global functions along a one-element fppf covering of an affine scheme by an
affine scheme is a faithfully flat ring map.**  The covering is flat and surjective by
`AlgebraicGeometry.flat_and_surjective_of_singleton_mem_fppfPrecoverage`, and
`AlgebraicGeometry.faithfullyFlat_appTop_of_flat_of_surjective` applies. -/
theorem faithfullyFlat_appTop_of_singleton_mem_fppfPrecoverage [IsAffine X] [IsAffine Y]
    (hf : Presieve.singleton f ∈ Scheme.fppfPrecoverage Y) : f.appTop.hom.FaithfullyFlat := by
  obtain ⟨hflat, hsurj, -⟩ := flat_and_surjective_of_singleton_mem_fppfPrecoverage f hf
  exact faithfullyFlat_appTop_of_flat_of_surjective f

/-- **The global functions on the source of a one-element fppf covering of an affine scheme by an
affine scheme are faithfully flat over the global functions on the target**, as a statement about
modules.  This is the ring-theoretic input of faithfully flat descent along a single fppf covering
morphism of affines. -/
@[ega "IV 2.2.3" "M = B"]
theorem faithfullyFlat_gamma_of_singleton_mem_fppfPrecoverage [IsAffine X] [IsAffine Y]
    [Algebra Γ(Y, ⊤) Γ(X, ⊤)] (halg : algebraMap Γ(Y, ⊤) Γ(X, ⊤) = f.appTop.hom)
    (hf : Presieve.singleton f ∈ Scheme.fppfPrecoverage Y) :
    Module.FaithfullyFlat Γ(Y, ⊤) Γ(X, ⊤) := by
  exact faithfullyFlat_of_algebraMap_eq halg
    (faithfullyFlat_appTop_of_singleton_mem_fppfPrecoverage f hf)

end FppfPrecoverage

section FinitePi

/-- **A finite product of flat algebras is faithfully flat as soon as every prime of the base is
the image of a prime of one of the factors.**  A finite product of modules is their direct sum, so
flatness is inherited; and if a maximal ideal generated the whole product then it would generate
each factor, which the prime lying over it in that factor forbids.

This is the form faithful flatness takes for a covering *family*: no single member of a covering
need be surjective, so no single factor need be faithfully flat, and it is the family which
covers.  It reproves, for the `Module.FaithfullyFlat` conclusion, the file-local
`AlgebraicGeometry.faithfullyFlat_pi_of_prime_lifts` of
`StacksFrontier/AlgebraicGeometry/Descent/Modules/FpqcLocallyProjective.lean`, which is `private`
and so unavailable here. -/
@[ega "IV 2.2.6" "special case", sga "3 VIB 11.9.1" "partial"]
theorem faithfullyFlat_pi_of_exists_comap_eq {A : Type*} [CommRing A] {ι : Type*} [Finite ι]
    (Bi : ι → Type*) [∀ i, CommRing (Bi i)] [∀ i, Algebra A (Bi i)]
    (hflat : ∀ i, Module.Flat A (Bi i))
    (hlift : ∀ q : PrimeSpectrum A, ∃ i, ∃ r : PrimeSpectrum (Bi i),
      PrimeSpectrum.comap (algebraMap A (Bi i)) r = q) :
    Module.FaithfullyFlat A (∀ i, Bi i) := by
  classical
  have _ := Fintype.ofFinite ι
  have _ : ∀ i, Module.Flat A (Bi i) := hflat
  rw [Module.faithfullyFlat_iff]
  refine ⟨Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype A ι Bi).symm, ?_⟩
  intro 𝔪 h𝔪 heq
  obtain ⟨i, r, hr⟩ := hlift ⟨𝔪, h𝔪.isPrime⟩
  have hsurj : Function.Surjective (LinearMap.proj i : (∀ j, Bi j) →ₗ[A] Bi i) :=
    fun b => ⟨Function.update 0 i b, by simp⟩
  have hproj : 𝔪 • (⊤ : Submodule A (Bi i)) = ⊤ := by
    have hp : Submodule.map (LinearMap.proj i : (∀ j, Bi j) →ₗ[A] Bi i)
        (𝔪 • (⊤ : Submodule A (∀ j, Bi j))) = 𝔪 • (⊤ : Submodule A (Bi i)) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hsurj]
    rw [heq, Submodule.map_top, LinearMap.range_eq_top.2 hsurj] at hp
    exact hp.symm
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] at hproj
  have hle : 𝔪.map (algebraMap A (Bi i)) ≤ r.asIdeal :=
    Ideal.map_le_iff_le_comap.2 (le_of_eq (congrArg PrimeSpectrum.asIdeal hr).symm)
  rw [hproj, top_le_iff] at hle
  exact r.isPrime.ne_top hle

/-- **Every prime of the ring of global functions on an affine scheme lies under a prime of the
ring of global functions on a member of a jointly surjective family of morphisms from affine
schemes.**  A prime of the ring of global functions is a point of the scheme, the identification
being `AlgebraicGeometry.Scheme.isoSpec`; joint surjectivity produces a point of a member above
it, and `AlgebraicGeometry.Scheme.isoSpec_hom_naturality` says that the prime it names is carried
to the given one by the induced map of global functions. -/
theorem exists_comap_appTop_eq_of_iUnion_range_eq_univ {Z : Scheme.{u}} [IsAffine Z] {ι : Type w}
    {Y : ι → Scheme.{u}} [∀ i, IsAffine (Y i)] (g : ∀ i, Y i ⟶ Z)
    (hsurj : (⋃ i, Set.range (g i)) = Set.univ) (q : PrimeSpectrum Γ(Z, ⊤)) :
    ∃ i, ∃ r : PrimeSpectrum Γ(Y i, ⊤), PrimeSpectrum.comap (g i).appTop.hom r = q := by
  obtain ⟨i, y, hy⟩ := Set.mem_iUnion.1 (hsurj ▸ Set.mem_univ (Z.isoSpec.inv q))
  refine ⟨i, (Y i).isoSpec.hom y, ?_⟩
  have hnat := congrArg (fun t : Y i ⟶ Spec Γ(Z, ⊤) => t y)
    (Scheme.isoSpec_hom_naturality (g i))
  simp only [Scheme.Hom.comp_apply] at hnat
  have hid : Z.isoSpec.hom (Z.isoSpec.inv q) = q := by
    show (Z.isoSpec.inv ≫ Z.isoSpec.hom) q = q
    rw [Z.isoSpec.inv_hom_id]
    rfl
  rw [show PrimeSpectrum.comap (g i).appTop.hom ((Y i).isoSpec.hom y) =
      Spec.map (g i).appTop ((Y i).isoSpec.hom y) from rfl, hnat, hy]
  exact hid

/-- **The product of the rings of global functions on the members of a finite jointly surjective
family of flat morphisms from affine schemes to an affine scheme is faithfully flat over the ring
of global functions on the target.**

This is the form of faithful flatness a covering *family* supplies, and it is what descent along
the family needs: no member of the family is surjective by itself, so no single ring of global
functions is faithfully flat over the base, and the separatedness argument runs through the
product, where a section restricting to zero on every member is zero.

Each factor is flat because its morphism is
(`AlgebraicGeometry.Scheme.Hom.flat_appTop`), and
`AlgebraicGeometry.exists_comap_appTop_eq_of_iUnion_range_eq_univ` discharges the hypothesis of
`AlgebraicGeometry.faithfullyFlat_pi_of_exists_comap_eq` from joint surjectivity.  As everywhere
here the algebra structures are the consumer's own, identified with the maps of global functions
by hypothesis. -/
theorem faithfullyFlat_pi_gamma_of_iUnion_range_eq_univ {Z : Scheme.{u}} [IsAffine Z]
    {ι : Type w} [Finite ι] {Y : ι → Scheme.{u}} [∀ i, IsAffine (Y i)] (g : ∀ i, Y i ⟶ Z)
    [∀ i, Flat (g i)] (hsurj : (⋃ i, Set.range (g i)) = Set.univ)
    [∀ i, Algebra Γ(Z, ⊤) Γ(Y i, ⊤)]
    (halg : ∀ i, algebraMap Γ(Z, ⊤) Γ(Y i, ⊤) = (g i).appTop.hom) :
    Module.FaithfullyFlat Γ(Z, ⊤) (∀ i, Γ(Y i, ⊤)) := by
  refine faithfullyFlat_pi_of_exists_comap_eq _ (fun i => ?_) (fun q => ?_)
  · rw [← RingHom.flat_algebraMap_iff, halg i]
    exact (g i).flat_appTop
  · obtain ⟨i, r, hr⟩ := exists_comap_appTop_eq_of_iUnion_range_eq_univ g hsurj q
    exact ⟨i, r, by rwa [halg i]⟩

/-- **The product of the rings of global functions on the members of a finite fppf covering family
of an affine scheme by affine schemes is faithfully flat over the ring of global functions on the
target.**  Membership in the fppf precoverage of schemes is flatness of every member together with
joint surjectivity (`AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff`), which is exactly
what `AlgebraicGeometry.faithfullyFlat_pi_gamma_of_iUnion_range_eq_univ` asks for. -/
theorem faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage {Z : Scheme.{u}} [IsAffine Z]
    {ι : Type w} [Finite ι] {Y : ι → Scheme.{u}} [∀ i, IsAffine (Y i)] (g : ∀ i, Y i ⟶ Z)
    (hg : Presieve.ofArrows Y g ∈ Scheme.fppfPrecoverage Z)
    [∀ i, Algebra Γ(Z, ⊤) Γ(Y i, ⊤)]
    (halg : ∀ i, algebraMap Γ(Z, ⊤) Γ(Y i, ⊤) = (g i).appTop.hom) :
    Module.FaithfullyFlat Γ(Z, ⊤) (∀ i, Γ(Y i, ⊤)) := by
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hg
  have _ : ∀ i, Flat (g i) := fun i => (hg.2 i).1
  exact faithfullyFlat_pi_gamma_of_iUnion_range_eq_univ g
    (Set.eq_univ_of_forall fun z => Set.mem_iUnion.2 (hg.1 z)) halg

end FinitePi

namespace IsStandardFppfCovering

variable {T : Scheme.{u}} {I : Type v} [Small.{u} I] {U : I → Scheme.{u}} {g : ∀ i, U i ⟶ T}

/-- **The morphism out of the coproduct of a standard fppf covering is flat.**  Flatness is
Zariski local at the source, so the morphism induced on a coproduct is flat as soon as every
member of the family is. -/
theorem flat_sigmaDesc (hg : IsStandardFppfCovering U g) : Flat (Sigma.desc g) := by
  have (i : I) : Flat (g i) := hg.flat i
  infer_instance

/-- **The morphism out of the coproduct of a standard fppf covering is surjective.**  The images
of the members of the family cover the target, which is surjectivity of the induced morphism by
`AlgebraicGeometry.Surjective.sigmaDesc_of_union_range_eq_univ`. -/
theorem surjective_sigmaDesc (hg : IsStandardFppfCovering U g) : Surjective (Sigma.desc g) :=
  Surjective.sigmaDesc_of_union_range_eq_univ hg.jointly_surjective

/-- **The coproduct of a standard fppf covering is affine.**  A standard fppf covering is finite
and all its members are affine, and a finite coproduct of affine schemes is affine. -/
theorem isAffine_sigmaObj (hg : IsStandardFppfCovering U g) : IsAffine (∐ U) := by
  have := hg.finite_index
  have (i : I) : IsAffine (U i) := hg.affine_source i
  infer_instance

/-- **The ring of global functions on the coproduct of a standard fppf covering is faithfully flat
over the ring of global functions on the base.**  The morphism out of the coproduct is one flat
surjective morphism of affine schemes, by
`AlgebraicGeometry.IsStandardFppfCovering.flat_sigmaDesc`,
`AlgebraicGeometry.IsStandardFppfCovering.surjective_sigmaDesc` and
`AlgebraicGeometry.IsStandardFppfCovering.isAffine_sigmaObj`, so
`AlgebraicGeometry.faithfullyFlat_appTop_of_flat_of_surjective` applies to it.

This is what turns a covering *family* into the single faithfully flat ring map which an Amitsur
complex is built from. -/
theorem faithfullyFlat_appTop_sigmaDesc (hg : IsStandardFppfCovering U g) :
    (Sigma.desc g).appTop.hom.FaithfullyFlat := by
  have := hg.affine_target
  have := hg.isAffine_sigmaObj
  have := hg.flat_sigmaDesc
  have := hg.surjective_sigmaDesc
  exact faithfullyFlat_appTop_of_flat_of_surjective _

/-- **The global functions on the coproduct of a standard fppf covering are faithfully flat over
the global functions on the base**, as a statement about modules. -/
theorem faithfullyFlat_gamma_sigmaDesc [Algebra Γ(T, ⊤) Γ(∐ U, ⊤)]
    (halg : algebraMap Γ(T, ⊤) Γ(∐ U, ⊤) = (Sigma.desc g).appTop.hom)
    (hg : IsStandardFppfCovering U g) : Module.FaithfullyFlat Γ(T, ⊤) Γ(∐ U, ⊤) := by
  exact faithfullyFlat_of_algebraMap_eq halg hg.faithfullyFlat_appTop_sigmaDesc

end IsStandardFppfCovering

namespace BigFppfSite

variable (B : BigFppfSite.{u}) {X Y : B.Schemes} (h : X ⟶ Y)

/-- **A morphism of a big fppf category of schemes whose one-element family is a selected covering
family has flat, surjective and locally finitely presented image in schemes.**  Every selected
covering family of a big fppf site is an fppf covering of schemes after applying the canonical
inclusion, and for a one-element family that is
`AlgebraicGeometry.flat_and_surjective_of_singleton_mem_fppfPrecoverage`. -/
theorem flat_and_surjective_of_singleton_mem_precoverage
    (hh : Presieve.singleton h ∈ B.precoverage Y) :
    Flat (B.inclusion.map h) ∧ Surjective (B.inclusion.map h) ∧
      LocallyOfFinitePresentation (B.inclusion.map h) := by
  obtain ⟨E, hE, hEcov⟩ := hh
  have hfppf : E.presieve₀ ∈ Scheme.fppfPrecoverage.comap B.inclusion Y :=
    B.isFppfCovering_of_isCovering hEcov
  rw [← hE, Precoverage.mem_comap_iff, Presieve.map_singleton] at hfppf
  exact flat_and_surjective_of_singleton_mem_fppfPrecoverage _ hfppf

/-- **The map of global functions along a one-element selected covering family of a big fppf site
between affine schemes is a faithfully flat ring map.** -/
theorem faithfullyFlat_appTop_of_singleton_mem_precoverage
    [IsAffine (B.inclusion.obj X)] [IsAffine (B.inclusion.obj Y)]
    (hh : Presieve.singleton h ∈ B.precoverage Y) :
    (B.inclusion.map h).appTop.hom.FaithfullyFlat := by
  obtain ⟨hflat, hsurj, -⟩ := B.flat_and_surjective_of_singleton_mem_precoverage h hh
  exact faithfullyFlat_appTop_of_flat_of_surjective _

end BigFppfSite

namespace FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- **The restriction map of the coefficient sheaf of rings of a slice of an associated site along
a morphism is the map of global functions along the underlying morphism of schemes.**  The
restriction of a sheaf to a slice is its composite with the forgetful functor of the slice, so this
is `AlgebraicGeometry.FibredSite.ringStructureSheafCore_obj_map` at the left components.

Like that lemma this is a definitional equation and not a `simp` lemma; it is named because a
consumer has to recognise the structure map of its algebra as a map of global functions in order
to apply `AlgebraicGeometry.FibredSite.faithfullyFlat_gamma_of_flat_of_surjective`. -/
theorem ringStructureSheafCore_over_map (hp : p.IsFiberedInGroupoids) (τ : SiteKind) {x : 𝒳}
    {D W : Over x} (h : D ⟶ W) :
    ((ringStructureSheafCore B S hS p hp τ).over x).obj.map h.op =
      (forget₂ CommRingCat RingCat).map
        ((BigFppfOver.toScheme B S hS).map (p.map h.left)).appTop := rfl

/-- **The global functions on the scheme underlying an affine object of a slice of an associated
fppf site are faithfully flat over the global functions on the scheme underlying another affine
object, along a morphism whose underlying morphism of schemes is flat and surjective.**

This is the ring-theoretic input of faithfully flat descent on a slice of an associated fppf site:
the Amitsur complex of the resulting algebra is what computes the sections of a presented sheaf of
modules over an affine object, so every statement proved by descent along a single covering
morphism of affine objects passes through this one.

Neither affineness of the object the slice is taken over nor the structure functor being fibred in
groupoids plays any part: faithful flatness is a property of the one morphism of affine schemes
underlying `h`. -/
theorem faithfullyFlat_gamma_of_flat_of_surjective {x : 𝒳} {D W : Over x} (h : D ⟶ W)
    (hD : IsAffineOver B S hS (p.obj D.left)) (hW : IsAffineOver B S hS (p.obj W.left))
    [Flat ((BigFppfOver.toScheme B S hS).map (p.map h.left))]
    [Surjective ((BigFppfOver.toScheme B S hS).map (p.map h.left))]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj D.left), ⊤)]
    (halg : algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj D.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map (p.map h.left)).appTop.hom) :
    Module.FaithfullyFlat Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj D.left), ⊤) := by
  have := hD
  have := hW
  exact _root_.AlgebraicGeometry.faithfullyFlat_gamma_of_flat_of_surjective _ halg

/-- **The product of the rings of global functions on the members of a finite fppf covering family
of affine objects of a slice of an associated fppf site is faithfully flat over the ring of global
functions on the object covered.**

This is the ring-theoretic input of descent along the family which
`AlgebraicGeometry.FibredSite.exists_finite_affine_fppf_ofArrows_le_over` produces: that
refinement supplies precisely the finiteness, the affineness and the fppf condition asked for
here, so the two compose with nothing left over.

The separatedness half of the sheaf condition for the family is what the product is for.  A
section over the object restricting to zero over every member of the family gives `1 ⊗ₜ n = 0` in
the base change along every factor, hence in the base change along the product, and
`Module.FaithfullyFlat.one_tmul_eq_zero_iff` makes the section zero. -/
theorem faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage {x : 𝒳} {W : Over x}
    {ι : Type w'} [Finite ι] (Y : ι → Over x) (a : ∀ i, Y i ⟶ W)
    (hW : IsAffineOver B S hS (p.obj W.left))
    (hY : ∀ i, IsAffineOver B S hS (p.obj (Y i).left))
    (hfppf : Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left))
        (fun i => (BigFppfOver.toScheme B S hS).map (p.map (a i).left)) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj (p.obj W.left)))
    [∀ i, Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)]
    (halg : ∀ i, algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map (p.map (a i).left)).appTop.hom) :
    Module.FaithfullyFlat Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (∀ i, Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)) := by
  have _ := hW
  have _ : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left)) := hY
  exact _root_.AlgebraicGeometry.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage _
    hfppf halg

end FibredSite

end AlgebraicGeometry

end
