module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainDescent
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionExactness
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.CechExactStandardCovering

/-!
# The descent of Tag 06VI, carried out over the algebras of the site

`Stacks.Adequate.StandardAffineDescent` is the third step of the source's proof of
[Stacks, Tag 06VI]: adequacy of the affine-section functors of `F` descends along a finite
standard affine `τ`-covering of an affine scheme of the site. The source proves it by passing
through the product `A' = A'₁ × ⋯ × A'ₘ` of the covering algebras — [Stacks, Tag 06VB] — and
then applying the descent of [Stacks, Tag 06VH] to the single ring map `A ⟶ A'`.

Both tags are available on the site's domain of algebras, so this module carries out that
proof, and `Stacks.Adequate.standardAffineDescent_of_productAdequacy` reduces
`StandardAffineDescent` to the single statement
`Stacks.Adequate.StandardAffineProductAdequacy`: that the affine-section functor at the
*product* algebra is adequate. That statement is proved in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/StandardAffineProductAdequacy.lean`,
so `StandardAffineDescent` holds outright and Tag 06VI is unconditional.

## Main results

* `Stacks.Adequate.siteBaseChangeClosed` — **the size clause.** The algebras of a chosen big
  site are closed under base change: if `Spec B` and `Spec A'` belong to the site, so does
  `Spec (B ⊗_A A')`. This is what lets the Čech diagram of [Stacks, Tag 06VH] be formed inside
  the site at all.
* `Stacks.Adequate.isAdequate_affineSectionFunctor_of_cechExactOn` — **[Stacks, Tag 06VH] in
  the geometric setting.** Adequacy of `F_{F, A}` from adequacy of `F_{F, A'}` for a single
  `A`-algebra `A'` of the site whose Čech condition holds.
* `Stacks.Adequate.standardAffineDescent_of_productAdequacy` —
  `Stacks.Adequate.StandardAffineDescent`, and hence the third step of [Stacks, Tag 06VI], from
  `Stacks.Adequate.StandardAffineProductAdequacy` alone.

## Implementation notes

**What is discharged here.** Of the four inputs the source's proof of
[Stacks, Tag 06VI] needs beyond the rest of the library, three are supplied here:

* the port of [Stacks, Tag 06VH], `AdequateFunctor.isAdequate_of_descent_on`;
* the port of [Stacks, Tag 06VA] that its Čech terms need,
  `AdequateFunctor.isAdequate_pushforwardOn`;
* the Čech-exactness hypothesis, `Stacks.Adequate.cechExactOn_affineSectionFunctor_pi`, which
  is unconditional.

The fourth, adequacy of `F_{F, A'}` for `A' = A'₁ × ⋯ × A'ₘ`, is left to
`Stacks.Adequate.standardAffineProductAdequacy` in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/StandardAffineProductAdequacy.lean`. In
the source it is [Stacks, Tag 06VB] together with the identification of `F_{F, A'}` with the
product of the `F_{F, A'ⱼ}`, which is the Zariski sheaf condition for the decomposition
`Spec A' = ⨆ⱼ Spec A'ⱼ`. [Stacks, Tag 06VB] itself is *not* needed on the site's domain for
it: `AdequateFunctor.isAdequate_pushforwardOn` already makes
`C ↦ F_{F, A'ⱼ}(C ⊗_{A'} A'ⱼ)` an adequate functor on the `A'`-algebras of the site for each
`j`, and `Stacks.Adequate.affineAdequateFiniteProducts` makes a finite product of those
adequate; so the whole of that remainder is the identification.

**The distinguished algebra is reached up to isomorphism.** `AdequateFunctor.baseAlgebra` of a
ring map carries `RingHom.toAlgebra` of that map, whereas the product algebra of
`Stacks.Adequate.cechExactOn_affineSectionFunctor_pi` carries `Pi.algebra`. The two have the
same `algebraMap` and are therefore isomorphic, but not equal, so the Čech condition is moved
between them by `AdequateFunctor.CechExactOn.of_iso`.

**The size clause is a cardinality bound, not a pullback.** `Spec (B ⊗_A A')` is the fibre
product of `Spec B` and `Spec A'`, so [Stacks, Tag 04T6] would bound its size; but the ring is
to hand, and `Cardinal.mk_tensorProduct_le` with `AlgebraicGeometry.Scheme.size_Spec` gives the
bound directly, with no scheme-level pullback and no appeal to the cutoff being a strong
prelimit. The base change of `AdequateFunctor.cechBaseChange` is the pushout of commutative
rings rather than the tensor product, and `Algebra.IsPushout.equiv` identifies the two.

## References

* [Stacks Project, Tag 06VI](https://stacks.math.columbia.edu/tag/06VI)
* [Stacks Project, Tag 06VH](https://stacks.math.columbia.edu/tag/06VH)
* [Stacks Project, Tag 06VB](https://stacks.math.columbia.edu/tag/06VB)
* [Stacks Project, Tag 06VA](https://stacks.math.columbia.edu/tag/06VA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct Cardinal

universe u m

namespace Stacks.Adequate

/-! ### The size clause -/

/-- **The algebras of a chosen big site are closed under base change.** If `Spec B` and
`Spec A'` are schemes of the site, so is `Spec (B ⊗_A A')`.

The base change `AdequateFunctor.cechBaseChange` is a pushout of commutative rings;
`Algebra.IsPushout.equiv` identifies it with the tensor product, whose cardinality is bounded
by `Cardinal.mk_tensorProduct_le`, and `AlgebraicGeometry.Scheme.size_Spec` turns that into the
size bound. -/
public theorem siteBaseChangeClosed {κ : Cardinal.{u}} {A A' : Type u} [CommRing A]
    [CommRing A'] (f : A →+* A') (hA' : (Spec (CommRingCat.of A')).size < κ) :
    AdequateFunctor.SiteBaseChangeClosed f (schemeSizeBelow κ) := by
  intro X
  have hX : (Spec (CommRingCat.of ↥X.obj)).size < κ := X.property
  let : Algebra A A' := f.toAlgebra
  set B : CommAlgCat.{u} A := X.obj
  set B' : Type u := ↥((AdequateFunctor.baseChangeFunctor f).obj B)
  let : Algebra ↥B B' :=
    (((AdequateFunctor.baseChangeRingHom f).app (op (op B))).hom).toAlgebra
  let : Algebra A B' := ((algebraMap A' B').comp f).toAlgebra
  let : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq' rfl
  set U := (commAlgCatEquivUnder (CommRingCat.of A)).functor.obj B
  have hcomm : U.hom ≫ pushout.inl U.hom (CommRingCat.ofHom f) =
      CommRingCat.ofHom f ≫ pushout.inr U.hom (CommRingCat.ofHom f) := pushout.condition
  have hcomp : algebraMap A B' = (algebraMap ↥B B').comp (algebraMap A ↥B) := by
    ext a
    change (pushout.inr U.hom (CommRingCat.ofHom f)).hom (f a) =
      (pushout.inl U.hom (CommRingCat.ofHom f)).hom (U.hom.hom a)
    exact congrArg (fun k : CommRingCat.Hom _ _ => k.hom a) hcomm.symm
  let : IsScalarTower A ↥B B' := IsScalarTower.of_algebraMap_eq' hcomp
  have : Algebra.IsPushout A ↥B A' B' :=
    (CommRingCat.isPushout_iff_isPushout (R := A) (R' := ↥B) (S := A') (S' := B')).mp
      ⟨⟨hcomm⟩, ⟨pushoutIsPushout U.hom (CommRingCat.ofHom f)⟩⟩
  have hten : (Spec (CommRingCat.of (TensorProduct A ↥B A'))).size < κ := by
    rw [Scheme.size_Spec]
    rw [Scheme.size_Spec, max_lt_iff] at hX hA'
    exact max_lt hX.1 (lt_of_le_of_lt Cardinal.mk_tensorProduct_le
      (max_lt hX.1 (max_lt hX.2 hA'.2)))
  let r : CommRingCat.of (TensorProduct A ↥B A') ≅ CommRingCat.of B' :=
    (Algebra.IsPushout.equiv A ↥B A' B').toRingEquiv.toCommRingCatIso
  have hiso : Spec (CommRingCat.of B') ≅ Spec (CommRingCat.of (TensorProduct A ↥B A')) :=
    { hom := Spec.map r.hom
      inv := Spec.map r.inv
      hom_inv_id := by rw [← Spec.map_comp, r.inv_hom_id, Spec.map_id]
      inv_hom_id := by rw [← Spec.map_comp, r.hom_inv_id, Spec.map_id] }
  exact (Scheme.size_congr hiso).trans_lt hten

/-! ### Tag 06VH in the geometric setting -/

/-- **[Stacks, Tag 06VH] for affine-section functors.** If `Spec A` and `Spec A'` are affine
schemes of the site over `S`, `φ : A ⟶ A'` a ring map, `F_{F, A'}` adequate, and the Čech
condition of the source holds for `F_{F, A}` at `A'`, then `F_{F, A}` is adequate.

This is `AdequateFunctor.isAdequate_of_descent_on` with its four inputs supplied: the size
clause `Stacks.Adequate.siteBaseChangeClosed`; the identification of `F_{F, A'}` with the
restriction of `F_{F, A}` to `A'`-algebras, `Stacks.Adequate.affineSectionRestriction`; and
closure of adequacy under kernels on the site's algebras,
`Stacks.Adequate.affineAdequateKernels`. -/
public theorem isAdequate_affineSectionFunctor_of_cechExactOn {τ : CoveringTopology}
    {S : Scheme.{u}} (B : BigSite τ S) (F : SheafOfModules.{max u m} B.structureSheaf)
    (A : CommRingCat.{u}) (f : Spec A ⟶ S) (hA : schemeSizeBelow B.cutoff (Spec A))
    (A' : CommRingCat.{u}) (φ : A ⟶ A') (hA' : schemeSizeBelow B.cutoff (Spec A'))
    (hadq : AdequateFunctor.IsAdequate
      (AdequateFunctor.siteAlgebraInclusion ↥A' (schemeSizeBelow B.cutoff))
      (affineSectionFunctor B F A' (Spec.map φ ≫ f)))
    (hexact : AdequateFunctor.CechExactOn
      (AdequateFunctor.siteAlgebraInclusion ↥A (schemeSizeBelow B.cutoff))
      (affineSectionFunctor B F A f)
      (AdequateFunctor.baseAlgebraOn φ.hom (schemeSizeBelow B.cutoff) hA')) :
    AdequateFunctor.IsAdequate
      (AdequateFunctor.siteAlgebraInclusion ↥A (schemeSizeBelow B.cutoff))
      (affineSectionFunctor B F A f) := by
  obtain ⟨e⟩ := affineSectionRestriction.{u, m} B F A A' φ f
  exact AdequateFunctor.isAdequate_of_descent_on.{m} φ.hom (schemeSizeBelow B.cutoff)
    (siteBaseChangeClosed φ.hom hA') hA'
    (affineSectionFunctor B F A f) (affineSectionFunctor B F A' (Spec.map φ ≫ f)) hadq
    ⟨e ≪≫ (AdequateFunctor.restrictFunctorOn.{max u m, u} φ.hom
        (schemeSizeBelow B.cutoff)).mapIso
          (AdequateFunctor.presheafOfModulesUliftIso.{u, max u m} _ _) ≪≫
      (AdequateFunctor.restrictZeroOnIso.{max u m} φ.hom (schemeSizeBelow B.cutoff) _).symm⟩
    (fun ψ hX hY => affineAdequateKernels.{u, m} B A hA ψ hX hY) hexact

/-! ### The remaining input, and the reduction to it -/

/-- A member of a finite covering family of affine schemes over `Spec A`, read as an
`A`-algebra through `AlgebraicGeometry.Spec.preimage`. -/
public noncomputable def coveringAlgebra {A : CommRingCat.{u}} {n : ℕ}
    (A' : Fin n → CommRingCat.{u}) (g : ∀ j, Spec (A' j) ⟶ Spec A) (j : Fin n) :
    CommAlgCat.{u} ↥A :=
  letI : Algebra ↥A ↥(A' j) := (Spec.preimage (g j)).hom.toAlgebra
  CommAlgCat.of ↥A ↥(A' j)

/-- The product `A'₁ × ⋯ × A'ₘ` of a finite covering family of affine schemes over `Spec A`,
as an `A`-algebra. This is the single algebra the source's proof of [Stacks, Tag 06VI] descends
along. -/
public noncomputable def coveringPi {A : CommRingCat.{u}} {n : ℕ}
    (A' : Fin n → CommRingCat.{u}) (g : ∀ j, Spec (A' j) ⟶ Spec A) : CommAlgCat.{u} ↥A :=
  CommAlgCat.of ↥A (∀ j, ↥(coveringAlgebra A' g j))

/-- **The one statement that `Stacks.Adequate.StandardAffineDescent` reduces to.** For a
finite standard affine `τ`-covering `{Spec A'ⱼ ⟶ Spec A}` by affine schemes of the site, with
each `F_{F, A'ⱼ}` adequate, the affine-section functor at the *product* `A'₁ × ⋯ × A'ₘ` is
adequate. It is a **theorem**, `Stacks.Adequate.standardAffineProductAdequacy`, proved in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/StandardAffineProductAdequacy.lean`.

In the source this is the passage through the product of [Stacks, Tag 06VB]. On the site's
domain of algebras [Stacks, Tag 06VB] itself is not what is needed:
`AdequateFunctor.isAdequate_pushforwardOn` makes `C ↦ F_{F, A'ⱼ}(C ⊗_{A'} A'ⱼ)` adequate on the
`A'`-algebras of the site, and `Stacks.Adequate.affineAdequateFiniteProducts` makes a finite
product of such adequate; all that is left is the identification of `F_{F, A'}` with that
product, which is the Zariski sheaf condition for `Spec A' = ⨆ⱼ Spec A'ⱼ`. -/
public abbrev StandardAffineProductAdequacy {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (F : SheafOfModules.{max u m} B.structureSheaf) : Prop :=
  ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ S), schemeSizeBelow B.cutoff (Spec A) →
    ∀ (n : ℕ) (A' : Fin n → CommRingCat.{u}) (g : ∀ j, Spec (A' j) ⟶ Spec A),
      IsStandardCovering τ (fun j => Spec (A' j)) g →
      (∀ j, schemeSizeBelow B.cutoff (Spec (A' j))) →
      (∀ j, AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion ↥(A' j) (schemeSizeBelow B.cutoff))
        (affineSectionFunctor B F (A' j) (g j ≫ f))) →
      AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion ↥(coveringPi A' g) (schemeSizeBelow B.cutoff))
        (affineSectionFunctor B F (CommRingCat.of ↥(coveringPi A' g))
          (Spec.map (CommRingCat.ofHom (algebraMap ↥A ↥(coveringPi A' g))) ≫ f))

/-- **`Stacks.Adequate.StandardAffineDescent` from the product statement alone.** The source's
proof of [Stacks, Tag 06VI] is carried out here: the product `A' = A'₁ × ⋯ × A'ₘ` is an algebra
of the site by `Stacks.Adequate.schemeSizeBelow_Spec_pi`, the Čech condition for it is
`Stacks.Adequate.cechExactOn_affineSectionFunctor_pi`, and the descent is
`Stacks.Adequate.isAdequate_affineSectionFunctor_of_cechExactOn`.

The Čech condition is proved at the product algebra carrying `Pi.algebra`, while the descent
asks for it at `AdequateFunctor.baseAlgebra` of the structure map, which carries
`RingHom.toAlgebra`; the identity is an isomorphism between the two, and
`AdequateFunctor.CechExactOn.of_iso` moves the condition across it. -/
public theorem standardAffineDescent_of_productAdequacy {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (F : SheafOfModules.{max u m} B.structureSheaf)
    (hprod : StandardAffineProductAdequacy.{u, m} B F) :
    StandardAffineDescent.{u, m} B F := by
  intro A f hA n A' g hstd hsize hadq
  have hPi : schemeSizeBelow B.cutoff (Spec (CommRingCat.of ↥(coveringPi A' g))) :=
    schemeSizeBelow_Spec_pi B A' hsize
  have hg : ∀ j, Spec.map (CommRingCat.ofHom (algebraMap ↥A ↥(coveringAlgebra A' g j))) =
      g j := fun j => by
    change Spec.map (CommRingCat.ofHom (Spec.preimage (g j)).hom) = g j
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hstd' : IsStandardCovering τ
      (fun j => Spec (CommRingCat.of ↥(coveringAlgebra A' g j)))
      (fun j => Spec.map (CommRingCat.ofHom
        (algebraMap ↥A ↥(coveringAlgebra A' g j)))) := by
    rwa [funext hg]
  refine isAdequate_affineSectionFunctor_of_cechExactOn.{u, m} B F A f hA
    (CommRingCat.of ↥(coveringPi A' g))
    (CommRingCat.ofHom (algebraMap ↥A ↥(coveringPi A' g))) hPi
    (hprod A f hA n A' g hstd hsize hadq) ?_
  exact AdequateFunctor.CechExactOn.of_iso
    (ObjectProperty.isoMk (P := AdequateFunctor.algebraInSite.{u, u} ↥A
      (schemeSizeBelow B.cutoff))
      (CommAlgCat.isoMk { toRingEquiv := RingEquiv.refl _, commutes' := fun a => rfl }))
    (cechExactOn_affineSectionFunctor_pi.{u, m} B F A f hA (coveringAlgebra A' g) hstd')

end Stacks.Adequate

end
