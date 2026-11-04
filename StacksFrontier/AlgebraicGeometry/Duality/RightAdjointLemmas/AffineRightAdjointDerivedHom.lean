module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.TildeFactorization
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.AffineLineExample
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.AffineRightAdjoint
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffineDerivedPushforward
public import StacksFrontier.RingTheory.Dualizing.DerivedHomAnyModel

/-!
# The right adjoint of affine derived pushforward is derived Hom, and is not coherent

Let `φ : R ⟶ S` be a homomorphism of commutative rings, `Y = Spec R`, `X = Spec S` and
`f : X ⟶ Y` the induced morphism. [Stacks, Tag 0A9F] says two things: that `Rf_*` corresponds to
restriction of scalars `D(S) ⥤ D(R)` under derived sheafification, and that *hence* the right
adjoint of `Rf_*` corresponds to `RHom_R(S, -)`. [Stacks, Tag 0A9G] then exhibits the affine line
over a field as a separated finite-type morphism of Noetherian schemes whose right adjoint does not
preserve coherent cohomology, by computing `RHom_k(k[X], k)`.

`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/AffineRightAdjoint.lean` proves the
"hence" with the right adjoint of derived restriction of scalars left as an abstract hypothesis,
because `Dualizing.derivedHom` — the functor 0A9F names — is stated at
`CategoryTheory.HasDerivedCategory.standard` while derived sheafification is stated at the locally
small models. This file removes that hypothesis. The comparison of models that the removal needs
turns out to be already available: `Dualizing.AnyModel.derivedHom` is `RHom_R(S, -)` between
*arbitrary* chosen models of `D(R)` and `D(S)`, with `Dualizing.AnyModel.derivedHom_eq_standard`
identifying it with `Dualizing.derivedHom` at the standard model. So no new comparison lemma is
required: the right thing is to state the transport at the locally small model with
`Dualizing.AnyModel.derivedHom`, which is what
`AlgebraicGeometry.derivedTilde_comp_rightAdjointIsoDerivedHom` does.

The same move is then made for 0A9G. Its obstruction is proved in `AffineLineExample.lean` at the
standard model only; the two statements there are combined below into the model-free algebraic fact
that `Hom_k(k[X], k)` is not a finite `k[X]`-module, and that fact is transported back to an
*arbitrary* model of the derived categories, so that it sits at the model the transport above uses.

## Main results

* `Dualizing.AnyModel.coextendScalarsMapDerivedCategoryIsoDerivedHom` — over a division ring,
  coextension of scalars is exact, so `RHom_A(B, -)` is its termwise extension to derived
  categories, at any chosen models.
* `Dualizing.polynomialCoextendScalars_not_finite` — `Hom_k(k[X], k)` is not a finite
  `k[X]`-module. This is the obstruction of [Stacks, Tag 0A9G], with no derived category in the
  statement.
* `Dualizing.AnyModel.polynomialDerivedHom_homologyZero` and
  `Dualizing.AnyModel.polynomialDerivedHom_not_finite` — the degree-zero cohomology of
  `RHom_k(k[X], k)` is that module, at any chosen models, hence is not finite.
* `AlgebraicGeometry.derivedTilde_comp_rightAdjointIsoDerivedHom` — the conclusion of
  [Stacks, Tag 0A9F] with the comparison functor of [Stacks, Tag 06VT] and the square of
  [Stacks, Tag 0DJK] as hypotheses.
* `AlgebraicGeometry.derivedTilde_comp_rightAdjoint_derivedQuasicoherentPushforwardIsoDerivedHom`
  — **the second assertion of [Stacks, Tag 0A9F]**, with both of those hypotheses discharged: a
  right adjoint of `Rf_* : D_QCoh(𝒪_{Spec S}) ⥤ D_QCoh(𝒪_{Spec R})` corresponds to
  `RHom_R(S, -)`.
* `AlgebraicGeometry.affineTwistedInverseImage` and
  `AlgebraicGeometry.derivedQuasicoherentPushforward_adj_affineTwistedInverseImage` — the right
  adjoint of `Rf_*` for a morphism of affine schemes, and the proof that it *is* one. This is the
  affine case of [Stacks, Tag 0A9E], obtained without Brown representability.
* `AlgebraicGeometry.exists_adj_derivedQuasicoherentPushforward_isoDerivedHom` —
  **[Stacks, Tag 0A9F] with nothing assumed**: `Rf_*` has a right adjoint, and that right adjoint
  corresponds to `RHom_R(S, -)` under derived sheafification.
* `AlgebraicGeometry.polynomialRightAdjoint_homologyZero_not_finite` — **[Stacks, Tag 0A9G]**: the
  right adjoint of `Rf_*` for the affine line over a field does not have coherent cohomology at
  the structure sheaf.

## Implementation notes

**Where the two halves of `@[stacks 0A9F]` sit.** Tag 0A9F asserts that `Rf_*` corresponds to
restriction of scalars — which is also [Stacks, Tag 0DJK], proved as
`AlgebraicGeometry.derivedTildeCompDerivedQuasicoherentPushforwardIso` in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/AffineDerivedPushforward.lean`, where the
attribute for that half is attached — and that *hence* the right adjoint corresponds to
`RHom_R(S, -)`, which is
`AlgebraicGeometry.derivedTilde_comp_rightAdjoint_derivedQuasicoherentPushforwardIsoDerivedHom`
below. The two inputs this needs are both discharged: that
the comparison functor of [Stacks, Tag 06VT] is an equivalence is
`Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence`, and [Stacks, Tag 0DJK] is the
declaration just named.

**The existence of the right adjoint is proved, not assumed.** The source cites
[Stacks, Tag 0A9E] for it, whose proof runs through Brown representability and needs compact
generation of `D_QCoh` ([Stacks, Tag 09IS]); that route is available here only in its affine case
with three hypotheses, as
`Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward_of_affine`. Between affine schemes
the adjoint does not need that route at all: derived sheafification is an equivalence on either
side and carries derived restriction of scalars to `Rf_*`, so `Rf_*` is conjugate to a functor
which already has a right adjoint, and the conjugate of that right adjoint is one for `Rf_*`.
That is `AlgebraicGeometry.derivedQuasicoherentPushforward_adj_affineTwistedInverseImage`, and the
adjoint it produces is `AlgebraicGeometry.affineTwistedInverseImage`.

`AlgebraicGeometry.derivedTilde_comp_rightAdjointIsoDerivedHom` and
`AlgebraicGeometry.derivedTilde_comp_rightAdjoint_derivedQuasicoherentPushforwardIsoDerivedHom`
keep the adjunction as the hypothesis `adjP`, because they are about an *arbitrary* right adjoint
`a` and so say more than the statement about the particular one; a right adjoint being unique up
to canonical isomorphism, the two readings agree.
`AlgebraicGeometry.exists_adj_derivedQuasicoherentPushforward_isoDerivedHom` is the combination
with no hypothesis left. The hypothesis in
`AlgebraicGeometry.polynomialRightAdjoint_homologyZero_not_finite` below could be discharged the
same way; it is kept because [Stacks, Tag 0A9G] itself takes the adjoint as given.

**Why 0A9G is stated about a module and not about a sheaf.** The source concludes that
`a(𝒪_Y)` does not have coherent cohomology sheaves. The dictionary between coherence of a
quasi-coherent module on `Spec A` and finiteness of the `A`-module it comes from is not formalized
here, so the conclusion is stated on the module side: an object of `D(k[X])` which derived
sheafification carries to `a(𝒪_Y)` has non-finite degree-zero cohomology. Derived sheafification
being an equivalence, that pins `a(𝒪_Y)` down and says the same thing.

**The exactness instance for coextension of scalars.** `Limits.PreservesFiniteColimits` of
`ModuleCat.coextendScalars` out of a division ring is a `local instance` of
`AffineLineExample.lean` and so is not visible outside it; the copy below is the only way to have
it here. Dropping `local` there and deleting this copy is a free deduplication.
`CategoryTheory.Functor.Additive` of the same functor is *not* re-proved: it is the public
`StacksDraft.KInjective.ChangeOfRings.coextendScalars_additive`, which
`StacksFrontier/RingTheory/Dualizing/DerivedHomAnyModel.lean` already brings in.

## References

* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
* [Stacks Project, Tag 0A9G](https://stacks.math.columbia.edu/tag/0A9G)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0DJK](https://stacks.math.columbia.edu/tag/0DJK)
* [Stacks Project, Tag 08D9](https://stacks.math.columbia.edu/tag/08D9)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.QuasicoherentDerived

universe u

/-- Finiteness of a module transfers along an isomorphism of module categories. -/
private theorem finite_of_iso {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (e : M ≅ N)
    (h : Module.Finite R M) : Module.Finite R N :=
  Module.Finite.of_surjective e.hom.hom fun m => ⟨e.inv m, by simp⟩

namespace Dualizing.AnyModel

/-- **Coextension of scalars out of a division ring is exact.** It is a right adjoint, so it
preserves finite limits; it preserves epimorphisms because its left adjoint, restriction of
scalars, preserves projective objects — every module over a division ring is free, hence
projective.

This duplicates a `local instance` of
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/AffineLineExample.lean`; see the
implementation notes of this file. -/
instance preservesFiniteColimits_coextendScalars {A B : Type u} [DivisionRing A] [Ring B]
    (f : A →+* B) : PreservesFiniteColimits (ModuleCat.coextendScalars.{u, u, u} f) := by
  have hproj : (ModuleCat.restrictScalars.{u} f).PreservesProjectiveObjects :=
    { projective_obj := fun {M} _ =>
        ModuleCat.projective_of_categoryTheory_projective
          (P := (ModuleCat.restrictScalars.{u} f).obj M) }
  have : (ModuleCat.coextendScalars.{u, u, u} f).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction_of_preservesProjectiveObjects
      (ModuleCat.restrictCoextendScalarsAdj.{u} f)
  have : (ModuleCat.coextendScalars.{u, u, u} f).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact Functor.preservesFiniteColimits_of_preservesHomology _

variable {A B : Type u} [DivisionRing A] [Ring B]
  [HasDerivedCategory.{u} (ModuleCat.{u} A)] [HasDerivedCategory.{u} (ModuleCat.{u} B)]

/-- **Over a division ring, `RHom_A(B, -)` needs no derived correction.** Coextension of scalars
along `f : A →+* B` is exact when `A` is a division ring, so the functor it induces termwise on
derived categories is already a total right derived functor of it, and therefore agrees with
`Dualizing.AnyModel.derivedHom f`.

Both functors are total right derived functors of
`(ModuleCat.coextendScalars f).mapHomotopyCategory _ ⋙ DerivedCategory.Qh` along the
quasi-isomorphisms, so they are canonically isomorphic by
`CategoryTheory.Functor.rightDerivedUnique`. -/
def coextendScalarsMapDerivedCategoryIsoDerivedHom (f : A →+* B) :
    (ModuleCat.coextendScalars.{u, u, u} f).mapDerivedCategory ≅
      derivedHom.{u, u, u, u, u} f := by
  let F := ModuleCat.coextendScalars.{u, u, u} f
  let W := HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)
  have hptw : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseRightDerivedFunctor W :=
    coextendScalars_hasPointwiseRightDerivedFunctor.{u, u, u, u} f
  have hF : F.mapDerivedCategory.IsRightDerivedFunctor F.mapDerivedCategoryFactorsh.inv W :=
    Functor.isRightDerivedFunctor_of_inverts W F.mapDerivedCategory F.mapDerivedCategoryFactorsh
  have hdef : derivedHom.{u, u, u, u, u} f =
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
        DerivedCategory.Qh W := rfl
  rw [hdef]
  exact Functor.rightDerivedUnique F.mapDerivedCategory
    ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
      DerivedCategory.Qh W)
    F.mapDerivedCategoryFactorsh.inv
    ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
      DerivedCategory.Qh W) W

end Dualizing.AnyModel

namespace Dualizing

/-- The `k[X]`-module `Hom_k(k[X], k)` of `k`-linear forms on the polynomial ring `k[X]` over a
field `k` is not finite. -/
theorem polynomialCoextendScalars_not_finite (k : Type u) [Field k] :
    ¬ Module.Finite (Polynomial k)
      ((ModuleCat.coextendScalars.{u, u, u}
        (Polynomial.C : k →+* Polynomial k)).obj (ModuleCat.of k k)) := by
  intro hfinite
  have := HasDerivedCategory.standard (ModuleCat.{u} k)
  have := HasDerivedCategory.standard (ModuleCat.{u} (Polynomial k))
  obtain ⟨e⟩ := polynomialDerivedHom_homologyZero.{u} k
  exact polynomialDerivedHom_not_finite.{u} k
    (finite_of_iso e.symm hfinite)

namespace AnyModel

variable (k : Type u) [Field k] [HasDerivedCategory.{u} (ModuleCat.{u} k)]
  [HasDerivedCategory.{u} (ModuleCat.{u} (Polynomial k))]

/-- **Stacks 0A9G, at any chosen models of the derived categories.** The degree-zero cohomology of
`RHom_k(k[X], k)` is the `k[X]`-module `Hom_k(k[X], k)` of `k`-linear forms on the polynomial ring.

`k[X]` is free over `k`, so `RHom_k(k[X], -)` is already exact and at the one-term complex `k` it
is concentrated in degree zero, where it is ordinary coextension of scalars. This is
`Dualizing.polynomialDerivedHom_homologyZero` freed of
`CategoryTheory.HasDerivedCategory.standard`. -/
theorem polynomialDerivedHom_homologyZero :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Polynomial k)) 0).obj
        ((derivedHom.{u, u, u, u, u} (Polynomial.C : k →+* Polynomial k)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))) ≅
      (ModuleCat.coextendScalars.{u, u, u}
        (Polynomial.C : k →+* Polynomial k)).obj (ModuleCat.of k k)) := by
  let φ : k →+* Polynomial k := Polynomial.C
  let F := ModuleCat.coextendScalars.{u, u, u} φ
  let e : F.mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (Polynomial k)) 0).obj
        (F.obj (ModuleCat.of k k)) :=
    (F.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of k k)
  exact ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} (Polynomial k)) 0).mapIso
    (((coextendScalarsMapDerivedCategoryIsoDerivedHom φ).app _).symm ≪≫ e) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} (Polynomial k)) 0).app _⟩

/-- **Stacks 0A9G, at any chosen models of the derived categories.** The degree-zero cohomology of
`RHom_k(k[X], k)` is not a finite `k[X]`-module.

This is `Dualizing.AnyModel.polynomialDerivedHom_homologyZero` together with the model-free
`Dualizing.polynomialCoextendScalars_not_finite`. It is the obstruction of [Stacks, Tag 0A9G] at
the locally small model `ModuleCat.hasDerivedCategory`, which is the one at which derived
sheafification and hence the transport of [Stacks, Tag 0A9F] is stated. The attribute for
[Stacks, Tag 0A9G] sits not here but on the sheaf-side statement this feeds,
`AlgebraicGeometry.polynomialRightAdjoint_homologyZero_not_isCoherent` in
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/CoherentCohomologySheaves.lean`. -/
theorem polynomialDerivedHom_not_finite :
    ¬ Module.Finite (Polynomial k)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Polynomial k)) 0).obj
        ((derivedHom.{u, u, u, u, u} (Polynomial.C : k →+* Polynomial k)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)))) := by
  intro hfinite
  obtain ⟨e⟩ := polynomialDerivedHom_homologyZero.{u} k
  exact polynomialCoextendScalars_not_finite.{u} k
    (finite_of_iso e hfinite)

end AnyModel

end Dualizing

namespace AlgebraicGeometry

/-- **The right adjoint of derived pushforward between affine schemes is derived Hom.** Let
`φ : R ⟶ S` be a homomorphism of commutative rings. Suppose the comparison functor
`D(QCoh(𝒪_{Spec R})) ⥤ D_QCoh(𝒪_{Spec R})` of [Stacks, Tag 06VT] is an equivalence on `Spec R` and
on `Spec S` — equivalently, by
`Stacks.DerivedQCoh.derivedTilde_isEquivalence_iff_comparison`, that derived sheafification is an
equivalence, which is the remaining content of [Stacks, Tag 06Z0]. Let `P` be a functor
`D_QCoh(𝒪_{Spec S}) ⥤ D_QCoh(𝒪_{Spec R})` with a right adjoint `a`, and suppose `P` corresponds to
derived restriction of scalars under derived sheafification ([Stacks, Tag 0DJK]). Then `a`
corresponds to `RHom_R(S, -)`.

This is the conclusion of [Stacks, Tag 0A9F]. It strengthens
`AlgebraicGeometry.derivedTilde_comp_rightAdjointIso`, which leaves a right adjoint of derived
restriction of scalars as a hypothesis: here it is `Dualizing.AnyModel.derivedHom`, the functor the
tag names, at the locally small model at which derived sheafification is stated. No attribute is
attached, because the version of this with `hR` and `hS` discharged is the one that carries it,
`AlgebraicGeometry.derivedTilde_comp_rightAdjoint_derivedQuasicoherentPushforwardIsoDerivedHom`
just below. -/
theorem derivedTilde_comp_rightAdjointIsoDerivedHom {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hR : (derivedQuasicoherentComparison.{u} (Spec R)).IsEquivalence)
    (hS : (derivedQuasicoherentComparison.{u} (Spec S)).IsEquivalence)
    {P : (DerivedCategoryB.derivedCategoryB (A := (Spec S).Modules)
        (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory}
    {a : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB (A := (Spec S).Modules)
        (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf)).FullSubcategory}
    (adjP : P ⊣ a)
    (hP : derivedTilde S ⋙ P ≅
      (ModuleCat.restrictScalars.{u} φ.hom).mapDerivedCategory ⋙ derivedTilde R) :
    Nonempty (derivedTilde R ⋙ a ≅
      Dualizing.AnyModel.derivedHom.{u, u, u, u, u} φ.hom ⋙ derivedTilde S) := by
  have := Stacks.DerivedQCoh.derivedTilde_isEquivalence R hR
  have := Stacks.DerivedQCoh.derivedTilde_isEquivalence S hS
  obtain ⟨adjRes⟩ :=
    Dualizing.AnyModel.restrictScalarsDerived_adj_derivedHom.{u, u, u, u, u} φ.hom
  exact ⟨derivedTilde_comp_rightAdjointIso φ adjP hP adjRes⟩

/-- **Stacks 0A9F.** Let `φ : R ⟶ S` be a homomorphism of commutative rings, `Y = Spec R`,
`X = Spec S` and `f = Spec φ : X ⟶ Y`. Let `a` be a right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. Then `a` corresponds to `RHom_R(S, -)` under derived
sheafification.

This is the second assertion of [Stacks, Tag 0A9F]; the first — that `Rf_*` corresponds to
restriction of scalars — is
`AlgebraicGeometry.derivedTildeCompDerivedQuasicoherentPushforwardIso`, which is also
[Stacks, Tag 0DJK] and is what discharges the hypothesis `hP` of
`AlgebraicGeometry.derivedTilde_comp_rightAdjointIsoDerivedHom` here. The other two hypotheses of
that statement, that the comparison functor of [Stacks, Tag 06VT] is an equivalence on the two
affine schemes, are `Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence`.

`a` is arbitrary, so this says more than the corresponding statement about the particular right
adjoint `AlgebraicGeometry.affineTwistedInverseImage` constructed below; its existence is
`AlgebraicGeometry.derivedQuasicoherentPushforward_adj_affineTwistedInverseImage`, and
`AlgebraicGeometry.exists_adj_derivedQuasicoherentPushforward_isoDerivedHom` combines the two into
the tag with no hypothesis. The adjunction `adjP` is therefore **not** hypothetical: it is
constructed, and this statement is kept in the general form only because quantifying over `a`
says more. -/
@[stacks 0A9F "the right adjoint is derived Hom; the general form, which takes the adjunction \
adjP for an arbitrary right adjoint a of Rf_* as data. THAT DATA IS NOT HYPOTHETICAL: it is \
constructed by AlgebraicGeometry.derivedQuasicoherentPushforward_adj_affineTwistedInverseImage \
below, at the functor AlgebraicGeometry.affineTwistedInverseImage, by conjugating the adjunction \
of Tag 0A70 (Dualizing.AnyModel.restrictScalarsDerived_adj_derivedHom) along the derived \
sheafification equivalences of Tag 06Z0; the two combine into \
AlgebraicGeometry.exists_adj_derivedQuasicoherentPushforward_isoDerivedHom below, which assumes \
nothing beyond the ring map. This form is kept because quantifying over an arbitrary right \
adjoint says more, a right adjoint being unique up to canonical isomorphism"]
theorem derivedTilde_comp_rightAdjoint_derivedQuasicoherentPushforwardIsoDerivedHom
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {a : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB (A := (Spec S).Modules)
        (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf)).FullSubcategory}
    (adjP : derivedQuasicoherentPushforward (Spec.map φ) ⊣ a) :
    Nonempty (derivedTilde R ⋙ a ≅
      Dualizing.AnyModel.derivedHom.{u, u, u, u, u} φ.hom ⋙ derivedTilde S) :=
  derivedTilde_comp_rightAdjointIsoDerivedHom φ
    (Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence R)
    (Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence S)
    adjP (derivedTildeCompDerivedQuasicoherentPushforwardIso φ)

/-- **The twisted inverse image `f^×` for a morphism of affine schemes.** For `φ : R ⟶ S` and
`f = Spec φ : Spec S ⟶ Spec R`, this is the composite
`D_QCoh(𝒪_{Spec R}) ⥤ D(R) ⥤ D(S) ⥤ D_QCoh(𝒪_{Spec S})` of a quasi-inverse of derived
sheafification, derived Hom `RHom_R(S, -)` and derived sheafification — that is, `RHom_R(S, -)`
read through the equivalences of [Stacks, Tag 06Z0].

`AlgebraicGeometry.derivedQuasicoherentPushforward_adj_affineTwistedInverseImage` proves that it
is right adjoint to `Rf_*`, so it is the functor [Stacks, Tag 0A9E] produces, here for a morphism
of affine schemes and without Brown representability. -/
def affineTwistedInverseImage {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB (A := (Spec S).Modules)
        (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf)).FullSubcategory :=
  (derivedTilde R).inv ⋙ Dualizing.AnyModel.derivedHom.{u, u, u, u, u} φ.hom ⋙ derivedTilde S

/-- **Stacks 0A9F, the existence of the right adjoint in the affine case.** Let `φ : R ⟶ S` be a
homomorphism of commutative rings and `f = Spec φ`. Then
`Rf_* : D_QCoh(𝒪_{Spec S}) ⥤ D_QCoh(𝒪_{Spec R})` *has* a right adjoint, namely
`AlgebraicGeometry.affineTwistedInverseImage φ`.

No hypothesis is assumed: the source cites [Stacks, Tag 0A9E] for existence, whose proof goes
through Brown representability and compact generation of `D_QCoh` ([Stacks, Tag 09IS]), but over
an affine base the adjoint can be produced directly. Derived sheafification is an equivalence on
either side ([Stacks, Tag 06Z0], `AlgebraicGeometry.derivedTilde_isEquivalence`) and carries
derived restriction of scalars to `Rf_*` ([Stacks, Tag 0DJK],
`AlgebraicGeometry.derivedTildeCompDerivedQuasicoherentPushforwardIso`), so `Rf_*` is conjugate to
a functor which already has a right adjoint, `RHom_R(S, -)` ([Stacks, Tag 0A70],
`Dualizing.AnyModel.restrictScalarsDerived_adj_derivedHom`); the conjugate of that right adjoint
is a right adjoint of `Rf_*`, which is
`CategoryTheory.Adjunction.ofSquare`. -/
@[stacks 0A9F "the right adjoint exists, affine case"]
theorem derivedQuasicoherentPushforward_adj_affineTwistedInverseImage
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    Nonempty (derivedQuasicoherentPushforward (Spec.map φ) ⊣ affineTwistedInverseImage φ) := by
  obtain ⟨adjRes⟩ :=
    Dualizing.AnyModel.restrictScalarsDerived_adj_derivedHom.{u, u, u, u, u} φ.hom
  exact ⟨Adjunction.ofSquare (derivedTilde R).asEquivalence (derivedTilde S).asEquivalence
    adjRes (derivedTildeCompDerivedQuasicoherentPushforwardIso φ)⟩

/-- The twisted inverse image of a morphism of affine schemes corresponds to `RHom_R(S, -)` under
derived sheafification, by construction: `AlgebraicGeometry.affineTwistedInverseImage` is
`RHom_R(S, -)` conjugated by the equivalences of [Stacks, Tag 06Z0], so precomposing with derived
sheafification cancels the quasi-inverse. The content of [Stacks, Tag 0A9F] is not here but in
`AlgebraicGeometry.derivedQuasicoherentPushforward_adj_affineTwistedInverseImage`, that this
functor is a right adjoint of `Rf_*`, and in
`AlgebraicGeometry.derivedTilde_comp_rightAdjoint_derivedQuasicoherentPushforwardIsoDerivedHom`,
that *any* right adjoint of `Rf_*` corresponds to `RHom_R(S, -)`. -/
def derivedTilde_comp_affineTwistedInverseImageIsoDerivedHom {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    derivedTilde R ⋙ affineTwistedInverseImage φ ≅
      Dualizing.AnyModel.derivedHom.{u, u, u, u, u} φ.hom ⋙ derivedTilde S :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedTilde R).asEquivalence.unitIso.symm _ ≪≫
    Functor.leftUnitor _

/-- **Stacks 0A9F in full, with nothing assumed.** Let `φ : R ⟶ S` be a homomorphism of
commutative rings, `Y = Spec R`, `X = Spec S` and `f = Spec φ : X ⟶ Y`. Then
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` has a right adjoint `a`, and `a` corresponds to `RHom_R(S, -)`
under derived sheafification.

This packages the two halves of the tag that the declarations above prove separately — existence,
`AlgebraicGeometry.derivedQuasicoherentPushforward_adj_affineTwistedInverseImage`, and the
identification, `AlgebraicGeometry.derivedTilde_comp_affineTwistedInverseImageIsoDerivedHom` —
into the single unconditional statement. The first assertion of the tag, that `Rf_*` itself is
derived restriction of scalars, is
`AlgebraicGeometry.derivedTildeCompDerivedQuasicoherentPushforwardIso`, which is also
[Stacks, Tag 0DJK]. -/
@[stacks 0A9F "existence and identification of the right adjoint, affine case"]
theorem exists_adj_derivedQuasicoherentPushforward_isoDerivedHom
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    ∃ a : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
          (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory ⥤
        (DerivedCategoryB.derivedCategoryB (A := (Spec S).Modules)
          (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf)).FullSubcategory,
      Nonempty (derivedQuasicoherentPushforward (Spec.map φ) ⊣ a) ∧
        Nonempty (derivedTilde R ⋙ a ≅
          Dualizing.AnyModel.derivedHom.{u, u, u, u, u} φ.hom ⋙ derivedTilde S) :=
  ⟨affineTwistedInverseImage φ,
    derivedQuasicoherentPushforward_adj_affineTwistedInverseImage φ,
    ⟨derivedTilde_comp_affineTwistedInverseImageIsoDerivedHom φ⟩⟩

/-- **Stacks 0A9G.** Let `k` be a field and `f : A¹_k ⟶ Spec k` the structure morphism of the
affine line, a separated finite-type morphism of Noetherian schemes. Let `a` be a right adjoint of
`Rf_* : D_QCoh(𝒪_{A¹_k}) ⥤ D_QCoh(𝒪_{Spec k})`. Then `a(𝒪_{Spec k})` does not have coherent
cohomology sheaves: an object `E` of `D(k[X])` that derived sheafification carries to it has
degree-zero cohomology which is not a finite `k[X]`-module, so that cohomology sheaf is not
coherent.

Derived sheafification `D(k[X]) ⥤ D_QCoh(𝒪_{A¹_k})` is fully faithful
(`AlgebraicGeometry.derivedTilde_isEquivalence`), so the hypothesis `hE` pins `E` down up to
isomorphism; by [Stacks, Tag 0A9F] it is `RHom_k(k[X], k)`, whose degree-zero cohomology is the
module `Hom_k(k[X], k)` of `k`-linear forms on `k[X]` — the product of countably many copies of
`k` the source computes — and that module is not finite, which is
`Dualizing.AnyModel.polynomialDerivedHom_not_finite`.

The statement is about the module rather than about the sheaf, and so is *not* the carrier of the
tag. [Stacks, Tag 0A9G] asserts that the right adjoint does not map `D_Coh(𝒪_Y)` into
`D_Coh(𝒪_X)`, a statement about coherent cohomology sheaves; that is
`AlgebraicGeometry.polynomialRightAdjoint_homologyZero_not_isCoherent` in
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/CoherentCohomologySheaves.lean`, where
`@[stacks 0A9G]` is attached. That statement also does without the pair `E`, `hE` below, derived
sheafification being an equivalence; the dictionary carrying this module-side statement across to
the sheaf-side one is `AlgebraicGeometry.isCoherent_homologyDerivedTilde_iff` in the same file. -/
theorem polynomialRightAdjoint_homologyZero_not_finite (k : Type u) [Field k]
    {a : (DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of k)).Modules)
        (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of k)).ringCatSheaf)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB
          (A := (Spec (CommRingCat.of (Polynomial k))).Modules)
        (SheafOfModules.isQuasicoherent
          (Spec (CommRingCat.of (Polynomial k))).ringCatSheaf)).FullSubcategory}
    (adjP : derivedQuasicoherentPushforward (Spec.map
      (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) ⊣ a)
    (E : DerivedCategory (ModuleCat.{u} (Polynomial k)))
    (hE : Nonempty ((derivedTilde (CommRingCat.of (Polynomial k))).obj E ≅
      a.obj ((derivedTilde (CommRingCat.of k)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))))) :
    ¬ Module.Finite (Polynomial k)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Polynomial k)) 0).obj E) := by
  intro hfin
  obtain ⟨e⟩ := hE
  obtain ⟨iso⟩ := derivedTilde_comp_rightAdjoint_derivedQuasicoherentPushforwardIsoDerivedHom
    (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) adjP
  have e2 : (derivedTilde (CommRingCat.of (Polynomial k))).obj E ≅
      (derivedTilde (CommRingCat.of (Polynomial k))).obj
        ((Dualizing.AnyModel.derivedHom.{u, u, u, u, u}
            (Polynomial.C : k →+* Polynomial k)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))) :=
    e ≪≫ iso.app ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))
  have := derivedTilde_isEquivalence (CommRingCat.of (Polynomial k))
  let eh := (DerivedCategory.homologyFunctor (ModuleCat.{u} (Polynomial k)) 0).mapIso
    ((derivedTilde (CommRingCat.of (Polynomial k))).preimageIso e2)
  exact Dualizing.AnyModel.polynomialDerivedHom_not_finite.{u} k
    (finite_of_iso eh hfin)

end AlgebraicGeometry

end
