module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.AffineRightAdjointDerivedHom
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness

/-!
# Coherence of the cohomology sheaves of a derived sheafification

Let `R` be a commutative ring and `E` an object of `D(R)`. The degree-`n` cohomology sheaf of the
derived sheafification `E^~` is the sheaf associated to the degree-`n` cohomology module of `E`,
because `(-)^~` is exact; so on `Spec R` with `R` Noetherian that cohomology sheaf is coherent
exactly when the cohomology module is finite. That dictionary is what turns a finiteness statement
about a module into a coherence statement about a sheaf, and it is proved here.

It is then applied to the affine line. Let `k` be a field, `f : 𝔸¹_k ⟶ Spec k` the structure
morphism, and `a` a right adjoint of `Rf_* : D_QCoh(𝒪_{𝔸¹_k}) ⥤ D_QCoh(𝒪_{Spec k})`. The input
`𝒪_{Spec k}` has coherent cohomology sheaves in every degree, while `a(𝒪_{Spec k})` does not have
one in degree zero: by [Stacks, Tag 0A9F] it is `RHom_k(k[X], k)^~`, whose degree-zero cohomology
module is the linear dual `Hom_k(k[X], k)` and is not a finite `k[X]`-module. So the right adjoint
of `Rf_*` does not carry `D_Coh(𝒪_Y)` into `D_Coh(𝒪_X)`, which is [Stacks, Tag 0A9G].

## Main definitions

* `AlgebraicGeometry.homologyDerivedTildeObjIso` — `Hⁿ(E^~) ≅ (Hⁿ E)^~`.
* `AlgebraicGeometry.homologyZeroDerivedTildeSelfIso` — `H⁰((R[0])^~)` is the structure sheaf, so
  the input of the example below really is `𝒪_{Spec R}`.

## Main results

* `AlgebraicGeometry.isCoherent_homologyDerivedTilde_iff` — on `Spec R` for `R` Noetherian, the
  degree-`n` cohomology sheaf of `E^~` is coherent if and only if `Hⁿ E` is a finite `R`-module.
  Its two halves are `AlgebraicGeometry.finite_of_isFiniteType_homologyDerivedTilde` and
  `AlgebraicGeometry.isFiniteType_homologyDerivedTilde_of_finite`, which are stated for finite
  type and so need no Noetherian hypothesis.
* `AlgebraicGeometry.isCoherent_homologyDerivedTildeSingle` — for `M` a finite module the object
  `(M[0])^~` lies in `D_Coh(𝒪_{Spec R})`; in particular `𝒪_{Spec k}` is a coherent input.
* `AlgebraicGeometry.polynomialRightAdjoint_homologyZero_not_isCoherent` —
  [Stacks, Tag 0A9G]: the degree-zero cohomology sheaf of `a(𝒪_{Spec k})` is not coherent.

## Implementation notes

**Where the tag sits, and why the sheaf form carries it.** [Stacks, Tag 0A9G] asserts that the
right adjoint does not map `D_Coh(𝒪_Y)` into `D_Coh(𝒪_X)` — a statement about coherent cohomology
*sheaves*. `AlgebraicGeometry.polynomialRightAdjoint_homologyZero_not_isCoherent` below says that,
and takes only the adjunction as a hypothesis. The module-side
`AlgebraicGeometry.polynomialRightAdjoint_homologyZero_not_finite` in
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/AffineRightAdjointDerivedHom.lean`
states instead that a cohomology *module* is not finite, and carries in addition an object `E` of
`D(k[X])` with a hypothesis identifying its sheafification with `a(𝒪_{Spec k})`. Here that pair is
not needed: derived sheafification is an equivalence
(`AlgebraicGeometry.derivedTilde_isEquivalence`), so the witness is constructed rather than
assumed. The attribute therefore lives below and not there.

**The dependence on [Stacks, Tag 0A9F] is real.** It is tempting to hope that, with derived
sheafification known to be an equivalence, the example could be read off the algebraic obstruction
of `AffineLineExample.lean` directly. It cannot. The obstruction is a statement about
`RHom_k(k[X], -)`, the example is a statement about `a`, and the only bridge between them is the
conclusion of [Stacks, Tag 0A9F],
`AlgebraicGeometry.derivedTilde_comp_rightAdjoint_derivedQuasicoherentPushforwardIsoDerivedHom`.
The equivalence identifies the two *categories* but says nothing about which functor `a` is; that
identification is exactly 0A9F's content, and nothing weaker suffices.

**Finiteness of the module from finite type of its sheaf is not re-proved.** The biconditional
`AlgebraicGeometry.tilde_isFiniteType_iff` ([Stacks, Tag 01PB]) already gives both directions, and
it is what both halves of the dictionary call. In the direction this file needs — coherent sheaf to
finite module — no Noetherian hypothesis and no form of [Stacks, Tag 01XZ] enters either, since
`Stacks.SheafOfModules.IsCoherent.isFiniteType` is a field of the coherence class.

**A composite functor applied to an object is not an application of its factors, for instance
synthesis.** `(F ⋙ G).obj X` and `G.obj (F.obj X)` are definitionally equal, but instance search
will not cross the difference: with `Hⁿ(ι(a.obj (E^~)))` of finite type in the local context, the
transport `Stacks.SheafOfModules.isFiniteType_of_iso` applied to `iso.app K` fails to
synthesize, because `iso.app K` presents its domain as `(derivedTilde R ⋙ a).obj K`. The fix used
below is to launder the isomorphism through a type-ascribed `have` (`e0`), after which both
spellings agree. That transport also needs its universe given explicitly as `.{u}`: inside
`@[expose] public section` its argument is elaborated late enough that the universe would
otherwise default to `0`.
The same phenomenon between `Stacks.SheafOfModules.IsCoherent` and the dot-notation spelling on
`AlgebraicGeometry.Scheme.Modules` is what
`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isCoherent'` exists to cross, and it is
used below for the same reason.

## References

* [Stacks Project, Tag 0A9G](https://stacks.math.columbia.edu/tag/0A9G)
* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
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

universe u

namespace AlgebraicGeometry

variable (R : CommRingCat.{u})

/-! ### Cohomology sheaves of a derived sheafification -/

/-- **The cohomology sheaves of `E^~` are the sheaves associated to the cohomology of `E`.**
Derived sheafification is the derived functor of the exact functor `(-)^~`
(`AlgebraicGeometry.derivedTildeCompι`), and an exact functor commutes with cohomology
(`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`); the isomorphism is the composite of
those two.

The left-hand side is read in `D(𝒪_{Spec R})`, that is after the fully faithful inclusion of the
complexes with quasi-coherent cohomology, because that is where the coherence predicate of a
cohomology sheaf lives. -/
def homologyDerivedTildeObjIso (E : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (Spec R).Modules n).obj
        ((DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.obj
            ((derivedTilde R).obj E)) ≅
      tilde ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj E) :=
  (DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso ((derivedTildeCompι R).app E) ≪≫
    ((tilde.functor R).mapDerivedCategoryHomologyIso n).app E

/-- **A cohomology sheaf of `E^~` of finite type has finite cohomology module.** If the `n`-th
cohomology sheaf of `E^~` on `Spec R` is of finite type, then `Hⁿ E` is a finite `R`-module. -/
theorem finite_of_isFiniteType_homologyDerivedTilde
    (E : DerivedCategory (ModuleCat.{u} R)) (n : ℤ)
    (h : ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
      ((DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.obj
          ((derivedTilde R).obj E))).IsFiniteType) :
    Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj E) :=
  have := h
  (tilde_isFiniteType_iff _).mp
    (Stacks.SheafOfModules.isFiniteType_of_iso.{u} (homologyDerivedTildeObjIso R E n))

/-- **The converse of `AlgebraicGeometry.finite_of_isFiniteType_homologyDerivedTilde`**: a finite
cohomology module gives a cohomology sheaf of finite type, by the other direction of
`AlgebraicGeometry.tilde_isFiniteType_iff`. -/
theorem isFiniteType_homologyDerivedTilde_of_finite
    (E : DerivedCategory (ModuleCat.{u} R)) (n : ℤ)
    (h : Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj E)) :
    ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
      ((DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.obj
          ((derivedTilde R).obj E))).IsFiniteType :=
  have := (tilde_isFiniteType_iff
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj E)).mpr h
  Stacks.SheafOfModules.isFiniteType_of_iso.{u} (homologyDerivedTildeObjIso R E n).symm

/-- **The dictionary between coherence of a cohomology sheaf and finiteness of a cohomology
module.** For `R` Noetherian and `E` an object of `D(R)`, the degree-`n` cohomology sheaf of `E^~`
is coherent if and only if `Hⁿ E` is a finite `R`-module.

Both directions are `AlgebraicGeometry.tilde_isFiniteType_iff` read through
`AlgebraicGeometry.homologyDerivedTildeObjIso`; what the Noetherian hypothesis buys is the passage
between coherence and finite type, through [Stacks, Tag 01XZ] in the form
`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType`. The
quasi-coherence that criterion also wants is free: an object of `D_QCoh` has quasi-coherent
cohomology by definition. -/
theorem isCoherent_homologyDerivedTilde_iff (hR : IsNoetherianRing R)
    (E : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
    ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
        ((DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.obj
            ((derivedTilde R).obj E))).IsCoherent ↔
      Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj E) := by
  have _ : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_Spec.mpr hR
  refine ⟨fun h => finite_of_isFiniteType_homologyDerivedTilde R E n h.isFiniteType,
    fun h => ?_⟩
  have _ := isFiniteType_homologyDerivedTilde_of_finite R E n h
  have _ : ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
      ((DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.obj
          ((derivedTilde R).obj E))).IsQuasicoherent := ((derivedTilde R).obj E).2 n
  exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-! ### A single finite module sheafifies into `D_Coh` -/

/-- **The degree-zero cohomology sheaf of `(R[0])^~` is the structure sheaf.** By
`AlgebraicGeometry.homologyDerivedTildeObjIso` it is the sheaf associated to `H⁰(R[0]) = R`, and
`AlgebraicGeometry.tildeSelf` identifies that with `𝒪_{Spec R}`.

This is what makes the input of the example below the structure sheaf of the base, as the source
of [Stacks, Tag 0A9G] has it. -/
def homologyZeroDerivedTildeSelfIso :
    (DerivedCategory.homologyFunctor (Spec R).Modules 0).obj
        ((DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.obj
            ((derivedTilde R).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
              (ModuleCat.of R R)))) ≅
      SheafOfModules.unit (Spec R).ringCatSheaf :=
  homologyDerivedTildeObjIso R _ 0 ≪≫
    (tilde.functor R).mapIso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).app
        (ModuleCat.of R R)) ≪≫
    tildeSelf

/-- **A finite module, placed in degree zero and sheafified, lies in `D_Coh(𝒪_{Spec R})`**: every
cohomology sheaf of `(M[0])^~` is coherent, for `R` Noetherian and `M` a finite `R`-module.

In degree zero this is `AlgebraicGeometry.isCoherent_homologyDerivedTilde_iff` together with
`H⁰(M[0]) ≅ M`. In every other degree the cohomology of `M[0]` vanishes, so the cohomology sheaf
is a zero object and is coherent by `Stacks.SheafOfModules.isCoherent_of_isZero`; the Noetherian
hypothesis is not used there. -/
theorem isCoherent_homologyDerivedTildeSingle (hR : IsNoetherianRing R)
    (M : ModuleCat.{u} R) (hM : Module.Finite R M) (n : ℤ) :
    ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
      ((DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.obj
          ((derivedTilde R).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)))).IsCoherent := by
  by_cases hn : n = 0
  · subst hn
    refine (isCoherent_homologyDerivedTilde_iff R hR _ 0).mpr ?_
    have e := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).app M
    have _ : Module.Finite R ((𝟭 (ModuleCat.{u} R)).obj M) := hM
    exact Module.Finite.of_surjective e.inv.hom fun m => ⟨e.hom m, by simp⟩
  · have hzC : IsZero ((((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ)
        0).obj M)).homology n) :=
      HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M n hn
    have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) :=
      hzC.of_iso ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).app
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M))
    exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isCoherent'
      (Stacks.SheafOfModules.isCoherent_of_isZero
        (((tilde.functor R).map_isZero hz).of_iso (homologyDerivedTildeObjIso R _ n)))

/-! ### The affine line: the right adjoint does not preserve coherent cohomology -/

/-- **Stacks Project, Tag 0A9G.** Let `k` be a field and `f : 𝔸¹_k ⟶ Spec k` the structure
morphism of the affine line, which is a separated morphism of finite type between Noetherian
schemes (`AlgebraicGeometry.affineLine_isSeparated`,
`AlgebraicGeometry.affineLine_locallyOfFiniteType`, `AlgebraicGeometry.affineLine_quasiCompact`,
`AlgebraicGeometry.affineLine_isLocallyNoetherian` and
`AlgebraicGeometry.isLocallyNoetherian_Spec_of_field`). Let `a` be a right adjoint of
`Rf_* : D_QCoh(𝒪_{𝔸¹_k}) ⥤ D_QCoh(𝒪_{Spec k})`. Then the degree-zero cohomology sheaf of
`a(𝒪_{Spec k})` is not coherent, so `a` does not carry `D_Coh(𝒪_{Spec k})` into
`D_Coh(𝒪_{𝔸¹_k})`.

The input is coherent: it is `𝒪_{Spec k}` in degree zero by
`AlgebraicGeometry.homologyZeroDerivedTildeSelfIso`, and lies in `D_Coh` by
`AlgebraicGeometry.isCoherent_homologyDerivedTildeSingle`. By [Stacks, Tag 0A9F] the output is
`RHom_k(k[X], k)^~`, whose degree-zero cohomology module is the linear dual `Hom_k(k[X], k)`; that
module is the product of countably many copies of `k`, and multiplication by `X` on it is a
surjective endomorphism with nonzero kernel, so it is not finite over the Noetherian ring `k[X]`
(`Dualizing.AnyModel.polynomialDerivedHom_not_finite`, resting on
`Dualizing.polynomialDerivedHom_not_finite`). The passage from that to non-coherence of the sheaf
is `AlgebraicGeometry.finite_of_isFiniteType_homologyDerivedTilde`.

The existence of `a` is not asserted, exactly as the source does not assert it: it comes from
[Stacks, Tag 0A9E] and enters as the hypothesis `adjP`. -/
@[stacks 0A9G]
theorem polynomialRightAdjoint_homologyZero_not_isCoherent (k : Type u) [Field k]
    {a : (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of k)).ringCatSheaf)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent
          (Spec (CommRingCat.of (Polynomial k))).ringCatSheaf)).FullSubcategory}
    (adjP : derivedQuasicoherentPushforward (Spec.map
      (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) ⊣ a) :
    ¬ ((DerivedCategory.homologyFunctor
          (Spec (CommRingCat.of (Polynomial k))).Modules 0).obj
        ((DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent
            (Spec (CommRingCat.of (Polynomial k))).ringCatSheaf)).ι.obj
          (a.obj ((derivedTilde (CommRingCat.of k)).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
              (ModuleCat.of k k)))))).IsCoherent := by
  intro hcoh
  obtain ⟨iso⟩ := derivedTilde_comp_rightAdjoint_derivedQuasicoherentPushforwardIsoDerivedHom
    (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) adjP
  have e0 : a.obj ((derivedTilde (CommRingCat.of k)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))) ≅
      (derivedTilde (CommRingCat.of (Polynomial k))).obj
        ((Dualizing.AnyModel.derivedHom.{u, u, u, u, u}
            (Polynomial.C : k →+* Polynomial k)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))) :=
    iso.app ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))
  have _ := hcoh.isFiniteType
  exact Dualizing.AnyModel.polynomialDerivedHom_not_finite.{u} k
    (finite_of_isFiniteType_homologyDerivedTilde (CommRingCat.of (Polynomial k)) _ 0
      (Stacks.SheafOfModules.isFiniteType_of_iso.{u}
        ((DerivedCategory.homologyFunctor
            (Spec (CommRingCat.of (Polynomial k))).Modules 0).mapIso
          ((DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherent
              (Spec (CommRingCat.of (Polynomial k))).ringCatSheaf)).ι.mapIso e0))))

end AlgebraicGeometry

end
