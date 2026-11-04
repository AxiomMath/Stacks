module

public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.DirectImageInDerivedCategory
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardOverRingConservative

/-!
# A complex of quasi-coherent modules computes its own derived direct image over `f_* 𝒪_X`

Let `f : X ⟶ S` be an affine morphism of schemes and let `Φ : D(𝒪_X) ⥤ D(f_* 𝒪_X)` be the
derived direct image over `f_* 𝒪_X` of
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/DerivedPushforwardOverPushforwardRing.lean`,
the functor of [Stacks, Tag 0AVW].  This file proves the analogue over `f_* 𝒪_X` of
[Stacks, Tag 0G9N] for an affine morphism: if `K` is a complex of quasi-coherent `𝒪_X`-modules
then the canonical comparison `f_*K ⟶ ΦK` is invertible, so `Φ` is computed on `K` by the
termwise direct image.  Specialised to a single sheaf this reads

`(f_*𝓕)[0] ≅ Φ(𝓕[0])` in `D(f_* 𝒪_X)` for `𝓕` quasi-coherent,

the identification, **object by object**, of `Φ` with ordinary direct image on the hearts.
Direct image is an equivalence from quasi-coherent `𝒪_X`-modules to quasi-coherent
`f_* 𝒪_X`-modules ([Stacks, Tag 01SB],
`Stacks.AlgebraicGeometry.AffineQcohUnit.isEquivalence_affineQuasicoherentPushforward`, whose
functor is this same `pushforwardModules` restricted to the quasi-coherent objects).  The
isomorphism below is stated at each `𝓕` and its naturality in `𝓕` is not recorded, so what is
proved is the objectwise statement, not an isomorphism of functors.

*How it is proved.*  The content is already available for `Rf_*`: the model-free
`AlgebraicGeometry.quasiIso_modulePushforward_map_of_isAffineHom` says that `f_*` carries a
quasi-isomorphism from a complex of quasi-coherent modules into a K-injective complex to a
quasi-isomorphism of complexes of `𝒪_S`-modules, which by the K-injective criterion of
[Stacks, Tag 070K] is the invertibility of the structure map of `Rf_*` at `K`.  The structure
maps of `Φ` and of `Rf_*` at `K` differ by the derived restriction of scalars, which reflects
isomorphisms (`Stacks.AlgebraicGeometry.DerivedAffinePushforward.scalarRestriction_faithful`),
so the two invertibility statements are the same statement.

The comparison of the two functors is made **in the derived category**, where
`derivedFactorisationComparison` already states it, and not degreewise on complexes: the
degreewise comparison is a true definitional equality that the elaborator does not finish, and
`QuasiIso (f_*s)` read over `f_* 𝒪_X` against the same statement read over `𝒪_S` exhausts the
heartbeats at `isDefEq`.  Stated at the spelling the library's isomorphism already has, the step
costs nothing.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.DerivedAffinePushforward`.

* `isIso_derivedPushforwardOverRingUnit_app_of_isAffineHom` — a complex of quasi-coherent
  `𝒪_X`-modules computes its own `Φ`.
* `derivedPushforwardOverRingSingleIso` — `(f_*𝓕)[0] ≅ Φ(𝓕[0])`, with
  `homologyDerivedPushforwardOverRingSingleIso` and
  `isZero_homology_derivedPushforwardOverRingSingle` its cohomology sheaves.

## Implementation notes

*No `@[stacks 0AVW]` attribute is placed here.*  The tag's first clause is that `Φ` is an
**equivalence** `D_QCoh(𝒪_X) ⥤ D_QCoh(f_* 𝒪_X)`, and an identification on the hearts is not
that: the source's quasi-inverse is the derived pullback `Lg^*` along the morphism of ringed
spaces `g : (X, 𝒪_X) ⟶ (S, f_* 𝒪_X)`, built out of the flatness of `g` in
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/FlatOverPushforwardRing.lean`.  The clause
of the tag whose attribute is placed carries it on
`derivedPushforwardOverRingCompRestrictScalarsIso`.

*All three derived categories are binders*, including `D(𝒪_S)`, which does not appear in any
statement below: the proof passes through the factorisation of `Rf_*`, which mentions it.

## References

* [Stacks Project, Tag 0AVW](https://stacks.math.columbia.edu/tag/0AVW)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe w u

namespace Stacks.AlgebraicGeometry.DerivedAffinePushforward

open Stacks.AlgebraicGeometry.AffineQcohPushforward

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]

/-- **[Stacks, Tag 0G9N] for an affine morphism, over `f_* 𝒪_X`.**  A complex `K` of
quasi-coherent `𝒪_X`-modules — no boundedness assumed — computes its own derived direct image
over `f_* 𝒪_X`: the canonical comparison `f_*K ⟶ ΦK` is invertible.

The K-injective criterion of [Stacks, Tag 070K] turns this into the invertibility in
`D(f_* 𝒪_X)` of the image of one quasi-isomorphism `s : K ⟶ I` into a K-injective complex;
derived restriction of scalars along `𝒪_S ⟶ f_* 𝒪_X` reflects isomorphisms and carries that
image to the image of `s` under `Rf_*`, which is invertible by
`AlgebraicGeometry.quasiIso_modulePushforward_map_of_isAffineHom`. -/
theorem isIso_derivedPushforwardOverRingUnit_app_of_isAffineHom [IsAffineHom f]
    (K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ)
    (hqc : ∀ n : ℤ, (K.X n).IsQuasicoherent) :
    IsIso ((derivedPushforwardOverRingUnit.{w} f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf)
        (ComplexShape.up ℤ)).obj K)) := by
  obtain ⟨I, s, hI, hs⟩ := AlgebraicGeometry.exists_quasiIso_isKInjective_ringCatSheaf X K
  refine (Stacks.SmallDerivedCategory.isIso_rightDerivedUnit_app_quotient_iff
      (AlgebraicGeometry.exists_quasiIso_isKInjective_ringCatSheaf X)
      (pushforwardOverRingToDerivedCategory.{w} f) (derivedPushforwardOverRing.{w} f)
      (derivedPushforwardOverRingUnit.{w} f) s hI hs).2 ?_
  rw [← isIso_iff_of_reflects_iso _ (scalarRestriction f).mapDerivedCategory,
    show (scalarRestriction f).mapDerivedCategory.map
        ((pushforwardOverRingToDerivedCategory.{w} f).map
          ((HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf)
            (ComplexShape.up ℤ)).map s)) =
      (pushforwardOverRingToDerivedCategory.{w} f ⋙
          (scalarRestriction f).mapDerivedCategory).map
        ((HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf)
          (ComplexShape.up ℤ)).map s) from rfl,
    ← NatIso.isIso_map_iff (derivedFactorisationComparison.{w} f)]
  exact (Stacks.SmallDerivedCategory.isIso_mapHomotopyCategoryCompQh_map_quotient_map_iff
    (AlgebraicGeometry.pushforwardSheafOfModules f) s).2
    (AlgebraicGeometry.quasiIso_modulePushforward_map_of_isAffineHom f hqc s hI hs)

/-- **The derived direct image over `f_* 𝒪_X` of a quasi-coherent module along an affine
morphism is its ordinary direct image**: for `f` affine and `𝓕` quasi-coherent,
`(f_*𝓕)[0] ≅ Φ(𝓕[0])` in `D(f_* 𝒪_X)`.  At each `𝓕` this identifies `Φ` on the hearts with the
functor [Stacks, Tag 01SB] proves to be an equivalence; naturality in `𝓕` is not recorded. -/
def derivedPushforwardOverRingSingleIso [IsAffineHom f]
    (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] :
    (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) 0).obj
        ((pushforwardModules.{u} f.base X.ringCatSheaf).obj F) ≅
      (derivedPushforwardOverRing.{w} f).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).obj F) :=
  let P := pushforwardModules.{u} f.base X.ringCatSheaf
  let K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ :=
    (CochainComplex.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).obj F
  have := isIso_derivedPushforwardOverRingUnit_app_of_isAffineHom.{w} f K
    (isQuasicoherent_single_obj_X F)
  (DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) 0).app (P.obj F) ≪≫
    (DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) 0).app F)).symm ≪≫
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))).app
      ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).symm ≪≫
    (DerivedCategory.Qh.mapIso
      ((P.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K)).symm ≪≫
    asIso ((derivedPushforwardOverRingUnit.{w} f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf)
        (ComplexShape.up ℤ)).obj K)) ≪≫
    (derivedPushforwardOverRing.{w} f).mapIso
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} X.ringCatSheaf)).app K ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ
          (SheafOfModules.{u} X.ringCatSheaf) 0).app F).symm)

/-- **The direct image is the only cohomology sheaf of `Φ(𝓕[0])`**: for `f` affine and `𝓕`
quasi-coherent, `H^0(Φ(𝓕[0])) ≅ f_*𝓕` as `f_* 𝒪_X`-modules. -/
def homologyDerivedPushforwardOverRingSingleIso [IsAffineHom f]
    (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] :
    (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) 0).obj
        ((derivedPushforwardOverRing.{w} f).obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).obj F)) ≅
      (pushforwardModules.{u} f.base X.ringCatSheaf).obj F :=
  (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) 0).mapIso
      (derivedPushforwardOverRingSingleIso.{w} f F).symm ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) 0).app
      ((pushforwardModules.{u} f.base X.ringCatSheaf).obj F)

/-- **`Φ` has no higher cohomology on a quasi-coherent sheaf**: `H^i(Φ(𝓕[0])) = 0` for every
`i ≠ 0`, when `f` is affine and `𝓕` is quasi-coherent. -/
theorem isZero_homology_derivedPushforwardOverRingSingle [IsAffineHom f]
    (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] {i : ℤ} (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) i).obj
      ((derivedPushforwardOverRing.{w} f).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).obj F))) :=
  have h : IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) i).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) 0).obj
        ((pushforwardModules.{u} f.base X.ringCatSheaf).obj F))) :=
    (((DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) i).app
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) 0).obj
          ((pushforwardModules.{u} f.base X.ringCatSheaf).obj F))).isZero_iff).2
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0
        ((pushforwardModules.{u} f.base X.ringCatSheaf).obj F) i hi)
  h.of_iso ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) i).mapIso
    (derivedPushforwardOverRingSingleIso.{w} f F).symm)

end Stacks.AlgebraicGeometry.DerivedAffinePushforward

end
