module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomKInjective
public import
  StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.QuasicoherentEquivalenceOverPushforwardRing
public import
  StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPseudoCoherentHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Duality.FiniteTraceDerivedInternalHom
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.HomIntoCoextension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FiniteMorphism
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.Noetherian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf

/-!
# The right adjoint of pushforward along a finite morphism is `R ℰom(f₊ 𝒪_Y, -)`

Let `f : Y ⟶ X` be a finite morphism of schemes with `X` locally Noetherian, let `a` be a right
adjoint of `Rf_* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`, and let `K` be an object of `D_QCoh^+(𝒪_X)`.
[Stacks, Tag 0AX3] is the commutativity of

```
Rf_* a(K)                     --Tr_{f, K}-->   K
    ‖                                          ‖
R ℰom_{𝒪_X}(f₊ 𝒪_Y, K)            -->          K
```

in which the left edge is the identification of [Stacks, Tag 0AX2] and the lower arrow is
induced by `𝒪_X ⟶ f₊ 𝒪_Y`.
`StacksFrontier/AlgebraicGeometry/Duality/FiniteTraceDerivedInternalHom.lean` builds the edges —
the left one as the canonical comparison map
`AlgebraicGeometry.pushforwardRightAdjointToDerivedInternalHom` — and proves that the square
commutes.  This file proves that the left edge is an *isomorphism*, which is what lets it be
drawn as an equality, and registers the remark on the two statements together.

## The proof of invertibility

It is the source's proof of [Stacks, Tag 0AX2], by uniqueness of adjoints.  Write `Φ` for the
equivalence `D_QCoh(𝒪_Y) ≌ D_QCoh(f₊ 𝒪_Y)` of [Stacks, Tag 0AVW] and `H = R ℰom(f₊ 𝒪_Y, -)`
for the right adjoint of restriction of scalars `D(f₊ 𝒪_Y) ⥤ D(𝒪_X)` of [Stacks, Tag 0BV0].
The comparison map is restriction of scalars applied to the transpose
`AlgebraicGeometry.pushforwardTraceTranspose : Φ(a(K)) ⟶ H(K)` of the trace, so it suffices to
show that this transpose is invertible.

* For every `N` in `D_QCoh(𝒪_Y)`, composition with the transpose is a bijection
  `Hom(Φ N, Φ a(K)) ⟶ Hom(Φ N, H(K))`: it is the composite of full faithfulness of `Φ`, the
  adjunction `Rf_* ⊣ a`, the factorisation `Rf_* = (restriction of scalars) ∘ Φ` of
  [Stacks, Tag 0AVW] and the adjunction of [Stacks, Tag 0BV0]
  (`AlgebraicGeometry.bijective_comp_pushforwardTraceTranspose`).
* `H(K)` lies in `D_QCoh(f₊ 𝒪_Y)`.  This is the first assertion of [Stacks, Tag 0AX2]
  (`AlgebraicGeometry.isQuasicoherent_homology_derivedHomSheaf`): after restriction of scalars
  `H(K)` is `R ℰom_{𝒪_X}(f₊ 𝒪_Y, K)`, which has quasi-coherent cohomology by part (1) of
  [Stacks, Tag 0A6H] because `f₊ 𝒪_Y` is pseudo-coherent ([Stacks, Tag 0AVX], with
  [Stacks, Tag 0684] for a finite morphism into a locally Noetherian scheme), and
  quasi-coherence descends along restriction of scalars for an affine morphism
  ([Stacks, Tag 01SB]).
* Every object of `D_QCoh(f₊ 𝒪_Y)` is some `Φ N`, `Φ` being an equivalence, so the transpose is
  an isomorphism in `D_QCoh(f₊ 𝒪_Y)` by Yoneda
  (`AlgebraicGeometry.isIso_pushforwardTraceTranspose`).

## The derived internal Hom out of `f₊ 𝒪_Y`

Part (1) of [Stacks, Tag 0A6H] is stated for the derived internal Hom bifunctor
`Stacks.SheafOfModules.derivedSheafHom`, while `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` is
`AlgebraicGeometry.derivedInternalHomPushforward`, the right derived functor of the underived
internal Hom `ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` of [Stacks, Tag 0BUZ].  The two agree on every object
(`AlgebraicGeometry.derivedSheafHomObjIsoDerivedInternalHomPushforward`), computed on a
K-injective complex `I`: the internal Hom complex out of `f₊ 𝒪_Y[0]` is, by
[Stacks, Tag 0996] part (2) along the morphism of ring sheaves `𝒪_X ⟶ f₊ 𝒪_Y`, the restriction
of scalars of the internal Hom complex over `f₊ 𝒪_Y` out of `f₊ 𝒪_Y[0]` into
`SheafHom_{𝒪_X}(f₊ 𝒪_Y, I)`; the latter is K-injective, so that internal Hom complex computes
the derived internal Hom out of the structure sheaf, which is the identity
(`AlgebraicGeometry.RingedSite.derivedStructureSheafHomNatIso`); and
`SheafHom_{𝒪_X}(f₊ 𝒪_Y, I)` computes `H(I)` by the K-injectivity of `I`.  The ringed site of
the opens of `X` with structure sheaf `f₊ 𝒪_Y` is where [Stacks, Tag 0996] is stated; the
restriction of scalars and the internal Hom there are those of the scheme by `rfl`.

## Main results

* `AlgebraicGeometry.isQuasicoherent_homology_derivedHomSheaf` — `R ℰom(f₊ 𝒪_Y, -)` carries
  `D_QCoh^+(𝒪_X)` into `D_QCoh(f₊ 𝒪_Y)`, for `f` finite and pseudo-coherent.
* `AlgebraicGeometry.isIso_pushforwardTraceTranspose` and
  `AlgebraicGeometry.isIso_pushforwardRightAdjointToDerivedInternalHom_of_pseudoCoherent` — the
  comparison map of [Stacks, Tag 0AX2] is invertible on `D_QCoh^+(𝒪_X)`, for `f` finite and
  pseudo-coherent.
* `AlgebraicGeometry.isIso_pushforwardRightAdjointToDerivedInternalHom_and_comp_evaluation` —
  **[Stacks, Tag 0AX3]**.

## Implementation notes

*Generality.*  The source asks for a finite morphism of Noetherian schemes.  What the proof uses
is that `f` is finite and that `f₊ 𝒪_Y` is pseudo-coherent, and the latter holds as soon as `X`
is locally Noetherian; Noetherianity of `Y` is not used.  The statements are made at that
generality.

*The right adjoint.*  The square is drawn with `Rf_* a(K)` in it and the trace is the counit of
`Rf_* ⊣ a`, so the statements are quantified over a right adjoint `a` of
`Rf_* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` and over an adjunction exhibiting it, at the model
`CategoryTheory.HasDerivedCategory.standard` which the constructions of
`StacksFrontier/AlgebraicGeometry/Duality/FiniteTraceDerivedInternalHom.lean` pin.

*Spellings.*  The category of `𝒪_X`-modules is spelled `SheafOfModules X.ringCatSheaf` on the
scheme side and `SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)` on the
ringed-site side; the two are equal, but their preadditive structures are found along different
paths, so the K-injective complex of the computation above is taken in the ringed-site
spelling and the instances are passed by name where the two meet.

## References

* [Stacks Project, Tag 0AX3](https://stacks.math.columbia.edu/tag/0AX3)
* [Stacks Project, Tag 0AX2](https://stacks.math.columbia.edu/tag/0AX2)
* [Stacks Project, Tag 0AVW](https://stacks.math.columbia.edu/tag/0AVW)
* [Stacks Project, Tag 0BV0](https://stacks.math.columbia.edu/tag/0BV0)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0AVX](https://stacks.math.columbia.edu/tag/0AVX)
* [Stacks Project, Tag 0684](https://stacks.math.columbia.edu/tag/0684)
* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.SheafOfModules (ringedSite)
open Stacks.AlgebraicGeometry.DerivedAffinePushforward (derivedPushforwardOverRing
  derivedPushforwardOverRingCompRestrictScalarsIso derivedQuasicoherentPushforwardOverRing
  isEquivalence_derivedQuasicoherentPushforwardOverRing)
open Stacks.Duality (affineHomQuasiCoherentDerivedPushforward derivedPushforward
  quasiCoherentDerivedCategory)

-- Standard model only: `AlgebraicGeometry.derivedRestrictionOfScalars`,
--   `AlgebraicGeometry.derivedHomSheaf`, `AlgebraicGeometry.derivedInternalHomPushforward`,
--   `Stacks.SheafOfModules.derivedSheafHom`.
attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- `f₊ 𝒪_Y`, as a sheaf of commutative rings on the ringed site of the opens of `X`. -/
abbrev pushforwardStructureSheafCommRing :
    Sheaf (ringedSite X.sheaf).J CommRingCat.{u} :=
  ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous CommRingCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj Y.sheaf

/-- The structure map `𝒪_X ⟶ f₊ 𝒪_Y` of `f`, as a morphism of sheaves of commutative rings. Its
image under the forgetful functor to sheaves of rings is `f.toRingCatSheafHom`, by `rfl`. -/
abbrev pushforwardStructureSheafCommRingHom :
    (ringedSite X.sheaf).O ⟶ pushforwardStructureSheafCommRing f :=
  ⟨f.c⟩

/-- `f₊ 𝒪_Y` in degree zero, as a complex of `𝒪_X`-modules: the restriction of scalars along
`𝒪_X ⟶ f₊ 𝒪_Y` of the structure sheaf complex of `f₊ 𝒪_Y`. -/
abbrev pushforwardStructureComplex :
    CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ :=
  (RingedSite.coeffRestrictComplex (ringedSite X.sheaf) (pushforwardStructureSheafCommRing f)
    (pushforwardStructureSheafCommRingHom f)).obj
    (RingedSite.structureSheafComplex
      (RingedSite.coeffSite (ringedSite X.sheaf) (pushforwardStructureSheafCommRing f)))

/-- `R ℰom(f₊ 𝒪_Y, -)` on a K-injective complex is `ℰom(f₊ 𝒪_Y, -)` applied degreewise. -/
def derivedHomSheafObjIsoOfIsKInjective
    (I : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ) [hI : I.IsKInjective] :
    letI := homSheaf_additive f
    (derivedHomSheaf f).obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj
        (((RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) :=
  let := homSheaf_additive f
  have : IsIso ((derivedHomSheafUnit f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u,
      u + 1, u + 1, u + 1, u + 1, u + 1}
      ((RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) (exists_isKInjective_quasiIso X)).2
      DerivedCategory.Qh (derivedHomSheaf f) (derivedHomSheafUnit f) I hI
  (derivedHomSheaf f).mapIso ((DerivedCategory.quotientCompQhIso _).app I).symm ≪≫
    (asIso ((derivedHomSheafUnit f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm ≪≫
    DerivedCategory.Qh.mapIso
      (((RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app I) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

/-- The structure map `𝒪_X ⟶ f₊ 𝒪_Y`, in the spelling of [Stacks, Tag 0996] part (2). -/
abbrev coeffHomPushforward :=
  RingedSite.coeffHom (ringedSite X.sheaf) (pushforwardStructureSheafCommRing f)
    (pushforwardStructureSheafCommRingHom f)

/-- Coextension of scalars along `𝒪_X ⟶ f₊ 𝒪_Y` is the internal-Hom functor of Tag 0BUZ. -/
def sheafCoextendScalarsIsoHomSheaf :
    Stacks.SheafOfModules.CoextendScalars.coextendScalars.{u} (coeffHomPushforward f) ≅
      RingedSpaceModuleAdjunction.homSheaf (coeffHomPushforward f) :=
  Adjunction.rightAdjointUniq
    (Stacks.SheafOfModules.CoextendScalars.restrictScalars_coextendScalars_adjunction
      (coeffHomPushforward f))
    (RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction (coeffHomPushforward f))

/-- **`R ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` is the derived internal Hom out of `f₊ 𝒪_Y[0]`**, at the class of
a K-injective complex `I`: the derived internal Hom bifunctor of [Stacks, Tag 08DH] at
`f₊ 𝒪_Y[0]` and the right derived functor `AlgebraicGeometry.derivedInternalHomPushforward` of
the internal Hom of [Stacks, Tag 0BUZ] agree.  See the module documentation for the chain of
identifications, whose central step is [Stacks, Tag 0996] part (2). -/
def derivedSheafHomObjIsoDerivedInternalHomPushforward
    (I : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X.sheaf).O)) ℤ)
    [hI : I.IsKInjective] :
    ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
        (op (DerivedCategory.Q.obj (pushforwardStructureComplex f)))).obj
        (DerivedCategory.Q.obj I) ≅
      (derivedInternalHomPushforward f).obj (DerivedCategory.Q.obj I) :=
  let : (RingedSpaceModuleAdjunction.homSheaf (coeffHomPushforward f)).Additive :=
    (RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction
      (coeffHomPushforward f)).right_adjoint_additive
  have : CochainComplex.IsKInjective ((RingedSite.coeffCoextendComplex (ringedSite X.sheaf)
      (pushforwardStructureSheafCommRing f) (pushforwardStructureSheafCommRingHom f)).obj I) :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact
      (RingedSite.coeffCoextend (ringedSite X.sheaf) (pushforwardStructureSheafCommRing f)
        (pushforwardStructureSheafCommRingHom f))
      (RingedSite.coeffRestrict (ringedSite X.sheaf) (pushforwardStructureSheafCommRing f)
        (pushforwardStructureSheafCommRingHom f))
      (Stacks.SheafOfModules.CoextendScalars.restrictScalars_coextendScalars_adjunction
        (coeffHomPushforward f)) I
  RingedSite.derivedSheafHomComparison (ringedSite X.sheaf) (pushforwardStructureComplex f) I ≪≫
    RingedSite.derivedSheafHom_coextendScalarsIso (ringedSite X.sheaf)
      (pushforwardStructureSheafCommRing f) (pushforwardStructureSheafCommRingHom f)
      (RingedSite.structureSheafComplex
        (RingedSite.coeffSite (ringedSite X.sheaf) (pushforwardStructureSheafCommRing f))) I ≪≫
    ((RingedSite.coeffRestrict (ringedSite X.sheaf) (pushforwardStructureSheafCommRing f)
        (pushforwardStructureSheafCommRingHom f)).mapDerivedCategoryFactors.app _).symm ≪≫
    (derivedRestrictionOfScalars f).mapIso
      ((RingedSite.derivedSheafHomComparison
          (RingedSite.coeffSite (ringedSite X.sheaf) (pushforwardStructureSheafCommRing f))
          (RingedSite.structureSheafComplex
            (RingedSite.coeffSite (ringedSite X.sheaf) (pushforwardStructureSheafCommRing f)))
          ((RingedSite.coeffCoextendComplex (ringedSite X.sheaf)
            (pushforwardStructureSheafCommRing f) (pushforwardStructureSheafCommRingHom f)).obj
              I)).symm ≪≫
        (RingedSite.derivedStructureSheafHomNatIso
          (RingedSite.coeffSite (ringedSite X.sheaf) (pushforwardStructureSheafCommRing f))).app
            _ ≪≫
        DerivedCategory.Q.mapIso
          ((NatIso.mapHomologicalComplex (sheafCoextendScalarsIsoHomSheaf f)
            (ComplexShape.up ℤ)).app I) ≪≫
        (derivedHomSheafObjIsoOfIsKInjective (hI := hI) f I).symm) ≪≫
    (derivedHomSheafRestrictionIso f).app _

/-- **[Stacks, Tag 0AVX] for `f₊ 𝒪_Y[0]`**: for a finite pseudo-coherent morphism, `f₊ 𝒪_Y` in
degree zero is a pseudo-coherent object of `D(𝒪_X)`. -/
theorem isPseudoCoherent_pushforwardStructureComplex [IsFinite f] (hf : PseudoCoherent f) :
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace)
      (DerivedCategory.Q.obj (pushforwardStructureComplex f)) :=
  RingedSpace.IsPseudoCoherent.of_iso (X := X.toRingedSpace)
    ((pseudoCoherent_iff_isPseudoCoherent_pushforward_unit f).1 hf)
    (DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (RingedSite.coeffRestrict (ringedSite X.sheaf) (pushforwardStructureSheafCommRing f)
          (pushforwardStructureSheafCommRingHom f)) (ComplexShape.up ℤ) 0).app
        (SheafOfModules.unit _)).symm)

/-- **The first assertion of [Stacks, Tag 0AX2], on cohomology sheaves.** Let `f : Y ⟶ X` be a
finite pseudo-coherent morphism of schemes and `K` an object of `D_QCoh^+(𝒪_X)`.  Then the
cohomology sheaves of `R ℰom(f₊ 𝒪_Y, K)` are quasi-coherent `f₊ 𝒪_Y`-modules.

After restriction of scalars, `R ℰom(f₊ 𝒪_Y, K)` is `R ℰom_{𝒪_X}(f₊ 𝒪_Y, K)` by
[Stacks, Tag 0BV1], which is the derived internal Hom out of the pseudo-coherent object
`f₊ 𝒪_Y[0]` by `AlgebraicGeometry.derivedSheafHomObjIsoDerivedInternalHomPushforward`; its
cohomology sheaves are quasi-coherent by part (1) of [Stacks, Tag 0A6H], and quasi-coherence
descends along restriction of scalars for an affine morphism by [Stacks, Tag 01SB]. -/
theorem isQuasicoherent_homology_derivedHomSheaf [IsFinite f] (hf : PseudoCoherent f)
    (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hK : DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) K) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (pushforwardRingCatSheaf f)) i).obj
      ((derivedHomSheaf f).obj K)).IsQuasicoherent := by
  let Q' := DerivedCategory.Q (C := SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X.sheaf).O))
  let R := Stacks.Injectives.functorialKInjectiveResolution
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X.sheaf).O))
  let K₀ := Q'.objPreimage K
  let I := R.functor.obj K₀
  have : I.IsKInjective := R.isKInjective K₀
  have : QuasiIso (R.inclusion.app K₀) := R.quasiIso K₀
  have hQ : IsIso (Q'.map (R.inclusion.app K₀)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := R.inclusion.app K₀)).2 inferInstance
  let eK : K ≅ Q'.obj I :=
    (Q'.objObjPreimageIso K).symm ≪≫ @asIso _ _ _ _ (Q'.map (R.inclusion.app K₀)) hQ
  have hQC := derivedCategoryB_derivedSheafHom_of_isPseudoCoherent X
    (DerivedCategory.Q.obj (pushforwardStructureComplex f)) K
    (isPseudoCoherent_pushforwardStructureComplex f hf) hK i
  refine (Stacks.AlgebraicGeometry.QcohLimits.affine_isQuasicoherent_restrictScalars_iff f
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (pushforwardRingCatSheaf f)) i).obj
      ((derivedHomSheaf f).obj K))).1 ?_
  refine (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso ?_ hQC
  exact (DerivedCategory.homologyFunctor _ i).mapIso
      (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
          (op (DerivedCategory.Q.obj (pushforwardStructureComplex f)))).mapIso eK ≪≫
        derivedSheafHomObjIsoDerivedInternalHomPushforward f I ≪≫
        ((derivedHomSheafRestrictionIso f).app _).symm ≪≫
        (derivedRestrictionOfScalars f).mapIso ((derivedHomSheaf f).mapIso eK.symm)) ≪≫
    ((Stacks.AlgebraicGeometry.DerivedAffinePushforward.scalarRestriction
      f).mapDerivedCategoryCompHomologyFunctorIso i).app _

section Yoneda

variable [IsAffineHom f]
  {a : quasiCoherentDerivedCategory X ⥤ quasiCoherentDerivedCategory Y}
  (adj : affineHomQuasiCoherentDerivedPushforward f ⊣ a)

/-- **The transpose of the trace induces a bijection on morphisms out of `Φ N`.** For `f`
affine, `N` in `D_QCoh(𝒪_Y)` and `K` in `D_QCoh(𝒪_X)`, composition with
`AlgebraicGeometry.pushforwardTraceTranspose : Φ(a(K)) ⟶ R ℰom(f₊ 𝒪_Y, K)` is a bijection

`Hom(Φ N, Φ a(K)) ⟶ Hom(Φ N, R ℰom(f₊ 𝒪_Y, K))`:

after the adjunction of [Stacks, Tag 0BV0] it is the composite of full faithfulness of the
equivalence `Φ` of [Stacks, Tag 0AVW], the adjunction `Rf_* ⊣ a` and the factorisation of
`Rf_*` through `Φ`.  This is the step of [Stacks, Tag 0AX2] in which both functors are right
adjoint to restriction of scalars. -/
theorem bijective_comp_pushforwardTraceTranspose (K : quasiCoherentDerivedCategory X)
    (N : quasiCoherentDerivedCategory Y) :
    Function.Bijective (fun g : (derivedPushforwardOverRing f).obj N.obj ⟶
        (derivedPushforwardOverRing f).obj (a.obj K).obj =>
      g ≫ pushforwardTraceTranspose f adj K) := by
  have := isEquivalence_derivedQuasicoherentPushforwardOverRing f
  let Φ := derivedQuasicoherentPushforwardOverRing f
  let e := derivedPushforwardOverRingCompRestrictScalarsIso f
  let ψ := ((derivedRestrictionHomSheafAdjunction f).homEquiv
    ((derivedPushforwardOverRing f).obj N.obj) K.obj).symm
  let E : ((derivedPushforwardOverRing f).obj N.obj ⟶
        (derivedPushforwardOverRing f).obj (a.obj K).obj) ≃
      ((derivedRestrictionOfScalars f).obj ((derivedPushforwardOverRing f).obj N.obj) ⟶
        K.obj) :=
    ((ObjectProperty.fullyFaithfulι _).homEquiv (X := Φ.obj N) (Y := Φ.obj (a.obj K))).symm.trans
      ((Functor.FullyFaithful.ofFullyFaithful Φ).homEquiv.symm.trans
        ((adj.homEquiv N K).symm.trans
          ((ObjectProperty.fullyFaithfulι _).homEquiv.trans
            (Iso.homCongr (e.app N.obj) (Iso.refl K.obj)))))
  have key : (fun g => ψ (g ≫ pushforwardTraceTranspose f adj K)) = ⇑E := by
    funext g
    obtain ⟨h, rfl⟩ : ∃ h : N ⟶ a.obj K, (Φ.map h).hom = g :=
      ⟨(Functor.FullyFaithful.ofFullyFaithful Φ).preimage (ObjectProperty.homMk g),
        congrArg (fun k => k.hom)
          ((Functor.FullyFaithful.ofFullyFaithful Φ).map_preimage (ObjectProperty.homMk g))⟩
    have h1 : ψ ((Φ.map h).hom ≫ pushforwardTraceTranspose f adj K) =
        (derivedRestrictionOfScalars f).map (Φ.map h).hom ≫
          (e.inv.app (a.obj K).obj ≫ (adj.counit.app K).hom) :=
      (Adjunction.homEquiv_naturality_left_symm _ _ _).trans
        (congrArg _ (Equiv.symm_apply_apply _ _))
    have h2 : (derivedRestrictionOfScalars f).map (Φ.map h).hom ≫ e.inv.app (a.obj K).obj =
        e.inv.app N.obj ≫ (derivedPushforward f).map h.hom :=
      e.inv.naturality h.hom
    have h3 : E (Φ.map h).hom =
        e.inv.app N.obj ≫ ((derivedPushforward f).map h.hom ≫ (adj.counit.app K).hom) ≫
          𝟙 K.obj := by
      change e.inv.app N.obj ≫ ((adj.homEquiv N K).symm
        ((Functor.FullyFaithful.ofFullyFaithful Φ).preimage
          (ObjectProperty.homMk (Φ.map h).hom))).hom ≫ 𝟙 K.obj = _
      rw [show ObjectProperty.homMk (Φ.map h).hom = Φ.map h from rfl,
        (Functor.FullyFaithful.ofFullyFaithful Φ).preimage_map h, Adjunction.homEquiv_counit]
      rfl
    exact h1.trans (((Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ (adj.counit.app K).hom) h2).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun t => e.inv.app N.obj ≫ t) (Category.comp_id _).symm)))).trans h3.symm)
  have hE : Function.Bijective
      (ψ ∘ fun g => g ≫ pushforwardTraceTranspose f adj K) := by
    rw [show (ψ ∘ fun g => g ≫ pushforwardTraceTranspose f adj K) = ⇑E from key]
    exact E.bijective
  exact (Function.Bijective.of_comp_iff' ψ.bijective _).1 hE

end Yoneda

section Finite

variable [IsFinite f] {a : quasiCoherentDerivedCategory X ⥤ quasiCoherentDerivedCategory Y}
  (adj : affineHomQuasiCoherentDerivedPushforward f ⊣ a)

/-- **The transpose of the trace is an isomorphism** on `D_QCoh^+(𝒪_X)`, for `f` finite and
pseudo-coherent: both its source and its target lie in `D_QCoh(f₊ 𝒪_Y)` — the target by
`AlgebraicGeometry.isQuasicoherent_homology_derivedHomSheaf` — every object of which is `Φ N`
for some `N`, `Φ` being an equivalence ([Stacks, Tag 0AVW]); so Yoneda applies to
`AlgebraicGeometry.bijective_comp_pushforwardTraceTranspose`. -/
theorem isIso_pushforwardTraceTranspose (hf : PseudoCoherent f)
    (K : quasiCoherentDerivedCategory X) (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    IsIso (pushforwardTraceTranspose f adj K) := by
  have := isEquivalence_derivedQuasicoherentPushforwardOverRing f
  let Φ := derivedQuasicoherentPushforwardOverRing f
  let P := DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent
    (Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardRing f.base Y.ringCatSheaf))
  let B' : P.FullSubcategory := ⟨(derivedHomSheaf f).obj K.obj,
    fun i => isQuasicoherent_homology_derivedHomSheaf f hf K.obj ⟨hK, K.property⟩ i⟩
  let t' : Φ.obj (a.obj K) ⟶ B' := ObjectProperty.homMk (pushforwardTraceTranspose f adj K)
  have : IsIso t' := by
    refine isIso_of_yoneda_map_bijective t' fun T => ?_
    let N := Φ.objPreimage T
    let eT : Φ.obj N ≅ T := Φ.objObjPreimageIso T
    let F : ∀ B : P.FullSubcategory, (T ⟶ B) ≃ ((derivedPushforwardOverRing f).obj N.obj ⟶ B.obj) :=
      fun B => (Iso.homCongr eT.symm (Iso.refl _)).trans (ObjectProperty.fullyFaithfulι P).homEquiv
    have hcomm : (F B' ∘ fun x => x ≫ t') =
        (fun g => g ≫ pushforwardTraceTranspose f adj K) ∘ F (Φ.obj (a.obj K)) := by
      funext x
      change eT.hom.hom ≫ (x.hom ≫ pushforwardTraceTranspose f adj K) ≫ 𝟙 B'.obj =
        (eT.hom.hom ≫ x.hom ≫ 𝟙 _) ≫ pushforwardTraceTranspose f adj K
      exact ((congrArg (fun k => eT.hom.hom ≫ k) (Category.comp_id _)).trans
        (Category.assoc _ _ _).symm).trans
          (congrArg (fun k => (eT.hom.hom ≫ k) ≫ pushforwardTraceTranspose f adj K)
            (Category.comp_id x.hom).symm)
    have h : Function.Bijective (F B' ∘ fun x => x ≫ t') := by
      rw [hcomm]
      exact (bijective_comp_pushforwardTraceTranspose f adj K N).comp (F _).bijective
    exact (Function.Bijective.of_comp_iff' (F B').bijective _).1 h
  exact (inferInstance : IsIso (P.ι.map t'))

/-- **The second assertion of [Stacks, Tag 0AX2], read through the comparison map.** For `f`
finite and pseudo-coherent and `K` in `D_QCoh^+(𝒪_X)`, the comparison map
`Rf_* a(K) ⟶ R ℰom_{𝒪_X}(f₊ 𝒪_Y, K)` is an isomorphism. -/
theorem isIso_pushforwardRightAdjointToDerivedInternalHom_of_pseudoCoherent
    (hf : PseudoCoherent f) (K : quasiCoherentDerivedCategory X)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    IsIso (pushforwardRightAdjointToDerivedInternalHom f adj K) := by
  have hτ := isIso_pushforwardTraceTranspose f adj hf K hK
  let e := (derivedPushforwardOverRingCompRestrictScalarsIso f).app (a.obj K).obj ≪≫
    (derivedRestrictionOfScalars f).mapIso (@asIso _ _ _ _ _ hτ) ≪≫
      (derivedHomSheafRestrictionIso f).app K.obj
  exact ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

/-- **The comparison map of [Stacks, Tag 0AX2] is an isomorphism** for `f` finite, `X` locally
Noetherian and `K` in `D_QCoh^+(𝒪_X)`: a finite morphism is of finite type, hence
pseudo-coherent over a locally Noetherian base by [Stacks, Tag 0684]. -/
theorem isIso_pushforwardRightAdjointToDerivedInternalHom [IsLocallyNoetherian X]
    (K : quasiCoherentDerivedCategory X) (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    IsIso (pushforwardRightAdjointToDerivedInternalHom f adj K) :=
  isIso_pushforwardRightAdjointToDerivedInternalHom_of_pseudoCoherent f adj
    ((pseudoCoherent_iff_locallyOfFiniteType f).2 inferInstance) K hK

/-- **Stacks Project, Tag 0AX3 (Remark 48.11.5).** Let `f : Y ⟶ X` be a finite morphism of
schemes with `X` locally Noetherian — in particular a finite morphism of Noetherian schemes —
let `a` be a right adjoint of `Rf_* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`, and let `K` be an object of
`D_QCoh^+(𝒪_X)`.  Then in the square

```
Rf_* a(K)                     --Tr_{f, K}-->   K
    ‖                                          ‖
R ℰom_{𝒪_X}(f₊ 𝒪_Y, K)            -->          K
```

the left edge — the comparison map `Rf_* a(K) ⟶ R ℰom_{𝒪_X}(f₊ 𝒪_Y, K)` of
[Stacks, Tag 0AX2] — is an isomorphism, so that it is the identification the source draws as an
equality, and the square commutes: that isomorphism followed by the map
`R ℰom_{𝒪_X}(f₊ 𝒪_Y, K) ⟶ K` induced by `𝒪_X ⟶ f₊ 𝒪_Y` is the trace map `Tr_{f, K}`, the counit
of `Rf_* ⊣ a`. -/
@[stacks 0AX3 "the whole remark, for every right adjoint a of Rf_* on D_QCoh and every \
adjunction exhibiting it: the comparison map Rf_* a(K) ⟶ R Eom_{O_X}(f_* O_Y, K) of Tag 0AX2 is \
an isomorphism (the left equality of the square) and, followed by the map induced by \
O_X ⟶ f_* O_Y, it is the trace Tr_{f, K}. Stated for f finite and X locally Noetherian, which \
contains the source's finite morphism of Noetherian schemes, and K in D_QCoh^+(O_X)"]
theorem isIso_pushforwardRightAdjointToDerivedInternalHom_and_comp_evaluation
    [IsLocallyNoetherian X] (K : quasiCoherentDerivedCategory X)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    IsIso (pushforwardRightAdjointToDerivedInternalHom f adj K) ∧
      pushforwardRightAdjointToDerivedInternalHom f adj K ≫
          (derivedInternalHomPushforwardEvaluation f).app K.obj =
        (adj.counit.app K).hom :=
  ⟨isIso_pushforwardRightAdjointToDerivedInternalHom f adj K hK,
    pushforwardRightAdjointToDerivedInternalHom_comp_evaluation f adj K⟩

end Finite

end AlgebraicGeometry
