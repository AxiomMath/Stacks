module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiBaseChange
public import StacksFrontier.Homology.Perfect.FiniteComplexEulerCharacteristic
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalRingStalks
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.PullbackOnRingedSpaces
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeFiniteFree
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.StrictlyPerfectIsKFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ClosedSupportPerfect
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import Mathlib.Topology.LocallyConstant.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Euler characteristic of the derived fibres of a perfect complex

Let `X` be a scheme and `E` a pseudo-coherent object of `D(𝒪_X)`.  Its *derived-fibre Euler
characteristic* sends a point `x` to the alternating sum
`∑ (-1)^i dim_{κ(x)} H^i(E ⊗^L_{𝒪_X} κ(x))` of the derived-fibre Betti numbers of
[Stacks, Tag 0BDI].

For a *perfect* `E` this function is locally constant, which is Tag 0BDJ: locally `E` is a
bounded complex of finite free modules, and there the function takes the single value
`∑ (-1)^i rank(E^i)`.

## Main definitions

* `AlgebraicGeometry.DerivedFibreBetti.chiDerivedFibre` is that alternating sum.
* `AlgebraicGeometry.DerivedFibreBetti.fibreFiniteFreeIso` identifies the derived fibre of
  `𝒪_X^{⊕ n}` with `R^n`.
* `AlgebraicGeometry.DerivedFibreBetti.derivedPullbackQIsoOfKFlat` and
  `AlgebraicGeometry.DerivedFibreBetti.derivedPullbackOpenQIso` compute the derived pullback,
  on a K-flat complex and along an open immersion respectively.

## Main results

* `AlgebraicGeometry.DerivedFibreBetti.isLocallyConstant_chiDerivedFibre`: Tag 0BDJ.
* `AlgebraicGeometry.DerivedFibreBetti.chiDerivedFibre_derivedPullback`: the derived-fibre Euler
  characteristic commutes with base change, inherited degreewise from Tag 0BDI.
* `AlgebraicGeometry.DerivedFibreBetti.derivedFiberBetti_congr` and
  `AlgebraicGeometry.DerivedFibreBetti.chiDerivedFibre_congr`: both are unchanged by an
  isomorphism of the object.
* `AlgebraicGeometry.DerivedFibreBetti.isPseudoCoherent_of_isPerfect`: a perfect object of
  `D(𝒪_X)` on a ringed space is pseudo-coherent, so the Euler characteristic above is defined
  for it.
* `AlgebraicGeometry.DerivedFibreBetti.preservesHomology_moduleSpecΓFunctor`: global sections on
  the spectrum of a field is exact.
* `AlgebraicGeometry.DerivedFibreBetti.kFlat_of_bounded_finiteFree`: a bounded complex of finite
  free `𝒪_X`-modules is K-flat.
* `AlgebraicGeometry.DerivedFibreBetti.exists_chiDerivedFibre_eq_of_bounded_finiteFree`: such a
  complex has constant derived-fibre Euler characteristic.

## Implementation notes

The sum is a `finsum` over all of `ℤ`, which is `0` unless the summand has finite support;
this is the junk-value convention of `Mathlib/Algebra/Homology/EulerCharacteristic`.  Nothing is
lost by it for a perfect object: the computation on a bounded finite free local model shows the
summand is supported in the degrees where that model is nonzero, so the `finsum` is at every
point the finite sum it is meant to be.

The signs are `Int.negOnePow`, matching the `ComplexShape.EulerCharSigns` instance for
`ComplexShape.up ℤ` that `HomologicalComplex.homologyEulerChar` uses, so that the Euler
characteristic of a complex of vector spaces computed there is this alternating sum on the nose.

`derivedFiberBetti` does not use its pseudo-coherence argument, which is why
`derivedFiberBetti_congr` can compare two different objects with two unrelated proofs.  The
argument is kept in the statements here so that they read at the same shape as Tag 0BDI's.

Three spellings of one category meet in the proof of the local computation, and none of the
three can be left to instance search.  `X.Modules` and `StrictlyPerfect.OXMod X.toRingedSpace`
are definitionally equal but have different discrimination keys, so the standard derived
category is seated by hand at the second spelling inside the proof of Tag 0BDJ — as the *same*
term as the one found at the first, so that the two agree wherever both occur.  Likewise the
codomain of the degreewise pullback to `Spec κ(x)` is ascribed to `(Spec κ(x)).Modules`, the
spelling that `AlgebraicGeometry.moduleSpecΓFunctor`'s domain is written at, so that the
additivity and exactness of global sections are found for the complexes the pullback produces.
This is the pattern of
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.presheafIsFlat_of_isDirectSummandOfFiniteFree`.

## References

* [Stacks Project, Tag 0BDJ](https://stacks.math.columbia.edu/tag/0BDJ)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
* [Stacks Project, Tag 0BCJ](https://stacks.math.columbia.edu/tag/0BCJ)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

namespace AlgebraicGeometry.DerivedFibreBetti

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **The derived-fibre Euler characteristic of a pseudo-coherent object of `D(𝒪_X)`.**  Its
value at `x` is the alternating sum `∑ (-1)^i dim_{κ(x)} H^i(E ⊗^L_{𝒪_X} κ(x))` of the
derived-fibre Betti numbers of `E` at `x`. -/
public def chiDerivedFibre (X : Scheme.{u}) (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) : X → ℤ :=
  fun x => ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (derivedFiberBetti X E hE i x : ℤ)

/-- The value of `chiDerivedFibre X E hE` at `x` is the alternating sum
`∑ᶠ i, (-1)^i * derivedFiberBetti X E hE i x`. -/
@[simp]
public theorem chiDerivedFibre_apply (X : Scheme.{u}) (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) (x : X) :
    chiDerivedFibre X E hE x =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (derivedFiberBetti X E hE i x : ℤ) :=
  rfl

/-- Termwise equal Betti-type functions have equal alternating sums. -/
private theorem finsum_negOnePow_mul_congr {a b : ℤ → ℕ} (h : ∀ i, a i = b i) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (a i : ℤ) = ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (b i : ℤ) := by
  simp only [h]

/-- **The derived-fibre Betti functions depend only on the isomorphism class of the object.**
The derived fibre of `E` at `x` is carried to that of `F` by the derived pullback of an
isomorphism `E ≅ F`, and an isomorphism of modules over `κ(x)` preserves dimension. -/
public theorem derivedFiberBetti_congr (X : Scheme.{u})
    {E F : DerivedCategory X.Modules}
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (hF : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) F)
    (e : E ≅ F) (i : ℤ) :
    derivedFiberBetti X E hE i = derivedFiberBetti X F hF i :=
  funext fun x => ((moduleSpecΓFunctor (R := X.residueField x)).mapIso
    ((DerivedCategory.homologyFunctor (Spec (X.residueField x)).Modules i).mapIso
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (X.fromSpecResidueField x).toLRSHom.toShHom).mapIso e))).toLinearEquiv.finrank_eq

/-- **The derived-fibre Euler characteristic depends only on the isomorphism class of the
object.** -/
public theorem chiDerivedFibre_congr (X : Scheme.{u})
    {E F : DerivedCategory X.Modules}
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (hF : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) F)
    (e : E ≅ F) :
    chiDerivedFibre X E hE = chiDerivedFibre X F hF :=
  funext fun x => finsum_negOnePow_mul_congr fun i =>
    congrFun (derivedFiberBetti_congr X hE hF e i) x

/-- **The derived-fibre Euler characteristic commutes with base change.**  For a morphism of
schemes `f : Y ⟶ X` the derived-fibre Euler characteristic of `Lf^* E` is the pullback along `f`
of the derived-fibre Euler characteristic of `E`.

This is Tag 0BDI's base change for each Betti number, summed. -/
public theorem chiDerivedFibre_derivedPullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) :
    chiDerivedFibre Y ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        f.toLRSHom.toShHom).obj E) (isPseudoCoherent_derivedPullback f E hE) =
      chiDerivedFibre X E hE ∘ f.base :=
  funext fun y => finsum_negOnePow_mul_congr fun i =>
    congrFun (derivedFiberBetti_derivedPullback f E hE i) y

/-- **A perfect object of `D(𝒪_X)` is pseudo-coherent.**  A strictly perfect local model is in
particular a strictly perfect approximation in every degree, since it is quasi-isomorphic to the
restricted complex and hence an isomorphism — a fortiori an epimorphism — on all cohomology. -/
public theorem isPseudoCoherent_of_isPerfect {X : RingedSpace.{u, u}}
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X))
    (hE : RingedSpace.IsPerfect.{u, u + 1} E) :
    RingedSpace.IsPseudoCoherent (X := X) E := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  refine ⟨K, fun m x => ?_, ⟨e⟩⟩
  obtain ⟨I, U, hcover, hlocal⟩ := hK
  have hx : x ∈ iSup U := by
    rw [hcover]
    simp
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  obtain ⟨P, hP, g, hg⟩ := hlocal i
  refine ⟨U i, hxi, P, hP, g, fun j _ => ?_, ?_⟩
  · exact (quasiIsoAt_iff_isIso_homologyMap _ j).1 (hg.quasiIsoAt j)
  · have : IsIso (HomologicalComplex.homologyMap g m) :=
      (quasiIsoAt_iff_isIso_homologyMap _ m).1 (hg.quasiIsoAt m)
    infer_instance

/-! ### Global sections on the spectrum of a field -/

/-- Global sections of a sheaf of modules on `Spec R` is additive: it evaluates a morphism on
the open `Spec R` itself, and addition of morphisms is sectionwise. -/
public instance additive_moduleSpecΓFunctor {R : CommRingCat.{u}} :
    (moduleSpecΓFunctor (R := R)).Additive := by
  constructor
  intro A B f g
  ext x
  rfl

/-- **Global sections on the spectrum of a field preserves homology.**  It is the inverse of the
equivalence `AlgebraicGeometry.SpecField.modulesEquiv` between `R`-modules and
`𝒪_{Spec R}`-modules, so it is exact. -/
public theorem preservesHomology_moduleSpecΓFunctor {R : CommRingCat.{u}} (hR : IsField R) :
    (moduleSpecΓFunctor (R := R)).PreservesHomology := by
  have h : (moduleSpecΓFunctor (R := R)).IsEquivalence := by
    rw [← SpecField.modulesEquiv_inverse hR]
    exact (SpecField.modulesEquiv hR).isEquivalence_inverse
  exact Functor.preservesHomologyOfExact _

/-- **The derived fibre of a finite free module is a finite free vector space.**  For a morphism
of ringed spaces `f : Spec R ⟶ X`, the global sections of `f^* (𝒪_X^{⊕ n})` are `R^n`: pullback
carries `𝒪_X^{⊕ n}` to `𝒪_{Spec R}^{⊕ n}`, which is the sheaf associated to `Fin n → R`, whose
global sections are `Fin n → R`. -/
public def fibreFiniteFreeIso {X : RingedSpace.{u, u}} {R : CommRingCat.{u}}
    (f : (Spec R).toRingedSpace ⟶ X) (n : ℕ) :
    (moduleSpecΓFunctor (R := R)).obj
        ((modulePullback f).obj (StrictlyPerfect.finiteFree X n)) ≅
      ModuleCat.of R (Fin n → R) :=
  (moduleSpecΓFunctor (R := R)).mapIso
      (Stacks.StrictlyPerfect.Pullback.modulePullbackFiniteFreeIso f n ≪≫
        Stacks.AffineTilde.finiteFreeIsoTilde R n) ≪≫
    ((tilde.toTildeΓNatIso (R := R)).app (ModuleCat.of R (Fin n → R))).symm

/-! ### Derived pullback of a bounded complex of finite free modules -/

/-- **A bounded complex of finite free `𝒪_X`-modules is K-flat.**  It is bounded above, and each
term, being isomorphic to `𝒪_X^{⊕ n}`, is a direct summand of a finite free module hence flat;
Tag 06YQ on a ringed space concludes. -/
public theorem kFlat_of_bounded_finiteFree {X : RingedSpace.{u, u}}
    (P : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ)
    (hbounded : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (hfree : ∀ i : ℤ, ∃ n : ℕ, Nonempty (P.X i ≅ StrictlyPerfect.finiteFree X n)) :
    RingedSpace.KFlatDerivedPullback.KFlat X P :=
  RingedSpace.KFlatDerivedPullback.kFlat_of_isStrictlyPerfect P
    { bounded := hbounded
      directSummand := fun i => by
        obtain ⟨m, ⟨e⟩⟩ := hfree i
        exact (StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract _).mpr
          ⟨m, ⟨⟨e.hom, e.inv, by simp⟩⟩⟩ }

/-- **On a K-flat complex the derived pullback is the degreewise pullback.**  The canonical
comparison `Lf^* K ⟶ f^* K` of Tag 06YJ is invertible there, and the two localisation
comparisons identify the classes of the complexes with the images of their homotopy classes. -/
public def derivedPullbackQIsoOfKFlat {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (P : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y P) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
        (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  have := Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
    f P hP
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).mapIso
      ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
    asIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≪≫
    DerivedCategory.Qh.mapIso
      (((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app P) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

/-! ### The local computation -/

/-- **The derived-fibre Euler characteristic of a bounded complex of finite free modules** is
`∑ (-1)^i rank(P^i)` at every point.

At a point `x` the derived fibre of the class of `P` is computed by the degreewise pullback of
`P`, because `P` is K-flat; global sections on `Spec κ(x)` turn that into a bounded complex of
`κ(x)`-vector spaces whose `i`-th term has dimension `rank(P^i)`; and for such a complex the
alternating sum of the dimensions of the cohomology is the alternating sum of the dimensions of
the terms. -/
public theorem chiDerivedFibre_eq_of_bounded_finiteFree (X : Scheme.{u})
    (P : CochainComplex (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) ℤ)
    (hbounded : {i : ℤ | ¬ IsZero (P.X i)}.Finite) (n : ℤ → ℕ)
    (hn : ∀ i : ℤ, Nonempty (P.X i ≅ StrictlyPerfect.finiteFree X.toRingedSpace (n i)))
    (hpc : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) (DerivedCategory.Q.obj P))
    (x : X) :
    chiDerivedFibre X (DerivedCategory.Q.obj P) hpc x =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (n i : ℤ) := by
  classical
  let k := X.residueField x
  let f := (X.fromSpecResidueField x).toLRSHom.toShHom
  let G := moduleSpecΓFunctor (R := k)
  -- The codomain of `F` is *ascribed* to `(Spec k).Modules`, the spelling of the category of
  -- `𝒪_{Spec k}`-modules that `G`'s domain is written at.  Ascription is a defeq check at
  -- default transparency, where the two spellings agree; instance search runs at `instances`
  -- transparency, where it does not, and would then not find the additivity of `G` at the
  -- spelling the degreewise pullback produces.
  let F : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace ⥤ (Spec k).Modules := modulePullback f
  have hGa : G.Additive := additive_moduleSpecΓFunctor
  have hFa : F.Additive := modulePullback_additive f
  have hGH : G.PreservesHomology := preservesHomology_moduleSpecΓFunctor (Field.toIsField _)
  let B := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let C := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj B
  let eTerm (i : ℤ) : C.X i ≅ ModuleCat.of k (Fin (n i) → k) :=
    G.mapIso (F.mapIso (hn i).some) ≪≫ fibreFiniteFreeIso f (n i)
  have hfin (i : ℤ) : Module.Finite k (C.X i) :=
    (eTerm i).toLinearEquiv.symm.finiteDimensional
  have hsupp : {i : ℤ | ¬ IsZero (C.X i)}.Finite :=
    hbounded.subset fun i hi hzero => hi (G.map_isZero (F.map_isZero hzero))
  let eD := derivedPullbackQIsoOfKFlat f P
    (kFlat_of_bounded_finiteFree P hbounded fun i => ⟨n i, hn i⟩)
  let eH (i : ℤ) : G.obj ((DerivedCategory.homologyFunctor (Spec k).Modules i).obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
        (DerivedCategory.Q.obj P))) ≅ C.homology i :=
    G.mapIso ((DerivedCategory.homologyFunctor _ i).mapIso eD ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app B) ≪≫
      ((B.sc i).mapHomologyIso G).symm
  calc
    chiDerivedFibre X (DerivedCategory.Q.obj P) hpc x =
        HomologicalComplex.homologyEulerChar C :=
      finsum_negOnePow_mul_congr fun i => (eH i).toLinearEquiv.finrank_eq
    _ = HomologicalComplex.eulerChar C :=
      StacksDraft.Perfect.homologyEulerChar_eq_eulerChar C hfin hsupp
    _ = ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (n i : ℤ) := by
      refine finsum_negOnePow_mul_congr fun i => ?_
      rw [(eTerm i).toLinearEquiv.finrank_eq]
      simp

/-- A bounded complex of finite free modules has constant derived-fibre Euler characteristic. -/
public theorem exists_chiDerivedFibre_eq_of_bounded_finiteFree (X : Scheme.{u})
    (P : CochainComplex (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) ℤ)
    (hbounded : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (hfree : ∀ i : ℤ, ∃ n : ℕ,
      Nonempty (P.X i ≅ StrictlyPerfect.finiteFree X.toRingedSpace n))
    (hpc : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) (DerivedCategory.Q.obj P)) :
    ∃ c : ℤ, ∀ x : X, chiDerivedFibre X (DerivedCategory.Q.obj P) hpc x = c := by
  choose n hn using hfree
  exact ⟨_, chiDerivedFibre_eq_of_bounded_finiteFree X P hbounded n hn hpc⟩

/-! ### Local constancy -/

/-- **Along an open immersion the derived pullback is restriction.**  Pullback along the
inclusion of an open subspace is restriction, hence exact, so it is its own derived functor and
sends the class of a complex to the class of the restricted complex. -/
public def derivedPullbackOpenQIso {X : RingedSpace.{u, u}} (U : Opens X)
    (E₀ : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (X.ofRestrict U.isOpenEmbedding)).obj (DerivedCategory.Q.obj E₀) ≅
      DerivedCategory.Q.obj (RingedSpace.restrictComplex E₀ U) :=
  (SpecField.derivedPullbackMapDerivedIso (X.ofRestrict U.isOpenEmbedding)).app _ ≪≫
    Stacks.Cohomology.ClosedSupportPerfect.derivedRestrictionComplexIso X U E₀

/-- **Stacks 0BDJ.** The derived-fibre Euler characteristic of a perfect object of `D(𝒪_X)` on a
scheme is locally constant.

Near any point, Tag 0BCJ represents `E` by a bounded complex of finite free modules on an open
`V`; base change along the open immersion `V ⟶ X` (Tag 0BDI) identifies the Euler characteristic
on `V` with the restriction of the one on `X`, and on `V` it is the constant
`∑ (-1)^i rank(P^i)`. -/
@[stacks 0BDJ,
  ega "III 7.9.3" "more general",
  sga "6 III 5.4.1" "a) rank, scheme case",
  sga "6 III 5.5" "(i), scheme case"]
public theorem isLocallyConstant_chiDerivedFibre (X : Scheme.{u})
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) E) :
    IsLocallyConstant (chiDerivedFibre X E (isPseudoCoherent_of_isPerfect E hE)) := by
  classical
  -- The two spellings `X.Modules` and `StrictlyPerfect.OXMod X.toRingedSpace` of the category of
  -- `𝒪_X`-modules are definitionally equal, but instance search does not cross them, so the
  -- standard derived category is seated here at the second spelling as well -- as the *same*
  -- term, so that the two agree wherever both occur.
  let hDC : HasDerivedCategory.{u + 1} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) :=
    HasDerivedCategory.standard X.Modules
  have hpc := isPseudoCoherent_of_isPerfect E hE
  obtain ⟨E₀, ⟨e⟩, I, U, hcover, hlocal⟩ :=
    (RingedSpace.hasFiniteLocallyFreeRepresentation_iff_hasFiniteFreeRepresentation E).mp
      ((RingedSpace.isPerfect_iff_hasFiniteLocallyFreeRepresentation E).mp hE)
  have hE0 : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace)
      (DerivedCategory.Q.obj E₀) :=
    RingedSpace.isPerfect_of_hasFiniteFreeRepresentation
      ⟨E₀, ⟨Iso.refl _⟩, I, U, hcover, hlocal⟩
  have hpc0 := isPseudoCoherent_of_isPerfect (DerivedCategory.Q.obj E₀) hE0
  rw [← chiDerivedFibre_congr X hpc0 hpc e, IsLocallyConstant.iff_exists_open]
  intro x
  have hx : x ∈ iSup U := by
    rw [hcover]
    simp
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  obtain ⟨P, hbounded, hfree, g, hg⟩ := hlocal i
  set V : X.Opens := U i
  have hgiso : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).2 hg
  let eModel : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      V.ι.toLRSHom.toShHom).obj (DerivedCategory.Q.obj E₀) ≅ DerivedCategory.Q.obj P :=
    derivedPullbackOpenQIso V E₀ ≪≫ (asIso (DerivedCategory.Q.map g)).symm
  have hpcV : RingedSpace.IsPseudoCoherent (X := V.toScheme.toRingedSpace)
      (DerivedCategory.Q.obj P) := by
    obtain ⟨K, hK, ⟨w⟩⟩ :=
      isPseudoCoherent_derivedPullback V.ι (DerivedCategory.Q.obj E₀) hpc0
    exact ⟨K, hK, ⟨w ≪≫ eModel⟩⟩
  obtain ⟨c, hc⟩ :=
    exists_chiDerivedFibre_eq_of_bounded_finiteFree V.toScheme P hbounded hfree hpcV
  refine ⟨V, V.2, hxi, fun y hy => ?_⟩
  have key (z : X) (hz : z ∈ V) :
      chiDerivedFibre X (DerivedCategory.Q.obj E₀) hpc0 z = c := by
    have hbase := congrFun
      (chiDerivedFibre_derivedPullback V.ι (DerivedCategory.Q.obj E₀) hpc0)
      (⟨z, hz⟩ : V.toScheme)
    refine hbase.symm.trans ?_
    refine Eq.trans ?_ (hc ⟨z, hz⟩)
    exact congrFun (chiDerivedFibre_congr V.toScheme _ hpcV eModel) ⟨z, hz⟩
  exact (key y hy).trans (key x hxi).symm

end AlgebraicGeometry.DerivedFibreBetti

end
