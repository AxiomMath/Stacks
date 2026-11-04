module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapHelpers
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.BaseChangeExactSequence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.Surjectivity
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.FiberFunctorComplete
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.InertiaDiagram
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GenericPoint
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.DenseOpenFinitelyManyComponents
public import StacksFrontier.AlgebraicGeometry.Morphisms.SpreadingOutFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.RingTheory.Branches.Henselization
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.StalksTestMaps

/-!
# Fundamental groups of irreducible geometrically unibranch schemes

Let `X` be an irreducible, geometrically unibranch scheme and let `U ⊆ X` be a nonempty open
subscheme. Base change of finite étale covers along `U ⟶ X` is fully faithful, and consequently
the canonical homomorphism `π₁(U, ū) ⟶ π₁(X, ū)` of étale fundamental groups is surjective. The
same holds for the generic point `η` of `X`: the map `π₁(η, η̄) ⟶ π₁(X, η̄)` is surjective.

## Main results

* `AlgebraicGeometry.isConnectedPuncturedStrictHenselization_stalk_of_isGeometricallyUnibranchAt`:
  at a non-generic point of an irreducible geometrically unibranch scheme the punctured spectrum
  of every strict henselization of the local ring is connected.
* `AlgebraicGeometry.nonempty_fullyFaithful_finiteEtaleBaseChange_opensι`: base change of finite
  étale covers to a nonempty open of an irreducible geometrically unibranch scheme is fully
  faithful.
* `AlgebraicGeometry.surjective_etaleFundamentalGroupMap_of_section_lifting`: if every connected
  finite étale cover of `X` with a section over `S` has a section, then `π₁(S) ⟶ π₁(X)` is
  surjective.
* `AlgebraicGeometry.surjective_etaleFundamentalGroupMap_opensι_of_isGeometricallyUnibranch`:
  `π₁(U, ū) ⟶ π₁(X, ū)` is surjective for a nonempty open subscheme `U`.
* `AlgebraicGeometry.surjective_galoisToFundamentalGroup_of_isGeometricallyUnibranch`: the map
  `π₁(η, η̄) ⟶ π₁(X, η̄)` is surjective.

## Implementation notes

The hypothesis on strict henselizations is phrased with
`Stacks.StrictHenselization.IsStrictHenselization`, relative to a separable closure of
`(maximalIdeal R).ResidueField`, whereas `IsLocalRing.IsHenselization` is relative to a separable
closure of `IsLocalRing.ResidueField R`; the two residue fields of a local ring are canonically
isomorphic, and the first notion is converted into the second along that isomorphism.

## References

* [Stacks Project, Tag 0BQI](https://stacks.math.columbia.edu/tag/0BQI)
* [Stacks Project, Tag 0BQG](https://stacks.math.columbia.edu/tag/0BQG)
* [Stacks Project, Tag 0BN6](https://stacks.math.columbia.edu/tag/0BN6)
* [Stacks Project, Tag 06DM](https://stacks.math.columbia.edu/tag/06DM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### Reconciling the two residue fields of a local ring -/

/-- A separable closure of the residue field of the localization at the maximal ideal is a
separable closure of the quotient residue field, along the canonical isomorphism. -/
private theorem isSepClosure_residueField_of_isScalarTower
    (R : Type u) [CommRing R] [IsLocalRing R]
    (κsep : Type u) [Field κsep] [Algebra (maximalIdeal R).ResidueField κsep]
    [IsSepClosure (maximalIdeal R).ResidueField κsep]
    [Algebra (ResidueField R) κsep]
    [IsScalarTower (ResidueField R) (maximalIdeal R).ResidueField κsep] :
    IsSepClosure (ResidueField R) κsep := by
  have hbot : Algebra.IsSeparable (ResidueField R) (maximalIdeal R).ResidueField :=
    Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl (ResidueField R))
      (residueFieldEquivMaximalIdealResidueField R) (RingHom.ext fun _ ↦ rfl)
  have htop : Algebra.IsSeparable (maximalIdeal R).ResidueField κsep := IsSepClosure.separable
  exact ⟨IsSepClosure.sep_closed (maximalIdeal R).ResidueField,
    Algebra.IsSeparable.trans (ResidueField R) (maximalIdeal R).ResidueField κsep⟩

/-! ### A strict henselization in the sense of Stacks 04GP is a henselization -/

/-- A strict henselization of `R` with respect to a separable closure `κsep` of
`(maximalIdeal R).ResidueField` is a henselization of `R` with respect to `κsep`, viewed as a
separable closure of `ResidueField R`. -/
private theorem isHenselization_of_isStrictHenselization
    (R : Type u) [CommRing R] [IsLocalRing R]
    (κsep : Type u) [Field κsep] [Algebra (maximalIdeal R).ResidueField κsep]
    [IsSepClosure (maximalIdeal R).ResidueField κsep]
    [Algebra (ResidueField R) κsep]
    [IsScalarTower (ResidueField R) (maximalIdeal R).ResidueField κsep]
    (Rsh : Type u) [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    (h : Stacks.StrictHenselization.IsStrictHenselization R κsep Rsh) :
    IsLocalRing.IsHenselization R κsep Rsh := by
  have := h.isLocalHom
  refine ⟨h.henselian, h.isFilteredColimitEtale,
    h.residueFieldEquiv.trans (residueFieldEquivMaximalIdealResidueField Rsh).symm, fun x ↦ ?_⟩
  have hbase : algebraMap (ResidueField R) κsep (residue R x)
      = algebraMap (maximalIdeal R).ResidueField κsep
        (algebraMap R (maximalIdeal R).ResidueField x) := by
    rw [IsScalarTower.algebraMap_apply (ResidueField R) (maximalIdeal R).ResidueField κsep,
      algebraMap_residueField_residue]
  have hcomp : h.residueFieldEquiv (algebraMap (maximalIdeal R).ResidueField κsep
      (algebraMap R (maximalIdeal R).ResidueField x))
      = Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal Rsh) (algebraMap R Rsh)
          (IsLocalRing.maximalIdeal_comap (algebraMap R Rsh)).symm
          (algebraMap R (maximalIdeal R).ResidueField x) :=
    DFunLike.congr_fun h.residueFieldEquiv_comp (algebraMap R (maximalIdeal R).ResidueField x)
  have hlast : residueFieldEquivMaximalIdealResidueField Rsh (residue Rsh (algebraMap R Rsh x))
      = algebraMap Rsh (maximalIdeal Rsh).ResidueField (algebraMap R Rsh x) :=
    algebraMap_residueField_residue Rsh (algebraMap R Rsh x)
  show (residueFieldEquivMaximalIdealResidueField Rsh).symm
    (h.residueFieldEquiv (algebraMap (ResidueField R) κsep (residue R x)))
      = residue Rsh (algebraMap R Rsh x)
  rw [hbase, hcomp, Ideal.ResidueField.map_algebraMap, ← hlast,
    RingEquiv.symm_apply_apply]

/-! ### The local input of Stacks 0BQG at a geometrically unibranch point -/

/-- A ring with a unique minimal prime has irreducible spectrum. -/
private theorem irreducibleSpace_primeSpectrum_of_unique_minimalPrime
    (R : Type u) [CommRing R] (h : ∃! p : Ideal R, p ∈ minimalPrimes R) :
    IrreducibleSpace (PrimeSpectrum R) := by
  obtain ⟨p, hp, hpu⟩ := h
  have hnil : nilradical R = p := by
    have hrad : (⊥ : Ideal R).radical = nilradical R := rfl
    rw [← hrad, ← Ideal.sInf_minimalPrimes]
    exact le_antisymm (sInf_le hp) (le_sInf fun q hq => (hpu q hq).symm ▸ le_rfl)
  exact PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mpr (hnil ▸ hp.isPrime)

/-- A henselization of the local ring at a non-generic point of an irreducible scheme has a prime
ideal other than its maximal ideal. -/
private theorem exists_isPrime_ne_maximalIdeal_of_isHenselization
    (X : Scheme.{u}) [IrreducibleSpace X] (x : X) (hx : x ≠ genericPoint X)
    (κsep : Type u) [Field κsep] [Algebra (ResidueField (X.presheaf.stalk x)) κsep]
    (Rsh : Type u) [CommRing Rsh] [IsLocalRing Rsh] [Algebra (X.presheaf.stalk x) Rsh]
    [IsLocalRing.IsHenselization (X.presheaf.stalk x) κsep Rsh] :
    ∃ P : Ideal Rsh, P.IsPrime ∧ P ≠ maximalIdeal Rsh := by
  have hηrange : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes x
  obtain ⟨p, hp⟩ := hηrange
  have : p.asIdeal.IsPrime := p.isPrime
  have hpne : p.asIdeal ≠ maximalIdeal (X.presheaf.stalk x) := by
    intro he
    obtain rfl : p = closedPoint (X.presheaf.stalk x) := PrimeSpectrum.ext he
    exact hx (Scheme.fromSpecStalk_closedPoint.symm.trans hp)
  have : Module.FaithfullyFlat (X.presheaf.stalk x) Rsh :=
    IsLocalRing.IsHenselization.faithfullyFlat (L := κsep)
  obtain ⟨P, hP, hPover⟩ :=
    Ideal.exists_isPrime_liesOver_of_faithfullyFlat
      (A := X.presheaf.stalk x) (B := Rsh) p.asIdeal
  refine ⟨P, hP, fun he ↦ hpne ?_⟩
  have hcomap : P.comap (algebraMap (X.presheaf.stalk x) Rsh)
      = maximalIdeal (X.presheaf.stalk x) := by
    rw [he]
    exact maximalIdeal_comap (algebraMap (X.presheaf.stalk x) Rsh)
  exact hPover.over.trans hcomap

/-- Let `X` be an irreducible scheme which is geometrically unibranch at a point `x` other than
its generic point. The punctured spectrum of every strict henselization of `𝒪_{X, x}` is then
connected. -/
@[ega "IV 18.9.7.3" "special case"]
theorem isConnectedPuncturedStrictHenselization_stalk_of_isGeometricallyUnibranchAt
    (X : Scheme.{u}) [IrreducibleSpace X] (x : X)
    (hx : IsGeometricallyUnibranchAt X x) (hxη : x ≠ genericPoint X) :
    IsConnectedPuncturedStrictHenselization (X.presheaf.stalk x) := by
  intro κsep _ _ _ Rsh _ _ _ h
  let : Algebra (ResidueField (X.presheaf.stalk x)) κsep :=
    ((algebraMap (maximalIdeal (X.presheaf.stalk x)).ResidueField κsep).comp
      (algebraMap (ResidueField (X.presheaf.stalk x))
        (maximalIdeal (X.presheaf.stalk x)).ResidueField)).toAlgebra
  have : IsScalarTower (ResidueField (X.presheaf.stalk x))
      (maximalIdeal (X.presheaf.stalk x)).ResidueField κsep :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsSepClosure (ResidueField (X.presheaf.stalk x)) κsep :=
    isSepClosure_residueField_of_isScalarTower (X.presheaf.stalk x) κsep
  have : IsLocalRing.IsHenselization (X.presheaf.stalk x) κsep Rsh :=
    isHenselization_of_isStrictHenselization (X.presheaf.stalk x) κsep Rsh h
  have : IrreducibleSpace (PrimeSpectrum Rsh) :=
    irreducibleSpace_primeSpectrum_of_unique_minimalPrime Rsh
      ((isGeometricallyUnibranch_iff_strictHenselization_has_unique_minimalPrime
        (X.presheaf.stalk x) Rsh κsep).mp
        ((isGeometricallyUnibranch_iff_isGeometricallyUnibranchRing _).2 hx))
  have hne : ({closedPoint Rsh}ᶜ : Set (PrimeSpectrum Rsh)).Nonempty := by
    obtain ⟨P, hP, hPne⟩ :=
      exists_isPrime_ne_maximalIdeal_of_isHenselization X x hxη κsep Rsh
    exact ⟨⟨P, hP⟩, fun hmem ↦ hPne
      (congrArg PrimeSpectrum.asIdeal (Set.eq_of_mem_singleton hmem))⟩
  exact ((IrreducibleSpace.isIrreducible_univ (PrimeSpectrum Rsh)).2.subset_irreducible
    hne (IsLocalRing.isClosed_singleton_closedPoint Rsh).isOpen_compl (fun _ ↦ id)
    (by simp)).isConnected

/-! ### Full faithfulness of base change to a nonempty open -/

/-- A nonempty open subscheme of an irreducible scheme is irreducible. -/
private theorem irreducibleSpace_opens_of_irreducibleSpace (X : Scheme.{u}) [IrreducibleSpace X]
    (U : X.Opens) [Nonempty U] : IrreducibleSpace U.toScheme :=
  Subtype.irreducibleSpace
    ((IrreducibleSpace.isIrreducible_univ X).2.subset_irreducible
      (by simpa using (inferInstance : Nonempty U)) U.isOpen (fun _ ↦ id) (by simp))

/-- A nonempty open subscheme of an irreducible scheme is connected. -/
instance connectedSpace_opens_of_irreducibleSpace (X : Scheme.{u}) [IrreducibleSpace X]
    (U : X.Opens) [Nonempty U] : ConnectedSpace U.toScheme :=
  letI := irreducibleSpace_opens_of_irreducibleSpace X U
  inferInstance

/-- **Base change of finite étale covers to a nonempty open of an irreducible geometrically
unibranch scheme is fully faithful.** -/
@[sga "7 II 2.3.1" "partial"]
theorem nonempty_fullyFaithful_finiteEtaleBaseChange_opensι
    (X : Scheme.{u}) [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)
    (U : X.Opens) [Nonempty U] :
    Nonempty (finiteEtaleBaseChange U.ι).FullyFaithful := by
  have hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite := by
    intro V _
    rcases isEmpty_or_nonempty V with _ | _
    · rw [Set.finite_def]
      exact ⟨⟨∅, fun C ↦ isEmptyElim C.2.1.nonempty.some⟩⟩
    · have : IrreducibleSpace V.toScheme := irreducibleSpace_opens_of_irreducibleSpace X V
      rw [irreducibleComponents_eq_singleton]
      exact Set.finite_singleton _
  have hU : Dense (U : Set X) :=
    U.isOpen.dense (by simpa using (inferInstance : Nonempty U))
  have hηU : genericPoint X ∈ U :=
    (genericPoint_spec X).mem_open_set_iff U.isOpen |>.mpr
      (by simpa using (inferInstance : Nonempty U))
  have hconn : ∀ x : X, x ∉ U →
      IsConnectedPuncturedStrictHenselization (X.presheaf.stalk x) := fun x hxU ↦
    isConnectedPuncturedStrictHenselization_stalk_of_isGeometricallyUnibranchAt X x (hX x)
      (fun hxg ↦ hxU (hxg ▸ hηU))
  exact fullyFaithful_finiteEtaleBaseChange_of_finite_irreducibleComponents X U hfinite hU hconn

/-! ### Surjectivity of the induced homomorphism of fundamental groups -/

/-- A section of a finite étale cover over `S`, compatible with `j : S ⟶ X`, is a morphism from
the terminal cover of `S` to the base change of the cover along `j`. -/
private theorem nonempty_hom_terminal_finiteEtaleBaseChange_of_section
    {S X : Scheme.{u}} (j : S ⟶ X) (V : FiniteEtaleOver X)
    (v : S ⟶ V.left) (hv : v ≫ V.hom = j) :
    Nonempty (finiteEtaleOverTerminal S ⟶ (finiteEtaleBaseChange j).obj V) := by
  have hc : v ≫ V.hom = 𝟙 S ≫ j := by rw [hv, Category.id_comp]
  exact ⟨MorphismProperty.Over.homMk (pullback.lift v (𝟙 S) hc) (pullback.lift_snd _ _ _)⟩

/-- Conversely, a morphism from the terminal cover of `S` to the base change of a cover along
`j : S ⟶ X` gives a section of the cover over `S` compatible with `j`. -/
private theorem exists_section_of_hom_terminal_finiteEtaleBaseChange
    {S X : Scheme.{u}} (j : S ⟶ X) (V : FiniteEtaleOver X)
    (q : finiteEtaleOverTerminal S ⟶ (finiteEtaleBaseChange j).obj V) :
    ∃ v : S ⟶ V.left, v ≫ V.hom = j := by
  obtain ⟨w, hw⟩ : ∃ w : S ⟶ pullback V.hom j, w ≫ pullback.snd V.hom j = 𝟙 S :=
    ⟨q.left, q.w⟩
  refine ⟨w ≫ pullback.fst V.hom j, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hw, Category.id_comp]

/-- For a morphism `j : S ⟶ X` of schemes, surjectivity of the homomorphism induced on fibre
functors, full faithfulness of base change along `j` and lifting of sections of connected finite
étale covers are equivalent. -/
private theorem tfae_surjective_hom_fullyFaithful_section_lifting
    {S X : Scheme.{u}} [ConnectedSpace S] [ConnectedSpace X] (j : S ⟶ X) (x : GeometricPoint S)
    (d : GaloisFunctorData (finiteEtaleFiberFintypeFunctor X (x.map j))
      (finiteEtaleFiberFintypeFunctor S x) (finiteEtaleBaseChange j)
      (finiteEtaleFiberFintypeFunctorBaseChangeIso j x)) :
    List.TFAE [Function.Surjective d.hom,
      Nonempty (finiteEtaleBaseChange j).FullyFaithful,
      ∀ V : FiniteEtaleOver X, PreGaloisCategory.IsConnected V →
        Nonempty (finiteEtaleOverTerminal S ⟶ (finiteEtaleBaseChange j).obj V) →
        Nonempty (finiteEtaleOverTerminal X ⟶ V)] := by
  have _gF : CategoryTheory.IsGaloisCategory (CategoryTheory.setValuedFiberFunctor
      (finiteEtaleFiberFintypeFunctor X (x.map j))) :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor X (x.map j)
  have _gF' : CategoryTheory.IsGaloisCategory (CategoryTheory.setValuedFiberFunctor
      (finiteEtaleFiberFintypeFunctor S x)) :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor S x
  have hs : IsTerminal (finiteEtaleOverTerminal X) := MorphismProperty.Over.mkIdTerminal _ _
  have hs' : IsTerminal (finiteEtaleOverTerminal S) := MorphismProperty.Over.mkIdTerminal _ _
  have hH := exactFunctor_finiteEtaleBaseChange j x
  have : PreservesFiniteLimits (finiteEtaleBaseChange j) := hH.1
  have h := CategoryTheory.surjective_inducedHom_tfae _ _ (finiteEtaleBaseChange j) hH _ d
    (finiteEtaleOverTerminal X) (finiteEtaleOverTerminal S) hs hs'
    (hs.isTerminalObj (finiteEtaleBaseChange j) (finiteEtaleOverTerminal X))
  tfae_have 1 ↔ 2 := h.out 1 2
  tfae_have 2 ↔ 3 := h.out 2 4
  tfae_finish

/-- **Lifting sections of connected covers gives a surjection of étale fundamental groups.** Let
`j : S ⟶ X` be a morphism of connected schemes. If every connected finite étale cover of `X` whose
base change along `j` has a section has a section itself, then `π₁(S, x) ⟶ π₁(X, x)` is
surjective. -/
theorem surjective_etaleFundamentalGroupMap_of_section_lifting
    {S X : Scheme.{u}} [ConnectedSpace S] [ConnectedSpace X] (j : S ⟶ X)
    (x : GeometricPoint S)
    (hlift : ∀ V : FiniteEtaleOver X, PreGaloisCategory.IsConnected V →
      Nonempty (finiteEtaleOverTerminal S ⟶ (finiteEtaleBaseChange j).obj V) →
      Nonempty (finiteEtaleOverTerminal X ⟶ V)) :
    Function.Surjective (etaleFundamentalGroupMap j x) := by
  let d := CategoryTheory.galoisFunctorDataOfFiberIso
    (finiteEtaleFiberFintypeFunctor X (x.map j)) (finiteEtaleFiberFintypeFunctor S x)
    (finiteEtaleBaseChange j) (finiteEtaleFiberFintypeFunctorBaseChangeIso j x)
  have hdsurj : Function.Surjective d.hom :=
    ((tfae_surjective_hom_fullyFaithful_section_lifting j x d).out 1 3).mpr hlift
  intro ρ
  obtain ⟨σ, hσ⟩ := hdsurj ((autMulEquivEtaleFundamentalGroup X (x.map j)).symm ρ)
  refine ⟨autMulEquivEtaleFundamentalGroup S x σ, ?_⟩
  rw [← autMulEquivEtaleFundamentalGroup_galoisFunctorData_hom j x d σ, hσ,
    MulEquiv.apply_symm_apply]

/-- **Full faithfulness of base change lets sections of connected covers be lifted.** If base
change of finite étale covers along a morphism `j : S ⟶ X` of connected schemes is fully faithful,
a connected finite étale cover of `X` whose base change along `j` has a section has a section. -/
theorem nonempty_hom_terminal_of_nonempty_fullyFaithful
    {S X : Scheme.{u}} [ConnectedSpace S] [ConnectedSpace X] (j : S ⟶ X)
    (x : GeometricPoint S)
    (hff : Nonempty (finiteEtaleBaseChange j).FullyFaithful)
    (V : FiniteEtaleOver X) (hV : PreGaloisCategory.IsConnected V)
    (hsec : Nonempty (finiteEtaleOverTerminal S ⟶ (finiteEtaleBaseChange j).obj V)) :
    Nonempty (finiteEtaleOverTerminal X ⟶ V) := by
  have hlift := ((tfae_surjective_hom_fullyFaithful_section_lifting j x
    (CategoryTheory.galoisFunctorDataOfFiberIso _ _ _ _)).out 2 3).mp hff
  exact hlift V hV hsec

/-- **Full faithfulness of base change gives a surjection of étale fundamental groups.** -/
theorem surjective_etaleFundamentalGroupMap_of_nonempty_fullyFaithful
    {S X : Scheme.{u}} [ConnectedSpace S] [ConnectedSpace X] (j : S ⟶ X)
    (x : GeometricPoint S)
    (hff : Nonempty (finiteEtaleBaseChange j).FullyFaithful) :
    Function.Surjective (etaleFundamentalGroupMap j x) :=
  surjective_etaleFundamentalGroupMap_of_section_lifting j x
    (nonempty_hom_terminal_of_nonempty_fullyFaithful j x hff)

/-- Let `X` be an irreducible, geometrically unibranch
scheme, let `U ⊆ X` be a nonempty open subscheme and let `ū` be a geometric point of `U`. The
canonical homomorphism

```
π₁(U, ū) ⟶ π₁(X, ū)
```

of étale fundamental groups is surjective. Equivalently, every connected finite étale cover of `X`
stays connected over `U`. -/
@[stacks 0BQI "the claim for a nonempty open subscheme, that π₁(U, ū) → π₁(X, ū) is surjective; \
the claim for the generic point is \
`surjective_galoisToFundamentalGroup_of_isGeometricallyUnibranch`"]
theorem surjective_etaleFundamentalGroupMap_opensι_of_isGeometricallyUnibranch
    (X : Scheme.{u}) [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)
    (U : X.Opens) [Nonempty U] (x : GeometricPoint U.toScheme) :
    Function.Surjective (etaleFundamentalGroupMap U.ι x) :=
  surjective_etaleFundamentalGroupMap_of_nonempty_fullyFaithful U.ι x
    (nonempty_fullyFaithful_finiteEtaleBaseChange_opensι X hX U)

/-! ### The generic point -/

/-- The spectrum of the local ring of an irreducible scheme at its generic point has at most one
point. -/
private theorem subsingleton_spec_stalk_genericPoint (X : Scheme.{u}) [IrreducibleSpace X] :
    Subsingleton (Spec (X.presheaf.stalk (genericPoint X))) := by
  have hmap (z : Spec (X.presheaf.stalk (genericPoint X))) :
      X.fromSpecStalk (genericPoint X) z = genericPoint X := by
    have hz : X.fromSpecStalk (genericPoint X) z
        ∈ Set.range (X.fromSpecStalk (genericPoint X)) := ⟨z, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hz
    exact (hz.antisymm (genericPoint_specializes _)).eq
  exact ⟨fun a b ↦ (X.fromSpecStalk (genericPoint X)).isEmbedding.injective
    ((hmap a).trans (hmap b).symm)⟩

/-- For an irreducible scheme `X` with generic point `η`, the morphism
`Spec κ(η) ⟶ Spec 𝒪_{X, η}` is a universal homeomorphism. -/
private theorem universalHomeomorphism_specMap_residue_genericPoint (X : Scheme.{u})
    [IrreducibleSpace X] :
    UniversalHomeomorphism (Spec.map (X.residue (genericPoint X))) := by
  have : IsClosedImmersion (Spec.map (X.residue (genericPoint X))) := inferInstance
  have := subsingleton_spec_stalk_genericPoint X
  refine (universalHomeomorphism_iff_integral_universallyInjective_surjective _).2
    ⟨inferInstance, inferInstance, ⟨fun z ↦ ?_⟩⟩
  obtain ⟨w⟩ : Nonempty (Spec (X.residueField (genericPoint X))) := inferInstance
  exact ⟨w, Subsingleton.elim _ _⟩

/-- A `κ(η)`-point of an étale scheme over an irreducible scheme lifts to the local ring at the
generic point. -/
private theorem exists_lift_fromSpecStalk_of_etale (X : Scheme.{u}) [IrreducibleSpace X]
    {W : Scheme.{u}} (p : W ⟶ X) [Etale p]
    (σ : Spec (X.residueField (genericPoint X)) ⟶ W)
    (hσ : σ ≫ p = X.fromSpecResidueField (genericPoint X)) :
    ∃ φ : Spec (X.presheaf.stalk (genericPoint X)) ⟶ W,
      φ ≫ p = X.fromSpecStalk (genericPoint X) := by
  have := universalHomeomorphism_specMap_residue_genericPoint X
  have hcond : σ ≫ p = Spec.map (X.residue (genericPoint X)) ≫
      X.fromSpecStalk (genericPoint X) := hσ.trans rfl
  have hs : pullback.lift σ (Spec.map (X.residue (genericPoint X))) hcond ≫
      pullback.snd p (X.fromSpecStalk (genericPoint X))
      = Spec.map (X.residue (genericPoint X)) := pullback.lift_snd _ _ _
  obtain ⟨τ, ⟨hτ, -⟩, -⟩ := Stacks.Etale.existsUnique_section_of_universalHomeomorphism
    (Spec.map (X.residue (genericPoint X)))
    (pullback.snd p (X.fromSpecStalk (genericPoint X))) _ hs
  refine ⟨τ ≫ pullback.fst p (X.fromSpecStalk (genericPoint X)), ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hτ, Category.id_comp]

/-- A section of a finite étale cover over the generic point extends to a section over an open
neighbourhood of the generic point. -/
private theorem exists_opens_section_of_genericPoint_section (X : Scheme.{u})
    [IrreducibleSpace X] (V : FiniteEtaleOver X)
    (σ : Spec (X.residueField (genericPoint X)) ⟶ V.left)
    (hσ : σ ≫ V.hom = X.fromSpecResidueField (genericPoint X)) :
    ∃ (U : X.Opens) (_ : genericPoint X ∈ U) (f : U.toScheme ⟶ V.left), f ≫ V.hom = U.ι := by
  have : IsFinite V.hom := V.prop.1
  have : Etale V.hom := V.prop.2
  have : LocallyOfFinitePresentation V.hom :=
    ((Etale.iff_flat_and_formallyUnramified (f := V.hom)).mp inferInstance).2.2
  obtain ⟨φ, hφ⟩ := exists_lift_fromSpecStalk_of_etale X V.hom σ hσ
  obtain ⟨U, hηU, f, -, hf⟩ :=
    spread_out_of_locallyOfFinitePresentation' (𝟙 X) V.hom φ (by rw [hφ, Category.comp_id])
  exact ⟨U, hηU, f, by rw [hf, Category.comp_id]⟩

/-- Let `X` be an irreducible, geometrically unibranch scheme with generic point `η`. The
homomorphism of étale fundamental groups induced by `Spec κ(η) ⟶ X` is surjective. -/
@[sga "1 V 8.2" "more general"]
theorem surjective_etaleFundamentalGroupMap_fromSpecResidueField_of_isGeometricallyUnibranch
    (X : Scheme.{u}) [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)
    (x : GeometricPoint (Spec (X.residueField (genericPoint X)))) :
    Function.Surjective
      (etaleFundamentalGroupMap (X.fromSpecResidueField (genericPoint X)) x) := by
  refine surjective_etaleFundamentalGroupMap_of_section_lifting _ x fun V hV hsec ↦ ?_
  obtain ⟨σ, hσ⟩ := exists_section_of_hom_terminal_finiteEtaleBaseChange _ V hsec.some
  obtain ⟨U, hηU, f, hf⟩ := exists_opens_section_of_genericPoint_section X V σ hσ
  have : Nonempty U := ⟨⟨genericPoint X, hηU⟩⟩
  exact nonempty_hom_terminal_of_nonempty_fullyFaithful U.ι
    (AlgebraicGeometry.Scheme.algClosedPoint U.toScheme ⟨genericPoint X, hηU⟩)
    (nonempty_fullyFaithful_finiteEtaleBaseChange_opensι X hX U) V hV
    (nonempty_hom_terminal_finiteEtaleBaseChange_of_section U.ι V f hf)

/-- Let `X` be an irreducible, geometrically unibranch
scheme with function field `K = κ(η)` at its generic point `η`, let `L` be a separable closure of
`K` and let `Ω` be an algebraically closed algebraic extension of `K` containing `L`. The
canonical continuous homomorphism

```
Gal(L / K) = π₁(η, η̄) ⟶ π₁(X, η̄)
```

is surjective. -/
@[stacks 0BQI "the claim for the generic point, that the map π₁(η, η̄) → π₁(X, η̄) of Tag 0BQH is \
surjective; the claim for a nonempty open subscheme is \
`surjective_etaleFundamentalGroupMap_opensι_of_isGeometricallyUnibranch`",
  sga "1 V 8.2" "special case"]
theorem surjective_galoisToFundamentalGroup_of_isGeometricallyUnibranch
    (X : Scheme.{u}) [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)
    (L Ω : Type u) [Field L] [Field Ω]
    [Algebra (X.residueField (genericPoint X)) L]
    [IsSepClosure (X.residueField (genericPoint X)) L]
    [Algebra L Ω] [Algebra (X.residueField (genericPoint X)) Ω]
    [IsScalarTower (X.residueField (genericPoint X)) L Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic (X.residueField (genericPoint X)) Ω] :
    Function.Surjective (galoisToFundamentalGroup X L Ω) := by
  intro ρ
  obtain ⟨τ, hτ⟩ :=
    surjective_etaleFundamentalGroupMap_fromSpecResidueField_of_isGeometricallyUnibranch X hX
      (algebraicClosureGeometricPoint (X.residueField (genericPoint X)) Ω) ρ
  obtain ⟨g, rfl⟩ :=
    (galoisEquivEtaleFundamentalGroup (X.residueField (genericPoint X)) L Ω).surjective τ
  exact ⟨g, hτ⟩

end AlgebraicGeometry

end
