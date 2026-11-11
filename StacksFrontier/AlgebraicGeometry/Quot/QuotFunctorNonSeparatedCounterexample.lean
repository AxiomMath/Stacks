module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Examples.Scheme.DoubledClosedPointPowerSeries
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertQuotFunctorEquality
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorModelSmall
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineFinitePresentationFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.Deformation.Artin.FormalObject.ApproximationEssSurj
public import StacksFrontier.Deformation.Artin.FormalObject.Realization
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFromQuotAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.QuotToCoherentRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAlgebraicFromExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalGenerationBound

/-!
# Quot and Coh of a non-separated morphism need not be algebraic

Let `k` be a field, `S = Spec k⟦t⟧` and let `X` be two copies of `S` glued along the generic
point `D(t)` (`Stacks.Examples.doubledClosedPoint`). The structure morphism `f : X ⟶ S` is of
finite presentation and flat but not separated. This file shows that, read as algebraic spaces
over `S` in a big fppf site,

* no model of the Quot functor `Quot_{𝒪_X/X/S}` (Stacks 09TR) is an algebraic space, so Stacks
  09TU fails without the separatedness hypothesis;
* the stack `Coh_{X/S}` (Stacks 08KB) is not an algebraic stack, so Stacks 09DS and 08WC fail
  without the separatedness hypothesis.

These are parts (3) and (2) of Stacks 0ARF.

## Main results

* `AlgebraicGeometry.Space.exists_quotSituation_not_isAlgebraicSpace`: a Quot situation of finite
  presentation, flat and not separated, with `F` of finite presentation, whose Quot functor has a
  model but no model which is an algebraic space.
* `AlgebraicGeometry.Space.exists_coherentSituation_not_isAlgebraicStack`: a coherent situation of
  finite presentation, flat and not separated, whose stack of coherent sheaves is not algebraic.

## Implementation notes

The proof is the source's. Over `T_n = Spec k⟦t⟧/(t^{n+1})` the section through the first copy
of the closed point cuts out a closed subscheme of `X_{T_n}` isomorphic to `T_n`; read through
Stacks 0D00 (`AlgebraicGeometry.Space.hilbertPresheafIsoQuotSitePresheaf`) these form a formal
object of the category fibred in sets of any model of `Quot_{𝒪_X/X/S}`. If the model were an
algebraic space, its category would be an algebraic stack
(`AlgebraicGeometry.Stack.isAlgebraicStack_fibredCategory`) and the formal object would be
effective (Stacks 07X8, `Deformation.Artin.FormalObject.isEffective_of_isAlgebraicStack`), giving
a closed subscheme `W ⊆ X` which restricts to the given one over every `T_n`. By Krull's
intersection theorem `W` contains the first copy of `Spec k⟦t⟧`, hence its closure, which is all
of `X`; as `X` is reduced, `W = X`. But then the restriction of `W` to `T_0` contains both copies
of the closed point, while the given one contains only the first. This is axiom [4] of Artin's
axioms failing, as in the source.

For `Coh_{X/S}`: the source deduces its non-algebraicity from part (1). Here it is deduced from
the Quot statement instead, by `AlgebraicGeometry.Space.QuotSitePresheafModel.isAlgebraicSpace_of_homRepresentations`:
the relative Hom functors of Stacks 08K6 are algebraic spaces with no separatedness hypothesis, so
algebraicity of `Coh_{X/S}` would make every model of `Quot_{𝒪_X/X/S}` an algebraic space.

The witness is the spectrum of `k⟦t⟧` with its closed point doubled rather than the source's
`Spec k⟦t⟧[x]` with its origin doubled; the statements are existential and both are
counterexamples for the same reason.

## References

* [Stacks Project, Tag 0ARF](https://stacks.math.columbia.edu/tag/0ARF)
* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] CategoryTheory.catToReflQuiver

namespace AlgebraicGeometry.Space.QuotNonSeparated

universe u

open Stacks.Examples

variable (k : Type u) [Field k]

/-- The base `S = Spec k⟦t⟧`. -/
abbrev base : Scheme.{u} := Spec (.of (PowerSeries k))

/-- The doubled closed point `X`. -/
abbrev space : Scheme.{u} := (doubledClosedPoint k).total

/-- The structure morphism `X ⟶ S`. -/
abbrev structureMap : space k ⟶ base k := (doubledClosedPoint k).proj

instance : _root_.AlgebraicGeometry.IsLocallyNoetherian (space k) :=
  LocallyOfFiniteType.isLocallyNoetherian (structureMap k)

instance : CompactSpace (space k) := by
  have : CompactSpace (base k) := PrimeSpectrum.compactSpace
  exact (quasiCompact_iff_compactSpace (structureMap k)).mp inferInstance

instance : QuasiSeparated (structureMap k) := by
  have : _root_.AlgebraicGeometry.IsNoetherian (space k) := {}
  infer_instance

instance : LocallyOfFinitePresentation (structureMap k) :=
  (doubledClosedPoint k).proj_prop _
    (HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation))
    inferInstance

theorem finitePresentation_structureMap : FinitePresentation (structureMap k) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

variable (B : BigFppfSite.{u}) (hS : B.Contains (base k))

include hS in
theorem contains_space : B.Contains (space k) :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (structureMap k) hS

/-- `X` as an object of the big fppf site of `S`. -/
abbrev spaceObj : BigFppfOver B (base k) hS :=
  Over.mk (ObjectProperty.homMk (X := B.obj (contains_space k B hS)) (Y := B.obj hS)
    (structureMap k))

/-- `X ⟶ S` as a morphism of the big fppf site of `S`. -/
abbrev structureObjMap : spaceObj k B hS ⟶ baseTerminal B (base k) hS :=
  Over.homMk (ObjectProperty.homMk (structureMap k)) (by rfl)

/-- `X` as an algebraic space over `S`. -/
abbrev spaceAlg : AlgebraicSpaces B (base k) hS :=
  ⟨yoneda.obj (spaceObj k B hS), isAlgebraicSpace_yoneda B _ hS _⟩

/-- `X ⟶ S` as a morphism of algebraic spaces over `S`. -/
abbrev structureAlgMap : spaceAlg k B hS ⟶ terminalSpace B (base k) hS :=
  ObjectProperty.homMk (yoneda.map (structureObjMap k B hS))

theorem isFinitePresentation_structureAlgMap :
    IsFinitePresentation B (base k) hS (structureAlgMap k B hS).hom :=
  isFinitePresentation_yoneda_map B (base k) hS (structureObjMap k B hS)
    (finitePresentation_structureMap k)

theorem not_isSeparated_structureAlgMap :
    ¬ IsSeparated B (base k) hS (structureAlgMap k B hS).hom := fun h =>
  not_isSeparated_doubledClosedPoint_proj k
    ((isSeparated_yoneda_map_iff B (base k) hS (structureObjMap k B hS)).mp h)

/-- The Quot situation `Quot_{𝒪_X/X/S}`. -/
abbrev quotSituation : QuotSituation B (base k) hS :=
  structureSheafQuotSituation (structureAlgMap k B hS) (isFinitePresentation_structureAlgMap k B hS)

open Deformation.Artin

/-! ### The formal base `k⟦t⟧` and its truncations -/

/-- `k⟦t⟧` as a complete local base over `S = Spec k⟦t⟧`, with the identity as structure
morphism. -/
abbrev formalBase : FormalBase (base k) where
  R := PowerSeries k
  noetherian := inferInstance
  complete := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  toS := 𝟙 _
  residueLocallyFiniteType := by
    have : _root_.AlgebraicGeometry.IsClosedImmersion (adicThickeningι (PowerSeries k)
        (IsLocalRing.maximalIdeal (PowerSeries k)) 0) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    rw [Category.comp_id]
    infer_instance
  residueQuasiCompact := by
    have : _root_.AlgebraicGeometry.IsClosedImmersion (adicThickeningι (PowerSeries k)
        (IsLocalRing.maximalIdeal (PowerSeries k)) 0) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    rw [Category.comp_id]
    infer_instance

include hS in
theorem contains_truncation (n : ℕ) : B.Contains ((formalBase k).truncation n) :=
  truncationContains B (base k) (formalBase k) hS n

/-- The truncation `Spec k⟦t⟧/(t^{n+1})` as an object of the site. -/
abbrev truncObj (n : ℕ) : BigFppfOver B (base k) hS :=
  truncationOver B (base k) hS (formalBase k) (contains_truncation k B hS) n

/-- `Spec k⟦t⟧` itself as an object of the site. -/
abbrev fullObj : BigFppfOver B (base k) hS :=
  baseOver B (base k) hS (formalBase k) hS

/-- The spectrum of a quotient of a ring by a power of a maximal ideal has a single point. -/
theorem subsingleton_primeSpectrum_quotient_pow {R : Type u} [CommRing R] (I : Ideal R)
    [I.IsMaximal] (n : ℕ) : Subsingleton (PrimeSpectrum (R ⧸ I ^ n)) := by
  have heq (p : PrimeSpectrum (R ⧸ I ^ n)) :
      (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ n)) p).asIdeal = I := by
    apply (Ideal.IsMaximal.eq_of_le ‹I.IsMaximal›
      (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ n)) p).isPrime.ne_top _).symm
    apply Ideal.IsPrime.le_of_pow_le (n := n)
    intro x hx
    change Ideal.Quotient.mk (I ^ n) x ∈ p.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Ideal.zero_mem _
  refine ⟨fun p q => ?_⟩
  apply PrimeSpectrum.comap_injective_of_surjective
    (Ideal.Quotient.mk (I ^ n)) Ideal.Quotient.mk_surjective
  exact PrimeSpectrum.ext ((heq p).trans (heq q).symm)

instance subsingleton_truncObj (n : ℕ) :
    Subsingleton ((BigFppfOver.toScheme B (base k) hS).obj (truncObj k B hS n)) :=
  subsingleton_primeSpectrum_quotient_pow (IsLocalRing.maximalIdeal (PowerSeries k)) (n + 1)

/-- The unique point of a truncation maps to the closed point of `Spec k⟦t⟧`. -/
theorem adicThickeningι_apply (n : ℕ)
    (c : (BigFppfOver.toScheme B (base k) hS).obj (truncObj k B hS n)) :
    adicThickeningι (PowerSeries k) (IsLocalRing.maximalIdeal (PowerSeries k)) n c =
      IsLocalRing.closedPoint (PowerSeries k) := by
  apply PrimeSpectrum.ext
  change (PrimeSpectrum.comap (Ideal.Quotient.mk _) c).asIdeal = _
  apply (Ideal.IsMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal (PowerSeries k))
    (PrimeSpectrum.comap (Ideal.Quotient.mk _) c).isPrime.ne_top _).symm
  apply Ideal.IsPrime.le_of_pow_le (n := n + 1)
  intro x hx
  change Ideal.Quotient.mk _ x ∈ c.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  exact Ideal.zero_mem _

/-! ### Maps to the terminal object -/

variable {k B hS}

/-- The structure morphism of an object of the site, as a morphism to the terminal object. -/
def toTerminal (T : BigFppfOver B (base k) hS) : T ⟶ baseTerminal B (base k) hS :=
  Over.homMk T.hom (Category.comp_id _)

theorem toTerminal_ext {T : BigFppfOver B (base k) hS} (a b : T ⟶ baseTerminal B (base k) hS) :
    a = b :=
  Over.mkIdTerminal.hom_ext a b

theorem yoneda_terminal_ext {F : (BigFppfOver B (base k) hS)ᵒᵖ ⥤ Type u}
    (a b : F ⟶ (terminalSpace B (base k) hS).obj) : a = b :=
  (baseTerminal_yonedaIsTerminal B (base k) hS).hom_ext a b

/-- The canonical morphism from a scheme of the site to the base, in the functor of points. -/
abbrev tb (T : BigFppfOver B (base k) hS) : yoneda.obj T ⟶ (terminalSpace B (base k) hS).obj :=
  yoneda.map (toTerminal T)

/-! ### Hilbert families of a section through one copy of the closed point -/

/-- The section `T ⟶ X_T` of the base change of `X ⟶ S` determined by a morphism `a : T ⟶ X`
over `S`. -/
def pointSection {T : BigFppfOver B (base k) hS} (a : T ⟶ spaceObj k B hS) :
    yoneda.obj T ⟶ schemeBaseChange (structureAlgMap k B hS) (CostructuredArrow.mk (tb T)) :=
  pullback.lift (yoneda.map a) (𝟙 _) (yoneda_terminal_ext _ _)

@[reassoc (attr := simp)]
theorem pointSection_fst {T : BigFppfOver B (base k) hS} (a : T ⟶ spaceObj k B hS) :
    pointSection a ≫ pullback.fst _ _ = yoneda.map a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pointSection_snd {T : BigFppfOver B (base k) hS} (a : T ⟶ spaceObj k B hS) :
    pointSection a ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

instance {T : BigFppfOver B (base k) hS} (a : T ⟶ spaceObj k B hS) : Mono (pointSection a) :=
  mono_of_mono_fac (pointSection_snd a)

/-- Over a scheme with one point, the section determined by a morphism to `X` is a closed
immersion. -/
theorem isClosedImmersion_pointSection {T : BigFppfOver B (base k) hS}
    [Subsingleton ((BigFppfOver.toScheme B (base k) hS).obj T)] (a : T ⟶ spaceObj k B hS) :
    IsClosedImmersion B (base k) hS (pointSection a) := by
  let Q := BigFppfOver.toScheme B (base k) hS
  have ha : a ≫ structureObjMap k B hS = toTerminal T := toTerminal_ext _ _
  let i : T ⟶ pullback (structureObjMap k B hS) (toTerminal T) := pullback.lift a (𝟙 T)
    (by rw [ha, Category.id_comp])
  have hi : i ≫ pullback.snd _ _ = 𝟙 T := pullback.lift_snd _ _ _
  have hclosed : AlgebraicGeometry.IsClosedImmersion (Q.map i) :=
    isClosedImmersion_of_comp_eq_id (Q.map (pullback.snd _ _)) (Q.map i)
      (by rw [← Q.map_comp, hi, Q.map_id])
  have hc : IsClosedImmersion B (base k) hS (yoneda.map i) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B (base k) hS
      (@AlgebraicGeometry.IsClosedImmersion.{u}) i).2 hclosed
  have heq : yoneda.map i ≫ (PreservesPullback.iso yoneda (structureObjMap k B hS)
      (toTerminal T)).hom = pointSection a := by
    apply pullback.hom_ext
    · rw [Category.assoc, PreservesPullback.iso_hom_fst, ← Functor.map_comp, pullback.lift_fst]
      exact (pointSection_fst a).symm
    · rw [Category.assoc, PreservesPullback.iso_hom_snd, ← Functor.map_comp, pullback.lift_snd]
      exact (CategoryTheory.Functor.map_id yoneda T).trans (pointSection_snd a).symm
  rw [← heq]
  exact MorphismProperty.RespectsIso.postcomp _ _ _ hc

/-- The range of an injective section, as a closed subspace isomorphic to `T`. -/
theorem isClosedSubspace_range_pointSection {T : BigFppfOver B (base k) hS}
    [Subsingleton ((BigFppfOver.toScheme B (base k) hS).obj T)] (a : T ⟶ spaceObj k B hS) :
    IsClosedSubspace B (base k) hS (Subfunctor.range (pointSection a)) := by
  refine ⟨isAlgebraicSpace_of_iso B (base k) hS (asIso (Subfunctor.toRange (pointSection a)))
    (isAlgebraicSpace_yoneda B (base k) hS T), ?_⟩
  have heq : (asIso (Subfunctor.toRange (pointSection a))).inv ≫ pointSection a =
      (Subfunctor.range (pointSection a)).ι :=
    (Iso.inv_comp_eq _).2 (Subfunctor.toRange_ι _).symm
  exact heq ▸ MorphismProperty.RespectsIso.precomp _
    (asIso (Subfunctor.toRange (pointSection a))).inv (pointSection a)
    (isClosedImmersion_pointSection a)

theorem range_pointSection_ι_snd {T : BigFppfOver B (base k) hS} (a : T ⟶ spaceObj k B hS) :
    (Subfunctor.range (pointSection a)).ι ≫ pullback.snd _ _ =
      (asIso (Subfunctor.toRange (pointSection a))).inv := by
  rw [← cancel_epi (Subfunctor.toRange (pointSection a)), ← Category.assoc,
    Subfunctor.toRange_ι, pointSection_snd]
  exact (asIso (Subfunctor.toRange (pointSection a))).hom_inv_id.symm

/-- The Hilbert family of the closed subspace of `X_T` cut out by the section determined by a
morphism `T ⟶ X`, over a one-point scheme `T`. -/
def pointFamily {T : BigFppfOver B (base k) hS}
    [Subsingleton ((BigFppfOver.toScheme B (base k) hS).obj T)] (a : T ⟶ spaceObj k B hS) :
    HilbertFamily (structureAlgMap k B hS) (CostructuredArrow.mk (tb T)) where
  Z := Subfunctor.range (pointSection a)
  closed := isClosedSubspace_range_pointSection a
  finitePresentation := by
    rw [range_pointSection_ι_snd]
    have hR : IsAlgebraicSpace B (base k) hS (Subfunctor.range (pointSection a)).toFunctor :=
      (isClosedSubspace_range_pointSection a).1
    simpa using isFinitePresentation_comp_iso hR hR (isAlgebraicSpace_yoneda B (base k) hS T)
      (𝟙 _) (asIso (Subfunctor.toRange (pointSection a))).symm
      (isFinitePresentation_id B (base k) hS hR)
  flat := by
    rw [range_pointSection_ι_snd]
    exact isFlat_of_isIso _ (isAlgebraicSpace_yoneda B (base k) hS T)
  proper := by
    rw [range_pointSection_ι_snd]
    exact isProper_of_isIso B (base k) hS _

/-- The Hilbert family of a section, over the canonical morphism to the base. -/
def pointFamilyOver {T : BigFppfOver B (base k) hS}
    [Subsingleton ((BigFppfOver.toScheme B (base k) hS).obj T)] (a : T ⟶ spaceObj k B hS) :
    HilbertFamilyOver (structureAlgMap k B hS) T :=
  ⟨tb T, pointFamily a⟩

/-- Every family over a scheme of the site lies over the canonical morphism to the base. -/
theorem exists_eq_mk_tb {T : BigFppfOver B (base k) hS}
    (x : HilbertFamilyOver (structureAlgMap k B hS) T) :
    ∃ z : HilbertFamily (structureAlgMap k B hS) (CostructuredArrow.mk (tb T)), x = ⟨tb T, z⟩ := by
  obtain ⟨b, z⟩ := x
  obtain rfl : b = tb T := yoneda_terminal_ext _ _
  exact ⟨z, rfl⟩

/-- Base change of a family over the canonical morphism, compared with a family over the
canonical morphism. -/
theorem baseChange_mk_eq_iff {T T' : BigFppfOver B (base k) hS} (g : T' ⟶ T)
    (z : HilbertFamily (structureAlgMap k B hS) (CostructuredArrow.mk (tb T)))
    (w : HilbertFamily (structureAlgMap k B hS) (CostructuredArrow.mk (tb T'))) :
    (⟨tb T, z⟩ : HilbertFamilyOver (structureAlgMap k B hS) T).baseChange g = ⟨tb T', w⟩ ↔
      w.Z = z.Z.preimage (schemeBaseChangeMap (structureAlgMap k B hS)
        (CostructuredArrow.homMk g (yoneda_terminal_ext _ _) :
          (CostructuredArrow.mk (tb T') : SchemesOverPresheaf B (base k) hS _) ⟶
            CostructuredArrow.mk (tb T))) := by
  have key : ∀ (b' : yoneda.obj T' ⟶ (terminalSpace B (base k) hS).obj)
      (h : yoneda.map g ≫ tb T = b')
      (w : HilbertFamily (structureAlgMap k B hS) (CostructuredArrow.mk b')),
      (⟨tb T, z⟩ : HilbertFamilyOver (structureAlgMap k B hS) T).baseChange g = ⟨b', w⟩ ↔
        w.Z = z.Z.preimage (schemeBaseChangeMap (structureAlgMap k B hS)
          (CostructuredArrow.homMk g h :
            (CostructuredArrow.mk b' : SchemesOverPresheaf B (base k) hS _) ⟶
              CostructuredArrow.mk (tb T))) := by
    rintro b' rfl w
    constructor
    · intro e
      have := HilbertFamilyOver.family_Z_heq e
      exact (eq_of_heq this).symm
    · intro e
      exact HilbertFamilyOver.ext rfl (heq_of_eq e.symm)
  exact key _ _ w

/-! ### The sections through the two copies of the closed point -/

variable (k B hS)

/-- The morphism `T_n ⟶ X` through the copy `b` of `Spec k⟦t⟧`. -/
def truncSection (b : Bool) (n : ℕ) : truncObj k B hS n ⟶ spaceObj k B hS :=
  Over.homMk (ObjectProperty.homMk
    ((formalBase k).truncationToS n ≫ (doubledClosedPoint k).chart b)) (by
      apply ObjectProperty.hom_ext
      change ((formalBase k).truncationToS n ≫ (doubledClosedPoint k).chart b) ≫
        structureMap k = (formalBase k).truncationToS n
      rw [Category.assoc, (doubledClosedPoint k).chart_comp_proj, Category.comp_id])

theorem truncationOverSucc_truncSection (b : Bool) (n : ℕ) :
    truncationOverSucc B (base k) hS (formalBase k) (contains_truncation k B hS) n ≫
      truncSection k B hS b (n + 1) = truncSection k B hS b n := by
  apply (Over.forget _).map_injective
  apply ObjectProperty.hom_ext
  change (formalBase k).truncationSucc n ≫
      ((formalBase k).truncationToS (n + 1) ≫ (doubledClosedPoint k).chart b) =
    (formalBase k).truncationToS n ≫ (doubledClosedPoint k).chart b
  rw [← Category.assoc, FormalBase.truncationSucc_toS]

/-- The family over `T_n` of the section through the first copy of the closed point. -/
abbrev levelFamily (n : ℕ) : HilbertFamilyOver (structureAlgMap k B hS) (truncObj k B hS n) :=
  pointFamilyOver (truncSection k B hS true n)

variable {k B hS}

/-- The square comparing a section with its restriction is cartesian. -/
theorem isPullback_of_compatible_sections {D : Type*} [Category D] {X X' T T' : D}
    {b : X' ⟶ X} {p : X ⟶ T} {p' : X' ⟶ T'} {g : T' ⟶ T}
    (hpb : IsPullback b p' p g) (s : T ⟶ X) (s' : T' ⟶ X')
    (hs : s ≫ p = 𝟙 T) (hs' : s' ≫ p' = 𝟙 T')
    (hcomm : s' ≫ b = g ≫ s) : IsPullback s' g b s := by
  have hv (c : PullbackCone b s) : c.fst ≫ p' ≫ g = c.snd := by
    rw [← hpb.w, ← Category.assoc, c.condition, Category.assoc, hs, Category.comp_id]
  refine IsPullback.of_isLimit (c := PullbackCone.mk s' g hcomm)
    (PullbackCone.IsLimit.mk hcomm (fun c => c.fst ≫ p') ?_ ?_ ?_)
  · intro c
    apply hpb.hom_ext
    · simpa only [Category.assoc, hcomm, reassoc_of% (hv c)] using c.condition.symm
    · simp [Category.assoc, hs']
  · intro c
    simpa only [Category.assoc] using hv c
  · intro c m hm _
    simpa only [Category.assoc, hs', Category.comp_id] using
      congrArg (fun f => f ≫ p') hm

/-- In a cartesian square of presheaves, the range of one side is the preimage of the range of
the opposite side. -/
theorem range_eq_preimage_of_isPullback {D : Type*} [Category D] {X X' T T' : D ⥤ Type u}
    {s' : T' ⟶ X'} {g : T' ⟶ T} {b : X' ⟶ X} {s : T ⟶ X}
    (h : IsPullback s' g b s) :
    Subfunctor.range s' = (Subfunctor.range s).preimage b := by
  ext U x
  exact Set.ext_iff.mp (Types.range_fst_of_isPullback
    (h.map ((evaluation D (Type u)).obj U))) x

/-- The range of the section of a morphism `a` is the preimage of the range of the section of
`a'` along a base change map, when `a` is the restriction of `a'`. -/
theorem range_pointSection_eq_preimage {T T' : BigFppfOver B (base k) hS} (g : T' ⟶ T)
    (a : T ⟶ spaceObj k B hS) (a' : T' ⟶ spaceObj k B hS) (ha : g ≫ a = a') :
    Subfunctor.range (pointSection a') = (Subfunctor.range (pointSection a)).preimage
      (schemeBaseChangeMap (structureAlgMap k B hS)
        (CostructuredArrow.homMk g (yoneda_terminal_ext _ _) :
          (CostructuredArrow.mk (tb T') : SchemesOverPresheaf B (base k) hS _) ⟶
            CostructuredArrow.mk (tb T))) := by
  apply range_eq_preimage_of_isPullback
  apply isPullback_of_compatible_sections (isPullback_schemeBaseChangeMap _ _)
    _ _ (pointSection_snd a) (pointSection_snd a')
  apply pullback.hom_ext
  · simp only [Category.assoc, schemeBaseChangeMap_fst, pointSection_fst]
    rw [← ha, Functor.map_comp]
    rfl
  · simp only [Category.assoc, schemeBaseChangeMap_snd, pointSection_snd_assoc,
      pointSection_snd, Category.comp_id, Category.id_comp]
    rfl

theorem levelFamily_compat (n : ℕ) :
    (levelFamily k B hS (n + 1)).baseChange
        (truncationOverSucc B (base k) hS (formalBase k) (contains_truncation k B hS) n) =
      levelFamily k B hS n :=
  (baseChange_mk_eq_iff _ _ _).2 (range_pointSection_eq_preimage _ _ _
    (truncationOverSucc_truncSection k B hS true n))

/-! ### A model of the Quot functor, read through the Hilbert functor -/

variable (N : QuotSitePresheafModel (quotSituation k B hS))

/-- A model of the Quot functor of `𝒪_X` is a model of the Hilbert functor of `X ⟶ S`
(Stacks 0D00). -/
def hilbertIso : N.presheaf ⋙ uliftFunctor.{u + 1, u} ≅
    hilbertPresheaf (structureAlgMap k B hS) :=
  N.iso ≪≫ (hilbertPresheafIsoQuotSitePresheaf _ _).symm

/-- The family named by a section of the model. -/
def toFamily {T : BigFppfOver B (base k) hS} (x : N.presheaf.obj (op T)) :
    HilbertFamilyOver (structureAlgMap k B hS) T :=
  (hilbertIso N).hom.app (op T) (ULift.up x)

/-- The section of the model naming a family. -/
def ofFamily {T : BigFppfOver B (base k) hS} (z : HilbertFamilyOver (structureAlgMap k B hS) T) :
    N.presheaf.obj (op T) :=
  ((hilbertIso N).inv.app (op T) z).down

theorem toFamily_ofFamily {T : BigFppfOver B (base k) hS}
    (z : HilbertFamilyOver (structureAlgMap k B hS) T) : toFamily N (ofFamily N z) = z :=
  congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _))
    ((hilbertIso N).inv_hom_id_app (op T))) z

theorem ofFamily_toFamily {T : BigFppfOver B (base k) hS} (x : N.presheaf.obj (op T)) :
    ofFamily N (toFamily N x) = x :=
  congrArg ULift.down (congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _))
    ((hilbertIso N).hom_inv_id_app (op T))) (ULift.up x))

theorem toFamily_map {T T' : BigFppfOver B (base k) hS} (g : T' ⟶ T) (x : N.presheaf.obj (op T)) :
    toFamily N (N.presheaf.map g.op x) = (toFamily N x).baseChange g :=
  congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _))
    ((hilbertIso N).hom.naturality g.op)) (ULift.up x)

theorem ofFamily_eq_map {T T' : BigFppfOver B (base k) hS} (g : T' ⟶ T)
    (z : HilbertFamilyOver (structureAlgMap k B hS) T)
    (z' : HilbertFamilyOver (structureAlgMap k B hS) T') (h : z.baseChange g = z') :
    ofFamily N z' = N.presheaf.map g.op (ofFamily N z) := by
  rw [← ofFamily_toFamily N (N.presheaf.map g.op (ofFamily N z)), toFamily_map,
    toFamily_ofFamily, h]

/-! ### The formal object -/

/-- **The formal object.** Over `T_n = Spec k⟦t⟧/(t^{n+1})`, the quotient of `𝒪_{X_{T_n}}`
cut out by the section through the first copy of the closed point, read in the model. -/
def formalObj : FormalObject B (base k) hS (Stack.fibredCategory B (base k) hS N.presheaf).val.p where
  base := formalBase k
  contains := contains_truncation k B hS
  level n := ⟨truncObj k B hS n, Discrete.mk (ofFamily N (levelFamily k B hS n))⟩
  level_eq _ := rfl
  transition n :=
    { base := truncationOverSucc B (base k) hS (formalBase k) (contains_truncation k B hS) n
      fiber := Discrete.eqToHom (ofFamily_eq_map N _ _ _ (levelFamily_compat n)) }
  transition_lift _ := IsHomLift.of_fac _ _ _ rfl rfl rfl

/-! ### Scheme-level facts used to rule out effectivity -/

/-- A closed immersion into `Spec R` through which every quotient `R ⧸ I n` factors, for a family
of ideals with zero intersection, is an isomorphism. -/
theorem isIso_of_isClosedImmersion_of_lifts_quotients {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R)) [_root_.AlgebraicGeometry.IsClosedImmersion f]
    (I : ℕ → Ideal R) (hI : (⨅ n, I n) = ⊥)
    (h : ∀ n, ∃ i : Spec (.of (R ⧸ I n)) ⟶ W,
      i ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I n)))) :
    IsIso f := by
  obtain ⟨J, e, hf⟩ := _root_.AlgebraicGeometry.IsClosedImmersion.Spec_iff.mp
    (inferInstance : _root_.AlgebraicGeometry.IsClosedImmersion f)
  have hJ : J = ⊥ := by
    apply le_antisymm _ bot_le
    rw [← hI]
    apply le_iInf
    intro n x hx
    obtain ⟨i, hi⟩ := h n
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ e.hom)
    have hc : (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ φ =
        CommRingCat.ofHom (Ideal.Quotient.mk (I n)) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ, Category.assoc, ← hf, hi]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he := congrArg (fun q : CommRingCat.of R ⟶ CommRingCat.of (R ⧸ I n) => q x) hc
    simpa [Ideal.Quotient.eq_zero_iff_mem.mpr hx] using he.symm
  rw [hf]
  haveI : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨?_, Ideal.Quotient.mk_surjective⟩
    subst J
    intro a b hab
    exact sub_eq_zero.mp (Ideal.mem_bot.mp (Ideal.Quotient.eq.mp hab))
  infer_instance

/-- A morphism `Spec R ⟶ X` lifts through a closed immersion `W ⟶ X` as soon as its restrictions
to `Spec (R ⧸ I n)` do, for a family of ideals with zero intersection. -/
theorem lifts_of_lifts_quotients {R : Type u} [CommRing R] {X W : Scheme.{u}}
    (j : W ⟶ X) [_root_.AlgebraicGeometry.IsClosedImmersion j] (s : Spec (.of R) ⟶ X)
    (I : ℕ → Ideal R) (hI : (⨅ n, I n) = ⊥)
    (h : ∀ n, ∃ t : Spec (.of (R ⧸ I n)) ⟶ W,
      t ≫ j = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I n))) ≫ s) :
    ∃ t : Spec (.of R) ⟶ W, t ≫ j = s := by
  have hP : IsIso (pullback.snd j s) :=
    isIso_of_isClosedImmersion_of_lifts_quotients (pullback.snd j s) I hI (by
      intro n
      obtain ⟨t, ht⟩ := h n
      exact ⟨pullback.lift t
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I n)))) ht,
        pullback.lift_snd _ _ _⟩)
  refine ⟨inv (pullback.snd j s) ≫ pullback.fst j s, ?_⟩
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

theorem iInf_maximalIdeal_pow_succ (R : Type u) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] :
    (⨅ n : ℕ, IsLocalRing.maximalIdeal R ^ (n + 1)) = ⊥ := by
  apply le_antisymm _ bot_le
  rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top]
  apply le_iInf
  intro n
  exact (iInf_le _ n).trans (Ideal.pow_le_pow_right (Nat.le_succ n))

instance isReduced_space : _root_.AlgebraicGeometry.IsReduced (space k) := by
  have : ∀ i, _root_.AlgebraicGeometry.IsReduced ((doubledClosedPoint k).cover.X i) := fun _ =>
    inferInstanceAs (_root_.AlgebraicGeometry.IsReduced (Spec (.of (PowerSeries k))))
  exact _root_.AlgebraicGeometry.IsReduced.of_openCover (𝒰 := (doubledClosedPoint k).cover)

/-! ### The formal object is not effective -/

variable (k B hS) in
/-- `X ⟶ S` as a morphism of the site to `Spec k⟦t⟧`, the base of the formal object. -/
def structureToFull : spaceObj k B hS ⟶ fullObj k B hS :=
  Over.homMk (ObjectProperty.homMk (structureMap k)) (ObjectProperty.hom_ext _ (Category.comp_id _))

variable (k B hS) in
/-- The inclusion `T_n ⟶ Spec k⟦t⟧`. -/
abbrev restr (n : ℕ) : truncObj k B hS n ⟶ fullObj k B hS :=
  restrictionToBase B (base k) hS (formalBase k) hS (contains_truncation k B hS) n

theorem truncSection_structureToFull (b : Bool) (n : ℕ) :
    truncSection k B hS b n ≫ structureToFull k B hS = restr k B hS n := by
  apply (Over.forget _).map_injective
  apply ObjectProperty.hom_ext
  change ((formalBase k).truncationToS n ≫ (doubledClosedPoint k).chart b) ≫ structureMap k =
    adicThickeningι (PowerSeries k) (IsLocalRing.maximalIdeal (PowerSeries k)) n
  rw [Category.assoc, (doubledClosedPoint k).chart_comp_proj, Category.comp_id]
  exact Category.comp_id _

variable (k B hS) in
/-- The graph `X ⟶ X ×_S Spec k⟦t⟧ = X_{Spec k⟦t⟧}`. -/
def graphMap : yoneda.obj (spaceObj k B hS) ⟶ schemeBaseChange (structureAlgMap k B hS)
    (CostructuredArrow.mk (tb (fullObj k B hS))) :=
  pullback.lift (𝟙 _) (yoneda.map (structureToFull k B hS)) (yoneda_terminal_ext _ _)

theorem yoneda_map_comp_graphMap {T : BigFppfOver B (base k) hS} (a : T ⟶ spaceObj k B hS)
    (ρ : T ⟶ fullObj k B hS) (ha : a ≫ structureToFull k B hS = ρ) :
    yoneda.map a ≫ graphMap k B hS = pointSection a ≫ schemeBaseChangeMap (structureAlgMap k B hS)
      (CostructuredArrow.homMk ρ (yoneda_terminal_ext _ _) :
        (CostructuredArrow.mk (tb T) : SchemesOverPresheaf B (base k) hS _) ⟶
          CostructuredArrow.mk (tb (fullObj k B hS))) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, schemeBaseChangeMap_fst, pointSection_fst, graphMap,
      pullback.lift_fst, Category.comp_id]
  · rw [Category.assoc, Category.assoc, schemeBaseChangeMap_snd, pointSection_snd_assoc,
      graphMap, pullback.lift_snd, ← Functor.map_comp, ha]
    exact (Category.id_comp _).symm

variable (k B hS) in
/-- The base change map `X_{T_n} ⟶ X_{Spec k⟦t⟧}` along the inclusion of a truncation. -/
abbrev restrBaseChange (n : ℕ) :=
  schemeBaseChangeMap (structureAlgMap k B hS)
    (CostructuredArrow.homMk (restr k B hS n) (yoneda_terminal_ext _ _) :
      (CostructuredArrow.mk (tb (truncObj k B hS n)) : SchemesOverPresheaf B (base k) hS _) ⟶
        CostructuredArrow.mk (tb (fullObj k B hS)))

theorem isEffective_formalObj (hN : IsAlgebraicSpace B (base k) hS N.presheaf) :
    FormalObject.IsEffective B (base k) hS (Stack.fibredCategory B (base k) hS N.presheaf).val.p
      (Stack.fibredCategory B (base k) hS N.presheaf).property (formalObj N) :=
  (FormalObject.isEffective_of_isAlgebraicStack
    (⟨Stack.fibredCategory B (base k) hS N.presheaf,
      Stack.isAlgebraicStack_fibredCategory.{u, u} B (base k) hS N.presheaf hN⟩ :
      Stack.AlgebraicStacks.{u, u} B (base k) hS) (formalObj N)).1

theorem realization_of_isAlgebraicSpace (hN : IsAlgebraicSpace B (base k) hS N.presheaf) :
    ∃ (x : (Stack.fibredCategory B (base k) hS N.presheaf).val.obj)
      (hx : (Stack.fibredCategory B (base k) hS N.presheaf).val.p.obj x =
        baseOver B (base k) hS (formalObj N).base hS),
      Nonempty ((formalObj N).Realization hS x hx) :=
  FormalObject.exists_realization_of_isEffective _ (isEffective_formalObj N hN)

/-- In the category fibred in sets of a presheaf, the source of a morphism names the restriction
of the element named by its target. -/
theorem fiber_eq_map_of_hom {F : (BigFppfOver B (base k) hS)ᵒᵖ ⥤ Type u}
    {x y : (Stack.fibredCategory B (base k) hS F).val.obj} (u : x ⟶ y) :
    x.fiber.as = F.map u.base.op y.fiber.as :=
  Discrete.eq_of_hom u.fiber

theorem exists_element_of_isAlgebraicSpace (hN : IsAlgebraicSpace B (base k) hS N.presheaf) :
    ∃ xf : N.presheaf.obj (op (fullObj k B hS)),
      ∀ n, ofFamily N (levelFamily k B hS n) = N.presheaf.map (restr k B hS n).op xf := by
  obtain ⟨⟨xb, ⟨xf⟩⟩, hx, ⟨Rz⟩⟩ := realization_of_isAlgebraicSpace N hN
  change xb = fullObj k B hS at hx
  subst hx
  refine ⟨xf, fun n => ?_⟩
  have hb : (Rz.r n).base = 𝟙 _ ≫ restr k B hS n ≫ 𝟙 _ := Rz.map_eq n
  rw [Category.id_comp, Category.comp_id] at hb
  rw [← hb]
  exact fiber_eq_map_of_hom (Rz.r n)

/-- If the model of the Quot functor were an algebraic space, the formal object would be
effective (Stacks 07X8), so some family over `Spec k⟦t⟧` would restrict to every level. -/
theorem exists_family_of_isAlgebraicSpace (hN : IsAlgebraicSpace B (base k) hS N.presheaf) :
    ∃ z : HilbertFamily (structureAlgMap k B hS) (CostructuredArrow.mk (tb (fullObj k B hS))),
      ∀ n, Subfunctor.range (pointSection (truncSection k B hS true n)) =
        z.Z.preimage (restrBaseChange k B hS n) := by
  obtain ⟨xf, hxf⟩ := exists_element_of_isAlgebraicSpace N hN
  obtain ⟨z, hz⟩ := exists_eq_mk_tb (toFamily N xf)
  refine ⟨z, fun n => (baseChange_mk_eq_iff (restr k B hS n) z
    (pointFamily (truncSection k B hS true n))).1 ?_⟩
  rw [← hz, ← toFamily_map, ← hxf n, toFamily_ofFamily]
  rfl

/-- **No family over `Spec k⟦t⟧` restricts to the section through the first copy of the closed
point at every level.** Such a family would be a closed subscheme `W` of `X` containing every
infinitesimal neighbourhood of the first copy of the closed point, hence the first copy of
`Spec k⟦t⟧`, hence (being closed, and `X` reduced) all of `X`; but its zeroth level contains only
one of the two copies of the closed point. -/
theorem not_exists_family
    (z : HilbertFamily (structureAlgMap k B hS) (CostructuredArrow.mk (tb (fullObj k B hS))))
    (hZ : ∀ n, Subfunctor.range (pointSection (truncSection k B hS true n)) =
      z.Z.preimage (restrBaseChange k B hS n)) : False := by
  let Q := BigFppfOver.toScheme B (base k) hS
  obtain ⟨W, j, w, hpb⟩ := z.closed.2.1 (graphMap k B hS)
  have hjc : _root_.AlgebraicGeometry.IsClosedImmersion (Q.map j) :=
    z.closed.2.2 (graphMap k B hS) w j hpb
  have hrange : Subfunctor.range (yoneda.map j) = z.Z.preimage (graphMap k B hS) := by
    simpa only [Subfunctor.range_ι] using range_eq_preimage_of_isPullback hpb.flip
  have hmem : ∀ (n : ℕ) (a : truncObj k B hS n ⟶ spaceObj k B hS),
      a ≫ structureToFull k B hS = restr k B hS n →
      ((pointSection a).app _ (𝟙 _) ∈ (Subfunctor.range
        (pointSection (truncSection k B hS true n))).obj _ ↔
        a ∈ (Subfunctor.range (yoneda.map j)).obj (op (truncObj k B hS n))) := by
    intro n a ha
    rw [hZ n, hrange]
    have h := congrArg (fun φ => φ.app (op (truncObj k B hS n)) (𝟙 (truncObj k B hS n)))
      (yoneda_map_comp_graphMap a (restr k B hS n) ha)
    have h' : (graphMap k B hS).app (op (truncObj k B hS n)) a =
        (restrBaseChange k B hS n).app (op (truncObj k B hS n))
          ((pointSection a).app (op (truncObj k B hS n)) (𝟙 (truncObj k B hS n))) := by
      simp only [NatTrans.comp_app_apply, yoneda_map_app, Category.id_comp] at h
      exact h
    exact Iff.of_eq (congrArg (fun e => e ∈ z.Z.obj (op (truncObj k B hS n))) h'.symm)
  have hfac : ∀ n, ∃ t : truncObj k B hS n ⟶ W, t ≫ j = truncSection k B hS true n := by
    intro n
    obtain ⟨t, ht⟩ := (hmem n _ (truncSection_structureToFull true n)).1 ⟨𝟙 _, rfl⟩
    exact ⟨t, by simpa using ht⟩
  obtain ⟨t, ht⟩ := lifts_of_lifts_quotients (Q.map j) ((doubledClosedPoint k).chart true)
    (fun n => IsLocalRing.maximalIdeal (PowerSeries k) ^ (n + 1))
    (iInf_maximalIdeal_pow_succ _) (fun n => by
      obtain ⟨t, ht⟩ := hfac n
      refine ⟨Q.map t, (Q.map_comp t j).symm.trans ?_⟩
      rw [ht]
      show (adicThickeningι _ _ n ≫ 𝟙 _) ≫ _ = _
      rw [Category.comp_id]
      rfl)
  have hsurj : Function.Surjective (Q.map j) := by
    have hcl : IsClosed (Set.range (Q.map j)) := hjc.isClosedEmbedding.isClosed_range
    have hsub : Set.range ((doubledClosedPoint k).chart true) ⊆ Set.range (Q.map j) := by
      rintro _ ⟨y, rfl⟩
      exact ⟨t y, by rw [← Scheme.Hom.comp_apply, ht]⟩
    intro x
    obtain ⟨b, y, rfl⟩ := (doubledClosedPoint k).exists_chart_eq x
    by_cases hy : y = IsLocalRing.closedPoint (PowerSeries k)
    · subst hy
      exact closure_minimal hsub hcl
        (doubledClosedPoint_chart_closedPoint_mem_closure k true b)
    · have hv := doubledClosedPoint_chart_true_apply_eq k
        ⟨y, (mem_powerSeriesGenericLocus_iff k y).2 hy⟩
      simp only [Scheme.Opens.ι_apply] at hv
      apply hsub
      cases b
      · exact ⟨y, hv⟩
      · exact ⟨y, rfl⟩
  haveI : Surjective (Q.map j) := ⟨hsurj⟩
  haveI : _root_.AlgebraicGeometry.IsReduced (Q.obj (spaceObj k B hS)) := isReduced_space (k := k)
  haveI : IsIso (Q.map j) := isIso_of_isClosedImmersion_of_surjective _
  let a' := truncSection k B hS false 0
  have hWj : Q.map j ≫ B.inclusion.map (spaceObj k B hS).hom = B.inclusion.map W.hom := by
    have h := congrArg B.inclusion.map (Over.w j)
    rw [Functor.map_comp] at h
    exact h
  have ha' : Q.map a' ≫ B.inclusion.map (spaceObj k B hS).hom =
      B.inclusion.map (truncObj k B hS 0).hom := by
    have h := congrArg B.inclusion.map (Over.w a')
    rw [Functor.map_comp] at h
    exact h
  obtain ⟨t', ht'⟩ := BigFppfOver.exists_hom_of_comp_eq B (base k) hS
    (X := truncObj k B hS 0) (Y := W) (Q.map a' ≫ inv (Q.map j)) (by
      rw [← hWj, Category.assoc, IsIso.inv_hom_id_assoc, ha'])
  have ht'j : t' ≫ j = a' := by
    apply Q.map_injective
    rw [Q.map_comp, ht', Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨h, hh⟩ := (hmem 0 a' (truncSection_structureToFull false 0)).2 ⟨t', by
    simpa using ht'j⟩
  let T0 := truncObj k B hS 0
  let fst0 := pullback.fst (structureAlgMap k B hS).hom (CostructuredArrow.mk (tb T0)).hom
  let snd0 := pullback.snd (structureAlgMap k B hS).hom (CostructuredArrow.mk (tb T0)).hom
  have e1 : fst0.app (op T0) ((pointSection (truncSection k B hS true 0)).app (op T0) h) =
      h ≫ truncSection k B hS true 0 :=
    congrArg (fun φ => φ.app (op T0) h) (pointSection_fst (truncSection k B hS true 0))
  have e2 : fst0.app (op T0) ((pointSection a').app (op T0) (𝟙 T0)) = 𝟙 T0 ≫ a' :=
    congrArg (fun φ => φ.app (op T0) (𝟙 T0)) (pointSection_fst a')
  have e3 : snd0.app (op T0) ((pointSection (truncSection k B hS true 0)).app (op T0) h) = h :=
    congrArg (fun φ => φ.app (op T0) h) (pointSection_snd (truncSection k B hS true 0))
  have e4 : snd0.app (op T0) ((pointSection a').app (op T0) (𝟙 T0)) = 𝟙 T0 :=
    congrArg (fun φ => φ.app (op T0) (𝟙 T0)) (pointSection_snd a')
  have hsnd : h = 𝟙 T0 := e3.symm.trans ((congrArg (fun e => snd0.app (op T0) e) hh).trans e4)
  have hfst : h ≫ truncSection k B hS true 0 = 𝟙 T0 ≫ a' :=
    e1.symm.trans ((congrArg (fun e => fst0.app (op T0) e) hh).trans e2)
  simp only [hsnd, Category.id_comp] at hfst
  have hQ := congrArg Q.map hfst
  obtain ⟨c⟩ : Nonempty (Q.obj (truncObj k B hS 0)) := by
    haveI : (IsLocalRing.maximalIdeal (PowerSeries k) ^ (0 + 1)).IsMaximal := by
      simpa using IsLocalRing.maximalIdeal.isMaximal (PowerSeries k)
    exact inferInstanceAs (Nonempty (PrimeSpectrum _))
  have hpt := congrArg (fun g => g c) hQ
  change ((adicThickeningι _ _ 0 ≫ 𝟙 _) ≫ (doubledClosedPoint k).chart true) c =
    ((adicThickeningι _ _ 0 ≫ 𝟙 _) ≫ (doubledClosedPoint k).chart false) c at hpt
  simp only [Category.comp_id] at hpt
  change (doubledClosedPoint k).chart true (adicThickeningι _ _ 0 c) =
    (doubledClosedPoint k).chart false (adicThickeningι _ _ 0 c) at hpt
  rw [adicThickeningι_apply] at hpt
  exact doubledClosedPoint_chart_closedPoint_ne k hpt

/-- **A model of `Quot_{𝒪_X/X/S}` is not an algebraic space.** -/
theorem not_isAlgebraicSpace : ¬ IsAlgebraicSpace B (base k) hS N.presheaf := fun hN => by
  obtain ⟨z, hz⟩ := exists_family_of_isAlgebraicSpace N hN
  exact not_exists_family z hz

/-! ### The counterexamples to Stacks 09TU and 09DS without separatedness -/

variable (k B hS) in
/-- The structure morphism of the doubled closed point is flat, as a morphism of algebraic
spaces. -/
theorem isFlat_structureAlgMap : IsFlat B (base k) hS (structureAlgMap k B hS).hom :=
  isFlat_yoneda_map B (base k) hS (structureObjMap k B hS)
    (inferInstanceAs (Flat (structureMap k)))

end AlgebraicGeometry.Space.QuotNonSeparated

namespace AlgebraicGeometry.Space

open QuotNonSeparated

universe u

/-- **The Quot functor of a non-separated morphism need not be an algebraic space.** There are
a big fppf site, a scheme `S` in it and a Quot situation `f : X ⟶ B` over `S` (Stacks 09TR), with
`f` of finite presentation and flat and the module `F` of finite presentation, such that `f` is
not separated, `Quot_{F/X/B}` has a model in the universe of the site, and no such model is an
algebraic space.

Here `S = B = Spec k⟦t⟧`, `X` is two copies of `Spec k⟦t⟧` glued along `D(t)` and `F = 𝒪_X`. -/
theorem exists_quotSituation_not_isAlgebraicSpace :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (D : QuotSituation B S hS),
      IsFlat B S hS D.f.hom ∧ ¬ IsSeparated B S hS D.f.hom ∧ D.F.IsFinitePresentationOnSite ∧
        Nonempty (QuotSitePresheafModel D) ∧
        ∀ N : QuotSitePresheafModel D, ¬ IsAlgebraicSpace B S hS N.presheaf := by
  obtain ⟨B, hS⟩ := BigFppfSite.exists_contains (QuotNonSeparated.base (ULift.{u} ℚ))
  obtain ⟨M, -⟩ := (quotSituation (ULift.{u} ℚ) B hS).exists_quotSitePresheafModel
  exact ⟨B, _, hS, quotSituation _ B hS, isFlat_structureAlgMap _ B hS,
    not_isSeparated_structureAlgMap _ B hS, isFinitePresentationOnSite_structureSheafModule _,
    ⟨M⟩, fun N => not_isAlgebraicSpace N⟩

attribute [local implicit_reducible] QuotSituation.toCoherentSituation in
/-- **The stack of coherent sheaves of a non-separated morphism need not be algebraic.** There
are a big fppf site, a scheme `S` in it and a coherent situation `f : X ⟶ Y` over `S` (Stacks
08KB), with `f` of finite presentation and flat, such that `f` is not separated and `Coh_{X/Y}`
is not an algebraic stack. -/
theorem exists_coherentSituation_not_isAlgebraicStack.{w} :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (D : CoherentSituation B S hS),
      IsFlat B S hS D.f.hom ∧ ¬ IsSeparated B S hS D.f.hom ∧
        ¬ Stack.IsAlgebraicStack.{u, w} B S hS D.coherentCFG.val := by
  obtain ⟨B, S, hS, D, hflat, hsep, hF, ⟨N⟩, hN⟩ := exists_quotSituation_not_isAlgebraicSpace.{u}
  refine ⟨B, S, hS, D.toCoherentSituation, hflat, hsep, fun hCoh => hN N ?_⟩
  exact N.isAlgebraicSpace_of_homRepresentations
    (D.hasHomRepresentation_of_isEtaleLocallyGeneratedBelow
      (exists_isEtaleLocallyGeneratedBelow_lt_cutoff_of_isFiniteTypeOnSite D.X D.F
        (@SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite _ _ _ _ _ hF)))
    hCoh

end AlgebraicGeometry.Space

end
