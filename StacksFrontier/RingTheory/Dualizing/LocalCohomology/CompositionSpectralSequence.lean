module

public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.Composition
public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.Triangulated
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.Assembled
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessIsLocal
import all StacksFrontier.RingTheory.LocalCohomology.FinitenessIsLocal

/-!
# The spectral sequence of a composition of local cohomology functors

Let `I` and `J` be finitely generated ideals of a commutative ring `A`, and let `Z = V(I)` and
`Y = V(J)`. This file builds the spectral sequence
`E₂^{p,q} = H^p_Y(H^q_Z(K)) ⇒ H^{p+q}_{Y ∩ Z}(K)` for `K` in `D⁺(A)`.

## Main definitions

* `Dualizing.localCohomologyFunctorPlus` — `RΓ_{V(I)}` as a triangulated endofunctor of `D⁺(A)`.

## Main results

* `Dualizing.isGE_localCohomologyFunctor_obj` — `RΓ_{V(I)}` does not lower connectivity:
  if `K` lies in `D^{≥m}` then so does `RΓ_{V(I)}(K)`. This is what makes `RΓ_{V(I)}` act on
  `D⁺(A)` at all, and it needs no Noetherian hypothesis.
* `Dualizing.spectralSequencePageTwoIso` — **[Stacks, Tag 0BJC]**, the second page of the
  spectral sequence is `E₂^{p, q} = H^p_Y(H^q_Z(K))`.
* `Dualizing.abutsTo_spectralSequence` — **[Stacks, Tag 0BJC]**, it abuts to
  `H^{p + q}_{Y ∩ Z}(K)`.
* `Dualizing.localCohomology_comp_spectralSequence` — **the whole of [Stacks, Tag 0BJC]**: the
  five clauses of the tag conjoined, the two in `Composition.lean` together with the two above
  and `Z ∩ Y = V(I + J)`.

## References

* [Stacks Project, Tag 0BJC](https://stacks.math.columbia.edu/tag/0BJC)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

universe u v

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.LocalCohomology.derivedPowerTorsionProperty_isTriangulated
attribute [local instance]
  Stacks.LocalCohomology.derivedPowerTorsionProperty_isClosedUnderIsomorphisms

/-! ### Local cohomology does not lower connectivity -/

/-- A zero module is `I`-power torsion. -/
private alias isIPowerTorsion_of_isZero := Stacks.LocalCohomology.torsion_of_isZero

/-- Truncation at level `n` does not change the cohomology in degrees `≤ n`. -/
private lemma isIso_homology_map_truncLEι {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (X : DerivedCategory C) (n i : ℤ) (hi : i ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncLEι n).app X)) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let T := (t.triangleLEGT n).obj X
  have hT := t.triangleLEGT_distinguished n X
  have : T.obj₃.IsGE (n + 1) := t.isGE_truncGT_obj X n (n + 1)
  have hz (j : ℤ) (hj : j ≤ n) : IsZero ((DerivedCategory.homologyFunctor C j).obj T.obj₃) :=
    DerivedCategory.isZero_of_isGE T.obj₃ (n + 1) j (by omega)
  have : Mono ((DerivedCategory.homologyFunctor C i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)).2
      ((hz (i - 1) (by omega)).eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).2
      ((hz i hi).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor C i).map T.mor₁)

/-- Truncation preserves the property of having `I`-power-torsion cohomology: the property is a
condition on each cohomology module, and truncation either leaves one unchanged or kills it. -/
private lemma derivedPowerTorsionProperty_truncLE
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (X : DerivedCategory (ModuleCat.{v} A))
    (hX : derivedPowerTorsionProperty A I hI X) (n : ℤ) :
    derivedPowerTorsionProperty A I hI
      ((DerivedCategory.TStructure.t.truncLE n).obj X) := by
  intro i
  by_cases hi : i ≤ n
  · have := isIso_homology_map_truncLEι X n i hi
    exact (powerTorsionModuleProperty A I hI).prop_of_iso
      (asIso ((DerivedCategory.homologyFunctor _ i).map
        ((DerivedCategory.TStructure.t.truncLEι n).app X))).symm (hX i)
  · exact isIPowerTorsion_of_isZero I _ (DerivedCategory.isZero_of_isLE _ n i (by omega))

/-- **Local cohomology does not lower connectivity.** If `K` lies in `D^{≥m}` then so does
`RΓ_{V(I)}(K)`, for `I` a finitely generated ideal of an arbitrary commutative ring.

The proof is the universal property of the coreflection. Write `W = τ^{≤m-1}(RΓ_{V(I)} K)`. The
property of having `I`-power-torsion cohomology is a condition on each cohomology module, so it
is inherited by `W`, which therefore lies in the subcategory that `RΓ_{V(I)}` corefects onto.
The counit then identifies `W ⟶ RΓ_{V(I)} K` with `W ⟶ K`, and the latter group vanishes because
`W` lies in `D^{≤m-1}` and `K` in `D^{≥m}`. Hence the canonical map `W ⟶ RΓ_{V(I)} K` is zero,
which forces `W = 0`, i.e. `RΓ_{V(I)} K` lies in `D^{≥m}`. -/
theorem isGE_localCohomologyFunctor_obj {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat.{v} A)) (m : ℤ) [K.IsGE m] :
    ((derivedPowerTorsionProperty A I hI).ι.obj
      ((localCohomologyFunctor A I hI).obj K)).IsGE m := by
  let P := derivedPowerTorsionProperty.{u, v} A I hI
  let adj := localCohomologyAdjunction A I hI
  let Z := (localCohomologyFunctor A I hI).obj K
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{v} A)
  let L : P.FullSubcategory := ⟨(t.truncLE (m - 1)).obj Z.obj,
    derivedPowerTorsionProperty_truncLE I hI Z.obj Z.property (m - 1)⟩
  have he : (t.truncLEι (m - 1)).app Z.obj = 0 := by
    apply (Stacks.LocalCohomology.inclusion_counit_bijective adj L K).1
    exact (t.zero_of_isLE_of_isGE
      ((t.truncLEι (m - 1)).app Z.obj ≫ adj.counit.app K) (m - 1) m (by omega)
      (t.isLE_truncLE_obj Z.obj (m - 1) (m - 1)) ‹K.IsGE m›).trans zero_comp.symm
  apply (t.isGE_iff_isZero_truncLE_obj (m - 1) m (by omega) Z.obj).2
  apply (IsZero.iff_id_eq_zero _).2
  apply t.to_truncLE_obj_ext
  simp [he]

/-! ### Local cohomology as an endofunctor of the bounded below derived category -/

section Endo

variable (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)

/-- **`RΓ_{V(I)}` as an endofunctor of `D(A)`**: local cohomology followed by the inclusion of
the objects with `I`-power-torsion cohomology. This is the functor the source writes `RΓ_Z`
when it composes it with anything defined on all of `D(A)`. -/
@[instance_reducible]
def localCohomologyEndo :
    DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A) :=
  localCohomologyFunctor A I hI ⋙ (derivedPowerTorsionProperty A I hI).ι

/-- `RΓ_{V(I)}` followed by the inclusion commutes with the shift: both factors do, the
inclusion because the power-torsion subcategory is stable under the shift and `RΓ_{V(I)}` by
`Stacks.LocalCohomology.localCohomologyFunctorCommShift`. -/
noncomputable instance localCohomologyEndoCommShift :
    (localCohomologyEndo.{u, v} A I hI).CommShift ℤ := by
  let : (localCohomologyFunctor.{u, v} A I hI).CommShift ℤ :=
    Stacks.LocalCohomology.localCohomologyFunctorCommShift.{v, u} A I hI
  unfold localCohomologyEndo
  infer_instance

/-- `RΓ_{V(I)}` followed by the inclusion is a triangulated functor: `RΓ_{V(I)}` is one by
`Stacks.LocalCohomology.localCohomologyFunctor_isTriangulated`, and the inclusion of a
triangulated subcategory is one. -/
instance localCohomologyEndo_isTriangulated :
    (localCohomologyEndo.{u, v} A I hI).IsTriangulated := by
  let : (localCohomologyFunctor.{u, v} A I hI).CommShift ℤ :=
    Stacks.LocalCohomology.localCohomologyFunctorCommShift.{v, u} A I hI
  let : (localCohomologyFunctor.{u, v} A I hI).IsTriangulated :=
    Stacks.LocalCohomology.localCohomologyFunctor_isTriangulated.{v, u} A I hI
  unfold localCohomologyEndo
  infer_instance

/-- **`RΓ_{V(I)}` as a triangulated endofunctor of `D⁺(A)`.** `RΓ_{V(I)}` sends `D⁺(A)` into
itself by `Dualizing.isGE_localCohomologyFunctor_obj`, so it restricts to the bounded below
derived category, and the restriction inherits the shift-compatibility and the triangulated
structure from the unrestricted functor. -/
@[instance_reducible]
def localCohomologyFunctorPlus :
    DerivedCategory.Plus (ModuleCat.{v} A) ⥤ DerivedCategory.Plus (ModuleCat.{v} A) :=
  (DerivedCategory.TStructure.t (C := ModuleCat.{v} A)).plus.lift
    (DerivedCategory.Plus.ι ⋙ localCohomologyEndo A I hI)
    (fun X => by
      obtain ⟨m, hm⟩ := X.2
      let _ : (DerivedCategory.Plus.ι.obj X).IsGE m := hm
      exact ⟨m, isGE_localCohomologyFunctor_obj I hI (DerivedCategory.Plus.ι.obj X) m⟩)

/-- The restriction of `RΓ_{V(I)}` to `D⁺(A)` commutes with the shift. -/
noncomputable instance localCohomologyFunctorPlusCommShift :
    (localCohomologyFunctorPlus.{u, v} A I hI).CommShift ℤ := by
  unfold localCohomologyFunctorPlus
  infer_instance

/-- The restriction of `RΓ_{V(I)}` to `D⁺(A)` is a triangulated functor. -/
instance localCohomologyFunctorPlus_isTriangulated :
    (localCohomologyFunctorPlus.{u, v} A I hI).IsTriangulated := by
  unfold localCohomologyFunctorPlus
  infer_instance

/-- The restriction of `RΓ_{V(I)}` to `D⁺(A)` is the unrestricted functor. -/
def localCohomologyFunctorPlusCompιIso :
    localCohomologyFunctorPlus.{u, v} A I hI ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ localCohomologyEndo A I hI :=
  (DerivedCategory.TStructure.t (C := ModuleCat.{v} A)).plus.liftCompιIso _ _

end Endo

/-! ### The spectral sequence -/

section SpectralSequence

variable (A : Type u) [CommRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG)

open Stacks.Cohomology.LerayTruncation

/-- **`RΓ_Y ∘ RΓ_Z ≅ RΓ_{Y ∩ Z}` as endofunctors of `D(A)`**, which is
`Dualizing.localCohomologyCompIso` read through the inclusion of the
`(I + J)`-power-torsion objects. -/
def localCohomologyEndoCompIso :
    localCohomologyEndo.{u, v} A I hI ⋙ localCohomologyEndo.{u, v} A J hJ ≅
      localCohomologyEndo.{u, v} A (I + J) (Submodule.FG.sup hI hJ) :=
  Functor.isoWhiskerRight (localCohomologyCompIso A I J hI hJ)
    (derivedPowerTorsionProperty A (I + J) (Submodule.FG.sup hI hJ)).ι

/-- **`RΓ_Y ∘ RΓ_Z ≅ RΓ_{Y ∩ Z}` on `D⁺(A)`.** The inclusion of `D⁺(A)` into `D(A)` is fully
faithful, so the isomorphism of endofunctors of `D(A)` descends to the restrictions. -/
def localCohomologyFunctorPlusCompIso :
    localCohomologyFunctorPlus.{u, v} A I hI ⋙ localCohomologyFunctorPlus.{u, v} A J hJ ≅
      localCohomologyFunctorPlus.{u, v} A (I + J) (Submodule.FG.sup hI hJ) :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (Functor.isoWhiskerLeft DerivedCategory.Plus.ι (localCohomologyEndoCompIso A I J hI hJ))

/-- Local cohomology is left `t`-exact on `D⁺(A)`. -/
lemma isGE_localCohomologyFunctorPlus_obj (Y : DerivedCategory.Plus (ModuleCat.{v} A))
    (m : ℤ) (hY : DerivedCategory.Plus.IsGE Y m) :
    DerivedCategory.Plus.IsGE ((localCohomologyFunctorPlus.{u, v} A J hJ).obj Y) m := by
  let _ : (DerivedCategory.Plus.ι.obj Y).IsGE m :=
    (DerivedCategory.Plus.isGE_ι_obj_iff Y m).2 hY
  exact (DerivedCategory.Plus.isGE_ι_obj_iff _ m).1
    (isGE_localCohomologyFunctor_obj J hJ (DerivedCategory.Plus.ι.obj Y) m)

/-- **The spectral sequence of a composition of local cohomology functors.** The
`E₂`-cohomological spectral sequence of the canonical truncation tower of `RΓ_Z K`, pushed
forward by `RΓ_Y` and read through cohomology, as a functor on `D⁺(A)`.

Nothing is chosen: this is the value of a functor, so the identification of the second page is a
natural isomorphism and not merely a pointwise one. -/
def spectralSequence :
    DerivedCategory.Plus (ModuleCat.{v} A) ⥤
      E₂CohomologicalSpectralSequence (ModuleCat.{v} A) :=
  localCohomologyFunctorPlus.{u, v} A I hI ⋙
    cohomologySpectralObjectFunctor (localCohomologyFunctorPlus.{u, v} A J hJ) ⋙
      Abelian.SpectralObject.E₂SpectralSequenceFunctor (ModuleCat.{v} A)

/-- **[Stacks, Tag 0BJC], the second page.** At `(p, q)` the second page of the spectral
sequence is `H^p_Y(H^q_Z(K))`, naturally in `K`: the `q`-th local cohomology module of `K`
supported on `Z = V(I)`, placed in degree zero, has its `p`-th local cohomology supported on
`Y = V(J)` taken.

This is `Stacks.Cohomology.LerayCard.pageTwoNatIsoDerived` for `Φ = RΓ_Y`, precomposed with
`RΓ_Z`; no Noetherian hypothesis and no comparison of models of local cohomology is involved. -/
@[stacks 0BJC "the second page of the spectral sequence"]
def spectralSequencePageTwoIso (p q : ℤ) :
    spectralSequence.{u, v} A I J hI hJ ⋙ SpectralSequence.pageFunctor _ _ 2 2 ⋙
        HomologicalComplex.eval _ _ (p, q) ≅
      localCohomologyFunctorPlus.{u, v} A I hI ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{v} A) q ⋙
          DerivedCategory.Plus.singleFunctor (ModuleCat.{v} A) 0 ⋙
            localCohomologyFunctorPlus.{u, v} A J hJ ⋙
              DerivedCategory.Plus.homologyFunctor (ModuleCat.{v} A) p :=
  Functor.isoWhiskerLeft (localCohomologyFunctorPlus.{u, v} A I hI)
    (Stacks.Cohomology.LerayCard.pageTwoNatIsoDerived
      (localCohomologyFunctorPlus.{u, v} A J hJ) p q)

/-- **[Stacks, Tag 0BJC], the convergence.** For `K` in `D⁺(A)` the spectral sequence has an
infinity page at every bidegree and the terms `E_∞^{p, n-p}` are the successive quotients of a
finite decreasing filtration of `H^n_{Y ∩ Z}(K)`.

Boundedness of the spectral object comes from
`Stacks.Cohomology.LerayTruncation.isBounded_cohomologySpectralObjectFunctor_obj`, whose
hypothesis is left `t`-exactness of `RΓ_Y` — that is
`Dualizing.isGE_localCohomologyFunctorPlus_obj`. The abutment the generic theorem produces is
`H^n(RΓ_Y(RΓ_Z K))`, and `Dualizing.localCohomologyFunctorPlusCompIso` identifies it with
`H^n_{Y ∩ Z}(K)`. -/
@[stacks 0BJC "the convergence of the spectral sequence"]
theorem abutsTo_spectralSequence (K : DerivedCategory.Plus (ModuleCat.{v} A)) :
    SpectralSequence.AbutsTo ((spectralSequence.{u, v} A I J hI hJ).obj K)
      (fun n : ℤ ↦ (DerivedCategory.Plus.homologyFunctor (ModuleCat.{v} A) n).obj
        ((localCohomologyFunctorPlus.{u, v} A (I + J) (Submodule.FG.sup hI hJ)).obj K)) :=
  have := isBounded_cohomologySpectralObjectFunctor_obj
    (localCohomologyFunctorPlus.{u, v} A J hJ)
    (isGE_localCohomologyFunctorPlus_obj A J hJ)
    ((localCohomologyFunctorPlus.{u, v} A I hI).obj K)
  (Abelian.SpectralObject.abutsTo_spectralSequenceFunctor_obj _).of_iso fun n ↦
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{v} A) n).mapIso
      ((localCohomologyFunctorPlusCompIso A I J hI hJ).app K)

/-! ### The whole of Stacks 0BJC -/

/-- **Stacks 0BJC, all five clauses.** Let `A` be a ring, let `I, J ⊆ A` be finitely generated
ideals and set `Z = V(I)`, `Y = V(J)`. Then

1. `Z ∩ Y = V(I + J)`;
2. `RΓ_Y` carries an object with `I`-power-torsion cohomology to one with
   `(I + J)`-power-torsion cohomology, so that `RΓ_Y ∘ RΓ_Z` is a functor
   `D(A) → D_{(I + J)^∞-torsion}(A)`;
3. `RΓ_Y ∘ RΓ_Z ≅ RΓ_{Y ∩ Z}` as functors `D(A) → D_{(I + J)^∞-torsion}(A)`;
4. for `K` in `D⁺(A)` the second page of the spectral sequence of the composition is
   `E₂^{p, q} = H^p_Y(H^q_Z(K))`, naturally in `K`; and
5. that spectral sequence abuts to `H^{p + q}_{Y ∩ Z}(K)`.

Clauses (3) and (4) are isomorphisms of functors, so they appear here as `Nonempty`; the
isomorphisms themselves are `Dualizing.localCohomologyCompIso` and
`Dualizing.spectralSequencePageTwoIso`, each of which carries the tag for its own clause, as do
`PrimeSpectrum.zeroLocus_sup` for (1), `Dualizing.localCohomology_comp_torsion` for (2) and
`Dualizing.abutsTo_spectralSequence` for (5). Nothing here is Noetherian and no comparison of
the two models of local cohomology is involved: everything is the coreflection model `RΓ_{V(I)}`
of [Stacks, Tag 0A6Q]. -/
@[stacks 0BJC "all five clauses conjoined; the two isomorphisms of functors appear as \
`Nonempty`, the isomorphisms themselves being the declarations that carry the tag for those \
clauses"]
theorem localCohomology_comp_spectralSequence :
    PrimeSpectrum.zeroLocus (I : Set A) ∩ PrimeSpectrum.zeroLocus (J : Set A) =
        PrimeSpectrum.zeroLocus ((I + J : Ideal A) : Set A) ∧
      (∀ K : PowerTorsionDerivedCategory.{u, v} A I hI,
        derivedPowerTorsionProperty A (I + J) (Submodule.FG.sup hI hJ)
          (((derivedPowerTorsionProperty A I hI).ι ⋙ localCohomologyFunctor A J hJ ⋙
            (derivedPowerTorsionProperty A J hJ).ι).obj K)) ∧
      Nonempty (localCohomologyFunctor.{u, v} A I hI ⋙
          localCohomologyOnPowerTorsion A I J hI hJ ≅
        localCohomologyFunctor A (I + J) (Submodule.FG.sup hI hJ)) ∧
      (∀ p q : ℤ, Nonempty (spectralSequence.{u, v} A I J hI hJ ⋙
          SpectralSequence.pageFunctor _ _ 2 2 ⋙ HomologicalComplex.eval _ _ (p, q) ≅
        localCohomologyFunctorPlus.{u, v} A I hI ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleCat.{v} A) q ⋙
            DerivedCategory.Plus.singleFunctor (ModuleCat.{v} A) 0 ⋙
              localCohomologyFunctorPlus.{u, v} A J hJ ⋙
                DerivedCategory.Plus.homologyFunctor (ModuleCat.{v} A) p)) ∧
      ∀ K : DerivedCategory.Plus (ModuleCat.{v} A),
        SpectralSequence.AbutsTo ((spectralSequence.{u, v} A I J hI hJ).obj K)
          (fun n : ℤ ↦ (DerivedCategory.Plus.homologyFunctor (ModuleCat.{v} A) n).obj
            ((localCohomologyFunctorPlus.{u, v} A (I + J) (Submodule.FG.sup hI hJ)).obj K)) :=
  ⟨by rw [Ideal.add_eq_sup, PrimeSpectrum.zeroLocus_sup],
    localCohomology_comp_torsion.{u, v} A I J hI hJ,
    ⟨localCohomologyCompIso.{u, v} A I J hI hJ⟩,
    fun p q ↦ ⟨spectralSequencePageTwoIso.{u, v} A I J hI hJ p q⟩,
    abutsTo_spectralSequence.{u, v} A I J hI hJ⟩

end SpectralSequence

end Dualizing

end
